"""Controller: decides each batch, then reviews it.

Per iteration:
  1. read stats (solved set, per-problem effort, yield of each action type)
  2. form hypotheses: which action types are paying off per engine-hour
  3. write a plan: problems x presets x budgets (+ macros / model toggles)
  4. run it (loop.run_batch), mine insights, maybe retrain the value model
  5. log reasoning + plan to ``insights`` (author='controller'), refresh
     dashboard and verified submission files.

Action types
  cover     never-attempted problems with the current best solver preset
  escalate  unsolved problems, next rung of the escalation ladder
  bidir     solved problems short enough for an exact optimum proof
  polish    re-shorten stored best paths with bigger balls
  resolve   solved problems re-searched with a different strategy/seed
            (diverse paths shorten to different lengths)

Steering: ``config/strategy.json`` (written by a human or AI analyst) is
merged over DEFAULTS each iteration, so the analyst can change presets,
ladders, budgets, weights, macros or the model without code changes.
Guardrails: the controller only creates jobs; results are stored only if
the official verifier accepts them (loop.run_batch -> official.verify_one).
"""
from __future__ import annotations

import json
import math
import time

from . import dashboard, db, export, loop, mining, problems
from .official import ROOT

CONFIG = ROOT / "config" / "strategy.json"

DEFAULTS = {
    "batch_jobs": 400,                 # jobs per batch
    "action_weights": {"cover": 1.0, "escalate": 1.0, "bidir": 0.5, "polish": 0.6, "resolve": 0.6},
    "cover_preset": "gbfs",
    "ladder": ["gbfs", "gbfs_noise", "beam", "gbfs_deep", "beam_wide"],
    "resolve_presets": ["gbfs_lam", "beam", "gbfs_noise"],
    "bidir_max_len": 14,               # attempt exact search when best <= this
    "preset_overrides": {},            # preset -> {param: value}
    "use_macros": False,
    "use_model": False,
    "retrain_every": 5,                # batches
    "mine_every": 1,
    "export_every": 1,
}


def load_config() -> dict:
    cfg = json.loads(json.dumps(DEFAULTS))
    if CONFIG.exists():
        user = json.loads(CONFIG.read_text())
        for k, v in user.items():
            if isinstance(v, dict) and isinstance(cfg.get(k), dict):
                cfg[k].update(v)
            else:
                cfg[k] = v
    return cfg


def action_yield(con) -> dict:
    """Moves saved + 30 per new solve, per engine-hour, by action (last 20 batches)."""
    out = {}
    rows = con.execute("SELECT batch_id, config FROM batches WHERE status='done' ORDER BY batch_id DESC LIMIT 20")
    per = {}
    for b in rows:
        try:
            act = json.loads(b["config"] or "{}").get("actions", {})
        except json.JSONDecodeError:
            continue
        for a in act:
            per.setdefault(a, []).append(b["batch_id"])
    for a, bids in per.items():
        q = ",".join("?" * len(bids))
        secs = con.execute(f"SELECT SUM(r.secs) FROM runs r JOIN batch_jobs j ON r.run_id=j.run_id "
                           f"WHERE r.batch_id IN ({q}) AND json_extract(j.params,'$._action')=?",
                           (*bids, a)).fetchone()[0] or 0
        gain = con.execute(
            f"SELECT SUM(CASE WHEN i.old_length IS NULL THEN 30 ELSE i.old_length-i.new_length END) "
            f"FROM improvements i JOIN batch_jobs j ON i.run_id=j.run_id "
            f"WHERE i.batch_id IN ({q}) AND json_extract(j.params,'$._action')=?", (*bids, a)).fetchone()[0] or 0
        out[a] = {"engine_hours": secs / 3600, "gain": gain, "gain_per_hour": gain / max(secs / 3600, 1e-3)}
    return out


def plan(con, cfg) -> tuple[list[dict], dict, str]:
    P = problems.ac_problems()
    best = db.best_lengths(con)
    status = {r["problem_id"]: dict(r) for r in con.execute("SELECT * FROM problem_status")}
    tried = {p for p in status if p.startswith("ac-")}
    last_action = {}
    for r in con.execute("SELECT r.problem_id, json_extract(j.params,'$._action') a, r.strategy FROM runs r "
                         "JOIN batch_jobs j ON r.run_id=j.run_id ORDER BY r.run_id"):
        last_action.setdefault(r["problem_id"], []).append((r["a"], r["strategy"]))

    def tot(p):
        return len(P[p]["r0"]) + len(P[p]["r1"])

    pools = {
        "cover": sorted((p for p in P if p not in tried), key=lambda p: (tot(p), p)),
        "escalate": sorted((p for p in P if p in tried and p not in best),
                           key=lambda p: (status[p]["attempts"], tot(p))),
        "bidir": sorted((p for p in best if p.startswith("ac-") and best[p] <= cfg["bidir_max_len"]
                         and not status.get(p, {}).get("optimal")
                         and not any(a == "bidir" for a, _ in last_action.get(p, []))),
                        key=lambda p: best[p]),
        "polish": sorted((p for p in best if p.startswith("ac-")
                          and not any(a == "polish" for a, _ in last_action.get(p, []))
                          and not status.get(p, {}).get("optimal")), key=lambda p: -best[p]),
        "resolve": sorted((p for p in best if p.startswith("ac-") and not status.get(p, {}).get("optimal")),
                          key=lambda p: (sum(1 for a, _ in last_action.get(p, []) if a == "resolve"), -best[p])),
    }
    yields = action_yield(con)
    # weight = analyst weight x (1 + normalized yield); unexplored actions get a bonus (UCB-style)
    raw = {}
    gmax = max([y["gain_per_hour"] for y in yields.values()] or [1]) or 1
    for a, w in cfg["action_weights"].items():
        if not pools.get(a):
            continue
        y = yields.get(a)
        bonus = 1.0 if y is None else 0.25 / math.sqrt(1 + y["engine_hours"])
        raw[a] = w * (0.5 + (y["gain_per_hour"] / gmax if y else 0.5) + bonus)
    total_w = sum(raw.values()) or 1
    n = cfg["batch_jobs"]
    alloc = {a: max(1, round(n * w / total_w)) for a, w in raw.items()}

    jobs, notes = [], []
    label = f"ctl|{db.now()}"
    for a, k in alloc.items():
        chosen = pools[a][:k]
        for p in chosen:
            if a == "cover":
                preset = cfg["cover_preset"]
            elif a == "escalate":
                rung = min(status[p]["attempts"], len(cfg["ladder"]) - 1)
                preset = cfg["ladder"][rung]
            elif a == "bidir":
                preset = "bidir"
            elif a == "polish":
                preset = "polish"
            else:
                n_prev = sum(1 for x, _ in last_action.get(p, []) if x == "resolve")
                preset = cfg["resolve_presets"][n_prev % len(cfg["resolve_presets"])]
            params = dict(loop.PRESETS[preset])
            params.update(cfg["preset_overrides"].get(preset, {}))
            params["_action"] = a
            jobs.append({"problem_id": p, "strategy": preset, "params": params,
                         "seed": loop.job_seed(label, len(jobs), p)})
        notes.append(f"{a}: {len(chosen)} jobs (pool {len(pools[a])}, weight {raw[a]:.2f}"
                     + (f", yield {yields[a]['gain_per_hour']:.1f}/h over {yields[a]['engine_hours']:.2f}h"
                        if a in yields else ", unexplored") + ")")
    solved = sum(1 for p in best if p.startswith("ac-"))
    reasoning = (f"State: {solved}/{len(P)} solved, {len(pools['cover'])} never attempted, "
                 f"{len(pools['escalate'])} attempted but unsolved.\n"
                 "Hypothesis: allocate effort to the action types with the highest verified gain per "
                 "engine-hour (new solve = 30, improvement = moves saved), keeping an exploration bonus for "
                 "rarely-tried actions; unsolved problems climb the escalation ladder one rung per attempt.\n"
                 + "\n".join(notes))
    return jobs, {"actions": alloc, "yields": yields, "config": cfg}, reasoning


def run_loop(con, iterations=1, threads=None):
    loop.resume_all(con, threads=threads)
    for it in range(iterations):
        cfg = load_config()
        jobs, meta, reasoning = plan(con, cfg)
        if not jobs:
            print("controller: nothing to do")
            return
        print(reasoning, flush=True)
        db.add_insight(con, "controller", "plan", f"plan for batch ({len(jobs)} jobs)",
                       {"reasoning": reasoning, "actions": meta["actions"]})
        macros = mining.MACROS_PATH if cfg["use_macros"] and mining.MACROS_PATH.exists() else None
        from .model import MODEL_PATH
        model = MODEL_PATH if cfg["use_model"] and MODEL_PATH.exists() else None
        # job params need a model if any preset scores with it
        t0 = time.time()
        bid = db.create_batch(con, "controller", meta, jobs)
        stats = loop.run_batch(con, bid, threads=threads, macros=macros, model=model)
        review(con, bid, stats, time.time() - t0, cfg)


def review(con, bid, stats, secs, cfg):
    done = con.execute("SELECT COUNT(*) FROM batches WHERE status='done'").fetchone()[0]
    res = None
    if cfg["mine_every"] and done % cfg["mine_every"] == 0:
        res = mining.mine(con, batch_id=bid)
    if cfg["use_model"] and cfg["retrain_every"] and done % cfg["retrain_every"] == 0:
        from . import model
        try:
            model.train(con)
        except RuntimeError as e:
            print("model:", e)
    by_action = {}
    for r in con.execute("SELECT json_extract(j.params,'$._action') a, COUNT(*) n, SUM(r.solved) s "
                         "FROM runs r JOIN batch_jobs j ON r.run_id=j.run_id WHERE r.batch_id=? GROUP BY a", (bid,)):
        by_action[r["a"]] = {"jobs": r["n"], "solved": r["s"]}
    for r in con.execute("SELECT json_extract(j.params,'$._action') a, COUNT(*) n, "
                         "SUM(COALESCE(i.old_length - i.new_length, 0)) g FROM improvements i "
                         "JOIN batch_jobs j ON i.run_id=j.run_id WHERE i.batch_id=? GROUP BY a", (bid,)):
        by_action.setdefault(r["a"], {}).update(records=r["n"], moves_saved=r["g"])
    lines = [f"Batch {bid} finished in {secs / 60:.1f} min: " + ", ".join(f"{k}={v}" for k, v in stats.items())]
    for a, v in by_action.items():
        lines.append(f"  {a}: {v}")
    if res:
        st = res["strategies"]
        ranked = sorted(((v.get("solve_rate", 0), s) for s, v in st.items() if v.get("runs", 0) >= 20), reverse=True)
        if ranked:
            lines.append("Strategy solve rates: " + ", ".join(f"{s} {r:.0%}" for r, s in ranked))
    db.add_insight(con, "controller", "review", f"review of batch {bid}", {"reasoning": "\n".join(lines),
                                                                           "by_action": by_action})
    print("\n".join(lines), flush=True)
    if cfg["export_every"] and done % cfg["export_every"] == 0:
        export.write_snapshot(con)
        try:
            export.write_submission(con)
        except RuntimeError as e:  # never silently ship a rejected file
            db.add_insight(con, "controller", "alert", "submission export failed", str(e), bid)
            print("EXPORT FAILED:", e)
        dashboard.render(con)
