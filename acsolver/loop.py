"""Batch execution: engine -> shortening -> official verification -> DB.

A batch is a list of jobs (problem, strategy preset, params, seed) written
to the DB before anything runs.  ``run_batch`` executes the pending jobs
of a batch, streaming results from the engine and committing each one as
soon as the official verifier has judged it, so it can be killed and
resumed at any time.
"""
from __future__ import annotations

import hashlib
import json
import sys
import time

from . import db, engine, official, problems

# Named strategy presets.  Every key is an engine parameter (search.hpp /
# shorten.hpp); the controller may override any of them per job.
PRESETS: dict[str, dict] = {
    # exact optimum when the optimum is <= bidir_fwd + endgame radius
    "bidir": {"strategy": "bidir", "bidir_fwd": 6, "max_nodes": 6_000_000, "time_limit": 60},
    "gbfs": {"strategy": "gbfs", "max_nodes": 4_000_000, "time_limit": 20},
    "gbfs_lam": {"strategy": "gbfs", "lam": 0.25, "max_nodes": 6_000_000, "time_limit": 30},
    "gbfs_noise": {"strategy": "gbfs", "noise": 3.0, "max_nodes": 4_000_000, "time_limit": 20},
    "gbfs_deep": {"strategy": "gbfs", "max_nodes": 30_000_000, "time_limit": 240, "maxlen": 160},
    "gbfs_model": {"strategy": "gbfs", "w_len": 0.3, "w_model": 1.0, "max_nodes": 4_000_000, "time_limit": 30},
    "beam": {"strategy": "beam", "beam_width": 2000, "max_nodes": 20_000_000, "time_limit": 30},
    "beam_wide": {"strategy": "beam", "beam_width": 20000, "max_nodes": 40_000_000, "time_limit": 120},
    "beam_model": {"strategy": "beam", "beam_width": 2000, "w_len": 0.3, "w_model": 1.0, "time_limit": 30},
    "walk": {"strategy": "walk", "p_greedy": 0.85, "walk_len": 300, "time_limit": 10, "stop_first": 0,
             "max_nodes": 10**12},
    "anneal": {"strategy": "anneal", "T0": 1.5, "T1": 0.05, "walk_len": 2000, "time_limit": 10,
               "stop_first": 0, "max_nodes": 10**12},
    # re-shorten the stored best path with larger balls
    "polish": {"strategy": "polish", "d1": 5, "d2": 5, "ball_budget": 60_000_000, "shorten_time": 120},
}

# shortening parameters applied to every solve job unless overridden
SHORTEN_DEFAULT = {"d1": 4, "d2": 4, "ball_budget": 30_000_000, "shorten_time": 60}


def job_seed(batch_label: str, idx: int, pid: str) -> int:
    h = hashlib.sha256(f"{batch_label}|{idx}|{pid}".encode()).digest()
    return int.from_bytes(h[:7], "big")


def make_jobs(label: str, pids: list[str], preset: str, overrides: dict | None = None,
              repeats: int = 1) -> list[dict]:
    base = dict(PRESETS[preset])
    base.update(overrides or {})
    jobs = []
    for r in range(repeats):
        for pid in pids:
            i = len(jobs)
            jobs.append({"problem_id": pid, "strategy": preset, "params": base, "seed": job_seed(label, i, pid)})
    return jobs


def _problem(pid: str) -> dict:
    if pid.startswith("ms-train"):
        return problems.training_problems()[pid]
    return problems.ac_problems()[pid]


def run_batch(con, batch_id: int, threads: int | None = None, endgame="default", model=None, macros=None,
              verbose=True) -> dict:
    jobs = db.pending_jobs(con, batch_id)
    stats = {"jobs": len(jobs), "solved": 0, "new": 0, "improved": 0, "tied": 0, "worse": 0, "rejected": 0,
             "unsolved": 0}
    if not jobs:
        db.finish_batch(con, batch_id)
        return stats
    t0 = time.time()
    solve_recs, polish_recs, by_idx = [], [], {}
    for j in jobs:
        params = json.loads(j["params"])
        by_idx[j["job_idx"]] = (j, params)
        p = _problem(j["problem_id"])
        rec = {"id": j["problem_id"], "job": j["job_idx"], "r0": p["r0"], "r1": p["r1"], "seed": j["seed"]}
        if params.get("strategy") == "polish":
            b = db.best(con, j["problem_id"])
            if b is None:  # nothing to polish: mark done as unsolved
                db.record_run(con, batch_id=batch_id, job_idx=j["job_idx"], problem_id=j["problem_id"],
                              strategy="polish", params=params, seed=j["seed"], started_at=db.now(),
                              result={"solved": False, "note": "no_best"}, verdict=None)
                continue
            rec["path"] = json.loads(b["path"])
            rec["params"] = {k: v for k, v in params.items() if k != "strategy"}
            polish_recs.append(rec)
        else:
            rec["params"] = {**SHORTEN_DEFAULT, **params}
            solve_recs.append(rec)

    gopts = {"shorten": 1, "emit_raw": 1}
    cor = write_corridors(con)
    if cor:
        gopts["corridors"] = str(cor)
    if model:
        gopts["model"] = str(model)
    if macros:
        gopts["macros"] = str(macros)

    def results():
        if solve_recs:
            yield from engine.stream("solve", solve_recs, params=gopts, endgame=endgame, threads=threads)
        if polish_recs:
            for res in engine.stream("shorten", polish_recs, params={"corridors": str(cor)} if cor else {},
                                     endgame=endgame, threads=threads):
                if "error" in res:
                    yield res
                    continue
                res = {"id": res["id"], "job": res["job"], "solved": res.get("valid", False),
                       "path": res.get("path"), "raw_len": res.get("before"), "len": res.get("after"),
                       "nodes": 0, "secs": res.get("secs"), "note": "polish"}
                yield res

    done = 0
    for res in results():
        if "error" in res:
            print("engine error:", res, file=sys.stderr)
            continue
        j, params = by_idx[res["job"]]
        verdict = None
        if res.get("solved"):
            verdict = official.verify_one(j["problem_id"], res["path"], problems.manifest_for(j["problem_id"]))
        started = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(time.time() - (res.get("secs") or 0)))
        _, outcome = db.record_run(con, batch_id=batch_id, job_idx=j["job_idx"], problem_id=j["problem_id"],
                                   strategy=j["strategy"], params=params, seed=j["seed"], started_at=started,
                                   result=res, verdict=verdict)
        stats[outcome] += 1
        if res.get("solved") and outcome != "rejected":
            stats["solved"] += 1
        done += 1
        if verbose and (done % 50 == 0 or done == len(jobs)):
            el = time.time() - t0
            print(f"[batch {batch_id}] {done}/{len(jobs)} jobs, {el:.0f}s: "
                  + ", ".join(f"{k}={v}" for k, v in stats.items() if k != "jobs"), flush=True)
    if not db.pending_jobs(con, batch_id):
        db.finish_batch(con, batch_id)
    return stats


CORRIDORS = engine.DATA / "corridors.jsonl"


def write_corridors(con, max_raw_len: int = 4000):
    """All verified best paths plus the raw (pre-shortening) paths of
    verified runs, as {id, r0, r1, path} lines for the engine's corridor
    table.  Raw paths visit many more states, so they widen the corridor."""
    allp = {**problems.ac_problems(), **problems.training_problems()}
    rows = con.execute("SELECT problem_id, path FROM best_solutions").fetchall()
    raws = con.execute("SELECT problem_id, raw_path FROM runs WHERE verified=1 AND raw_path IS NOT NULL "
                       "AND raw_len <= ?", (max_raw_len,)).fetchall()
    if not rows:
        return None
    tmp = CORRIDORS.with_suffix(".tmp")
    with open(tmp, "w") as f:
        for pid, path in list(rows) + list(raws):
            p = allp.get(pid)
            if p:
                f.write(json.dumps({"id": pid, "r0": p["r0"], "r1": p["r1"], "path": json.loads(path)}) + "\n")
    tmp.replace(CORRIDORS)
    return CORRIDORS


def submit_batch(con, label: str, jobs: list[dict], config: dict | None = None, **kw) -> tuple[int, dict]:
    bid = db.create_batch(con, label, config or {}, jobs)
    return bid, run_batch(con, bid, **kw)


def resume_all(con, **kw):
    for b in db.unfinished_batches(con):
        print(f"resuming batch {b['batch_id']} ({b['label']})", flush=True)
        run_batch(con, b["batch_id"], **kw)
