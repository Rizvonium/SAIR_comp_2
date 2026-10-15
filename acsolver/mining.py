"""Insight mining over stored runs and verified best paths.

Produces (all stored as rows in ``insights`` and as results/insights.md):
  * frequent move n-grams in best paths -> macro-move candidates
    (written to data/macros.jsonl for the engine's --macros option)
  * solve rate and path length by problem features / families
  * relator-length profiles of best paths (how high before it shrinks)
  * strategy/parameter effectiveness (who finds the records)
"""
from __future__ import annotations

import collections
import json
import statistics

from . import db, official, problems
from .official import vcore

INV = [0, 1, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12]
MACROS_PATH = official.ROOT / "data" / "macros.jsonl"
REPORT = official.ROOT / "results" / "insights.md"


def _best_paths(con):
    return {r["problem_id"]: json.loads(r["path"])
            for r in con.execute("SELECT problem_id, path FROM best_solutions WHERE problem_id LIKE 'ac-%'")}


def ngrams(paths: dict, nmin=2, nmax=6, top=40):
    out = {}
    for n in range(nmin, nmax + 1):
        c = collections.Counter()
        for p in paths.values():
            seen = set()
            for i in range(len(p) - n + 1):
                g = tuple(p[i:i + n])
                if any(g[k + 1] == INV[g[k]] for k in range(n - 1)):
                    continue
                c[g] += 1
                seen.add(g)
        out[n] = c.most_common(top)
    return out


def select_macros(grams: dict, k=24, min_count=20):
    """Macro score = occurrences x (n-1): moves saved per use in search depth."""
    cands = []
    for n, lst in grams.items():
        if n < 3:
            continue
        for g, cnt in lst:
            if cnt >= min_count:
                cands.append((cnt * (n - 1), list(g), cnt))
    cands.sort(reverse=True)
    chosen, keys = [], set()
    for score, g, cnt in cands:
        # skip macros that are a sub-sequence of an already chosen one
        s = " ".join(map(str, g))
        if any(s in k_ for k_ in keys):
            continue
        keys.add(s)
        chosen.append({"moves": g, "count": cnt, "score": score})
        if len(chosen) >= k:
            break
    return chosen


def profile(r0, r1, path):
    s = (tuple(r0), tuple(r1))
    lens = [len(r0) + len(r1)]
    for m in path:
        s = vcore.apply_move(s, m)
        lens.append(len(s[0]) + len(s[1]))
    return lens


def length_profiles(paths: dict):
    P = problems.ac_problems()
    ratios, peak_pos, resampled = [], [], [[] for _ in range(21)]
    for pid, path in paths.items():
        p = P[pid]
        lens = profile(p["r0"], p["r1"], path)
        peak = max(lens)
        ratios.append(peak / lens[0])
        peak_pos.append(lens.index(peak) / max(1, len(lens) - 1))
        for k in range(21):
            resampled[k].append(lens[round(k * (len(lens) - 1) / 20)] / lens[0])
    if not ratios:
        return {}
    return {
        "n": len(ratios),
        "peak_over_initial_mean": statistics.mean(ratios),
        "peak_over_initial_quantiles": statistics.quantiles(ratios, n=10) if len(ratios) > 10 else ratios,
        "frac_paths_growing": sum(1 for r in ratios if r > 1.0) / len(ratios),
        "peak_position_mean": statistics.mean(peak_pos),
        "mean_profile_relative": [round(statistics.mean(c), 3) for c in resampled],
    }


def by_feature(con, paths: dict):
    P = problems.ac_problems()
    rows = collections.defaultdict(lambda: {"n": 0, "solved": 0, "lens": []})
    fam = collections.defaultdict(lambda: {"n": 0, "solved": 0, "lens": []})
    for pid, p in P.items():
        f = problems.features(p)
        b = f["total"] // 4 * 4
        key = f"{b:02d}-{b + 3:02d}"
        for d, k in ((rows, key), (fam, f["family"])):
            d[k]["n"] += 1
            if pid in paths:
                d[k]["solved"] += 1
                d[k]["lens"].append(len(paths[pid]))

    def summarize(d):
        return {k: {"n": v["n"], "solved": v["solved"], "rate": round(v["solved"] / v["n"], 3),
                    "mean_len": round(statistics.mean(v["lens"]), 2) if v["lens"] else None}
                for k, v in sorted(d.items())}
    return {"by_total_length": summarize(rows), "by_family": summarize(fam)}


HARD_FEATURES = ["total", "min_len", "max_len", "syl0", "syl1", "nx", "ny", "ex0", "ey0", "ex1", "ey1",
                 "cyc0", "cyc1", "ms_n"]


def hardness_model(con, min_attempts=1):
    """Logistic regression solved ~ features over attempted problems.
    Returns standardized coefficients (positive = easier) and accuracy."""
    import numpy as np
    P = problems.ac_problems()
    best = db.best_lengths(con)
    rows = [r["problem_id"] for r in con.execute("SELECT problem_id FROM problem_status WHERE attempts >= ? "
                                                  "AND problem_id LIKE 'ac-%'", (min_attempts,))]
    if len(rows) < 200:
        return {}
    X, y = [], []
    for pid in rows:
        f = problems.features(P[pid])
        X.append([float(abs(f[k])) if f[k] is not None else 0.0 for k in HARD_FEATURES]
                 + [1.0 if f["ms_n"] else 0.0])
        y.append(1.0 if pid in best else 0.0)
    X, y = np.array(X), np.array(y)
    mu, sd = X.mean(0), X.std(0) + 1e-9
    Z = np.hstack([(X - mu) / sd, np.ones((len(X), 1))])
    w = np.zeros(Z.shape[1])
    for _ in range(3000):
        p = 1 / (1 + np.exp(-Z @ w))
        w -= 0.1 * (Z.T @ (p - y) / len(y) + 1e-3 * np.r_[w[:-1], 0])
    acc = float((((Z @ w) > 0) == (y > 0.5)).mean())
    names = HARD_FEATURES + ["has_ms_relator"]
    coef = sorted(zip(names, w[:-1].tolist()), key=lambda t: -abs(t[1]))
    return {"n": len(y), "solve_rate": float(y.mean()), "accuracy": acc,
            "base_accuracy": float(max(y.mean(), 1 - y.mean())),
            "coefficients": [(k, round(v, 3)) for k, v in coef]}


def strategy_stats(con):
    out = {}
    for r in con.execute(
            "SELECT strategy, COUNT(*) n, SUM(solved) s, AVG(secs) t, AVG(CASE WHEN solved THEN path_len END) L "
            "FROM runs GROUP BY strategy"):
        out[r["strategy"]] = {"runs": r["n"], "solved": r["s"] or 0, "solve_rate": round((r["s"] or 0) / r["n"], 3),
                              "mean_secs": round(r["t"] or 0, 2), "mean_len": round(r["L"] or 0, 2)}
    for r in con.execute("SELECT strategy, COUNT(*) n FROM best_solutions GROUP BY strategy"):
        out.setdefault(r["strategy"], {})["holds_records"] = r["n"]
    for r in con.execute("SELECT strategy, COUNT(*) n, SUM(COALESCE(old_length,0)-new_length) g FROM improvements "
                         "WHERE old_length IS NOT NULL GROUP BY strategy"):
        out.setdefault(r["strategy"], {}).update(improvements=r["n"], moves_saved=r["g"])
    # per-run gap to the current best: who is closest to the record?
    best = db.best_lengths(con)
    gaps = collections.defaultdict(list)
    for r in con.execute("SELECT problem_id, strategy, path_len FROM runs WHERE verified=1"):
        if r["problem_id"] in best:
            gaps[r["strategy"]].append(r["path_len"] - best[r["problem_id"]])
    for s, g in gaps.items():
        out.setdefault(s, {}).update(mean_gap_to_best=round(statistics.mean(g), 2),
                                     hits_record=round(sum(1 for x in g if x == 0) / len(g), 3))
    return out


def mine(con, verbose=False, batch_id=None) -> dict:
    paths = _best_paths(con)
    grams = ngrams(paths)
    macros = select_macros(grams)
    MACROS_PATH.parent.mkdir(exist_ok=True)
    with open(MACROS_PATH, "w") as f:
        for m in macros:
            f.write(json.dumps(m) + "\n")
    res = {
        "solved": len(paths),
        "total_moves": sum(len(p) for p in paths.values()),
        "length_hist": dict(sorted(collections.Counter(len(p) for p in paths.values()).items())),
        "move_freq": dict(sorted(collections.Counter(m for p in paths.values() for m in p).items())),
        "top_ngrams": {n: [[list(g), c] for g, c in lst[:15]] for n, lst in grams.items()},
        "macros": macros,
        "profiles": length_profiles(paths),
        "features": by_feature(con, paths),
        "strategies": strategy_stats(con),
        "hardness": hardness_model(con),
    }
    db.add_insight(con, "miner", "stats", "insight mining", res, batch_id)
    notes = [dict(r) for r in con.execute(
        "SELECT created_at, author, title, body FROM insights WHERE author='analyst' ORDER BY id")]
    review = con.execute("SELECT body FROM insights WHERE author='controller' AND kind='review' "
                         "ORDER BY id DESC LIMIT 1").fetchone()
    res_for_report = dict(res, notes=notes,
                          review=json.loads(review[0]).get("reasoning") if review else None)
    write_report(res_for_report)
    if verbose:
        print(json.dumps({k: res[k] for k in ("solved", "total_moves", "profiles", "strategies")}, indent=1))
    return res


def write_report(res: dict):
    L = ["# Insight report (auto-generated by acsolver.mining)", ""]
    L.append(f"Solved: **{res['solved']}** / 10115, total moves {res['total_moves']}.")
    L.append("")
    L.append("## Path length histogram")
    L.append("| length | problems |\n|---:|---:|")
    for k, v in res["length_hist"].items():
        L.append(f"| {k} | {v} |")
    L.append("\n## Solve rate by initial total relator length")
    L.append("| total length | problems | solved | rate | mean best length |\n|---|---:|---:|---:|---:|")
    for k, v in res["features"]["by_total_length"].items():
        L.append(f"| {k} | {v['n']} | {v['solved']} | {v['rate']} | {v['mean_len']} |")
    L.append("\n## Families")
    L.append("| family | problems | solved | rate | mean best length |\n|---|---:|---:|---:|---:|")
    for k, v in res["features"]["by_family"].items():
        L.append(f"| {k} | {v['n']} | {v['solved']} | {v['rate']} | {v['mean_len']} |")
    pr = res["profiles"]
    if pr:
        L.append("\n## Relator-length profiles of best paths")
        L.append(f"- paths whose total length rises above the start: {pr['frac_paths_growing']:.1%}")
        L.append(f"- mean peak / initial total length: {pr['peak_over_initial_mean']:.2f}")
        L.append(f"- mean relative position of the peak: {pr['peak_position_mean']:.2f}")
        L.append(f"- mean profile (length / initial, 21 points along the path): {pr['mean_profile_relative']}")
    hm = res.get("hardness") or {}
    if hm:
        L.append("\n## What predicts solvability (logistic regression, standardized coefficients)")
        L.append(f"{hm['n']} attempted problems, solve rate {hm['solve_rate']:.1%}, in-sample accuracy "
                 f"{hm['accuracy']:.1%} (majority baseline {hm['base_accuracy']:.1%}). Positive = easier.")
        L.append("| feature | coefficient |\n|---|---:|")
        for k, v in hm["coefficients"]:
            L.append(f"| {k} | {v} |")
    L.append("\n## Macro-move candidates (frequent n-grams)")
    L.append("| moves | occurrences |\n|---|---:|")
    for m in res["macros"]:
        L.append(f"| {m['moves']} | {m['count']} |")
    L.append("\n## Strategies")
    L.append("| strategy | runs | solve rate | mean secs | mean len | records held | mean gap to best | hits record |")
    L.append("|---|---:|---:|---:|---:|---:|---:|---:|")
    for s, v in sorted(res["strategies"].items()):
        L.append(f"| {s} | {v.get('runs', '')} | {v.get('solve_rate', '')} | {v.get('mean_secs', '')} | "
                 f"{v.get('mean_len', '')} | {v.get('holds_records', 0)} | {v.get('mean_gap_to_best', '')} | "
                 f"{v.get('hits_record', '')} |")
    if res.get("review"):
        L.append("\n## Latest controller review")
        L.append("```\n" + res["review"] + "\n```")
    if res.get("notes"):
        L.append("\n## Analyst notes (hypotheses and conclusions)")
        for n in res["notes"]:
            L.append(f"- **{n['title']}** ({n['created_at']}): {n['body']}")
    REPORT.parent.mkdir(exist_ok=True)
    REPORT.write_text("\n".join(L) + "\n")
