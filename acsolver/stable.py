"""Phase 2 (Stable AC): derive ``sac-`` solutions from verified AC paths.

At rank 2 without stabilizing, destabilization needs a relator that is a
single positive generator absent from the other relator, so the only
states with a stable finish are signed permutations of (x, y); their
minimal finishes are the official ``canonicalization_table`` of
stable_move_spec.json (cost 2-4).  For each AC path we take the cheapest
``i + cost(s_i)`` over its signed-permutation states — never longer than
the AC path + [16, 15], often shorter (e.g. (y, x) costs 2 here vs 5 + 2).
Every derived path is checked with the official verifier (``sac-`` IDs,
spec ``sac-r8-v1``) before it is written.
"""
from __future__ import annotations

import functools
import json

from . import official, problems
from .official import vcore

STABLE_SPEC = official.TOOLS / "verifier" / "data" / "stable_move_spec.json"
RESULTS = official.ROOT / "results"


@functools.lru_cache(maxsize=None)
def finishes() -> dict:
    with open(STABLE_SPEC) as f:
        rows = json.load(f)["canonicalization_table"]["rows"]
    return {tuple(tuple(r) for r in row["final_state"]): list(row["path"]) for row in rows}


def to_stable(r0, r1, path) -> list[int] | None:
    fin = finishes()
    s = (tuple(r0), tuple(r1))
    best = None
    for i in range(len(path) + 1):
        f = fin.get(s)
        if f is not None and (best is None or i + len(f) < len(best)):
            best = list(path[:i]) + f
        if i < len(path):
            s = vcore.apply_move(s, path[i])
    return best


def stable_bests(con) -> list[tuple[str, list[int], dict]]:
    """[(sac_id, moves, verdict)] for every AC best, officially verified."""
    P = problems.ac_problems()
    items = []
    for r in con.execute("SELECT problem_id, path FROM best_solutions WHERE problem_id LIKE 'ac-%' "
                         "ORDER BY problem_id"):
        p = P[r["problem_id"]]
        sp = to_stable(p["r0"], p["r1"], json.loads(r["path"]))
        if sp is not None:
            items.append(("s" + r["problem_id"], sp))
    verdicts = official.verify_many(items)
    return [(cid, mv, v) for (cid, mv), v in zip(items, verdicts)]


def write_stable_submission(con, outdir=RESULTS, check=True) -> dict:
    rows = [(cid, mv) for cid, mv, v in stable_bests(con) if v["ok"]]
    lines = [official.format_line(cid, mv) for cid, mv in rows]
    (outdir / "stable_submission.txt").write_text(
        "# SAIR ACC Discovery Track - Stable AC submission (derived from verified AC paths)\n"
        + "\n".join(lines) + "\n")
    parts = outdir / "stable_submission_parts"
    parts.mkdir(parents=True, exist_ok=True)
    for old in parts.glob("part_*.txt"):
        old.unlink()
    n = official.MAX_LINES_PER_FILE
    report = {"solutions": len(lines), "total_moves": sum(len(m) for _, m in rows), "parts": []}
    for k in range(0, len(lines), n):
        p = parts / f"part_{k // n + 1:02d}.txt"
        p.write_text("\n".join(lines[k:k + n]) + "\n")
        entry = {"file": p.name, "lines": len(lines[k:k + n])}
        if check:
            code, receipt = official.run_cli(p)
            bad = [r["challenge_id"] for r in receipt.get("results", []) if not r.get("ok")]
            entry.update(exit=code, failed=bad)
            if code != 0 or bad:
                raise RuntimeError(f"official verifier rejected {p}: {entry}")
        report["parts"].append(entry)
    (outdir / "stable_submission_report.json").write_text(json.dumps(report, indent=1))
    return report
