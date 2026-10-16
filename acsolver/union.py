"""Path union: shortest path through the union of all known paths of a problem.

Every verified run leaves a path (and its raw, pre-shortening path).  Two
paths of the same problem often meet in a common state, so a prefix of one
and a suffix of the other may be shorter than either.  The union graph has
the states of all such paths as nodes and their moves (plus inverses) as
edges; a BFS from the start finds the best combination.  Results are
verified officially and stored like any other run (strategy ``union``).

    python3 -m acsolver union [--ids ...] [--extra FILE ...]
"""
from __future__ import annotations

import json
from collections import deque

from . import db, official, problems
from .official import vcore

INV = {0: 0, 1: 1, 2: 3, 3: 2, 4: 5, 5: 4, 6: 7, 7: 6, 8: 9, 9: 8, 10: 11, 11: 10, 12: 13, 13: 12}
TARGET = ((1,), (2,))


def known_paths(con, pid: str) -> list[list[int]]:
    rows = con.execute("SELECT path, raw_path FROM runs WHERE problem_id=? AND verified=1", (pid,)).fetchall()
    out = []
    for r in rows:
        for k in ("path", "raw_path"):
            if r[k]:
                out.append(json.loads(r[k]))
    b = con.execute("SELECT path FROM best_solutions WHERE problem_id=?", (pid,)).fetchone()
    if b:
        out.append(json.loads(b[0]))
    return out


def union_path(start, paths) -> list[int] | None:
    adj: dict = {}
    for p in paths:
        s = start
        for m in p:
            t = vcore.apply_move(s, m)
            adj.setdefault(s, {})[t] = m
            adj.setdefault(t, {})[s] = INV[m]
            s = t
    if TARGET not in adj:
        return None
    prev = {start: None}
    q = deque([start])
    while q:
        s = q.popleft()
        if s == TARGET:
            break
        for t, m in adj.get(s, {}).items():
            if t not in prev:
                prev[t] = (s, m)
                q.append(t)
    if TARGET not in prev:
        return None
    out, s = [], TARGET
    while prev[s] is not None:
        s, m = prev[s]
        out.append(m)
    return out[::-1]


def union_all(con, ids=None, extra: dict[str, list[list[int]]] | None = None, verbose=False) -> dict:
    P = problems.ac_problems()
    best = db.best_lengths(con)
    ids = ids or [p for p in best if p.startswith("ac-")]
    stats = {"problems": 0, "improved": 0, "moves_saved": 0}
    for pid in ids:
        paths = known_paths(con, pid) + (extra or {}).get(pid, [])
        if len(paths) < 2:
            continue
        stats["problems"] += 1
        start = (tuple(P[pid]["r0"]), tuple(P[pid]["r1"]))
        u = union_path(start, paths)
        if u is None or pid not in best or len(u) >= best[pid]:
            continue
        v = official.verify_one(pid, u)
        _, outcome = db.record_run(con, batch_id=None, job_idx=None, problem_id=pid, strategy="union",
                                   params={"paths": len(paths)}, seed=0, started_at=db.now(),
                                   result={"solved": True, "path": u, "note": "union"}, verdict=v)
        if outcome == "improved":
            stats["improved"] += 1
            stats["moves_saved"] += best[pid] - len(u)
            if verbose:
                print(f"union {pid}: {best[pid]} -> {len(u)}", flush=True)
    return stats


def main(argv):
    import argparse
    ap = argparse.ArgumentParser(prog="acsolver union")
    ap.add_argument("--ids", nargs="*")
    ap.add_argument("--extra", nargs="*", default=[], help="TXT files with more paths (id: [moves])")
    a = ap.parse_args(argv)
    extra: dict[str, list[list[int]]] = {}
    for f in a.extra:
        for line in open(f):
            if ":" in line and not line.startswith("#"):
                cid, _, mv = line.partition(":")
                extra.setdefault(cid.strip(), []).append(json.loads(mv.split("#")[0]))
    print(union_all(db.connect(), a.ids, extra, verbose=True))
    return 0
