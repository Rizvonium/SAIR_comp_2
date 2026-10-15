"""Map pool problems to MS-1190 metadata (status, reported AC-class).

The frozen MS encoding is r0 = x^-1 y^n x y^-(n+1), r1 = x w^-1 (both
freely reduced).  Pool problems are matched up to relator order, cyclic
rotation and inversion (the manifest guarantees uniqueness under these).
"""
from __future__ import annotations

import csv
import functools

from . import official, problems
from .official import vcore

CSV = official.TOOLS / "verifier" / "data" / "ms1190_metadata.csv"


def _inv(w):
    return [-a for a in reversed(w)]


def _canon_word(w):
    """Lexicographically least rotation of w or its inverse (cyclically reduced)."""
    w = list(vcore.free_reduce(w))
    while len(w) > 1 and w[0] == -w[-1]:
        w = w[1:-1]
    best = None
    for v in (w, _inv(w)):
        for k in range(max(1, len(v))):
            r = tuple(v[k:] + v[:k])
            if best is None or r < best:
                best = r
    return best or ()


def canon_pair(r0, r1):
    a, b = _canon_word(r0), _canon_word(r1)
    return (a, b) if a <= b else (b, a)


@functools.lru_cache(maxsize=None)
def metadata() -> list[dict]:
    with open(CSV) as f:
        rows = list(csv.DictReader(f))
    for r in rows:
        n = int(r["n"])
        w = [int(x) for x in r["w_vector"].split()]
        r["r0"] = list(vcore.free_reduce([-1] + [2] * n + [1] + [-2] * (n + 1)))
        r["r1"] = list(vcore.free_reduce([1] + _inv(w)))
    return rows


@functools.lru_cache(maxsize=None)
def pool_map() -> dict[str, dict]:
    """challenge_id -> MS-1190 row, for pool problems that are MS-1190 instances."""
    idx = {canon_pair(p["r0"], p["r1"]): pid for pid, p in problems.ac_problems().items()}
    out = {}
    for r in metadata():
        pid = idx.get(canon_pair(r["r0"], r["r1"]))
        if pid:
            out[pid] = r
    return out


def classes() -> dict[str, list[str]]:
    """reported_class -> pool challenge ids (open instances only carry classes)."""
    out: dict[str, list[str]] = {}
    for pid, r in pool_map().items():
        if r["reported_class"]:
            out.setdefault(r["reported_class"], []).append(pid)
    return out
