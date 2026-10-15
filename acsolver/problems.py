"""Problem loading and cheap, interpretable problem features."""
from __future__ import annotations

import functools
import json

from . import official


@functools.lru_cache(maxsize=None)
def ac_problems() -> dict[str, dict]:
    """``{challenge_id: {"id", "r0", "r1"}}`` for the 10,115 scored AC problems."""
    out = {}
    for c in official.ac_challenges():
        r0, r1 = c["initial_relators"]
        out[c["challenge_id"]] = {"id": c["challenge_id"], "r0": r0, "r1": r1}
    return out


@functools.lru_cache(maxsize=None)
def training_problems() -> dict[str, dict]:
    """424 training instances keyed by ``ms-train-NNNN`` with known paths."""
    with open(official.TRAINING_424) as f:
        inst = json.load(f)["instances"]
    return {t["training_id"]: {"id": t["training_id"], "r0": t["initial_relators"][0],
                               "r1": t["initial_relators"][1], "known": t["moves"],
                               "n": t["n"], "w": t["w_vector"]} for t in inst}


def manifest_for(cid: str) -> str:
    return str(official.TRAIN_MANIFEST if cid.startswith("ms-train") else official.MANIFEST)


def _syllables(w):
    if not w:
        return 0
    s = 1 + sum(1 for a, b in zip(w, w[1:]) if abs(a) != abs(b))
    if len(w) > 1 and s > 1 and abs(w[0]) == abs(w[-1]):
        s -= 1
    return s


def _cyc_reduced_len(w):
    i, j = 0, len(w) - 1
    while i < j and w[i] == -w[j]:
        i += 1
        j -= 1
    return max(0, j - i + 1)


def _inv(w):
    return [-a for a in reversed(w)]


def _is_ms_relator(w):
    """n if w is x^-1 y^n x y^-(n+1) (n >= 1), else None."""
    if len(w) < 4 or w[0] != -1:
        return None
    k = 1
    while k < len(w) and w[k] == 2:
        k += 1
    n = k - 1
    if n >= 1 and k < len(w) and w[k] == 1 and w[k + 1:] == [-2] * (n + 1):
        return n
    return None


def ms_signature(r0, r1):
    """(n, index of the MS relator) if, up to cyclic rotation and inversion,
    one relator is the Miller–Schupp relator x^-1 y^n x y^-(n+1); else None.
    Prefers r1 (the usual position in this pool)."""
    for idx in (1, 0):
        r = (r0, r1)[idx]
        for w in (r, _inv(r)):
            for k in range(len(w)):
                n = _is_ms_relator(w[k:] + w[:k])
                if n:
                    return n, idx
    return None


def features(p: dict) -> dict:
    r0, r1 = p["r0"], p["r1"]
    ex = [sum(1 if a == 1 else -1 if a == -1 else 0 for a in r) for r in (r0, r1)]
    ey = [sum(1 if a == 2 else -1 if a == -2 else 0 for a in r) for r in (r0, r1)]
    return {
        "len0": len(r0), "len1": len(r1), "total": len(r0) + len(r1),
        "min_len": min(len(r0), len(r1)), "max_len": max(len(r0), len(r1)),
        "ex0": ex[0], "ey0": ey[0], "ex1": ex[1], "ey1": ey[1],
        "syl0": _syllables(r0), "syl1": _syllables(r1),
        "cyc0": _cyc_reduced_len(r0), "cyc1": _cyc_reduced_len(r1),
        "nx": sum(1 for a in r0 + r1 if abs(a) == 1), "ny": sum(1 for a in r0 + r1 if abs(a) == 2),
        "ms_n": (ms_signature(r0, r1) or (None,))[0],
        "ms_rel": (ms_signature(r0, r1) or (None, None))[1],
    }
