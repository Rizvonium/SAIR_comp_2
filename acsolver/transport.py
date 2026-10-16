"""Aut(F2)-orbit transport: reuse a verified path of a donor problem P to
solve every problem Q in the same Aut(F2)-orbit.

Background.  If phi is an automorphism of F2 = <x, y> and (p0, p1) is a
balanced presentation, the AC moves commute with phi: inversion and
multiplication are word operations, and conjugation of a relator by a
letter g becomes conjugation by the word phi(g), i.e. |phi(g)| official
letter-conjugations.  So a verified path P -> (x, y) maps to a path
phi(P) -> (phi(x), phi(y)), and (phi(x), phi(y)) is a basis of F2, which
is AC-trivial by a short Nielsen walk.  Two problems are in the same orbit
iff their Whitehead-minimal canonical forms agree.

Orbit key (``orbit_key``).  Both relators are cyclically reduced and the
pair is taken up to rotation, inversion and order (``canon_pair``).  Greedy
Whitehead reduction (the 8 rank-2 type-II automorphisms b -> ba,
b -> a^-1 b) reaches the minimal total cyclic length; a BFS over the
length-preserving Whitehead moves enumerates the whole minimal level, and
the lexicographically least image under the 8 signed permutations is the
canonical form.  By Whitehead's theorem two pairs are in the same orbit
(of unordered pairs of conjugacy classes up to inversion) iff the forms
agree.  Keys are cached in ``data/orbit_keys.json``.

Transport (``transport_path``) for Q = phi(P) up to cyclic/inversion/order:
  prefix  conjugations (and possibly an inversion) taking Q's relators to
          exactly phi(p0), phi(p1)   (or swapped: then moves are mirrored)
  body    P's path; conjugation by g -> conjugations by the letters of
          phi(g) (last letter first), other moves unchanged
  suffix  basis (phi(x), phi(y)) -> (x, y) by the engine (GBFS), with a
          greedy Nielsen finish as fallback.
Several maps phi exist (stabiliser of the canonical form, plus inner
automorphisms); all are tried, shortest raw estimates first.  Candidates
are shortened with the engine and judged by the official verifier.

``transport_all`` runs over the whole pool (and the 424 training problems
as donors), records results with strategy 'transport' in a batch of its
own, and snowballs: every new record becomes a donor for its orbit.
"""
from __future__ import annotations

import collections
import json
import time
from pathlib import Path

from . import db, engine, official, problems
from .official import ROOT, vcore

CACHE = ROOT / "data" / "orbit_keys.json"
GENS = (1, -1, 2, -2)
ID = {1: (1,), 2: (2,)}
LETTER = {1: "x", -1: "X", 2: "y", -2: "Y"}
UNLETTER = {v: k for k, v in LETTER.items()}

# ---------------------------------------------------------------------------
# words and automorphisms (maps are dicts {1: word, 2: word} of tuples)


def fr(w):
    out = []
    for a in w:
        if out and out[-1] == -a:
            out.pop()
        else:
            out.append(a)
    return out


def inv(w):
    return [-a for a in reversed(w)]


def cyc(w):
    w = fr(w)
    i, j = 0, len(w) - 1
    while i < j and w[i] == -w[j]:
        i += 1
        j -= 1
    return w[i:j + 1]


def canon_word(w) -> tuple:
    """Least rotation of the cyclic reduction of w or of w^-1."""
    w = cyc(w)
    if not w:
        return ()
    best = None
    for v in (w, inv(w)):
        for k in range(len(v)):
            r = tuple(v[k:] + v[:k])
            if best is None or r < best:
                best = r
    return best


def canon_pair(u, v) -> tuple:
    a, b = canon_word(u), canon_word(v)
    return (a, b) if a <= b else (b, a)


def plen(p) -> int:
    return len(p[0]) + len(p[1])


def apply_aut(img, w) -> list:
    out = []
    for a in w:
        s = img[abs(a)]
        out.extend(s if a > 0 else inv(s))
    return fr(out)


def compose(f, g):
    """(f o g)(a) = f(g(a))."""
    return {1: tuple(apply_aut(f, g[1])), 2: tuple(apply_aut(f, g[2]))}


def _wh_maps():
    wh = []
    for a in (1, -1, 2, -2):
        b = 2 if abs(a) == 1 else 1
        wh.append({abs(a): (abs(a),), b: (b, a)})      # b -> b a
        wh.append({abs(a): (abs(a),), b: (-a, b)})     # b -> a^-1 b
    perm = []
    for sw in (False, True):
        for sx in (1, -1):
            for sy in (1, -1):
                perm.append({1: (sx * 1,), 2: (sy * 2,)} if not sw else {1: (sx * 2,), 2: (sy * 1,)})
    return wh, perm


WH, PERM = _wh_maps()


def aut_inverse(img):
    """Inverse of a Whitehead type-II map or a signed permutation."""
    if len(img[1]) == 1 and len(img[2]) == 1:
        out = {}
        for g in (1, 2):
            a = img[g][0]
            out[abs(a)] = (g if a > 0 else -g,)
        return out
    out = {}
    for g in (1, 2):
        w = img[g]
        if len(w) == 1:
            out[g] = tuple(w)
        elif w[0] == g:
            out[g] = (g, -w[1])       # b -> b a    =>  b -> b a^-1
        else:
            out[g] = (-w[0], g)       # b -> a^-1 b =>  b -> a b
    return out


def _img_pair(img, p):
    return canon_pair(apply_aut(img, list(p[0])), apply_aut(img, list(p[1])))


def _reduce(p, track=False):
    T, Ti = dict(ID), dict(ID)
    while True:
        best = None
        for img in WH:
            q = _img_pair(img, p)
            if plen(q) < plen(p) and (best is None or plen(q) < plen(best[0])):
                best = (q, img)
        if best is None:
            return p, T, Ti
        p = best[0]
        if track:
            T, Ti = compose(best[1], T), compose(Ti, aut_inverse(best[1]))


LEVEL_CAP = 20000


def _level(p, track=False):
    """All pairs of the minimal level reachable from p (with maps from p)."""
    L = plen(p)
    seen = {p: (dict(ID), dict(ID))}
    frontier = [p]
    while frontier and len(seen) < LEVEL_CAP:
        nf = []
        for q in frontier:
            G, Gi = seen[q]
            for img in WH:
                r = _img_pair(img, q)
                if plen(r) == L and r not in seen:
                    seen[r] = (compose(img, G), compose(Gi, aut_inverse(img))) if track else (None, None)
                    nf.append(r)
        frontier = nf
    return seen


def canonical_form(r0, r1) -> tuple:
    p, _, _ = _reduce(canon_pair(r0, r1))
    best = None
    for q in _level(p):
        for img in PERM:
            r = _img_pair(img, q)
            if best is None or r < best:   # all pairs of the level have equal length
                best = r
    return best


def tracked_forms(r0, r1, max_maps: int = 8):
    """(cf, [(T, Ti), ...]) with canon_pair(T(r0), T(r1)) == cf for every
    listed T (Ti = T^-1); several T differ by the stabiliser of cf."""
    p, T, Ti = _reduce(canon_pair(r0, r1), track=True)
    lvl = _level(p, track=True)
    cands = []
    for q, (G, Gi) in lvl.items():
        for img in PERM:
            r = _img_pair(img, q)
            cands.append((r, img, G, Gi))
    cf = min(c[0] for c in cands)
    maps, seen = [], set()
    for r, img, G, Gi in cands:
        if r != cf:
            continue
        Tq = compose(compose(img, G), T)
        k = (Tq[1], Tq[2])
        if k in seen:
            continue
        seen.add(k)
        maps.append((Tq, compose(Ti, compose(Gi, aut_inverse(img)))))
        if len(maps) >= max_maps:
            break
    return cf, maps


def key_str(cf) -> str:
    return "|".join("".join(LETTER[a] for a in w) for w in cf)


def _rel_str(r0, r1) -> str:
    return "".join(LETTER[a] for a in r0) + "|" + "".join(LETTER[a] for a in r1)


_KEYS: dict | None = None


def _load_cache() -> dict:
    global _KEYS
    if _KEYS is None:
        _KEYS = {}
        try:
            with open(CACHE) as f:
                _KEYS = json.load(f)
        except (OSError, ValueError):
            _KEYS = {}
    return _KEYS


def orbit_key(r0, r1) -> str:
    """Canonical Aut(F2)-orbit key of the presentation (cached in memory and,
    via ``orbit_keys``, on disk)."""
    cache = _load_cache()
    rs = _rel_str(r0, r1)
    k = cache.get(rs)
    if k is None:
        k = key_str(canonical_form(r0, r1))
        cache[rs] = k
    return k


def _save_cache():
    if _KEYS is None:
        return
    CACHE.parent.mkdir(parents=True, exist_ok=True)
    tmp = CACHE.with_suffix(".tmp")
    with open(tmp, "w") as f:
        json.dump(_KEYS, f, separators=(",", ":"))
    tmp.replace(CACHE)


def all_problems() -> dict[str, tuple]:
    out = {k: (v["r0"], v["r1"]) for k, v in problems.ac_problems().items()}
    out.update({k: (v["r0"], v["r1"]) for k, v in problems.training_problems().items()})
    return out


def orbit_keys(save: bool = True) -> dict[str, str]:
    """problem id -> orbit key for the 10,115 pool + 424 training problems."""
    cache = _load_cache()
    n0 = len(cache)
    out = {pid: orbit_key(r0, r1) for pid, (r0, r1) in all_problems().items()}
    if save and len(cache) != n0:
        _save_cache()
    return out


def orbit_index(keys: dict[str, str] | None = None) -> dict[str, list[str]]:
    keys = keys or orbit_keys()
    idx = collections.defaultdict(list)
    for pid, k in keys.items():
        idx[k].append(pid)
    return dict(idx)


# ---------------------------------------------------------------------------
# path construction

def conj_move(i: int, c: int) -> int:
    """Move id conjugating relator i by letter c (c r c^-1)."""
    return (6 if i == 0 else 10) + GENS.index(c)


def to_exact(q, g, i: int) -> list[int]:
    """Moves turning relator i from word q into exactly g (q ~cyc g^{+-1})."""
    moves, cur = [], list(q)

    def do(m):
        nonlocal cur
        st = (tuple(cur), ()) if i == 0 else ((), tuple(cur))
        cur = list(vcore.apply_move(st, m)[i])
        moves.append(m)

    while len(cur) > 1 and cur[0] == -cur[-1]:
        do(conj_move(i, -cur[0]))
    gc = cyc(g)
    k = (len(g) - len(gc)) // 2
    v = list(g[:k])

    def rot_index(a, b):
        n = len(a)
        if n != len(b):
            return None
        for s in range(max(1, n)):
            if a[s:] + a[:s] == b:
                return s
        return None

    s = rot_index(cur, gc)
    if s is None:
        do(i)  # inversion move (0 or 1)
        s = rot_index(cur, gc)
    if s is None:
        raise ValueError("relator not conjugate to target")
    n = len(cur)
    if s <= n - s:
        for _ in range(s):
            do(conj_move(i, -cur[0]))
    else:
        for _ in range(n - s):
            do(conj_move(i, cur[-1]))
    for c in reversed(v):
        do(conj_move(i, c))
    if cur != list(g):
        raise ValueError("to_exact failed")
    return moves


SWAP = {0: 1, 1: 0, 2: 4, 3: 5, 4: 2, 5: 3}
for _k in range(4):
    SWAP[6 + _k] = 10 + _k
    SWAP[10 + _k] = 6 + _k


def strip_inner(phi):
    """Compose phi with an inner automorphism so that phi(x), phi(y) do not
    share a conjugating prefix (shorter body and suffix, same orbit map)."""
    a, b = list(phi[1]), list(phi[2])
    while len(a) > 1 and len(b) > 1 and a[0] == b[0] and a[-1] == -a[0] and b[-1] == -b[0]:
        a, b = a[1:-1], b[1:-1]
    return {1: tuple(a), 2: tuple(b)}


def transport_path(Q, P, path, phi):
    """Official moves taking Q to (phi(x), phi(y)) along the image of P's path.

    Q, P: (r0, r1); phi maps P to Q up to rotation/inversion/order.
    Returns (moves, end_state)."""
    p = [list(P[0]), list(P[1])]
    M = list(path)
    im = [apply_aut(phi, p[0]), apply_aut(phi, p[1])]
    if not (canon_word(Q[0]) == canon_word(im[0]) and canon_word(Q[1]) == canon_word(im[1])):
        M = [SWAP[m] for m in M]
        im = [im[1], im[0]]
        swapped = True
    else:
        swapped = False
    if not (canon_word(Q[0]) == canon_word(im[0]) and canon_word(Q[1]) == canon_word(im[1])):
        raise ValueError("phi does not map P onto Q")
    pre = to_exact(Q[0], im[0], 0) + to_exact(Q[1], im[1], 1)
    body = []
    for m in M:
        if m <= 5:
            body.append(m)
        else:
            i = 0 if m <= 9 else 1
            g = GENS[(m - 6) % 4]
            w = phi[abs(g)] if g > 0 else inv(phi[abs(g)])
            body += [conj_move(i, c) for c in reversed(w)]
    st = (tuple(Q[0]), tuple(Q[1]))
    for m in pre + body:
        st = vcore.apply_move(st, m)
    # the endpoint is the image of the target (x, y) (swapped if mirrored)
    exp = (tuple(phi[1]), tuple(phi[2])) if not swapped else (tuple(phi[2]), tuple(phi[1]))
    if (tuple(fr(exp[0])), tuple(fr(exp[1]))) != st:
        raise ValueError("transport endpoint mismatch")
    return pre + body, st


_LEFT = [[0, 3, 0], [0, 2, 0], [1, 5, 1], [1, 4, 1]]


def nielsen_finish(st, max_steps: int = 400):
    """Greedy Nielsen reduction of a basis state to length 2, then a short
    canonical finish; returns moves to (x, y) or None."""
    path = []
    for _ in range(max_steps):
        if len(st[0]) + len(st[1]) <= 2:
            break
        best = None
        for seq in [[2], [3], [4], [5]] + _LEFT:
            t = st
            for m in seq:
                t = vcore.apply_move(t, m)
            L = len(t[0]) + len(t[1])
            if best is None or L < best[0]:
                best = (L, seq, t)
        if best[0] >= len(st[0]) + len(st[1]):
            return None
        path += best[1]
        st = best[2]
    # length-2 basis: letters of both generators; BFS over 14 moves to (x, y)
    start = st
    seen = {start: []}
    frontier = [start]
    for _ in range(8):
        nf = []
        for s in frontier:
            if s == ((1,), (2,)):
                return path + seen[s]
            for m in range(14):
                t = vcore.apply_move(s, m)
                if len(t[0]) + len(t[1]) <= 4 and t not in seen:
                    seen[t] = seen[s] + [m]
                    nf.append(t)
        frontier = nf
    for s in frontier:
        if s == ((1,), (2,)):
            return path + seen[s]
    return None


# ---------------------------------------------------------------------------
# pool-level solver

def _donor_paths(con) -> dict[str, list[list[int]]]:
    """Every verified path: DB best solutions + published training certificates."""
    out = collections.defaultdict(list)
    for r in con.execute("SELECT problem_id, path FROM best_solutions"):
        out[r[0]].append(json.loads(r[1]))
    for pid, t in problems.training_problems().items():
        if t["known"] not in out[pid]:
            out[pid].append(list(t["known"]))
    return out


def _last_state(con) -> int:
    row = con.execute("SELECT body FROM insights WHERE author='transport' AND kind='state' "
                      "ORDER BY id DESC LIMIT 1").fetchone()
    if not row:
        return 0
    try:
        return int(json.loads(row[0]).get("last_improvement_id", 0))
    except (ValueError, AttributeError):
        return 0


def candidates_for(Q, donors, max_maps: int = 6):
    """Yield (estimate, donor_id, moves, end_state, phi) for problem Q from
    donors = [(donor_id, (r0, r1), path)], all in Q's orbit."""
    cfQ, mapsQ = tracked_forms(*Q, max_maps=max_maps)
    tf_cache = {}
    out = []
    for did, P, path in donors:
        key = (tuple(P[0]), tuple(P[1]))
        if key not in tf_cache:
            tf_cache[key] = tracked_forms(*P, max_maps=1)
        cfP, mapsP = tf_cache[key]
        if cfP != cfQ:
            continue
        TP = mapsP[0][0]
        phis, seen = [], set()
        for TQ, TQi in mapsQ:
            for phi in (compose(TQi, TP), strip_inner(compose(TQi, TP))):
                k = (phi[1], phi[2])
                if k not in seen:
                    seen.add(k)
                    phis.append(phi)
        for phi in phis:
            try:
                moves, st = transport_path(Q, P, path, phi)
            except ValueError:
                continue
            est = len(moves) + 2 * (len(st[0]) + len(st[1]))
            out.append((est, did, moves, st, phi))
    out.sort(key=lambda c: c[0])
    return out


def _finish(states: list[tuple], threads: int, endgame) -> dict[tuple, list[int]]:
    """Suffix paths basis -> (x, y) for the distinct end states."""
    res = {}
    todo = []
    for s in set(states):
        if s == ((1,), (2,)):
            res[s] = []
        else:
            todo.append(s)
    recs = [{"id": str(i), "r0": list(s[0]), "r1": list(s[1])} for i, s in enumerate(todo)]
    if recs:
        for r in engine.stream("solve", recs, params={"strategy": "gbfs", "max_nodes": 300000, "time_limit": 5},
                               endgame=endgame, threads=threads):
            if r.get("solved"):
                res[todo[int(r["id"])]] = r["path"]
    for s in todo:
        if s not in res:
            nf = nielsen_finish(s)
            if nf is not None:
                res[s] = nf
    return res


def _targets(idx, orbits, donors_all, best, pool, allp, improve, max_donors, skip):
    """[(q, [(donor_id, (r0, r1), path), ...])] for the given orbits."""
    targets = []
    for k in orbits:
        ids = idx.get(k, [])
        donor_ids = [d for d in ids if d in donors_all]
        if not donor_ids:
            continue
        for q in ids:
            if q not in pool or (q in best and not improve):
                continue
            ds = []
            for d in donor_ids:
                if d == q:
                    continue
                for path in donors_all[d]:
                    # a donor can only help a solved target if its path is shorter
                    if q in best and len(path) >= best[q]:
                        continue
                    ds.append((len(path), d, path))
            if ds:
                ds.sort(key=lambda t: t[0])
                ds = ds[:max_donors]
                # skip a target already tried with the same record and the same donors
                sig = json.dumps([best.get(q, -1), [[n, d] for n, d, _ in ds]])
                if skip.get(q) == sig:
                    continue
                targets.append((q, [(d, allp[d], p) for _, d, p in ds], sig))
    targets.sort(key=lambda t: (t[0] in best, t[0]))
    return targets


def _load_attempts(con) -> dict[str, str]:
    con.execute("CREATE TABLE IF NOT EXISTS transport_attempts (problem_id TEXT PRIMARY KEY, sig TEXT NOT NULL,"
                " at TEXT)")
    return {r[0]: r[1] for r in con.execute("SELECT problem_id, sig FROM transport_attempts")}


def _save_attempts(con, rows):
    with con:
        con.executemany("INSERT OR REPLACE INTO transport_attempts(problem_id, sig, at) VALUES (?,?,?)",
                        [(q, sig, db.now()) for q, sig in rows])


# measured on the pool: shortening keeps >= ~0.39 of a transported raw path,
# so a candidate whose raw estimate is far above the record cannot improve it
IMPROVE_RATIO = 0.35


def _process_chunk(con, chunk, best, allp, *, max_maps, keep, shorten_quick, shorten_final, threads,
                   endgame, stats, batch):
    """Build, shorten, verify and record the candidates of one chunk of
    targets.  Returns the ids that got a new or better record."""
    cands = {}
    for q, ds, _sig in chunk:
        cs =candidates_for(allp[q], ds, max_maps=max_maps)
        if q in best:
            cs = [c for c in cs if c[0] * IMPROVE_RATIO < best[q]]
        if cs:
            cands[q] = cs[:keep]
    stats["targets"] += len(cands)
    stats["candidates"] += sum(len(c) for c in cands.values())
    if not cands:
        return []
    fin = _finish([c[3] for cs in cands.values() for c in cs], threads, endgame)
    recs, meta = [], {}
    for q, cs in cands.items():
        for j, (est, did, moves, st, phi) in enumerate(cs):
            if st not in fin:
                stats["no_suffix"] += 1
                continue
            raw = moves + fin[st]
            rid = f"{q}#{j}"
            meta[rid] = (q, did, raw, phi)
            recs.append({"id": rid, "r0": allp[q][0], "r1": allp[q][1], "path": raw, "params": shorten_quick})
    # quick shortening of every candidate, keep the best per target
    quick = {}
    for r in engine.stream("shorten", recs, endgame=endgame, threads=threads):
        if r.get("valid"):
            quick[r["id"]] = (r["path"], r.get("secs") or 0)
    winners = {}
    for rid, (path, _) in quick.items():
        q = meta[rid][0]
        if q not in winners or len(path) < len(quick[winners[q]][0]):
            winners[q] = rid
    # final shortening of the winners that can still matter
    recs2 = []
    for q, rid in winners.items():
        if q in best and len(quick[rid][0]) * 0.6 >= best[q]:
            continue
        recs2.append({"id": rid, "r0": allp[q][0], "r1": allp[q][1], "path": quick[rid][0],
                      "params": shorten_final})
    final = {}
    for r in engine.stream("shorten", recs2, endgame=endgame, threads=threads):
        if r.get("valid"):
            final[r["id"]] = (r["path"], quick[r["id"]][1] + (r.get("secs") or 0))
    rids = list(final)
    items = [(meta[rid][0], final[rid][0]) for rid in rids]
    verdicts = official.verify_many(items) if items else []
    rows = []
    for rid, (q, path), v in zip(rids, items, verdicts):
        if not v.get("ok"):
            stats["rejected"] += 1
            continue
        stats["verified"] += 1
        if q in best and v["length"] >= best[q]:
            stats["no_gain"] += 1
            continue
        _, did, raw, phi = meta[rid]
        params = {"_action": "transport", "donor": did, "phi": [key_str([phi[1]]), key_str([phi[2]])],
                  "raw_len": len(raw)}
        rows.append(({"problem_id": q, "strategy": "transport", "params": params, "seed": 0},
                     path, raw, v, final[rid][1]))
    if not rows:
        return []
    if batch["id"] is None:
        batch["id"] = db.create_batch(con, "transport", {"actions": {"transport": 0}}, [])
    bid = batch["id"]
    base = con.execute("SELECT COALESCE(MAX(job_idx), -1) + 1 FROM batch_jobs WHERE batch_id=?",
                       (bid,)).fetchone()[0]
    with con:
        con.executemany(
            "INSERT INTO batch_jobs(batch_id, job_idx, problem_id, strategy, params, seed) VALUES (?,?,?,?,?,?)",
            [(bid, base + i, row[0]["problem_id"], row[0]["strategy"], json.dumps(row[0]["params"], sort_keys=True),
              0) for i, row in enumerate(rows)])
        n = con.execute("SELECT COUNT(*) FROM batch_jobs WHERE batch_id=?", (bid,)).fetchone()[0]
        con.execute("UPDATE batches SET n_jobs=?, config=? WHERE batch_id=?",
                    (n, json.dumps({"actions": {"transport": n}}), bid))
    gained = []
    for i, (j, path, raw, v, secs) in enumerate(rows):
        res = {"solved": True, "path": path, "raw_path": raw, "raw_len": len(raw), "secs": secs, "nodes": 0,
               "note": "transport from " + j["params"]["donor"]}
        _, outcome = db.record_run(con, batch_id=bid, job_idx=base + i, problem_id=j["problem_id"],
                                   strategy="transport", params=j["params"], seed=0, started_at=db.now(),
                                   result=res, verdict=v)
        if outcome in ("new", "improved"):
            stats[outcome] += 1
            if outcome == "improved":
                stats["moves_saved"] += best[j["problem_id"]] - v["length"]
            gained.append(j["problem_id"])
    return gained


def transport_all(con, *, only_changed: bool = False, improve: bool = True, max_donors: int = 6,
                  max_maps: int = 6, keep: int = 3, shorten_quick: dict | None = None,
                  shorten_final: dict | None = None, threads: int = 2, endgame="default",
                  max_rounds: int = 6, limit: int | None = None, chunk: int = 40,
                  time_budget: float | None = None, retry: bool = False, verbose: bool = True) -> dict:
    """Transport verified paths to every unsolved (and, with ``improve``,
    every improvable) pool problem that has a solved donor in its orbit.

    Per target: the ``max_donors`` shortest donor paths of the orbit x
    every orbit map (``max_maps`` stabiliser maps, each also with its inner
    part stripped) are built; the ``keep`` best raw estimates are shortened
    quickly, the best one again with the full shortener, and the official
    verifier's verdict is recorded (strategy 'transport', one batch per
    call) when the path is new or strictly shorter.  Chunks of ``chunk``
    targets are committed as they finish.  Repeats on the orbits of new
    records (snowball) for at most ``max_rounds`` rounds or ``time_budget``
    seconds.  ``only_changed``: start from orbits containing a problem
    whose record changed since the previous transport run (cheap enough
    to run after every batch).  A target is skipped when it was already
    tried with the same record and the same donor paths (table
    ``transport_attempts``), unless ``retry``."""
    t0 = time.time()
    shorten_quick = shorten_quick or {"d1": 2, "d2": 2, "ball_budget": 5_000_000, "shorten_time": 3}
    shorten_final = shorten_final or {"d1": 3, "d2": 3, "ball_budget": 20_000_000, "shorten_time": 15}
    keys = orbit_keys()
    idx = orbit_index(keys)
    allp = all_problems()
    pool = problems.ac_problems()
    stats = {"rounds": 0, "targets": 0, "candidates": 0, "no_suffix": 0, "verified": 0, "new": 0,
             "improved": 0, "moves_saved": 0, "rejected": 0, "no_gain": 0}
    last_imp = con.execute("SELECT COALESCE(MAX(id), 0) FROM improvements").fetchone()[0]
    if only_changed:
        since = _last_state(con)
        changed = {r[0] for r in con.execute("SELECT DISTINCT problem_id FROM improvements WHERE id > ?",
                                             (since,))}
        orbits = {keys[p] for p in changed if p in keys}
    else:
        orbits = set(idx)
    # target -> signature (record, donors) of its last attempt, persisted in the DB
    attempted = {} if retry else _load_attempts(con)
    if retry:
        _load_attempts(con)
    batch = {"id": None}
    out_of_time = False
    for rnd in range(max_rounds):
        donors_all = _donor_paths(con)
        best = db.best_lengths(con)
        targets = _targets(idx, orbits, donors_all, best, pool, allp, improve, max_donors, attempted)
        if limit:
            targets = targets[:limit]
        if not targets:
            break
        stats["rounds"] += 1
        gained = []
        for i in range(0, len(targets), chunk):
            part = targets[i:i + chunk]
            gained += _process_chunk(con, part, best, allp, max_maps=max_maps, keep=keep,
                                     shorten_quick=shorten_quick, shorten_final=shorten_final,
                                     threads=threads, endgame=endgame, stats=stats, batch=batch)
            _save_attempts(con, [(q, sig) for q, _, sig in part])
            attempted.update({q: sig for q, _, sig in part})
            if verbose:
                print(f"[transport] round {rnd + 1}: {min(i + chunk, len(targets))}/{len(targets)} targets, "
                      + ", ".join(f"{k}={v}" for k, v in stats.items()) + f" ({time.time() - t0:.0f}s)",
                      flush=True)
            if time_budget and time.time() - t0 > time_budget:
                out_of_time = True
                break
        if out_of_time or not gained:
            break
        # snowball: every new record is a donor for the rest of its orbit
        orbits = {keys[p] for p in gained}
    if batch["id"] is not None:
        db.finish_batch(con, batch["id"])
    stats["secs"] = round(time.time() - t0, 1)
    stats["batch_id"] = batch["id"]
    stats["complete"] = not out_of_time
    # an interrupted run keeps the old watermark so that the next run redoes the rest
    state = {"last_improvement_id": last_imp if not out_of_time else _last_state(con), **stats}
    db.add_insight(con, "transport", "state", "transport run", state, batch["id"])
    return stats


# ---------------------------------------------------------------------------
# statistics

def orbit_stats(con) -> dict:
    """Orbit statistics of the pool (+ training) and of the MS-1190 open classes."""
    from . import ms1190
    keys = orbit_keys()
    idx = orbit_index(keys)
    pool = problems.ac_problems()
    best = db.best_lengths(con)
    train = problems.training_problems()
    solved = set(best) | set(train)
    pool_orbits = collections.defaultdict(list)
    for pid in pool:
        pool_orbits[keys[pid]].append(pid)
    size_hist = collections.Counter(len(v) for v in pool_orbits.values())
    unsolved = [p for p in pool if p not in best]
    shared = [p for p in unsolved if any(d in solved and d != p for d in idx[keys[p]])]
    solved_orbits = sum(1 for k, ids in pool_orbits.items() if any(d in solved for d in idx[k]))
    classes = {}
    for cls, ids in sorted(ms1190.classes().items()):
        ks = collections.Counter(keys[i] for i in ids)
        classes[cls] = {
            "members": len(ids),
            "orbits": len(ks),
            "orbit_sizes_pool": sorted((len(pool_orbits[k]) for k in ks), reverse=True),
            "orbit_sizes_all": sorted((len(idx[k]) for k in ks), reverse=True),
            "solved_members": sum(1 for i in ids if i in best),
            "members_in_solved_orbit": sum(1 for i in ids if any(d in solved for d in idx[keys[i]])),
        }
    return {
        "pool_problems": len(pool),
        "orbits_pool": len(pool_orbits),
        "orbits_all": len(idx),
        "orbit_size_hist_pool": dict(sorted(size_hist.items())),
        "largest_orbits": sorted((len(v) for v in pool_orbits.values()), reverse=True)[:10],
        "orbits_with_training": sum(1 for k in pool_orbits if any(d in train for d in idx[k])),
        "orbits_with_solved": solved_orbits,
        "unsolved": len(unsolved),
        "unsolved_sharing_orbit_with_solved": len(shared),
        "ms1190_open_classes": classes,
    }
