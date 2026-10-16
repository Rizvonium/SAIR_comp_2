"""Aut(F2)-orbit transport: orbit keys are automorphism invariants, and
transported paths are accepted by the official verifier."""
import random

from acsolver import official, problems, transport as T


def _random_aut(rng, n):
    phi = dict(T.ID)
    for _ in range(n):
        g = rng.choice(T.WH + T.PERM)
        phi = T.compose(g, phi)
    return phi


def _random_conj(rng, w):
    """A random conjugate of w (or of w^-1), freely reduced."""
    w = list(w)
    if rng.random() < 0.5:
        w = T.inv(w)
    k = rng.randrange(len(w) + 1)
    w = w[k:] + w[:k]
    c = [rng.choice(T.GENS) for _ in range(rng.randrange(3))]
    return T.fr(c + w + T.inv(c))


def test_orbit_key_invariant_under_random_automorphisms():
    rng = random.Random(7)
    P = problems.ac_problems()
    ids = sorted(P)
    for pid in rng.sample(ids, 40):
        r0, r1 = P[pid]["r0"], P[pid]["r1"]
        k = T.orbit_key(r0, r1)
        for _ in range(3):
            phi = _random_aut(rng, rng.randrange(1, 7))
            a, b = T.apply_aut(phi, r0), T.apply_aut(phi, r1)
            a, b = _random_conj(rng, a), _random_conj(rng, b)
            if rng.random() < 0.5:
                a, b = b, a
            assert T.orbit_key(a, b) == k, (pid, phi)


def test_orbit_key_separates_and_matches_tracked_forms():
    P = problems.ac_problems()
    p = P["ac-00001"]
    cf, maps = T.tracked_forms(p["r0"], p["r1"])
    assert T.key_str(cf) == T.orbit_key(p["r0"], p["r1"])
    for Tm, Ti in maps:  # every listed map sends the problem onto the canonical form
        assert T.canon_pair(T.apply_aut(Tm, p["r0"]), T.apply_aut(Tm, p["r1"])) == cf
        assert T.compose(Tm, Ti) == {1: (1,), 2: (2,)}
    # the trivial presentation and an AK(3)-type pair are in different orbits
    assert T.orbit_key([1], [2]) != T.orbit_key([1, 1, 1, -2, -2, -2, -2], [1, 2, 1, -2, -1, -2])


def _training_pairs(n):
    """(target, donor) pairs in one orbit, donors = training certificates."""
    keys = T.orbit_keys()
    idx = T.orbit_index(keys)
    train = problems.training_problems()
    pairs = []
    for k, ids in sorted(idx.items()):
        donors = sorted(d for d in ids if d in train)
        for q in sorted(ids):
            for d in donors:
                if d != q:
                    pairs.append((q, d))
                    break
    rng = random.Random(3)
    rng.shuffle(pairs)
    # mix pool and training targets when both exist
    pool_first = [p for p in pairs if p[0].startswith("ac-")][: n // 2 + 1]
    rest = [p for p in pairs if p not in pool_first]
    return (pool_first + rest)[:n]


def test_transported_training_paths_pass_official_verifier():
    allp = T.all_problems()
    train = problems.training_problems()
    pairs = _training_pairs(10)
    assert len(pairs) == 10
    items, ends = [], []
    built = []
    for q, d in pairs:
        cands = T.candidates_for(allp[q], [(d, allp[d], train[d]["known"])], max_maps=3)
        assert cands, (q, d)
        est, did, moves, st, phi = cands[0]
        built.append((q, moves, st))
        ends.append(st)
    fin = T._finish(ends, threads=2, endgame="default")
    for q, moves, st in built:
        assert st in fin, q
        items.append((q, moves + fin[st]))
    for (q, path), v in zip(items, [official.verify_one(q, p, problems.manifest_for(q)) for q, p in items]):
        assert v["ok"], (q, v)
        assert v["length"] == len(path)


def test_nielsen_finish_reaches_target():
    from acsolver.official import vcore
    rng = random.Random(11)
    for _ in range(20):
        phi = _random_aut(rng, rng.randrange(1, 9))
        st = (tuple(phi[1]), tuple(phi[2]))
        path = T.nielsen_finish(st)
        assert path is not None
        for m in path:
            st = vcore.apply_move(st, m)
        assert st == ((1,), (2,))
