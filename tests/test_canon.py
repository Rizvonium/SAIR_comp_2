"""Canonical classes (engine/canon.hpp) and the cflood strategy.

* the class key is invariant under rotation, inversion, conjugation, relator
  swap and the 8 signed generator permutations, and equals an independent
  Python reference;
* the canonical component at cap L equals the class projection of the exact
  (official-move) component at cap L;
* cflood solves the hard MS-1190 'uncertified' sample, with paths accepted
  by the official verifier;
* corridor splicing through an automorphism + relator swap is exact.
"""
import json
import random
import subprocess
from pathlib import Path

import pytest

from acsolver import engine, official, problems
from acsolver.official import vcore

ROOT = Path(__file__).resolve().parent.parent
HARD = json.loads((ROOT / "scripts" / "hard_sample.json").read_text())
CODE = {1: 0, -1: 1, 2: 2, -2: 3}


def run(cmd, recs, *flags):
    engine.ensure_built()
    out = subprocess.run([str(engine.BIN), cmd, *flags], input="\n".join(json.dumps(r) for r in recs),
                         capture_output=True, text=True, check=True).stdout
    return [json.loads(l) for l in out.splitlines() if l.strip()]


# ---------------------------------------------------------------- reference
def inv(w):
    return tuple(-a for a in reversed(w))


def core(w):
    w = vcore.free_reduce(tuple(w))
    k = 0
    while 2 * k + 1 < len(w) and w[k] == -w[len(w) - 1 - k]:
        k += 1
    return w[k:len(w) - k]


def phi(ph, a):
    if ph & 1:
        a = a * 2 if a in (1, -1) else a // 2
    if (ph & 2) and a in (1, -1):
        a = -a
    if (ph & 4) and a in (2, -2):
        a = -a
    return a


def ref_key(r0, r1):
    """Independent reference: min over automorphisms of the sorted pair of
    (length, least rotation of the word or its inverse)."""
    def cyc(w):
        best = None
        for v in (w, inv(w)):
            cv = tuple(CODE[a] for a in v)
            for r in range(len(cv)):
                t = cv[r:] + cv[:r]
                best = t if best is None or t < best else best
        return best
    best = None
    for ph in range(8):
        a = cyc(tuple(phi(ph, x) for x in core(r0)))
        b = cyc(tuple(phi(ph, x) for x in core(r1)))
        k = tuple(sorted([(len(a), a), (len(b), b)]))
        best = k if best is None or k < best else best
    return "_".join("".join("xXyY"[c] for c in w) for _, w in best)


def rand_word(rng, n):
    return list(vcore.free_reduce(tuple(rng.choice([1, -1, 2, -2]) for _ in range(n))))


def test_key_invariance_and_reference():
    rng = random.Random(7)
    base, variants = [], []
    for _ in range(150):
        r0, r1 = rand_word(rng, rng.randint(1, 14)), rand_word(rng, rng.randint(1, 14))
        if not core(r0) or not core(r1):
            continue
        base.append({"r0": r0, "r1": r1})
        vs = []
        c0, c1 = list(core(r0)), list(core(r1))
        k = rng.randrange(len(c0))
        vs.append({"r0": c0[k:] + c0[:k], "r1": r1})                      # rotation
        vs.append({"r0": list(inv(r0)), "r1": r1})                         # inversion
        vs.append({"r0": r1, "r1": r0})                                    # relator swap
        g = rand_word(rng, rng.randint(1, 5))                              # conjugation
        vs.append({"r0": list(vcore.free_reduce(tuple(g) + tuple(r0) + inv(g))), "r1": r1})
        for ph in range(1, 8):                                             # signed permutations
            vs.append({"r0": [phi(ph, a) for a in r0], "r1": [phi(ph, a) for a in r1]})
        ph = rng.randrange(8)                                              # everything at once
        vs.append({"r0": [phi(ph, a) for a in inv(r1)], "r1": [phi(ph, a) for a in c0[k:] + c0[:k]]})
        variants.append(vs)
    keys = run("canon", base)
    flat = run("canon", [v for vs in variants for v in vs])
    i = 0
    for b, k, vs in zip(base, keys, variants):
        assert k["key"] == ref_key(b["r0"], b["r1"])
        assert k["total"] == len(core(b["r0"])) + len(core(b["r1"]))
        for _ in vs:
            assert flat[i]["key"] == k["key"]
            i += 1


@pytest.mark.parametrize("pid,cap", [("ac-00008", 18), ("ac-00008", 20), ("ac-00066", 20)])
def test_exact_vs_canonical_component(pid, cap):
    p = problems.ac_problems()[pid]
    (r,) = run("canon-xcheck", [{"r0": p["r0"], "r1": p["r1"]}], "--cap", str(cap))
    assert r["complete"]
    assert r["exact_not_in_canon"] == 0     # soundness: barrier lower bounds are proofs
    assert r["canon_not_in_exact"] == 0     # and nothing spurious
    assert r["exact_classes"] == r["canon_classes"]
    assert r["exact_states"] > 100 * r["canon_classes"]


@pytest.fixture(scope="module")
def trivial(tmp_path_factory):
    big = engine.default_trivial()
    if big is not None and int(big.stem.split("_c")[1]) >= 18:
        return big
    out = tmp_path_factory.mktemp("triv") / "trivial_c18.bin"
    subprocess.run([str(engine.BIN), "build-trivial", "--cap", "18", "--out", str(out), "--threads", "2"],
                   check=True, capture_output=True)
    return out


def test_trivial_table_sizes(tmp_path):
    engine.ensure_built()
    for cap, n in [(12, 1105), (14, 7374)]:
        out = tmp_path / f"t{cap}.bin"
        r = subprocess.run([str(engine.BIN), "build-trivial", "--cap", str(cap), "--out", str(out), "--threads", "2"],
                           check=True, capture_output=True, text=True)
        assert f"T_{cap}: {n} classes" in r.stderr


def test_cflood_solves_uncertified(trivial):
    P = problems.ac_problems()
    ids = HARD["ms1190_uncertified"][:10]
    recs = [{"id": i, "r0": P[i]["r0"], "r1": P[i]["r1"]} for i in ids]
    out = engine.run("solve", recs, params={"strategy": "cflood", "max_nodes": 300000, "time_limit": 60,
                                            "ccompact": 300000, "ctime": 4, "trivial": str(trivial),
                                            "shorten": 1, "d1": 3, "d2": 3, "shorten_time": 10},
                     threads=2)
    solved = [o for o in out if o.get("solved")]
    for o in out:
        assert "water" in o and "barrier_lb" in o and "fingerprint" in o
    verdicts = official.verify_many([(o["id"], o["path"]) for o in solved])
    ok = sum(bool(v["ok"]) for v in verdicts)
    assert all(v["ok"] for v in verdicts)
    assert ok >= 8, [(o["id"], o.get("note")) for o in out]


def test_cflood_barrier_lower_bound(trivial):
    # ac-00008 (greedy-failed, total 16) has no path with peak <= 22: the
    # flood exhausts the capped component and proves barrier_lb = cap + 1
    p = problems.ac_problems()["ac-00008"]
    (o,) = engine.run("solve", [{"id": "ac-00008", "r0": p["r0"], "r1": p["r1"]}],
                      params={"strategy": "cflood", "max_nodes": 2000000, "maxlen": 22, "trivial": str(trivial)},
                      threads=1)
    assert not o["solved"]
    assert o["barrier_lb"] == 23 and o["water"] == 22
    assert o["note"].startswith("exhausted")


def test_cflood_corridor_splice(tmp_path):
    """A corridor path stored for an automorphic, swapped, conjugated copy of
    a training problem: cflood (no trivial table) must hit its class at the
    start and splice through the transformed path."""
    T = problems.training_problems()
    k = "ms-train-0300"
    t = T[k]
    ph = 5  # swap x<->y and invert y
    g = [2, 1]
    s = (tuple(t["r0"]), tuple(t["r1"]))
    # exact copy: X = (phi(r1), phi(g r0 g^-1)); its path: transform the
    # known moves by phi and the relator swap, after undoing the conjugation
    X0 = [phi(ph, a) for a in t["r1"]]
    X1 = [phi(ph, a) for a in vcore.free_reduce(tuple(g) + tuple(t["r0"]) + inv(g))]
    rec = {"id": "fake-copy", "r0": X0, "r1": X1}
    # a solution of the copy: undo the conjugation of relator 1, follow the
    # known path transformed by phi and the relator swap, fix the last sign
    h = [phi(ph, a) for a in inv(g)]
    moves = [10 + CODE[a] for a in reversed(h)]

    def tr(m):
        if m <= 1:
            return 1 - m
        if m <= 5:
            return {2: 4, 3: 5, 4: 2, 5: 3}[m]
        rel, a = (0 if m < 10 else 1), [1, -1, 2, -2][(m - 6) % 4]
        return (10 if rel == 0 else 6) + CODE[phi(ph, a)]
    moves += [tr(m) for m in t["known"]]
    st = (tuple(X0), tuple(X1))
    for m in moves:
        st = vcore.apply_move(st, m)
    fix = [i for i in (0, 1) if st[i][0] < 0]
    moves += fix
    for m in fix:
        st = vcore.apply_move(st, m)
    assert st == ((1,), (2,))
    sol = {"path": moves}
    cor = tmp_path / "cor.jsonl"
    cor.write_text(json.dumps({**rec, "path": sol["path"]}) + "\n")
    (o,) = engine.run("solve", [{"id": k, "r0": t["r0"], "r1": t["r1"]}],
                      params={"strategy": "cflood", "max_nodes": 1000, "corridors": str(cor)}, endgame=None,
                      threads=1)
    assert o["solved"] and o["via"] == "corridor", o
    st = s
    for m in o["path"]:
        st = vcore.apply_move(st, m)
    assert st == ((1,), (2,))
    v = official.verify_one(k, o["path"], str(official.TRAIN_MANIFEST))
    assert v["ok"]


def test_cflood_through_loop(tmp_path, trivial, monkeypatch):
    """Preset 'cflood' through acsolver.loop: engine -> shortening ->
    official verification -> temporary DB."""
    from acsolver import db, loop
    monkeypatch.setattr(engine, "default_trivial", lambda: trivial)
    con = db.connect(tmp_path / "t.sqlite")
    ids = HARD["ms1190_uncertified"][:2] + ["ac-00008"]
    jobs = loop.make_jobs("c", ids, "cflood", {"max_nodes": 100000, "ccompact": 100000, "shorten_time": 5,
                                               "d1": 3, "d2": 3})
    _, stats = loop.submit_batch(con, "c", jobs, threads=2, verbose=False)
    assert stats["rejected"] == 0 and stats["new"] == 2
    for r in con.execute("SELECT * FROM best_solutions"):
        v = official.verify_one(r["problem_id"], json.loads(r["path"]))
        assert v["ok"] and v["length"] == r["length"]
    note = con.execute("SELECT note FROM runs WHERE problem_id='ac-00008'").fetchone()[0]
    assert "barrier_lb=" in note and "fp=" in note
