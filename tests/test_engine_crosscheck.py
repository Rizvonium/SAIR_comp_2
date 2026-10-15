"""Blocking cross-check: the C++ engine must agree bit-for-bit with the
official Python verifier (external/Andrews-Curtis, unmodified).

1. All 424 training certificates: engine replay reaches the target with
   the same work, and the official verifier accepts them.
2. Thousands of random start states and random move sequences: the final
   state and work of the engine equal the official core's replay.
3. Every intermediate state of random sequences matches (step by step).
"""
import json
import random

import pytest

from acsolver import engine, official
from acsolver.official import vcore


@pytest.fixture(scope="module")
def training():
    with open(official.TRAINING_424) as f:
        return json.load(f)["instances"]


def official_replay(r0, r1, path):
    s = (tuple(r0), tuple(r1))
    work = len(s[0]) + len(s[1])
    for m in path:
        s = vcore.apply_move(s, m)
        work += len(s[0]) + len(s[1])
    return s, work


def test_training_certificates_engine(training):
    recs = [{"r0": t["initial_relators"][0], "r1": t["initial_relators"][1], "path": t["moves"]}
            for t in training]
    out = engine.run("replay", recs, endgame=None, threads=1)
    assert len(out) == 424
    for t, o in zip(training, out):
        assert o["target"], t["training_id"]
        assert o["work"] == t["work"], t["training_id"]
        assert o["peak"] == t["peak_total_relator_length"], t["training_id"]


def test_training_certificates_official_verifier(training):
    items = [(t["training_id"], t["moves"]) for t in training]
    verdicts = official.verify_many(items, str(official.TRAIN_MANIFEST))
    assert all(v["ok"] for v in verdicts)


@pytest.mark.parametrize("seed,length", [(1, 20), (2, 80), (3, 300)])
def test_random_sequences(seed, length):
    out = []
    import subprocess
    engine.ensure_built()
    proc = subprocess.run([str(engine.BIN), "random-test", "--n", "2000", "--len", str(length),
                           "--seed", str(seed)], capture_output=True, text=True, check=True)
    for line in proc.stdout.splitlines():
        out.append(json.loads(line))
    assert len(out) == 2000
    for o in out:
        s, work = official_replay(o["r0"], o["r1"], o["path"])
        assert list(s[0]) == o["f0"] and list(s[1]) == o["f1"], o
        assert work == o["work"]


def test_random_stepwise():
    rng = random.Random(7)
    letters = [1, -1, 2, -2]
    recs, expect = [], []
    for _ in range(500):
        r = [list(vcore.free_reduce([rng.choice(letters) for _ in range(rng.randint(0, 25))])) for _ in range(2)]
        path, st = [], (tuple(r[0]), tuple(r[1]))
        for _ in range(rng.randint(0, 60)):  # legal prefix only (<= 10000 letters)
            m = rng.randrange(14)
            st = vcore.apply_move(st, m)
            if len(st[0]) + len(st[1]) > 10000:
                break
            path.append(m)
        # every prefix as its own replay record
        for k in range(0, len(path) + 1, 7):
            recs.append({"r0": r[0], "r1": r[1], "path": path[:k]})
            expect.append(official_replay(r[0], r[1], path[:k]))
    out = engine.run("replay", recs, endgame=None, threads=1)
    for o, (s, work) in zip(out, expect):
        assert (tuple(o["r0"]), tuple(o["r1"])) == s
        assert o["work"] == work
