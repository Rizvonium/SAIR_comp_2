"""Exactness of the commutation canonicalization and of full shortening."""
import json
import random
import subprocess

from acsolver import engine, official, problems
from acsolver.official import vcore


def replay(r0, r1, path):
    s = (tuple(r0), tuple(r1))
    for m in path:
        s = vcore.apply_move(s, m)
    return s


def test_commute_reduce_exact_and_shorter():
    engine.ensure_built()
    rng = random.Random(3)
    local = [0, 1, 6, 7, 8, 9, 10, 11, 12, 13]
    recs = []
    for _ in range(300):
        r = [list(vcore.free_reduce([rng.choice([1, -1, 2, -2]) for _ in range(rng.randint(1, 12))]))
             for _ in range(2)]
        path = [rng.choice(local if rng.random() < 0.85 else list(range(14))) for _ in range(rng.randint(0, 40))]
        recs.append({"r0": r[0], "r1": r[1], "path": path})
    out = subprocess.run([str(engine.BIN), "commute"], input="\n".join(json.dumps(r) for r in recs),
                         capture_output=True, text=True, check=True).stdout.splitlines()
    shorter = 0
    for rec, line in zip(recs, out):
        p = json.loads(line)["path"]
        assert replay(rec["r0"], rec["r1"], p) == replay(rec["r0"], rec["r1"], rec["path"])
        assert len(p) <= len(rec["path"])
        shorter += len(p) < len(rec["path"])
    assert shorter > 100
    # a hand example: r0 conjugated by x then back, r1 by x y -> 2 moves
    one = subprocess.run([str(engine.BIN), "commute"], capture_output=True, text=True, check=True,
                         input=json.dumps({"r0": [1, 2, 2], "r1": [2, -1, 2], "path": [6, 10, 7, 12]})).stdout
    assert len(json.loads(one)["path"]) == 2


def test_shorten_keeps_training_paths_valid():
    T = problems.training_problems()
    recs = [{"id": k, "r0": t["r0"], "r1": t["r1"], "path": t["known"]} for k, t in list(T.items())[:60]]
    out = engine.run("shorten", recs, params={"d1": 3, "d2": 3}, threads=2)
    items = [(o["id"], o["path"]) for o in out]
    for o, v in zip(out, official.verify_many(items, str(official.TRAIN_MANIFEST))):
        assert v["ok"] and o["after"] <= o["before"]
