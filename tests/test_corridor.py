"""Corridor table: searches finish through other problems' solution paths."""
import json

from acsolver import engine, official, problems
from acsolver.official import vcore


def test_corridor_finish_and_self_exclusion(tmp_path):
    T = problems.training_problems()
    a = T["ms-train-0050"]
    path = a["known"]
    # problem B starts at an intermediate state of A's known path
    s = (tuple(a["r0"]), tuple(a["r1"]))
    k = len(path) // 2
    for m in path[:k]:
        s = vcore.apply_move(s, m)
    cor = tmp_path / "cor.jsonl"
    cor.write_text(json.dumps({"id": "A", "r0": a["r0"], "r1": a["r1"], "path": path}) + "\n")
    recs = [{"id": "B", "r0": list(s[0]), "r1": list(s[1])},
            {"id": "A", "r0": a["r0"], "r1": a["r1"]}]
    out = {o["id"]: o for o in engine.run("solve", recs, params={"strategy": "gbfs", "max_nodes": 1,
                                                                   "corridors": str(cor)}, endgame=None,
                                          threads=1)}
    # B: solved at the root via the corridor, by exactly A's remaining suffix
    assert out["B"]["solved"] and out["B"]["path"] == path[k:]
    # A: its own corridor is excluded, so a 1-node search cannot solve it
    assert not out["A"]["solved"]
    # and the spliced path is accepted by the official verifier when replayed
    # from A's start (prefix + corridor suffix == A's known path)
    v = official.verify_one("ms-train-0050", path[:k] + out["B"]["path"], str(official.TRAIN_MANIFEST))
    assert v["ok"]
