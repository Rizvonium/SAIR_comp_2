"""Stable AC paths derived from AC paths are accepted by the official verifier."""
from acsolver import official, problems, stable


def test_stable_from_training_paths():
    T = problems.training_problems()
    items = [("sac-train-" + k.split("-")[-1], stable.to_stable(t["r0"], t["r1"], t["known"]))
             for k, t in T.items()]
    verdicts = official.verify_many(items, str(official.TRAIN_MANIFEST))
    assert all(v["ok"] for v in verdicts)
    # never longer than AC path + [16, 15]
    assert all(len(m) <= len(t["known"]) + 2 for (_, m), t in zip(items, T.values()))


def test_swap_finish_is_cheaper():
    # (y, x) finishes in 2 stable moves instead of 5 AC moves + 2
    assert stable.to_stable([2], [1], []) == [16, 15]
