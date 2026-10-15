"""Controller planning on a fresh DB (no engine runs)."""
from acsolver import controller, db, loop


def test_plan_fresh_db(tmp_path):
    con = db.connect(tmp_path / "c.sqlite")
    cfg = controller.load_config()
    cfg["batch_jobs"] = 50
    jobs, meta, reasoning = controller.plan(con, cfg)
    assert 0 < len(jobs) <= 50
    assert all(j["strategy"] in loop.PRESETS for j in jobs)
    assert all(j["params"]["_action"] == "cover" for j in jobs)  # nothing solved yet
    assert "Hypothesis" in reasoning and meta["actions"]
