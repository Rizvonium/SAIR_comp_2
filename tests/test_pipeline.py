"""End-to-end pipeline on a temporary DB with a few training problems."""
import json

import pytest

from acsolver import db, export, loop, official


@pytest.fixture()
def con(tmp_path):
    return db.connect(tmp_path / "t.sqlite")


IDS = ["ms-train-0001", "ms-train-0002", "ms-train-0160", "ms-train-0300"]


def test_batch_verify_store_resume_polish(con, tmp_path):
    jobs = loop.make_jobs("t", IDS, "gbfs", {"time_limit": 5})
    bid = db.create_batch(con, "t", {}, jobs)
    # simulate a crash after creating the batch: nothing ran yet
    assert len(db.pending_jobs(con, bid)) == len(IDS)
    loop.resume_all(con, threads=2, verbose=False)
    assert not db.pending_jobs(con, bid)
    rows = con.execute("SELECT * FROM best_solutions").fetchall()
    assert len(rows) == len(IDS)
    for r in rows:  # stored results must re-verify with the official code
        v = official.verify_one(r["problem_id"], json.loads(r["path"]), str(official.TRAIN_MANIFEST))
        assert v["ok"] and v["length"] == r["length"] and v["certificate_hash"] == r["certificate_hash"]
    assert con.execute("SELECT COUNT(*) FROM improvements WHERE old_length IS NULL").fetchone()[0] == len(IDS)
    assert con.execute("SELECT status FROM batches WHERE batch_id=?", (bid,)).fetchone()[0] == "done"
    # polish never makes a record longer
    before = db.best_lengths(con)
    _, stats = loop.submit_batch(con, "p", loop.make_jobs("p", IDS, "polish", {"shorten_time": 10}),
                                 threads=2, verbose=False)
    after = db.best_lengths(con)
    assert all(after[k] <= before[k] for k in before)
    assert stats["rejected"] == 0


def test_rejected_paths_not_stored(con):
    bad = {"solved": True, "path": [6, 7], "nodes": 1, "secs": 0.1}
    v = official.verify_one("ms-train-0001", bad["path"], str(official.TRAIN_MANIFEST))
    assert not v["ok"]
    _, outcome = db.record_run(con, batch_id=None, job_idx=None, problem_id="ms-train-0001", strategy="x",
                               params={}, seed=1, started_at=db.now(), result=bad, verdict=v)
    assert outcome == "rejected"
    assert con.execute("SELECT COUNT(*) FROM best_solutions").fetchone()[0] == 0


def test_snapshot_roundtrip(con, tmp_path):
    loop.submit_batch(con, "t", loop.make_jobs("t", IDS[:2], "gbfs", {"time_limit": 5}), threads=2, verbose=False)
    export.write_snapshot(con, tmp_path)
    con2 = db.connect(tmp_path / "u.sqlite")
    stats = export.import_jsonl(con2, tmp_path / "best_solutions.jsonl")
    assert stats["new"] == 2 and stats["rejected"] == 0
    assert db.best_lengths(con2) == db.best_lengths(con)


def test_bookkeeping_params_and_tail(con):
    # controller-style jobs carry "_action"; the engine must never see it
    jobs = loop.make_jobs("t", IDS[:2], "gbfs", {"time_limit": 5, "_action": "cover"})
    _, stats = loop.submit_batch(con, "t", jobs, threads=2, verbose=False)
    assert stats["solved"] == 2
    before = db.best_lengths(con)
    # tail re-search splices the prefix back; anything stored must verify
    jobs = loop.make_jobs("u", IDS[:2], "tail", {"tail_frac": 0.5, "_action": "resolve"})
    _, stats = loop.submit_batch(con, "u", jobs, threads=2, verbose=False)
    assert stats["rejected"] == 0
    after = db.best_lengths(con)
    assert all(after[k] <= before[k] for k in before)
    for r in con.execute("SELECT * FROM runs WHERE strategy='tail' AND solved=1"):
        assert r["verified"] == 1
