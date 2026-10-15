"""SQLite storage.

Crash safety: WAL journal with ``synchronous=FULL``; every job result is
committed on its own as soon as it is verified, so an interrupted batch
loses only in-flight jobs.  Resumability: a batch's full job list is
written up front to ``batch_jobs``; re-running a batch executes only jobs
still ``pending``.  Reproducibility: each job carries its seed, strategy
and parameters, and runs record the engine's git revision.

Tables
  runs            every engine job (solved or not)
  best_solutions  current verified best per problem (official verifier)
  improvements    history of every record that got shorter
  insights        mined statistics and controller notes
  batches         batch metadata/config
  batch_jobs      the work list of each batch (for resume)
  problem_status  per-problem effort, proven bounds
"""
from __future__ import annotations

import json
import sqlite3
import subprocess
import time
from pathlib import Path

from .official import ROOT

DB_PATH = ROOT / "data" / "acsolver.sqlite"

SCHEMA = """
CREATE TABLE IF NOT EXISTS batches (
  batch_id     INTEGER PRIMARY KEY AUTOINCREMENT,
  started_at   TEXT NOT NULL,
  ended_at     TEXT,
  status       TEXT NOT NULL DEFAULT 'running',
  label        TEXT,
  config       TEXT,
  n_jobs       INTEGER DEFAULT 0,
  n_solved     INTEGER DEFAULT 0,
  n_new        INTEGER DEFAULT 0,
  n_improved   INTEGER DEFAULT 0
);
CREATE TABLE IF NOT EXISTS batch_jobs (
  batch_id    INTEGER NOT NULL,
  job_idx     INTEGER NOT NULL,
  problem_id  TEXT NOT NULL,
  strategy    TEXT NOT NULL,
  params      TEXT NOT NULL,
  seed        INTEGER NOT NULL,
  status      TEXT NOT NULL DEFAULT 'pending',
  run_id      INTEGER,
  PRIMARY KEY (batch_id, job_idx)
);
CREATE INDEX IF NOT EXISTS batch_jobs_status ON batch_jobs(batch_id, status);
CREATE TABLE IF NOT EXISTS runs (
  run_id         INTEGER PRIMARY KEY AUTOINCREMENT,
  batch_id       INTEGER,
  problem_id     TEXT NOT NULL,
  strategy       TEXT NOT NULL,
  params         TEXT,
  seed           INTEGER,
  engine_rev     TEXT,
  started_at     TEXT,
  ended_at       TEXT,
  steps          INTEGER,
  secs           REAL,
  solved         INTEGER NOT NULL,
  raw_len        INTEGER,
  path_len       INTEGER,
  path           TEXT,
  verified       INTEGER,
  verify_code    TEXT,
  note           TEXT
);
CREATE INDEX IF NOT EXISTS runs_problem ON runs(problem_id);
CREATE INDEX IF NOT EXISTS runs_batch ON runs(batch_id);
CREATE TABLE IF NOT EXISTS best_solutions (
  problem_id        TEXT PRIMARY KEY,
  length            INTEGER NOT NULL,
  path              TEXT NOT NULL,
  certificate_hash  TEXT NOT NULL,
  work              INTEGER,
  found_at          TEXT NOT NULL,
  strategy          TEXT,
  run_id            INTEGER
);
CREATE TABLE IF NOT EXISTS improvements (
  id          INTEGER PRIMARY KEY AUTOINCREMENT,
  problem_id  TEXT NOT NULL,
  old_length  INTEGER,
  new_length  INTEGER NOT NULL,
  strategy    TEXT,
  run_id      INTEGER,
  batch_id    INTEGER,
  found_at    TEXT NOT NULL
);
CREATE INDEX IF NOT EXISTS improvements_problem ON improvements(problem_id);
CREATE TABLE IF NOT EXISTS insights (
  id          INTEGER PRIMARY KEY AUTOINCREMENT,
  batch_id    INTEGER,
  created_at  TEXT NOT NULL,
  author      TEXT NOT NULL,
  kind        TEXT NOT NULL,
  title       TEXT,
  body        TEXT
);
CREATE TABLE IF NOT EXISTS problem_status (
  problem_id    TEXT PRIMARY KEY,
  attempts      INTEGER DEFAULT 0,
  total_secs    REAL DEFAULT 0,
  last_attempt  TEXT,
  lower_bound   INTEGER DEFAULT 0,
  optimal       INTEGER DEFAULT 0
);
"""


def now() -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


_REV = None


def engine_rev() -> str:
    global _REV
    if _REV is None:
        try:
            _REV = subprocess.run(["git", "-C", str(ROOT), "rev-parse", "--short", "HEAD"],
                                  capture_output=True, text=True).stdout.strip() or "unknown"
        except OSError:
            _REV = "unknown"
    return _REV


def connect(path: Path | str = DB_PATH) -> sqlite3.Connection:
    Path(path).parent.mkdir(parents=True, exist_ok=True)
    con = sqlite3.connect(str(path), timeout=60)
    con.row_factory = sqlite3.Row
    con.execute("PRAGMA journal_mode=WAL")
    con.execute("PRAGMA synchronous=FULL")
    con.executescript(SCHEMA)
    cols = {r[1] for r in con.execute("PRAGMA table_info(runs)")}
    if "raw_path" not in cols:  # migration: pre-shortening path (corridor source)
        con.execute("ALTER TABLE runs ADD COLUMN raw_path TEXT")
    return con


# ---------------------------------------------------------------------------
# batches & jobs

def create_batch(con, label: str, config: dict, jobs: list[dict]) -> int:
    with con:
        cur = con.execute("INSERT INTO batches(started_at, label, config, n_jobs) VALUES (?,?,?,?)",
                          (now(), label, json.dumps(config), len(jobs)))
        bid = cur.lastrowid
        con.executemany(
            "INSERT INTO batch_jobs(batch_id, job_idx, problem_id, strategy, params, seed) VALUES (?,?,?,?,?,?)",
            [(bid, i, j["problem_id"], j["strategy"], json.dumps(j["params"], sort_keys=True), j["seed"])
             for i, j in enumerate(jobs)])
    return bid


def pending_jobs(con, batch_id: int) -> list[sqlite3.Row]:
    return con.execute("SELECT * FROM batch_jobs WHERE batch_id=? AND status='pending' ORDER BY job_idx",
                       (batch_id,)).fetchall()


def unfinished_batches(con) -> list[sqlite3.Row]:
    return con.execute("SELECT * FROM batches WHERE status='running' ORDER BY batch_id").fetchall()


def finish_batch(con, batch_id: int):
    with con:
        row = con.execute(
            "SELECT COUNT(*) n, SUM(solved) s FROM runs WHERE batch_id=?", (batch_id,)).fetchone()
        imp = con.execute("SELECT COUNT(*) FROM improvements WHERE batch_id=? AND old_length IS NOT NULL",
                          (batch_id,)).fetchone()[0]
        new = con.execute("SELECT COUNT(*) FROM improvements WHERE batch_id=? AND old_length IS NULL",
                          (batch_id,)).fetchone()[0]
        con.execute("UPDATE batches SET status='done', ended_at=?, n_solved=?, n_new=?, n_improved=? "
                    "WHERE batch_id=?", (now(), row["s"] or 0, new, imp, batch_id))


# ---------------------------------------------------------------------------
# results

def best(con, problem_id: str):
    return con.execute("SELECT * FROM best_solutions WHERE problem_id=?", (problem_id,)).fetchone()


def best_lengths(con) -> dict[str, int]:
    return {r[0]: r[1] for r in con.execute("SELECT problem_id, length FROM best_solutions")}


def record_run(con, *, batch_id, job_idx, problem_id, strategy, params, seed, started_at, result,
               verdict) -> tuple[int, str]:
    """Insert one run (and update best/improvements) in a single
    transaction.  ``verdict`` is the official verifier's result for the
    final path (or None if the job did not solve).  Returns (run_id,
    outcome) where outcome is 'new', 'improved', 'tied', 'worse',
    'unsolved' or 'rejected'."""
    solved = bool(result.get("solved"))
    path = result.get("path") if solved else None
    verified = None if verdict is None else int(bool(verdict.get("ok")))
    outcome = "unsolved"
    with con:
        cur = con.execute(
            "INSERT INTO runs(batch_id, problem_id, strategy, params, seed, engine_rev, started_at, ended_at,"
            " steps, secs, solved, raw_len, path_len, path, verified, verify_code, note, raw_path)"
            " VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
            (batch_id, problem_id, strategy, json.dumps(params, sort_keys=True), seed, engine_rev(),
             started_at, now(), result.get("nodes"), result.get("secs"), int(solved),
             result.get("raw_len"), len(path) if path is not None else None,
             json.dumps(path) if path is not None else None, verified,
             None if verdict is None else verdict.get("code"), result.get("note"),
             json.dumps(result["raw_path"]) if solved and verified and result.get("raw_path") else None))
        run_id = cur.lastrowid
        if solved and not verified:
            outcome = "rejected"
        elif solved and verified:
            old = con.execute("SELECT length FROM best_solutions WHERE problem_id=?", (problem_id,)).fetchone()
            L = verdict["length"]
            if old is None or L < old[0]:
                con.execute(
                    "INSERT OR REPLACE INTO best_solutions(problem_id, length, path, certificate_hash, work,"
                    " found_at, strategy, run_id) VALUES (?,?,?,?,?,?,?,?)",
                    (problem_id, L, json.dumps(path), verdict["certificate_hash"], verdict.get("work"), now(),
                     strategy, run_id))
                con.execute(
                    "INSERT INTO improvements(problem_id, old_length, new_length, strategy, run_id, batch_id,"
                    " found_at) VALUES (?,?,?,?,?,?,?)",
                    (problem_id, None if old is None else old[0], L, strategy, run_id, batch_id, now()))
                outcome = "new" if old is None else "improved"
            else:
                outcome = "tied" if L == old[0] else "worse"
        con.execute(
            "INSERT INTO problem_status(problem_id, attempts, total_secs, last_attempt) VALUES (?,1,?,?)"
            " ON CONFLICT(problem_id) DO UPDATE SET attempts=attempts+1, total_secs=total_secs+excluded.total_secs,"
            " last_attempt=excluded.last_attempt", (problem_id, result.get("secs") or 0, now()))
        if result.get("lower_bound"):
            con.execute("UPDATE problem_status SET lower_bound=MAX(lower_bound, ?) WHERE problem_id=?",
                        (result["lower_bound"], problem_id))
        if result.get("optimal") and verified:
            con.execute("UPDATE problem_status SET optimal=1 WHERE problem_id=?", (problem_id,))
        if job_idx is not None:
            con.execute("UPDATE batch_jobs SET status='done', run_id=? WHERE batch_id=? AND job_idx=?",
                        (run_id, batch_id, job_idx))
    return run_id, outcome


def add_insight(con, author: str, kind: str, title: str, body, batch_id=None):
    with con:
        con.execute("INSERT INTO insights(batch_id, created_at, author, kind, title, body) VALUES (?,?,?,?,?,?)",
                    (batch_id, now(), author, kind, title, body if isinstance(body, str) else json.dumps(body)))
