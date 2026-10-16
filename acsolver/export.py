"""Submission export and git-friendly result snapshots.

* ``results/best_solutions.jsonl`` -- every verified best path (source of
  truth that survives a lost DB; ``import_jsonl`` re-verifies and loads it).
* ``results/submission.txt`` -- all scored AC best paths in one file.  The
  official parser caps a file at 500 solution lines, so this combined file
  is for reference/archival only.
* ``results/submission_parts/part_NN.txt`` -- upload-ready files of at most
  500 lines each; every part is checked with the official CLI and must exit
  0 with every row ``ok: true``.
"""
from __future__ import annotations

import json
from pathlib import Path

from . import db, official

RESULTS = official.ROOT / "results"


def _rows(con):
    return con.execute("SELECT * FROM best_solutions WHERE problem_id LIKE 'ac-%' ORDER BY problem_id").fetchall()


def write_snapshot(con, outdir: Path = RESULTS) -> int:
    outdir.mkdir(parents=True, exist_ok=True)
    rows = con.execute("SELECT * FROM best_solutions ORDER BY problem_id").fetchall()
    tmp = outdir / "best_solutions.jsonl.tmp"
    with open(tmp, "w") as f:
        for r in rows:
            f.write(json.dumps({"problem_id": r["problem_id"], "length": r["length"],
                                "path": json.loads(r["path"]), "certificate_hash": r["certificate_hash"],
                                "work": r["work"], "strategy": r["strategy"], "found_at": r["found_at"]}) + "\n")
    tmp.replace(outdir / "best_solutions.jsonl")
    return len(rows)


def write_submission(con, outdir: Path = RESULTS, check: bool = True) -> dict:
    rows = _rows(con)
    outdir.mkdir(parents=True, exist_ok=True)
    lines = [official.format_line(r["problem_id"], json.loads(r["path"])) for r in rows]
    header = ["# SAIR ACC Discovery Track - AC submission", f"# {len(lines)} verified best paths",
              f"# total moves {sum(r['length'] for r in rows)}"]
    (outdir / "submission.txt").write_text("\n".join(header + lines) + "\n")
    parts_dir = outdir / "submission_parts"
    parts_dir.mkdir(exist_ok=True)
    for old in parts_dir.glob("part_*.txt"):
        old.unlink()
    n = official.MAX_LINES_PER_FILE
    parts = [lines[i:i + n] for i in range(0, len(lines), n)]
    report = {"solutions": len(lines), "parts": []}
    for k, chunk in enumerate(parts, 1):
        p = parts_dir / f"part_{k:02d}.txt"
        p.write_text("\n".join(chunk) + "\n")
        entry = {"file": p.name, "lines": len(chunk)}
        if check:
            code, receipt = official.run_cli(p)
            res = receipt.get("results", [])
            entry.update(exit=code, accepted=receipt.get("accepted"), ok=sum(1 for r in res if r.get("ok")),
                         failed=[r["challenge_id"] for r in res if not r.get("ok")])
            if code != 0 or entry["failed"]:
                raise RuntimeError(f"official verifier rejected {p}: {entry}")
        report["parts"].append(entry)
    (outdir / "submission_report.json").write_text(json.dumps(report, indent=1))
    return report


def import_jsonl(con, path: Path) -> dict:
    """Load a best_solutions.jsonl snapshot, or a submission TXT file
    (``ac-00001: [0, 2, 6]`` lines, ``#`` comments); a directory imports every
    .jsonl/.txt in it.  Every path is re-verified; Stable AC (sac-) lines are
    skipped because they are derived from the AC paths."""
    path = Path(path)
    if path.is_dir():
        tot = {}
        for f in sorted(path.glob("*.jsonl")) + sorted(path.glob("*.txt")):
            for k, v in import_jsonl(con, f).items():
                tot[k] = tot.get(k, 0) + v
        return tot
    items = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            if line.startswith("{"):
                items.append(json.loads(line))
            else:
                cid, _, moves = line.partition(":")
                cid = cid.strip()
                if cid.startswith("sac-"):
                    continue
                items.append({"problem_id": cid, "path": json.loads(moves), "strategy": "import"})
    stats = {"new": 0, "improved": 0, "tied": 0, "worse": 0, "rejected": 0}
    for r in items:
        pid = r["problem_id"]
        manifest = str(official.TRAIN_MANIFEST if pid.startswith("ms-train") else official.MANIFEST)
        v = official.verify_one(pid, r["path"], manifest)
        _, outcome = db.record_run(con, batch_id=None, job_idx=None, problem_id=pid,
                                   strategy=r.get("strategy") or "import", params={"import": str(path)}, seed=0,
                                   started_at=db.now(), result={"solved": True, "path": r["path"], "note": "import"},
                                   verdict=v)
        stats[outcome] = stats.get(outcome, 0) + 1
    return stats
