"""Thin, read-only bridge to the official SAIR verifier.

The verifier lives untouched in the ``external/Andrews-Curtis`` git
submodule.  Every result we store goes through
``verifier.submission.process_submission`` -- the exact function the
official CLI calls -- on a real TXT submission body, so our acceptance test
is the official one, parser included.  Nothing here modifies verifier code
or data.
"""
from __future__ import annotations

import functools
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
UPSTREAM = ROOT / "external" / "Andrews-Curtis"
COMPETITION = UPSTREAM / "competition"
TOOLS = COMPETITION / "tools"
MANIFEST = TOOLS / "verifier" / "data" / "manifest.json"
TRAIN_MANIFEST = COMPETITION / "examples" / "training_manifest.json"
TRAINING_424 = COMPETITION / "examples" / "training_424.json"
PROBLEMS = COMPETITION / "problems" / "ac.jsonl"
MOVE_SPEC = TOOLS / "verifier" / "data" / "move_spec.json"

if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from verifier import core as vcore  # noqa: E402  (official code)
from verifier import submission as vsub  # noqa: E402

MAX_LINES_PER_FILE = vsub.DEFAULT_STRUCTURAL_LIMITS["max_solutions"]


@functools.lru_cache(maxsize=None)
def load_manifest(path: str = str(MANIFEST)) -> dict:
    with open(path, encoding="utf-8") as f:
        return json.load(f)


@functools.lru_cache(maxsize=None)
def challenge_index(path: str = str(MANIFEST)) -> dict:
    return vsub.build_challenge_index(load_manifest(path))


def ac_challenges(path: str = str(MANIFEST)) -> list[dict]:
    """The AC (``ac-``) challenges, in manifest order."""
    return [c for c in load_manifest(path)["challenges"]
            if c["move_spec_version"] == "ac-r2-v1"]


def format_line(cid: str, moves) -> str:
    return "%s: [%s]" % (cid, ", ".join(str(int(m)) for m in moves))


def verify_many(items, manifest_path: str = str(MANIFEST)) -> list[dict]:
    """Verify ``[(challenge_id, moves), ...]`` with the official code.

    Items are chunked into official-size submission bodies (<= 500 lines)
    and each chunk is processed by ``process_submission``.  Returns one
    verdict dict per item, in order (``ok``, ``length``, ``work``,
    ``certificate_hash`` or an error ``code``).  Duplicate IDs in one call
    are verified independently (each in its own body) so that the
    "first success wins" rule never hides a result.
    """
    manifest = load_manifest(manifest_path)
    index = challenge_index(manifest_path)
    out: list[dict | None] = [None] * len(items)
    pending = list(range(len(items)))
    while pending:
        chunk, seen, rest = [], set(), []
        for i in pending:
            cid = items[i][0]
            if cid in seen or len(chunk) >= MAX_LINES_PER_FILE:
                rest.append(i)
            else:
                seen.add(cid)
                chunk.append(i)
        body = "\n".join(format_line(*items[i]) for i in chunk).encode()
        verdict = vsub.process_submission(body, manifest, index)
        if not verdict.get("accepted"):
            for i in chunk:
                out[i] = {"ok": False, "code": "E_MALFORMED",
                          "detail": verdict.get("detail")}
        else:
            for i, r in zip(chunk, verdict["results"]):
                assert r["challenge_id"] == items[i][0]
                out[i] = r
        pending = rest
    return out  # type: ignore[return-value]


def verify_one(cid: str, moves, manifest_path: str = str(MANIFEST)) -> dict:
    return verify_many([(cid, moves)], manifest_path)[0]


def run_cli(submission_path: Path, manifest_path: Path = MANIFEST) -> tuple[int, dict]:
    """Run the official CLI exactly as documented; returns (exit, receipt)."""
    proc = subprocess.run(
        [sys.executable, "-m", "verifier", "--manifest", str(manifest_path),
         "--submission", str(submission_path)],
        cwd=UPSTREAM, env={"PYTHONPATH": "competition/tools"},
        capture_output=True, text=True)
    try:
        receipt = json.loads(proc.stdout)
    except json.JSONDecodeError:
        receipt = {"raw": proc.stdout, "stderr": proc.stderr}
    return proc.returncode, receipt


def canonicalization_table() -> dict:
    with open(MOVE_SPEC, encoding="utf-8") as f:
        return json.load(f).get("canonicalization_table")
