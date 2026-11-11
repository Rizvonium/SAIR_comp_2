"""Formal submission to the SAIR Lean Kernel Challenge (Stage 1).

    python3 lean_kernel/submit.py PROBLEM FILE.lean --note "..." [--yes]

Safety rules (the LATEST formal entry per problem is selected, not the best):
  * the file is re-validated locally first with lean_kernel/bench.py (build with
    warnings as errors, permitted axioms only, every local case kernel-checked);
  * without --yes this is a dry run;
  * the idempotency key is derived from (problem, sha256(text), note), so a retry
    after a timeout can never create a second submission;
  * every created submission is appended to lean_kernel/submissions.jsonl.
The API key is read only from SAIR_API_KEY and never printed.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import time
import urllib.error
import urllib.request
from pathlib import Path

BASE = "https://api.sair.foundation/api/public/v1/competitions/lean-kernel-challenge"
HERE = Path(__file__).resolve().parent
LOG = HERE / "submissions.jsonl"


def call(method, path, body=None):
    # raw UTF-8 JSON: the API rejected \u-escaped Lean source as MALFORMED_BODY
    data = json.dumps(body, ensure_ascii=False).encode("utf-8") if body is not None else None
    req = urllib.request.Request(BASE + path, data=data, method=method, headers={
        "Authorization": "Bearer " + os.environ["SAIR_API_KEY"], "Accept": "application/json",
        "Content-Type": "application/json", "User-Agent": "acsolver-lkc/1.0"})
    try:
        with urllib.request.urlopen(req, timeout=120) as r:
            return r.status, json.loads(r.read().decode() or "{}")
    except urllib.error.HTTPError as e:
        try:
            return e.code, json.loads(e.read().decode())
        except Exception:
            return e.code, {}


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("problem")
    ap.add_argument("file")
    ap.add_argument("--note", default="")
    ap.add_argument("--yes", action="store_true")
    ap.add_argument("--skip-bench", action="store_true", help="only for files already validated")
    a = ap.parse_args(argv)
    text = Path(a.file).read_text(encoding="utf-8")
    if not a.skip_bench:
        rc = subprocess.run([sys.executable, str(HERE / "bench.py"), a.problem, a.file, "--seeds", "1"]).returncode
        if rc != 0:
            print("local validation FAILED - not submitting")
            return 1
    st, spec = call("GET", "/submission-spec")
    if st != 200:
        print("cannot read submission spec:", st, spec)
        return 1
    contract = spec["data"]["contractVersion"]
    if a.problem not in spec["data"]["problems"]:
        print("unknown problem", a.problem)
        return 1
    if len(text.encode()) > spec["data"]["limits"]["maxUploadBytes"]:
        print("file too large")
        return 1
    digest = hashlib.sha256(text.encode()).hexdigest()
    key = "lkc-" + hashlib.sha256(f"{a.problem}\0{digest}\0{a.note}".encode()).hexdigest()[:40]
    body = {"idempotencyKey": key, "contractVersionAcknowledged": contract,
            "payload": {"problem": a.problem, "text": text}}
    if not a.yes:
        print(f"DRY RUN: would submit {a.problem} ({len(text)} bytes, sha256 {digest[:12]}); add --yes")
        return 0
    st, res = call("POST", "/submissions", body)
    print("HTTP", st, json.dumps(res)[:600])
    if st in (200, 201) and res.get("ok"):
        with open(LOG, "a") as f:
            f.write(json.dumps({"at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "problem": a.problem,
                                "sha256": digest, "note": a.note, "file": str(a.file),
                                "submissionId": res["data"].get("submissionId")}) + "\n")
        return 0
    return 1


if __name__ == "__main__":
    sys.exit(main())
