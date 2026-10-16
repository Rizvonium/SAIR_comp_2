"""Client for the SAIR ACC public API (submit solutions, read records).

The API key is read ONLY from the environment variable SAIR_API_KEY (create
it on the SAIR site with scopes competition.read + competition.write after
registering for the ACC Challenge and creating/joining a team).  It is never
written to disk or logged.

    python3 -m acsolver sair me                 # eligibility check
    python3 -m acsolver sair snapshot           # current records -> data/sair_snapshot.json + comparison
    python3 -m acsolver sair submit             # dry run: what would be submitted and why
    python3 -m acsolver sair submit --yes       # submit (uses one unit of the daily quota per batch)
    python3 -m acsolver sair status ID          # poll a submission
    python3 -m acsolver sair mine               # team submission history

Only lines that can score are submitted: problems where our verified best is
shorter than or equal to the current shortest record (or nobody has one).
Every line is re-verified with the official verifier before upload.
"""
from __future__ import annotations

import json
import os
import time
import urllib.error
import urllib.request

from . import db, official

BASE = "https://api.sair.foundation/api/public/v1"
SNAPSHOT = official.ROOT / "data" / "sair_snapshot.json"


class ApiError(RuntimeError):
    pass


def _key() -> str:
    k = os.environ.get("SAIR_API_KEY", "").strip()
    if not k:
        raise ApiError("SAIR_API_KEY is not set. Create an API key on the SAIR site "
                       "(scopes competition.read and competition.write) and export it.")
    return k


def call(method: str, path: str, body: dict | None = None, retries: int = 4):
    data = json.dumps(body).encode() if body is not None else None
    for attempt in range(retries):
        req = urllib.request.Request(BASE + path, data=data, method=method,
                                     headers={"Authorization": "Bearer " + _key(),
                                              "Content-Type": "application/json",
                                              "Accept": "application/json"})
        try:
            with urllib.request.urlopen(req, timeout=120) as r:
                txt = r.read().decode()
                return json.loads(txt) if txt else {}
        except urllib.error.HTTPError as e:
            msg = e.read().decode(errors="replace")[:500]
            if e.code in (429, 502, 503, 504) and attempt + 1 < retries:
                time.sleep(int(e.headers.get("Retry-After") or 2 ** (attempt + 1)))
                continue
            raise ApiError(f"{method} {path} -> HTTP {e.code}: {msg}") from None
        except urllib.error.URLError as e:
            if attempt + 1 < retries:
                time.sleep(2 ** (attempt + 1))
                continue
            raise ApiError(f"{method} {path} -> network error: {e.reason}") from None


def me():
    return call("GET", "/competitions/acc/me")


def spec():
    return call("GET", "/competitions/acc/submission-spec")


def snapshot(problem: str = "ac") -> dict[str, dict]:
    """{challengeId: progress item} for the whole scored pool; cached to disk."""
    res = call("GET", f"/competitions/acc/discoveries/snapshot?problem={problem}")
    items = (res.get("data") or {}).get("items") or []
    out = {it.get("challengeId"): it for it in items if it.get("challengeId")}
    SNAPSHOT.parent.mkdir(exist_ok=True)
    cached = json.loads(SNAPSHOT.read_text()) if SNAPSHOT.exists() else {}
    cached[problem] = {"fetched_at": db.now(), "items": out}
    SNAPSHOT.write_text(json.dumps(cached))
    return out


def _record_len(item: dict):
    """Current shortest move count from a progress item (field names per the API reference)."""
    for k in ("shortestMoveCount", "currentShortestMoveCount", "bestLength", "shortestLength", "moveCount"):
        if isinstance(item.get(k), int):
            return item[k]
    return None


def compare(con, items: dict[str, dict]) -> dict:
    best = db.best_lengths(con)
    rows = {"beat": [], "tie": [], "behind": [], "no_record": [], "unsolved_by_us": []}
    for cid, it in items.items():
        rec = _record_len(it)
        ours = best.get(cid)
        if ours is None:
            rows["unsolved_by_us"].append((cid, rec))
        elif rec is None:
            rows["no_record"].append((cid, ours))
        elif ours < rec:
            rows["beat"].append((cid, ours, rec))
        elif ours == rec:
            rows["tie"].append((cid, ours, rec))
        else:
            rows["behind"].append((cid, ours, rec))
    return rows


def candidates(con, items: dict[str, dict] | None, include_ties=True) -> list[tuple[str, list]]:
    """Our verified best paths that can score now."""
    out = []
    for r in con.execute("SELECT problem_id, length, path FROM best_solutions WHERE problem_id LIKE 'ac-%' "
                         "ORDER BY problem_id"):
        rec = _record_len(items.get(r["problem_id"], {})) if items else None
        if rec is None or r["length"] < rec or (include_ties and r["length"] == rec):
            out.append((r["problem_id"], json.loads(r["path"])))
    return out


def submit(con, yes=False, note="", include_ties=True, max_batches=1) -> list[dict]:
    try:
        items = snapshot("ac")
    except ApiError as e:
        print("warning: could not read records, submitting all verified bests:", e)
        items = None
    cands = candidates(con, items, include_ties)
    # re-verify locally with the official code before spending quota
    verdicts = official.verify_many(cands)
    cands = [c for c, v in zip(cands, verdicts) if v["ok"]]
    try:
        limit = int(((spec().get("data") or {}).get("maxSolutionsPerSubmission")) or 500)
    except (ApiError, ValueError, TypeError):
        limit = official.MAX_LINES_PER_FILE
    batches = [cands[i:i + limit] for i in range(0, len(cands), limit)][:max_batches]
    print(f"{len(cands)} scoring candidates (verified); {len(batches)} batch(es) of <= {limit}")
    results = []
    for b in batches:
        text = (f"# {note}\n" if note else "") + "\n".join(official.format_line(c, m) for c, m in b) + "\n"
        if not yes:
            print(f"DRY RUN: would submit {len(b)} lines ({b[0][0]} .. {b[-1][0]}); pass --yes to submit")
            continue
        body = {"payload": {"text": text}}
        if note:
            body["meta"] = {"description": note}
        res = call("POST", "/competitions/acc/submissions", body)
        sid = (res.get("data") or {}).get("submissionId")
        db.add_insight(con, "submitter", "sair_submission", f"submitted {len(b)} lines", {"submissionId": sid,
                       "lines": len(b), "first": b[0][0], "last": b[-1][0]})
        print("submitted:", sid)
        results.append(res)
    return results


def status(sid: str, wait=True):
    while True:
        res = call("GET", f"/competitions/acc/submissions/{sid}")
        st = (res.get("data") or {}).get("status")
        if not wait or st not in ("queued", "running"):
            return res
        time.sleep(10)


def main(argv):
    import argparse
    ap = argparse.ArgumentParser(prog="acsolver sair")
    ap.add_argument("cmd", choices=["me", "spec", "snapshot", "submit", "status", "mine", "leaderboard"])
    ap.add_argument("arg", nargs="?")
    ap.add_argument("--yes", action="store_true", help="really submit (consumes daily quota)")
    ap.add_argument("--note", default="")
    ap.add_argument("--no-ties", action="store_true")
    ap.add_argument("--max-batches", type=int, default=1)
    a = ap.parse_args(argv)
    con = db.connect()
    try:
        if a.cmd == "me":
            print(json.dumps(me(), indent=1))
        elif a.cmd == "spec":
            print(json.dumps(spec(), indent=1))
        elif a.cmd == "snapshot":
            rows = compare(con, snapshot("ac"))
            for k, v in rows.items():
                print(f"{k}: {len(v)}")
            for cid, ours, rec in sorted(rows["behind"], key=lambda t: t[1] - t[2])[:15]:
                print(f"  behind {cid}: ours {ours} vs record {rec}")
            for cid, ours, rec in rows["beat"][:15]:
                print(f"  BEAT {cid}: ours {ours} vs record {rec}")
        elif a.cmd == "submit":
            submit(con, yes=a.yes, note=a.note, include_ties=not a.no_ties, max_batches=a.max_batches)
        elif a.cmd == "status":
            print(json.dumps(status(a.arg), indent=1))
        elif a.cmd == "mine":
            print(json.dumps(call("GET", "/competitions/acc/submissions/mine"), indent=1))
        elif a.cmd == "leaderboard":
            print(json.dumps(call("GET", "/competitions/acc/leaderboard?problem=ac"), indent=1))
    except ApiError as e:
        print("error:", e)
        return 1
    return 0
