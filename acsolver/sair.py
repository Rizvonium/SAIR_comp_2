"""Client for the SAIR ACC public API (submit solutions, read records).

The API key is read ONLY from the environment variable SAIR_API_KEY (create
it on the SAIR site with scopes competition.read + competition.write after
registering for the ACC Challenge and creating/joining a team).  It is never
written to disk or logged.

    python3 -m acsolver sair me                 # eligibility check
    python3 -m acsolver sair snapshot           # current records -> data/sair_snapshot.json + comparison
    python3 -m acsolver sair submit             # dry run: what would be submitted and why
    python3 -m acsolver sair submit --yes       # submit (uses one unit of the daily quota per batch)
    python3 -m acsolver sair status ID          # poll a submission until verified
    python3 -m acsolver sair leaderboard [--problem stable_ac]
    python3 -m acsolver sair mine               # team submission history

Only lines that can score are submitted (AC and derived Stable AC lines in the
same batch): problems where our verified best is shorter than or equal to the
current shortest record (or nobody has one), and shorter than what we already
uploaded (ledger: results/sair_submitted.json).  Every line is re-verified with
the official verifier before upload.

API notes (checked against the live service): Cloudflare rejects the default
urllib User-Agent; snapshot items carry ``currentBestLength`` and ``kTeams``;
the spec's batch cap is ``limits.maxSolutions`` (500).
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
SUBMITTED = official.ROOT / "results" / "sair_submitted.json"
# Cloudflare in front of the API rejects the default "Python-urllib" agent (error 1010)
USER_AGENT = "acsolver/1.0 (+https://github.com/Rizvonium/SAIR_comp_2)"
PROBLEMS = {"ac": "ac-", "stable_ac": "sac-"}


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
                                              "Accept": "application/json",
                                              "User-Agent": USER_AGENT})
        try:
            with urllib.request.urlopen(req, timeout=120) as r:
                txt = r.read().decode()
                return json.loads(txt) if txt else {}
        except urllib.error.HTTPError as e:
            msg = e.read().decode(errors="replace")[:500]
            # never blindly retry a POST: an accepted retry would consume quota twice
            if e.code in (429, 502, 503, 504) and method == "GET" and attempt + 1 < retries:
                time.sleep(int(e.headers.get("Retry-After") or 2 ** (attempt + 1)))
                continue
            raise ApiError(f"{method} {path} -> HTTP {e.code}: {msg}") from None
        except urllib.error.URLError as e:
            if method == "GET" and attempt + 1 < retries:
                time.sleep(2 ** (attempt + 1))
                continue
            raise ApiError(f"{method} {path} -> network error: {e.reason}") from None


def me():
    return call("GET", "/competitions/acc/me")


def spec():
    return call("GET", "/competitions/acc/submission-spec")


def snapshot(problem: str = "ac") -> dict[str, dict]:
    """{challengeId: progress item} for the whole scored pool; cached to disk.
    Items: {problem, challengeId, status, currentBestLength, kTeams}."""
    res = call("GET", f"/competitions/acc/discoveries/snapshot?problem={problem}")
    items = (res.get("data") or {}).get("items") or []
    out = {it.get("challengeId"): it for it in items if it.get("challengeId")}
    SNAPSHOT.parent.mkdir(exist_ok=True)
    cached = json.loads(SNAPSHOT.read_text()) if SNAPSHOT.exists() else {}
    cached[problem] = {"fetched_at": db.now(), "generated_at": (res.get("data") or {}).get("generatedAt"),
                       "items": out}
    SNAPSHOT.write_text(json.dumps(cached))
    return out


def _record_len(item: dict):
    """Current shortest verified move count of a snapshot item (None: nobody solved it)."""
    for k in ("currentBestLength", "shortestMoveCount", "bestLength"):
        if isinstance(item.get(k), int):
            return item[k]
    return None


KNOWN = official.ROOT / "config" / "known_records.json"


def load_records(problem: str = "ac") -> tuple[dict[str, int], str]:
    """{challenge_id: current shortest record length} and its source:
    the cached live API snapshot when present, else manual known records."""
    recs, src = {}, "none"
    if KNOWN.exists() and problem == "ac":
        recs.update({k: int(v) for k, v in json.loads(KNOWN.read_text()).get("records", {}).items()})
        src = f"manual ({KNOWN.name})"
    if SNAPSHOT.exists():
        snap = json.loads(SNAPSHOT.read_text()).get(problem)
        if snap:
            live = {cid: _record_len(it) for cid, it in snap["items"].items()}
            recs = {k: v for k, v in live.items() if v is not None}
            src = f"SAIR API snapshot {snap.get('generated_at') or snap['fetched_at']}"
    return recs, src


def load_kteams(problem: str = "ac") -> dict[str, int]:
    if not SNAPSHOT.exists():
        return {}
    snap = json.loads(SNAPSHOT.read_text()).get(problem) or {}
    return {cid: int(it.get("kTeams") or 0) for cid, it in snap.get("items", {}).items()}


def compare(ours: dict[str, int], items: dict[str, dict]) -> dict:
    rows = {"beat": [], "tie": [], "behind": [], "no_record": [], "unsolved_by_us": []}
    for cid, it in items.items():
        rec = _record_len(it)
        mine = ours.get(cid)
        if mine is None:
            if rec is not None:
                rows["unsolved_by_us"].append((cid, rec))
        elif rec is None:
            rows["no_record"].append((cid, mine))
        elif mine < rec:
            rows["beat"].append((cid, mine, rec))
        elif mine == rec:
            rows["tie"].append((cid, mine, rec))
        else:
            rows["behind"].append((cid, mine, rec))
    return rows


def our_paths(con, problem: str) -> dict[str, list]:
    """Our verified best paths for one problem ({challenge_id: moves})."""
    if problem == "ac":
        return {r["problem_id"]: json.loads(r["path"]) for r in con.execute(
            "SELECT problem_id, path FROM best_solutions WHERE problem_id LIKE 'ac-%'")}
    from . import stable
    return {cid: mv for cid, mv, v in stable.stable_bests(con) if v["ok"]}


def _submitted() -> dict[str, int]:
    return json.loads(SUBMITTED.read_text()) if SUBMITTED.exists() else {}


def candidates(paths: dict[str, list], items: dict[str, dict] | None, include_ties=True,
               already: dict[str, int] | None = None) -> list[tuple[int, str, list]]:
    """[(priority, cid, moves)] of our paths that can score now and are shorter
    than what we already uploaded.  Priority: 0 beats the record, 1 nobody
    else solved it, 2 ties the record."""
    out = []
    already = already or {}
    for cid, mv in paths.items():
        if cid in already and len(mv) >= already[cid]:
            continue                               # already uploaded this length or better
        rec = _record_len(items.get(cid, {})) if items else None
        if rec is None:
            out.append((1, cid, mv))
        elif len(mv) < rec:
            out.append((0, cid, mv))
        elif include_ties and len(mv) == rec:
            out.append((2, cid, mv))
    return out


def submit(con, yes=False, note="", include_ties=True, max_batches=1, resubmit=False) -> list[dict]:
    allc = []
    for problem in PROBLEMS:
        try:
            items = snapshot(problem)
        except ApiError as e:
            print(f"warning: could not read {problem} records, considering all verified bests:", e)
            items = None
        c = candidates(our_paths(con, problem), items, include_ties, None if resubmit else _submitted())
        print(f"{problem}: {sum(p == 0 for p, _, _ in c)} beat, {sum(p == 1 for p, _, _ in c)} sole, "
              f"{sum(p == 2 for p, _, _ in c)} tie (not yet uploaded at this length)")
        allc += c
    # point order: record-beaters, sole solver, ties; shorter-gain first within a class
    allc.sort(key=lambda t: (t[0], t[1].startswith("sac-"), t[1]))
    cands = [(cid, mv) for _, cid, mv in allc]
    # re-verify locally with the official code before spending quota
    verdicts = official.verify_many(cands)
    cands = [c for c, v in zip(cands, verdicts) if v["ok"]]
    try:
        lim = (spec().get("data") or {}).get("limits") or {}
    except ApiError:
        lim = {}
    limit = int(lim.get("maxSolutions") or official.MAX_LINES_PER_FILE)
    note = note[:int(lim.get("maxNotesChars") or 2000)]
    batches = [cands[i:i + limit] for i in range(0, len(cands), limit)][:max_batches]
    print(f"{len(cands)} scoring candidates (officially verified); {len(batches)} batch(es) of <= {limit}")
    results = []
    for b in batches:
        text = "\n".join(official.format_line(c, m) for c, m in b) + "\n"
        if len(text.encode()) > int(lim.get("maxBodyBytes") or 10_000_000):
            raise ApiError("batch exceeds maxBodyBytes")
        if not yes:
            print(f"DRY RUN: would submit {len(b)} lines ({b[0][0]} .. {b[-1][0]}); pass --yes to submit")
            continue
        body = {"payload": {"text": text}}
        if note:
            body["meta"] = {"description": note}
        res = call("POST", "/competitions/acc/submissions", body)
        sid = (res.get("data") or {}).get("submissionId")
        sent = _submitted()
        sent.update({c: len(m) for c, m in b})
        SUBMITTED.write_text(json.dumps(sent))
        db.add_insight(con, "submitter", "sair_submission", f"submitted {len(b)} lines", {"submissionId": sid,
                       "lines": len(b), "first": b[0][0], "last": b[-1][0]})
        print("submitted:", sid, f"({len(b)} lines)")
        results.append(res)
    if yes:
        for problem in PROBLEMS:   # keep the dashboard's standings fresh
            try:
                leaderboard(problem)
            except ApiError as e:
                print("leaderboard refresh failed:", e)
    return results


def status(sid: str, wait=True):
    while True:
        res = call("GET", f"/competitions/acc/submissions/{sid}")
        st = (res.get("data") or {}).get("status")
        if not wait or st not in ("queued", "running", "pending", "verifying"):
            return res
        time.sleep(15)


def summarize_status(res: dict) -> str:
    d = res.get("data") or {}
    rs = d.get("results") or []
    ok = [r for r in rs if r.get("ok")]
    bad = [r for r in rs if not r.get("ok")]
    out = [f"status: {d.get('status')}  results: {len(rs)}  ok: {len(ok)}  failed: {len(bad)}"]
    for r in bad[:10]:
        out.append("  FAILED " + json.dumps(r)[:300])
    if bad:   # forget failed lines so they are retried later
        sent = _submitted()
        for r in bad:
            sent.pop(r.get("challenge_id") or r.get("challengeId"), None)
        SUBMITTED.write_text(json.dumps(sent))
    return "\n".join(out)


LEADERBOARD = official.ROOT / "data" / "sair_leaderboard.json"


def load_leaderboard() -> dict:
    return json.loads(LEADERBOARD.read_text()) if LEADERBOARD.exists() else {}


def leaderboard(problem="ac", top=15) -> str:
    d = call("GET", f"/competitions/acc/leaderboard?problem={problem}").get("data") or {}
    mine = (call("GET", f"/competitions/acc/leaderboard/me?problem={problem}").get("data") or {}).get("entry")
    cache = load_leaderboard()
    cache[problem] = {"generated_at": d.get("generatedAt"), "fetched_at": db.now(), "me": mine,
                      "n_teams": len(d.get("items") or []), "top": (d.get("items") or [])[:25]}
    LEADERBOARD.write_text(json.dumps(cache))
    lines = [f"{problem} leaderboard (generated {d.get('generatedAt')}):"]
    for it in (d.get("items") or [])[:top]:
        t = it.get("team") or {}
        lines.append(f"  #{it.get('rank'):>3}  {float(it.get('score') or 0):9.2f} pts  "
                     f"{it.get('currentBestCount', 0):>5} current bests  {t.get('teamName') or t.get('teamNumber')}")
    if mine:
        lines.append(f"  ME: rank {mine.get('rank')}, score {mine.get('score')}, "
                     f"{mine.get('currentBestCount')} current bests")
    else:
        lines.append("  ME: not on the leaderboard yet (no verified current-best solution in the published snapshot)")
    return "\n".join(lines)


def main(argv):
    import argparse
    ap = argparse.ArgumentParser(prog="acsolver sair")
    ap.add_argument("cmd", choices=["me", "spec", "snapshot", "submit", "status", "mine", "leaderboard", "refresh"])
    ap.add_argument("arg", nargs="?")
    ap.add_argument("--yes", action="store_true", help="really submit (consumes daily quota)")
    ap.add_argument("--note", default="")
    ap.add_argument("--no-ties", action="store_true")
    ap.add_argument("--max-batches", type=int, default=1)
    ap.add_argument("--problem", default="ac", choices=list(PROBLEMS))
    ap.add_argument("--resubmit", action="store_true", help="ignore the record of what was already uploaded")
    ap.add_argument("--no-wait", action="store_true")
    a = ap.parse_args(argv)
    con = db.connect()
    try:
        if a.cmd == "me":
            print(json.dumps(me(), indent=1))
        elif a.cmd == "spec":
            print(json.dumps(spec(), indent=1))
        elif a.cmd == "snapshot":
            for problem in PROBLEMS:
                rows = compare({c: len(m) for c, m in our_paths(con, problem).items()}, snapshot(problem))
                print(f"== {problem}: " + ", ".join(f"{k} {len(v)}" for k, v in rows.items()))
                for cid, ours, rec in sorted(rows["behind"], key=lambda t: t[1] - t[2])[:10]:
                    print(f"  behind {cid}: ours {ours} vs record {rec}")
                for cid, ours, rec in sorted(rows["beat"], key=lambda t: t[1] - t[2])[:10]:
                    print(f"  BEAT {cid}: ours {ours} vs record {rec}")
        elif a.cmd == "submit":
            submit(con, yes=a.yes, note=a.note, include_ties=not a.no_ties, max_batches=a.max_batches,
                   resubmit=a.resubmit)
        elif a.cmd == "status":
            res = status(a.arg, wait=not a.no_wait)
            print(summarize_status(res))
        elif a.cmd == "mine":
            print(json.dumps(call("GET", "/competitions/acc/submissions/mine"), indent=1))
        elif a.cmd == "leaderboard":
            print(leaderboard(a.problem))
        elif a.cmd == "refresh":   # snapshots + leaderboards of both problems (for the dashboard)
            for problem in PROBLEMS:
                snapshot(problem)
                print(leaderboard(problem, top=5))
    except ApiError as e:
        print("error:", e)
        return 1
    return 0
