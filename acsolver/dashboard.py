"""Static HTML dashboard (results/dashboard.html), regenerated each batch.

Self-contained: inline CSS/SVG/JS, no external requests.  Shows solved
count, totals, improvement timeline, length histogram, leaderboards
(shortest paths, biggest improvements, hardest unsolved, best strategies),
controller notes, and a link to the verified submission files.
"""
from __future__ import annotations

import html
import json
import re

from . import db, official, problems

OUT = official.ROOT / "results" / "dashboard.html"

CSS = """
:root{color-scheme:light;--surface:#fcfcfb;--panel:#ffffff;--ink:#0b0b0b;--ink2:#52514e;--muted:#8a8984;
--grid:#e6e5e0;--series:#2a78d6;--accent:#eb6834;--good:#0ca30c;--border:#e2e1dc}
@media (prefers-color-scheme:dark){:root:not([data-theme="light"]){color-scheme:dark;--surface:#1a1a19;
--panel:#222220;--ink:#f0efec;--ink2:#c3c2b7;--muted:#8f8e88;--grid:#33332f;--series:#3987e5;--accent:#d95926;
--good:#0ca30c;--border:#3a3a36}}
:root[data-theme="dark"]{color-scheme:dark;--surface:#1a1a19;--panel:#222220;--ink:#f0efec;--ink2:#c3c2b7;
--muted:#8f8e88;--grid:#33332f;--series:#3987e5;--accent:#d95926;--good:#0ca30c;--border:#3a3a36}
*{box-sizing:border-box}body{margin:0;background:var(--surface);color:var(--ink);
font:14px/1.45 system-ui,-apple-system,Segoe UI,Roboto,sans-serif}
main{max-width:1180px;margin:0 auto;padding-block:20px 60px;padding-left:max(16px,env(safe-area-inset-left,0px));padding-right:max(16px,env(safe-area-inset-right,0px))}
h1{font-size:22px;margin:0 0 4px}h2{font-size:16px;margin:28px 0 10px}
.sub{color:var(--ink2);margin:0 0 18px}
.tiles{display:grid;grid-template-columns:repeat(auto-fit,minmax(min(100%,150px),1fr));gap:12px}
.tile{background:var(--panel);border:1px solid var(--border);border-radius:10px;padding:12px 14px}
.tile .v{font-size:26px;font-weight:650;font-variant-numeric:tabular-nums}.tile .k{color:var(--ink2);font-size:12px}
.grid2{display:grid;grid-template-columns:repeat(auto-fit,minmax(min(100%,480px),1fr));gap:16px}
.card{background:var(--panel);border:1px solid var(--border);border-radius:10px;padding:12px 14px;overflow:auto}
table{border-collapse:collapse;width:100%;font-variant-numeric:tabular-nums}
th,td{text-align:left;padding:4px 8px;border-bottom:1px solid var(--grid);white-space:nowrap}
th{color:var(--ink2);font-weight:600;font-size:12px}td.n,th.n{text-align:right}
code{font-size:12px;color:var(--ink2)}svg text{fill:var(--ink2);font-size:11px}
.axis line,.axis path{stroke:var(--grid)}.bar{fill:var(--series)}.bar:hover{opacity:.75}
.line{fill:none;stroke:var(--series);stroke-width:2}
#tip{position:fixed;pointer-events:none;background:var(--panel);color:var(--ink);border:1px solid var(--border);
border-radius:6px;padding:4px 8px;font-size:12px;display:none;box-shadow:0 2px 8px rgba(0,0,0,.15)}
.note{white-space:pre-wrap;color:var(--ink2);font-size:13px}
.pill{display:inline-block;padding:1px 8px;border-radius:999px;font-size:12px;font-weight:600;border:1px solid var(--border)}
.pill.beating{color:var(--good);border-color:var(--good)}.pill.tied{color:var(--series);border-color:var(--series)}
.pill.behind{color:var(--accent);border-color:var(--accent)}.pill.sole{color:var(--good);border-color:var(--good)}.pill.unsolved{color:var(--muted)}
a{color:var(--series);overflow-wrap:anywhere}
.grid2>*,.tiles>*{min-width:0}
html,body{overflow-x:hidden}
.toggle{float:right;font-size:12px;background:var(--panel);color:var(--ink);border:1px solid var(--border);
border-radius:6px;padding:3px 8px;cursor:pointer}
"""

JS = """
const tip=document.getElementById('tip');
document.querySelectorAll('[data-tip]').forEach(el=>{
 el.addEventListener('mousemove',e=>{tip.style.display='block';tip.textContent=el.dataset.tip;
  tip.style.left=(e.clientX+12)+'px';tip.style.top=(e.clientY+12)+'px'});
 el.addEventListener('mouseleave',()=>tip.style.display='none')});
document.getElementById('theme').onclick=()=>{const r=document.documentElement;
 const dark=r.dataset.theme?r.dataset.theme==='dark':matchMedia('(prefers-color-scheme: dark)').matches;
 r.dataset.theme=dark?'light':'dark'};
"""


def _esc(x):
    return html.escape(str(x))


def _table(headers, rows, num_cols=()):
    h = "".join(f'<th class="{"n" if i in num_cols else ""}">{_esc(c)}</th>' for i, c in enumerate(headers))
    body = "".join("<tr>" + "".join(f'<td class="{"n" if i in num_cols else ""}">{c}</td>'
                                     for i, c in enumerate(r)) + "</tr>" for r in rows)
    return f"<table><thead><tr>{h}</tr></thead><tbody>{body}</tbody></table>"


def _bars(counts: dict, w=520, h=180, xlabel=""):
    if not counts:
        return "<p class='sub'>no data yet</p>"
    keys = sorted(counts)
    lo, hi = keys[0], keys[-1]
    span = list(range(lo, hi + 1))
    mx = max(counts.values())
    pl, pb, pt = 36, 22, 8
    bw = (w - pl - 4) / len(span)
    out = [f'<svg viewBox="0 0 {w} {h}" width="100%" role="img" aria-label="histogram">']
    for t in (0, 0.5, 1):
        y = pt + (h - pt - pb) * (1 - t)
        out.append(f'<line x1="{pl}" x2="{w}" y1="{y:.1f}" y2="{y:.1f}" stroke="var(--grid)"/>'
                   f'<text x="{pl - 4}" y="{y + 4:.1f}" text-anchor="end">{round(mx * t)}</text>')
    for i, k in enumerate(span):
        c = counts.get(k, 0)
        bh = (h - pt - pb) * c / mx
        x = pl + i * bw
        out.append(f'<rect class="bar" x="{x + 1:.1f}" y="{h - pb - bh:.1f}" width="{max(1, bw - 2):.1f}" '
                   f'height="{bh:.1f}" rx="2" data-tip="{xlabel} {k}: {c} problems"/>')
    step = max(1, len(span) // 10)
    for i, k in enumerate(span):
        if i % step == 0:
            out.append(f'<text x="{pl + i * bw + bw / 2:.1f}" y="{h - 6}" text-anchor="middle">{k}</text>')
    out.append("</svg>")
    return "".join(out)


def _line(points, w=520, h=180, ylabel=""):
    if len(points) < 2:
        return "<p class='sub'>not enough history yet</p>"
    xs = list(range(len(points)))
    ys = [p[1] for p in points]
    lo, hi = min(ys), max(ys)
    if hi == lo:
        hi = lo + 1
    pl, pb, pt = 52, 22, 8
    X = lambda i: pl + (w - pl - 6) * i / (len(xs) - 1)  # noqa: E731
    Y = lambda v: pt + (h - pt - pb) * (1 - (v - lo) / (hi - lo))  # noqa: E731
    out = [f'<svg viewBox="0 0 {w} {h}" width="100%" role="img" aria-label="{_esc(ylabel)} over batches">']
    for t in (0, 0.5, 1):
        v = lo + (hi - lo) * t
        out.append(f'<line x1="{pl}" x2="{w}" y1="{Y(v):.1f}" y2="{Y(v):.1f}" stroke="var(--grid)"/>'
                   f'<text x="{pl - 4}" y="{Y(v) + 4:.1f}" text-anchor="end">{round(v)}</text>')
    d = " ".join(f"{'M' if i == 0 else 'L'}{X(i):.1f},{Y(v):.1f}" for i, v in enumerate(ys))
    out.append(f'<path class="line" d="{d}"/>')
    for i, (lab, v) in enumerate(points):
        out.append(f'<circle cx="{X(i):.1f}" cy="{Y(v):.1f}" r="7" fill="transparent" '
                   f'data-tip="{_esc(lab)}: {ylabel} {v}"/>')
    out.append(f'<text x="{pl}" y="{h - 6}">{_esc(points[0][0])}</text>'
               f'<text x="{w - 4}" y="{h - 6}" text-anchor="end">{_esc(points[-1][0])}</text></svg>')
    return "".join(out)


def _timeline(con):
    """Cumulative (solved, total moves) after each batch, replayed from improvements."""
    best, pts_s, pts_m = {}, [], []
    rows = con.execute("SELECT problem_id, new_length, batch_id FROM improvements "
                       "WHERE problem_id LIKE 'ac-%' ORDER BY id").fetchall()
    cur = None
    for r in rows:
        if cur is not None and r["batch_id"] != cur:
            pts_s.append((f"batch {cur}", len(best)))
            pts_m.append((f"batch {cur}", sum(best.values())))
        cur = r["batch_id"]
        best[r["problem_id"]] = r["new_length"]
    if cur is not None:
        pts_s.append((f"batch {cur}", len(best)))
        pts_m.append((f"batch {cur}", sum(best.values())))
    return pts_s, pts_m


def render(con) -> str:
    P = problems.ac_problems()
    best = {r["problem_id"]: r for r in con.execute("SELECT * FROM best_solutions WHERE problem_id LIKE 'ac-%'")}
    status = {r["problem_id"]: r for r in con.execute("SELECT * FROM problem_status")}
    n_solved = len(best)
    total = sum(r["length"] for r in best.values())
    n_opt = sum(1 for p in best if status.get(p) is not None and status[p]["optimal"])
    runs = con.execute("SELECT COUNT(*), SUM(secs) FROM runs").fetchone()
    tiles = [("problems solved", f"{n_solved:,} / {len(P):,}"), ("total moves", f"{total:,}"),
             ("mean path length", f"{total / n_solved:.2f}" if n_solved else "-"),
             ("proven optimal", f"{n_opt:,}"), ("engine runs", f"{runs[0]:,}"),
             ("engine hours", f"{(runs[1] or 0) / 3600:.1f}")]
    from . import sair
    recs, rec_src = sair.load_records("ac")
    kteams = sair.load_kteams("ac")
    cmp_rows, n_beat, n_tie, n_behind = [], 0, 0, 0
    for pid, ours in ((p, r["length"]) for p, r in best.items()):
        rec = recs.get(pid)
        if rec is None:
            state, gap = "sole", None
        elif ours < rec:
            state, gap = "beating", ours - rec
            n_beat += 1
        elif ours == rec:
            state, gap = "tied", 0
            n_tie += 1
        else:
            state, gap = "behind", ours - rec
            n_behind += 1
        cmp_rows.append((pid, ours, rec, gap, state))
    n_others = sum(1 for p in recs if p not in best)
    n_nobody = len(P) - len(recs) - sum(1 for p in best if p not in recs)
    order = {"beating": 0, "sole": 0, "tied": 1, "behind": 2}
    cmp_rows.sort(key=lambda r: (order[r[4]], r[3] if r[3] is not None else -999))
    shown = [r for r in cmp_rows if r[4] != "behind"] + [r for r in cmp_rows if r[4] == "behind"][:40]
    cmp_html = _table(["problem", "my best", "record", "gap", "teams at record", "status"],
                      [(_esc(p), o, r if r is not None else "–", (f"{g:+d}" if g is not None else "–"),
                        kteams.get(p, 0), f'<span class="pill {s}">{s}</span>') for p, o, r, g, s in shown],
                      (1, 2, 3, 4))
    gaps = {}
    for _, o, r, g, s in cmp_rows:
        if s == "behind":
            k = min(g // 10 * 10, 200)
            gaps[k] = gaps.get(k, 0) + 1
    gap_svg = _bars({k // 10: v for k, v in gaps.items()}, xlabel="gap /10 moves")
    lb = sair.load_leaderboard()
    lb_html = ""
    for prob, label in (("ac", "AC"), ("stable_ac", "Stable AC")):
        e = lb.get(prob)
        if not e:
            continue
        rows = [(it.get("rank"), _esc((it.get("team") or {}).get("teamName") or (it.get("team") or {}).get("teamNumber")),
                 f"{float(it.get('score') or 0):.1f}", it.get("currentBestCount")) for it in e["top"][:10]]
        me = e.get("me")
        mine = (f"Our team: rank {me.get('rank')}, {float(me.get('score') or 0):.2f} points, "
                f"{me.get('currentBestCount')} current bests." if me else
                "Our team is not on this leaderboard yet: no verified current-best path in the published standings.")
        lb_html += (f"<div class='card'><b>{label} leaderboard</b> <span class='sub'>(published "
                    f"{_esc(e.get('generated_at'))})</span><p class='sub' style='margin:4px 0 8px'>{_esc(mine)}</p>"
                    + _table(["rank", "team", "points", "current bests"], rows, (0, 2, 3)) + "</div>")
    if recs:
        tiles = [("records beaten", f"{n_beat}"), ("records tied", f"{n_tie}"),
                 ("behind the record", f"{n_behind}"), ("solved by others, not us", f"{n_others:,}"),
                 ("solved by nobody", f"{n_nobody:,}")] + tiles
    tiles_html = "".join(f'<div class="tile"><div class="v">{v}</div><div class="k">{k}</div></div>' for k, v in tiles)

    hist = {}
    for r in best.values():   # buckets of 10 moves, 400+ in the last one
        k = min(r["length"], 400) // 10
        hist[k] = hist.get(k, 0) + 1
    ts, tm = _timeline(con)

    shortest = sorted(best.values(), key=lambda r: (r["length"], r["problem_id"]))[:15]
    sh_rows = [(_esc(r["problem_id"]), r["length"], _esc(r["strategy"]),
                f"<code>{_esc(r['path'][:60])}{'…' if len(r['path']) > 60 else ''}</code>") for r in shortest]
    longest = sorted(best.values(), key=lambda r: -r["length"])[:15]
    lo_rows = [(_esc(r["problem_id"]), r["length"], _esc(r["strategy"]), _esc(r["found_at"])) for r in longest]
    imp = con.execute(
        "SELECT problem_id, MAX(old_length) first_len, MIN(new_length) now_len, COUNT(*) steps FROM improvements "
        "WHERE problem_id LIKE 'ac-%' GROUP BY problem_id HAVING first_len IS NOT NULL "
        "ORDER BY first_len - now_len DESC LIMIT 15").fetchall()
    imp_rows = [(_esc(r["problem_id"]), r["first_len"], r["now_len"], r["first_len"] - r["now_len"], r["steps"])
                for r in imp]
    unsolved = [p for p in P if p not in best and p in status and status[p]["attempts"] > 0]
    hard = sorted(unsolved, key=lambda p: -(status[p]["total_secs"] if p in status else 0))[:15]
    hard_rows = []
    for p in hard:
        s = status.get(p)
        f = problems.features(P[p])
        hard_rows.append((_esc(p), f["total"], f["ms_n"] or "-", s["attempts"] if s else 0,
                          f"{(s['total_secs'] if s else 0):.0f}", s["lower_bound"] if s else 0))
    strat = con.execute(
        "SELECT r.strategy, COUNT(*) n, SUM(r.solved) s, AVG(r.secs) t, "
        "(SELECT COUNT(*) FROM best_solutions b WHERE b.strategy=r.strategy) held, "
        "(SELECT COUNT(*) FROM improvements i WHERE i.strategy=r.strategy) imps "
        "FROM runs r GROUP BY r.strategy ORDER BY held DESC").fetchall()
    st_rows = [(_esc(r["strategy"]), r["n"], r["s"] or 0, f"{(r['s'] or 0) / r['n']:.1%}", f"{r['t'] or 0:.1f}",
                r["held"], r["imps"]) for r in strat]
    batches = con.execute("SELECT * FROM batches ORDER BY batch_id DESC LIMIT 12").fetchall()
    b_rows = [(b["batch_id"], _esc(b["label"]), _esc(b["status"]), b["n_jobs"], b["n_solved"], b["n_new"],
               b["n_improved"], _esc(b["started_at"])) for b in batches]
    notes = con.execute("SELECT * FROM insights WHERE author IN ('controller','analyst') "
                        "ORDER BY id DESC LIMIT 6").fetchall()
    notes_html = "".join(f"<div class='card' style='margin-bottom:10px'><b>{_esc(n['title'])}</b> "
                         f"<span class='sub'>({_esc(n['author'])}, {_esc(n['created_at'])})</span>"
                         f"<div class='note'>{_esc(_pretty(n['body']))}</div></div>" for n in notes) \
        or "<p class='sub'>no notes yet</p>"

    rep = official.ROOT / "results" / "submission_report.json"
    sub_info = ""
    if rep.exists():
        r = json.loads(rep.read_text())
        sub_info = (f"AC: {r['solutions']} verified paths in {len(r['parts'])} upload-ready parts "
                    f"(≤500 lines each, all checked by the official CLI).")
    srep = official.ROOT / "results" / "stable_submission_report.json"
    if srep.exists():
        r = json.loads(srep.read_text())
        sub_info += (f" Stable AC: {r['solutions']} derived paths ({r['total_moves']} moves) in "
                     f"{len(r['parts'])} parts.")

    page = f"""<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><title>ACC Solver Dashboard</title>
<style>{CSS}</style></head><body><main>
<button class="toggle" id="theme">light / dark</button>
<h1>Andrews–Curtis solver — Discovery Track (AC)</h1>
<p class="sub">Generated {_esc(db.now())}. Every path below was accepted by the official SAIR verifier.</p>
<div class="tiles">{tiles_html}</div>
<h2>Me vs the leaderboard</h2>
<div class="grid2">{lb_html}<div class="card"><b>How far behind the record our paths are</b>
<p class="sub" style="margin:4px 0 0">Problems we solved but trail, by gap in moves (bucket 20 = 200 or more).</p>{gap_svg}</div></div>
<div class="card" style="margin-top:16px"><p class="sub" style="margin:0 0 8px">Our best against the shortest verified record
(source: {_esc(rec_src)}). Points go only to the shortest path (k tied teams get 2<sup>1-k</sup> each), so only
<b>beating</b>, <b>sole</b> and <b>tied</b> rows score. Shown: every scoring row and the 40 closest chases.</p>
{cmp_html if recs else "<p class='sub'>No records loaded yet: run <code>python3 -m acsolver sair refresh</code>.</p>"}</div>
<h2>Export</h2>
<div class="card"><a href="submission.txt" download>Download submission.txt</a> (all verified best paths) ·
<a href="submission_parts/">upload-ready parts</a> · <a href="best_solutions.jsonl" download>best_solutions.jsonl</a> ·
<a href="stable_submission.txt" download>stable_submission.txt</a>
<p class="sub" style="margin:6px 0 0">{_esc(sub_info)}</p></div>
<h2>Progress</h2>
<div class="grid2">
<div class="card"><b>Problems solved, after each batch</b>{_line(ts, ylabel="solved")}</div>
<div class="card"><b>Total moves over solved problems, after each batch</b>{_line(tm, ylabel="total moves")}</div>
<div class="card"><b>Best path length distribution</b>{_bars(hist, xlabel="length /10")}</div>
</div>
<h2>Leaderboards</h2>
<div class="grid2">
<div class="card"><b>Shortest paths</b>{_table(["problem", "len", "strategy", "path"], sh_rows, (1,))}</div>
<div class="card"><b>Biggest improvements</b>{_table(["problem", "first", "now", "saved", "records"], imp_rows,
                                                     (1, 2, 3, 4))}</div>
<div class="card"><b>Longest current best paths (most room to improve)</b>{_table(
        ["problem", "len", "strategy", "found"], lo_rows, (1,))}</div>
<div class="card"><b>Hardest unsolved (most effort spent)</b>{_table(
        ["problem", "init len", "MS n", "attempts", "secs", "lower bound"], hard_rows, (1, 3, 4, 5))}</div>
<div class="card"><b>Strategies</b>{_table(["strategy", "runs", "solved", "rate", "mean s", "records", "improvements"],
                                              st_rows, (1, 2, 3, 4, 5, 6))}</div>
<div class="card"><b>Recent batches</b>{_table(["#", "label", "status", "jobs", "solved", "new", "improved",
                                                   "started"], b_rows, (0, 3, 4, 5, 6))}</div>
</div>
<h2>Controller and analyst notes</h2>{notes_html}
</main><div id="tip"></div><script>{JS}</script></body></html>"""
    OUT.parent.mkdir(exist_ok=True)
    OUT.write_text(page)
    PUBLISH.write_text(publishable(page))
    return str(OUT)


PUBLISH = official.ROOT / "data" / "dashboard_publish.html"


def publishable(page: str) -> str:
    """Artifact version: no document skeleton (the host adds it), safe-area
    gutters, and download links shown as file names (downloads are blocked)."""
    m = re.search(r"<title>.*?</title>", page)
    style = re.search(r"<style>.*?</style>", page, re.S).group(0)
    body = page[page.index("<body>") + 6: page.rindex("</body>")]
    body = re.sub(r'<a href="([^"]+)"[^>]*>(.*?)</a>', r"<code>\2</code>", body)
    return (m.group(0) + '\n<meta name="claude:viewport-fit-sides" content="cover">\n' + style + "\n" + body)


def _pretty(body: str) -> str:
    try:
        obj = json.loads(body)
    except (TypeError, json.JSONDecodeError):
        return body
    if isinstance(obj, dict) and "reasoning" in obj:
        return obj["reasoning"]
    return json.dumps(obj, indent=1)[:2000]
