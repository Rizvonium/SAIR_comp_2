"""Command line: ``python3 -m acsolver <command>``.

  status                         solved count, totals, recent batches
  batch --preset P [--ids ...|--unsolved|--solved|--all|--training] [--limit N]
        [--order shortest|longest|random] [--set k=v ...] [--repeats R]
  loop  [--iterations N]         controller-driven batches (resumes first)
  resume                         finish interrupted batches
  mine                           insight mining over all runs
  train                          retrain the value model
  dashboard                      regenerate results/dashboard.html
  export                         write snapshots + verified submission parts
  import FILE                    load a best_solutions.jsonl (re-verified)
  transport [--changed] [--budget S] [--stats]  Aut(F2)-orbit transport of verified paths
  note "title" "text"            log an AI/analyst note into insights
"""
from __future__ import annotations

import argparse
import json
import random
import sys

from . import db, export, loop, problems


def _select(con, args) -> list[str]:
    if args.training:
        ids = sorted(problems.training_problems())
    else:
        allp = problems.ac_problems()
        best = db.best_lengths(con)
        if args.ids:
            ids = args.ids
        elif args.unsolved:
            ids = [p for p in allp if p not in best]
        elif args.solved:
            ids = [p for p in allp if p in best]
        else:
            ids = list(allp)
    P = {**problems.ac_problems(), **problems.training_problems()}
    if args.order == "shortest":
        ids.sort(key=lambda i: (len(P[i]["r0"]) + len(P[i]["r1"]), i))
    elif args.order == "longest":
        ids.sort(key=lambda i: (-(len(P[i]["r0"]) + len(P[i]["r1"])), i))
    elif args.order == "random":
        random.Random(args.shuffle_seed).shuffle(ids)
    elif args.order == "best_desc":
        best = db.best_lengths(con)
        ids.sort(key=lambda i: -best.get(i, 0))
    if args.limit:
        ids = ids[: args.limit]
    return ids


def _parse_sets(sets):
    out = {}
    for s in sets or []:
        k, v = s.split("=", 1)
        try:
            out[k] = json.loads(v)
        except json.JSONDecodeError:
            out[k] = v
    return out


def cmd_status(con, args):
    n = len(problems.ac_problems())
    r = con.execute("SELECT COUNT(*) c, SUM(length) s, AVG(length) a FROM best_solutions "
                    "WHERE problem_id LIKE 'ac-%'").fetchone()
    print(f"AC solved: {r['c']}/{n}   total moves: {r['s']}   mean length: {(r['a'] or 0):.2f}")
    opt = con.execute("SELECT COUNT(*) FROM problem_status WHERE optimal=1 AND problem_id LIKE 'ac-%'").fetchone()[0]
    print(f"proven optimal: {opt}")
    runs = con.execute("SELECT COUNT(*), SUM(solved), SUM(secs) FROM runs").fetchone()
    print(f"runs: {runs[0]}  solved runs: {runs[1]}  engine hours: {(runs[2] or 0) / 3600:.2f}")
    for b in con.execute("SELECT * FROM batches ORDER BY batch_id DESC LIMIT 8"):
        print(f"  batch {b['batch_id']:4d} {b['status']:8s} {b['label']:<28s} jobs={b['n_jobs']} "
              f"solved={b['n_solved']} new={b['n_new']} improved={b['n_improved']}")


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    if argv[:1] == ["union"]:  # path union has its own argument parser
        from . import union
        return union.main(argv[1:])
    if argv[:1] == ["sair"]:  # SAIR API client has its own argument parser
        from . import sair
        return sair.main(argv[1:])
    ap = argparse.ArgumentParser(prog="acsolver")
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("status")
    b = sub.add_parser("batch")
    b.add_argument("--preset", required=True, choices=sorted(loop.PRESETS))
    b.add_argument("--ids", nargs="*")
    g = b.add_mutually_exclusive_group()
    g.add_argument("--unsolved", action="store_true")
    g.add_argument("--solved", action="store_true")
    g.add_argument("--training", action="store_true")
    b.add_argument("--limit", type=int)
    b.add_argument("--order", default="shortest", choices=["shortest", "longest", "random", "best_desc", "id"])
    b.add_argument("--shuffle-seed", type=int, default=0)
    b.add_argument("--set", nargs="*", help="override engine params, k=v")
    b.add_argument("--repeats", type=int, default=1)
    b.add_argument("--label")
    b.add_argument("--threads", type=int)
    b.add_argument("--macros")
    b.add_argument("--model")
    lp = sub.add_parser("loop")
    lp.add_argument("--iterations", type=int, default=1)
    lp.add_argument("--threads", type=int)
    sub.add_parser("resume")
    sub.add_parser("mine")
    sub.add_parser("train")
    sub.add_parser("dashboard")
    ex = sub.add_parser("export")
    ex.add_argument("--no-check", action="store_true")
    im = sub.add_parser("import")
    im.add_argument("file")
    tr = sub.add_parser("transport")
    tr.add_argument("--changed", action="store_true",
                    help="only orbits whose records changed since the last transport run")
    tr.add_argument("--no-improve", action="store_true", help="only unsolved targets")
    tr.add_argument("--budget", type=float, help="time budget in seconds")
    tr.add_argument("--threads", type=int, default=2)
    tr.add_argument("--limit", type=int)
    tr.add_argument("--stats", action="store_true", help="print orbit statistics only")
    tr.add_argument("--retry", action="store_true", help="also redo targets already tried with the same donors")
    tr.add_argument("--db", help="database path (default data/acsolver.sqlite)")
    nt = sub.add_parser("note")
    nt.add_argument("title")
    nt.add_argument("text")
    args = ap.parse_args(argv)
    con = db.connect(args.db) if getattr(args, "db", None) else db.connect()

    if args.cmd == "status":
        cmd_status(con, args)
    elif args.cmd == "batch":
        ids = _select(con, args)
        overrides = _parse_sets(args.set)
        label = args.label or f"{args.preset}:{len(ids)}"
        jobs = loop.make_jobs(label + "|" + db.now(), ids, args.preset, overrides, args.repeats)
        cfg = {"preset": args.preset, "overrides": overrides, "selection": vars(args).get("order")}
        bid, stats = loop.submit_batch(con, label, jobs, cfg, threads=args.threads, model=args.model,
                                       macros=args.macros)
        print(json.dumps({"batch": bid, **stats}))
        export.write_snapshot(con)
    elif args.cmd == "resume":
        loop.resume_all(con)
        export.write_snapshot(con)
    elif args.cmd == "loop":
        from . import controller
        controller.run_loop(con, iterations=args.iterations, threads=args.threads)
    elif args.cmd == "mine":
        from . import mining
        mining.mine(con, verbose=True)
    elif args.cmd == "train":
        from . import model
        model.train(con, verbose=True)
    elif args.cmd == "dashboard":
        from . import dashboard
        print(dashboard.render(con))
    elif args.cmd == "export":
        n = export.write_snapshot(con)
        rep = export.write_submission(con, check=not args.no_check)
        from . import stable
        srep = stable.write_stable_submission(con, check=not args.no_check)
        print(json.dumps({"snapshot_rows": n, "ac": rep, "stable": srep}, indent=1))
    elif args.cmd == "import":
        print(export.import_jsonl(con, args.file))
    elif args.cmd == "transport":
        from . import transport
        if args.stats:
            print(json.dumps(transport.orbit_stats(con), indent=1))
        else:
            st = transport.transport_all(con, only_changed=args.changed, improve=not args.no_improve,
                                         threads=args.threads, limit=args.limit, time_budget=args.budget,
                                         retry=args.retry)
            print(json.dumps(st))
            if (st["new"] or st["improved"]) and not args.db:
                export.write_snapshot(con)
    elif args.cmd == "note":
        db.add_insight(con, "analyst", "note", args.title, args.text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
