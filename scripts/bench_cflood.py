"""Benchmark a strategy preset on a subset of scripts/hard_sample.json.

Runs the engine exactly as acsolver.loop does (preset params + shortening),
verifies every path with the official verifier, writes nothing to any DB.

    python3 scripts/bench_cflood.py ms1190_uncertified --preset cflood --threads 2
    python3 scripts/bench_cflood.py bench80 --start 0 --stop 40 --shorten_time 30 --out res.jsonl
"""
from __future__ import annotations

import argparse
import json
import statistics
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from acsolver import engine, loop, official, problems  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("subset")
    ap.add_argument("--preset", default="cflood")
    ap.add_argument("--start", type=int, default=0)
    ap.add_argument("--stop", type=int, default=None)
    ap.add_argument("--threads", type=int, default=2)
    ap.add_argument("--shorten_time", type=float, default=None)
    ap.add_argument("--no_shorten", action="store_true")
    ap.add_argument("--set", action="append", default=[], help="override k=v")
    ap.add_argument("--trivial", default=None)
    ap.add_argument("--out", default=None)
    ap.add_argument("--unsolved_from", action="append", default=[],
                    help="restrict to the problems a previous --out file did not solve")
    a = ap.parse_args()
    ids = json.loads((ROOT / "scripts" / "hard_sample.json").read_text())[a.subset][a.start:a.stop]
    if a.unsolved_from:
        prev = [json.loads(l) for f in a.unsolved_from for l in open(f)]
        failed = {o["id"] for o in prev if not o.get("solved")}
        ids = [i for i in ids if i in failed]
    P = problems.ac_problems()
    params = {**loop.SHORTEN_DEFAULT, **loop.PRESETS[a.preset]}
    if a.shorten_time is not None:
        params["shorten_time"] = a.shorten_time
    for kv in a.set:
        k, v = kv.split("=", 1)
        params[k] = v
    recs = [{"id": i, "r0": P[i]["r0"], "r1": P[i]["r1"], "params": params} for i in ids]
    gopts = {"emit_raw": 1}
    if not a.no_shorten:
        gopts["shorten"] = 1
    triv = a.trivial or engine.default_trivial()
    if triv:
        gopts["trivial"] = str(triv)
    t0 = time.time()
    out = list(engine.stream("solve", recs, params=gopts, threads=a.threads))
    wall = time.time() - t0
    solved = [o for o in out if o.get("solved")]
    ver = official.verify_many([(o["id"], o["path"]) for o in solved])
    ok = [o for o, v in zip(solved, ver) if v["ok"]]
    for o, v in zip(solved, ver):
        o["official_ok"] = bool(v["ok"])
    if a.out:
        with open(a.out, "w") as f:
            for o in out:
                f.write(json.dumps(o) + "\n")
    for o in sorted(out, key=lambda o: ids.index(o["id"])):
        print(o["id"], "SOLVED" if o.get("solved") else "-", "raw", o.get("raw_len"), "len", o.get("len"),
              "water", o.get("water"), "lb", o.get("barrier_lb"), "nodes", o.get("nodes"),
              "%.1fs" % o.get("secs", 0), o.get("note", ""), "" if not o.get("solved") else
              ("OK" if o.get("official_ok") else "REJECTED"))
    lens = [o["len"] for o in ok]
    raws = [o["raw_len"] for o in ok]
    print(f"{a.subset}[{a.start}:{a.stop}] preset={a.preset}: solved {len(solved)}/{len(out)}, "
          f"official ok {len(ok)}, wall {wall:.0f}s, engine secs {sum(o.get('secs', 0) for o in out):.0f}")
    if lens:
        print(f"  final len: median {statistics.median(lens)}, mean {statistics.mean(lens):.0f}, "
              f"min {min(lens)}, max {max(lens)}; raw median {statistics.median(raws)}, sum raw {sum(raws)} -> "
              f"final {sum(lens)}")


if __name__ == "__main__":
    main()
