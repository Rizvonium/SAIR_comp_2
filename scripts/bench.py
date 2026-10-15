"""Compare engine configurations on a fixed random sample of scored problems.

usage: python3 scripts/bench.py N SEED '{"strategy":"gbfs",...}' ['{...}' ...]
Prints solved count, mean raw/shortened length and time per configuration.
"""
import json
import random
import statistics
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from acsolver import engine, problems  # noqa: E402

n, seed = int(sys.argv[1]), int(sys.argv[2])
P = problems.ac_problems()
ids = sorted(P)
random.Random(seed).shuffle(ids)
recs = [P[i] for i in ids[:n]]
for cfg in sys.argv[3:]:
    params = json.loads(cfg)
    t = time.time()
    out = engine.run("solve", recs, params=params)
    sol = [o for o in out if o.get("solved")]
    raw = [o["raw_len"] for o in sol]
    fin = [o["len"] for o in sol]
    print(f"{cfg}: solved {len(sol)}/{n} in {time.time() - t:.0f}s; "
          f"median raw {statistics.median(raw) if raw else '-'}; median len {statistics.median(fin) if fin else '-'}; "
          f"solved ids {sorted(o['id'] for o in sol)[:0]}", flush=True)
    Path("/tmp/claude-0").mkdir(exist_ok=True)
