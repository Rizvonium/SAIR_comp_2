"""Like bench.py but also reports the union of solved sets across configs
(to measure diversity between seeds / variants)."""
import json
import random
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
union = set()
for cfg in sys.argv[3:]:
    t = time.time()
    out = engine.run("solve", recs, params=json.loads(cfg))
    s = {o["id"] for o in out if o.get("solved")}
    new = len(s - union)
    union |= s
    print(f"{cfg}: solved {len(s)}/{n} in {time.time() - t:.0f}s; new vs union {new}; union {len(union)}", flush=True)
