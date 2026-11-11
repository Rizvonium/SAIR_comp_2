"""Exact kernel instruction counts (the leaderboard metric) with valgrind/callgrind.

For each input n, a fresh Lean process builds the judge-shaped declaration
`Submission.impl n = v` (proof `Eq.refl v`) and kernel-checks it three times via
`Environment.addDeclCore` (three differently named copies, like the judge's three
replays).  Callgrind counts instructions only inside `lean_elab_add_decl` and dumps
after every call (`--dump-after`), so each replay gets its own count; the last three
dumps are the replays (earlier dumps are the harness's own auxiliary declarations,
which cost ~1.7M and must NOT be counted).  We report the median of the three, like
the judge.  Calibration: a trivial `impl n := n` costs ~166K per case here; the
official per-case floor on the leaderboard is ~236K (different hardware/counters), so
expect the same order of magnitude, not identical numbers.

usage: python3 lean_kernel/bench_ir.py PROBLEM FILE.lean [--workdir NAME] [--inputs a,b,...]
           [--values v1,v2,...] [--annotate]
`--values` gives the expected outputs (same order as --inputs) when impl is
noncomputable; `--annotate` prints the hottest functions of the median replay.
Only works in core-only workspaces (valgrind dies when Mathlib is loaded): for
Mathlib problems benchmark the computational definitions alone in a core workspace.
"""
from __future__ import annotations

import argparse
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import bench  # noqa: E402

ONE = r"""import Submission
import Lean
set_option maxRecDepth 4000000
set_option maxHeartbeats 0
open Lean Meta Elab

def rhsExpr : __OUT__ → Expr
__RHS__

run_meta do
  let n : Nat := __N__
  let v := __VALUE__
  let lhs := mkApp (mkConst ``Submission.impl) (mkNatLit n)
  let rhs := rhsExpr v
  let ty ← mkEq lhs rhs
  let pf ← mkEqRefl rhs
  for i in [1, 2, 3] do
    let decl := Declaration.thmDecl
      { name := Name.mkSimple s!"irCheck{n}_{i}", levelParams := [], type := ty, value := pf }
    match (← getEnv).addDeclCore 0 4000000 decl none with
    | .ok _ => IO.println s!"IR n={n} replay {i} ok"
    | .error _ => IO.println s!"IR n={n} replay {i} REJECTED"
"""


def dump_total(path: Path) -> int | None:
    for line in path.read_text().splitlines():
        if line.startswith("summary:") or line.startswith("totals:"):
            return int(line.split()[1])
    return None


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("problem")
    ap.add_argument("submission")
    ap.add_argument("--workdir")
    ap.add_argument("--inputs")
    ap.add_argument("--seeds", type=int, default=1)
    ap.add_argument("--timeout", type=int, default=3600)
    ap.add_argument("--values", help="expected outputs (same order as --inputs); needed when impl is noncomputable")
    ap.add_argument("--annotate", action="store_true", help="print the hottest functions of the median replay")
    a = ap.parse_args(argv)
    d = bench.prepare(a.problem, a.workdir)
    shutil.copy(a.submission, d / "Submission.lean")
    rc, out, _ = bench.run(["lake", "build"], d, a.timeout)
    if rc != 0:
        print(out[-3000:])
        return 1
    inputs = [int(x) for x in a.inputs.split(",")] if a.inputs else bench.default_inputs(a.problem, a.seeds)
    is_int = a.problem in bench.OUT_INT
    vals = None
    if a.values:
        vs = [v.strip() for v in a.values.split(",")]
        vals = {n: (f"({v} : Int)" if is_int else v) for n, v in zip(inputs, vs)}
    rc, lean_path, _ = bench.run(["lake", "env", "printenv", "LEAN_PATH"], d, 600)
    lean_bin = Path.home() / ".elan/toolchains/leanprover--lean4---v4.33.1/bin/lean"
    total = 0
    for n in inputs:
        src = (ONE.replace("__OUT__", "Int" if is_int else "Nat")
               .replace("__RHS__", bench.RHS_INT if is_int else bench.RHS_NAT)
               .replace("__N__", str(n))
               .replace("__VALUE__", vals[n] if vals else "Submission.impl n"))
        (d / "BenchIr.lean").write_text(src)
        with tempfile.TemporaryDirectory() as tmp:
            outfile = Path(tmp) / "cg.out"
            cmd = ["valgrind", "--tool=callgrind", f"--callgrind-out-file={outfile}",
                   "--toggle-collect=lean_elab_add_decl", "--dump-after=lean_elab_add_decl",
                   str(lean_bin), "BenchIr.lean"]
            e = bench.env()
            e["LEAN_PATH"] = lean_path.strip()
            p = subprocess.run(cmd, cwd=d, env=e, capture_output=True, text=True, timeout=a.timeout)
            ok = all(f"IR n={n} replay {i} ok" in p.stdout for i in (1, 2, 3))
            dumps = sorted(Path(tmp).glob("cg.out.*"), key=lambda q: int(q.suffix[1:]))
            counts = [dump_total(q) for q in dumps]
            if not ok or len(counts) < 3 or any(c is None for c in counts[-3:]):
                print(f"IR n={n} FAILED ok={ok} dumps={len(counts)}\n{p.stdout[-500:]}\n{p.stderr[-1500:]}")
                return 1
            reps = counts[-3:]
            med = sorted(reps)[1]
            total += med
            print(f"IR n={n} instructions={med:,} replays={','.join(f'{c:,}' for c in reps)}")
            if a.annotate:
                q = dumps[-3:][reps.index(med)]
                ann = subprocess.run(["callgrind_annotate", "--inclusive=no", str(q)],
                                     capture_output=True, text=True).stdout
                body = [ln for ln in ann.splitlines() if ln.strip()]
                start = next((i for i, ln in enumerate(body) if "file:function" in ln), 0)
                print("\n".join(body[start:start + 30]))
    print(f"IR_RESULT problem={a.problem} total_instructions={total:,} cases={len(inputs)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
