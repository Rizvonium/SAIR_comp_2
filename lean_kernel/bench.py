"""Local kernel benchmark for Lean Kernel Challenge submissions.

Mirrors the judge's timing theorem: for each input n, the declaration
`Submission.impl n = v` with proof `Eq.refl v` (raw Nat literal, or
Int.ofNat / Int.negSucc for Int outputs) is type-checked by the KERNEL alone
(`Environment.addDeclCore`, synchronous), and its wall time is measured.
`v` comes from evaluating `Submission.impl n` in Lean; a wrong `v` makes the
kernel reject the declaration, so a pass also checks the value.
Also builds the submission (lake build, warnings as errors) and checks that
`impl_correct` uses only the permitted axioms.

usage: python3 lean_kernel/bench.py PROBLEM SUBMISSION.lean [--inputs n1,n2,...] [--seeds 3]
"""
from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

REPO = Path("/home/user/lkc/lean-kernel-challenge")
WORK = Path("/home/user/lkc/work")
ELAN = Path.home() / ".elan" / "bin"
PERMITTED = {"propext", "Quot.sound", "Classical.choice"}
OUT_INT = {"mertens", "polydisc"}

SEEDS = [0x1234abcd, 0x9e3779b9, 0x0badf00d, 0x7feb352d, 0x31415926]


def default_inputs(problem: str, nseeds: int) -> list[int]:
    cfg = json.loads((REPO / "evaluation/problems" / problem / "config.json").read_text())
    out = []
    for g in cfg["evaluation"]["groups"]:
        s = g["sampling"]
        if s["kind"] == "geometric_range":
            out += [s["min"], s["max"]]
        elif s["kind"] == "uniform_int":
            out += [s["min"], (s["min"] + s["max"]) // 2]
        elif s["kind"] == "packed":
            out += [(s["scale"] << 32) | sd for sd in SEEDS[:nseeds]]
    return out


def env():
    import os
    e = dict(os.environ)
    e["PATH"] = f"{ELAN}:{e['PATH']}"
    return e


def run(cmd, cwd, timeout):
    t = time.time()
    p = subprocess.run(cmd, cwd=cwd, env=env(), capture_output=True, text=True, timeout=timeout)
    return p.returncode, p.stdout + p.stderr, time.time() - t


BENCH = r"""import Submission
import Lean
set_option maxRecDepth 4000000
set_option maxHeartbeats 0
open Lean Meta Elab

def rhsExpr : __OUT__ → Expr
__RHS__

run_meta do
  for n in [__INPUTS__] do
    let v := Submission.impl n
    let lhs := mkApp (mkConst ``Submission.impl) (mkNatLit n)
    let rhs := rhsExpr v
    let ty ← mkEq lhs rhs
    let pf ← mkEqRefl rhs
    let decl := Declaration.thmDecl
      { name := Name.mkSimple s!"benchCheck{n}", levelParams := [], type := ty, value := pf }
    let env ← getEnv
    let t0 ← IO.monoNanosNow
    match env.addDeclCore 0 4000000 decl none with
    | .ok _ =>
      let t1 ← IO.monoNanosNow
      IO.println s!"BENCH n={n} ok ms={(t1 - t0).toFloat / 1000000.0}"
    | .error _ =>
      IO.println s!"BENCH n={n} REJECTED"

#print axioms Submission.impl_correct
"""

RHS_NAT = "  | v => mkNatLit v"
RHS_INT = ("  | .ofNat k => mkApp (mkConst ``Int.ofNat) (mkNatLit k)\n"
           "  | .negSucc k => mkApp (mkConst ``Int.negSucc) (mkNatLit k)")


MATHLIB = {"fib", "mertens", "primecount"}
SHARED_PACKAGES = WORK / "fib" / ".lake" / "packages"   # one pinned Mathlib checkout + cache


def prepare(problem: str, workdir: str | None = None) -> Path:
    """Private copy of the official problem workspace (one per concurrent user)."""
    d = WORK / (workdir or problem)
    if not d.exists():
        shutil.copytree(REPO / "problems" / problem, d)
        if problem in MATHLIB and d != WORK / "fib":
            (d / ".lake").mkdir(exist_ok=True)
            (d / ".lake" / "packages").symlink_to(SHARED_PACKAGES)
    return d


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("problem")
    ap.add_argument("submission")
    ap.add_argument("--inputs")
    ap.add_argument("--seeds", type=int, default=2)
    ap.add_argument("--timeout", type=int, default=1800)
    ap.add_argument("--workdir", help="private work directory name under /home/user/lkc/work (use one per agent)")
    a = ap.parse_args(argv)
    d = prepare(a.problem, a.workdir)
    shutil.copy(a.submission, d / "Submission.lean")
    rc, out, secs = run(["lake", "build"], d, a.timeout)
    print(f"build: rc={rc} {secs:.1f}s")
    if rc != 0:
        print(out[-3000:])
        return 1
    inputs = [int(x) for x in a.inputs.split(",")] if a.inputs else default_inputs(a.problem, a.seeds)
    is_int = a.problem in OUT_INT
    src = (BENCH.replace("__OUT__", "Int" if is_int else "Nat")
           .replace("__RHS__", RHS_INT if is_int else RHS_NAT)
           .replace("__INPUTS__", ", ".join(str(n) for n in inputs)))
    (d / "Bench.lean").write_text(src)
    rc, out, secs = run(["lake", "env", "lean", "Bench.lean"], d, a.timeout)
    total, ok = 0.0, True
    for line in out.splitlines():
        m = re.match(r"BENCH n=(\d+) (ok ms=([\d.e+-]+)|REJECTED)", line)
        if m:
            print(line)
            if m.group(3):
                total += float(m.group(3))
            else:
                ok = False
    axioms = set(re.findall(r"\b(propext|Quot\.sound|Classical\.choice|sorryAx|[A-Za-z_.]+\.\w+)\b",
                            out.split("depends on axioms:")[-1].split("]")[0])) if "depends on axioms" in out else set()
    if "does not depend on any axioms" in out:
        axioms = set()
    bad = axioms - PERMITTED
    print(f"axioms: {sorted(axioms)}{'  <-- NOT PERMITTED' if bad else ''}")
    if rc != 0 and not ok:
        print(out[-2000:])
    print(f"RESULT problem={a.problem} ok={ok and not bad and rc == 0} total_ms={total:.1f} lean_secs={secs:.1f}")
    return 0 if ok and not bad and rc == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
