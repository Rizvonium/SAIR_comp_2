# Lean Kernel Challenge (Stage 1) — working notes

Team LKC01-T00264 (owner Rizwan). Deadline **2026-11-20 23:59 AoE**. Official repo
cloned read-only at `/home/user/lkc/lean-kernel-challenge` (rules in `rules/`, specs in
`problems/<id>/Spec.lean`, worked examples in `examples/<id>/Submission.lean`).

## What is scored
For each problem, the judge proves nothing new: it checks `impl_correct : ∀ n, impl n = spec n`
(universal proof, permitted axioms `propext`, `Quot.sound`, `Classical.choice` only; no `sorry`,
`native_decide`, lookup tables, hardcoded answers, `partial`/`unsafe`). Then for each hidden
input `n` it kernel-checks `Submission.impl n = v` with proof `Eq.refl v` (raw Nat literal,
`Int.ofNat`/`Int.negSucc` for Int) and counts kernel instructions. Score per problem = sum over
cases of the median of 3 replays; lowest wins. The **latest** formal submission per problem is
selected (not the best) — never submit anything not validated.

## Tools
- `python3 lean_kernel/bench.py PROBLEM FILE.lean [--workdir NAME] [--inputs a,b,c] [--seeds k]`
  builds the file in a private copy of the official workspace (warnings are errors), checks
  axioms, and times the kernel check of `impl n = v` exactly like the judge (synchronous
  `Environment.addDeclCore`). Default inputs = endpoints of every official test group.
  **Use your own `--workdir`** (e.g. `partition-a1`) so concurrent runs do not collide.
- `python3 lean_kernel/submit.py PROBLEM FILE.lean --yes` (lead only) — formal submission.
- Lean 4.33.1 via elan (`export PATH=$HOME/.elan/bin:$PATH`). Mathlib (pinned) is shared for
  fib/mertens/primecount through a symlinked `.lake/packages`.

## Kernel cost model (measured locally, wall time)
| thing | cost |
|---|---|
| fixed cost of one `impl n = v` check | ~21 µs |
| `a * 3 + 1` written with `*`, `+`, numerals (typeclass unfolding) | ~27 µs |
| same with raw primitives `Nat.add (Nat.mul a (nat_lit 3)) (nat_lit 1)` | ~1 µs |
| one raw `Nat.rec` loop step (accumulator style) | ~2–3 µs |
| one equation-compiler (`match`/structural) recursive step | ~9 µs |
| one `List.range`/`foldl` step | ~37 µs |
| a primitive op on a 65,536-bit Nat vs a 64-bit Nat | about the same |

More measurements (2026-11-11, fib work):
| thing | cost |
|---|---|
| `Nat.log2 n` | 12–80 µs: NOT kernel-accelerated (well-founded recursion) — avoid |
| `cond b x y` | ~10 µs (unfolds a matcher) |
| `Bool.rec (motive := fun _ => α) y x b` or `Nat.rec` on a 0/1 literal | ~1 µs |
| threading a `Prod` through a `Nat.rec` loop | ~4.6 µs/step extra |
| continuation-style loop `Nat.rec (motive := fun _ => Nat → Nat → Nat)` passing state as plain args | cheapest loop shape found |

Bit-length trick without `log2`: compute any cheap guess `c` and use
`L := Bool.rec n c (Nat.beq (Nat.shiftRight n c) 0)`; correctness only needs `n >>> L = 0`,
which holds in both branches (`n >>> n = 0`). See `solutions/fib/v2_cps_boolrec.lean`.

Rules of thumb:
1. In the computational path use the kernel-accelerated primitives directly: `Nat.add sub mul div
   mod land lor xor shiftLeft shiftRight pow beq ble gcd` with `nat_lit k` constants (NOT `log2`).
   Avoid `HAdd/HMul/...` notation, `OfNat` numerals, `decide`, `if` on `Prop` (`Nat.decEq`
   unfolds), `cond`, `List`, `Array`, `Prod` where possible. Branch with `Bool.rec` on
   `Nat.beq`/`Nat.ble` results, or `Nat.rec` on a 0/1 value.
2. Minimize the number of kernel reduction steps; loops cost µs per iteration, big-number
   arithmetic is almost free. Bit-parallel (SWAR) encodings in one big `Nat` beat per-element
   loops by orders of magnitude.
3. Write loops with raw `Nat.rec` (or `Nat.repeat`-like folds); avoid equation-compiler recursion
   and well-founded recursion (WF does not reduce well in the kernel).
4. Raw forms are definitionally equal to the notation forms, so proofs can `show`/`change` to
   the notation form and use ordinary lemmas.
5. Keep `impl` computable (bench evaluates it to get the expected value).

## Leaderboard snapshot (2026-11-11, instructions, lower is better)
| problem | #1 | #5 | median | teams |
|---|---:|---:|---:|---:|
| ca-rule110 | 3.01M | 3.08M | 5.4M | 55 |
| fib | 3.71M | 6.93M | 13.3M | 65 |
| mertens | 1.52M | 1.59M | 10.0M | 46 |
| partition | 1.42M | 1.43M | 3.6M | 62 |
| permanent | 24.3M | 27.4M | 280M | 50 |
| polydisc | 649M | 756M | 2.49B | 49 |
| primecount | 1.42M | 1.45M | 4.3M | 49 |
| sha256 | 8.91B | 9.63B | 12.8B | 48 |

## Submissions
See `submissions.jsonl`. v0 = official examples (all 8 submitted 2026-11-11).

## First official edition with our entries (2026-11-12 08:00 UTC, cutoff 00:00 UTC)
| problem | our rank | our total (official) | #1 | median | version scored |
|---|---:|---:|---:|---:|---|
| fib | 39/66 | 18.10M | 3.72M | 13.4M | v2 |
| partition | 43/64 | 17.61M | 1.39M | 4.43M | v1 |
| ca-rule110 | 56/56 | 2.16B | 3.01M | 5.98M | v0 example |
| mertens | 43/48 | 7.15B | 1.50M | 10.96M | v0 example |
| primecount | 50/50 | 6.03B | 1.39M | 4.81M | v0 example |
| permanent | 49/51 | 698B | 23.9M | 425M | v0 example |
| polydisc | 45/50 | 10.3B | 632M | 2.60B | v0 example |
| sha256 | 46/50 | 183B | 8.90B | 17.5B | v0 example |

Calibration: official / bench_ir ≈ 1.0 (fib v2 18.10M vs 17.06M local; partition v1 17.61M vs
18.56M local). The earlier "×1.4" guess was wrong: bench_ir numbers are directly comparable.
