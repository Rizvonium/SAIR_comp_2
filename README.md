# Andrews–Curtis solver for the SAIR ACC Challenge (Discovery Track, AC)

A self-improving search system for the
[SAIR Andrews–Curtis Conjecture Challenge](https://github.com/SAIRcompetition/Andrews-Curtis):
a fast C++ engine runs many search strategies in loops; Python stores every
run, verifies every result with the **official verifier**, mines insights,
trains a value model, and a controller steers the next batch.

The official repository is pinned (read-only) as the git submodule
`external/Andrews-Curtis`. Nothing in it is modified; every stored result
was accepted by `verifier.submission.process_submission`, the same function
the official CLI runs.

## Quick start

```sh
git submodule update --init
make                         # builds bin/acengine
make endgame R=8             # shared endgame table (~30 s, ~300 MB on disk)
pip install pytest && make test

python3 -m acsolver batch --preset gbfs --training           # solve the 424 training problems
python3 -m acsolver batch --preset gbfs --unsolved --limit 500 # scored problems, shortest first
python3 -m acsolver loop --iterations 10                       # controller-driven batches
python3 -m acsolver status
python3 -m acsolver export      # results/submission.txt + verified 500-line parts
python3 -m acsolver dashboard   # results/dashboard.html
```

A lost database can be rebuilt from the committed snapshot (every path is
re-verified on import): `python3 -m acsolver import results/best_solutions.jsonl`.

## Layout

| Path | Contents |
|---|---|
| `engine/ac.hpp` | words, the 14 `ac-r2-v1` moves, left-fold free reduction, hashing, node arena |
| `engine/endgame.hpp` | endgame table: exact distance-to-target for all states within radius B of `(x, y)` |
| `engine/search.hpp` | GBFS (compact, 2-bit packed), beam, greedy-random walks, annealing, bidirectional BFS |
| `engine/shorten.hpp` | path shortening: cycle cut, endgame truncation, ball-shortcut DP (window re-optimisation) |
| `engine/features.hpp` | state features + MLP evaluator for the value model |
| `engine/main.cpp` | JSONL CLI: `solve`, `shorten`, `replay`, `features`, `build-endgame`, `random-test` |
| `acsolver/official.py` | bridge to the official verifier (unmodified submodule) |
| `acsolver/db.py` | SQLite schema: runs, best_solutions, improvements, insights, batches, batch_jobs, problem_status |
| `acsolver/loop.py` | batch runner: engine → shortening → official verification → DB (crash-safe, resumable) |
| `acsolver/controller.py` | plans batches from measured yield per action, logs reasoning |
| `acsolver/transport.py` | Aut(F2)-orbit keys (Whitehead) and transport of verified paths along orbits |
| `acsolver/mining.py` | n-grams/macro-moves, solve rate by feature/family, length profiles, strategy stats |
| `acsolver/model.py` | numpy MLP value model trained on states of verified paths |
| `acsolver/dashboard.py` | static HTML dashboard |
| `acsolver/export.py` | snapshots and upload-ready submission parts |
| `config/strategy.json` | analyst/AI steering of the controller |
| `results/` | committed snapshot: best paths, submission files, insights, dashboard |

## How the search works

1. **Endgame table** (`make endgame R=8`): BFS from the target `(x, y)` to
   radius 8 (24.6M states). Any search that touches it finishes with an exact
   shortest suffix; it also makes bidirectional search exact up to length 14.
2. **Corridor table**: every state on every known solution path (our raw and
   shortened paths, plus the 424 published training certificates). The pool
   is one big AC-connected family, so a search for one problem often walks
   into another problem's corridor and finishes along it. Each problem
   ignores its own paths unless explicitly asked (`self_corridor`).
3. **Strategies** (presets in `acsolver/loop.py`): GBFS on total relator
   length (best single heuristic measured), ε-GBFS, beam search, greedy-random
   walks, annealing, bidirectional BFS (exact), and for solved problems:
   `polish` (bigger shortening balls), `guided` (own best path as corridor +
   depth-weighted GBFS, bound = current best) and `tail` (guided search from
   an intermediate state, prefix spliced back).
4. **Shortening** of every solution: cycle cut (subsumes inverse-pair
   cancellation) → endgame/corridor truncation → ball-shortcut DP (every
   path state gets a BFS ball; shortcuts of up to d1+d2 moves between any
   two path states are combined optimally by DP and rebuilt exactly) →
   repeat until no gain.
5. **Verification**: the official verifier judges every candidate; only
   `ok: true` paths are stored.

## Aut(F2)-orbit transport

`acsolver/transport.py` (`python3 -m acsolver transport`, and the controller
action `transport` after every batch). AC moves commute with automorphisms
of F2: if Q = phi(P) up to rotation, inversion and relator order, a verified
path of P becomes a path of Q (prefix of conjugations, P's body with each
conjugation by g replaced by conjugations by the letters of phi(g), then a
short basis -> (x, y) finish). Orbits are identified by Whitehead-minimal
canonical forms (`orbit_key`, cached in `data/orbit_keys.json`). Donors are
all verified paths in the DB plus the 424 training certificates; for each
target, every donor and several orbit maps (stabiliser of the canonical form,
inner part stripped) are tried, shortened by the engine, verified officially
and recorded with strategy `transport`. New records snowball to their orbit
siblings. `python3 -m acsolver transport --stats` prints orbit statistics
(also in the mining report, including the MS-1190 open classes).

## Controller: automatic policy + AI analyst

* `acsolver/controller.py` (automatic, every batch): measures verified gain
  per engine-hour for each action type (`cover`, `escalate`, `bidir`,
  `polish`, `resolve`), allocates the next batch accordingly with an
  exploration bonus, walks unsolved problems up an escalation ladder, and
  writes its plan and review (with reasoning) to the `insights` table.
* The AI analyst (Claude, in the session) reads the insight report and
  benchmarks, forms hypotheses, tests them (`scripts/bench*.py`), records
  conclusions with `python3 -m acsolver note`, and steers the controller by
  editing `config/strategy.json` (weights, presets, ladder, model/macros).
* Guardrails: neither touches the official verifier or data (read-only
  submodule); every stored result passed the official verifier.

## Stable AC (Phase 2)

`acsolver/stable.py` derives `sac-` solutions from verified AC paths: the AC
path truncated at its cheapest signed-permutation state plus the official
stable finish (2–4 moves). On the training set this beats "AC path +
[16, 15]" (14,219 vs 15,105 moves); all paths pass the official stable
verifier. Export writes `results/stable_submission*.txt`.

## Engine correctness

`tests/test_engine_crosscheck.py` is blocking: the engine's replay must match
the official verifier on all 424 training certificates (target, work, peak)
and on thousands of random start states and move sequences, step by step.
Every path the engine emits is replayed before output, and then verified
officially before storage.

## Submission limits worth knowing

* At most **500 solution lines per file** and 40 uploads per day, so the
  10,115 problems need ≥ 21 files. `results/submission.txt` holds every
  best path (reference); `results/submission_parts/part_NN.txt` are the
  upload-ready files, each checked with the official CLI (exit 0, all `ok`).
* Scoring rewards only the shortest path per problem (ties split
  `2^(1-k)`), so the loop keeps polishing solved problems.
