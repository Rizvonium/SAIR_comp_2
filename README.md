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
| `acsolver/mining.py` | n-grams/macro-moves, solve rate by feature/family, length profiles, strategy stats |
| `acsolver/model.py` | numpy MLP value model trained on states of verified paths |
| `acsolver/dashboard.py` | static HTML dashboard |
| `acsolver/export.py` | snapshots and upload-ready submission parts |
| `config/strategy.json` | analyst/AI steering of the controller |
| `results/` | committed snapshot: best paths, submission files, insights, dashboard |

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
