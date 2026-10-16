# Paths from public prior work

`ac_public_paths.txt`: 218 verified `ac-r2-v1` paths for scored AC problems, converted from
public data (each line's comment names its source commit):

- shehper/AC-Solver (MIT), commit fd65d8f: greedy Miller–Schupp paths
  (`ac_solver/search/miller_schupp/data/greedy_search_paths.txt`) and PPO notebook paths;
  Shehper et al. 2024, "What makes math problems hard for reinforcement learning: a case study".
- Math-AI-Caltech/ACSolverX (code MIT, data CC BY 4.0), commit 6a12515: solved supermove
  paths from the PPO checkpoint `ppo_checkpoints/610model/1000/solve_data`
  (Fagan, Shehper, Gukov et al., arXiv 2606.21611).

Imported on 2026-10-16 with `python3 -m acsolver import` (official verifier): 29 problems
new to us, the rest longer than our paths. All 218 already had SAIR records.

`scripts/public_data/` holds the converters; `build_pub_corridor.py` expands the 146,099
ACSolverX solved paths into a corridor file (`data/public_corridors.jsonl`, not committed).
A test on 12 problems nobody has solved found no corridor hits, so it is not loaded by the loop.
