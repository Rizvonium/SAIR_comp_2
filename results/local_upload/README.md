# Local results upload

Drop solution files from another machine here (GitHub web: Add file -> Upload files):

- `best_solutions.jsonl` (preferred: every verified best path), or
- submission TXT files (`ac-00001: [0, 2, 6]` lines, e.g. `part_01.txt`).

Import them (every path is re-verified with the official verifier; only new or
shorter paths replace stored ones):

    python3 -m acsolver import results/local_upload/
