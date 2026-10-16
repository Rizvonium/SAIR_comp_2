#!/usr/bin/env bash
# Long-running driver: controller iterations forever; every N iterations the
# verified results snapshot (results/) is committed and pushed so nothing is
# lost if the container is reclaimed.  Stop with: touch data/STOP
set -u
cd "$(dirname "$0")/.."
N=${COMMIT_EVERY:-3}
BRANCH=$(git rev-parse --abbrev-ref HEAD)
i=0
while [ ! -f data/STOP ]; do
  python3 -m acsolver loop --iterations 1 || sleep 30
  i=$((i+1))
  if [ $((i % N)) -eq 0 ]; then
    git add results/ data/macros.jsonl data/value_model.txt config/ 2>/dev/null
    if ! git diff --cached --quiet; then
      git commit -qm "results: snapshot after controller iteration $i ($(python3 -m acsolver status | head -1))" \
        -m "Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>" \
        -m "Claude-Session: https://claude.ai/code/session_01P3DxKPrtYyb6xBtERJhcyh"
      for t in 2 4 8 16; do git push -q -u origin "$BRANCH" && break; sleep $t; done
      # keep main in sync with the working branch (fast-forward only)
      [ -n "${SYNC_MAIN:-1}" ] && git push -q origin "HEAD:main" || true
    fi
  fi
  # automatic SAIR upload (only when an API key is configured): every
  # SUBMIT_EVERY iterations, upload all verified paths that can score
  # (record-beaters first); ~24 uploads/day at the default, under the 40/day quota
  if [ -n "${SAIR_API_KEY:-}" ] && [ $((i % ${SUBMIT_EVERY:-4})) -eq 0 ]; then
    python3 -m acsolver sair submit --yes --note "${SAIR_NOTE:-AC solver (canonical flood + Aut-orbit transport)}" || true
  fi
done
echo "stopped (data/STOP present)"
