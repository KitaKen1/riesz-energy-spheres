#!/usr/bin/env bash
# Every batch must finish. Time limits are failures, never successful checkpoints.
set -euo pipefail
RZ_STAGE=$1
RZ_RECEIPT="../build-stage-${RZ_STAGE}-receipt"
mkdir -p "$RZ_RECEIPT"
python3 comparator/build-stage.py --stage "$RZ_STAGE" \
  --targets "$RZ_RECEIPT/targets.txt" > "$RZ_RECEIPT/batch.json"
mapfile -t RZ_TARGETS < "$RZ_RECEIPT/targets.txt"
printf 'NOT_COMPLETED\n' > "$RZ_RECEIPT/status.txt"
set +e
LEAN_NUM_THREADS=2 /usr/bin/time -v timeout --kill-after=120 240m \
  lake build "${RZ_TARGETS[@]}" 2>&1 | tee "$RZ_RECEIPT/build.log"
RZ_PIPE=("${PIPESTATUS[@]}")
set -e
if [[ ${RZ_PIPE[0]} -ne 0 || ${RZ_PIPE[1]} -ne 0 ]]; then
  printf 'FAIL: compile=%s log=%s\n' "${RZ_PIPE[0]}" "${RZ_PIPE[1]}" > "$RZ_RECEIPT/status.txt"
  exit 1
fi
printf 'PASS\n' > "$RZ_RECEIPT/status.txt"
printf 'ready=true\n' >> "$GITHUB_OUTPUT"
