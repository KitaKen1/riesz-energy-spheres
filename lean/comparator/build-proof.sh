#!/usr/bin/env bash
set -euo pipefail
mkdir -p ../build-receipt
# The largest generated kernel certificates may require several six-hour CI runs.
# Only products for the exact checked proof-source digest can resume a partial build.
set +e
LEAN_NUM_THREADS=2 timeout --kill-after=120 305m lake build FCSolution FCAudit 2>&1 | tee ../build-receipt/build.log
RZ_PIPE=("${PIPESTATUS[@]}")
set -e
test "${RZ_PIPE[1]}" -eq 0
if [[ "${RZ_PIPE[0]}" -eq 0 ]]; then
  printf 'ready=true\n' >> "$GITHUB_OUTPUT"
  printf 'PASS\n' > ../build-receipt/status.txt
elif [[ "${RZ_PIPE[0]}" -eq 124 || "${RZ_PIPE[0]}" -eq 137 ]]; then
  printf 'ready=false\n' >> "$GITHUB_OUTPUT"
  printf 'INCOMPLETE: rerun this commit to resume the cached build\n' > ../build-receipt/status.txt
else
  printf 'FAIL: exit=%s\n' "${RZ_PIPE[0]}" > ../build-receipt/status.txt
  exit "${RZ_PIPE[0]}"
fi
