#!/usr/bin/env bash
set -euo pipefail
mkdir -p ../library-receipt
set +e
LEAN_NUM_THREADS=2 timeout --kill-after=120 305m lake build Riesz.SphereOptimalMain24 2>&1 | tee ../library-receipt/build.log
RZ_PIPE=("${PIPESTATUS[@]}")
set -e
if [[ ${RZ_PIPE[0]} -eq 0 && ${RZ_PIPE[1]} -eq 0 ]]; then
  printf 'PASS\n' > ../library-receipt/status.txt
elif [[ ${RZ_PIPE[0]} -eq 124 || ${RZ_PIPE[0]} -eq 137 ]]; then
  printf 'INCOMPLETE: resume exact library digest\n' > ../library-receipt/status.txt
else
  printf 'FAIL: exit=%s\n' "${RZ_PIPE[0]}" > ../library-receipt/status.txt
fi
test "${RZ_PIPE[0]}" -eq 0
test "${RZ_PIPE[1]}" -eq 0
