#!/usr/bin/env bash
set -euo pipefail
mkdir -p ../fc-challenge-receipt
printf 'NOT_RUN\n' > ../fc-challenge-receipt/status.txt
trap 'code=$?; if [[ $code -ne 0 ]]; then printf "FAIL: exit=%s\n" "$code" > ../fc-challenge-receipt/status.txt; fi' EXIT
cmp Challenge.lean ../FClikelean/RieszEnergySpheres.lean
lake env lean --version | tee ../fc-challenge-receipt/compiler.txt
lake build Challenge 2>&1 | tee ../fc-challenge-receipt/build.log
printf 'PASS\n' > ../fc-challenge-receipt/status.txt
