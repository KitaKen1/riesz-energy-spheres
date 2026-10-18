#!/usr/bin/env bash
set -euo pipefail
RZ_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
: "${COMPARATOR_TOOLS:?Run install-tools.sh first}"
RZ_DIMENSION=${1:?Select sphere dimension 2, 8 or 24}
case "$RZ_DIMENSION" in 2|8|24) ;; *) exit 2 ;; esac
RZ_RECEIPT="$RZ_ROOT/comparator-S${RZ_DIMENSION}-receipt"
mkdir -p "$RZ_RECEIPT"
printf 'NOT_RUN\n' > "$RZ_RECEIPT/status.txt"
trap 'code=$?; if [[ $code -ne 0 ]]; then printf "FAIL: exit=%s\n" "$code" > "$RZ_RECEIPT/status.txt"; fi' EXIT
python3 "$RZ_ROOT/lean/comparator/check-inputs.py" --receipt-dir "$RZ_RECEIPT"
test "$(uname -s)" = Linux
python3 - "$RZ_ROOT/lean/comparator/pins.json" "$COMPARATOR_TOOLS" "$RZ_ROOT/lean/lean-toolchain" "$RZ_RECEIPT/checker-environment.json" <<'PY'
from pathlib import Path
import hashlib, json, re, subprocess, sys
pins=json.load(open(sys.argv[1])); tools=Path(sys.argv[2])
for tool,key in [('comparator','comparator_commit'),('landrun','landrun_commit'),('lean4export','lean4export_commit')]:
    actual=subprocess.check_output(['git','-C',str(tools/tool),'rev-parse','HEAD'],text=True).strip()
    if actual!=pins[key]: raise SystemExit('Tool commit differs: '+tool)
for name in ['comparator','lean4export']:
    if (tools/name/'lean-toolchain').read_bytes()!=Path(sys.argv[3]).read_bytes():
        raise SystemExit('Toolchain differs from proof: '+name)
    changed=subprocess.check_output(['git','-C',str(tools/name),'diff','--name-only'],text=True).splitlines()
    if changed!=['lean-toolchain']:
        raise SystemExit('Unexpected checker source changes: '+name)
versions={}
for name,directory in [('proof',Path(sys.argv[3]).parent),('comparator',tools/'comparator'),('lean4export',tools/'lean4export')]:
    version=subprocess.check_output(['lake','env','lean','--version'],cwd=directory,text=True).strip()
    if not re.search(r'Lean \(version 4\.34\.1(?:,|\))',version):
        raise SystemExit('Compiler must be exactly Lean 4.34.1: '+name+': '+version)
    versions[name]=version
binaries={name:hashlib.sha256((tools/name/'.lake/build/bin'/name).read_bytes()).hexdigest()
          for name in ['comparator','lean4export']}
Path(sys.argv[4]).write_text(json.dumps({'status':'PASS','required_version':'4.34.1',
    'compiler_versions':versions,'binary_sha256':binaries,
    'source_changes':['lean-toolchain']},indent=2)+'\n')
PY
for RZ_FILE in lean/comparator/pins.json .github/workflows/comparator.yml lean/FCSolution.lean lean/FCTargetDefinitions.lean; do
  cp "$RZ_ROOT/$RZ_FILE" "$RZ_RECEIPT/$(basename "$RZ_FILE")"
done
cp "$RZ_ROOT/lean/comparator.json" "$RZ_RECEIPT/comparator-all.json"
python3 "$RZ_ROOT/lean/comparator/dimension-config.py" --dimension "$RZ_DIMENSION" \
  --output "$RZ_RECEIPT/comparator.json"
{
  printf 'run_url=%s/%s/actions/runs/%s\n' "${GITHUB_SERVER_URL:-https://github.com}" "${GITHUB_REPOSITORY:-local}" "${GITHUB_RUN_ID:-local}"
  printf 'run_attempt=%s\ntested_commit=%s\n' "${GITHUB_RUN_ATTEMPT:-local}" "$(git -C "$RZ_ROOT" rev-parse HEAD)"
  date -u +started_utc=%FT%TZ
  uname -a; id
  (cd "$RZ_ROOT/lean" && lake env lean --version)
  for RZ_TOOL in comparator landrun lean4export; do
    printf '%s_commit=%s\n' "$RZ_TOOL" "$(git -C "$COMPARATOR_TOOLS/$RZ_TOOL" rev-parse HEAD)"
  done
  (cd "$COMPARATOR_TOOLS/comparator" && lake env lean --version)
  (cd "$COMPARATOR_TOOLS/lean4export" && lake env lean --version)
  git -C "$COMPARATOR_TOOLS/comparator" diff -- lean-toolchain
  git -C "$COMPARATOR_TOOLS/lean4export" diff -- lean-toolchain
  printf 'sandbox: unprivileged uid/gid, RestrictAddressFamilies=~AF_UNIX, NoNewPrivileges=yes\n'
} > "$RZ_RECEIPT/environment.txt"
set +e
sudo systemd-run --wait --collect --pipe \
  --uid="$(id -u)" --gid="$(id -g)" \
  --property='RestrictAddressFamilies=~AF_UNIX' --property=NoNewPrivileges=yes \
  --property=RuntimeMaxSec=300min --working-directory="$RZ_ROOT/lean" \
  --setenv="PATH=$PATH" --setenv="HOME=$HOME" \
  --setenv="COMPARATOR_LANDRUN=$COMPARATOR_TOOLS/bin/landrun" \
  --setenv="COMPARATOR_LEAN4EXPORT=$COMPARATOR_TOOLS/lean4export/.lake/build/bin/lean4export" \
  -- /usr/bin/stdbuf -oL -eL "$HOME/.elan/bin/lake" env \
  "$COMPARATOR_TOOLS/comparator/.lake/build/bin/comparator" "$RZ_RECEIPT/comparator.json" \
  2>&1 | tee "$RZ_RECEIPT/comparator.log"
RZ_PIPE=("${PIPESTATUS[@]}")
set -e
test "${RZ_PIPE[0]}" -eq 0
test "${RZ_PIPE[1]}" -eq 0
grep -Fxq 'Lean default kernel accepts the solution' "$RZ_RECEIPT/comparator.log"
grep -Fxq 'Your solution is okay!' "$RZ_RECEIPT/comparator.log"
python3 "$RZ_ROOT/lean/comparator/check-inputs.py" --receipt-dir "$RZ_RECEIPT/after"
# Inspect the solution only after the sandboxed Comparator has accepted it.
(cd "$RZ_ROOT/lean" && lake env lean FCAudit.lean) 2>&1 | tee "$RZ_RECEIPT/axioms.log"
python3 "$RZ_ROOT/lean/comparator/check-axioms.py" "$RZ_RECEIPT/axioms.log" "$RZ_RECEIPT/axioms.json"
printf 'PASS\n' > "$RZ_RECEIPT/status.txt"
