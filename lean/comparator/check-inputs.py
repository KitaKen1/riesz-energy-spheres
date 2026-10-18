#!/usr/bin/env python3
"""Validate published inputs, reference statements, and the proof-only mirror."""
from pathlib import Path
import argparse, hashlib, json, re, shutil, subprocess, os
import sys

root = Path(__file__).resolve().parents[2]
parser = argparse.ArgumentParser()
parser.add_argument('--receipt-dir', type=Path)
args = parser.parse_args()
manifest = json.loads((root/'SOURCE-MANIFEST.json').read_text())
for name, expected in manifest['files_sha256'].items():
    p = root/name
    if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest() != expected:
        raise SystemExit('Source hash differs: '+name)
proof = root/'lean'
mirror = root/'leanWithoutComparator'
common = manifest['mirror_files']
for name in common:
    if (proof/name).read_bytes() != (mirror/name).read_bytes():
        raise SystemExit('Proof-only mirror differs: '+name)
cfg = json.loads((proof/'comparator.json').read_text())
challenge = (proof/'Challenge.lean').read_text()
solution = (proof/'FCSolution.lean').read_text()
def without_comments(text):
    text = re.sub(r'/\-[\s\S]*?\-/', '', text)
    return re.sub(r'--[^\n]*', '', text)
def theorem_types(text):
    return [re.sub(r'\s+', ' ', s).strip() for s in
        re.findall(r'^theorem ([\s\S]*?) := by\n', text, re.M)]
names = cfg['theorem_names']
defs = (proof/'FCTargetDefinitions.lean').read_text()
imports = re.findall(r'^import (\S+)', defs, re.M)
if not imports or not all(name.startswith('Mathlib.') for name in imports):
    raise SystemExit('Reference definitions must import Mathlib only')
fc_bytes = (root/'FClikelean/RieszEnergySpheres.lean').read_bytes()
fc_sha256 = hashlib.sha256(fc_bytes).hexdigest()
if fc_sha256 != '24c8bbfab4701aa7445ee2090e11f5b26e3a24bb1bb0ad278a3a03818ee95b57':
    raise SystemExit('The user-frozen FClikelean target was changed')
fc = fc_bytes.decode()
fc_imports = re.findall(r'^(?:public )?import (\S+)', fc, re.M)
if not fc_imports or not all(name == 'FormalConjecturesUtil' or name.startswith('Mathlib.')
                             for name in fc_imports):
    raise SystemExit('FC draft must use FormalConjecturesUtil or Mathlib imports only')
if (proof/'Challenge.lean').read_bytes() != (root/'FClikelean/RieszEnergySpheres.lean').read_bytes():
    raise SystemExit('Challenge is not an exact copy of FClikelean/RieszEnergySpheres.lean')
fc_solved = ['RieszSphereFC.'+name for name in re.findall(
    r'@\[category research solved[\s\S]*?\]\s*theorem\s+(\S+)', fc)]
if fc_solved != names or len(names) != 9:
    raise SystemExit('Comparator must select exactly the nine solved FC variants')
fc_names = ['RieszSphereFC.'+t.split()[0] for t in theorem_types(fc)]
if len(fc_names) != 18:
    raise SystemExit('FC draft must retain all eighteen statements')
fc_definitions = without_comments(fc).split('\ntheorem ', 1)[0]
if re.search(r'\b(sorry|admit|axiom|native_decide)\b', fc_definitions):
    raise SystemExit('Unexpected hole or axiom in FC definitions')
for p in proof.rglob('*.lean'):
    if '.lake' in p.parts or p.name == 'Challenge.lean': continue
    # Preserved upstream benchmark reference, documented as uncompiled in its NOTICE.
    if p.relative_to(proof).as_posix().startswith('third_party/OpenAIMath/challenge/'): continue
    if re.search(r'\b(sorry|admit|axiom|native_decide)\b', without_comments(p.read_text())):
        raise SystemExit('Unexpected proof hole, axiom, or native_decide: '+str(p.relative_to(root)))
result = dict(status='PASS', targets=names, reference_imports=imports,
    definition_holes=False, mirror_files=len(common), hashed_files=len(manifest['files_sha256']),
    fc_reference_correspondence='EXACT_CHALLENGE_COPY; SOLUTION_CHECK_SEPARATE', fc_exact_source_copy=True, frozen_fc_sha256=fc_sha256,
    fc_statement_count=len(fc_names), comparator_target_count=len(names))
commit = subprocess.run(['git','rev-parse','HEAD'],cwd=root,text=True,capture_output=True)
result['checkout_base_commit'] = commit.stdout.strip() if commit.returncode == 0 else None
dirty = subprocess.run(['git','status','--porcelain'],cwd=root,text=True,capture_output=True)
result['working_tree_dirty'] = bool(dirty.stdout.strip()) if dirty.returncode == 0 else None
result['working_tree_changes'] = dirty.stdout.splitlines() if dirty.returncode == 0 else None
result['tested_commit'] = result['checkout_base_commit'] if result['working_tree_dirty'] is False else None
result['source_manifest_sha256'] = hashlib.sha256((root/'SOURCE-MANIFEST.json').read_bytes()).hexdigest()
result['pins'] = json.loads((proof/'comparator/pins.json').read_text())
proof_inputs = {name:sha for name,sha in manifest['files_sha256'].items()
    if name.startswith('lean/') and ('/comparator/' not in name) and
       (name.endswith('.lean') or name in {'lean/lakefile.toml','lean/lake-manifest.json','lean/lean-toolchain'})}
result['proof_digest'] = hashlib.sha256(json.dumps(proof_inputs,sort_keys=True).encode()).hexdigest()
if os.environ.get('GITHUB_OUTPUT'):
    with open(os.environ['GITHUB_OUTPUT'],'a') as output:
        output.write('proof_digest='+result['proof_digest']+'\n')
if args.receipt_dir:
    args.receipt_dir.mkdir(parents=True, exist_ok=True)
    (args.receipt_dir/'input-check.json').write_text(json.dumps(result,indent=2)+'\n')
    for name in ['SOURCE-MANIFEST.json','lean/comparator/pins.json','lean/comparator.json',
                 'lean/FCTargetDefinitions.lean','lean/Challenge.lean','lean/FCSolution.lean']:
        shutil.copy2(root/name, args.receipt_dir/Path(name).name)
if os.environ.get('GITHUB_ACTIONS') == 'true' and result['working_tree_dirty']:
    result['status'] = 'FAIL'
    if args.receipt_dir:
        (args.receipt_dir/'input-check.json').write_text(json.dumps(result,indent=2)+'\n')
    print(dirty.stdout, file=sys.stderr, end='')
    raise SystemExit('CI must verify an unmodified checkout')
print(json.dumps(result))
