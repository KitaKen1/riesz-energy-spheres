#!/usr/bin/env python3
"""Apply a pinned import-only FC utility adapter for the proof project's Mathlib."""
from pathlib import Path
import argparse, difflib, hashlib, json
p=argparse.ArgumentParser(); p.add_argument('--receipt-dir',required=True,type=Path); a=p.parse_args()
root=Path(__file__).resolve().parents[2]
source=root/'lean/.lake/packages/formal_conjectures/FormalConjecturesUtil.lean'
original_hash='3a73749a2b247a1ad08820de102f0d32353bf6e519eb954de53e08553cdbc663'
removed=[
 'public import FormalConjecturesForMathlib',
 'public meta import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Eccentricity',
 'public meta import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.VertexDistance']
original=source.read_text()
if hashlib.sha256(source.read_bytes()).hexdigest()!=original_hash:
    raise SystemExit('FC utility entry point differs from the pinned upstream source')
for line in removed:
    if original.count(line+'\n')!=1: raise SystemExit('Unexpected upstream import inventory')
adapted=original
for line in removed: adapted=adapted.replace(line+'\n','')
source.write_text(adapted)
a.receipt_dir.mkdir(parents=True,exist_ok=True)
(a.receipt_dir/'fc-utils-compat.patch').write_text(''.join(difflib.unified_diff(
    original.splitlines(True),adapted.splitlines(True),
    fromfile='upstream/FormalConjecturesUtil.lean',tofile='adapted/FormalConjecturesUtil.lean')))
r={'status':'APPLIED','upstream_commit':'c77fdd446d23539302aa73bcfae4a9fa962b8382',
   'upstream_sha256':original_hash,'adapted_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
   'removed_imports':removed,'retained':'Mathlib and all FC attribute and linter implementations',
   'scope':'Import-only adapter; Challenge and FC mathematical definitions are unmodified.',
   'reason':'The upstream FC extension aggregate targets an older Mathlib. The Challenge uses none of its extensions.'}
(a.receipt_dir/'fc-utils-compat.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r))
