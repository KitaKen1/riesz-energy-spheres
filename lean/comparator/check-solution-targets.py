#!/usr/bin/env python3
"""Reject absent or textually different FC theorem signatures before a costly proof build."""
from pathlib import Path
import argparse,json,re,sys
root=Path(__file__).resolve().parents[2]
p=argparse.ArgumentParser();p.add_argument('--receipt-dir',type=Path);args=p.parse_args()
cfg=json.loads((root/'lean/comparator.json').read_text())
def declarations(path):
    text=path.read_text()
    return {name:re.sub(r'\s+',' ',sig).strip() for name,sig in re.findall(
        r'^theorem\s+([^\s:{]+)([\s\S]*?) := by\n',text,re.M)}
challenge=declarations(root/'lean/Challenge.lean')
solution=declarations(root/'lean/FCSolution.lean')
missing=[];different=[]
for full in cfg['theorem_names']:
    name=full.removeprefix('RieszSphereFC.')
    if name not in solution:missing.append(full)
    elif challenge[name]!=solution[name]:different.append(full)
result={'status':'FAIL' if missing or different else 'PASS','selected_targets':cfg['theorem_names'],
    'missing_solution_targets':missing,'different_source_signatures':different,
    'available_solution_targets':['RieszSphereFC.'+name for name in solution],
    'formal_type_comparison':'NOT_RUN: performed by Comparator only after proof build'}
if args.receipt_dir:
    args.receipt_dir.mkdir(parents=True,exist_ok=True)
    (args.receipt_dir/'fc-solution-targets.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
if result['status']!='PASS':
    print('The solution does not yet supply the exact FClikelean solved targets.',file=sys.stderr)
    sys.exit(1)
