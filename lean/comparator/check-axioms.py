#!/usr/bin/env python3
from pathlib import Path
import json,re,sys
root=Path(__file__).resolve().parents[2]
names=json.loads((root/'lean/comparator.json').read_text())['theorem_names']
text=Path(sys.argv[1]).read_text()
records={}
for name in names:
    matches=re.findall("'"+re.escape(name)+r"' depends on axioms: \[(.*?)\]",text,re.S)
    if len(matches)!=1: raise SystemExit('Missing or duplicate axiom report: '+name)
    axioms=[x.strip() for x in matches[0].split(',') if x.strip()]
    if set(axioms)-{'propext','Classical.choice','Quot.sound'}:
        raise SystemExit('Unexpected axiom: '+name)
    records[name]=axioms
if 'sorryAx' in text or 'error:' in text: raise SystemExit('Axiom audit failed')
Path(sys.argv[2]).write_text(json.dumps(dict(status='PASS',targets=records),indent=2)+'\n')
print('PASS:',len(records),'targets use only the three permitted axioms.')
