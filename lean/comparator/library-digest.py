#!/usr/bin/env python3
"""Identify the unchanged mathematical library independently of the FC bridge files."""
from pathlib import Path
import hashlib,json,os
root=Path(__file__).resolve().parents[2]
manifest=json.loads((root/'SOURCE-MANIFEST.json').read_text())
inputs={n:h for n,h in manifest['files_sha256'].items() if
    (n.startswith(('lean/Riesz/','lean/prototype/','lean/third_party/')) and n.endswith('.lean')
     and not n.startswith('lean/Riesz/FC')) or n in {'lean/lean-toolchain','lean/lake-manifest.json'}}
digest=hashlib.sha256(json.dumps(inputs,sort_keys=True).encode()).hexdigest()
print(digest)
if os.environ.get('GITHUB_OUTPUT'):
 with open(os.environ['GITHUB_OUTPUT'],'a') as f:f.write('library_digest='+digest+'\n')
