#!/usr/bin/env python3
"""Refresh the proof-only copy and pin all candidate source inputs before testing."""
from pathlib import Path
import hashlib,json,shutil,re
root=Path(__file__).resolve().parents[2]
canonical=root/'lean'
mirror=root/'leanWithoutComparator'
mirror.mkdir(exist_ok=True)
excluded={'Challenge.lean','FCAudit.lean','comparator.json','README.md'}
common=[]
benchmark=mirror/'third_party/OpenAIMath/challenge'
if benchmark.exists():shutil.rmtree(benchmark)
for p in sorted(canonical.rglob('*')):
    rel=p.relative_to(canonical)
    if any(part in {'.lake','__pycache__','comparator','verification'} for part in rel.parts):continue
    if not p.is_file() or p.name in excluded:continue
    if rel.as_posix().startswith('third_party/OpenAIMath/challenge/'):continue
    dest=mirror/rel;dest.parent.mkdir(parents=True,exist_ok=True)
    if p.name=='lakefile.toml' and len(rel.parts)==1:
        text=p.read_text()
        for name in ['Challenge','FCAudit']:
            text=text.replace('\n[[lean_lib]]\nname = "'+name+'"\n','')
        dest.write_text(text)
    else:
        shutil.copy2(p,dest)
        common.append(str(rel))
(mirror/'README.md').write_text('''# Lean proof without Comparator\n\nThe mathematical sources are byte-identical to `../lean/`.\nThe project Comparator reference, axiom-audit entry point, checker scripts and unused upstream Comparator benchmark are omitted.\nThe retained third-party notices and original hash manifests describe the canonical vendored snapshot.\nThe default target remains the complete `FCSolution` containing the nine solved FClikelean variants.\n\n```sh\nlake exe cache get\nlake build\n```\n\nLean 4.34.1 and the fixed `lake-manifest.json` are required.\n''')
files={}
for base in ['lean','leanWithoutComparator','FClikelean','.github/workflows']:
    for p in sorted((root/base).rglob('*')):
        rel=p.relative_to(root)
        if any(part in {'.lake','__pycache__','verification'} for part in rel.parts):continue
        if p.is_file():files[str(rel)]=hashlib.sha256(p.read_bytes()).hexdigest()
manifest=dict(schema=1,lean_toolchain=(canonical/'lean-toolchain').read_text().strip(),
    mathematical_reference='lean/Challenge.lean',solution='lean/FCSolution.lean',
    mirror_files=common,files_sha256=files)
(root/'SOURCE-MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('Pinned',len(files),'files;',len(common),'byte-identical shared proof files.')
