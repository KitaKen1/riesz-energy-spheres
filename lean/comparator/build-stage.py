#!/usr/bin/env python3
"""Validate the complete import graph and emit one dependency-ordered CI batch."""
from pathlib import Path
import argparse, json, re

root = Path(__file__).resolve().parents[1]
plan = json.loads((root/'comparator/build-stages.json').read_text())
bases = [root, root/'prototype', root/'third_party/E8Leech/lean',
         root/'third_party/OpenAIMath/lean']

def source(module):
    for base in bases:
        path = base/(module.replace('.', '/')+'.lean')
        if path.is_file():
            return path

seen = set()
visiting = set()
graph = {}

def visit(module):
    path = source(module)
    if path is None or module in seen:
        return
    if module in visiting:
        raise SystemExit('Import cycle: '+module)
    visiting.add(module)
    imports = re.findall(r'^(?:public )?(?:meta )?import (\S+)', path.read_text(), re.M)
    graph[module] = [name for name in imports if source(name)]
    for name in imports:
        visit(name)
    visiting.remove(module)
    seen.add(module)

for module in plan['roots']:
    visit(module)
if plan['roots'] != ['FCSolution', 'FCAudit'] or plan['stage_count'] != 6:
    raise SystemExit('Expected six batches covering FCSolution and FCAudit')
positions = {}
for index, stage in enumerate(plan['stages'], 1):
    if stage['stage'] != index or not stage['modules']:
        raise SystemExit('Invalid stage number or empty batch')
    for module in stage['modules']:
        if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*', module) or module in positions:
            raise SystemExit('Invalid or duplicate module: '+module)
        positions[module] = index
if set(positions) != seen:
    raise SystemExit('Batch plan does not match the full proof import closure')
for module, imports in graph.items():
    for dependency in imports:
        if positions[dependency] > positions[module]:
            raise SystemExit('Dependency assigned to a later stage: '+module+' -> '+dependency)
if any(positions[module] != 6 for module in plan['roots']):
    raise SystemExit('Final targets must belong to the final stage')
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--stage', type=int, choices=range(1, 7))
parser.add_argument('--targets', type=Path)
args = parser.parse_args()
if args.stage:
    stage = plan['stages'][args.stage-1]
    if args.targets:
        args.targets.write_text('\n'.join(stage['modules'])+'\n')
    print(json.dumps({'status': 'PASS', 'stage': args.stage,
        'stage_count': 6, 'module_count': len(stage['modules']),
        'complete_import_closure_modules': len(seen),
        'estimated_serial_seconds': stage['estimated_serial_seconds']}))
else:
    print('PASS:', len(seen), 'modules covered exactly once by six dependency-ordered batches.')
