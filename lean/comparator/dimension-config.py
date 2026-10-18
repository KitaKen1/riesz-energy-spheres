#!/usr/bin/env python3
"""Partition all nine fixed Comparator targets into three complete dimension groups."""
from pathlib import Path
import argparse, hashlib, json

root = Path(__file__).resolve().parents[2]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--dimension', required=True, type=int, choices=[2, 8, 24])
parser.add_argument('--output', required=True, type=Path)
args = parser.parse_args()
source = root/'lean/comparator.json'
config = json.loads(source.read_text())
pins = json.loads((root/'lean/comparator/pins.json').read_text())
suffixes = {2: 'dimension_two', 8: 'dimension_eight', 24: 'dimension_twenty_four'}
families = ['riesz_energy_lattice', 'log_energy_lattice', 'cap_discrepancy_lattice']
expected = {f'RieszSphereFC.{family}.variants.{suffix}'
            for family in families for suffix in suffixes.values()}
names = config['theorem_names']
if len(names) != 9 or set(names) != expected or set(pins['targets']) != expected:
    raise SystemExit('Dimension groups must cover exactly the nine fixed FC targets')
if config['challenge_module'] != 'Challenge' or config['solution_module'] != 'FCSolution':
    raise SystemExit('Unexpected Challenge or solution module')
if set(config['permitted_axioms']) != {'propext', 'Classical.choice', 'Quot.sound'}:
    raise SystemExit('Unexpected permitted axioms')
selected = [name for name in names if name.endswith('.'+suffixes[args.dimension])]
if len(selected) != 3:
    raise SystemExit('Each dimension must contain the Riesz, logarithmic and cap targets')
config['theorem_names'] = selected
args.output.parent.mkdir(parents=True, exist_ok=True)
args.output.write_text(json.dumps(config, indent=2)+'\n')
scope = {'dimension': args.dimension, 'selected_targets': selected,
         'all_targets': names, 'complete_config_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
         'target_sha256': hashlib.sha256((root/'lean/Challenge.lean').read_bytes()).hexdigest(),
         'verification': 'Unmodified pinned Comparator, including its builtin kernel replay'}
args.output.with_name('scope.json').write_text(json.dumps(scope, indent=2)+'\n')
print(json.dumps(scope))
