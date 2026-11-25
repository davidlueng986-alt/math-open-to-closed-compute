import json
import re
import sys
from pathlib import Path

root = Path(sys.argv[1])
standard = {'propext', 'Classical.choice', 'Quot.sound'}
expected = {
    'Wave2Agent1': [
        'E64Wave2Agent1.high_degree_independent',
        'E64Wave2Agent1.no_all_high_neighbors',
        'E64Wave2Agent1.defect_neighbor_at_most_one_high_neighbor',
        'E64Wave2Agent1.no_c4_of_power_free',
        'E64Wave2Agent1.identify_pair_dyadic_path',
        'E64Wave2Agent1.dist_ge3_dyadic_path',
        'E64Wave2Agent1.cubic_all_pairs_dyadic_path',
        'E64Wave2Agent1.cubic_every_edge_on_dyadic_plus_one_cycle',
        'E64Wave2Agent1.tri_free_edge_on_dyadic_plus_one_cycle',
    ]
}
audits = {}
for path in sorted(root.glob('*.log')):
    text = path.read_text()
    assert not re.search(r'sorryAx|native_decide|Lean\.ofReduceBool', text), path
    for name, body in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text):
        axioms = {item.strip() for item in body.split(',') if item.strip()}
        assert axioms <= standard, (name, axioms - standard)
        audits[name] = sorted(axioms)
for module, names in expected.items():
    assert (root / f'{module}.log').is_file(), module
    assert all(name in audits for name in names), (module, names, sorted(audits.keys()))
for path in (root / 'source').glob('*.lean'):
    source = path.read_text()
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', re.sub(r'/\-.*?\-/', '', source, flags=re.S)), path
result = {
    'status': 'PASS',
    'scope': 'Wave 2 Agent 1 MinimalBad structural & all-pairs dyadic path theorems (standard axioms only).',
    'mathlib': (root / 'mathlib-commit.txt').read_text().strip(),
    'lean': (root / 'lean-version.txt').read_text().strip(),
    'audits': audits,
}
(root / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
