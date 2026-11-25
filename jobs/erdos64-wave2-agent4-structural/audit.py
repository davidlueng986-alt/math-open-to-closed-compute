import json
import re
import sys
from pathlib import Path

root = Path(sys.argv[1])
standard = {'propext', 'Classical.choice', 'Quot.sound'}
expected = [
    'E64Wave2Agent4.high_degree_independent',
    'E64Wave2Agent4.exists_low_degree_neighbor',
    'E64Wave2Agent4.class_h_v3_ge_two_v4',
    'E64Wave2Agent4.class_h_v3_two_thirds',
    'E64Wave2Agent4.dyadic_path_of_identify_power',
    'E64Wave2Agent4.dyadic_path_of_no_common_neighbor',
    'E64Wave2Agent4.non_triangle_edge_odd_power_cycle',
    'E64Wave2Agent4.unified_bipartite_exclusion',
    'E64Wave2Agent4.class_h_common_neighbor_dyadic_path',
    'E64Wave2Agent4.cubic_triangle_free_two_path_mersenne',
    'E64Wave2Agent4.cubic_triangle_free_two_path_dyadic',
    'E64Wave2Agent4.all_pairs_dyadic_path_cubic_triangle_free',
]
audits = {}
for path in sorted(root.glob('*.log')):
    text = path.read_text()
    assert not re.search(r'sorryAx|native_decide|Lean\.ofReduceBool', text), path
    for name, body in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text):
        axioms = {item.strip() for item in body.split(',') if item.strip()}
        assert axioms <= standard, (name, axioms - standard)
        audits[name] = sorted(axioms)
for name in expected:
    assert name in audits, f"Missing expected theorem audit: {name}"
for path in (root / 'source').glob('*.lean'):
    source = path.read_text()
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', re.sub(r'/\-.*?\-/', '', source, flags=re.S)), path
result = {
    'status': 'PASS',
    'scope': 'Wave 2 Agent #4 unconditional all-order MinimalBad structural theorems (12 kernel-checked theorems, standard axioms only).',
    'mathlib': (root / 'mathlib-commit.txt').read_text().strip(),
    'lean': (root / 'lean-version.txt').read_text().strip(),
    'audits': {k: audits[k] for k in expected},
}
(root / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
