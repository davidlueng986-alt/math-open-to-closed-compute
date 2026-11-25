import json
import re
import sys
from pathlib import Path

root = Path(sys.argv[1])
standard = {'propext', 'Classical.choice', 'Quot.sound'}
expected = [
    'E64Wave2Structural.no_c4_of_minimal_bad',
    'E64Wave2Structural.common_neighbor_unique',
    'E64Wave2Structural.high_degree_independent',
    'E64Wave2Structural.no_defect_triangle_without_2cut',
    'E64Wave2Structural.universal_dyadic_path',
    'E64Wave2Structural.unified_bipartite_exclusion',
    'E64Wave2Structural.cubic_nonadj_dyadic_path',
    'E64Wave2Structural.cubic_two_path_dyadic_plus_two_cycle',
    'E64Wave2Structural.cubic_edge_dyadic_plus_one_cycle',
]
text = (root / 'Wave2Structural.log').read_text()
assert not re.search(r'sorryAx|native_decide|Lean\.ofReduceBool', text)
audits = {}
for name, body in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text):
    axioms = {item.strip() for item in body.split(',') if item.strip()}
    assert axioms <= standard, (name, axioms - standard)
    audits[name] = sorted(axioms)
for name in expected:
    assert name in audits, f"Missing audit for {name}"
for path in (root / 'source').glob('*.lean'):
    source = path.read_text()
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', re.sub(r'/\-.*?\-/', '', source, flags=re.S)), path
result = {
    'status': 'PASS',
    'scope': 'Wave 2 Agent 2 all-order MinimalBad structural theorem suite (standard axioms only).',
    'mathlib': (root / 'mathlib-commit.txt').read_text().strip(),
    'lean': (root / 'lean-version.txt').read_text().strip(),
    'audits': audits,
}
(root / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
