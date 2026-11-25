import json
import re
import sys
from pathlib import Path

root = Path(sys.argv[1])
standard = {'propext', 'Classical.choice', 'Quot.sound'}
expected = {
    'DyadicPaths': [
        'E64Wave2Structural.minimal_bad_no_c4',
        'E64Wave2Structural.unique_common_neighbor',
        'E64Wave2Structural.minimal_bad_no_high_adj',
        'E64Wave2Structural.universal_dyadic_path',
        'E64Wave2Structural.unified_bipartite_exclusion',
        'E64Wave2Structural.cubic_dist2_dyadic_path',
        'E64Wave2Structural.cubic_all_nonadj_dyadic_path',
        'E64Wave2Structural.cubic_p3_dyadic_plus_two_cycle',
        'E64Wave2Structural.defect_dist2_dyadic_path',
    ],
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
    assert all(name in audits for name in names), (module, names)
for path in (root / 'source').glob('*.lean'):
    source = path.read_text()
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', re.sub(r'/\-.*?\-/', '', source, flags=re.S)), path
result = {
    'status': 'PASS',
    'scope': 'Wave 2 Agent #3 unconditional all-order structural theorems on MinimalBad (Lean 4.36.0, standard axioms only).',
    'mathlib': (root / 'mathlib-commit.txt').read_text().strip(),
    'lean': (root / 'lean-version.txt').read_text().strip(),
    'audits': audits,
}
(root / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
