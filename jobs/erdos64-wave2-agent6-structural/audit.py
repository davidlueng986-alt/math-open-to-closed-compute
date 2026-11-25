import json
import re
import sys
from pathlib import Path

root = Path(sys.argv[1])
standard = {'propext', 'Classical.choice', 'Quot.sound'}
expected = {
    'Identification': [
        'E64Identification.dyadic_path_of_identify',
        'E64Identification.dyadic_path_of_dist_ge_three',
        'E64Identification.no_bipartite_minimal_bad',
        'E64Identification.dyadic_path_of_dist_two',
        'E64Identification.cubic_all_nonadj_dyadic_path',
        'E64Identification.fermat_cycle_of_non_triangle_edge',
        'E64Identification.cubic_fermat_cycle_of_edge',
        'E64Identification.no_bridge_minimal_bad',
    ],
    'HighCodeDistance': [
        'E64HighCode.high_independent',
        'E64HighCode.high_neighbor_cubic',
        'E64HighCode.high_code_weight_ge_two_sub_four',
        'E64HighCode.high_code_dist_ge_four',
    ],
    'InvolutionExclusion': [
        'E64Involution.no_parallel_of_involution',
        'E64Involution.hasPower_of_invQuot',
        'E64Involution.no_fpf_involution_le_one_edge',
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
    'scope': 'Wave 2 Agent 6 unconditional structural theorems for Erdős #64 MinimalBad(G); original conjecture remains open.',
    'mathlib': (root / 'mathlib-commit.txt').read_text().strip(),
    'lean': (root / 'lean-version.txt').read_text().strip(),
    'audits': audits,
}
(root / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
