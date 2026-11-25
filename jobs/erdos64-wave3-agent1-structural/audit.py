import json
import re
import sys
from pathlib import Path

root = Path(sys.argv[1])
standard = {'propext', 'Classical.choice', 'Quot.sound'}
expected = {
    'ClassHSharpCode': [
        'E64Wave3HighCode.two_deg_sum_deg_le',
        'E64Wave3HighCode.c4_free_two_deg_sum_deg_le_eight',
        'E64Wave3HighCode.c4_free_five_common_neighbor',
        'E64Wave3HighCode.c4_free_two_deg_sum_deg_le_ten',
        'E64Wave3HighCode.minimal_bad_proper_sum_deg_le',
        'E64Wave3HighCode.high_code_weight_ge_six',
        'E64Wave3HighCode.high_code_weight_ge_eight',
        'E64Wave3HighCode.high_code_weight_ge_ten',
    ],
    'GeneralInvolution': [
        'E64Wave3Involution.hasPower_of_general_invQuot',
        'E64Wave3Involution.no_involution_le_one_quot_defect',
        'E64Wave3Involution.no_fpf_involution_le_three_edges',
        'E64Wave3Involution.cayley_no_disjoint_involution_class',
    ],
    'PathCycleForcing': [
        'E64Wave3PathCycle.cubic_p3_fermat_cycle',
        'E64Wave3PathCycle.defect_p3_fermat_cycle',
        'E64Wave3PathCycle.defect_neighbor_p3_fermat_cycle',
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
    assert all(name in audits for name in names), (module, [n for n in names if n not in audits])
for path in (root / 'source').glob('*.lean'):
    source = path.read_text()
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', re.sub(r'/\-.*?\-/', '', source, flags=re.S)), path
result = {
    'status': 'PASS',
    'scope': 'Wave 3 Agent 1 unconditional all-order structural theorems for Erdős #64 MinimalBad(G); original conjecture remains open.',
    'mathlib': (root / 'mathlib-commit.txt').read_text().strip(),
    'lean': (root / 'lean-version.txt').read_text().strip(),
    'audits': audits,
}
(root / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
