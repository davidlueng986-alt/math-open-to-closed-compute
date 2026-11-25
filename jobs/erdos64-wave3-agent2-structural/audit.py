import json
import re
import sys
from pathlib import Path

root = Path(sys.argv[1])
standard = {'propext', 'Classical.choice', 'Quot.sound'}
expected = {
    'ClassHSharpCode': [
        'E64Wave3ClassH.c4_free_sum_choose_two_le',
        'E64Wave3ClassH.c4_free_four_edges_le_four',
        'E64Wave3ClassH.c4_free_five_edges_le_six',
        'E64Wave3ClassH.c4_free_six_edges_le_seven',
        'E64Wave3ClassH.c4_near_free_edges_le_four',
        'E64Wave3ClassH.c4_near_free_edges_le_five',
        'E64Wave3ClassH.class_h_no_all_high_cubic',
        'E64Wave3ClassH.high_code_weight_sharp_ge_six',
        'E64Wave3ClassH.high_code_weight_sharp_ge_eight',
        'E64Wave3ClassH.high_code_weight_sharp_ge_ten',
        'E64Wave3ClassH.class_h_v3_sharp_bound',
        'E64Wave3ClassH.class_h_trifree_density_8_11',
    ],
    'GeneralInvolution': [
        'E64Wave3Involution.hasPower_of_general_invQuot',
        'E64Wave3Involution.cubic_involution_defect_ge_two',
        'E64Wave3Involution.one_defect_no_symmetric_involution',
    ],
    'LocalReductions': [
        'E64Wave3Local.trifree_two_edge_y_reduction',
        'E64Wave3Local.class_h_high_neighbor_suppression',
        'E64Wave3Local.class_h_high_triangle_contraction',
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
    for name in names:
        assert name in audits, (module, name)
for path in (root / 'source').glob('*.lean'):
    source = path.read_text()
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', re.sub(r'/\-.*?\-/', '', source, flags=re.S)), path
result = {
    'status': 'PASS',
    'scope': 'Wave 3 Agent 2 unconditional all-order structural theorems for Erdős #64 MinimalBad(G); original conjecture remains open.',
    'mathlib': (root / 'mathlib-commit.txt').read_text().strip(),
    'lean': (root / 'lean-version.txt').read_text().strip(),
    'audits': audits,
}
(root / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
