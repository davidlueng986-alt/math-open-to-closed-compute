import json
import re
import sys
from pathlib import Path

root = Path(sys.argv[1])
standard = {'propext', 'Classical.choice', 'Quot.sound'}
expected = {
    'GeneralInvolution': [
        'E64GenInvolution.no_parallel_of_gen_involution',
        'E64GenInvolution.hasPower_of_genInvQuot',
        'E64GenInvolution.genInvQuot_degree_of_nonfixed',
        'E64GenInvolution.no_gen_involution_near_quot',
        'E64GenInvolution.no_single_fixed_involution_zero_inv_edge',
        'E64GenInvolution.no_mirror_involution_ge3_fixed',
    ],
    'ClassHWeapons': [
        'E64ClassH.class_h_no_defect_triangle_adj_high',
        'E64ClassH.class_h_defect_to_high_neighbor_dyadic_path',
        'E64ClassH.class_h_defect_neighbor_high_edge_fermat',
        'E64ClassH.defect_suppression_dyadic_path',
        'E64ClassH.class_h_double_edge_deletion_path',
    ],
    'CutBoundaryWeapons': [
        'E64CutBoundary.wfree_2cut_matching_and_cubic_boundary',
        'E64CutBoundary.wfree_3cut_at_most_one_high_boundary',
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
    'scope': 'Wave 3 Agent 5 unconditional all-order structural theorems for Erdos #64 MinimalBad(G); original conjecture remains open.',
    'mathlib': (root / 'mathlib-commit.txt').read_text().strip(),
    'lean': (root / 'lean-version.txt').read_text().strip(),
    'audits': audits,
}
(root / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
