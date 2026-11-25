import json
import re
import sys
from pathlib import Path

root = Path(sys.argv[1])
standard = {'propext', 'Classical.choice', 'Quot.sound'}
expected = {
    'GeneralInvolution': [
        'E64GenInvolution.hasPower_of_any_invQuot',
        'E64GenInvolution.no_nontrivial_involution_near_quot',
        'E64GenInvolution.invQuot_degree_nonfixed',
        'E64GenInvolution.invQuot_degree_fixed_interior',
        'E64GenInvolution.no_involution_le_one_boundary',
    ],
    'P3AndDefectForcing': [
        'E64P3Defect.mersenne_path_of_add_edge',
        'E64P3Defect.fermat_cycle_of_p3_and_mersenne',
        'E64P3Defect.cubic_p3_fermat_cycle',
        'E64P3Defect.defect_edge_del_mersenne_path',
    ],
    'CutObstructions': [
        'E64CutObstructions.cutCount_erase',
        'E64CutObstructions.no_bipartite_small_cut_side',
        'E64CutObstructions.cubic_odd_cycle_transversal_ge_two',
    ],
    'TriangleCoverContraction': [
        'E64TriangleCover.TriangleFamily.no_parallel_from_tri',
        'E64TriangleCover.TriangleFamily.contr_degree_tri',
        'E64TriangleCover.TriangleFamily.contr_degree_res',
        'E64TriangleCover.TriangleFamily.lift_cycle_double',
        'E64TriangleCover.no_triangle_cover_le_one_edge',
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
    assert all(name in audits for name in names), (module, names, sorted(audits.keys()))
for path in (root / 'source').glob('*.lean'):
    source = path.read_text()
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', re.sub(r'/\-.*?\-/', '', source, flags=re.S)), path
result = {
    'status': 'PASS',
    'scope': 'Wave 3 Agent 6 unconditional all-order structural theorems for Erdős #64 MinimalBad(G); original conjecture remains open.',
    'mathlib': (root / 'mathlib-commit.txt').read_text().strip(),
    'lean': (root / 'lean-version.txt').read_text().strip(),
    'audits': audits,
}
(root / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
