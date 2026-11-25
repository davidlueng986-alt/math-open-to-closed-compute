import json
import re
import sys
from pathlib import Path

root = Path(sys.argv[1])
standard = {'propext', 'Classical.choice', 'Quot.sound'}
expected = {
    'AuxPairGraph': [
        'E64AuxPair.near_free_deg_sum_le',
        'E64AuxPair.c4_near_free_deg_sum_le_four',
        'E64AuxPair.c4_near_free_deg_sum_le_six',
        'E64AuxPair.aux_pair_graph_power_free',
        'E64AuxPair.class_h_code_weight_ge_six',
        'E64AuxPair.class_h_code_weight_ge_eight',
        'E64AuxPair.class_h_code_weight_ge_ten',
        'E64AuxPair.class_h_v3_density_sharp',
        'E64AuxPair.cubic_indep_j2_j3_bound',
    ],
    'InvolutionThreeEdges': [
        'E64Involution3.inv_edges_independent_in_quot',
        'E64Involution3.hasPower_of_invQuot_add_edge',
        'E64Involution3.no_fpf_involution_le_three_edges',
        'E64Involution3.no_defect_fixed_involution_zero_edges',
    ],
    'TwoCutCouplingAndC5': [
        'E64TwoCutC5.two_cut_cross_side_dyadic_coupling',
        'E64TwoCutC5.no_two_c5_share_single_edge',
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
    missing = [n for n in names if n not in audits]
    assert not missing, (module, missing)
for path in (root / 'source').glob('*.lean'):
    source = path.read_text()
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', re.sub(r'/\-.*?\-/', '', source, flags=re.S)), path
result = {
    'status': 'PASS',
    'scope': 'Wave 3 Agent 4 unconditional all-order structural theorems for Erdős #64 MinimalBad(G); original conjecture remains open.',
    'mathlib': (root / 'mathlib-commit.txt').read_text().strip(),
    'lean': (root / 'lean-version.txt').read_text().strip(),
    'audits': audits,
}
(root / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
