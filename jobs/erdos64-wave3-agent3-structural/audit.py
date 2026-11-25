import json
import re
import sys
from pathlib import Path

root = Path(sys.argv[1])
standard = {'propext', 'Classical.choice', 'Quot.sound'}
expected = {
    'GeneralInvolution': [
        'E64Wave3Involution.no_parallel_of_nonfixed_involution',
        'E64Wave3Involution.hasPower_of_invQuot_general',
        'E64Wave3Involution.invQuot_degree_nonfixed',
        'E64Wave3Involution.invQuot_degree_fixed_double_ge',
        'E64Wave3Involution.invQuot_degree_fixed_all_fixed',
        'E64Wave3Involution.general_involution_two_low_orbits',
        'E64Wave3Involution.no_defect_fixing_involution_no_other_low',
        'E64Wave3Involution.cubic_involution_two_seam_orbits',
    ],
    'ClassHAuxiliary': [
        'E64Wave3ClassH.exists_deg_le_two_of_no_near',
        'E64Wave3ClassH.card_edgeFinset_induce_erase',
        'E64Wave3ClassH.no_near_two_degenerate_edges_induce',
        'E64Wave3ClassH.no_near_c4free_edges_induce',
        'E64Wave3ClassH.class_h_n2_n3_le_two_sub_three',
        'E64Wave3ClassH.class_h_n2_n3_le_two_sub_four',
    ],
    'ForcedCyclesAndPaths': [
        'E64Wave3Forced.dyadic_path_of_identify_erase',
        'E64Wave3Forced.cubic_forbidden_edge_dyadic_path',
        'E64Wave3Forced.cubic_two_distinct_exit_dyadic_paths',
        'E64Wave3Forced.cubic_non_triangle_two_path_fermat_cycle',
        'E64Wave3Forced.defect_three_path_dyadic_plus_two_cycle',
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
    'scope': 'Wave 3 Agent 3 unconditional all-order structural theorems for Erdős #64 MinimalBad(G); original conjecture remains open.',
    'mathlib': (root / 'mathlib-commit.txt').read_text().strip(),
    'lean': (root / 'lean-version.txt').read_text().strip(),
    'audits': audits,
}
(root / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
