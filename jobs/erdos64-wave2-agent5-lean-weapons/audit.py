import json
import re
import sys
from pathlib import Path

root = Path(sys.argv[1])
standard = {'propext', 'Classical.choice', 'Quot.sound'}
expected = {
    'IndependentExpansion': [
        'E64Wave2Indep.indep_neighborhood_expansion',
        'E64Wave2Indep.indep_syndrome_no_kernel',
        'E64Wave2Indep.dual_kernel_non_j3_ge_two',
    ],
    'ConnectivityAndCuts': [
        'E64Wave2Conn.minimal_bad_no_cut_vertex',
        'E64Wave2Conn.minimal_bad_two_edge_connected',
    ],
    'IdentificationAndContraction': [
        'E64Wave2Ident.universal_dyadic_path',
        'E64Wave2Ident.cubic_dist2_dyadic_path',
        'E64Wave2Ident.cubic_nonadj_dyadic_path',
        'E64Wave2Ident.edge_contraction_dyadic_plus_one',
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
    'scope': 'Wave 2 Agent 5 unconditional MinimalBad structural, F2-expansion, dual-kernel, connectivity, and identification/contraction theorems; standard axioms only.',
    'mathlib': (root / 'mathlib-commit.txt').read_text().strip(),
    'lean': (root / 'lean-version.txt').read_text().strip(),
    'audits': audits,
}
(root / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
