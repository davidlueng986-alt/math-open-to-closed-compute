import json
import re
import sys
from pathlib import Path

root = Path(sys.argv[1])
standard = {'propext', 'Classical.choice', 'Quot.sound'}
expected = {
    'ClosedBipartiteDefect': ['E64BipartiteDefect.exclude_bipartite_defect',
        'E64BipartiteDefect.exclude_hb', 'E64BipartiteDefect.exclude_sb'],
    'Remaining': ['E64Remaining.exclude_closed', 'E64Remaining.original_of_remaining'],
    'ClosedBipartite': ['E64Closed.exclude_cb', 'E64Closed.exclude_sb'],
    'ClosedTriangle': ['E64Closed.exclude_ct_core', 'E64Closed.exclude_st_core'],
    'ClosedDefectCore': [
        'E64DefectCore.defect_neighbor_cubic',
        'E64DefectCore.adjacent_two_three_cut',
        'E64DefectCore.defect_forces_small_cut',
        'E64DefectCore.exclude_st_core', 'E64DefectCore.exclude_sn_core',
        'E64DefectCore.exclude_hb_core4', 'E64DefectCore.exclude_hb_core5',
        'E64DefectCore.exclude_ht_core4', 'E64DefectCore.exclude_ht_core5',
        'E64DefectCore.exclude_hn_core4', 'E64DefectCore.exclude_hn_core5',
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
    'scope': 'Complete exclusions of specified MinimalBad terminal classes; original conjecture remains open.',
    'mathlib': (root / 'mathlib-commit.txt').read_text().strip(),
    'lean': (root / 'lean-version.txt').read_text().strip(),
    'audits': audits,
}
(root / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
