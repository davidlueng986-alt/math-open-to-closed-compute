#!/usr/bin/env python3
"""Accept only a successful kernel artifact and the complete standard-axiom log."""
import hashlib
import json
import os
import re
import sys
from pathlib import Path

source = Path(sys.argv[1])
out = Path(sys.argv[2])
text = source.read_text()
log = (out / 'kernel.log').read_text()
assert not re.search(r'\b(sorry|admit|native_decide)\b', text)
assert not re.search(r'^\s*(axiom|unsafe)\b', text, re.M)
assert 'sorryAx' not in log
assert 'error:' not in log
expected = re.findall(r'^#print axioms (\w+)', text, re.M)
expected = ['ABCWave3Fermat.' + name for name in expected]
assert len(expected) == 4 and len(set(expected)) == 4
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
found = {}
for name, body in re.findall(r"'?(ABCWave3Fermat\.\w+)'? depends on axioms:\s*\[([^\]]*)\]", log, re.S):
    axioms = [s.strip() for s in body.split(',') if s.strip()]
    assert set(axioms) <= allowed, (name, axioms)
    found[name] = axioms
for name in re.findall(r"'?(ABCWave3Fermat\.\w+)'? does not depend on any axioms", log):
    found[name] = []
assert set(found) == set(expected), {'missing': sorted(set(expected)-set(found)), 'extra': sorted(set(found)-set(expected))}
assert (out / 'FermatSquareArea.olean').is_file()
result = {
    'agent': 4, 'wave': 3, 'status': 'LEAN_VERIFIED', 'problem_resolution': 'unknown',
    'lean_version': (out / 'lean-version.txt').read_text().strip(),
    'mathlib_commit': (out / 'mathlib-commit.txt').read_text().strip(),
    'pinned_mathlib_verified': (out / 'mathlib-commit.txt').read_text().strip() == 'fc4f59e577feb1a4956671bc04ac18aaaf8cd842',
    'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
    'kernel_log_sha256': hashlib.sha256((out / 'kernel.log').read_bytes()).hexdigest(),
    'theorem_count': len(found), 'axioms': found,
    'github_run_id': os.getenv('GITHUB_RUN_ID'), 'github_sha': os.getenv('GITHUB_SHA'),
    'scope': 'Primitive positive integer square-area triangles cannot exist, proved by complete descending construction and strong induction. The quartic consequence c^4-b^4 != w^2 is proved for 0<b<c, gcd(c,b)=1, odd c and even b. These statements suffice for the quartic ROOT escape, but the uniform ROOT bound and full abc are not proved.',
    'original_abc_closed': False,
}
(out / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
