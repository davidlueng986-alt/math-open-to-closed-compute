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
expected = ['ABCWave3Orbit.' + n for n in re.findall(r'^#print axioms (\w+)', text, re.M)]
assert len(expected) == 5 and len(set(expected)) == 5
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
found = {}
for name, body in re.findall(r"'?(ABCWave3Orbit\.\w+)'? depends on axioms:\s*\[([^\]]*)\]", log, re.S):
    axioms = [s.strip() for s in body.split(',') if s.strip()]
    assert set(axioms) <= allowed, (name, axioms)
    found[name] = axioms
for name in re.findall(r"'?(ABCWave3Orbit\.\w+)'? does not depend on any axioms", log):
    found[name] = []
assert set(found) == set(expected), {'missing': sorted(set(expected)-set(found)), 'extra': sorted(set(found)-set(expected))}
assert (out / 'Structural.olean').is_file()
assert (out / 'mathlib-commit.txt').read_text().strip() == 'fc4f59e577feb1a4956671bc04ac18aaaf8cd842'
result = {
    'agent': 2, 'wave': 3, 'status': 'LEAN_VERIFIED', 'problem_resolution': 'unknown',
    'lean_version': (out / 'lean-version.txt').read_text().strip(),
    'mathlib_commit': (out / 'mathlib-commit.txt').read_text().strip(),
    'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
    'kernel_log_sha256': hashlib.sha256((out / 'kernel.log').read_bytes()).hexdigest(),
    'theorem_count': len(found), 'axioms': found,
    'github_run_id': os.getenv('GITHUB_RUN_ID'), 'github_sha': os.getenv('GITHUB_SHA'),
    'scope': 'Five exact complex-polynomial, integer-polynomial and valuation-exponent declarations. No kernel proof of Darmon-Granville, rational-point finiteness, all orbit identities, the global ROOT estimate, or abc is claimed. The separate finite Python checks are CHECKED only.',
    'finite_checks': json.loads((out / 'finite/result.json').read_text()),
    'original_abc_closed': False,
}
(out / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
