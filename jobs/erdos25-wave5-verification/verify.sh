#!/usr/bin/env bash
set -euo pipefail
root="$(pwd)"
file="$root/jobs/erdos25-wave5-verification/BlockClosure.lean"
mkdir -p "$root/out"
cd /opt/mathlib4
lake env lean --version
git rev-parse HEAD
sha256sum "$file"
lake env lean "$file" 2>&1 | tee "$root/out/block-closure.log"
python3 - "$root/out/block-closure.log" <<'PY'
import re,sys,pathlib
s=pathlib.Path(sys.argv[1]).read_text()
assert 'sorryAx' not in s
a=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",s,re.S)
assert len(a)==6,a
assert all({x.strip() for x in v.split(',') if x.strip()} <= {'propext','Classical.choice','Quot.sound'} for _,v in a),a
print('PASS six transitive axiom audits; standard axioms only')
PY
