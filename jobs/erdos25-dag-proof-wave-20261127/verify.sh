#!/usr/bin/env bash
set -euo pipefail
module="${1:?module name required}"
case "$module" in BoundedGcdSignature|BoundedQuotient|AffineResidues) ;; *) exit 2 ;; esac
task_root="$(pwd)"
source_file="$task_root/jobs/erdos25-dag-proof-wave-20261127/$module.lean"
mkdir -p "$task_root/out"
sha256sum "$source_file" > "$task_root/out/$module.sha256"
cd /opt/mathlib4
lake env lean --version | tee "$task_root/out/lean-version.txt"
git rev-parse HEAD > "$task_root/out/mathlib-commit.txt"
lake env lean "$source_file" 2>&1 | tee "$task_root/out/$module.log"
python3 - "$task_root/out/$module.log" <<'PY'
import json, pathlib, re, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
if 'sorryAx' in text:
    raise SystemExit('Unproved sorryAx detected')
closures = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", text, re.S)
if not closures:
    raise SystemExit('No transitive axiom output found')
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
checked = []
for theorem, names in closures:
    axioms = {name.strip() for name in names.split(',') if name.strip()}
    if not axioms <= allowed:
        raise SystemExit(f'Unexpected axioms for {theorem}: {axioms-allowed}')
    checked.append({'theorem': theorem, 'axioms': sorted(axioms)})
path.with_suffix('.axioms.json').write_text(json.dumps(checked, indent=2)+'\n')
print(json.dumps({'compiled': True, 'axiom_closures': len(checked), 'standard_axioms_only': True}))
PY
