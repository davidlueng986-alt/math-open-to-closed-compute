#!/usr/bin/env bash
set -euo pipefail

JOB_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
OUT_DIR="${PWD}/out"
mkdir -p "${OUT_DIR}"

# Locate pre-built Mathlib project inside the Lean 4.36.0 container
MATHLIB_DIR=""
for cand in /opt/mathlib /opt/lean-project /opt/project /root/mathlib /workspace/mathlib; do
  if [ -f "${cand}/lakefile.toml" ] || [ -f "${cand}/lakefile.lean" ]; then
    MATHLIB_DIR="${cand}"
    break
  fi
done
if [ -z "${MATHLIB_DIR}" ]; then
  FOUND="$(find /opt /root / -maxdepth 3 \( -name lakefile.toml -o -name lakefile.lean \) 2>/dev/null | head -n 1 || true)"
  if [ -n "${FOUND}" ]; then
    MATHLIB_DIR="$(dirname "${FOUND}")"
  fi
fi
if [ -z "${MATHLIB_DIR}" ]; then
  echo "ERROR: Could not locate prebuilt Mathlib project" >&2
  exit 1
fi

echo "Using MATHLIB_DIR=${MATHLIB_DIR}"
lean --version

cp "${JOB_DIR}/Wave6Agent6DyadicPinch.lean" "${MATHLIB_DIR}/Wave6Agent6DyadicPinch.lean"

(
  cd "${MATHLIB_DIR}"
  lake env lean -DwarningAsError=true Wave6Agent6DyadicPinch.lean
) 2>&1 | tee "${OUT_DIR}/lean_verify.log"

python3 - "${OUT_DIR}/lean_verify.log" "${OUT_DIR}/audit.json" << 'EOF'
import json, re, sys

log_path, out_path = sys.argv[1], sys.argv[2]
text = open(log_path).read()

allowed = {"propext", "Classical.choice", "Quot.sound"}
axioms = {}
# Parse both single-line and multi-line #print axioms output
pattern = re.compile(
    r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",
    re.MULTILINE | re.DOTALL,
)
for m in pattern.finditer(text):
    thm = m.group(1)
    ax_raw = m.group(2)
    if ax_raw is None:
        axs = []
    else:
        axs = [a.strip() for a in ax_raw.replace("\n", " ").split(",") if a.strip()]
    axioms[thm] = sorted(axs)
    bad = [a for a in axs if a not in allowed]
    if bad:
        print(f"FAIL: {thm} uses disallowed axioms: {bad}", file=sys.stderr)
        sys.exit(1)

if len(axioms) < 14:
    print(f"FAIL: expected >= 14 audited theorems, found {len(axioms)}", file=sys.stderr)
    sys.exit(1)

res = {
    "status": "PASS",
    "module": "Wave6Agent6DyadicPinch",
    "audited_theorems": len(axioms),
    "axioms": axioms,
}
open(out_path, "w").write(json.dumps(res, indent=2))
print(json.dumps(res, indent=2))
EOF
