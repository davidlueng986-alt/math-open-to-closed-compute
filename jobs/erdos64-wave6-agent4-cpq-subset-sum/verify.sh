#!/usr/bin/env bash
set -euo pipefail

mkdir -p out
SRC="jobs/erdos64-wave6-agent4-cpq-subset-sum/Wave6Agent4CycleContraction.lean"

git rev-parse HEAD
lean --version

# Locate prebuilt Mathlib project inside container
MATHLIB_PROJ=""
for cand in /opt/mathlib /opt/lean-project /workspace/mathlib /root/mathlib /opt/mathlib4; do
  if [ -d "$cand" ] && { [ -f "$cand/lakefile.toml" ] || [ -f "$cand/lakefile.lean" ]; }; then
    MATHLIB_PROJ="$cand"
    break
  fi
done
if [ -z "$MATHLIB_PROJ" ]; then
  FOUND=$(find /opt /workspace /root -maxdepth 3 \( -name "lakefile.toml" -o -name "lakefile.lean" \) 2>/dev/null | head -n 1 || true)
  if [ -n "$FOUND" ]; then
    MATHLIB_PROJ="$(dirname "$FOUND")"
  fi
fi

echo "Detected MATHLIB_PROJ=${MATHLIB_PROJ}"
if [ -z "$MATHLIB_PROJ" ]; then
  echo "ERROR: Could not locate prebuilt Mathlib project"
  exit 1
fi

ABS_SRC="$(realpath "$SRC")"
(
  cd "$MATHLIB_PROJ"
  lake env lean -DwarningAsError=true "$ABS_SRC"
) 2>&1 | tee out/lean_audit.log

# Check zero sorryAx / native_decide
if grep -E "sorryAx|Lean\.ofReduceBool|Lean\.trustCompiler" out/lean_audit.log; then
  echo "ERROR: Non-standard axiom detected!"
  exit 1
fi

sha256sum "$SRC" > out/sha256.txt
echo "VERIFICATION_STATUS=PASS" | tee out/status.txt
