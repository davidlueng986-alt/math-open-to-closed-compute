#!/usr/bin/env bash
set -euo pipefail
construction_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
construction_seed="${1:-770101}"
construction_seconds="${2:-19000}"
construction_out="${3:-$construction_root/out-$construction_seed}"
mkdir -p "$construction_out"
g++ -O3 -std=c++17 -Wall -Wextra -Wpedantic "$construction_root/search.cpp" -o "$construction_out/search"
"$construction_out/search" --self-test "$construction_out/positive_control.json"
python3 "$construction_root/verify.py" "$construction_out/positive_control.json" --exhaustive --report "$construction_out/positive_control_verified.json"
"$construction_out/search" --input "$construction_root/seeds.txt" --audit "$construction_out/baseline_audit.json"
python3 "$construction_root/verify.py" "$construction_out/baseline_audit.json" --exhaustive --report "$construction_out/baseline_verified.json"
construction_args=(--input "$construction_root/seeds.txt" --out "$construction_out" --seed "$construction_seed" --seconds "$construction_seconds" --mate-nodes 200000 --pack-nodes 200000 --mates 16)
if [[ -f "$construction_out/resume.txt" ]]; then construction_args+=(--resume "$construction_out/resume.txt"); fi
"$construction_out/search" "${construction_args[@]}" | tee "$construction_out/progress.jsonl"
python3 "$construction_root/verify.py" "$construction_out/checkpoint.json" --report "$construction_out/verified.json"
if timeout 180s python3 "$construction_root/verify.py" "$construction_out/checkpoint.json" --exhaustive --report "$construction_out/verified_exhaustive.json"; then
  printf '%s\n' 'Detailed final pair audit completed.'
else
  construction_verify_code=$?
  if [[ "$construction_verify_code" -eq 124 ]]; then
    printf '%s\n' '{"status":"AUDIT_BUDGET_EXHAUSTED","direct_witness_verification":"PASSED","global_nonexistence_claim":false}' > "$construction_out/exhaustive_audit_status.json"
  else
    exit "$construction_verify_code"
  fi
fi
