#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
JOB_DIR="$ROOT_DIR/jobs/wave8_agent5"
WORK_DIR="$ROOT_DIR/work_lean_wave8_agent5"
OUT_DIR="$ROOT_DIR/out_wave8_agent5"
mkdir -p "$WORK_DIR" "$OUT_DIR"

cp "$JOB_DIR/Wave8Agent5Core.lean" "$WORK_DIR/"
cp "$JOB_DIR/Wave8Agent5Petersen.lean" "$WORK_DIR/"

cat > "$WORK_DIR/Wave8Agent5Audit.lean" << 'EOF'
import Wave8Agent5Core
import Wave8Agent5Petersen

#print axioms E64Wave8Agent5.zero_voltage_cycle_lifts
#print axioms E64Wave8Agent5.abelian_cover_theta_commutator_simple
#print axioms E64Wave8Agent5.abelian_cover_theta_dichotomy
#print axioms E64Wave8Agent5.abelian_cover_theta_pow2_of_girth
#print axioms E64Wave8Agent5.abelian_cover_theta233_girth7_hasPower
#print axioms E64Wave8Agent5.abelian_cover_theta134_girth8_hasPower
#print axioms E64Wave8Agent5.abelian_cover_theta556_girth12_hasPower
#print axioms E64Wave8Agent5.abelian_cover_barbell_commutator_simple
#print axioms E64Wave8Agent5.abelian_cover_barbell_pow2
#print axioms E64Wave8Agent5.c6_no_antipodal_chord_of_no_pow2
#print axioms E64Wave8Agent5.c12_no_odd_chord_of_no_pow2
#print axioms E64Wave8Agent5.crossing_chords_six_cycles
#print axioms E64Wave8Agent5.c10_no_two_antipodal_chords
#print axioms E64Wave8Agent5.two_disjoint_c5_at_most_one_bridge
#print axioms E64Wave8Agent5.two_disjoint_c6_no_equal_dist_bridges
#print axioms E64Wave8Agent5.two_disjoint_c6_bipartite_at_most_two_bridges
#print axioms E64Wave8Agent5.tait_even_c6_ring_dist1_spectrum_hits_pow2
#print axioms E64Wave8Agent5.petersen_all_abelian_covers_hasPower
EOF

cd /opt/mathlib4
echo "Mathlib commit: $(git rev-parse HEAD)" | tee "$OUT_DIR/env.log"
test "$(git rev-parse HEAD)" = fc4f59e577feb1a4956671bc04ac18aaaf8cd842
lake env lean --version | tee -a "$OUT_DIR/env.log"

export LEAN_PATH="$WORK_DIR"
lake env lean --root="$WORK_DIR" -DwarningAsError=true -o "$WORK_DIR/Wave8Agent5Core.olean" "$WORK_DIR/Wave8Agent5Core.lean" 2>&1 | tee "$OUT_DIR/core.log"
lake env lean --root="$WORK_DIR" -DwarningAsError=true -o "$WORK_DIR/Wave8Agent5Petersen.olean" "$WORK_DIR/Wave8Agent5Petersen.lean" 2>&1 | tee "$OUT_DIR/petersen.log"
lake env lean --root="$WORK_DIR" -DwarningAsError=true "$WORK_DIR/Wave8Agent5Audit.lean" 2>&1 | tee "$OUT_DIR/axioms.log"

python3 - "$JOB_DIR/Wave8Agent5Core.lean" "$JOB_DIR/Wave8Agent5Petersen.lean" "$OUT_DIR/axioms.log" "$OUT_DIR/verification.json" << 'PY'
import hashlib, json, re, sys

core_p, pet_p, log_p, out_p = sys.argv[1:5]
hashes = {}
for p in (core_p, pet_p):
    raw = open(p, "rb").read()
    hashes[p.split("/")[-1]] = hashlib.sha256(raw).hexdigest()
    txt = raw.decode("utf-8")
    # Strip block comments /- ... -/ and line comments -- ...
    clean = re.sub(r"/-.*?-/", "", txt, flags=re.S)
    clean = re.sub(r"--.*", "", clean)
    for tok in ("sorry", "admit", "axiom", "native_decide"):
        assert not re.search(r"\b" + tok + r"\b", clean), f"Forbidden token {tok} in {p}"

log_txt = open(log_p, encoding="utf-8").read()
allowed = {"propext", "Classical.choice", "choice", "Quot.sound"}
axioms, disallowed = {}, {}
for m in re.finditer(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log_txt):
    name = m.group(1).strip()
    axs = [a.strip() for a in m.group(2).split(",") if a.strip()]
    axioms[name] = axs
    bad = [a for a in axs if a not in allowed]
    if bad:
        disallowed[name] = bad

ok = (len(axioms) == 18) and (len(disallowed) == 0)
res = {
    "status": "PASS" if ok else "FAIL",
    "audited_count": len(axioms),
    "disallowed_axioms": disallowed,
    "source_sha256": hashes,
    "axioms": axioms,
}
open(out_p, "w", encoding="utf-8").write(json.dumps(res, indent=2) + "\n")
print(json.dumps(res, indent=2))
sys.exit(0 if ok else 1)
PY
