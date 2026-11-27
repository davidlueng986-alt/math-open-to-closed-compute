import Mathlib

namespace ABCWave3Orbit

def P (x : ℂ) : ℂ :=
  128*x^8 - 256*x^6 + 160*x^4 - 32*x^2 + 1

def Q (x : ℂ) : ℂ :=
  128*x^7 - 192*x^5 + 80*x^3 - 8*x

theorem triple_composition (x : ℂ) :
    2 * (2 * (2*x^2 - 1)^2 - 1)^2 - 1 = P x := by
  unfold P
  ring

theorem squarefree_certificate (x : ℂ) :
    P x ^ 2 + (1-x^2) * Q x ^ 2 = 1 := by
  unfold P Q
  ring

theorem no_common_zero (x : ℂ) (hp : P x = 0) (hq : Q x = 0) : False := by
  have h := squarefree_certificate x
  rw [hp, hq] at h
  norm_num at h

theorem homogeneous_triple (d c : ℤ) :
    2*(2*(2*d^2-c^2)^2-c^4)^2-c^8 =
      128*d^8-256*d^6*c^2+160*d^4*c^4-32*d^2*c^6+c^8 := by
  ring

theorem square_part_exponent_budget (v : ℕ) (hv : 0 < v) :
    v/2 ≤ v-1 ∧ v-1 ≤ 2*(v/2) := by
  omega

#print axioms triple_composition
#print axioms squarefree_certificate
#print axioms no_common_zero
#print axioms homogeneous_triple
#print axioms square_part_exponent_budget

end ABCWave3Orbit
