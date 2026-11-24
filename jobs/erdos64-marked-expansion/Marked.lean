import Mathlib

namespace MarkedExpansion

def hits (r t p : ℕ) : Prop := r + t ≤ p ∧ p ≤ r + 2 * t

-- A cycle of r base vertices with t expanded triangles has precisely
-- the lengths r+t+j, 0 ≤ j ≤ t. This file checks the arithmetic interface,
-- not the graph-to-cycle correspondence (proved in the accompanying note).
theorem interval_iff (r t p : ℕ) :
    hits r t p ↔ ∃ j : ℕ, j ≤ t ∧ p = r + t + j := by
  unfold hits
  constructor
  · intro hp
    exact ⟨p - (r + t), by omega, by omega⟩
  · rintro ⟨j, hj, rfl⟩
    omega

theorem triangle_even (t : ℕ) (ht : t ≤ 3)
    (h4 : ¬ hits 3 t 4) (h8 : ¬ hits 3 t 8) :
    t = 0 ∨ t = 2 := by
  unfold hits at h4 h8
  omega

theorem quadrilateral_one (t : ℕ) (ht : t ≤ 4)
    (h4 : ¬ hits 4 t 4) (h8 : ¬ hits 4 t 8) : t = 1 := by
  unfold hits at h4 h8
  omega

theorem dyadic_cycle_sparse (r t : ℕ) (ht : t ≤ r)
    (h0 : ¬ hits r t r) (h1 : ¬ hits r t (2*r)) :
    0 < t ∧ 2*t < r := by
  unfold hits at h0 h1
  omega

-- Two triangles abc, abd sharing ab and the quadrilateral cadb.
-- The marks are 0 or 1. No such base pattern admits a power-free expansion.
theorem diamond_obstruction (a b c d : ℕ)
    (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1) (hd : d ≤ 1)
    (hT1 : a+b+c = 0 ∨ a+b+c = 2)
    (hT2 : a+b+d = 0 ∨ a+b+d = 2)
    (hQ : a+b+c+d = 1) : False := by
  omega

#print axioms interval_iff
#print axioms triangle_even
#print axioms quadrilateral_one
#print axioms dyadic_cycle_sparse
#print axioms diamond_obstruction

end MarkedExpansion
