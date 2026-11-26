namespace HadamardAllOrders

/-- The small-lattice determinant bound covers all four near-completion defects at p=599. -/
theorem defect_599_bound (s : Nat) (lo : 8 ≤ s) (hi : s ≤ 11) :
    4 * s ^ s < 599 ^ 2 * 4 ^ s := by
  have casesS : s = 8 ∨ s = 9 ∨ s = 10 ∨ s = 11 := by omega
  rcases casesS with rfl | rfl | rfl | rfl <;> decide

/-- The squared upper and lower determinant bounds for a three-column change conflict. -/
theorem three_change_bound (p : Nat) (hp : 599 ≤ p) :
    11 ^ 11 < (p * 2 ^ 10) ^ 2 := by
  have lower : 599 * 2 ^ 10 ≤ p * 2 ^ 10 := Nat.mul_le_mul_right _ hp
  exact Nat.lt_of_lt_of_le (by decide : 11 ^ 11 < (599 * 2 ^ 10) ^ 2)
    (Nat.pow_le_pow_left lower 2)

/-- The determinant is a square p-power, so only 1 and p² are below this bound. -/
theorem two_overlattices_bound (s : Nat) (lo : 1 ≤ s) (hi : s ≤ 16) :
    4 * s ^ s < 599 ^ 4 * 4 ^ s := by
  have values : s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 ∨
    s = 9 ∨ s = 10 ∨ s = 11 ∨ s = 12 ∨ s = 13 ∨ s = 14 ∨ s = 15 ∨ s = 16 := by omega
  rcases values with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

#print axioms defect_599_bound
#print axioms three_change_bound
#print axioms two_overlattices_bound

end HadamardAllOrders
