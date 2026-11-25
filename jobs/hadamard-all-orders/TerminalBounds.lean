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

theorem integral_defect_twelve_599_bound : 8 ^ 8 < 599 ^ 2 * 3 ^ 4 := by
  decide

#print axioms defect_599_bound
#print axioms three_change_bound
#print axioms integral_defect_twelve_599_bound

end HadamardAllOrders
