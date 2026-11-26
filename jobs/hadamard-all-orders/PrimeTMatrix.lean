import Constructions

namespace HadamardAllOrders

private theorem small_of_square_le_599 {x : Nat} (hx : x * x ≤ 599) : x ≤ 24 := by
  by_cases h : x ≤ 24
  · exact h
  · have large : 25 * 25 ≤ x * x := Nat.mul_le_mul (by omega) (by omega)
    omega

/-- Absolute row sums are enough. Three channels omit zero and one takes the sign at zero. -/
theorem t599_no_fixed_multiplier_13 (a b c z : Nat)
    (ha : a % 13 = 0) (hb : b % 13 = 0) (hc : c % 13 = 0)
    (hz : z % 13 = 1 ∨ z % 13 = 12) : a * a + b * b + c * c + z * z ≠ 599 := by
  intro total
  have aSmall := small_of_square_le_599 (x := a) (by omega)
  have bSmall := small_of_square_le_599 (x := b) (by omega)
  have cSmall := small_of_square_le_599 (x := c) (by omega)
  have zSmall := small_of_square_le_599 (x := z) (by omega)
  have aValues : a = 0 ∨ a = 13 := by omega
  have bValues : b = 0 ∨ b = 13 := by omega
  have cValues : c = 0 ∨ c = 13 := by omega
  have zValues : z = 1 ∨ z = 12 ∨ z = 14 := by omega
  rcases aValues with rfl | rfl <;> rcases bValues with rfl | rfl <;>
    rcases cValues with rfl | rfl <;> rcases zValues with rfl | rfl | rfl <;> simp at total

/-- Absolute row sums of four orbit-constant channels under an order-23 multiplier. -/
theorem t599_no_fixed_multiplier_23 (a b c z : Nat)
    (ha : a % 23 = 0) (hb : b % 23 = 0) (hc : c % 23 = 0)
    (hz : z % 23 = 1 ∨ z % 23 = 22) : a * a + b * b + c * c + z * z ≠ 599 := by
  intro total
  have aSmall := small_of_square_le_599 (x := a) (by omega)
  have bSmall := small_of_square_le_599 (x := b) (by omega)
  have cSmall := small_of_square_le_599 (x := c) (by omega)
  have zSmall := small_of_square_le_599 (x := z) (by omega)
  have aValues : a = 0 ∨ a = 23 := by omega
  have bValues : b = 0 ∨ b = 23 := by omega
  have cValues : c = 0 ∨ c = 23 := by omega
  have zValues : z = 1 ∨ z = 22 ∨ z = 24 := by omega
  rcases aValues with rfl | rfl <;> rcases bValues with rfl | rfl <;>
    rcases cValues with rfl | rfl <;> rcases zValues with rfl | rfl | rfl <;> simp at total

/-- One singleton channel at zero and one reflected pair cannot give order 7 modulo 8. -/
theorem t_matrix_reflected_pair_residue (b : Nat) : (1 + 2 * (b * b)) % 8 ≠ 7 := by
  rw [Nat.add_mod 1 (2 * (b * b)) 8, Nat.mul_mod 2 (b * b) 8, Nat.mul_mod b b 8]
  have bound := Nat.mod_lt b (by decide : 0 < 8)
  have casesMod : b % 8 = 0 ∨ b % 8 = 1 ∨ b % 8 = 2 ∨ b % 8 = 3 ∨
      b % 8 = 4 ∨ b % 8 = 5 ∨ b % 8 = 6 ∨ b % 8 = 7 := by omega
  rcases casesMod with h | h | h | h | h | h | h | h <;> rw [h] <;> decide

theorem t599_no_reflected_pair (b : Nat) : 1 + 2 * (b * b) ≠ 599 := by
  intro h
  exact t_matrix_reflected_pair_residue b (congrArg (fun x : Nat => x % 8) h)

#print axioms t599_no_fixed_multiplier_13
#print axioms t599_no_fixed_multiplier_23
#print axioms t599_no_reflected_pair

end HadamardAllOrders
