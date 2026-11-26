import Constructions

namespace HadamardAllOrders

/-- The multiplier of the Paley block product with the order-three T-matrices. -/
def paleyTripleMultiplier (q : Nat) := 3 * ((q + 1) / 4)

set_option exponentiation.threshold 528 in
set_option maxRecDepth 4096 in
theorem paley_triple_residue (k : Nat) : 107 ^ (528 * k + 1) % 2080120 = 107 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show 528 * (k + 1) + 1 = 528 * k + 1 + 528 by omega, Nat.pow_add, Nat.mul_mod, ih]

/-- Both direct Paley parameters have two distinct prime factors throughout this residue class. -/
theorem paley_triple_parameters {q : Nat} (hq : q % 2080120 = 107) :
    q % 8 = 3 ∧ 4 * paleyTripleMultiplier q = 3 * (q + 1) ∧
    paleyTripleMultiplier q % 2 = 1 ∧
    (4 * paleyTripleMultiplier q - 1) % 17 = 0 ∧
    (4 * paleyTripleMultiplier q - 1) % 19 = 0 ∧
    (2 * paleyTripleMultiplier q - 1) % 7 = 0 ∧
    (2 * paleyTripleMultiplier q - 1) % 23 = 0 ∧
    (16 * paleyTripleMultiplier q + 1) % 5 = 2 := by
  have quotient : q = 107 + 2080120 * (q / 2080120) := by
    simpa only [hq] using (Nat.mod_add_div q 2080120).symm
  unfold paleyTripleMultiplier
  omega

theorem square_mod_five_ne_two (x : Nat) : x * x % 5 ≠ 2 := by
  rw [Nat.mul_mod]
  have h := Nat.mod_lt x (by decide : 0 < 5)
  have casesMod : x % 5 = 0 ∨ x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by omega
  rcases casesMod with hr | hr | hr | hr | hr <;> rw [hr] <;> decide

/-- The Scarpis order parameter is excluded even without requiring a prime power. -/
theorem paley_triple_not_scarpis {q : Nat} (hq : q % 2080120 = 107) (a : Nat) :
    a * (a + 1) ≠ 4 * paleyTripleMultiplier q := by
  intro h
  have squareIdentity : (2 * a + 1) * (2 * a + 1) = 4 * (a * (a + 1)) + 1 := by
    simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    omega
  rw [h, show 4 * (4 * paleyTripleMultiplier q) = 16 * paleyTripleMultiplier q by omega] at squareIdentity
  obtain ⟨_, _, _, _, _, _, _, residue⟩ := paley_triple_parameters hq
  exact square_mod_five_ne_two (2 * a + 1) (squareIdentity ▸ residue)

#print axioms paley_triple_residue
#print axioms paley_triple_parameters
#print axioms paley_triple_not_scarpis

end HadamardAllOrders
