import Std

namespace HadamardAllOrders

def paleyThirteenMultiplier (q : Nat) := 13 * ((q + 1) / 4)

set_option exponentiation.threshold 1434 in
set_option maxRecDepth 8192 in
theorem paley_thirteen_residue (k : Nat) : 712051 ^ (1434 * k + 1) % 7644840 = 712051 := by
  induction k with
  | zero => decide
  | succ k ih =>
    have period : 712051 ^ 1434 % 7644840 = 1 := by decide
    rw [show 1434 * (k + 1) + 1 = 1434 * k + 1 + 1434 by omega, Nat.pow_add, Nat.mul_mod, ih, period]

/-- The parameter lies in the previously isolated arithmetic progression and avoids
the two direct Paley tests and every Scarpis parameter. -/
theorem paley_thirteen_parameters {q : Nat} (hq : q % 7644840 = 712051) :
    q % 8 = 3 ∧ 4 * paleyThirteenMultiplier q = 13 * (q + 1) ∧
    paleyThirteenMultiplier q % 100590 = 599 ∧
    (4 * paleyThirteenMultiplier q - 1) % 5 = 0 ∧
    (4 * paleyThirteenMultiplier q - 1) % 479 = 0 ∧
    (2 * paleyThirteenMultiplier q - 1) % 3 = 0 ∧
    (2 * paleyThirteenMultiplier q - 1) % 7 = 0 ∧
    (16 * paleyThirteenMultiplier q + 1) % 19 = 18 := by
  have quotient : q = 712051 + 7644840 * (q / 7644840) := by
    simpa only [hq] using (Nat.mod_add_div q 7644840).symm
  unfold paleyThirteenMultiplier
  omega

theorem paley_thirteen_not_scarpis {q : Nat} (hq : q % 7644840 = 712051) (a : Nat) :
    a * (a + 1) ≠ 4 * paleyThirteenMultiplier q := by
  intro h
  have identity : (2 * a + 1) * (2 * a + 1) = 4 * (a * (a + 1)) + 1 := by
    simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    omega
  rw [h, show 4 * (4 * paleyThirteenMultiplier q) = 16 * paleyThirteenMultiplier q by omega] at identity
  obtain ⟨_, _, _, _, _, _, _, residue⟩ := paley_thirteen_parameters hq
  have squares : ∀ x : Fin 19, x.val * x.val % 19 ≠ 18 := by decide
  have contradiction := identity ▸ residue
  rw [Nat.mul_mod] at contradiction
  exact squares ⟨(2 * a + 1) % 19, Nat.mod_lt _ (by decide)⟩ contradiction

#print axioms paley_thirteen_residue
#print axioms paley_thirteen_parameters
#print axioms paley_thirteen_not_scarpis

end HadamardAllOrders
