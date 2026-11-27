import Std

namespace HadamardAllOrders

def coverage45Power (j : Nat) : Nat := 45^(12*j+1)
def coverage45Multiplier (j : Nat) : Nat := (coverage45Power j+1)/2
def coverage45Order (j : Nat) : Nat := 2*(coverage45Power j+1)

/-- The common residue modulo 4·3·5·7·13 along this power progression. -/
theorem coverage45_residue (j : Nat) : coverage45Power j % 5460 = 45 := by
  unfold coverage45Power
  induction j with
  | zero => decide
  | succ j ih =>
    rw [show 12*(j+1)+1 = 12*j+1+12 by omega, Nat.pow_add, Nat.mul_mod, ih]

private theorem residue_of_factor (j d : Nat) (hd : d ∣ 5460) :
    coverage45Power j % d = 45 % d := by
  rw [← Nat.mod_mod_of_dvd _ hd, coverage45_residue]

theorem coverage45_multiplier_properties (j : Nat) :
    5 ≤ coverage45Multiplier j ∧ coverage45Multiplier j % 2 = 1 := by
  have grow : 45 ≤ coverage45Power j := by
    change (45 : Nat)^1 ≤ 45^(12*j+1)
    apply Nat.pow_le_pow_right (by decide)
    omega
  have mod4 : coverage45Power j % 4 = 1 := residue_of_factor j 4 (by decide)
  unfold coverage45Multiplier
  omega

theorem coverage45_order_identities (j : Nat) :
    coverage45Order j = 4*coverage45Multiplier j ∧
    2*coverage45Multiplier j-1 = coverage45Power j ∧
    4*coverage45Multiplier j-1 = 2*coverage45Power j+1 := by
  have mod4 : coverage45Power j % 4 = 1 := residue_of_factor j 4 (by decide)
  unfold coverage45Order coverage45Multiplier
  omega

/-- Each of the two Paley-test arguments is divisible by two distinct primes. -/
theorem coverage45_paley_divisors (j : Nat) :
    3 ∣ 2*coverage45Multiplier j-1 ∧ 5 ∣ 2*coverage45Multiplier j-1 ∧
    7 ∣ 4*coverage45Multiplier j-1 ∧ 13 ∣ 4*coverage45Multiplier j-1 := by
  rw [(coverage45_order_identities j).2.1, (coverage45_order_identities j).2.2]
  have mod7 : coverage45Power j % 7 = 3 := residue_of_factor j 7 (by decide)
  have mod13 : coverage45Power j % 13 = 6 := residue_of_factor j 13 (by decide)
  exact ⟨Nat.dvd_of_mod_eq_zero (residue_of_factor j 3 (by decide)),
    Nat.dvd_of_mod_eq_zero (residue_of_factor j 5 (by decide)),
    Nat.dvd_of_mod_eq_zero (by omega), Nat.dvd_of_mod_eq_zero (by omega)⟩

theorem coverage45_order_mod7 (j : Nat) : coverage45Order j % 7 = 1 := by
  have mod7 : coverage45Power j % 7 = 3 := residue_of_factor j 7 (by decide)
  unfold coverage45Order
  omega

private theorem consecutive_mod7_ne_one (q : Nat) : (q*(q+1)) % 7 ≠ 1 := by
  have bound := Nat.mod_lt q (by decide : 0 < 7)
  rw [Nat.mul_mod, Nat.add_mod q 1 7]
  have small : q%7 = 0 ∨ q%7 = 1 ∨ q%7 = 2 ∨ q%7 = 3 ∨ q%7 = 4 ∨ q%7 = 5 ∨ q%7 = 6 := by
    omega
  rcases small with h | h | h | h | h | h | h <;> rw [h] <;> decide

/-- The Scarpis order equation fails even without restricting q to prime powers. -/
theorem coverage45_no_consecutive_product (j q : Nat) : q*(q+1) ≠ coverage45Order j := by
  intro eq
  apply consecutive_mod7_ne_one q
  rw [eq, coverage45_order_mod7]

theorem coverage45_order_strict {i j : Nat} (h : i < j) : coverage45Order i < coverage45Order j := by
  have grow : coverage45Power i < coverage45Power j := by
    unfold coverage45Power
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  unfold coverage45Order
  omega

#print axioms coverage45_residue
#print axioms coverage45_multiplier_properties
#print axioms coverage45_order_identities
#print axioms coverage45_paley_divisors
#print axioms coverage45_order_mod7
#print axioms coverage45_no_consecutive_product
#print axioms coverage45_order_strict

end HadamardAllOrders
