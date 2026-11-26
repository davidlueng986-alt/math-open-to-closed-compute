import Std

namespace HadamardAllOrders

def golayLength (k : Nat) : Nat := 2 ^ (82 + 8604 * k) * 26 ^ 33

def golayMultiplier (k : Nat) : Nat := 2 * golayLength k + 1

set_option exponentiation.threshold 8604 in
set_option maxRecDepth 32768 in
theorem golay_length_residue (k : Nat) : golayLength k % 12422865 = 9153989 := by
  induction k with
  | zero => decide
  | succ k ih =>
    have step : golayLength (k + 1) = golayLength k * 2 ^ 8604 := by
      unfold golayLength
      rw [show 82 + 8604 * (k + 1) = 82 + 8604 * k + 8604 by omega, Nat.pow_add,
        Nat.mul_right_comm]
    have period : 2 ^ 8604 % 12422865 = 1 := by decide
    rw [step, Nat.mul_mod, ih, period]

theorem golay_parameters (k : Nat) :
    golayMultiplier k % 100590 = 599 ∧
    golayMultiplier k % 13 = 1 ∧
    golayMultiplier k % 19 = 16 ∧
    (4 * golayMultiplier k - 1) % 2395 = 0 ∧
    (2 * golayMultiplier k - 1) % 21 = 0 ∧
    (16 * golayMultiplier k + 1) % 19 = 10 := by
  have quotient : golayLength k = 9153989 + 12422865 * (golayLength k / 12422865) := by
    simpa only [golay_length_residue] using (Nat.mod_add_div (golayLength k) 12422865).symm
  unfold golayMultiplier
  omega

private theorem scarpis_square {a t : Nat} (h : a * (a + 1) = 4 * t) :
    (2 * a + 1) * (2 * a + 1) = 16 * t + 1 := by
  calc
    (2 * a + 1) * (2 * a + 1) = 4 * (a * (a + 1)) + 1 := by
      simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      omega
    _ = 16 * t + 1 := by rw [h]; omega

theorem golay_not_scarpis (k a : Nat) : a * (a + 1) ≠ 4 * golayMultiplier k := by
  intro h
  obtain ⟨_, _, _, _, _, residue⟩ := golay_parameters k
  have squares : ∀ x : Fin 19, x.val * x.val % 19 ≠ 10 := by decide
  have contradiction := scarpis_square h ▸ residue
  rw [Nat.mul_mod] at contradiction
  exact squares ⟨(2 * a + 1) % 19, Nat.mod_lt _ (by decide)⟩ contradiction

#print axioms golay_length_residue
#print axioms golay_parameters
#print axioms golay_not_scarpis

def golayPaleyPrimePower (k : Nat) : Nat := 3 ^ (217 + 94644 * k)

def golayPaleyMultiplier (k : Nat) : Nat := 95051009 * ((golayPaleyPrimePower k + 1) / 4)

set_option exponentiation.threshold 94644 in
set_option maxRecDepth 65536 in
theorem golay_paley_residue_coprime (k : Nat) :
    golayPaleyPrimePower k % 761935720 = 150907123 := by
  induction k with
  | zero => decide
  | succ k ih =>
    have step : golayPaleyPrimePower (k + 1) = golayPaleyPrimePower k * 3 ^ 94644 := by
      unfold golayPaleyPrimePower
      rw [show 217 + 94644 * (k + 1) = 217 + 94644 * k + 94644 by omega, Nat.pow_add]
    have period : 3 ^ 94644 % 761935720 = 1 := by decide
    rw [step, Nat.mul_mod, ih, period]

theorem golay_paley_residue (k : Nat) :
    golayPaleyPrimePower k % 2285807160 = 1674778563 := by
  let j := golayPaleyPrimePower k / 761935720
  have hthree : golayPaleyPrimePower k % 3 = 0 := by
    unfold golayPaleyPrimePower
    rw [show 217 + 94644 * k = 216 + 94644 * k + 1 by omega, Nat.pow_succ, Nat.mul_mod]
    omega
  have quotient : golayPaleyPrimePower k = 150907123 + 761935720 * j := by
    simpa only [golay_paley_residue_coprime] using
      (Nat.mod_add_div (golayPaleyPrimePower k) 761935720).symm
  have jmod : j % 3 = 2 := by
    rw [quotient, Nat.add_mod, Nat.mul_mod] at hthree
    simp only [show 150907123 % 3 = 1 by decide, Nat.one_mul, Nat.mod_mod] at hthree
    omega
  have jrepr : j = 2 + 3 * (j / 3) := by
    simpa only [jmod] using (Nat.mod_add_div j 3).symm
  rw [quotient, jrepr, Nat.mul_add]
  have period : 761935720 * (3 * (j / 3)) = 2285807160 * (j / 3) := by rw [← Nat.mul_assoc]
  rw [period, ← Nat.add_assoc]
  omega

theorem golay_paley_parameters (k : Nat) :
    golayPaleyPrimePower k % 8 = 3 ∧
    golayPaleyMultiplier k % 100590 = 599 ∧
    golayPaleyMultiplier k % 13 = 1 ∧
    golayPaleyMultiplier k % 19 = 13 ∧
    (16 * golayPaleyMultiplier k + 1) % 23 = 20 := by
  have quotient :
      golayPaleyPrimePower k = 1674778563 + 2285807160 * (golayPaleyPrimePower k / 2285807160) := by
    simpa only [golay_paley_residue] using
      (Nat.mod_add_div (golayPaleyPrimePower k) 2285807160).symm
  unfold golayPaleyMultiplier
  omega

theorem golay_paley_not_scarpis (k a : Nat) : a * (a + 1) ≠ 4 * golayPaleyMultiplier k := by
  intro h
  obtain ⟨_, _, _, _, residue⟩ := golay_paley_parameters k
  have squares : ∀ x : Fin 23, x.val * x.val % 23 ≠ 20 := by decide
  have contradiction := scarpis_square h ▸ residue
  rw [Nat.mul_mod] at contradiction
  exact squares ⟨(2 * a + 1) % 23, Nat.mod_lt _ (by decide)⟩ contradiction

#print axioms golay_paley_residue_coprime
#print axioms golay_paley_residue
#print axioms golay_paley_parameters
#print axioms golay_paley_not_scarpis

end HadamardAllOrders
