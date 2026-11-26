import Std

namespace HadamardAllOrders

def cfGolayPaleyWidth : Nat := 2 * 2^6 * 26^19 + 1

def cfGolayPaleyQ (k : Nat) : Nat := 3 ^ (2821 + 43020*k)

def cfGolayPaleyT (k : Nat) : Nat := cfGolayPaleyWidth * ((cfGolayPaleyQ k + 1)/4)

set_option exponentiation.threshold 43020 in
set_option maxRecDepth 65536 in
theorem cf_golay_paley_residue_coprime (k : Nat) : cfGolayPaleyQ k % 728808080 = 691811123 := by
  induction k with
  | zero => decide
  | succ k ih =>
    have step : cfGolayPaleyQ (k+1) = cfGolayPaleyQ k * 3^43020 := by
      unfold cfGolayPaleyQ
      rw [show 2821 + 43020*(k+1) = 2821 + 43020*k + 43020 by omega, Nat.pow_add]
    have period : 3^43020 % 728808080 = 1 := by decide
    rw [step, Nat.mul_mod, ih, period]

set_option maxHeartbeats 800000 in
theorem cf_golay_paley_residue (k : Nat) : cfGolayPaleyQ k % 2186424240 = 2149427283 := by
  let j := cfGolayPaleyQ k / 728808080
  have hthree : cfGolayPaleyQ k % 3 = 0 := by
    unfold cfGolayPaleyQ
    rw [show 2821 + 43020*k = 2820 + 43020*k + 1 by omega, Nat.pow_succ, Nat.mul_mod,
      show 3 % 3 = 0 by decide, Nat.mul_zero, Nat.zero_mod]
  have repr : cfGolayPaleyQ k = 691811123 + 728808080*j := by
    simpa only [cf_golay_paley_residue_coprime] using
      (Nat.mod_add_div (cfGolayPaleyQ k) 728808080).symm
  have jmod : j % 3 = 2 := by
    rw [repr, Nat.add_mod, Nat.mul_mod] at hthree
    change (2 + (2*(j%3))%3)%3 = 0 at hthree
    omega
  have jrepr : j = 2 + 3*(j/3) := by
    simpa only [jmod] using (Nat.mod_add_div j 3).symm
  rw [repr, jrepr, Nat.mul_add]
  have period : 728808080*(3*(j/3)) = 2186424240*(j/3) := by rw [← Nat.mul_assoc]
  rw [period, ← Nat.add_assoc]
  omega

theorem cf_golay_paley_parameters (k : Nat) :
    cfGolayPaleyQ k % 8 = 3 ∧
    cfGolayPaleyT k % 24342780 = 20018009 ∧
    cfGolayPaleyT k % 13 = 1 ∧ cfGolayPaleyT k % 19 = 15 ∧
    cfGolayPaleyT k % 121 = 11 ∧ (16*cfGolayPaleyT k + 1) % 19 = 13 := by
  have repr : cfGolayPaleyQ k = 2149427283 + 2186424240*(cfGolayPaleyQ k / 2186424240) := by
    simpa only [cf_golay_paley_residue] using (Nat.mod_add_div (cfGolayPaleyQ k) 2186424240).symm
  let n := cfGolayPaleyQ k / 2186424240
  have side : (cfGolayPaleyQ k + 1)/4 = 537356821 + 546606060*n := by omega
  have t_repr : cfGolayPaleyT k =
      52718900867664690369919178695823026709 + 53626323449618550211390104947341429740*n := by
    unfold cfGolayPaleyT
    rw [side, Nat.mul_add, ← Nat.mul_assoc]
    have constant : cfGolayPaleyWidth * 537356821 = 52718900867664690369919178695823026709 := by decide
    have coefficient : cfGolayPaleyWidth * 546606060 = 53626323449618550211390104947341429740 := by decide
    rw [constant, coefficient]
  rw [repr, t_repr]
  omega

theorem cf_golay_paley_not_scarpis (k a : Nat) : a*(a+1) ≠ 4*cfGolayPaleyT k := by
  intro h
  have formula : (2*a+1)*(2*a+1) = 16*cfGolayPaleyT k + 1 := by
    calc
      (2*a+1)*(2*a+1) = 4*(a*(a+1))+1 := by
        simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        omega
      _ = 16*cfGolayPaleyT k+1 := by rw [h]; omega
  have residual : (16*cfGolayPaleyT k+1)%19 = 13 := (cf_golay_paley_parameters k).2.2.2.2.2
  have squares : ∀ x : Fin 19, x.val*x.val%19 ≠ 13 := by decide
  have contradiction := formula ▸ residual
  rw [Nat.mul_mod] at contradiction
  exact squares ⟨(2*a+1)%19, Nat.mod_lt _ (by decide)⟩ contradiction

set_option exponentiation.threshold 43020 in
set_option maxRecDepth 65536 in
theorem cf_golay_paley_divisibility (k : Nat) : cfGolayPaleyT k % 1621 = 1 := by
  have qres : cfGolayPaleyQ k % 6484 = 5415 := by
    induction k with
    | zero => decide
    | succ k ih =>
      have step : cfGolayPaleyQ (k+1) = cfGolayPaleyQ k * 3^43020 := by
        unfold cfGolayPaleyQ
        rw [show 2821 + 43020*(k+1) = 2821 + 43020*k + 43020 by omega, Nat.pow_add]
      have period : 3^43020 % 6484 = 1 := by decide
      rw [step, Nat.mul_mod, ih, period]
  have repr : cfGolayPaleyQ k = 5415 + 6484*(cfGolayPaleyQ k/6484) := by
    simpa only [qres] using (Nat.mod_add_div (cfGolayPaleyQ k) 6484).symm
  have side : ((cfGolayPaleyQ k+1)/4)%1621 = 1354 := by omega
  unfold cfGolayPaleyT
  rw [Nat.mul_mod, side]
  decide

#print axioms cf_golay_paley_residue_coprime
#print axioms cf_golay_paley_residue
#print axioms cf_golay_paley_parameters
#print axioms cf_golay_paley_not_scarpis
#print axioms cf_golay_paley_divisibility

end HadamardAllOrders
