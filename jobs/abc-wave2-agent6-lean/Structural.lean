import Mathlib

set_option autoImplicit false

namespace ABCWave2

theorem parity_transform_identity (a b c : ℚ) (h : a + b = c) :
    b ^ 2 + 4 * a * c = (a + c) ^ 2 := by
  rw [← h]
  ring

theorem inverse_identities (w x : ℚ) :
    (w + x) / 2 + (w - x) / 2 = w ∧
    (w + x) / 2 - (w - x) / 2 = x ∧
    4 * ((w + x) / 2) * ((w - x) / 2) = w ^ 2 - x ^ 2 := by
  constructor
  · ring
  · constructor <;> ring

theorem cutoff_exponent_identity (k e : ℕ) :
    k + (e - k) = e + (k - e) := by
  omega

theorem compensation_budget (H H0 L0 W d A B : ℝ)
    (hH0 : 0 ≤ H0) (hH : H0 ≤ H) (hd : 0 ≤ d) (hA : 0 ≤ A)
    (hroot : (1 - d) * H0 - A ≤ L0)
    (hgrowth : W ≤ max (L0 - H0) 0 + d * H + B) :
    (1 - 2 * d) * H - A - B ≤ H + L0 - H0 - W := by
  have hscale : d * H0 ≤ d * H := mul_le_mul_of_nonneg_left hH hd
  by_cases hsur : 0 ≤ L0 - H0
  · rw [max_eq_left hsur] at hgrowth
    have hHnonneg : 0 ≤ H := le_trans hH0 hH
    have hdH : 0 ≤ d * H := mul_nonneg hd hHnonneg
    nlinarith [hscale, hgrowth, hdH]
  · have hsur' : L0 - H0 ≤ 0 := le_of_lt (lt_of_not_ge hsur)
    rw [max_eq_right hsur'] at hgrowth
    nlinarith [hscale, hroot, hgrowth]

theorem budget_log_bound (H L d e A B : ℝ) (he : 0 ≤ 1 + e)
    (hchoice : (1 + e) * (1 - 2 * d) = 1)
    (hbudget : (1 - 2 * d) * H - A - B ≤ L) :
    H ≤ (1 + e) * L + (1 + e) * (A + B) := by
  have hscale := mul_le_mul_of_nonneg_left hbudget he
  have hidentity := congrArg (fun q : ℝ => q * H) hchoice
  nlinarith [hscale, hidentity]

theorem epsilon_choice (e : ℝ) (he : 0 < e) :
    0 < e / (2 * (1 + e)) ∧ e / (2 * (1 + e)) < 1 / 2 ∧
    (1 + e) * (1 - 2 * (e / (2 * (1 + e)))) = 1 := by
  have hpos : 0 < 2 * (1 + e) := by positivity
  have hne : 1 + e ≠ 0 := by linarith
  constructor
  · exact div_pos he hpos
  · constructor
    · apply (div_lt_iff₀ hpos).2
      linarith
    · field_simp [hne] <;> ring

theorem uniform_root_orbit_composition {ι : Type*}
    (H0 L0 : ι → ℝ) (H L W : ι → ℕ → ℝ)
    (hH0 : ∀ r, 0 ≤ H0 r)
    (hH : ∀ r n, H0 r ≤ H r n)
    (hidentity : ∀ r n, L r n = H r n + L0 r - H0 r - W r n)
    (hroot : ∀ d : ℝ, 0 < d → d < 1 / 2 →
      ∃ A : ℝ, 0 ≤ A ∧ ∀ r, (1 - d) * H0 r - A ≤ L0 r)
    (hgrowth : ∀ d : ℝ, 0 < d → d < 1 / 2 →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ r n,
        W r n ≤ max (L0 r - H0 r) 0 + d * H r n + B) :
    ∀ e : ℝ, 0 < e → ∃ C : ℝ, ∀ r n,
      H r n ≤ (1 + e) * L r n + C := by
  intro e he
  let d : ℝ := e / (2 * (1 + e))
  have hchoice := epsilon_choice e he
  have hdpos : 0 < d := hchoice.1
  have hdhalf : d < 1 / 2 := hchoice.2.1
  have heq : (1 + e) * (1 - 2 * d) = 1 := hchoice.2.2
  obtain ⟨A, hA, hrootA⟩ := hroot d hdpos hdhalf
  obtain ⟨B, hB, hgrowthB⟩ := hgrowth d hdpos hdhalf
  refine ⟨(1 + e) * (A + B), ?_⟩
  intro r n
  have hb := compensation_budget (H r n) (H0 r) (L0 r) (W r n) d A B
    (hH0 r) (hH r n) (le_of_lt hdpos) hA (hrootA r) (hgrowthB r n)
  have hL : (1 - 2 * d) * H r n - A - B ≤ L r n := by
    rw [hidentity r n]
    exact hb
  exact budget_log_bound (H r n) (L r n) d e A B (by linarith) heq hL

theorem cubic_compensation (a b c R U S : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hR : R ≠ 0) (hS : S ≠ 0)
    (hfactor : R ^ 3 * U = a * b * c * S) :
    (c / R) ^ 3 = (U / S) * (c / a) * (c / b) := by
  have hscaled := congrArg (fun q : ℝ => q * c ^ 2) hfactor
  field_simp [ha, hb, hR, hS]
  nlinarith [hscaled]

theorem cube_free_integer_bridge (a b c R : ℤ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hR : 1 ≤ R)
    (hadd : a + b = c) (hproduct : a * b * c ≤ R ^ 2) :
    c ≤ R := by
  have hprod : 0 ≤ (a - 1) * (b - 1) :=
    mul_nonneg (by linarith) (by linarith)
  have hab : c - 1 ≤ a * b := by nlinarith [hprod]
  have hc : 0 ≤ c := by linarith
  have hmass := mul_le_mul_of_nonneg_right hab hc
  by_contra h
  have hcR : R + 1 ≤ c := by omega
  have hgap : 0 ≤ (c - (R + 1)) * (c + R) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith [hmass, hgap, hproduct]

theorem cube_free_natural_bridge (a b c R : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hadd : a + b = c) (hproduct : a * b * c ≤ R ^ 2) :
    c ≤ R := by
  have ha' : (1 : ℤ) ≤ (a : ℤ) := by exact_mod_cast (Nat.succ_le_of_lt ha)
  have hb' : (1 : ℤ) ≤ (b : ℤ) := by exact_mod_cast (Nat.succ_le_of_lt hb)
  have hR' : (1 : ℤ) ≤ (R : ℤ) := by exact_mod_cast (Nat.succ_le_of_lt hR)
  have hadd' : (a : ℤ) + (b : ℤ) = (c : ℤ) := by exact_mod_cast hadd
  have hp' : (a : ℤ) * (b : ℤ) * (c : ℤ) ≤ (R : ℤ) ^ 2 := by
    exact_mod_cast hproduct
  have result := cube_free_integer_bridge (a : ℤ) (b : ℤ) (c : ℤ) (R : ℤ)
    ha' hb' hR' hadd' hp'
  exact_mod_cast result

theorem mass_prefix_step (e : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), e j) =
      (∑ j ∈ Finset.range n, e j) + e n := by
  exact Finset.sum_range_succ e n

theorem one_level_controls_next (e : ℕ → ℝ) (n : ℕ)
    (he : ∀ j, 0 ≤ e j) :
    e n ≤ ∑ j ∈ Finset.range (n + 1), e j := by
  have hp : 0 ≤ ∑ j ∈ Finset.range n, e j :=
    Finset.sum_nonneg (fun j _ => he j)
  rw [Finset.sum_range_succ]
  linarith

theorem positive_mass_log_bound (H k T C L : ℝ)
    (hC : C ≤ (k / 4) * T)
    (hL : L ≤ H * T + C - (k / 2) * T) :
    L ≤ (H - k / 4) * T := by
  nlinarith [hC, hL]

theorem quality_margin_identity (H k : ℝ) (hH : 0 < H)
    (hk : 0 < k) (hkH : k ≤ H) :
    H / (H - k / 4) = 1 + k / (4 * H - k) ∧
    0 < k / (4 * H - k) := by
  have hd : 0 < 4 * H - k := by linarith
  have he : 0 < H - k / 4 := by linarith
  constructor
  · have hnormalized : H * 4 - k ≠ 0 := by nlinarith
    field_simp [ne_of_gt hd, ne_of_gt he, hnormalized] <;> ring
  · exact div_pos hk hd

end ABCWave2

#print axioms ABCWave2.parity_transform_identity
#print axioms ABCWave2.inverse_identities
#print axioms ABCWave2.cutoff_exponent_identity
#print axioms ABCWave2.compensation_budget
#print axioms ABCWave2.budget_log_bound
#print axioms ABCWave2.epsilon_choice
#print axioms ABCWave2.uniform_root_orbit_composition
#print axioms ABCWave2.cubic_compensation
#print axioms ABCWave2.cube_free_integer_bridge
#print axioms ABCWave2.cube_free_natural_bridge
#print axioms ABCWave2.mass_prefix_step
#print axioms ABCWave2.one_level_controls_next
#print axioms ABCWave2.positive_mass_log_bound
#print axioms ABCWave2.quality_margin_identity
