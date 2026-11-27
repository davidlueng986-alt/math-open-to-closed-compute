import Mathlib

set_option autoImplicit false

namespace ABCWave1

theorem frey_discriminant_identity (a b : ℚ) :
    (16 * (a ^ 2 + a * b + b ^ 2)) ^ 3 -
      (32 * (a - b) * (2 * a + b) * (a + 2 * b)) ^ 2 =
      1728 * (16 * (a * b * (a + b)) ^ 2) := by
  ring

theorem minimal_invariants_identity (a b : ℚ) :
    (a ^ 2 + a * b + b ^ 2) ^ 3 -
      (((a - b) * (2 * a + b) * (a + 2 * b)) / 2) ^ 2 =
      1728 * ((a * b * (a + b)) ^ 2 / 256) := by
  ring

theorem doubling_identity (a b : ℚ) :
    (a - b) ^ 2 + 4 * a * b = (a + b) ^ 2 := by
  ring

theorem c4_sum_of_squares (a b : ℝ) :
    2 * (a ^ 2 + a * b + b ^ 2) = a ^ 2 + b ^ 2 + (a + b) ^ 2 := by
  ring

theorem c4_dominates_a (a b : ℝ) :
    a ^ 2 / 2 ≤ a ^ 2 + a * b + b ^ 2 := by
  nlinarith [sq_nonneg (a + b), sq_nonneg b]

theorem c4_dominates_b (a b : ℝ) :
    b ^ 2 / 2 ≤ a ^ 2 + a * b + b ^ 2 := by
  nlinarith [sq_nonneg (a + b), sq_nonneg a]

theorem c4_dominates_sum (a b : ℝ) :
    (a + b) ^ 2 / 2 ≤ a ^ 2 + a * b + b ^ 2 := by
  nlinarith [sq_nonneg a, sq_nonneg b]

theorem frey_epsilon_equation (e eta : ℝ)
    (h : eta * (4 + 3 * e) = 6 * e) :
    6 + eta = (1 + e) * (6 - 3 * eta) := by
  nlinarith [h]

theorem frey_epsilon_choice (e : ℝ) (he : 0 < e) :
    (6 * e / (4 + 3 * e)) * (4 + 3 * e) = 6 * e := by
  have hd : 4 + 3 * e ≠ 0 := by linarith
  field_simp [hd]

theorem reverse_epsilon_equation (eta d : ℝ)
    (h : d * (36 + 5 * eta) = eta) :
    6 * (1 + d) = (6 + eta) * (1 - 5 * d) := by
  nlinarith [h]

theorem reverse_epsilon_choice (eta : ℝ) (he : 0 < eta) :
    (eta / (36 + 5 * eta)) * (36 + 5 * eta) = eta := by
  have hd : 36 + 5 * eta ≠ 0 := by linarith
  field_simp [hd]

theorem balanced_factorization (a c : ℝ) :
    16 * a * (c - a) - 3 * c ^ 2 = (4 * a - c) * (3 * c - 4 * a) := by
  ring

theorem balanced_cube_excess_step (a b c R U : ℝ)
    (hadd : a + b = c) (hleft : c ≤ 4 * a) (hright : 2 * a ≤ c)
    (hc : 0 ≤ c) (hfactor : a * b * c ≤ R ^ 3 * U) :
    3 * c ^ 3 ≤ 16 * R ^ 3 * U := by
  have hfirst : 0 ≤ 4 * a - c := by linarith
  have hsecond : 0 ≤ 3 * c - 4 * a := by linarith
  have hb : 0 ≤ 16 * a * b - 3 * c ^ 2 := by
    calc
      0 ≤ (4 * a - c) * (3 * c - 4 * a) := mul_nonneg hfirst hsecond
      _ = 16 * a * b - 3 * c ^ 2 := by rw [← hadd]; ring
  have hbc := mul_nonneg hb hc
  nlinarith [hbc, hfactor]

theorem exponent_tail (e : ℕ) : e ≤ 3 + (e - 3) := by
  omega

theorem normalization_error_iff (x s E : ℝ) :
    -x ≤ -s * x + E ↔ (s - 1) * x ≤ E := by
  constructor <;> intro h <;> nlinarith [h]

theorem positive_scaling_needs_error (x s : ℝ) (hx : 0 < x) (hs : 1 < s) :
    ¬ (-x ≤ -s * x) := by
  intro h
  have hp := mul_pos (sub_pos.mpr hs) hx
  nlinarith [hp]

theorem reyssat_sum : (2 : ℕ) + 3 ^ 10 * 109 = 23 ^ 5 := by
  norm_num

theorem reyssat_prime_support :
    Nat.Prime 2 ∧ Nat.Prime 3 ∧ Nat.Prime 109 ∧ Nat.Prime 23 := by
  norm_num

theorem reyssat_coprime : Nat.Coprime 2 (3 ^ 10 * 109) := by
  norm_num [Nat.Coprime]

theorem reyssat_radical_product : (2 : ℕ) * 3 * 109 * 23 = 15042 := by
  norm_num

theorem reyssat_exact_quality_test : (6436343 : ℕ) ^ 5 > 15042 ^ 8 := by
  norm_num

def radical (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ p ∣ n)).prod (fun p => p)

theorem radical_support_iff (n p : ℕ) (hn : 0 < n) :
    p ∈ (Finset.range (n + 1)).filter (fun r => Nat.Prime r ∧ r ∣ n) ↔
      Nat.Prime p ∧ p ∣ n := by
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨Nat.lt_succ_iff.mpr (Nat.le_of_dvd hn h.2), h⟩

theorem radical_positive (n : ℕ) : 0 < radical n := by
  unfold radical
  apply Finset.prod_pos
  intro p hp
  exact ((Finset.mem_filter.mp hp).2).1.pos

def PrimitiveTriple (a b c : ℕ) : Prop :=
  0 < a ∧ 0 < b ∧ 0 < c ∧ a + b = c ∧ Nat.Coprime a b

def ArithmeticABC : Prop :=
  ∀ e : ℝ, 0 < e → ∃ K : ℝ, 0 < K ∧
    ∀ a b c : ℕ, PrimitiveTriple a b c →
      (c : ℝ) < K * (radical (a * b * c) : ℝ) ^ (1 + e)

def UnboundedRatioAt (e : ℝ) : Prop :=
  ∀ K : ℝ, 0 < K → ∃ a b c : ℕ, PrimitiveTriple a b c ∧
    K * (radical (a * b * c) : ℝ) ^ (1 + e) ≤ (c : ℝ)

theorem unbounded_ratio_refutes_abc (e : ℝ) (he : 0 < e)
    (hsequence : UnboundedRatioAt e) : ¬ ArithmeticABC := by
  intro habc
  obtain ⟨K, hK, hbound⟩ := habc e he
  obtain ⟨a, b, c, htriple, hlarge⟩ := hsequence K hK
  exact (not_le_of_gt (hbound a b c htriple)) hlarge

end ABCWave1

#print axioms ABCWave1.frey_discriminant_identity
#print axioms ABCWave1.minimal_invariants_identity
#print axioms ABCWave1.doubling_identity
#print axioms ABCWave1.c4_sum_of_squares
#print axioms ABCWave1.c4_dominates_a
#print axioms ABCWave1.c4_dominates_b
#print axioms ABCWave1.c4_dominates_sum
#print axioms ABCWave1.frey_epsilon_equation
#print axioms ABCWave1.frey_epsilon_choice
#print axioms ABCWave1.reverse_epsilon_equation
#print axioms ABCWave1.reverse_epsilon_choice
#print axioms ABCWave1.balanced_factorization
#print axioms ABCWave1.balanced_cube_excess_step
#print axioms ABCWave1.exponent_tail
#print axioms ABCWave1.normalization_error_iff
#print axioms ABCWave1.positive_scaling_needs_error
#print axioms ABCWave1.reyssat_sum
#print axioms ABCWave1.reyssat_prime_support
#print axioms ABCWave1.reyssat_coprime
#print axioms ABCWave1.reyssat_radical_product
#print axioms ABCWave1.reyssat_exact_quality_test
#print axioms ABCWave1.radical_support_iff
#print axioms ABCWave1.radical_positive
#print axioms ABCWave1.unbounded_ratio_refutes_abc
