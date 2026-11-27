import Mathlib
namespace Erdos25FiberFourier
open scoped BigOperators

theorem real_telescoping (a : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, (a (k+1) - a k)) = a n - a 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

theorem abel_tail_identity (a : ℕ → ℝ) (B : ℕ → ℂ) (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), (a k : ℂ) * (B k - B (k+1))) =
      (a 0 : ℂ) * B 0 +
      (∑ k ∈ Finset.range n, ((a (k+1) - a k : ℝ) : ℂ) * B (k+1)) -
      (a n : ℂ) * B (n+1) := by
  induction n with
  | zero =>
    simp
    ring
  | succ n ih =>
    change (∑ k ∈ Finset.range (n+1+1), (a k : ℂ) * (B k - B (k+1))) =
      (a 0 : ℂ) * B 0 +
      (∑ k ∈ Finset.range (n+1), ((a (k+1) - a k : ℝ) : ℂ) * B (k+1)) -
      (a (n+1) : ℂ) * B (n+1+1)
    rw [Finset.sum_range_succ _ (n+1), ih, Finset.sum_range_succ _ n]
    push_cast
    ring

/-- Uniform bound by the maximum norm of the tail sums, for monotone
weights between zero and one. Analytic limits are not formalized here. -/
theorem monotone_tail_bound (a : ℕ → ℝ) (B : ℕ → ℂ) (n : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (ha0 : 0 ≤ a 0) (han : a n ≤ 1)
    (ham : ∀ k, k < n → a k ≤ a (k+1))
    (hb : ∀ k, k ≤ n → ‖B k‖ ≤ C) (hz : B (n+1) = 0) :
    ‖∑ k ∈ Finset.range (n+1), (a k : ℂ) * (B k - B (k+1))‖ ≤ C := by
  rw [abel_tail_identity, hz, mul_zero, sub_zero]
  calc
    ‖(a 0 : ℂ) * B 0 +
        (∑ k ∈ Finset.range n, ((a (k+1) - a k : ℝ) : ℂ) * B (k+1))‖
      ≤ ‖(a 0 : ℂ) * B 0‖ +
        (∑ k ∈ Finset.range n, ‖((a (k+1) - a k : ℝ) : ℂ) * B (k+1)‖) := by
          exact (norm_add_le _ _).trans (add_le_add (le_refl _) (norm_sum_le _ _))
    _ ≤ a 0 * C + ∑ k ∈ Finset.range n, (a (k+1) - a k) * C := by
      apply add_le_add
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha0]
        exact mul_le_mul_of_nonneg_left (hb 0 (Nat.zero_le n)) ha0
      · apply Finset.sum_le_sum
        intro k hk
        have hk' : k < n := Finset.mem_range.mp hk
        have hk0 : 0 ≤ a (k+1) - a k := sub_nonneg.mpr (ham k hk')
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk0]
        exact mul_le_mul_of_nonneg_left (hb (k+1) (by omega)) hk0
    _ = a n * C := by
      rw [← Finset.sum_mul, real_telescoping]
      ring
    _ ≤ C := by
      simpa using mul_le_mul_of_nonneg_right han hC

#print axioms real_telescoping
#print axioms abel_tail_identity
#print axioms monotone_tail_bound
end Erdos25FiberFourier
