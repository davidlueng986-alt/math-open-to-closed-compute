import Mathlib

/-! Exact arc-choice arithmetic for a spanning pentagon factor.
    The graph contraction proof uses this arithmetic. This is not a
    proof of general global unavoidability or the original conjecture. -/
namespace Erdos64Pentagon

theorem two_pow_mod_three (k : ℕ) :
    (2 ^ k : ℕ) % 3 = 1 ∨ (2 ^ k : ℕ) % 3 = 2 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> decide

/-- For a dyadic quotient cycle visiting a adjacent-port pentagons and
    b distance-two-port pentagons, the original cycle length can be a
    power of two. The numbers of long arcs are i and j, respectively.
    In the two types the contributions including one external edge are
    2 or 5, and 3 or 4. -/
theorem pentagon_lift_counts (a b k : ℕ) (h : a + b = 2 ^ k) :
    ∃ i j : ℕ, i ≤ a ∧ j ≤ b ∧
      (2*a + 3*b + 3*i + j = 2^(k+1) ∨
       2*a + 3*b + 3*i + j = 2^(k+2)) := by
  have h2 : (2 : ℕ)^(k+1) = 2*(a+b) := by
    rw [pow_succ, ← h]
    omega
  have h4 : (2 : ℕ)^(k+2) = 4*(a+b) := by
    rw [pow_add, ← h]
    norm_num <;> omega
  by_cases hb : b = 0
  · refine ⟨0, 0, by omega, by omega, Or.inl ?_⟩
    omega
  · have hmod : (2*a+b)%3 ≤ b := by
      have hm := Nat.mod_lt (2*a+b) (by decide : 0 < 3)
      by_cases hb1 : b = 1
      · rcases two_pow_mod_three k with hr | hr <;> omega
      · omega
    by_cases hq : (2*a+b)/3 ≤ a
    · refine ⟨(2*a+b)/3, (2*a+b)%3, hq, hmod, Or.inr ?_⟩
      omega
    · refine ⟨a, (2*a+b)-3*a, le_rfl, ?_, Or.inr ?_⟩ <;> omega

#print axioms two_pow_mod_three
#print axioms pentagon_lift_counts
end Erdos64Pentagon
