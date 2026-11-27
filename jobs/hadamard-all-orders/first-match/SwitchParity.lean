import Triples

namespace HadamardAllOrders

open Hadamard2396 (sumAt sumAt_succ)

private theorem ternary_parity {a b : Int} (ha : -1 ≤ a ∧ a ≤ 1)
    (hb : -1 ≤ b ∧ b ≤ 1) (different : a ≠ b) :
    (a + b + a*b) % 2 = 1 := by
  have av : a = -1 ∨ a = 0 ∨ a = 1 := by omega
  have bv : b = -1 ∨ b = 0 ∨ b = 1 := by omega
  rcases av with h | h | h <;> rcases bv with k | k | k <;>
    subst a <;> subst b <;> first | contradiction | decide

private theorem different_sum_parity (n : Nat) (a b : Nat → Int)
    (ha : ∀ i, i < n → -1 ≤ a i ∧ a i ≤ 1)
    (hb : ∀ i, i < n → -1 ≤ b i ∧ b i ≤ 1)
    (different : ∀ i, i < n → a i ≠ b i) :
    (sumAt n a + sumAt n b + sumAt n (fun i => a i * b i)) % 2 = (n : Int) % 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have earlier := ih (fun i hi => ha i (by omega)) (fun i hi => hb i (by omega))
      (fun i hi => different i (by omega))
    have here := ternary_parity (ha n (by omega)) (hb n (by omega)) (different n (by omega))
    simp only [sumAt_succ, Int.natCast_succ]
    omega

/-- Two ternary lists of odd common length agree somewhere if both sums and
their dot product are even. Apply this to the two row differences of a full clique. -/
theorem ternary_coincidence_of_odd (n : Nat) (a b : Nat → Int)
    (odd : (n : Int) % 2 = 1)
    (ha : ∀ i, i < n → -1 ≤ a i ∧ a i ≤ 1)
    (hb : ∀ i, i < n → -1 ≤ b i ∧ b i ≤ 1)
    (evenA : sumAt n a % 2 = 0) (evenB : sumAt n b % 2 = 0)
    (evenDot : sumAt n (fun i => a i * b i) % 2 = 0) :
    ∃ i, i < n ∧ a i = b i := by
  by_cases same : ∃ i, i < n ∧ a i = b i
  · exact same
  · have different (i : Nat) (hi : i < n) (h : a i = b i) : False := same ⟨i, hi, h⟩
    have h := different_sum_parity n a b ha hb different
    omega

#print axioms ternary_coincidence_of_odd

end HadamardAllOrders
