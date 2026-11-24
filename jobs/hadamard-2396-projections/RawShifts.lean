import Witness

namespace Hadamard2396
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Sum of both autocorrelations on the original 1197 positions. -/
def combinedPaf (s : Nat) : Int :=
  paf 1197 (signWord wordA) s + paf 1197 (signWord wordB) s

private def primary : List Nat :=
  [63,126,133,171,189,252,266,315,342,378,399,441,504,513,532,567,630,665,684,693,756,798,819,855,882,931,945,1008,1026,1064,1071,1134]

private theorem coverage (s : Fin 1197) (h₀ : s.val ≠ 0)
    (h : 7*s.val%1197 = 0 ∨ 9*s.val%1197 = 0 ∨ 19*s.val%1197 = 0) :
    s.val ∈ primary := by
  have hAll : ∀ t : Fin 1197, t.val ≠ 0 →
      (7*t.val%1197 = 0 ∨ 9*t.val%1197 = 0 ∨ 19*t.val%1197 = 0) →
      t.val ∈ primary := by decide +kernel
  exact hAll s h₀ h

private theorem onPrimary (s : Nat) (h : s ∈ primary) : combinedPaf s = -2 := by
  simp only [primary, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst s; decide +kernel

/-- Every nonzero shift in the subgroups of orders 7, 9 and 19 passes on these very words. -/
theorem exact_primary (s : Fin 1197) (h₀ : s.val ≠ 0)
    (h : 7*s.val%1197 = 0 ∨ 9*s.val%1197 = 0 ∨ 19*s.val%1197 = 0) :
    combinedPaf s.val = -2 :=
  onPrimary s.val (coverage s h₀ h)

/-- This certificate fails the first original equation. -/
theorem shift_one : combinedPaf 1 = 2 := by decide +kernel

#print axioms exact_primary
#print axioms shift_one
end Hadamard2396
