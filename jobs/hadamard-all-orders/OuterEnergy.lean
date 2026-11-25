import Constructions

namespace HadamardAllOrders

open Hadamard2396 (sumAt sumAt_succ sumAt_split sumAt_add sumAt_congr sumAt_le)

theorem mul_sum (c : Int) (n : Nat) (f : Nat → Int) :
    c * sumAt n f = sumAt n (fun j => c * f j) := by
  induction n with
  | zero => simp [sumAt]
  | succ n ih => simp [sumAt_succ, Int.mul_add, ih]

theorem sum_mul (c : Int) (n : Nat) (f : Nat → Int) :
    sumAt n f * c = sumAt n (fun j => f j * c) := by
  simpa only [Int.mul_comm _ c] using mul_sum c n f

def firstHalf (t : Nat) (y : Family) (r : Nat) : Int := weight t (fun j => y j r)
def secondHalf (t : Nat) (y : Family) (r : Nat) : Int := weight t (fun j => y (t+j) r)
def imbalance (t : Nat) (y : Family) (r : Nat) := firstHalf t y r - secondHalf t y r

theorem split_row {t : Nat} {y : Family} (hy : Outer t y) {r : Nat} (hr : r < lowerRows t) :
    firstHalf t y r + secondHalf t y r = t := by
  have h := hy.rowSize r hr
  simpa only [weight, show 2*t = t+t by omega, sumAt_split, firstHalf, secondHalf] using h

theorem bit_mul (a b : Bool) : bit a * bit b = bit (a && b) := by
  cases a <;> cases b <;> decide

theorem cross_pairs {t : Nat} {y : Family} (hy : Outer t y) :
    sumAt (lowerRows t) (fun r => firstHalf t y r * secondHalf t y r)
    = (t : Int) * ((t : Int) * ((t : Int)-1)) := by
  have expand (r : Nat) :
      firstHalf t y r * secondHalf t y r =
      sumAt t (fun i => sumAt t (fun j => bit (y i r && y (t+j) r))) := by
    unfold firstHalf secondHalf weight
    rw [sum_mul]
    apply sumAt_congr
    intro i _
    rw [mul_sum]
    apply sumAt_congr
    intro j _
    exact bit_mul _ _
  rw [sumAt_congr _ (fun r _ => expand r), swap_sums (lowerRows t) t]
  have fixed (i : Nat) (hi : i < t) :
      sumAt (lowerRows t) (fun r => sumAt t (fun j => bit (y i r && y (t+j) r))) =
      (t : Int)*((t : Int)-1) := by
    rw [swap_sums (lowerRows t) t, ← sum_const]
    apply sumAt_congr
    intro j hj
    exact hy.common _ _ (by omega) (by omega)
  rw [sumAt_congr _ fixed, sum_const]

/-- For any equal partition of the points (put the halves first and last by relabelling),
the squared row imbalances have an exact total. -/
theorem energy {t : Nat} {y : Family} (ht : 1 ≤ t) (hy : Outer t y) :
    sumAt (lowerRows t) (fun r => imbalance t y r * imbalance t y r) = 2*(t : Int)*(t : Int) := by
  have row {r : Nat} (hr : r < lowerRows t) :
      imbalance t y r * imbalance t y r =
      (t : Int)*(t : Int) + (-4)*(firstHalf t y r * secondHalf t y r) := by
    have hh := split_row hy hr
    unfold imbalance
    rw [← hh]
    grind
  rw [sumAt_congr _ (fun _ hr => row hr), sumAt_add, sum_const, ← mul_sum, cross_pairs hy]
  have size : (lowerRows t : Int) = 4*(t : Int)-2 := by unfold lowerRows; omega
  rw [size]
  grind

theorem sum_single {n j : Nat} (hj : j < n) (c : Int) :
    sumAt n (fun i => if i = j then c else 0) = c := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [sumAt_succ]
    by_cases h : n = j
    · subst j
      have hz := sumAt_congr n (f := fun i => if i = n then c else 0) (g := fun _ => 0)
        (fun _ h => by simp [Nat.ne_of_lt h])
      simp [hz, sum_zero]
    · simp [h, ih (by omega)]

theorem third_row {n r s : Nat} (hn : 3 ≤ n) : ∃ u, u < n ∧ u ≠ r ∧ u ≠ s := by
  by_cases h : 0 ≠ r ∧ 0 ≠ s
  · exact ⟨0, by omega, h⟩
  by_cases h' : 1 ≠ r ∧ 1 ≠ s
  · exact ⟨1, by omega, h'⟩
  exact ⟨2, by omega, by omega, by omega⟩

/-- At odd t ≥ 3, at most one row may consist of an entire half of the points. -/
theorem at_most_one_pure {t : Nat} {y : Family} (ht : 3 ≤ t) (ho : t%2=1) (hy : Outer t y)
    {r s : Nat} (hr : r < lowerRows t) (hs : s < lowerRows t)
    (pr : imbalance t y r * imbalance t y r = (t : Int)*(t : Int))
    (ps : imbalance t y s * imbalance t y s = (t : Int)*(t : Int)) : r = s := by
  by_cases eq : r = s
  · exact eq
  obtain ⟨u, hu, hur, hus⟩ := third_row (n := lowerRows t) (r := r) (s := s) (by unfold lowerRows; omega)
  have nonzero : imbalance t y u ≠ 0 := by
    have hh := split_row hy hu
    unfold imbalance
    omega
  have pos : 1 ≤ imbalance t y u * imbalance t y u := by
    by_cases h : 0 < imbalance t y u
    · exact Int.mul_pos h h
    · exact Int.mul_pos_of_neg_of_neg (by omega) (by omega)
  let one (j : Nat) (v : Int) (i : Nat) := if i = j then v else 0
  let tt := (t : Int)*(t : Int)
  have bound := sumAt_le (lowerRows t)
    (f := fun i => one r tt i + one s tt i + one u 1 i)
    (g := fun i => imbalance t y i * imbalance t y i) (by
      intro i _
      by_cases ir : i = r
      · subst i
        simp [one, eq, Ne.symm hur, pr, tt]
      by_cases is : i = s
      · subst i
        simp [one, ir, Ne.symm hus, ps, tt]
      by_cases iu : i = u
      · subst i
        simpa [one, ir, is] using pos
      simp [one, ir, is, iu]
      by_cases h : 0 ≤ imbalance t y i
      · exact Int.mul_nonneg h h
      · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega))
  simp only [one, sumAt_add, sum_single hr, sum_single hs, sum_single hu, energy (by omega) hy, tt] at bound
  grind

#print axioms at_most_one_pure

end HadamardAllOrders
