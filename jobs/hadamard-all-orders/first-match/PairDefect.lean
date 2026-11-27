import Lattice

namespace HadamardAllOrders

open Hadamard2396 (sumAt sumAt_add sumAt_congr sumAt_le)

/-- Number of points shared by two rows of the outer design. -/
def outsideRowMeet (t : Nat) (y : Family) (p q : Nat) : Int :=
  meet (2*t) (fun j => y j p) (fun j => y j q)

/-- The signed integer column `(YYᵀ − tI)(eₚ + e_q) − (t − 1)·1`. -/
def pairFirstMatch (t : Nat) (y : Family) (p q s : Nat) : Int :=
  firstMatchCentered t y p s + firstMatchCentered t y q s - ((t : Int)-1)

theorem pair_first_match_counts {t p q : Nat} {y : Family} (hy : Outer t y)
    (hp : p < lowerRows t) (hq : q < lowerRows t) :
    (∀ i, i < 2*t → countOn (lowerRows t) (y i) (pairFirstMatch t y p q) = (t : Int)-1) ∧
    sumAt (lowerRows t) (pairFirstMatch t y p q) = 2*(t : Int)-2 := by
  have hp' := first_match_integer hy hp
  have hq' := first_match_integer hy hq
  have double (s : Nat) : 2*pairFirstMatch t y p q s =
      firstMatchInteger t y p s + firstMatchInteger t y q s := by
    unfold pairFirstMatch firstMatchInteger
    omega
  constructor
  · intro i hi
    have twice : 2*countOn (lowerRows t) (y i) (pairFirstMatch t y p q) =
        countOn (lowerRows t) (y i) (firstMatchInteger t y p) +
        countOn (lowerRows t) (y i) (firstMatchInteger t y q) := by
      unfold countOn
      rw [mul_sum, ← sumAt_add]
      apply sumAt_congr
      intro s _
      rw [← Int.mul_add, ← double]
      ac_rfl
    rw [hp'.1 i hi, hq'.1 i hi] at twice
    omega
  · have twice : 2*sumAt (lowerRows t) (pairFirstMatch t y p q) =
        sumAt (lowerRows t) (firstMatchInteger t y p) +
        sumAt (lowerRows t) (firstMatchInteger t y q) := by
      rw [mul_sum, ← sumAt_add]
      exact sumAt_congr _ (fun s _ => double s)
    rw [hp'.2, hq'.2] at twice
    omega

private theorem centered_diagonal {t p : Nat} {y : Family} (hy : Outer t y)
    (hp : p < lowerRows t) : firstMatchCentered t y p p = 0 := by
  change sumAt (2*t) (fun j => bit (y j p)*bit (y j p)) - (if p = p then (t : Int) else 0) = _
  simp only [bit_mul, Bool.and_self]
  change weight (2*t) (fun j => y j p) - (t : Int) = 0
  rw [hy.rowSize p hp]
  omega

private theorem centered_off_diagonal {t p q : Nat} {y : Family} (hne : p ≠ q) :
    firstMatchCentered t y p q = outsideRowMeet t y p q := by
  change sumAt (2*t) (fun j => bit (y j p)*bit (y j q)) -
    (if q = p then (t : Int) else 0) = _
  simp [bit_mul, Ne.symm hne, outsideRowMeet, meet]

/-- Contracting the p-th column of YYᵀ − tI with any first-column count solution. -/
theorem centered_dot_first_count {t p : Nat} {y : Family} (hy : Outer t y)
    (hp : p < lowerRows t) (z : Nat → Int)
    (counts : ∀ i, i < 2*t → countOn (lowerRows t) (y i) z = (t : Int)-1) :
    sumAt (lowerRows t) (fun s => firstMatchCentered t y p s * z s) =
      (t : Int)*((t : Int)-1) - (t : Int)*z p := by
  change sumAt (lowerRows t) (fun s =>
    (sumAt (2*t) (fun j => bit (y j p)*bit (y j s)) - (if s = p then (t : Int) else 0))*z s) = _
  simp only [Int.sub_mul, sum_sub]
  have diagonal (s : Nat) :
      (if s = p then (t : Int) else 0)*z s = if s = p then (t : Int)*z p else 0 := by
    by_cases eq : s = p <;> simp [eq]
  rw [sumAt_congr _ (fun s _ => diagonal s), sum_single hp]
  have other (s : Nat) :
      sumAt (2*t) (fun j => bit (y j p)*bit (y j s))*z s =
        sumAt (2*t) (fun j => bit (y j p)*(bit (y j s)*z s)) := by
    rw [sum_mul]
    apply sumAt_congr
    intro j _
    ac_rfl
  rw [sumAt_congr _ (fun s _ => other s), swap_sums]
  have contracted (j : Nat) (hj : j < 2*t) :
      sumAt (lowerRows t) (fun s => bit (y j p)*(bit (y j s)*z s)) =
        bit (y j p)*((t : Int)-1) := by
    rw [← mul_sum]
    change bit (y j p)*countOn (lowerRows t) (y j) z = _
    rw [counts j hj]
  rw [sumAt_congr _ contracted, ← sum_mul]
  change weight (2*t) (fun j => y j p)*((t : Int)-1) - (t : Int)*z p = _
  rw [hy.rowSize p hp]

/-- The exact quadratic defect of the signed column from two distinct rows. -/
theorem pair_first_match_defect {t p q : Nat} {y : Family} (hy : Outer t y)
    (hp : p < lowerRows t) (hq : q < lowerRows t) (hne : p ≠ q) :
    sumAt (lowerRows t) (fun s => pairFirstMatch t y p q s*(pairFirstMatch t y p q s-1)) =
      2*(t : Int)*((t : Int)-1-outsideRowMeet t y p q) := by
  let z := pairFirstMatch t y p q
  have hz := pair_first_match_counts hy hp hq
  have symmetric : outsideRowMeet t y q p = outsideRowMeet t y p q := meet_comm _ _ _
  have atP : z p = outsideRowMeet t y p q - ((t : Int)-1) := by
    change firstMatchCentered t y p p + firstMatchCentered t y q p - ((t : Int)-1) = _
    rw [centered_diagonal hy hp, centered_off_diagonal (Ne.symm hne), symmetric, Int.zero_add]
  have atQ : z q = outsideRowMeet t y p q - ((t : Int)-1) := by
    change firstMatchCentered t y p q + firstMatchCentered t y q q - ((t : Int)-1) = _
    rw [centered_off_diagonal hne, centered_diagonal hy hq, Int.add_zero]
  have split (s : Nat) :
      z s*(z s-1) = firstMatchCentered t y p s*z s + firstMatchCentered t y q s*z s - (t : Int)*z s := by
    dsimp [z, pairFirstMatch]
    grind
  change sumAt (lowerRows t) (fun s => z s*(z s-1)) = _
  rw [sumAt_congr _ (fun s _ => split s), sum_sub, sumAt_add, ← mul_sum,
    centered_dot_first_count hy hp z hz.1, centered_dot_first_count hy hq z hz.1, hz.2, atP, atQ]
  grind

private theorem binomial_nonnegative (v : Int) : 0 ≤ v*(v-1) := by
  by_cases nonpos : v ≤ 0
  · exact Int.mul_nonneg_of_nonpos_of_nonpos nonpos (by omega)
  · exact Int.mul_nonneg (by omega) (by omega)

/-- Distinct row indices have intersection at most t−1, at every order. -/
theorem outside_distinct_rows_overlap_le {t p q : Nat} {y : Family} (hy : Outer t y)
    (hp : p < lowerRows t) (hq : q < lowerRows t) (hne : p ≠ q) :
    outsideRowMeet t y p q ≤ (t : Int)-1 := by
  have nonnegative := sumAt_le (lowerRows t) (f := fun _ => 0)
    (g := fun s => pairFirstMatch t y p q s*(pairFirstMatch t y p q s-1))
    (fun s _ => binomial_nonnegative (pairFirstMatch t y p q s))
  rw [sum_zero, pair_first_match_defect hy hp hq hne] at nonnegative
  have ht : 0 < t := by unfold lowerRows at hp; omega
  by_cases bound : outsideRowMeet t y p q ≤ (t : Int)-1
  · exact bound
  · have negative : 2*(t : Int)*((t : Int)-1-outsideRowMeet t y p q) < 0 :=
      Int.mul_neg_of_pos_of_neg (by omega) (by omega)
    omega

theorem pair_first_match_binary {t p q : Nat} {y : Family} (hy : Outer t y)
    (hp : p < lowerRows t) (hq : q < lowerRows t) (hne : p ≠ q)
    (near : outsideRowMeet t y p q = (t : Int)-1) (s : Nat) (hs : s < lowerRows t) :
    pairFirstMatch t y p q s = 0 ∨ pairFirstMatch t y p q s = 1 := by
  let z := pairFirstMatch t y p q
  have defect : sumAt (lowerRows t) (fun i => z i*(z i-1)) = 0 := by
    simpa [z, near] using pair_first_match_defect hy hp hq hne
  have individual := sumAt_le (lowerRows t)
    (f := fun i => if i = s then z s*(z s-1) else 0)
    (g := fun i => z i*(z i-1)) (by
      intro i _
      by_cases eq : i = s
      · subst i
        simp
      · simpa [eq] using binomial_nonnegative (z i))
  rw [sum_single hs, defect] at individual
  have zero := Int.le_antisymm individual (binomial_nonnegative (z s))
  rcases Int.mul_eq_zero.mp zero with eq | eq
  · exact Or.inl eq
  · exact Or.inr (show z s = 1 by omega)

def pairFirstColumn (t : Nat) (y : Family) (p q : Nat) : Column :=
  fun s => decide (pairFirstMatch t y p q s = 1)

private theorem pair_first_column_bits {t p q : Nat} {y : Family} (hy : Outer t y)
    (hp : p < lowerRows t) (hq : q < lowerRows t) (hne : p ≠ q)
    (near : outsideRowMeet t y p q = (t : Int)-1) (s : Nat) (hs : s < lowerRows t) :
    bit (pairFirstColumn t y p q s) = pairFirstMatch t y p q s := by
  rcases pair_first_match_binary hy hp hq hne near s hs with zero | one
  · simp [pairFirstColumn, zero, bit]
  · simp [pairFirstColumn, one, bit]

/-- A near-twin pair gives a compatible first column, including the capacity bounds. -/
theorem first_prefix_of_near_twin {t p q : Nat} {y : Family} (ht : 2 ≤ t) (hy : Outer t y)
    (hp : p < lowerRows t) (hq : q < lowerRows t) (hne : p ≠ q)
    (near : outsideRowMeet t y p q = (t : Int)-1) : Prefix t 1 := by
  let c := pairFirstColumn t y p q
  have bits := pair_first_column_bits hy hp hq hne near
  have counts := pair_first_match_counts hy hp hq
  have size : weight (lowerRows t) c = 2*(t : Int)-2 := by
    unfold weight
    rw [sumAt_congr _ bits, counts.2]
  refine ⟨y, fun _ => c, hy, ⟨fun _ _ => size, fun _ _ _ h => by omega⟩,
    ?_, capacity_small_width (by omega)⟩
  intro _ _ j hj
  unfold meet
  rw [sumAt_congr _ (fun s hs => by rw [← bit_mul, bits s hs])]
  exact counts.1 j hj

/-- The signed column Z(c) = (YYᵀ − tI)c − (t − 1)·1. -/
def firstMatchFromCoefficients (t : Nat) (y : Family) (c : Nat → Int) (s : Nat) : Int :=
  sumAt (lowerRows t) (fun p => c p * firstMatchCentered t y p s) - ((t : Int)-1)

private theorem coefficient_dot {t : Nat} {y : Family} (c x : Nat → Int) :
    sumAt (lowerRows t) (fun s => firstMatchFromCoefficients t y c s * x s) =
      sumAt (lowerRows t) (fun p => c p *
        sumAt (lowerRows t) (fun s => firstMatchCentered t y p s * x s)) -
          ((t : Int)-1)*sumAt (lowerRows t) x := by
  unfold firstMatchFromCoefficients
  simp only [Int.sub_mul, sum_sub]
  have expand (s : Nat) :
      sumAt (lowerRows t) (fun p => c p * firstMatchCentered t y p s)*x s =
        sumAt (lowerRows t) (fun p => c p * (firstMatchCentered t y p s * x s)) := by
    rw [sum_mul]
    apply sumAt_congr
    intro p _
    ac_rfl
  rw [sumAt_congr _ (fun s _ => expand s), swap_sums]
  congr 1
  · apply sumAt_congr
    intro p _
    rw [mul_sum]
  · rw [mul_sum]
    simp only [Int.one_mul]

theorem first_match_from_coefficients_counts {t : Nat} {y : Family} (ht : 0 < t)
    (hy : Outer t y) (c : Nat → Int) (total : sumAt (lowerRows t) c = 2) :
    (∀ i, i < 2*t → countOn (lowerRows t) (y i) (firstMatchFromCoefficients t y c) = (t : Int)-1) ∧
    sumAt (lowerRows t) (firstMatchFromCoefficients t y c) = 2*(t : Int)-2 := by
  have counts (i : Nat) (hi : i < 2*t) :
      countOn (lowerRows t) (y i) (firstMatchFromCoefficients t y c) = (t : Int)-1 := by
    unfold countOn
    rw [sumAt_congr _ (fun s _ => Int.mul_comm _ _), coefficient_dot]
    have contracted (p : Nat) (hp : p < lowerRows t) :
        sumAt (lowerRows t) (fun s => firstMatchCentered t y p s*bit (y i s)) =
          (t : Int)*((t : Int)-1) := by
      rw [sumAt_congr _ (fun s _ => Int.mul_comm _ _)]
      exact first_match_centered_count hy hp hi
    rw [sumAt_congr _ (fun p hp => by rw [contracted p hp]), ← sum_mul, total]
    change 2*((t : Int)*((t : Int)-1)) - ((t : Int)-1)*weight (lowerRows t) (y i) = _
    rw [hy.colSize i hi]
    grind
  exact ⟨counts, first_count_forces_size ht hy _ counts⟩

theorem first_match_from_coefficients_dot {t : Nat} {y : Family} (hy : Outer t y)
    (c x : Nat → Int) (total : sumAt (lowerRows t) c = 2)
    (counts : ∀ i, i < 2*t → countOn (lowerRows t) (y i) x = (t : Int)-1)
    (size : sumAt (lowerRows t) x = 2*(t : Int)-2) :
    sumAt (lowerRows t) (fun s => firstMatchFromCoefficients t y c s * x s) =
      2*(t : Int)-2 - (t : Int)*sumAt (lowerRows t) (fun s => c s*x s) := by
  rw [coefficient_dot]
  have term (p : Nat) (hp : p < lowerRows t) :
      c p*sumAt (lowerRows t) (fun s => firstMatchCentered t y p s*x s) =
        c p*((t : Int)*((t : Int)-1)) - (t : Int)*(c p*x p) := by
    rw [centered_dot_first_count hy hp x counts, Int.mul_sub]
    ac_rfl
  rw [sumAt_congr _ term, sum_sub, ← sum_mul, ← mul_sum, total, size]
  grind

private theorem meet_lt_at_row {m s : Nat} {a b : Column} (hs : s < m)
    (ha : a s = true) (hb : b s = false) : meet m a b < weight m a := by
  have smaller := sumAt_le m
    (f := fun i => bit (a i && b i) + (if i = s then 1 else 0))
    (g := fun i => bit (a i)) (by
      intro i _
      by_cases eq : i = s
      · subst i
        simp [ha, hb, bit]
      · cases a i <;> cases b i <;> simp [eq, bit])
  rw [sumAt_add, sum_single hs] at smaller
  change meet m a b + 1 ≤ weight m a at smaller
  omega

/-- Any Boolean Z(c) with integer coefficients summing to two is adjacent to every
other legal first column of the same outside design. Inequality is on a valid row. -/
theorem first_match_from_coefficients_universal {t : Nat} {y : Family} (ht : 2 ≤ t)
    (hy : Outer t y) (c : Nat → Int) (total : sumAt (lowerRows t) c = 2)
    (z x : Column) (hz : ∀ s, s < lowerRows t → bit (z s) = firstMatchFromCoefficients t y c s)
    (xCounts : ∀ i, i < 2*t → meet (lowerRows t) (y i) x = (t : Int)-1)
    (xSize : weight (lowerRows t) x = 2*(t : Int)-2)
    (different : ∃ s, s < lowerRows t ∧ z s ≠ x s) :
    meet (lowerRows t) z x = (t : Int)-2 := by
  have zSize : weight (lowerRows t) z = 2*(t : Int)-2 := by
    unfold weight
    rw [sumAt_congr _ hz, (first_match_from_coefficients_counts (by omega) hy c total).2]
  have xCounts' (i : Nat) (hi : i < 2*t) :
      countOn (lowerRows t) (y i) (fun s => bit (x s)) = (t : Int)-1 := by
    unfold countOn
    rw [sumAt_congr _ (fun s _ => bit_mul _ _)]
    exact xCounts i hi
  have dot := first_match_from_coefficients_dot hy c (fun s => bit (x s)) total xCounts' xSize
  have asBits (s : Nat) (hs : s < lowerRows t) :
      firstMatchFromCoefficients t y c s*bit (x s) = bit (z s && x s) := by
    rw [← hz s hs, bit_mul]
  rw [sumAt_congr _ asBits] at dot
  let d := sumAt (lowerRows t) (fun s => c s*bit (x s))
  change meet (lowerRows t) z x = 2*(t : Int)-2 - (t : Int)*d at dot
  have nonnegative : 0 ≤ meet (lowerRows t) z x := by
    have bound := sumAt_le (lowerRows t) (f := fun _ => 0) (g := fun s => bit (z s && x s))
      (fun s _ => by cases z s <;> cases x s <;> decide)
    rw [sum_zero] at bound
    exact bound
  have less : meet (lowerRows t) z x < 2*(t : Int)-2 := by
    obtain ⟨s, hs, ne⟩ := different
    cases zBit : z s <;> cases xBit : x s
    · simp [zBit, xBit] at ne
    · rw [meet_comm, ← xSize]
      exact meet_lt_at_row hs xBit zBit
    · rw [← zSize]
      exact meet_lt_at_row hs zBit xBit
    · simp [zBit, xBit] at ne
  have positive : 0 < d := by
    by_cases h : 0 < d
    · exact h
    · have bound := Int.mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ (t : Int) by omega) (show d ≤ 0 by omega)
      omega
  have belowTwo : d < 2 := by
    by_cases h : d < 2
    · exact h
    · have bound := Int.mul_le_mul_of_nonneg_left (show 2 ≤ d by omega) (show 0 ≤ (t : Int) by omega)
      omega
  have one : d = 1 := by omega
  rw [one, Int.mul_one] at dot
  omega

/-- The near-twin column has exact intersection t−2 with every distinct legal first column. -/
theorem near_twin_universal {t p q : Nat} {y : Family} (ht : 2 ≤ t) (hy : Outer t y)
    (hp : p < lowerRows t) (hq : q < lowerRows t) (hne : p ≠ q)
    (near : outsideRowMeet t y p q = (t : Int)-1) (x : Column)
    (xCounts : ∀ i, i < 2*t → meet (lowerRows t) (y i) x = (t : Int)-1)
    (xSize : weight (lowerRows t) x = 2*(t : Int)-2)
    (different : ∃ s, s < lowerRows t ∧ pairFirstColumn t y p q s ≠ x s) :
    meet (lowerRows t) (pairFirstColumn t y p q) x = (t : Int)-2 := by
  let c (r : Nat) : Int := (if r = p then 1 else 0) + (if r = q then 1 else 0)
  have total : sumAt (lowerRows t) c = 2 := by
    dsimp only [c]
    rw [sumAt_add, sum_single hp, sum_single hq]
    decide
  apply first_match_from_coefficients_universal ht hy c total _ _ _ xCounts xSize different
  intro s hs
  rw [pair_first_column_bits hy hp hq hne near s hs]
  unfold pairFirstMatch firstMatchFromCoefficients
  have term (r : Nat) :
      c r * firstMatchCentered t y r s =
        (if r = p then firstMatchCentered t y p s else 0) +
        (if r = q then firstMatchCentered t y q s else 0) := by
    dsimp only [c]
    rw [Int.add_mul]
    congr 1
    · by_cases ep : r = p <;> simp [ep]
    · by_cases eq : r = q <;> simp [eq]
  rw [sumAt_congr _ (fun r _ => term r), sumAt_add, sum_single hp, sum_single hq]

#print axioms pair_first_match_counts
#print axioms pair_first_match_defect
#print axioms outside_distinct_rows_overlap_le
#print axioms pair_first_match_binary
#print axioms first_prefix_of_near_twin
#print axioms first_match_from_coefficients_counts
#print axioms first_match_from_coefficients_dot
#print axioms first_match_from_coefficients_universal
#print axioms near_twin_universal

end HadamardAllOrders
