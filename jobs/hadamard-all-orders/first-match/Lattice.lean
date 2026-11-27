import Rounding

namespace HadamardAllOrders

open Hadamard2396 (sumAt sumAt_add sumAt_congr)

private def rowMoment (t : Nat) (y : Family) (r s : Nat) : Int :=
  sumAt (2*t) (fun j => bit (y j r) * bit (y j s))

/-- The lower-row vector Y(Yᵀeᵣ) − t eᵣ. -/
def firstMatchCentered (t : Nat) (y : Family) (r s : Nat) : Int :=
  rowMoment t y r s - if s = r then (t : Int) else 0

private theorem outer_meet {t i j : Nat} {y : Family} (hy : Outer t y)
    (hi : i < 2*t) (hj : j < 2*t) :
    meet (lowerRows t) (y i) (y j) = (t : Int)-1 + (if j = i then (t : Int) else 0) := by
  by_cases eq : j = i
  · subst j
    rw [meet_self, hy.colSize i hi]
    simp
    omega
  · simp only [ite_eq_right eq, Int.add_zero]
    by_cases before : i < j
    · exact hy.common i j before hj
    · rw [meet_comm]
      exact hy.common j i (by omega) hi

private theorem row_moment_count {t r i : Nat} {y : Family} (hy : Outer t y)
    (hr : r < lowerRows t) (hi : i < 2*t) :
    countOn (lowerRows t) (y i) (rowMoment t y r) =
      (t : Int)*((t : Int)-1) + (t : Int)*bit (y i r) := by
  unfold countOn rowMoment
  rw [sumAt_congr _ (fun s _ => mul_sum (bit (y i s)) _ _), swap_sums]
  have exchange (j : Nat) :
      sumAt (lowerRows t) (fun s => bit (y i s)*(bit (y j r)*bit (y j s))) =
        bit (y j r)*meet (lowerRows t) (y i) (y j) := by
    unfold meet
    rw [mul_sum]
    apply sumAt_congr
    intro s _
    rw [← bit_mul]
    ac_rfl
  rw [sumAt_congr _ (fun j _ => exchange j)]
  have term (j : Nat) (hj : j < 2*t) :
      bit (y j r)*meet (lowerRows t) (y i) (y j) =
        bit (y j r)*((t : Int)-1) + (if j = i then (t : Int)*bit (y i r) else 0) := by
    rw [outer_meet hy hi hj, Int.mul_add]
    by_cases same : j = i
    · subst j
      simp [Int.mul_comm]
    · simp [same]
  rw [sumAt_congr _ term, sumAt_add, ← sum_mul, sum_single hi]
  change weight (2*t) (fun j => y j r)*((t : Int)-1) + _ = _
  rw [hy.rowSize r hr]

theorem first_match_centered_count {t r i : Nat} {y : Family} (hy : Outer t y)
    (hr : r < lowerRows t) (hi : i < 2*t) :
    countOn (lowerRows t) (y i) (firstMatchCentered t y r) = (t : Int)*((t : Int)-1) := by
  unfold firstMatchCentered countOn
  rw [sumAt_congr _ (fun s _ => Int.mul_sub (bit (y i s)) _ _), sum_sub]
  change countOn (lowerRows t) (y i) (rowMoment t y r) -
    sumAt (lowerRows t) (fun s => bit (y i s)*(if s = r then (t : Int) else 0)) = _
  have single (s : Nat) :
      bit (y i s)*(if s = r then (t : Int) else 0) =
        if s = r then (t : Int)*bit (y i r) else 0 := by
    by_cases same : s = r
    · subst s
      simp [Int.mul_comm]
    · simp [same]
  rw [row_moment_count hy hr hi, sumAt_congr _ (fun s _ => single s), sum_single hr]
  omega

private theorem affine_count (m : Nat) (c : Column) (g : Nat → Int) (a b : Int) :
    countOn m c (fun s => a*g s+b) = a*countOn m c g + b*weight m c := by
  unfold countOn weight
  have factor (s : Nat) : bit (c s)*(a*g s+b) = a*(bit (c s)*g s) + b*bit (c s) := by
    rw [Int.mul_add]
    ac_rfl
  rw [sumAt_congr _ (fun s _ => factor s), sumAt_add, ← mul_sum, ← mul_sum]

private theorem sum_point_counts {t : Nat} {y : Family} (hy : Outer t y) (g : Nat → Int) :
    sumAt (2*t) (fun j => countOn (lowerRows t) (y j) g) =
      (t : Int)*sumAt (lowerRows t) g := by
  unfold countOn
  rw [swap_sums, mul_sum]
  apply sumAt_congr
  intro s hs
  rw [← sum_mul]
  change weight (2*t) (fun j => y j s)*g s = _
  rw [hy.rowSize s hs]

theorem first_count_forces_size {t : Nat} {y : Family} (ht : 0 < t) (hy : Outer t y)
    (g : Nat → Int) (counts : ∀ i, i < 2*t → countOn (lowerRows t) (y i) g = (t : Int)-1) :
    sumAt (lowerRows t) g = 2*(t : Int)-2 := by
  have total := sum_point_counts hy g
  rw [sumAt_congr _ counts, sum_const, Int.natCast_mul] at total
  have prod : (t : Int)*(2*(t : Int)-2) = (t : Int)*sumAt (lowerRows t) g :=
    calc
      _ = (2*(t : Int))*((t : Int)-1) := by grind
      _ = _ := total
  exact (Int.eq_of_mul_eq_mul_left (by omega : (t : Int) ≠ 0) prod).symm

/-- An explicit signed-integer solution to the first column's size and mixed counts. -/
def firstMatchInteger (t : Nat) (y : Family) (r s : Nat) : Int :=
  2*firstMatchCentered t y r s + (1-(t : Int))

theorem first_match_integer {t r : Nat} {y : Family} (hy : Outer t y) (hr : r < lowerRows t) :
    (∀ i, i < 2*t → countOn (lowerRows t) (y i) (firstMatchInteger t y r) = (t : Int)-1) ∧
    sumAt (lowerRows t) (firstMatchInteger t y r) = 2*(t : Int)-2 := by
  have counts (i : Nat) (hi : i < 2*t) :
      countOn (lowerRows t) (y i) (firstMatchInteger t y r) = (t : Int)-1 := by
    change countOn (lowerRows t) (y i) (fun s => 2*firstMatchCentered t y r s + (1-(t : Int))) = _
    rw [affine_count, first_match_centered_count hy hr hi, hy.colSize i hi]
    grind
  have ht : 0 < t := by unfold lowerRows at hr; omega
  exact ⟨counts, first_count_forces_size ht hy _ counts⟩

/-- An explicit signed-integer vector with unit point counts on any represented outer design. -/
def firstMatchUnit (t : Nat) (y : Family) (r s : Nat) : Int :=
  (-4)*firstMatchCentered t y r s + (2*(t : Int)-1)

theorem first_match_unit {t r : Nat} {y : Family} (hy : Outer t y) (hr : r < lowerRows t)
    (i : Nat) (hi : i < 2*t) :
    countOn (lowerRows t) (y i) (firstMatchUnit t y r) = 1 := by
  change countOn (lowerRows t) (y i) (fun s => (-4)*firstMatchCentered t y r s + (2*(t : Int)-1)) = _
  rw [affine_count, first_match_centered_count hy hr hi, hy.colSize i hi]
  grind

#print axioms first_match_integer
#print axioms first_match_unit

end HadamardAllOrders
