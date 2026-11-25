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

def rowOverlap (t : Nat) (y : Family) (r s : Nat) : Int :=
    meet (2*t) (fun j => y j r) (fun j => y j s)

private def outsideOverlap (t : Nat) (y : Family) (r s : Nat) : Int :=
    meet (2*t) (fun j => !(y j r)) (fun j => y j s)

private theorem overlap_split (n : Nat) (a b : Column) :
    meet n a b + meet n (fun j => !(a j)) b = weight n b := by
  unfold meet weight
  rw [← sumAt_add]
  apply sumAt_congr
  intro j _
  change bit (a j && b j) + bit (!(a j) && b j) = bit (b j)
  cases a j <;> cases b j <;> decide

private theorem row_cross_pairs {t : Nat} {y : Family} (hy : Outer t y)
    {r : Nat} (hr : r < lowerRows t) :
    sumAt (lowerRows t) (fun s => rowOverlap t y r s * outsideOverlap t y r s) =
    (t : Int) * ((t : Int) * ((t : Int)-1)) := by
  let count (i j : Nat) := bit (y i r) * bit (!(y j r))
  have expand (s : Nat) : rowOverlap t y r s * outsideOverlap t y r s =
      sumAt (2*t) (fun i => sumAt (2*t) (fun j => count i j * bit (y i s && y j s))) := by
    unfold rowOverlap outsideOverlap meet
    rw [sum_mul]
    apply sumAt_congr
    intro i _
    rw [mul_sum]
    apply sumAt_congr
    intro j _
    simp only [count, ← bit_mul]
    ac_rfl
  rw [sumAt_congr _ (fun s _ => expand s), swap_sums (lowerRows t) (2*t)]
  have fixed (i : Nat) (hi : i < 2*t) :
      sumAt (lowerRows t) (fun s => sumAt (2*t) (fun j => count i j * bit (y i s && y j s))) =
      sumAt (2*t) (fun j => count i j * ((t : Int)-1)) := by
    rw [swap_sums (lowerRows t) (2*t)]
    apply sumAt_congr
    intro j hj
    rw [← mul_sum]
    rcases Nat.lt_trichotomy i j with h | h | h
    · rw [show sumAt (lowerRows t) (fun s => bit (y i s && y j s)) = (t : Int)-1 from
          hy.common i j h hj]
    · subst j
      have zero : count i i = 0 := by
        dsimp [count]
        cases y i r <;> decide
      simp [zero]
    · rw [show sumAt (lowerRows t) (fun s => bit (y i s && y j s)) = (t : Int)-1 by
          change meet (lowerRows t) (y i) (y j) = _
          rw [meet_comm, hy.common j i h hi]]
  rw [sumAt_congr _ fixed]
  have first := hy.rowSize r hr
  have second := overlap_split (2*t) (fun j => y j r) ones
  rw [meet_comm _ _ ones, meet_comm _ (fun j => !(y j r)) ones,
      meet_ones, meet_ones, first, weight_ones] at second
  have secondWeight : weight (2*t) (fun j => !(y j r)) = t := by omega
  have weighted (i : Nat) :
      sumAt (2*t) (fun j => count i j * ((t : Int)-1)) = bit (y i r) * ((t : Int)*((t : Int)-1)) := by
    simp only [count, Int.mul_assoc, ← mul_sum, ← sum_mul]
    rw [← weight, secondWeight]
  rw [sumAt_congr _ (fun i _ => weighted i), ← sum_mul, ← weight, first]

/-- The imbalance of every block against a block and its complement gives this energy. -/
theorem row_overlap_energy {t : Nat} {y : Family} (ht : 1 ≤ t) (hy : Outer t y)
    {r : Nat} (hr : r < lowerRows t) :
    sumAt (lowerRows t) (fun s => (2*rowOverlap t y r s - t)*(2*rowOverlap t y r s - t)) =
    2*(t : Int)*(t : Int) := by
  have row (s : Nat) (hs : s < lowerRows t) :
      (2*rowOverlap t y r s - t)*(2*rowOverlap t y r s - t) =
      (t : Int)*(t : Int) + (-4)*(rowOverlap t y r s * outsideOverlap t y r s) := by
    have split : rowOverlap t y r s + outsideOverlap t y r s = (t : Int) :=
      (overlap_split (2*t) (fun j => y j r) (fun j => y j s)).trans (hy.rowSize s hs)
    rw [← split]
    grind
  rw [sumAt_congr _ row, sumAt_add, sum_const, ← mul_sum, row_cross_pairs hy hr]
  have size : (lowerRows t : Int) = 4*(t : Int)-2 := by unfold lowerRows; omega
  rw [size]
  grind

private theorem row_overlap_self {t : Nat} {y : Family} (hy : Outer t y)
    {r : Nat} (hr : r < lowerRows t) : rowOverlap t y r r = t := by
  have self : meet (2*t) (fun j => y j r) (fun j => y j r) = weight (2*t) (fun j => y j r) := by
    unfold meet weight
    simp
  exact self.trans (hy.rowSize r hr)

private theorem odd_imbalance_square_pos {t : Nat} (ho : t%2=1) (a : Int) :
    1 ≤ (2*a-t)*(2*a-t) := by
  have hn : (2*a-(t : Int)) ≠ 0 := by omega
  by_cases hp : 0 < 2*a-(t : Int)
  · exact Int.mul_pos hp hp
  · exact Int.mul_pos_of_neg_of_neg (by omega) (by omega)

/-- A near-equal or near-complementary block exhausts a row's excess square energy.
Every other distinct block meets it in one of the two middle sizes. -/
theorem near_row_rigidity {t : Nat} {y : Family} (ht : 3 ≤ t) (ho : t%2=1) (hy : Outer t y)
    {r s u : Nat} (hr : r < lowerRows t) (hs : s < lowerRows t) (hu : u < lowerRows t)
    (hrs : r ≠ s) (hru : r ≠ u) (hsu : s ≠ u)
    (near : rowOverlap t y r s = 1 ∨ rowOverlap t y r s = (t : Int)-1) :
    2*rowOverlap t y r u = (t : Int)-1 ∨ 2*rowOverlap t y r u = (t : Int)+1 := by
  let square (i : Nat) := (2*rowOverlap t y r i - (t : Int))*(2*rowOverlap t y r i - (t : Int))
  let atRow (j : Nat) (v : Int) (i : Nat) := if i = j then v else 0
  let tt := (t : Int)*(t : Int)
  let nearSquare := ((t : Int)-2)*((t : Int)-2)
  have self : square r = tt := by
    dsimp [square, tt]
    rw [row_overlap_self hy hr]
    grind
  have nearValue : square s = nearSquare := by
    rcases near with h | h <;> simp only [square, nearSquare, h] <;> grind
  have bound := sumAt_le (lowerRows t)
    (f := fun i => 1 + atRow r (tt-1) i + atRow s (nearSquare-1) i + atRow u (square u-1) i)
    (g := square) (by
      intro i _
      by_cases h : i = r
      · subst i
        simp [atRow, hrs, hru, self] <;> omega
      by_cases h' : i = s
      · subst i
        simp [atRow, h, hsu, nearValue] <;> omega
      by_cases h'' : i = u
      · subst i
        simp [atRow, h, h'] <;> omega
      simpa [atRow, h, h', h'', square] using odd_imbalance_square_pos ho (rowOverlap t y r i))
  change _ ≤ sumAt (lowerRows t) square at bound
  have total : sumAt (lowerRows t) square = 2*(t : Int)*(t : Int) :=
    row_overlap_energy (by omega) hy hr
  simp only [atRow, sumAt_add, sum_single hr, sum_single hs, sum_single hu, sum_const, total] at bound
  have size : (lowerRows t : Int) = 4*(t : Int)-2 := by unfold lowerRows; omega
  rw [size] at bound
  have sqSmall : square u ≤ 1 := by
    dsimp [tt, nearSquare] at bound
    grind
  let d := 2*rowOverlap t y r u - (t : Int)
  change d*d ≤ 1 at sqSmall
  have dBounds : -1 ≤ d ∧ d ≤ 1 := by
    constructor
    · by_cases h : -1 ≤ d
      · exact h
      have hmul := Int.mul_le_mul_of_nonneg_right (show 2 ≤ -d by omega) (show 0 ≤ -d by omega)
      simp only [Int.neg_mul_neg] at hmul
      omega
    · by_cases h : d ≤ 1
      · exact h
      have hmul := Int.mul_le_mul_of_nonneg_right (show 2 ≤ d by omega) (show 0 ≤ d by omega)
      omega
  dsimp [d] at dBounds
  omega

/-- At odd t ≥ 5, a block has at most one distinct near-equal or near-complementary neighbour. -/
theorem near_row_unique {t : Nat} {y : Family} (ht : 5 ≤ t) (ho : t%2=1) (hy : Outer t y)
    {r s u : Nat} (hr : r < lowerRows t) (hs : s < lowerRows t) (hu : u < lowerRows t)
    (hrs : r ≠ s) (hru : r ≠ u)
    (nearS : rowOverlap t y r s = 1 ∨ rowOverlap t y r s = (t : Int)-1)
    (nearU : rowOverlap t y r u = 1 ∨ rowOverlap t y r u = (t : Int)-1) : s = u := by
  by_cases hsu : s = u
  · exact hsu
  have middle := near_row_rigidity (by omega) ho hy hr hs hu hrs hru hsu nearS
  omega

/-- The total excess over the minimum square of one is `(t-1)*(t-3)` off the diagonal.
Any selected off-diagonal blocks with square at least `minimum` consume that budget. -/
theorem row_deviation_cap {t : Nat} {y : Family} (ht : 1 ≤ t) (ho : t%2=1) (hy : Outer t y)
    {r : Nat} (hr : r < lowerRows t) (minimum : Int) :
    let square i := (2*rowOverlap t y r i - (t : Int))*(2*rowOverlap t y r i - (t : Int))
    let count := sumAt (lowerRows t) (fun i => if i ≠ r ∧ minimum ≤ square i then 1 else 0)
    (minimum-1)*count ≤ ((t : Int)-1)*((t : Int)-3) := by
  dsimp only
  let square (i : Nat) := (2*rowOverlap t y r i - (t : Int))*(2*rowOverlap t y r i - (t : Int))
  change (minimum-1)*sumAt (lowerRows t) (fun i => if i ≠ r ∧ minimum ≤ square i then 1 else 0) ≤ _
  let removeSelf (i : Nat) := if i = r then 1-(t : Int)*(t : Int) else 0
  rw [mul_sum]
  calc
    _ ≤ sumAt (lowerRows t) (fun i => square i + (-1) + removeSelf i) := by
      apply sumAt_le
      intro i _
      by_cases h : i = r
      · subst i
        have self := row_overlap_self hy hr
        simp only [ne_eq, not_true_eq_false, false_and, ite_false, Int.mul_zero, removeSelf,
          ite_true, square, self]
        grind
      by_cases selected : minimum ≤ square i
      · rw [ite_eq_left ⟨h, selected⟩]
        simp [removeSelf, h]
        omega
      · have lower := odd_imbalance_square_pos ho (rowOverlap t y r i)
        change 1 ≤ square i at lower
        rw [ite_eq_right (fun h => selected h.2)]
        simp [removeSelf, h]
        omega
    _ = _ := by
      have size : (lowerRows t : Int) = 4*(t : Int)-2 := by unfold lowerRows; omega
      have total : sumAt (lowerRows t) square = 2*(t : Int)*(t : Int) := row_overlap_energy ht hy hr
      simp only [sumAt_add, sum_const, removeSelf, sum_single hr, total, size]
      grind

#print axioms near_row_rigidity
#print axioms near_row_unique
#print axioms row_deviation_cap

end HadamardAllOrders
