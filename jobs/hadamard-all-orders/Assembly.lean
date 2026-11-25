import Triples

/-! Sign columns are encoded by their positive entries. Only the finite prefix of a
column or family specified by the dimension is used. All orders are variables. -/
namespace HadamardAllOrders

open Hadamard2396 (sumAt sumAt_succ sumAt_split sumAt_congr)

abbrev Column := Nat → Bool
abbrev Family := Nat → Column

def bit (b : Bool) : Int := if b then 1 else 0
def weight (n : Nat) (a : Column) := sumAt n fun i => bit (a i)
def meet (n : Nat) (a b : Column) := sumAt n fun i => bit (a i && b i)
def dot (n : Nat) (a b : Column) := sumAt n fun i => if a i = b i then (1 : Int) else -1

def HasColumns (n k : Nat) : Prop :=
  ∃ c : Family, ∀ i j, i < j → j < k → dot n (c i) (c j) = 0

def Had (n : Nat) : Prop := HasColumns n n

theorem gram (n : Nat) (a b : Column) :
    dot n a b = (n : Int) - 2 * (weight n a + weight n b) + 4 * meet n a b := by
  induction n with
  | zero => simp [dot, weight, meet, sumAt]
  | succ n ih =>
    simp only [dot, weight, meet, sumAt_succ, Int.natCast_succ] at *
    cases a n <;> cases b n <;> simp [bit] at * <;> omega

def ones : Column := fun _ => true

theorem weight_ones (n : Nat) : weight n ones = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [weight, sumAt_succ, ones, bit, ite_true, Int.natCast_succ] at *
    omega

theorem meet_ones (n : Nat) (a : Column) : meet n ones a = weight n a := by
  unfold meet weight
  apply sumAt_congr
  intro i _
  simp [ones]

theorem meet_comm (n : Nat) (a b : Column) : meet n a b = meet n b a := by
  unfold meet
  apply sumAt_congr
  intro i _
  rw [Bool.and_comm]

def lowerRows (t : Nat) := 4*t-2
def target (t : Nat) := 2*t-8

structure Outer (t : Nat) (y : Family) : Prop where
  rowSize : ∀ r, r < lowerRows t → weight (2*t) (fun j => y j r) = t
  colSize : ∀ j, j < 2*t → weight (lowerRows t) (y j) = 2*(t : Int)-1
  common : ∀ i j, i < j → j < 2*t → meet (lowerRows t) (y i) (y j) = (t : Int)-1

structure Inner (t k : Nat) (x : Family) : Prop where
  colSize : ∀ j, j < k → weight (lowerRows t) (x j) = 2*(t : Int)-2
  common : ∀ i j, i < j → j < k → meet (lowerRows t) (x i) (x j) = (t : Int)-2

def Mixed (t q : Nat) (y x : Family) : Prop := ∀ i, i < q →
  ∀ j, j < 2*t → meet (lowerRows t) (y j) (x i) = (t : Int)-1

def border (flag : Bool) (c : Column) : Column
  | 0 => true
  | 1 => flag
  | r+2 => c r

theorem weight_border (m : Nat) (f : Bool) (c : Column) :
    weight (m+2) (border f c) = 1 + bit f + weight m c := by
  unfold weight
  rw [Nat.add_comm m 2, sumAt_split]
  simp [sumAt, List.range_succ, border, Nat.add_comm 2, bit, Int.add_comm] <;> rfl

theorem meet_border (m : Nat) (f g : Bool) (c d : Column) :
    meet (m+2) (border f c) (border g d) = 1 + bit (f && g) + meet m c d := by
  unfold meet
  rw [Nat.add_comm m 2, sumAt_split]
  simp [sumAt, List.range_succ, border, Nat.add_comm 2, bit, Int.add_comm] <;> rfl

def nonconstant (t : Nat) (y x : Family) (j : Nat) : Column :=
  if j < 2*t then border false (y j) else border true (x (j-2*t))

theorem balanced {t k : Nat} {y x : Family} (ht : 1 ≤ t)
    (hy : Outer t y) (hx : Inner t k x) (j : Nat) (hj : j < 2*t+k) :
    weight (4*t) (nonconstant t y x j) = 2*(t : Int) := by
  have hn : 4*t = lowerRows t + 2 := by unfold lowerRows; omega
  unfold nonconstant
  split
  next h =>
    rw [hn, weight_border, hy.colSize j h]
    simp [bit]
    omega
  next h =>
    rw [hn, weight_border, hx.colSize (j-2*t) (by omega)]
    simp [bit]
    omega

theorem pair_count {t k : Nat} {y x : Family} (ht : 1 ≤ t)
    (hy : Outer t y) (hx : Inner t k x) (hm : Mixed t k y x)
    (i j : Nat) (hij : i < j) (hj : j < 2*t+k) :
    meet (4*t) (nonconstant t y x i) (nonconstant t y x j) = t := by
  have hn : 4*t = lowerRows t + 2 := by unfold lowerRows; omega
  by_cases hi : i < 2*t <;> by_cases hj' : j < 2*t
  · simp only [nonconstant, ite_eq_left hi, ite_eq_left hj', hn, meet_border]
    rw [hy.common i j hij hj']
    simp [bit]
    omega
  · simp only [nonconstant, ite_eq_left hi, ite_eq_right hj', hn, meet_border]
    rw [hm (j-2*t) (by omega) i hi]
    simp [bit]
    omega
  · omega
  · simp only [nonconstant, ite_eq_right hi, ite_eq_right hj', hn, meet_border]
    rw [hx.common (i-2*t) (j-2*t) (by omega) (by omega)]
    simp [bit]
    omega

def joined (t : Nat) (y x : Family) : Family
  | 0 => ones
  | j+1 => nonconstant t y x j

/-- Sufficient at every width, with no group or symmetry on the rows or columns. -/
theorem assemble {t k : Nat} {y x : Family} (ht : 1 ≤ t) (hy : Outer t y)
    (hx : Inner t k x) (hm : Mixed t k y x) : HasColumns (4*t) (1+2*t+k) := by
  refine ⟨joined t y x, ?_⟩
  intro i j hij hj
  cases j with
  | zero => omega
  | succ j =>
    have hj' : j < 2*t+k := by omega
    cases i with
    | zero =>
      change dot (4*t) ones (nonconstant t y x j) = 0
      rw [gram, weight_ones, meet_ones, balanced ht hy hx j hj']
      omega
    | succ i =>
      change dot (4*t) (nonconstant t y x i) (nonconstant t y x j) = 0
      have hij' : i < j := by omega
      rw [gram, balanced ht hy hx i (by omega), balanced ht hy hx j hj',
        pair_count ht hy hx hm i j hij' hj']
      omega

/-- The published last-seven theorem is passed as an explicit hypothesis. -/
theorem finish {t : Nat} {y x : Family} (ht : 5 ≤ t) (hy : Outer t y)
    (hx : Inner t (target t) x) (hm : Mixed t (target t) y x)
    (lastSeven : HasColumns (4*t) (4*t-7) → Had (4*t)) : Had (4*t) := by
  apply lastSeven
  have size : 1+2*t+target t = 4*t-7 := by unfold target; omega
  rw [← size]
  exact assemble (by omega) hy hx hm

/-- The full-width version needs no external completion theorem. -/
theorem finish_full {t : Nat} {y x : Family} (ht : 1 ≤ t) (hy : Outer t y)
    (hx : Inner t (2*t-1) x) (hm : Mixed t (2*t-1) y x) : Had (4*t) := by
  have size : 1+2*t+(2*t-1) = 4*t := by omega
  simpa only [Had, size] using assemble ht hy hx hm

end HadamardAllOrders
