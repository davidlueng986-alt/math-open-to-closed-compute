import Assembly

namespace HadamardAllOrders

open Hadamard2396 (sumAt sumAt_succ sumAt_split sumAt_congr sumAt_add)

def OuterExists (t : Nat) := ∃ y, Outer t y
def InnerExists (t k : Nat) := ∃ x, Inner t k x
def CompatibleThrough (t q : Nat) :=
  ∃ y x, Outer t y ∧ Inner t (target t) x ∧ Mixed t q y x

theorem climb {P : Nat → Prop} {a b : Nat} (hab : a ≤ b) (start : P a)
    (step : ∀ j, a ≤ j → j < b → P j → P (j+1)) : P b := by
  have reach (d : Nat) (hd : a+d ≤ b) : P (a+d) := by
    induction d with
    | zero => exact start
    | succ d ih => exact step (a+d) (by omega) (by omega) (ih (by omega))
  exact (show a+(b-a) = b by omega) ▸ reach (b-a) (by omega)

theorem mixed_zero {t : Nat} (hy : OuterExists t) (hx : InnerExists t (target t)) :
    CompatibleThrough t 0 := by
  obtain ⟨y, hy⟩ := hy
  obtain ⟨x, hx⟩ := hx
  exact ⟨y, x, hy, hx, fun _ h => by omega⟩

theorem solve_order {t : Nat} (ht : 5 ≤ t)
    (outer : OuterExists t)
    (seed : OuterExists t → InnerExists t (min t (target t)))
    (grow : ∀ k, min t (target t) ≤ k → k < target t →
      InnerExists t k → InnerExists t (k+1))
    (couple : ∀ k, k < target t → CompatibleThrough t k → CompatibleThrough t (k+1))
    (lastSeven : HasColumns (4*t) (4*t-7) → Had (4*t)) : Had (4*t) := by
  have fullInner := climb (Nat.min_le_right t (target t)) (seed outer) grow
  have fully := climb (Nat.zero_le (target t)) (mixed_zero outer fullInner)
    (fun k _ hk prev => couple k hk prev)
  obtain ⟨y, x, hy, hx, hm⟩ := fully
  exact finish ht hy hx hm lastSeven

/-- Remove all powers of two from the multiplier. -/
theorem all_of_odd (oddOrders : ∀ t, t%2 = 1 → Had (4*t))
    (doubling : ∀ n, Had n → Had (2*n)) (t : Nat) (ht : 0 < t) : Had (4*t) := by
  induction t using Nat.strongRecOn with
  | ind t ih =>
    by_cases ho : t%2 = 1
    · exact oddOrders t ho
    · have hh := ih (t/2) (by omega) (by omega)
      have hn : 4*t = 2*(4*(t/2)) := by omega
      rw [hn]
      exact doubling _ hh

/-- 'Covered' is the chosen collection of odd multipliers already settled, e.g. by Paley. -/
theorem all_orders (Covered : Nat → Prop)
    (covered : ∀ t, t%2 = 1 → Covered t → Had (4*t))
    (small : ∀ t, t%2 = 1 → t < 5 → Covered t)
    (outer : ∀ t, t%2 = 1 → 5 ≤ t → ¬ Covered t → OuterExists t)
    (seed : ∀ t, 5 ≤ t → OuterExists t → InnerExists t (min t (target t)))
    (grow : ∀ t, t%2 = 1 → 5 ≤ t → ¬ Covered t → ∀ k, min t (target t) ≤ k →
      k < target t → InnerExists t k → InnerExists t (k+1))
    (couple : ∀ t, t%2 = 1 → 5 ≤ t → ¬ Covered t → ∀ k, k < target t →
      CompatibleThrough t k → CompatibleThrough t (k+1))
    (lastSeven : ∀ t, 5 ≤ t → HasColumns (4*t) (4*t-7) → Had (4*t))
    (doubling : ∀ n, Had n → Had (2*n)) : ∀ t, 0 < t → Had (4*t) := by
  apply all_of_odd _ doubling
  intro t ho
  by_cases hc : Covered t
  · exact covered t ho hc
  · have ht : 5 ≤ t := Nat.le_of_not_gt (fun h => hc (small t ho h))
    exact solve_order ht (outer t ho ht hc) (seed t ht) (grow t ho ht hc)
      (couple t ho ht hc) (lastSeven t ht)

theorem sum_zero (n : Nat) : sumAt n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumAt_succ, ih]

/-- Clearing a common positive entry reduces each column size and pair intersection by one. -/
def erase (r : Nat) (a : Column) : Column := fun i => if i = r then false else a i

theorem weight_erase {n r : Nat} (a : Column) (hr : r < n) :
    weight n (erase r a) = weight n a - bit (a r) := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [weight, sumAt_succ] at *
    by_cases heq : n = r
    · subst r
      have same := sumAt_congr n (f := fun i => bit (erase n a i)) (g := fun i => bit (a i))
        (fun i hi => by simp [erase, Nat.ne_of_lt hi])
      rw [same]
      simp [erase, bit]
    · rw [ih (by omega)]
      simp [erase, heq]
      omega

theorem meet_erase {n r : Nat} (a b : Column) (hr : r < n) :
    meet n (erase r a) (erase r b) = meet n a b - bit (a r && b r) := by
  have same : meet n (erase r a) (erase r b) = weight n (erase r (fun i => a i && b i)) := by
    unfold weight meet
    apply sumAt_congr
    intro i _
    by_cases h : i = r <;> simp [erase, h]
  rw [same, weight_erase _ hr]
  rfl

/-- Choose increasing indices for the positive entries of a row. -/
def support (n : Nat) (a : Column) := (List.range n).filter fun i => a i

theorem support_weight (n : Nat) (a : Column) :
    ((support n a).length : Int) = weight n a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [support, weight, List.range_succ, List.filter_append, List.length_append,
      Int.natCast_add, sumAt_succ] at *
    rw [ih]
    cases h : a n <;> simp [h, bit]

/-- The seed only satisfies the X marginal. Its mixed counts can change. -/
theorem seed_from_outer {t : Nat} (ht : 5 ≤ t) (hy : OuterExists t) :
    InnerExists t (min t (target t)) := by
  obtain ⟨y, hy⟩ := hy
  have h0 : 0 < lowerRows t := by unfold lowerRows; omega
  let s := support (2*t) (fun j => y j 0)
  have hsize : s.length = t := by
    have h := support_weight (2*t) (fun j => y j 0)
    rw [hy.rowSize 0 h0] at h
    change (s.length : Int) = t at h
    omega
  let idx := fun (j : Nat) => s[j]?.getD 0
  have selected {j : Nat} (hj : j < min t (target t)) :
      idx j < 2*t ∧ y (idx j) 0 = true := by
    have hn : j < s.length := by omega
    have hm : idx j ∈ s := by
      simp [idx, List.getElem?_eq_getElem hn]
    simpa [s, support, List.mem_filter, List.mem_range] using hm
  have ordered {i j : Nat} (hij : i < j) (hj : j < min t (target t)) : idx i < idx j := by
    have hi : i < s.length := by omega
    have hj' : j < s.length := by omega
    have increasing : s.Pairwise (· < ·) := List.pairwise_lt_range.filter _
    simpa [idx, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj'] using
      (List.pairwise_iff_getElem.mp increasing i j hi hj' hij)
  refine ⟨fun j => erase 0 (y (idx j)), ?_, ?_⟩
  · intro j hj
    obtain ⟨hl, hp⟩ := selected hj
    rw [weight_erase _ h0, hy.colSize _ hl, hp]
    simp [bit]
    omega
  · intro i j hij hj
    obtain ⟨_, hp⟩ := selected (j := i) (by omega)
    obtain ⟨hl, hq⟩ := selected hj
    rw [meet_erase _ _ h0, hy.common _ _ (ordered hij hj) hl, hp, hq]
    simp [bit]
    omega

end HadamardAllOrders
