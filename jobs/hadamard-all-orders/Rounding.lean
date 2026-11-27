import OuterEnergy

namespace HadamardAllOrders

open Hadamard2396 (sumAt sumAt_succ sumAt_add sumAt_congr)

def slots (t : Nat) := 2*t-1
def load (x : Family) (j r : Nat) := weight j (fun i => x i r)
def need (t j : Nat) (x : Family) (r : Nat) := (t : Int)-1-load x j r
def countOn (m : Nat) (c : Column) (v : Nat → Int) := sumAt m (fun r => bit (c r) * v r)

def Capacity (t j : Nat) (x : Family) : Prop :=
  ∀ r, r < lowerRows t → 0 ≤ need t j x r ∧ need t j x r ≤ (slots t : Int)-(j : Int)

theorem load_bounds (x : Family) (r j : Nat) : 0 ≤ load x j r ∧ load x j r ≤ (j : Int) := by
  induction j with
  | zero => simp [load, weight, sumAt]
  | succ j ih =>
    have next : load x (j+1) r = load x j r + bit (x j r) := by
      simp only [load, weight, sumAt_succ]
    rw [next]
    cases x j r <;> simp [bit] <;> omega

/-- Before width t, every binary family meets the row capacities. -/
theorem capacity_small_width {t j : Nat} {x : Family} (hj : j < t) : Capacity t j x := by
  intro r hr
  have := load_bounds x r j
  unfold need slots
  omega

theorem sum_sub (n : Nat) (a b : Nat → Int) :
    sumAt n (fun i => a i - b i) = sumAt n a - sumAt n b := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumAt_succ, ih]; omega

theorem total_load (t j : Nat) (x : Family) (hx : Inner t j x) :
    sumAt (lowerRows t) (load x j) = (j : Int)*(2*(t : Int)-2) := by
  unfold load weight
  rw [swap_sums, ← sum_const]
  exact sumAt_congr _ hx.colSize

theorem load_on (m j : Nat) (c : Column) (x : Family) :
    countOn m c (load x j) = sumAt j (fun i => meet m c (x i)) := by
  unfold countOn load weight meet
  rw [sumAt_congr m (fun r _ => mul_sum (bit (c r)) j _), swap_sums]
  apply sumAt_congr
  intro i _
  apply sumAt_congr
  intro r _
  exact bit_mul _ _

theorem need_on (t j : Nat) (c : Column) (x : Family) :
    countOn (lowerRows t) c (need t j x) =
    weight (lowerRows t) c * ((t : Int)-1) - countOn (lowerRows t) c (load x j) := by
  unfold countOn need weight
  simp only [Int.mul_sub, sum_sub, sum_mul]

theorem meet_self (n : Nat) (c : Column) : meet n c c = weight n c := by
  simp [meet, weight]

theorem inner_load {t j i : Nat} {x : Family} (hx : Inner t j x) (hi : i < j) :
    countOn (lowerRows t) (x i) (load x j) = (j : Int)*((t : Int)-2) + (t : Int) := by
  rw [load_on]
  have pair {l : Nat} (hl : l < j) :
      meet (lowerRows t) (x i) (x l) = (t : Int)-2 + (if l = i then (t : Int) else 0) := by
    by_cases h : l = i
    · subst l
      rw [meet_self, hx.colSize i hi]
      simp
      omega
    · simp only [ite_eq_right h, Int.add_zero]
      by_cases before : i < l
      · exact hx.common i l before hl
      · rw [meet_comm]
        exact hx.common l i (by omega) hi
  rw [sumAt_congr j (fun _ h => pair h), sumAt_add, sum_const, sum_single hi]

/-- Integer numerators of one exact rational solution to every next-column constraint.
Divide by the positive number of remaining slots. Capacity keeps all entries in [0,1]. -/
theorem fractional_next {t j : Nat} {y x : Family} (ht : 1 ≤ t)
    (hy : Outer t y) (hx : Inner t j x) (mixed : Mixed t j y x) :
    sumAt (lowerRows t) (need t j x) = ((slots t : Int)-(j : Int))*(2*(t : Int)-2) ∧
    (∀ i, i < 2*t → countOn (lowerRows t) (y i) (need t j x) =
      ((slots t : Int)-(j : Int))*((t : Int)-1)) ∧
    (∀ i, i < j → countOn (lowerRows t) (x i) (need t j x) =
      ((slots t : Int)-(j : Int))*((t : Int)-2)) := by
  have m : (lowerRows t : Int) = 4*(t : Int)-2 := by unfold lowerRows; omega
  have b : (slots t : Int) = 2*(t : Int)-1 := by unfold slots; omega
  constructor
  · change sumAt (lowerRows t) (fun r => (t : Int)-1-load x j r) = _
    rw [sum_sub, sum_const, total_load t j x hx, m, b]
    grind
  constructor
  · intro i hi
    rw [need_on, hy.colSize i hi, load_on, sumAt_congr j (fun l hl => mixed l hl i hi), sum_const, b]
    grind
  · intro i hi
    rw [need_on, hx.colSize i hi, inner_load hx hi, b]
    grind

def Prefix (t j : Nat) := ∃ y x, Outer t y ∧ Inner t j x ∧ Mixed t j y x ∧ Capacity t j x

/-- Install a new column at index j, leaving every earlier column in place. -/
def appendNext (x : Family) (j : Nat) (z : Column) : Family :=
  fun i => if i = j then z else x i

theorem need_succ (t j : Nat) (x : Family) (r : Nat) :
    need t (j+1) x r = need t j x r - bit (x j r) := by
  simp only [need, load, weight, sumAt_succ]
  omega

theorem need_appendNext (t j : Nat) (x : Family) (z : Column) (r : Nat) :
    need t (j+1) (appendNext x j z) r = need t j x r - bit (z r) := by
  have old : load (appendNext x j z) j r = load x j r := by
    unfold load weight
    apply sumAt_congr
    intro i hi
    simp [appendNext, Nat.ne_of_lt hi]
  rw [need_succ]
  simp [need, old, appendNext]

/-- For a feasible old prefix, exactly the two boundary rules preserve capacity. -/
theorem capacity_appendNext_iff {t j : Nat} {x : Family} (z : Column)
    (capacity : Capacity t j x) :
    Capacity t (j+1) (appendNext x j z) ↔
      ∀ r, r < lowerRows t →
        (need t j x r = 0 → z r = false) ∧
        (need t j x r = (slots t : Int)-(j : Int) → z r = true) := by
  constructor
  · intro next r hr
    have h := next r hr
    rw [need_appendNext] at h
    cases hz : z r <;> simp [bit, hz] at h ⊢ <;> omega
  · intro boundaries r hr
    have old := capacity r hr
    obtain ⟨zero, full⟩ := boundaries r hr
    rw [need_appendNext]
    cases hz : z r <;> simp [bit, hz] at zero full ⊢ <;> omega

/-- Reversing a binary step preserves the extent to which row counts can be completed. -/
theorem capacity_of_succ {t j : Nat} {x : Family} (next : Capacity t (j+1) x) :
    Capacity t j x := by
  intro r hr
  have h := next r hr
  rw [need_succ] at h
  cases hz : x j r <;> simp [bit, hz] at h <;> omega

/-- The exact conditions for appending a binary column to this particular prefix. -/
theorem appendNext_valid_iff {t j : Nat} {y x : Family} (z : Column)
    (inner : Inner t j x) (mixed : Mixed t j y x) (capacity : Capacity t j x) :
    (Inner t (j+1) (appendNext x j z) ∧ Mixed t (j+1) y (appendNext x j z) ∧
      Capacity t (j+1) (appendNext x j z)) ↔
    (weight (lowerRows t) z = 2*(t : Int)-2 ∧
      (∀ i, i < 2*t → meet (lowerRows t) (y i) z = (t : Int)-1) ∧
      (∀ i, i < j → meet (lowerRows t) (x i) z = (t : Int)-2) ∧
      ∀ r, r < lowerRows t →
        (need t j x r = 0 → z r = false) ∧
        (need t j x r = (slots t : Int)-(j : Int) → z r = true)) := by
  have atNext : appendNext x j z j = z := by simp [appendNext]
  have earlier (i : Nat) (hi : i < j) : appendNext x j z i = x i := by
    simp [appendNext, Nat.ne_of_lt hi]
  rw [capacity_appendNext_iff z capacity]
  constructor
  · rintro ⟨newInner, newMixed, boundaries⟩
    refine ⟨?_, ?_, ?_, boundaries⟩
    · simpa only [atNext] using newInner.colSize j (by omega)
    · intro i hi
      simpa only [atNext] using newMixed j (by omega) i hi
    · intro i hi
      simpa only [earlier i hi, atNext] using newInner.common i j hi (by omega)
  · rintro ⟨size, outside, inside, boundaries⟩
    refine ⟨⟨?_, ?_⟩, ?_, boundaries⟩
    · intro i hi
      by_cases h : i < j
      · rw [earlier i h]
        exact inner.colSize i h
      · rw [show i = j by omega, atNext]
        exact size
    · intro i k hik hk
      rw [earlier i (by omega)]
      by_cases h : k < j
      · rw [earlier k h]
        exact inner.common i k hik h
      · rw [show k = j by omega, atNext]
        exact inside i (by omega)
    · intro i hi k hk
      by_cases h : i < j
      · rw [earlier i h]
        exact mixed i h k hk
      · rw [show i = j by omega, atNext]
        exact outside k hk

/-- A wider admissible prefix supplies every smaller prefix on the same row labels. -/
theorem prefix_of_le {t j k : Nat} (hjk : j ≤ k) (witness : Prefix t k) : Prefix t j := by
  induction hjk with
  | refl => exact witness
  | @step k _ ih =>
    obtain ⟨y, x, outer, inner, mixed, capacity⟩ := witness
    exact ih ⟨y, x, outer,
      ⟨fun i hi => inner.colSize i (by omega), fun i l hil hl => inner.common i l hil (by omega)⟩,
      fun i hi => mixed i (by omega), capacity_of_succ capacity⟩

theorem empty_prefix {t : Nat} (ht : 5 ≤ t) (outer : OuterExists t) : Prefix t 0 := by
  obtain ⟨y, hy⟩ := outer
  exact ⟨y, fun _ _ => false, hy, ⟨fun _ h => by omega, fun _ _ _ h => by omega⟩,
    fun _ h => by omega, capacity_small_width (by omega)⟩

/-- With an outer design, the existential stage family is equivalent to a terminal prefix. -/
theorem existential_rounding_iff_target {t : Nat} (ht : 5 ≤ t) (outer : OuterExists t) :
    (∀ j, j < target t → Prefix t j → Prefix t (j+1)) ↔ Prefix t (target t) := by
  constructor
  · intro step
    exact climb (Nat.zero_le (target t)) (empty_prefix ht outer) (fun j _ h => step j h)
  · intro terminal j hj _
    exact prefix_of_le (by omega) terminal

/-- It suffices that some capacity-feasible prefix can be extended at each stage.
No nesting or extendibility of an arbitrary input witness is assumed. -/
theorem from_rounding (Covered : Nat → Prop)
    (covered : ∀ t, t%2 = 1 → Covered t → Had (4*t))
    (small : ∀ t, t%2 = 1 → t < 5 → Covered t)
    (outer : ∀ t, t%2 = 1 → 5 ≤ t → ¬ Covered t → OuterExists t)
    (rounding : ∀ t, t%2 = 1 → 5 ≤ t → ¬ Covered t → ∀ j, j < target t →
      Prefix t j → Prefix t (j+1))
    (lastSeven : ∀ t, 5 ≤ t → HasColumns (4*t) (4*t-7) → Had (4*t)) :
    ∀ t, 0 < t → Had (4*t) := by
  apply all_of_odd _ double_order
  intro t ho
  by_cases hc : Covered t
  · exact covered t ho hc
  · have ht : 5 ≤ t := Nat.le_of_not_gt (fun h => hc (small t ho h))
    have start := empty_prefix ht (outer t ho ht hc)
    obtain ⟨y, x, hy, hx, hm, _⟩ :=
      climb (Nat.zero_le (target t)) start (fun j _ h => rounding t ho ht hc j h)
    exact finish ht hy hx hm (lastSeven t ht)

#print axioms fractional_next
#print axioms capacity_small_width
#print axioms capacity_appendNext_iff
#print axioms appendNext_valid_iff
#print axioms prefix_of_le
#print axioms existential_rounding_iff_target
#print axioms from_rounding

end HadamardAllOrders
