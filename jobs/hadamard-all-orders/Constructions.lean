import Reductions

namespace HadamardAllOrders

open Hadamard2396 (sumAt sumAt_succ sumAt_split sumAt_add sumAt_congr)

def appendCol (m : Nat) (a b : Column) : Column :=
  fun i => if i < m then a i else b (i-m)

theorem dot_append (m n : Nat) (a b c d : Column) :
    dot (m+n) (appendCol m a b) (appendCol m c d) = dot m a c + dot n b d := by
  unfold dot
  rw [sumAt_split]
  congr 1
  · apply sumAt_congr
    intro i hi
    simp [appendCol, hi]
  · apply sumAt_congr
    intro i _
    simp [appendCol, Nat.not_lt_of_ge (Nat.le_add_right m i)]

theorem stack {m n k : Nat} (top : HasColumns m k) (bottom : HasColumns n k) :
    HasColumns (m+n) k := by
  obtain ⟨a, ha⟩ := top
  obtain ⟨b, hb⟩ := bottom
  exact ⟨fun j => appendCol m (a j) (b j), fun i j hij hj => by
    rw [dot_append, ha i j hij hj, hb i j hij hj]; decide⟩

theorem restrict_cols {n k l : Nat} (h : HasColumns n k) (hl : l ≤ k) : HasColumns n l := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, fun i j hij hj => ha i j hij (by omega)⟩

def negate (a : Column) : Column := fun i => !(a i)

theorem dot_neg_right (n : Nat) (a b : Column) : dot n a (negate b) = -(dot n a b) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [dot, sumAt_succ] at *
    rw [ih]
    have point (u v : Bool) :
        (if u = !v then (1 : Int) else -1) = -(if u = v then (1 : Int) else -1) := by
      cases u <;> cases v <;> decide
    unfold negate
    rw [point (a n) (b n)]
    omega

theorem dot_neg_neg (n : Nat) (a b : Column) : dot n (negate a) (negate b) = dot n a b := by
  unfold dot
  apply sumAt_congr
  intro i _
  simp [negate]

def doubleFamily (n : Nat) (a : Family) (j : Nat) : Column :=
  if j < n then appendCol n (a j) (a j)
  else appendCol n (a (j-n)) (negate (a (j-n)))

theorem double_order (n : Nat) (h : Had n) : Had (2*n) := by
  obtain ⟨a, ha⟩ := h
  refine ⟨doubleFamily n a, ?_⟩
  intro i j hij hj
  rw [show 2*n = n+n by omega]
  by_cases hi : i < n <;> by_cases hj' : j < n
  · simp [doubleFamily, hi, hj', dot_append, ha i j hij hj']
  · simp [doubleFamily, hi, hj', dot_append, dot_neg_right]
    omega
  · omega
  · simp [doubleFamily, hi, hj', dot_append, dot_neg_neg, ha (i-n) (j-n) (by omega) (by omega)]

theorem swap_sums (m n : Nat) (f : Nat → Nat → Int) :
    sumAt m (fun i => sumAt n (f i)) = sumAt n (fun j => sumAt m (fun i => f i j)) := by
  induction m with
  | zero => exact (sum_zero n).symm
  | succ m ih =>
    simp only [sumAt_succ, sumAt_add, ih]

theorem sum_const (n : Nat) (c : Int) : sumAt n (fun _ => c) = (n : Int)*c := by
  induction n with
  | zero => simp [sumAt]
  | succ n ih => simp [sumAt_succ, ih, Int.add_mul]

/-- Summing all mixed counts double-counts incidences on the support of a column. -/
theorem mixed_sum {t : Nat} {y : Family} (hy : Outer t y) (x : Column) :
    sumAt (2*t) (fun j => meet (lowerRows t) (y j) x) = weight (lowerRows t) x * (t : Int) := by
  unfold meet
  rw [swap_sums]
  have hrow {r : Nat} (hr : r < lowerRows t) :
      sumAt (2*t) (fun j => bit (y j r && x r)) = bit (x r)*(t : Int) := by
    cases h : x r
    · simp [bit, sum_zero]
    · simpa [weight, bit] using hy.rowSize r hr
  rw [sumAt_congr _ (fun i hi => hrow hi)]
  unfold weight
  generalize lowerRows t = m
  induction m with
  | zero => simp [sumAt]
  | succ m ih => simp only [sumAt_succ, ih, Int.add_mul]

theorem last_mixed {t : Nat} {y : Family} (ht : 1 ≤ t) (hy : Outer t y)
    (x : Column) (hx : weight (lowerRows t) x = 2*(t : Int)-2)
    (prev : ∀ j, j < 2*t-1 → meet (lowerRows t) (y j) x = (t : Int)-1) :
    meet (lowerRows t) (y (2*t-1)) x = (t : Int)-1 := by
  let m := 2*t-1
  have h : 2*t = m+1 := by dsimp [m]; omega
  have hc : (m : Int) = 2*(t : Int)-1 := by dsimp [m]; omega
  have total := mixed_sum hy x
  rw [h, sumAt_succ, sumAt_congr m prev, sum_const, hc, hx] at total
  simp only [Int.sub_mul, Int.mul_sub, Int.mul_one, Int.one_mul] at total
  change meet (lowerRows t) (y m) x = (t : Int)-1
  omega

/-- Full marginals, all mixed counts for the first j inner columns, and the
first l mixed counts for inner column j. Every count refers to the same pair. -/
def Stage (t j l : Nat) : Prop := ∃ y x,
  Outer t y ∧ Inner t (target t) x ∧ Mixed t j y x ∧
    ∀ k, k < l → meet (lowerRows t) (y k) (x j) = (t : Int)-1

theorem coupling_from_single_checks {t j : Nat} (ht : 5 ≤ t) (hj : j < target t)
    (checks : ∀ l, l < 2*t-1 → Stage t j l → Stage t j (l+1))
    (earlier : CompatibleThrough t j) : CompatibleThrough t (j+1) := by
  obtain ⟨y, x, hy, hx, hm⟩ := earlier
  have start : Stage t j 0 := ⟨y, x, hy, hx, hm, fun _ h => by omega⟩
  obtain ⟨y', x', hy', hx', hm', row⟩ := climb (Nat.zero_le (2*t-1)) start
    (fun l _ hl prev => checks l hl prev)
  refine ⟨y', x', hy', hx', ?_⟩
  intro i hi k hk
  by_cases h : i < j
  · exact hm' i h k hk
  · have eq : i = j := by omega
    subst i
    by_cases before : k < 2*t-1
    · exact row k before
    · have endIndex : k = 2*t-1 := by omega
      rw [endIndex]
      exact last_mixed (by omega) hy' _ (hx'.colSize j hj) row

/-- The open inputs are exterior existence, interior growth and compatible growth.
The established Paley/small cases and the published last-seven theorem are explicit. -/
theorem from_three_families (Covered : Nat → Prop)
    (covered : ∀ t, t%2 = 1 → Covered t → Had (4*t))
    (small : ∀ t, t%2 = 1 → t < 5 → Covered t)
    (outer : ∀ t, t%2 = 1 → 5 ≤ t → ¬ Covered t → OuterExists t)
    (grow : ∀ t, t%2 = 1 → 5 ≤ t → ¬ Covered t → ∀ k, min t (target t) ≤ k →
      k < target t → InnerExists t k → InnerExists t (k+1))
    (couple : ∀ t, t%2 = 1 → 5 ≤ t → ¬ Covered t → ∀ k, k < target t →
      CompatibleThrough t k → CompatibleThrough t (k+1))
    (lastSeven : ∀ t, 5 ≤ t → HasColumns (4*t) (4*t-7) → Had (4*t)) :
    ∀ t, 0 < t → Had (4*t) :=
  all_orders Covered covered small outer (fun _ ht => seed_from_outer ht)
    grow couple lastSeven double_order

/-- Keeps q = 43^(60k+1) in one residue class modulo 8·3·5·31·61. -/
theorem scarpis_residue (k : Nat) : 43^(60*k+1) % 226920 = 43 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show 60*(k+1)+1 = 60*k+1+60 by omega, Nat.pow_add, Nat.mul_mod, ih]

#print axioms scarpis_residue
#print axioms coupling_from_single_checks
#print axioms from_three_families
#print axioms last_mixed
#print axioms stack
#print axioms finish_full

end HadamardAllOrders
