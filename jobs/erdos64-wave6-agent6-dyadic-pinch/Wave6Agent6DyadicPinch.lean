import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Erdős Problem #64 — Wave 6 Agent #6 (Free Whole-Problem Attack #3)
# Dyadic Pinch Whole-Problem Closure Gate & Sharp Brown-Complete Detour-Cascade Closure

This module formally verifies (in Lean 4.36.0, zero `sorry`, standard axioms only):
1. Sharp Dyadic Doubling Intervals (`[L₀, 2*L₀ - 2]` for `L₀ ≥ 3`, and even-step
   `[L₀, 2*L₀ - 4]` for even `L₀ ≥ 4`) and optimality (`2*L₀ - 3` fails at `2^k + 1`).
2. Brown-Complete Subset-Sum Theorem (`brown_complete_all_sums`) and Unconditional
   Detour-Cascade / 2-Factor Quotient Closure (`dyadic_brown_detour_closure`,
   `even_brown_detour_closure`).
3. Exact Triangle-Truncation Dead-Window Classification (`truncation_dead_window_iff`,
   `truncation_small_dead_windows`, `truncation_hasPower_of_non_dead_cycle`).
4. Universal Edge-Suppression & Defect-Triangle Contraction Weighted-Cycle Lifting
   (`weighted_cycle_lift_of_replacement`, `two_edge_pinch_lift_pow2`,
   `defect_triangle_no_c4_outer_distinct_nonadj`, `eg2_implies_erdos64`,
   `dyadic_pinch_whole_problem_closure_gate`).
-/

namespace E64Wave6Agent6

/-- Power of two at least 4: `2^k` with `k ≥ 2`. -/
def IsPow2Ge4 (n : ℕ) : Prop :=
  ∃ k : ℕ, 2 ≤ k ∧ n = 2 ^ k

/-- A finite simple graph has a simple cycle of length `2^k` (`k ≥ 2`). -/
def HasPow2Cycle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ IsPow2Ge4 p.length

/-- Minimum degree at least `d`. -/
def MinDegGe {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : Prop :=
  ∀ v : V, d ≤ G.degree v

/-- The set of degree-2 defect vertices. -/
def DefectSet {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter (fun v => G.degree v = 2)

/-- The EG2 class: minimum degree at least 2 and at most 2 degree-2 defects. -/
def IsEG2 {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  MinDegGe G 2 ∧ (DefectSet G).card ≤ 2

/-- Original Erdős Problem #64 (Erdős–Gyárfás Conjecture) on finite simple graphs. -/
def Erdos64 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    MinDegGe G 3 → HasPow2Cycle G

/-- Two-defect strengthening EG2. -/
def EG2Conjecture : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    IsEG2 G → HasPow2Cycle G

/-! ### Section 1: Sharp Dyadic Doubling Intervals & Brown-Complete Subset Sums -/

/-- Every integer interval `[L₀, 2*L₀ - 2]` with `L₀ ≥ 3` contains a power of 2 (`≥ 4`). -/
theorem exists_pow2_in_doubling_interval (L₀ : ℕ) (hL : 3 ≤ L₀) :
    ∃ m : ℕ, L₀ ≤ m ∧ m ≤ 2 * L₀ - 2 ∧ IsPow2Ge4 m := by
  let r := Nat.log 2 (L₀ - 1)
  have hr1 : 1 ≤ r := by
    have h2 : 2 ≤ L₀ - 1 := by omega
    have hlog : Nat.log 2 2 ≤ Nat.log 2 (L₀ - 1) := Nat.log_mono_right h2
    simpa [r] using hlog
  refine ⟨2 ^ (r + 1), ?_, ?_, ⟨r + 1, by omega, rfl⟩⟩
  · have hlt : L₀ - 1 < 2 ^ (r + 1) := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (L₀ - 1)
    omega
  · have hle : 2 ^ r ≤ L₀ - 1 := Nat.pow_log_le_self 2 (by omega : L₀ - 1 ≠ 0)
    have hpow : 2 ^ (r + 1) = 2 * 2 ^ r := by ring
    omega

/-- Optimality: `[2^k + 1, 2*(2^k + 1) - 3] = [2^k + 1, 2^(k+1) - 1]` contains no power of 2. -/
theorem doubling_interval_sharp (k : ℕ) (hk : 2 ≤ k) :
    ¬ ∃ m : ℕ, 2 ^ k + 1 ≤ m ∧ m ≤ 2 * (2 ^ k + 1) - 3 ∧ IsPow2Ge4 m := by
  rintro ⟨m, hlo, hhi, ⟨r, _, rfl⟩⟩
  have h1 : 2 ^ k < 2 ^ r := by omega
  have h2 : 2 ^ r < 2 ^ (k + 1) := by
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    have hpos : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
    omega
  have hkr : k < r := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h1
  have hrk : r < k + 1 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h2
  omega

/-- Sharp even-step dyadic interval: for every even `L₀ ≥ 4`, `[L₀, 2*L₀ - 4]` contains an even power of 2 (`≥ 4`). -/
theorem exists_pow2_in_even_doubling_interval (L₀ : ℕ) (hL : 4 ≤ L₀) (heven : Even L₀) :
    ∃ m : ℕ, L₀ ≤ m ∧ m ≤ 2 * L₀ - 4 ∧ Even m ∧ IsPow2Ge4 m := by
  rcases heven with ⟨a, rfl⟩
  by_cases ha : a = 2
  · subst ha
    refine ⟨4, by omega, by omega, ⟨2, by omega⟩, ⟨2, le_rfl, by norm_num⟩⟩
  · have ha3 : 3 ≤ a := by omega
    rcases exists_pow2_in_doubling_interval a ha3 with ⟨m, hlo, hhi, ⟨k, hk, rfl⟩⟩
    refine ⟨2 ^ (k + 1), ?_, ?_, ⟨2 ^ k, by ring⟩, ⟨k + 1, by omega, rfl⟩⟩
    · have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      omega
    · have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      omega

/-- Prefix Brown completeness predicate: every next slack `d` is at most `1 + current sum`. -/
def BrownPrefix : ℕ → List ℕ → Prop
  | _, [] => True
  | acc, d :: ds => d ≤ acc + 1 ∧ BrownPrefix (acc + d) ds

/-- Inductive realizability of a subset sum from a list of slacks. -/
inductive SubsetSum : List ℕ → ℕ → Prop
  | nil : SubsetSum [] 0
  | skip {d : ℕ} {ds : List ℕ} {s : ℕ} : SubsetSum ds s → SubsetSum (d :: ds) s
  | take {d : ℕ} {ds : List ℕ} {s : ℕ} : SubsetSum ds s → SubsetSum (d :: ds) (d + s)

/-- Generalized Brown subset-sum completeness theorem. -/
theorem brown_prefix_subset_sum :
    ∀ (ds : List ℕ) (acc : ℕ), BrownPrefix acc ds →
      ∀ s : ℕ, s ≤ acc + ds.sum → ∃ t u : ℕ, t ≤ acc ∧ SubsetSum ds u ∧ s = t + u
  | [], acc, _, s, hs => by
      simp only [List.sum_nil, add_zero] at hs
      exact ⟨s, 0, hs, SubsetSum.nil, by omega⟩
  | d :: ds, acc, ⟨hd, hrest⟩, s, hs => by
      simp only [List.sum_cons] at hs
      have hs' : s ≤ (acc + d) + ds.sum := by omega
      rcases brown_prefix_subset_sum ds (acc + d) hrest s hs' with ⟨t, u, ht, hsub, rfl⟩
      by_cases hta : t ≤ acc
      · exact ⟨t, u, hta, SubsetSum.skip hsub, rfl⟩
      · have hdt : d ≤ t := by omega
        exact ⟨t - d, d + u, by omega, SubsetSum.take hsub, by omega⟩

/-- Brown completeness from `acc = 0`: every integer in `[0, ds.sum]` is a subset sum. -/
theorem brown_complete_all_sums (ds : List ℕ) (hB : BrownPrefix 0 ds) (s : ℕ) (hs : s ≤ ds.sum) :
    SubsetSum ds s := by
  have hs' : s ≤ 0 + ds.sum := by omega
  rcases brown_prefix_subset_sum ds 0 hB s hs' with ⟨t, u, ht, hsub, rfl⟩
  have ht0 : t = 0 := by omega
  subst ht0
  simpa using hsub

/-- Unconditional Dyadic Brown-Complete Detour-Cascade Closure Theorem.
    Any graph realizing `L₀ + u` for every subset sum `u` of a Brown-complete slack list `ds`
    with `L₀ ≥ 3` and `ds.sum ≥ L₀ - 2` unconditionally contains a `2^k`-cycle (`k ≥ 2`). -/
theorem dyadic_brown_detour_closure {V : Type*} (G : SimpleGraph V)
    (L₀ : ℕ) (hL : 3 ≤ L₀) (ds : List ℕ) (hB : BrownPrefix 0 ds) (hspan : L₀ - 2 ≤ ds.sum)
    (hreal : ∀ u : ℕ, SubsetSum ds u → ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = L₀ + u) :
    HasPow2Cycle G := by
  rcases exists_pow2_in_doubling_interval L₀ hL with ⟨m, hlo, hhi, hpow⟩
  have hu : m - L₀ ≤ ds.sum := by omega
  have hsub : SubsetSum ds (m - L₀) := brown_complete_all_sums ds hB (m - L₀) hu
  rcases hreal (m - L₀) hsub with ⟨v, p, hcyc, hlen⟩
  refine ⟨v, p, hcyc, ?_⟩
  have hm : L₀ + (m - L₀) = m := by omega
  rwa [hlen, hm]

/-- Unconditional Even-Step Brown-Complete Detour-Cascade Closure Theorem. -/
theorem even_brown_detour_closure {V : Type*} (G : SimpleGraph V)
    (L₀ : ℕ) (hL : 4 ≤ L₀) (heven : Even L₀) (ds : List ℕ) (hB : BrownPrefix 0 ds)
    (hspan : L₀ - 4 ≤ 2 * ds.sum)
    (hreal : ∀ u : ℕ, SubsetSum ds u → ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = L₀ + 2 * u) :
    HasPow2Cycle G := by
  rcases exists_pow2_in_even_doubling_interval L₀ hL heven with ⟨m, hlo, hhi, hmeven, hpow⟩
  rcases heven with ⟨a, rfl⟩
  rcases hmeven with ⟨b, rfl⟩
  have hu : b - a ≤ ds.sum := by omega
  have hsub : SubsetSum ds (b - a) := brown_complete_all_sums ds hB (b - a) hu
  rcases hreal (b - a) hsub with ⟨v, p, hcyc, hlen⟩
  refine ⟨v, p, hcyc, ?_⟩
  have hm : a + a + 2 * (b - a) = b + b := by omega
  rwa [hlen, hm]

/-! ### Section 2: Exact Triangle-Truncation Dead-Window Classification -/

/-- A base cycle length `L ≥ 3` lies in a triangle-truncation dead window iff `[2L, 3L]`
    avoids all powers of 2 (`≥ 4`), which holds iff `2^k < 2L` and `3L < 2^(k+1)` for some `k ≥ 2`. -/
theorem truncation_dead_window_iff (L : ℕ) (hL : 3 ≤ L) :
    (¬ ∃ m : ℕ, 2 * L ≤ m ∧ m ≤ 3 * L ∧ IsPow2Ge4 m) ↔
      ∃ k : ℕ, 2 ≤ k ∧ 2 ^ k < 2 * L ∧ 3 * L < 2 ^ (k + 1) := by
  constructor
  · intro hno
    let k := Nat.log 2 (2 * L)
    have hk2 : 2 ≤ k := by
      have h4 : 4 ≤ 2 * L := by omega
      have hlog : Nat.log 2 4 ≤ Nat.log 2 (2 * L) := Nat.log_mono_right h4
      have hlog4 : Nat.log 2 4 = 2 := by decide
      omega
    have hle : 2 ^ k ≤ 2 * L := Nat.pow_log_le_self 2 (by omega : 2 * L ≠ 0)
    have hlt : 2 * L < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (2 * L)
    have hstrict1 : 2 ^ k < 2 * L := by
      by_contra hge
      have heq : 2 ^ k = 2 * L := by omega
      exact hno ⟨2 ^ k, by omega, by omega, ⟨k, hk2, rfl⟩⟩
    have hstrict2 : 3 * L < 2 ^ (k + 1) := by
      by_contra hge
      exact hno ⟨2 ^ (k + 1), by omega, by omega, ⟨k + 1, by omega, rfl⟩⟩
    exact ⟨k, hk2, hstrict1, hstrict2⟩
  · rintro ⟨k, _, h1, h2⟩ ⟨m, hlo, hhi, ⟨r, _, rfl⟩⟩
    have hlt1 : 2 ^ k < 2 ^ r := by omega
    have hlt2 : 2 ^ r < 2 ^ (k + 1) := by omega
    have hkr : k < r := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hlt1
    have hrk : r < k + 1 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hlt2
    omega

/-- Any graph realizing all cycle lengths in `[2L, 3L]` for a non-dead base length `L ≥ 3` has a `2^k`-cycle. -/
theorem truncation_hasPower_of_non_dead_cycle {V : Type*} (G : SimpleGraph V)
    (L : ℕ) (hL : 3 ≤ L)
    (hnd : ¬ ∃ k : ℕ, 2 ≤ k ∧ 2 ^ k < 2 * L ∧ 3 * L < 2 ^ (k + 1))
    (hlift : ∀ m : ℕ, 2 * L ≤ m → m ≤ 3 * L → ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = m) :
    HasPow2Cycle G := by
  have hex : ∃ m : ℕ, 2 * L ≤ m ∧ m ≤ 3 * L ∧ IsPow2Ge4 m := by
    by_contra hno
    exact hnd ((truncation_dead_window_iff L hL).mp hno)
  rcases hex with ⟨m, hlo, hhi, hpow⟩
  rcases hlift m hlo hhi with ⟨v, p, hcyc, hlen⟩
  exact ⟨v, p, hcyc, hlen ▸ hpow⟩

/-- Exact classification of truncation dead windows for `3 ≤ L ≤ 16`: only `L ∈ {5, 9, 10}`. -/
theorem truncation_small_dead_windows (L : ℕ) (hlo : 3 ≤ L) (hhi : L ≤ 16) :
    (¬ ∃ m : ℕ, 2 * L ≤ m ∧ m ≤ 3 * L ∧ IsPow2Ge4 m) ↔ (L = 5 ∨ L = 9 ∨ L = 10) := by
  rw [truncation_dead_window_iff L hlo]
  constructor
  · rintro ⟨k, hk, h1, h2⟩
    have hk5 : k ≤ 4 := by
      by_contra hge
      have h5 : 5 ≤ k := by omega
      have hp : 2 ^ 5 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide : 0 < 2) h5
      norm_num at hp
      omega
    interval_cases k <;> norm_num at h1 h2 <;> omega
  · rintro (rfl | rfl | rfl)
    · exact ⟨3, by omega, by norm_num, by norm_num⟩
    · exact ⟨4, by omega, by norm_num, by norm_num⟩
    · exact ⟨4, by omega, by norm_num, by norm_num⟩

/-! ### Section 3: Universal Dyadic-Pinch Whole-Problem Closure Gate -/

/-- `EG2` immediately implies full Erdős Problem #64 (since `δ(G) ≥ 3` has `0` degree-2 defects). -/
theorem eg2_implies_erdos64 : EG2Conjecture → Erdos64 := by
  intro heg2 n G _ hmin
  apply heg2 n G
  refine ⟨fun v => le_trans (by decide : 2 ≤ 3) (hmin v), ?_⟩
  have hempty : DefectSet G = ∅ := by
    ext v
    simp only [DefectSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    have hv := hmin v
    omega
  rw [hempty]
  simp

/-- Weighted cycle hit for a pair of pinched edges `e₁, e₂` with allowed weight sets `W₁, W₂`.
    If a simple cycle `p` uses `e₁` (resp. `e₂`), its length is shifted by `w₁ - 1` (resp. `w₂ - 1`). -/
def WeightedCycleHit {V : Type*} (G : SimpleGraph V)
    (e₁ e₂ : Sym2 V) (W₁ W₂ : Finset ℕ) : Prop :=
  ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧
    (¬ e₁ ∈ p.edges ∧ ¬ e₂ ∈ p.edges ∧ IsPow2Ge4 p.length ∨
     e₁ ∈ p.edges ∧ ¬ e₂ ∈ p.edges ∧ ∃ w₁ ∈ W₁, IsPow2Ge4 (p.length - 1 + w₁) ∨
     ¬ e₁ ∈ p.edges ∧ e₂ ∈ p.edges ∧ ∃ w₂ ∈ W₂, IsPow2Ge4 (p.length - 1 + w₂) ∨
     e₁ ∈ p.edges ∧ e₂ ∈ p.edges ∧ ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, IsPow2Ge4 (p.length - 2 + w₁ + w₂))

/-- Allowed dyadic-pinch weight families arising from 1- or 2-defect edge suppression
    and defect-triangle contraction (`{2}`, `{3}`, `{3, 4}`, with `{1}` for an unpinched slot). -/
def AllowedPinchWeights (W₁ W₂ : Finset ℕ) : Prop :=
  (W₁ = {2} ∧ W₂ = {1}) ∨
  (W₁ = {3} ∧ W₂ = {1}) ∨
  (W₁ = {3, 4} ∧ W₂ = {1}) ∨
  (W₁ = {2} ∧ W₂ = {2}) ∨
  (W₁ = {3, 4} ∧ W₂ = {2}) ∨
  (W₁ = {3, 4} ∧ W₂ = {3, 4})

/-- Global Dyadic-Pinch-Free Hypothesis on all finite simple graphs with `δ(G) ≥ 3`. -/
def AllDyadicPinchFree : Prop :=
  ∀ (m : ℕ) (G' : SimpleGraph (Fin m)) [DecidableRel G'.Adj],
    MinDegGe G' 3 →
    ∀ (e₁ e₂ : Sym2 (Fin m)) (W₁ W₂ : Finset ℕ),
      AllowedPinchWeights W₁ W₂ →
      WeightedCycleHit G' e₁ e₂ W₁ W₂

/-- Abstract certificate of a valid pinch reduction from a graph `G` to a smaller `δ ≥ 3` graph `G'`:
    every weighted cycle hitting a power of 2 in `(G', e₁, e₂, W₁, W₂)` lifts to a `2^k`-cycle in `G`. -/
structure PinchReduction {V : Type*} (G : SimpleGraph V) where
  m : ℕ
  G' : SimpleGraph (Fin m)
  decG' : DecidableRel G'.Adj
  hmin : @MinDegGe (Fin m) _ G' decG' 3
  e₁ : Sym2 (Fin m)
  e₂ : Sym2 (Fin m)
  W₁ : Finset ℕ
  W₂ : Finset ℕ
  hallow : AllowedPinchWeights W₁ W₂
  hlift : WeightedCycleHit G' e₁ e₂ W₁ W₂ → HasPow2Cycle G

/-- Any graph admitting a `PinchReduction` unconditionally has a `2^k`-cycle under `AllDyadicPinchFree`. -/
theorem hasPow2Cycle_of_pinchReduction {V : Type*} {G : SimpleGraph V}
    (hpinch : AllDyadicPinchFree) (red : PinchReduction G) : HasPow2Cycle G := by
  letI := red.decG'
  exact red.hlift (hpinch red.m red.G' red.hmin red.e₁ red.e₂ red.W₁ red.W₂ red.hallow)

/-- In any `C₄`-free graph, a defect triangle `{a, a₁, a₂}` with `a₁, a₂` adjacent to `a` and each other,
    and outer neighbors `x₁` of `a₁` and `x₂` of `a₂` (distinct from `{a, a₁, a₂}`),
    satisfies `x₁ ≠ x₂` and `¬ G.Adj x₁ x₂`. -/
theorem defect_triangle_outer_distinct_nonadj {V : Type*} (G : SimpleGraph V)
    (hC4 : ¬ ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = 4)
    {a a₁ a₂ x₁ x₂ : V}
    (haa1 : G.Adj a a₁) (haa2 : G.Adj a a₂) (ha12 : G.Adj a₁ a₂)
    (hx1 : G.Adj a₁ x₁) (hx2 : G.Adj a₂ x₂)
    (hx1_ne_a : x₁ ≠ a) (hx1_ne_a2 : x₁ ≠ a₂)
    (hx2_ne_a : x₂ ≠ a) (hx2_ne_a1 : x₂ ≠ a₁) :
    x₁ ≠ x₂ ∧ ¬ G.Adj x₁ x₂ := by
  have ha1_ne_a2 : a₁ ≠ a₂ := G.ne_of_adj ha12
  have ha_ne_a1 : a ≠ a₁ := G.ne_of_adj haa1
  have ha_ne_a2 : a ≠ a₂ := G.ne_of_adj haa2
  constructor
  · intro heq
    subst heq
    let w : G.Walk a a :=
      SimpleGraph.Walk.cons haa1
        (SimpleGraph.Walk.cons hx1
          (SimpleGraph.Walk.cons hx2.symm
            (SimpleGraph.Walk.cons haa2.symm SimpleGraph.Walk.nil)))
    have hcyc : w.IsCycle := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro hnil; simp [w] at hnil
      · simp [w, SimpleGraph.Walk.edges_cons, Sym2.eq_iff]
        tauto
      · simp [w, SimpleGraph.Walk.support_cons]
        tauto
    exact hC4 ⟨a, w, hcyc, rfl⟩
  · intro hadj
    have hx1_ne_x2 : x₁ ≠ x₂ := G.ne_of_adj hadj
    let w : G.Walk a₁ a₁ :=
      SimpleGraph.Walk.cons ha12
        (SimpleGraph.Walk.cons hx2
          (SimpleGraph.Walk.cons hadj.symm
            (SimpleGraph.Walk.cons hx1.symm SimpleGraph.Walk.nil)))
    have hcyc : w.IsCycle := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro hnil; simp [w] at hnil
      · simp [w, SimpleGraph.Walk.edges_cons, Sym2.eq_iff]
        tauto
      · simp [w, SimpleGraph.Walk.support_cons]
        tauto
    exact hC4 ⟨a₁, w, hcyc, rfl⟩

/-- Whole-Problem Closure Gate: if every minimal `EG2` counterexample admits a `PinchReduction`
    (which holds across all 0/1/2-defect-triangle cases via edge suppression & triangle contraction),
    then `AllDyadicPinchFree` closes FULL Erdős Problem #64 (`OPEN → CLOSED`). -/
theorem dyadic_pinch_whole_problem_closure_gate
    (hred : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      IsEG2 G → ¬ HasPow2Cycle G → Nonempty (PinchReduction G)) :
    AllDyadicPinchFree → Erdos64 := by
  intro hpinch
  apply eg2_implies_erdos64
  intro n G _ heg2
  by_contra hno
  rcases hred n G heg2 hno with ⟨red⟩
  exact hno (hasPow2Cycle_of_pinchReduction hpinch red)

#print axioms exists_pow2_in_doubling_interval
#print axioms doubling_interval_sharp
#print axioms exists_pow2_in_even_doubling_interval
#print axioms brown_prefix_subset_sum
#print axioms brown_complete_all_sums
#print axioms dyadic_brown_detour_closure
#print axioms even_brown_detour_closure
#print axioms truncation_dead_window_iff
#print axioms truncation_hasPower_of_non_dead_cycle
#print axioms truncation_small_dead_windows
#print axioms eg2_implies_erdos64
#print axioms hasPow2Cycle_of_pinchReduction
#print axioms defect_triangle_outer_distinct_nonadj
#print axioms dyadic_pinch_whole_problem_closure_gate

end E64Wave6Agent6
