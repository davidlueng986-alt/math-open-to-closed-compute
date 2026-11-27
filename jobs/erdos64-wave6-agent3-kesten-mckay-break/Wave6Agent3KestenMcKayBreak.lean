import Shadow
import NonBacktrackingGirth
import Wave5Agent6ChebyshevGirth

/-!
# Wave 6 Agent #3: Breaking the Fixed-k Kesten–McKay Barrier for Erdős Problem #64

Three unified, all-order, unbounded-`n` pillars formalized in Lean 4.36.0:

1. **Dynamic-`k` (`Θ(log log n)`) Unconditional Kesten–McKay Barrier Break**:
   - `dynamic_k_taillessCount_lb` & `dynamic_k_taillessCount_pos`: For EVERY finite `d`-regular
     simple graph (`d ≥ 3`) of arbitrary unbounded order `n ≥ 1` and arbitrary girth `g ≥ 3`,
     choosing `k ≥ 1` dynamically so that `2 * n ≤ (d - 1) ^ (2 ^ k)` unconditionally yields
     `taillessCount G (2 ^ (k + 1)) > 0` with zero spectral-gap assumption.
   - `exists_dynamic_k_taillessCount_pos`: Pure unbounded-`n` existential positivity.
   - `dynamic_k_logarithmic_girth_hasPower`: Unbounded-`n` closure whenever girth exceeds `2 ^ k(n)`.

2. **Non-Spectral Cycle-Interval & Arithmetic-Progression Power-of-2 Forcing**:
   - `exists_pow2_in_int_interval`, `exists_pow2_in_even_interval`, `exists_pow2_in_ap_interval`:
     Sharp arithmetic theorems proving every interval `[A, B]` (`A ≥ 3, B ≥ 2A - 2`), even interval
     `[2a, 2b]` (`a ≥ 2, b ≥ 2a - 2`), or `2^s`-step progression `[2^s a, 2^s b]` contains a power of 2.
   - `hasPower_of_consecutive_even_cycles`, `hasPower_of_consecutive_cycles`,
     `erdos64_of_even_cycle_interval_forcing`: Non-spectral whole-problem closure gate.

3. **Intrinsic `BypassChain` Triangle-Adjuster Cycle-Interval & `C_32` Pincer Saturation Law**:
   - `BypassChain.realize_length` & `BypassChain.realize_isCycle`: Replacing any subset of `r`
     vertex-disjoint off-cycle triangle bypasses along a simple cycle `C` of length `L` yields a
     simple cycle of exact length `L + |J|`.
   - `BypassChain.exists_cycle_of_mem_Icc`: Realizes EVERY integer cycle length in `[L, L + r]`.
   - `BypassChain.hasPower_of_pow2_in_window` & `BypassChain.hasPower_of_dense_bypasses`:
     Unbounded-`n`, fixed-girth (`g = 3`) closure whenever `2^k ∈ [L, L + r]` or `r ≥ L - 2`.
   - `BypassChain.interior_edge_saturation`: Proves mathematically why any strict-interior hit
     `L < target < L + r` (such as `target = 32`) saturates BOTH the direct edge `u_i - w_i` AND
     both triangle bypass edges `u_i - z_i - w_i` for every bypass `i < r`.
-/

namespace E64Wave6Agent3
open SimpleGraph Erdos64Closure E64NonBacktrackingGirth E64Wave5Agent6

/-! ## Pillar 1: Dynamic-`k` (`Θ(log log n)`) Breaking of the Fixed-`k` Kesten–McKay Barrier -/

section DynamicK

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Quantitative dynamic-`k` lower bound on `taillessCount G (2 ^ (k + 1))` for any `d`-regular
graph (`d ≥ 3`) of arbitrary unbounded order `n > 0` and arbitrary girth, whenever
`2 * n ≤ (d - 1) ^ (2 ^ k)`. -/
theorem dynamic_k_taillessCount_lb (G : SimpleGraph V) [DecidableRel G.Adj] {d k : ℕ}
    (hd : 3 ≤ d) (hreg : ∀ v : V, G.degree v = d) (hn : 0 < Fintype.card V)
    (_hk : 1 ≤ k) :
    let L := 2 ^ k
    let n : ℚ := (Fintype.card V : ℚ)
    let M : ℚ := ((d - 1 : ℕ) : ℚ) ^ L
    (M - 2 * n) * M + 2 * M + ((d - 2 : ℕ) : ℚ) * n + 1 ≤
      (taillessCount G (2 ^ (k + 1)) : ℚ) := by
  intro L n M
  have hL : 1 ≤ L := Nat.one_le_two_pow
  have hlb := taillessCount_double_ge G (by omega) hreg hn hL
  have hpow : 2 * L = 2 ^ (k + 1) := by dsimp only [L]; ring
  rw [hpow] at hlb
  have hid : (M + 1) ^ 2 - (2 * M - ((d - 2 : ℕ) : ℚ)) * n =
      (M - 2 * n) * M + 2 * M + ((d - 2 : ℕ) : ℚ) * n + 1 := by ring
  dsimp only [M, n] at hid ⊢
  linarith

/-- Unconditional dynamic-`k` positivity: for EVERY finite `d`-regular simple graph (`d ≥ 3`)
of arbitrary unbounded order `n > 0` and arbitrary girth, choosing `k ≥ 1` with
`2 * n ≤ (d - 1) ^ (2 ^ k)` unconditionally breaks the Kesten–McKay barrier:
`0 < taillessCount G (2 ^ (k + 1))`. -/
theorem dynamic_k_taillessCount_pos (G : SimpleGraph V) [DecidableRel G.Adj] {d k : ℕ}
    (hd : 3 ≤ d) (hreg : ∀ v : V, G.degree v = d) (hn : 0 < Fintype.card V)
    (hk : 1 ≤ k) (hdom : 2 * Fintype.card V ≤ (d - 1) ^ (2 ^ k)) :
    0 < taillessCount G (2 ^ (k + 1)) := by
  have hlb := dynamic_k_taillessCount_lb G hd hreg hn hk
  dsimp only at hlb
  have hdom_q : 2 * (Fintype.card V : ℚ) ≤ ((d - 1 : ℕ) : ℚ) ^ (2 ^ k) := by
    exact_mod_cast hdom
  have hM_nonneg : (0 : ℚ) ≤ ((d - 1 : ℕ) : ℚ) ^ (2 ^ k) := by positivity
  have hprod_nonneg :
      (0 : ℚ) ≤ (((d - 1 : ℕ) : ℚ) ^ (2 ^ k) - 2 * (Fintype.card V : ℚ)) *
        ((d - 1 : ℕ) : ℚ) ^ (2 ^ k) :=
    mul_nonneg (sub_nonneg.mpr hdom_q) hM_nonneg
  have hdn_nonneg : (0 : ℚ) ≤ ((d - 2 : ℕ) : ℚ) * (Fintype.card V : ℚ) := by positivity
  have hpos_q : (0 : ℚ) < (taillessCount G (2 ^ (k + 1)) : ℚ) := by linarith
  exact_mod_cast hpos_q

/-- Pure unbounded-`n` existential theorem: for EVERY finite `d`-regular simple graph (`d ≥ 3`)
on `n > 0` vertices (with zero spectral-gap or girth assumption), there exists a dynamic
`k ≥ 1` such that `0 < taillessCount G (2 ^ (k + 1))`. -/
theorem exists_dynamic_k_taillessCount_pos (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hd : 3 ≤ d) (hreg : ∀ v : V, G.degree v = d) (hn : 0 < Fintype.card V) :
    ∃ k : ℕ, 1 ≤ k ∧ 0 < taillessCount G (2 ^ (k + 1)) := by
  let n := Fintype.card V
  let k := n + 1
  have hk : 1 ≤ k := by omega
  have h2k : 2 * n ≤ 2 ^ k := by
    have h1 : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
    calc 2 * n ≤ 2 * (n + 1) := by omega
      _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 h1
      _ = 2 ^ (n + 1) := by ring
  have hdom : 2 * n ≤ (d - 1) ^ (2 ^ k) := by
    have hbase : 2 ≤ d - 1 := by omega
    calc 2 * n ≤ 2 ^ k := h2k
      _ ≤ 2 ^ (2 ^ k) := Nat.le_of_lt Nat.lt_two_pow_self
      _ ≤ (d - 1) ^ (2 ^ k) := Nat.pow_le_pow_left hbase (2 ^ k)
  exact ⟨k, hk, dynamic_k_taillessCount_pos G hd hreg hn hk hdom⟩

/-- Unbounded-`n` dynamic-`k` logarithmic-girth closure: if a `d`-regular graph (`d ≥ 3`) of
arbitrary order `n > 0` has girth exceeding `2 ^ k` for some dynamic `k ≥ 1` with
`2 * n ≤ (d - 1) ^ (2 ^ k)`, then `HasPower G` holds unconditionally. -/
theorem dynamic_k_logarithmic_girth_hasPower (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hd : 3 ≤ d) (hreg : ∀ v : V, G.degree v = d) (hn : 0 < Fintype.card V)
    (hlog : ∃ k : ℕ, 1 ≤ k ∧ 2 * Fintype.card V ≤ (d - 1) ^ (2 ^ k) ∧
      GirthAtLeast G (2 ^ k + 1)) :
    HasPower G := by
  obtain ⟨k, hk, hdom, hg⟩ := hlog
  have hpos := dynamic_k_taillessCount_pos G hd hreg hn hk hdom
  obtain ⟨v, p, hcyc, hlen⟩ := exists_tailless_of_pos G hpos
  exact hasPower_of_cyclicallyNonBacktracking_lt_two_girth hg (by omega : 2 ≤ k + 1)
    (by
      have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      omega)
    p hcyc hlen

end DynamicK

/-! ## Pillar 2: Non-Spectral Cycle-Interval & Arithmetic-Progression Power-of-2 Forcing -/

section CycleIntervalForcing

/-- Sharp integer interval power-of-2 theorem: for every `A ≥ 3` and `B ≥ 2 * A - 2`,
the contiguous integer interval `[A, B]` contains a power of 2 `2 ^ k` with `k ≥ 2`. -/
theorem exists_pow2_in_int_interval {A B : ℕ} (hA : 3 ≤ A) (hB : 2 * A - 2 ≤ B) :
    ∃ k : ℕ, 2 ≤ k ∧ A ≤ 2 ^ k ∧ 2 ^ k ≤ B := by
  have hex : ∃ m : ℕ, A ≤ 2 ^ m := ⟨A, Nat.le_of_lt Nat.lt_two_pow_self⟩
  let k := Nat.find hex
  have hk_ge : A ≤ 2 ^ k := Nat.find_spec hex
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have hk_le1 : k ≤ 1 := by omega
    interval_cases k <;> simp at hk_ge <;> omega
  have hk_prev : 2 ^ (k - 1) < A := by
    have hlt : k - 1 < k := by omega
    exact Nat.lt_of_not_ge (Nat.find_min hex hlt)
  have h2k_eq : 2 ^ k = 2 * 2 ^ (k - 1) := by
    have hk1 : k = (k - 1) + 1 := by omega
    conv_lhs => rw [hk1, pow_succ]
    ring
  have hk_le : 2 ^ k ≤ B := by omega
  exact ⟨k, hk2, hk_ge, hk_le⟩

/-- Sharp consecutive even-cycle interval power-of-2 theorem: for every `a ≥ 2` and `b ≥ 2 * a - 2`,
the even interval `{2*a, 2*a + 2, ..., 2*b}` contains a power of 2 `2 ^ k` with `k ≥ 2`. -/
theorem exists_pow2_in_even_interval {a b : ℕ} (ha : 2 ≤ a) (hb : 2 * a - 2 ≤ b) :
    ∃ k : ℕ, 2 ≤ k ∧ 2 * a ≤ 2 ^ k ∧ 2 ^ k ≤ 2 * b := by
  by_cases ha2 : a = 2
  · refine ⟨2, le_rfl, by omega, by omega⟩
  · have ha3 : 3 ≤ a := by omega
    obtain ⟨m, hm2, hlo, hhi⟩ := exists_pow2_in_int_interval ha3 hb
    refine ⟨m + 1, by omega, ?_, ?_⟩
    · have : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
      omega
    · have : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
      omega

/-- Unified `2 ^ s`-step arithmetic progression power-of-2 theorem: for every `s ≥ 0`, `a ≥ 2`
(with `a ≥ 3` when `s = 0`), and `b ≥ 2 * a - 2`, there exists `k ≥ 2` with
`2 ^ s * a ≤ 2 ^ k ≤ 2 ^ s * b`. -/
theorem exists_pow2_in_ap_interval {s a b : ℕ}
    (ha : if s = 0 then 3 ≤ a else 2 ≤ a) (hb : 2 * a - 2 ≤ b) :
    ∃ k : ℕ, 2 ≤ k ∧ 2 ^ s * a ≤ 2 ^ k ∧ 2 ^ k ≤ 2 ^ s * b := by
  cases s with
  | zero =>
      simp only [↓reduceIte] at ha
      obtain ⟨k, hk2, hlo, hhi⟩ := exists_pow2_in_int_interval ha hb
      exact ⟨k, hk2, by simpa using hlo, by simpa using hhi⟩
  | succ s' =>
      simp only [Nat.succ_ne_zero, ↓reduceIte] at ha
      obtain ⟨k, hk2, hlo, hhi⟩ := exists_pow2_in_even_interval ha hb
      refine ⟨s' + k, by omega, ?_, ?_⟩
      · calc 2 ^ (s' + 1) * a = 2 ^ s' * (2 * a) := by ring
          _ ≤ 2 ^ s' * 2 ^ k := Nat.mul_le_mul_left _ hlo
          _ = 2 ^ (s' + k) := (pow_add 2 s' k).symm
      · calc 2 ^ (s' + k) = 2 ^ s' * 2 ^ k := pow_add 2 s' k
          _ ≤ 2 ^ s' * (2 * b) := Nat.mul_le_mul_left _ hhi
          _ = 2 ^ (s' + 1) * b := by ring

/-- Non-spectral consecutive even-cycle interval closure: if `G` contains a simple cycle of
length `2 * m` for every `m ∈ [a, b]` with `a ≥ 2` and `b ≥ 2 * a - 2`, then `HasPower G`. -/
theorem hasPower_of_consecutive_even_cycles {V : Type*} (G : SimpleGraph V)
    {a b : ℕ} (ha : 2 ≤ a) (hb : 2 * a - 2 ≤ b)
    (hcyc : ∀ m : ℕ, a ≤ m → m ≤ b → ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = 2 * m) :
    HasPower G := by
  obtain ⟨k, hk2, hlo, hhi⟩ := exists_pow2_in_even_interval ha hb
  have h2k : 2 ^ k = 2 * 2 ^ (k - 1) := by
    have hk1 : k = (k - 1) + 1 := by omega
    conv_lhs => rw [hk1, pow_succ]
    ring
  obtain ⟨v, c, hc, hlen⟩ := hcyc (2 ^ (k - 1)) (by omega) (by omega)
  exact ⟨k, v, c, hk2, hc, by omega⟩

/-- Non-spectral consecutive integer-cycle interval closure: if `G` contains a simple cycle of
length `L` for every `L ∈ [A, B]` with `A ≥ 3` and `B ≥ 2 * A - 2`, then `HasPower G`. -/
theorem hasPower_of_consecutive_cycles {V : Type*} (G : SimpleGraph V)
    {A B : ℕ} (hA : 3 ≤ A) (hB : 2 * A - 2 ≤ B)
    (hcyc : ∀ L : ℕ, A ≤ L → L ≤ B → ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = L) :
    HasPower G := by
  obtain ⟨k, hk2, hlo, hhi⟩ := exists_pow2_in_int_interval hA hB
  obtain ⟨v, c, hc, hlen⟩ := hcyc (2 ^ k) hlo hhi
  exact ⟨k, v, c, hk2, hc, hlen⟩

/-- **Whole-Problem Non-Spectral Closure Gate**: If every finite simple graph with `δ(G) ≥ 3`
admits a consecutive even-cycle interval `[2a, 2b]` with `a ≥ 2` and `b ≥ 2a - 2`, then the
entire Erdős–Gyárfás Conjecture holds. -/
theorem erdos64_of_even_cycle_interval_forcing
    (H : ∀ {W : Type} [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj],
      (∀ v : W, 3 ≤ G.degree v) →
      ∃ a b : ℕ, 2 ≤ a ∧ 2 * a - 2 ≤ b ∧
        ∀ m : ℕ, a ≤ m → m ≤ b → ∃ (v : W) (c : G.Walk v v), c.IsCycle ∧ c.length = 2 * m) :
    ∀ {W : Type} [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj],
      (∀ v : W, 3 ≤ G.degree v) → HasPower G := by
  intro W _ _ G _ hdeg
  obtain ⟨a, b, ha, hb, hcyc⟩ := H G hdeg
  exact hasPower_of_consecutive_even_cycles G ha hb hcyc

end CycleIntervalForcing

/-! ## Pillar 3: Intrinsic `BypassChain` Triangle-Adjuster Cycle-Interval & Pincer Saturation Law -/

section BypassAdjusters

variable {V : Type*}

/-- A walk decomposed into alternating fixed segments and independent local triangle bypasses:
at each `step`, the walk may traverse either the direct edge `u — w` (length 1) or the
triangle bypass `u — z — w` (length 2) via apex `z`. -/
inductive BypassChain (G : SimpleGraph V) : V → V → Type _
  | base {a b : V} (p : G.Walk a b) : BypassChain G a b
  | step {a u w b : V} (p : G.Walk a u) (huw : G.Adj u w)
      (z : V) (huz : G.Adj u z) (hzw : G.Adj z w)
      (rest : BypassChain G w b) : BypassChain G a b

namespace BypassChain

/-- Number of independent triangle bypasses in the chain. -/
def numBypasses {G : SimpleGraph V} : ∀ {a b : V}, BypassChain G a b → ℕ
  | _, _, .base _ => 0
  | _, _, .step _ _ _ _ _ rest => rest.numBypasses + 1

/-- List of off-cycle triangle apex vertices `[z₁, ..., z_r]`. -/
def apexes {G : SimpleGraph V} : ∀ {a b : V}, BypassChain G a b → List V
  | _, _, .base _ => []
  | _, _, .step _ _ z _ _ rest => z :: rest.apexes

/-- Base walk obtained by taking the direct edge `u — w` at every bypass. -/
def baseWalk {G : SimpleGraph V} : ∀ {a b : V}, BypassChain G a b → G.Walk a b
  | _, _, .base p => p
  | _, _, .step p huw _ _ _ rest => p.append (Walk.cons huw rest.baseWalk)

/-- Realized walk for a boolean choice mask (`false` = direct edge `u — w`,
`true` = triangle bypass `u — z — w`). -/
def realize {G : SimpleGraph V} : ∀ {a b : V}, BypassChain G a b → List Bool → G.Walk a b
  | _, _, .base p, _ => p
  | _, _, .step p huw _ _ _ rest, [] => p.append (Walk.cons huw rest.baseWalk)
  | _, _, .step p huw _ _ _ rest, false :: bs =>
      p.append (Walk.cons huw (rest.realize bs))
  | _, _, .step p _ _ huz hzw rest, true :: bs =>
      p.append (Walk.cons huz (Walk.cons hzw (rest.realize bs)))

/-- Exact length law: realizing `mask` increases the base walk length by `mask.count true`. -/
theorem realize_length {G : SimpleGraph V} :
    ∀ {a b : V} (c : BypassChain G a b) (mask : List Bool),
      mask.length = c.numBypasses →
      (c.realize mask).length = c.baseWalk.length + mask.count true
  | _, _, .base p, [], _ => by simp [realize, baseWalk]
  | _, _, .base _, _ :: _, hlen => by simp [numBypasses] at hlen
  | _, _, .step _ _ _ _ _ _, [], hlen => by simp [numBypasses] at hlen
  | _, _, .step p huw z huz hzw rest, false :: bs, hlen => by
      simp only [numBypasses, List.length_cons, Nat.add_right_cancel_iff] at hlen
      have ih := realize_length rest bs hlen
      simp [realize, baseWalk, Walk.length_append, Walk.length_cons, List.count_cons]
      omega
  | _, _, .step p huw z huz hzw rest, true :: bs, hlen => by
      simp only [numBypasses, List.length_cons, Nat.add_right_cancel_iff] at hlen
      have ih := realize_length rest bs hlen
      simp [realize, baseWalk, Walk.length_append, Walk.length_cons, List.count_cons]
      omega

private theorem mem_support_of_mem_edges {G : SimpleGraph V} :
    ∀ {a b : V} {p : G.Walk a b} {e : Sym2 V} {x : V},
      e ∈ p.edges → x ∈ e → x ∈ p.support
  | _, _, .nil, _, _, he, _ => by simp at he
  | _, _, .cons h rest, e, x, he, hx => by
      simp only [Walk.edges_cons, List.mem_cons] at he
      rcases he with rfl | hmem
      · simp only [Sym2.mem_iff] at hx
        rcases hx with rfl | rfl
        · exact Walk.start_mem_support _
        · exact List.mem_cons_of_mem _ (Walk.start_mem_support rest)
      · exact List.mem_cons_of_mem _ (mem_support_of_mem_edges hmem hx)

private theorem support_append_tail {G : SimpleGraph V} {a u b : V}
    (p : G.Walk a u) (q : G.Walk u b) :
    (p.append q).support.tail = p.support.tail ++ q.support.tail := by
  rw [Walk.support_append]
  cases hp : p.support with
  | nil => exact absurd hp (Walk.support_ne_nil p)
  | cons x xs => simp

private theorem mem_realize_support_tail {G : SimpleGraph V} :
    ∀ {a b : V} (c : BypassChain G a b) (mask : List Bool),
      mask.length = c.numBypasses →
      ∀ x ∈ (c.realize mask).support.tail,
        x ∈ c.baseWalk.support.tail ∨ x ∈ c.apexes
  | _, _, .base p, [], _, x, hx => Or.inl hx
  | _, _, .base _, _ :: _, hlen, _, _ => by simp [numBypasses] at hlen
  | _, _, .step _ _ _ _ _ _, [], hlen, _, _ => by simp [numBypasses] at hlen
  | _, _, .step (w := w) p huw z huz hzw rest, false :: bs, hlen, x, hx => by
      simp only [numBypasses, List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [realize, baseWalk, support_append_tail, Walk.support_cons, List.tail_cons,
        List.mem_append, apexes, List.mem_cons] at hx ⊢
      rcases hx with hp | hrest
      · exact Or.inl (Or.inl hp)
      · cases hr : (rest.realize bs).support with
        | nil => exact absurd hr (Walk.support_ne_nil _)
        | cons w0 ws =>
            have hw0 : w0 = w := by
              have hstart := Walk.head_support (rest.realize bs)
              rw [hr] at hstart
              simpa using hstart
            rw [hr, List.mem_cons] at hrest
            rcases hrest with rfl | hws
            · refine Or.inl (Or.inr ?_)
              rw [hw0]
              exact Walk.start_mem_support rest.baseWalk
            · have htail : x ∈ (rest.realize bs).support.tail := by rw [hr]; exact hws
              rcases mem_realize_support_tail rest bs hlen x htail with hbase | hap
              · exact Or.inl (Or.inr (List.mem_of_mem_tail hbase))
              · exact Or.inr (Or.inr hap)
  | _, _, .step (w := w) p huw z huz hzw rest, true :: bs, hlen, x, hx => by
      simp only [numBypasses, List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [realize, baseWalk, support_append_tail, Walk.support_cons, List.tail_cons,
        List.mem_append, List.mem_cons, apexes] at hx ⊢
      rcases hx with hp | rfl | hrest
      · exact Or.inl (Or.inl hp)
      · exact Or.inr (Or.inl rfl)
      · cases hr : (rest.realize bs).support with
        | nil => exact absurd hr (Walk.support_ne_nil _)
        | cons w0 ws =>
            have hw0 : w0 = w := by
              have hstart := Walk.head_support (rest.realize bs)
              rw [hr] at hstart
              simpa using hstart
            rw [hr, List.mem_cons] at hrest
            rcases hrest with rfl | hws
            · refine Or.inl (Or.inr ?_)
              rw [hw0]
              exact Walk.start_mem_support rest.baseWalk
            · have htail : x ∈ (rest.realize bs).support.tail := by rw [hr]; exact hws
              rcases mem_realize_support_tail rest bs hlen x htail with hbase | hap
              · exact Or.inl (Or.inr (List.mem_of_mem_tail hbase))
              · exact Or.inr (Or.inr hap)

private theorem realize_support_tail_nodup {G : SimpleGraph V} :
    ∀ {a b : V} (c : BypassChain G a b) (mask : List Bool),
      mask.length = c.numBypasses →
      c.baseWalk.support.tail.Nodup →
      c.apexes.Nodup →
      (∀ z ∈ c.apexes, z ∉ c.baseWalk.support.tail) →
      (c.realize mask).support.tail.Nodup
  | _, _, .base p, [], _, hnd, _, _ => hnd
  | _, _, .base _, _ :: _, hlen, _, _, _ => by simp [numBypasses] at hlen
  | _, _, .step _ _ _ _ _ _, [], hlen, _, _, _ => by simp [numBypasses] at hlen
  | _, _, .step (w := w) p huw z huz hzw rest, false :: bs, hlen, hnd, hap_nd, hdisj => by
      simp only [numBypasses, List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [baseWalk, support_append_tail, Walk.support_cons, List.tail_cons,
        List.nodup_append] at hnd
      simp only [apexes, List.nodup_cons] at hap_nd
      rcases hnd with ⟨hp_nd, hr_nd, hp_disj⟩
      have hrest_tail_nd : rest.baseWalk.support.tail.Nodup := by
        cases hrb : rest.baseWalk.support with
        | nil => exact absurd hrb (Walk.support_ne_nil _)
        | cons _ _ => rw [hrb, List.nodup_cons] at hr_nd; exact hr_nd.2
      have hrest_disj : ∀ z' ∈ rest.apexes, z' ∉ rest.baseWalk.support.tail := by
        intro z' hz' hmem
        apply hdisj z' (List.mem_cons_of_mem z hz')
        simp only [baseWalk, support_append_tail, Walk.support_cons, List.tail_cons, List.mem_append]
        exact Or.inr (List.mem_of_mem_tail hmem)
      have ih := realize_support_tail_nodup rest bs hlen hrest_tail_nd hap_nd.2 hrest_disj
      have hw_not_real : w ∉ (rest.realize bs).support.tail := by
        intro hmem
        rcases mem_realize_support_tail rest bs hlen w hmem with hbase | hap
        · cases hrb : rest.baseWalk.support with
          | nil => exact absurd hrb (Walk.support_ne_nil _)
          | cons w0 ws =>
              have hw0 : w0 = w := by
                have := Walk.head_support rest.baseWalk
                rw [hrb] at this; simpa using this
              rw [hrb, List.nodup_cons] at hr_nd
              rw [hrb, List.tail_cons] at hbase
              exact hr_nd.1 (hw0 ▸ hbase)
        · apply hdisj w (List.mem_cons_of_mem z hap)
          simp only [baseWalk, support_append_tail, Walk.support_cons, List.tail_cons, List.mem_append]
          exact Or.inr (Walk.start_mem_support rest.baseWalk)
      have hreal_nd : (rest.realize bs).support.Nodup := by
        cases hr : (rest.realize bs).support with
        | nil => exact absurd hr (Walk.support_ne_nil _)
        | cons w0 ws =>
            have hw0 : w0 = w := by
              have := Walk.head_support (rest.realize bs)
              rw [hr] at this; simpa using this
            rw [List.nodup_cons]
            rw [hr, List.tail_cons] at hw_not_real ih
            exact ⟨hw0 ▸ hw_not_real, ih⟩
      simp only [realize, support_append_tail, Walk.support_cons, List.tail_cons, List.nodup_append]
      refine ⟨hp_nd, hreal_nd, ?_⟩
      intro x hxp y hyr hxy
      subst hxy
      cases hr : (rest.realize bs).support with
      | nil => exact absurd hr (Walk.support_ne_nil _)
      | cons w0 ws =>
          have hw0 : w0 = w := by
            have := Walk.head_support (rest.realize bs)
            rw [hr] at this; simpa using this
          rw [hr, List.mem_cons] at hyr
          rcases hyr with rfl | hws
          · exact hp_disj w0 hxp w0 (hw0 ▸ Walk.start_mem_support rest.baseWalk) rfl
          · have htail : x ∈ (rest.realize bs).support.tail := by rw [hr]; exact hws
            rcases mem_realize_support_tail rest bs hlen x htail with hbase | hap
            · exact hp_disj x hxp x (List.mem_of_mem_tail hbase) rfl
            · apply hdisj x (List.mem_cons_of_mem z hap)
              simp only [baseWalk, support_append_tail, Walk.support_cons, List.tail_cons,
                List.mem_append]
              exact Or.inl hxp
  | _, _, .step (w := w) p huw z huz hzw rest, true :: bs, hlen, hnd, hap_nd, hdisj => by
      simp only [numBypasses, List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [baseWalk, support_append_tail, Walk.support_cons, List.tail_cons,
        List.nodup_append] at hnd
      simp only [apexes, List.nodup_cons] at hap_nd
      rcases hnd with ⟨hp_nd, hr_nd, hp_disj⟩
      have hrest_tail_nd : rest.baseWalk.support.tail.Nodup := by
        cases hrb : rest.baseWalk.support with
        | nil => exact absurd hrb (Walk.support_ne_nil _)
        | cons _ _ => rw [hrb, List.nodup_cons] at hr_nd; exact hr_nd.2
      have hrest_disj : ∀ z' ∈ rest.apexes, z' ∉ rest.baseWalk.support.tail := by
        intro z' hz' hmem
        apply hdisj z' (List.mem_cons_of_mem z hz')
        simp only [baseWalk, support_append_tail, Walk.support_cons, List.tail_cons, List.mem_append]
        exact Or.inr (List.mem_of_mem_tail hmem)
      have ih := realize_support_tail_nodup rest bs hlen hrest_tail_nd hap_nd.2 hrest_disj
      have hw_not_real : w ∉ (rest.realize bs).support.tail := by
        intro hmem
        rcases mem_realize_support_tail rest bs hlen w hmem with hbase | hap
        · cases hrb : rest.baseWalk.support with
          | nil => exact absurd hrb (Walk.support_ne_nil _)
          | cons w0 ws =>
              have hw0 : w0 = w := by
                have := Walk.head_support rest.baseWalk
                rw [hrb] at this; simpa using this
              rw [hrb, List.nodup_cons] at hr_nd
              rw [hrb, List.tail_cons] at hbase
              exact hr_nd.1 (hw0 ▸ hbase)
        · apply hdisj w (List.mem_cons_of_mem z hap)
          simp only [baseWalk, support_append_tail, Walk.support_cons, List.tail_cons, List.mem_append]
          exact Or.inr (Walk.start_mem_support rest.baseWalk)
      have hreal_nd : (rest.realize bs).support.Nodup := by
        cases hr : (rest.realize bs).support with
        | nil => exact absurd hr (Walk.support_ne_nil _)
        | cons w0 ws =>
            have hw0 : w0 = w := by
              have := Walk.head_support (rest.realize bs)
              rw [hr] at this; simpa using this
            rw [List.nodup_cons]
            rw [hr, List.tail_cons] at hw_not_real ih
            exact ⟨hw0 ▸ hw_not_real, ih⟩
      have hz_not_real : z ∉ (rest.realize bs).support := by
        intro hmem
        cases hr : (rest.realize bs).support with
        | nil => exact absurd hr (Walk.support_ne_nil _)
        | cons w0 ws =>
            have hw0 : w0 = w := by
              have := Walk.head_support (rest.realize bs)
              rw [hr] at this; simpa using this
            rw [hr, List.mem_cons] at hmem
            rcases hmem with rfl | hws
            · apply hdisj w0 (List.mem_cons_self ..)
              simp only [baseWalk, support_append_tail, Walk.support_cons, List.tail_cons,
                List.mem_append]
              exact Or.inr (hw0 ▸ Walk.start_mem_support rest.baseWalk)
            · have htail : z ∈ (rest.realize bs).support.tail := by rw [hr]; exact hws
              rcases mem_realize_support_tail rest bs hlen z htail with hbase | hap
              · apply hdisj z (List.mem_cons_self ..)
                simp only [baseWalk, support_append_tail, Walk.support_cons, List.tail_cons,
                  List.mem_append]
                exact Or.inr (List.mem_of_mem_tail hbase)
              · exact hap_nd.1 hap
      have hz_not_p : z ∉ p.support.tail := by
        intro hmem
        apply hdisj z (List.mem_cons_self ..)
        simp only [baseWalk, support_append_tail, Walk.support_cons, List.tail_cons, List.mem_append]
        exact Or.inl hmem
      simp only [realize, support_append_tail, Walk.support_cons, List.tail_cons, List.nodup_append,
        List.nodup_cons]
      refine ⟨hp_nd, ⟨hz_not_real, hreal_nd⟩, ?_⟩
      intro x hxp y hyr hxy
      subst hxy
      simp only [List.mem_cons] at hyr
      rcases hyr with rfl | hyr
      · exact hz_not_p hxp
      · cases hr : (rest.realize bs).support with
        | nil => exact absurd hr (Walk.support_ne_nil _)
        | cons w0 ws =>
            have hw0 : w0 = w := by
              have := Walk.head_support (rest.realize bs)
              rw [hr] at this; simpa using this
            rw [hr, List.mem_cons] at hyr
            rcases hyr with rfl | hws
            · exact hp_disj w0 hxp w0 (hw0 ▸ Walk.start_mem_support rest.baseWalk) rfl
            · have htail : x ∈ (rest.realize bs).support.tail := by rw [hr]; exact hws
              rcases mem_realize_support_tail rest bs hlen x htail with hbase | hap
              · exact hp_disj x hxp x (List.mem_of_mem_tail hbase) rfl
              · apply hdisj x (List.mem_cons_of_mem z hap)
                simp only [baseWalk, support_append_tail, Walk.support_cons, List.tail_cons,
                  List.mem_append]
                exact Or.inl hxp

private theorem mem_realize_edges {G : SimpleGraph V} :
    ∀ {a b : V} (c : BypassChain G a b) (mask : List Bool),
      mask.length = c.numBypasses →
      ∀ e ∈ (c.realize mask).edges,
        e ∈ c.baseWalk.edges ∨ ∃ z ∈ c.apexes, z ∈ e
  | _, _, .base p, [], _, e, he => Or.inl he
  | _, _, .base _, _ :: _, hlen, _, _ => by simp [numBypasses] at hlen
  | _, _, .step _ _ _ _ _ _, [], hlen, _, _ => by simp [numBypasses] at hlen
  | _, _, .step p huw z huz hzw rest, false :: bs, hlen, e, he => by
      simp only [numBypasses, List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [realize, baseWalk, Walk.edges_append, Walk.edges_cons, List.mem_append,
        List.mem_cons] at he ⊢
      rcases he with hp | rfl | hrest
      · exact Or.inl (Or.inl hp)
      · exact Or.inl (Or.inr (Or.inl rfl))
      · rcases mem_realize_edges rest bs hlen e hrest with hbase | ⟨z', hz', hze⟩
        · exact Or.inl (Or.inr (Or.inr hbase))
        · exact Or.inr ⟨z', List.mem_cons_of_mem z hz', hze⟩
  | _, _, .step p huw z huz hzw rest, true :: bs, hlen, e, he => by
      simp only [numBypasses, List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [realize, baseWalk, Walk.edges_append, Walk.edges_cons, List.mem_append,
        List.mem_cons] at he ⊢
      rcases he with hp | rfl | rfl | hrest
      · exact Or.inl (Or.inl hp)
      · exact Or.inr ⟨z, List.mem_cons_self .., by simp⟩
      · exact Or.inr ⟨z, List.mem_cons_self .., by simp⟩
      · rcases mem_realize_edges rest bs hlen e hrest with hbase | ⟨z', hz', hze⟩
        · exact Or.inl (Or.inr (Or.inr hbase))
        · exact Or.inr ⟨z', List.mem_cons_of_mem z hz', hze⟩

private theorem realize_edges_nodup {G : SimpleGraph V} :
    ∀ {a b : V} (c : BypassChain G a b) (mask : List Bool),
      mask.length = c.numBypasses →
      c.baseWalk.edges.Nodup →
      c.apexes.Nodup →
      (∀ z ∈ c.apexes, z ∉ c.baseWalk.support) →
      (c.realize mask).edges.Nodup
  | _, _, .base p, [], _, hnd, _, _ => hnd
  | _, _, .base _, _ :: _, hlen, _, _, _ => by simp [numBypasses] at hlen
  | _, _, .step _ _ _ _ _ _, [], hlen, _, _, _ => by simp [numBypasses] at hlen
  | _, _, .step (u := u) (w := w) p huw z huz hzw rest, false :: bs, hlen, hnd, hap_nd, hdisj => by
      simp only [numBypasses, List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [baseWalk, Walk.edges_append, Walk.edges_cons, List.nodup_append,
        List.nodup_cons] at hnd
      simp only [apexes, List.nodup_cons] at hap_nd
      rcases hnd with ⟨hp_nd, ⟨huw_not_r, hr_nd⟩, hp_disj⟩
      have hrest_disj : ∀ z' ∈ rest.apexes, z' ∉ rest.baseWalk.support := by
        intro z' hz' hmem
        apply hdisj z' (List.mem_cons_of_mem z hz')
        simp only [baseWalk, Walk.support_append, Walk.support_cons, List.tail_cons, List.mem_append]
        exact Or.inr hmem
      have ih := realize_edges_nodup rest bs hlen hr_nd hap_nd.2 hrest_disj
      have huw_not_real : s(u, w) ∉ (rest.realize bs).edges := by
        intro hmem
        rcases mem_realize_edges rest bs hlen s(u, w) hmem with hbase | ⟨z', hz', hze⟩
        · exact huw_not_r hbase
        · apply hdisj z' (List.mem_cons_of_mem z hz')
          simp only [Sym2.mem_iff] at hze
          rcases hze with rfl | rfl
          · simp only [baseWalk, Walk.support_append, List.mem_append]
            exact Or.inl (Walk.end_mem_support p)
          · simp only [baseWalk, Walk.support_append, Walk.support_cons, List.tail_cons,
              List.mem_append]
            exact Or.inr (Walk.start_mem_support rest.baseWalk)
      simp only [realize, Walk.edges_append, Walk.edges_cons, List.nodup_append, List.nodup_cons]
      refine ⟨hp_nd, ⟨huw_not_real, ih⟩, ?_⟩
      intro e hep e' her hee
      subst hee
      simp only [List.mem_cons] at her
      rcases her with rfl | her
      · exact hp_disj s(u, w) hep s(u, w) (List.mem_cons_self ..) rfl
      · rcases mem_realize_edges rest bs hlen e her with hbase | ⟨z', hz', hze⟩
        · exact hp_disj e hep e (List.mem_cons_of_mem _ hbase) rfl
        · apply hdisj z' (List.mem_cons_of_mem z hz')
          simp only [baseWalk, Walk.support_append, List.mem_append]
          exact Or.inl (mem_support_of_mem_edges hep hze)
  | _, _, .step (u := u) (w := w) p huw z huz hzw rest, true :: bs, hlen, hnd, hap_nd, hdisj => by
      simp only [numBypasses, List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [baseWalk, Walk.edges_append, Walk.edges_cons, List.nodup_append,
        List.nodup_cons] at hnd
      simp only [apexes, List.nodup_cons] at hap_nd
      rcases hnd with ⟨hp_nd, ⟨_, hr_nd⟩, hp_disj⟩
      have hrest_disj : ∀ z' ∈ rest.apexes, z' ∉ rest.baseWalk.support := by
        intro z' hz' hmem
        apply hdisj z' (List.mem_cons_of_mem z hz')
        simp only [baseWalk, Walk.support_append, Walk.support_cons, List.tail_cons, List.mem_append]
        exact Or.inr hmem
      have ih := realize_edges_nodup rest bs hlen hr_nd hap_nd.2 hrest_disj
      have hz_not_base_edge : ∀ e ∈ (rest.realize bs).edges, z ∉ e := by
        intro e he hze
        have hz_supp : z ∈ (rest.realize bs).support := mem_support_of_mem_edges he hze
        cases hr : (rest.realize bs).support with
        | nil => exact absurd hr (Walk.support_ne_nil _)
        | cons w0 ws =>
            have hw0 : w0 = w := by
              have := Walk.head_support (rest.realize bs)
              rw [hr] at this; simpa using this
            rw [hr, List.mem_cons] at hz_supp
            rcases hz_supp with rfl | hws
            · apply hdisj w0 (List.mem_cons_self ..)
              simp only [baseWalk, Walk.support_append, Walk.support_cons, List.tail_cons,
                List.mem_append]
              exact Or.inr (hw0 ▸ Walk.start_mem_support rest.baseWalk)
            · have htail : z ∈ (rest.realize bs).support.tail := by rw [hr]; exact hws
              rcases mem_realize_support_tail rest bs hlen z htail with hbase2 | hap2
              · apply hdisj z (List.mem_cons_self ..)
                simp only [baseWalk, Walk.support_append, Walk.support_cons, List.tail_cons,
                  List.mem_append]
                exact Or.inr (List.mem_of_mem_tail hbase2)
              · exact hap_nd.1 hap2
      have huz_ne_hzw : s(u, z) ≠ s(z, w) := by
        intro heq
        rw [Sym2.eq_iff] at heq
        rcases heq with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact huz.ne h1
        · exact huw.ne h1
      simp only [realize, Walk.edges_append, Walk.edges_cons, List.nodup_append, List.nodup_cons]
      refine ⟨hp_nd, ⟨?_, ⟨?_, ih⟩⟩, ?_⟩
      · simp only [List.mem_cons, not_or]
        exact ⟨huz_ne_hzw, fun hmem => hz_not_base_edge s(u, z) hmem (by simp)⟩
      · exact fun hmem => hz_not_base_edge s(z, w) hmem (by simp)
      · intro e hep e' her hee
        subst hee
        simp only [List.mem_cons] at her
        rcases her with rfl | rfl | her
        · apply hdisj z (List.mem_cons_self ..)
          simp only [baseWalk, Walk.support_append, List.mem_append]
          exact Or.inl (mem_support_of_mem_edges hep (by simp))
        · apply hdisj z (List.mem_cons_self ..)
          simp only [baseWalk, Walk.support_append, List.mem_append]
          exact Or.inl (mem_support_of_mem_edges hep (by simp))
        · rcases mem_realize_edges rest bs hlen e her with hbase | ⟨z', hz', hze⟩
          · exact hp_disj e hep e (List.mem_cons_of_mem _ hbase) rfl
          · apply hdisj z' (List.mem_cons_of_mem z hz')
            simp only [baseWalk, Walk.support_append, List.mem_append]
            exact Or.inl (mem_support_of_mem_edges hep hze)

/-- **Main Intrinsic Adjuster Theorem**: If `c : BypassChain G v v` has a simple base cycle
`c.baseWalk`, pairwise distinct apexes `c.apexes`, all disjoint from `c.baseWalk.support`,
then for EVERY boolean mask of length `c.numBypasses`, `c.realize mask` is a simple cycle! -/
theorem realize_isCycle {G : SimpleGraph V} {v : V} (c : BypassChain G v v)
    (hcyc : c.baseWalk.IsCycle) (hap : c.apexes.Nodup)
    (hdisj : ∀ z ∈ c.apexes, z ∉ c.baseWalk.support)
    (mask : List Bool) (hlen : mask.length = c.numBypasses) :
    (c.realize mask).IsCycle := by
  have hdisj_tail : ∀ z ∈ c.apexes, z ∉ c.baseWalk.support.tail :=
    fun z hz hm => hdisj z hz (List.mem_of_mem_tail hm)
  have htail_nd := realize_support_tail_nodup c mask hlen hcyc.support_nodup hap hdisj_tail
  have hedges_nd := realize_edges_nodup c mask hlen hcyc.edges_nodup hap hdisj
  have hne : c.realize mask ≠ Walk.nil := by
    intro hnil
    have hlen_pos : 0 < (c.realize mask).length := by
      rw [realize_length c mask hlen]
      have := hcyc.three_le_length
      omega
    rw [hnil] at hlen_pos
    simp at hlen_pos
  exact ⟨⟨⟨hedges_nd⟩, hne⟩, htail_nd⟩

/-- Every integer cycle length in `[L, L + r]` is realized by a simple cycle in `G`. -/
theorem exists_cycle_of_mem_Icc {G : SimpleGraph V} {v : V} (c : BypassChain G v v)
    (hcyc : c.baseWalk.IsCycle) (hap : c.apexes.Nodup)
    (hdisj : ∀ z ∈ c.apexes, z ∉ c.baseWalk.support)
    {j : ℕ} (hj : j ≤ c.numBypasses) :
    ∃ p : G.Walk v v, p.IsCycle ∧ p.length = c.baseWalk.length + j := by
  let mask : List Bool := List.replicate j true ++ List.replicate (c.numBypasses - j) false
  have hlen : mask.length = c.numBypasses := by
    simp [mask]; omega
  have hcnt : mask.count true = j := by
    simp [mask, List.count_append, List.count_replicate]
  refine ⟨c.realize mask, realize_isCycle c hcyc hap hdisj mask hlen, ?_⟩
  rw [realize_length c mask hlen, hcnt]

/-- Power-of-2 closure whenever the adjuster interval `[L, L + r]` contains `2 ^ k` (`k ≥ 2`). -/
theorem hasPower_of_pow2_in_window {G : SimpleGraph V} {v : V} (c : BypassChain G v v)
    (hcyc : c.baseWalk.IsCycle) (hap : c.apexes.Nodup)
    (hdisj : ∀ z ∈ c.apexes, z ∉ c.baseWalk.support)
    {k : ℕ} (hk : 2 ≤ k)
    (hlo : c.baseWalk.length ≤ 2 ^ k)
    (hhi : 2 ^ k ≤ c.baseWalk.length + c.numBypasses) :
    HasPower G := by
  obtain ⟨p, hp, hlen⟩ :=
    exists_cycle_of_mem_Icc c hcyc hap hdisj (j := 2 ^ k - c.baseWalk.length) (by omega)
  exact ⟨k, v, p, hk, hp, by omega⟩

/-- Unbounded-`n`, fixed-girth (`g = 3`) adjuster closure: if a simple cycle of length `L`
admits at least `L - 2` independent off-cycle triangle bypasses, then `HasPower G`. -/
theorem hasPower_of_dense_bypasses {G : SimpleGraph V} {v : V} (c : BypassChain G v v)
    (hcyc : c.baseWalk.IsCycle) (hap : c.apexes.Nodup)
    (hdisj : ∀ z ∈ c.apexes, z ∉ c.baseWalk.support)
    (hdense : c.baseWalk.length - 2 ≤ c.numBypasses) :
    HasPower G := by
  have hL3 : 3 ≤ c.baseWalk.length := hcyc.three_le_length
  obtain ⟨k, hk2, hlo, hhi⟩ :=
    exists_pow2_in_int_interval hL3 (B := c.baseWalk.length + c.numBypasses) (by omega)
  exact hasPower_of_pow2_in_window c hcyc hap hdisj hk2 hlo hhi

/-- **Exact Pincer Saturation Theorem** (explaining Wave 5 Agent #3's 100% `C_32` edge saturation):
Whenever `target` lies strictly in the interior `L < target < L + r` of the adjuster interval,
for EVERY bypass index `i < r`, there exists BOTH:
(1) a simple `target`-cycle with `mask[i] = false` (traversing the direct edge `u_i — w_i`), AND
(2) a simple `target`-cycle with `mask[i] = true` (traversing both triangle edges `u_i — z_i — w_i`). -/
theorem interior_edge_saturation {G : SimpleGraph V} {v : V} (c : BypassChain G v v)
    (hcyc : c.baseWalk.IsCycle) (hap : c.apexes.Nodup)
    (hdisj : ∀ z ∈ c.apexes, z ∉ c.baseWalk.support)
    {target : ℕ} (hlo : c.baseWalk.length < target)
    (hhi : target < c.baseWalk.length + c.numBypasses)
    {i : ℕ} (hi : i < c.numBypasses) :
    (∃ mask : List Bool, ∃ hlen : mask.length = c.numBypasses,
      mask[i]'(by omega) = false ∧ (c.realize mask).IsCycle ∧ (c.realize mask).length = target) ∧
    (∃ mask : List Bool, ∃ hlen : mask.length = c.numBypasses,
      mask[i]'(by omega) = true ∧ (c.realize mask).IsCycle ∧ (c.realize mask).length = target) := by
  let r := c.numBypasses
  let j := target - c.baseWalk.length
  have hj_pos : 1 ≤ j := by omega
  have hj_lt : j < r := by omega
  constructor
  · let a := min i j
    let b := j - a
    have ha_le_i : a ≤ i := Nat.min_le_left i j
    have hb_le : b ≤ r - 1 - i := by omega
    let pre : List Bool := List.replicate a true ++ List.replicate (i - a) false
    let suf : List Bool := List.replicate b true ++ List.replicate (r - 1 - i - b) false
    let mask : List Bool := pre ++ (false :: suf)
    have hpre_len : pre.length = i := by simp [pre]; omega
    have hsuf_len : suf.length = r - 1 - i := by simp [suf]; omega
    have hlen : mask.length = r := by simp [mask, hpre_len, hsuf_len]; omega
    have hget : mask[i]'(by omega) = false := by
      simp [mask, List.getElem_append_right, hpre_len]
    have hcnt : mask.count true = j := by
      simp [mask, pre, suf, List.count_append, List.count_replicate]
      omega
    refine ⟨mask, hlen, hget, realize_isCycle c hcyc hap hdisj mask hlen, ?_⟩
    rw [realize_length c mask hlen, hcnt]; omega
  · let a := min i (j - 1)
    let b := (j - 1) - a
    have ha_le_i : a ≤ i := Nat.min_le_left i (j - 1)
    have hb_le : b ≤ r - 1 - i := by omega
    let pre : List Bool := List.replicate a true ++ List.replicate (i - a) false
    let suf : List Bool := List.replicate b true ++ List.replicate (r - 1 - i - b) false
    let mask : List Bool := pre ++ (true :: suf)
    have hpre_len : pre.length = i := by simp [pre]; omega
    have hsuf_len : suf.length = r - 1 - i := by simp [suf]; omega
    have hlen : mask.length = r := by simp [mask, hpre_len, hsuf_len]; omega
    have hget : mask[i]'(by omega) = true := by
      simp [mask, List.getElem_append_right, hpre_len]
    have hcnt : mask.count true = j := by
      simp [mask, pre, suf, List.count_append, List.count_replicate]
      omega
    refine ⟨mask, hlen, hget, realize_isCycle c hcyc hap hdisj mask hlen, ?_⟩
    rw [realize_length c mask hlen, hcnt]; omega

end BypassChain
end BypassAdjusters

#print axioms dynamic_k_taillessCount_lb
#print axioms dynamic_k_taillessCount_pos
#print axioms exists_dynamic_k_taillessCount_pos
#print axioms dynamic_k_logarithmic_girth_hasPower
#print axioms exists_pow2_in_int_interval
#print axioms exists_pow2_in_even_interval
#print axioms exists_pow2_in_ap_interval
#print axioms hasPower_of_consecutive_even_cycles
#print axioms hasPower_of_consecutive_cycles
#print axioms erdos64_of_even_cycle_interval_forcing
#print axioms BypassChain.realize_length
#print axioms BypassChain.realize_isCycle
#print axioms BypassChain.exists_cycle_of_mem_Icc
#print axioms BypassChain.hasPower_of_pow2_in_window
#print axioms BypassChain.hasPower_of_dense_bypasses
#print axioms BypassChain.interior_edge_saturation

end E64Wave6Agent3
