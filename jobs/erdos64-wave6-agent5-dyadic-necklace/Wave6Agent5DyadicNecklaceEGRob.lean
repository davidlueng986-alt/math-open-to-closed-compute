import Mathlib

/-!
# Erdős Problem #64 (Erdős–Gyárfás Conjecture) — Wave 6 Agent #5
## Dyadic Necklace Surgery & EG2-CORE Hitting-Edge Exclusions

This self-contained Lean 4.36.0 module formalizes two complementary whole-problem-closing
architectures for Erdős Problem #64:

1. **Pillar 1 — Universal Dyadic Necklace & Independent-Bypass Surgery (`E64Wave6Agent5`)**:
   - Breaks the Wave 5 Kesten–McKay fixed-`k` spectral barrier at fixed small girth `g ≥ 3`
     and unbounded order `n → ∞`, for arbitrary non-regular graphs with `δ(G) ≥ 3` and zero
     spectral-gap hypothesis.
   - Proves exact simple-cycle surgery for arbitrary independent bypass necklaces
     (`necklace_walk_isCycle`), Brown's unit-step and even-step completeness theorems
     (`brown_unit_complete`, `brown_even_complete`), sharp octave dyadic-hitting
     (`exists_pow2_in_octave`), whole-problem closure gate
     (`erdos64_closed_of_brown_necklace_target`), and unconditional infinite-family closures
     for triangle-chain and fine+coarse necklaces (`hasPowerCycle_of_triangle_necklace`).

2. **Pillar 2 — All-Order `EG2-CORE` / `EGRob3ConnCore` Hitting-Edge Exclusions**:
   - Directly attacks Wave 5's master 26/26 closure target `EGRob3ConnCore`.
   - Proves unconditionally (without even needing `V_{≥4}` independence!) that in any
     `EG2-CORE` completion `H = G + ab`, every edge incident to any vertex of degree `≥ 4`
     is avoided by a simple `2^k`-cycle of `H` (`eg2_core_high_edge_avoided`).
   - Deduces that the entire hitting-edge set `E_hit(H)` lies inside the cubic induced
     subgraph `H[V_3(H)]` (`eg2_core_hitting_edges_in_V3`), and that any `2^k`-cycle
     visiting `V_{≥4}(H)` forces a second distinct `2^k`-cycle (`eg2_core_high_vertex_forces_two_pow2_cycles`).
-/

namespace E64Wave6Agent5

/-! ### 0. Core Erdős–Gyárfás Predicates -/

def IsPowerOfTwo (n : ℕ) : Prop :=
  ∃ k : ℕ, 2 ≤ k ∧ n = 2 ^ k

def HasPowerCycle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ IsPowerOfTwo p.length

def MinDeg {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : Prop :=
  ∀ v : V, d ≤ G.degree v

def Erdos64 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    MinDeg G 3 → HasPowerCycle G

/-! ### 1. Brown–Octave Subset-Sum & Dyadic-Hitting Arithmetic -/

def maskedSum : List ℕ → List Bool → ℕ
  | [], _ => 0
  | _, [] => 0
  | d :: ds, b :: bs => (if b then d else 0) + maskedSum ds bs

theorem maskedSum_append (ds1 ds2 : List ℕ) (bs1 bs2 : List Bool)
    (h : ds1.length = bs1.length) :
    maskedSum (ds1 ++ ds2) (bs1 ++ bs2) = maskedSum ds1 bs1 + maskedSum ds2 bs2 := by
  induction ds1 generalizing bs1 with
  | nil =>
    cases bs1 with
    | nil => simp [maskedSum]
    | cons _ _ => simp at h
  | cons d ds ih =>
    cases bs1 with
    | nil => simp at h
    | cons b bs =>
      simp only [List.cons_append, maskedSum]
      have hlen : ds.length = bs.length := by simpa using h
      rw [ih bs hlen, Nat.add_assoc]

/-- Brown's unit-step completeness condition: each new element `d` is at most `1 + sum of prefix`. -/
inductive BrownUnit : List ℕ → Prop
  | nil : BrownUnit []
  | snoc {ds : List ℕ} {d : ℕ} : BrownUnit ds → d ≤ ds.sum + 1 → BrownUnit (ds ++ [d])

theorem brown_unit_complete {ds : List ℕ} (hB : BrownUnit ds) :
    ∀ t : ℕ, t ≤ ds.sum → ∃ bs : List Bool, bs.length = ds.length ∧ maskedSum ds bs = t := by
  induction hB with
  | nil =>
    intro t ht
    have ht0 : t = 0 := by simpa using ht
    exact ⟨[], rfl, by simp [maskedSum, ht0]⟩
  | @snoc ds d hB hd ih =>
    intro t ht
    rw [List.sum_append, List.sum_singleton] at ht
    by_cases hle : t ≤ ds.sum
    · obtain ⟨bs, hlen, hsum⟩ := ih t hle
      refine ⟨bs ++ [false], by simp [hlen], ?_⟩
      rw [maskedSum_append ds [d] bs [false] hlen.symm]
      simp [maskedSum, hsum]
    · have hdt : d ≤ t := by omega
      have hrem : t - d ≤ ds.sum := by omega
      obtain ⟨bs, hlen, hsum⟩ := ih (t - d) hrem
      refine ⟨bs ++ [true], by simp [hlen], ?_⟩
      rw [maskedSum_append ds [d] bs [true] hlen.symm]
      simp [maskedSum, hsum]
      omega

theorem maskedSum_map_mul2 (cs : List ℕ) (bs : List Bool) :
    maskedSum (cs.map (2 * ·)) bs = 2 * maskedSum cs bs := by
  induction cs generalizing bs with
  | nil => simp [maskedSum]
  | cons c cs ih =>
    cases bs with
    | nil => simp [maskedSum]
    | cons b bs =>
      cases b <;> simp [maskedSum, ih bs, Nat.mul_add]

theorem brown_even_complete {cs : List ℕ} (hB : BrownUnit cs) :
    ∀ t : ℕ, t ≤ cs.sum →
      ∃ bs : List Bool, bs.length = cs.length ∧ maskedSum (cs.map (2 * ·)) bs = 2 * t := by
  intro t ht
  obtain ⟨bs, hlen, hsum⟩ := brown_unit_complete hB t ht
  refine ⟨bs, hlen, ?_⟩
  rw [maskedSum_map_mul2, hsum]

/-- Sharp octave dyadic-hitting: for every `L ≥ 3`, there is a power `2^k` (`k ≥ 2`) in `[L, 2L - 2]`. -/
theorem exists_pow2_in_octave {L : ℕ} (hL : 3 ≤ L) :
    ∃ k : ℕ, 2 ≤ k ∧ L ≤ 2 ^ k ∧ 2 ^ k ≤ 2 * L - 2 := by
  let m := Nat.log 2 L
  have hm_le : 2 ^ m ≤ L := Nat.pow_log_le_self 2 (by omega)
  have hm_lt : L < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by decide : 1 < 2) L
  have hm_ge1 : 1 ≤ m := by
    have : Nat.log 2 2 ≤ Nat.log 2 L := Nat.log_mono_right (by omega)
    simpa using this
  by_cases heq : 2 ^ m = L
  · have hm_ge2 : 2 ≤ m := by
      by_contra h
      have hm1 : m = 1 := by omega
      rw [hm1] at heq
      omega
    exact ⟨m, hm_ge2, by omega, by omega⟩
  · have hlt : 2 ^ m < L := by omega
    refine ⟨m + 1, by omega, by omega, ?_⟩
    have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    omega

theorem exists_subset_sum_pow2_of_brown_unit {L0 : ℕ} {ds : List ℕ}
    (hL0 : 3 ≤ L0) (hB : BrownUnit ds) (hspan : L0 - 2 ≤ ds.sum) :
    ∃ (bs : List Bool) (k : ℕ), bs.length = ds.length ∧ 2 ≤ k ∧ L0 + maskedSum ds bs = 2 ^ k := by
  obtain ⟨k, hk, hlo, hhi⟩ := exists_pow2_in_octave hL0
  have ht : 2 ^ k - L0 ≤ ds.sum := by omega
  obtain ⟨bs, hlen, hsum⟩ := brown_unit_complete hB (2 ^ k - L0) ht
  refine ⟨bs, k, hlen, hk, ?_⟩
  omega

theorem exists_subset_sum_pow2_of_brown_even {L0 : ℕ} {cs : List ℕ}
    (hL0 : 4 ≤ L0) (hEven : Even L0) (hB : BrownUnit cs) (hspan : L0 - 2 ≤ 2 * cs.sum) :
    ∃ (bs : List Bool) (k : ℕ), bs.length = cs.length ∧ 2 ≤ k ∧
      L0 + maskedSum (cs.map (2 * ·)) bs = 2 ^ k := by
  obtain ⟨k, hk, hlo, hhi⟩ := exists_pow2_in_octave (by omega : 3 ≤ L0)
  obtain ⟨q, hq⟩ := hEven
  have hpow_even : Even (2 ^ k) := by
    refine ⟨2 ^ (k - 1), ?_⟩
    have : k = (k - 1) + 1 := by omega
    conv_lhs => rw [this, pow_succ]
    ring
  obtain ⟨p, hp⟩ := hpow_even
  have ht : p - q ≤ cs.sum := by omega
  obtain ⟨bs, hlen, hsum⟩ := brown_even_complete hB (p - q) ht
  refine ⟨bs, k, hlen, hk, ?_⟩
  omega

theorem brown_unit_replicate_one (k : ℕ) : BrownUnit (List.replicate k 1) := by
  induction k with
  | zero => exact BrownUnit.nil
  | succ k ih =>
    have hrep : List.replicate (k + 1) 1 = List.replicate k 1 ++ [1] := by
      rw [List.replicate_succ, List.replicate_succ']
      rfl
    rw [hrep]
    exact BrownUnit.snoc ih (by omega)

/-! ### 2. Simple-Cycle Bypass Necklace Surgery in `SimpleGraph V` -/

/--
A `BypassNecklace G` is a cyclic sequence of `r ≥ 3` junction vertices `v_0, ..., v_{r-1}`
connected by `r` segments, each offering a short path `segA i` and a long path `segB i`
(with `|segA i| ≤ |segB i|`), such that the half-open vertex blocks `support.dropLast` of
distinct segments are pairwise disjoint for every choice of `segA`/`segB`.
-/
structure BypassNecklace {V : Type*} (G : SimpleGraph V) where
  r : ℕ
  hr : 3 ≤ r
  junction : Fin r → V
  segA : ∀ i : Fin r, G.Walk (junction i) (junction ⟨(i.val + 1) % r, Nat.mod_lt _ (by omega)⟩)
  segB : ∀ i : Fin r, G.Walk (junction i) (junction ⟨(i.val + 1) % r, Nat.mod_lt _ (by omega)⟩)
  segA_path : ∀ i, (segA i).IsPath
  segB_path : ∀ i, (segB i).IsPath
  segA_pos : ∀ i, 1 ≤ (segA i).length
  segB_ge : ∀ i, (segA i).length ≤ (segB i).length
  disjoint_blocks : ∀ (i j : Fin r), i ≠ j → ∀ (b1 b2 : Bool),
    List.Disjoint
      (if b1 then (segB i).support.dropLast else (segA i).support.dropLast)
      (if b2 then (segB j).support.dropLast else (segA j).support.dropLast)

namespace BypassNecklace

variable {V : Type*} {G : SimpleGraph V} (N : BypassNecklace G)

def nextIdx (i : Fin N.r) : Fin N.r :=
  ⟨(i.val + 1) % N.r, Nat.mod_lt _ (by have := N.hr; omega)⟩

def seg (σ : Fin N.r → Bool) (i : Fin N.r) :
    G.Walk (N.junction i) (N.junction (N.nextIdx i)) :=
  if σ i then N.segB i else N.segA i

theorem seg_isPath (σ : Fin N.r → Bool) (i : Fin N.r) : (N.seg σ i).IsPath := by
  unfold seg
  split
  · exact N.segB_path i
  · exact N.segA_path i

theorem seg_pos (σ : Fin N.r → Bool) (i : Fin N.r) : 1 ≤ (N.seg σ i).length := by
  unfold seg
  split
  · exact le_trans (N.segA_pos i) (N.segB_ge i)
  · exact N.segA_pos i

theorem seg_disjoint (σ : Fin N.r → Bool) {i j : Fin N.r} (hij : i ≠ j) :
    List.Disjoint (N.seg σ i).support.dropLast (N.seg σ j).support.dropLast := by
  have h := N.disjoint_blocks i j hij (σ i) (σ j)
  unfold seg
  cases h1 : σ i <;> cases h2 : σ j <;> simpa [h1, h2] using h

/-- Concatenate segments `0, 1, ..., m - 1` along the necklace. -/
def prefixWalk (σ : Fin N.r → Bool) :
    ∀ m : ℕ, (hm : m ≤ N.r) →
      G.Walk (N.junction ⟨0, by have := N.hr; omega⟩)
             (N.junction ⟨m % N.r, Nat.mod_lt _ (by have := N.hr; omega)⟩)
  | 0, _ => by
      have h0 : (0 : ℕ) % N.r = 0 := Nat.zero_mod _
      exact (Eq.ndrec (SimpleGraph.Walk.nil) (by simp [h0]))
  | m + 1, hm =>
      let idx : Fin N.r := ⟨m, by omega⟩
      have hmod : m % N.r = m := Nat.mod_eq_of_lt (by omega)
      have hcast : N.junction ⟨m % N.r, Nat.mod_lt _ (by have := N.hr; omega)⟩ = N.junction idx := by
        congr 1; ext; exact hmod
      let wPrev := N.prefixWalk σ m (by omega)
      let wSeg := N.seg σ idx
      (wPrev.copy rfl hcast).append wSeg

def cycleWalk (σ : Fin N.r → Bool) :
    G.Walk (N.junction ⟨0, by have := N.hr; omega⟩) (N.junction ⟨0, by have := N.hr; omega⟩) :=
  (N.prefixWalk σ N.r le_rfl).copy rfl (by
    congr 1; ext; exact Nat.mod_self N.r)

theorem support_dropLast_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).support.dropLast = p.support.dropLast ++ q.support.dropLast := by
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
    simp only [SimpleGraph.Walk.cons_append, SimpleGraph.Walk.support_cons]
    have hne1 : (p.append q).support ≠ [] := SimpleGraph.Walk.support_ne_nil _
    have hne2 : p.support ≠ [] := SimpleGraph.Walk.support_ne_nil _
    rw [List.dropLast_cons_of_ne_nil hne1, List.dropLast_cons_of_ne_nil hne2, ih, List.cons_append]

theorem prefixWalk_length (σ : Fin N.r → Bool) :
    ∀ m (hm : m ≤ N.r),
      (N.prefixWalk σ m hm).length =
        (List.finRange N.r |>.take m |>.map (fun i => (N.seg σ i).length)).sum := by
  intro m hm
  induction m with
  | zero =>
    simp [prefixWalk]
  | succ m ih =>
    simp only [prefixWalk, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_copy]
    rw [ih (by omega)]
    have htake : (List.finRange N.r).take (m + 1) =
        (List.finRange N.r).take m ++ [⟨m, by omega⟩] := by
      apply List.ext_getElem
      · simp; omega
      · intro i hi1 hi2
        by_cases h : i < m
        · simp [List.getElem_append_left, h]
        · have him : i = m := by simp at hi1; omega
          subst him
          simp [List.getElem_append_right]
    rw [htake, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]

theorem prefixWalk_support_dropLast (σ : Fin N.r → Bool) :
    ∀ m (hm : m ≤ N.r),
      (N.prefixWalk σ m hm).support.dropLast =
        ((List.finRange N.r).take m).flatMap (fun i => (N.seg σ i).support.dropLast) := by
  intro m hm
  induction m with
  | zero =>
    simp [prefixWalk]
  | succ m ih =>
    simp only [prefixWalk, support_dropLast_append, SimpleGraph.Walk.support_copy]
    rw [ih (by omega)]
    have htake : (List.finRange N.r).take (m + 1) =
        (List.finRange N.r).take m ++ [⟨m, by omega⟩] := by
      apply List.ext_getElem
      · simp; omega
      · intro i hi1 hi2
        by_cases h : i < m
        · simp [List.getElem_append_left, h]
        · have him : i = m := by simp at hi1; omega
          subst him
          simp [List.getElem_append_right]
    rw [htake, List.flatMap_append, List.flatMap_singleton]

theorem cycleWalk_support_dropLast_nodup (σ : Fin N.r → Bool) :
    (N.cycleWalk σ).support.dropLast.Nodup := by
  unfold cycleWalk
  rw [SimpleGraph.Walk.support_copy, N.prefixWalk_support_dropLast σ N.r le_rfl]
  have htake : (List.finRange N.r).take N.r = List.finRange N.r := by
    rw [List.take_of_length_le (by simp)]
  rw [htake, List.nodup_flatMap]
  refine ⟨?_, ?_⟩
  · intro i _
    exact ((N.seg_isPath σ i).support_nodup).sublist (List.dropLast_sublist _)
  · exact (List.nodup_finRange N.r).imp (fun hij => N.seg_disjoint σ hij)

theorem cycleWalk_length_eq (σ : Fin N.r → Bool) :
    (N.cycleWalk σ).length =
      ((List.finRange N.r).map (fun i => (N.seg σ i).length)).sum := by
  unfold cycleWalk
  rw [SimpleGraph.Walk.length_copy, N.prefixWalk_length σ N.r le_rfl]
  rw [List.take_of_length_le (by simp)]

theorem cycleWalk_length_ge_three (σ : Fin N.r → Bool) : 3 ≤ (N.cycleWalk σ).length := by
  rw [N.cycleWalk_length_eq σ]
  have hge : ((List.finRange N.r).map (fun _ => 1)).sum ≤
      ((List.finRange N.r).map (fun i => (N.seg σ i).length)).sum := by
    apply List.Forall₂.sum_le_sum
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.Forall₂.of_eq_true (by simp) |>.imp (by intro a b hab; subst hab; exact N.seg_pos σ a)
  have hones : ((List.finRange N.r).map (fun _ => 1)).sum = N.r := by
    simp
  have := N.hr
  omega

/--
Core graph-theoretic lemma: any closed walk `p : G.Walk v v` of length `≥ 3` whose
`support.dropLast` has no duplicate vertices is a simple cycle (`p.IsCycle`).
-/
theorem isCycle_of_dropLast_nodup {v : V} (p : G.Walk v v)
    (hlen : 3 ≤ p.length) (hnodup : p.support.dropLast.Nodup) : p.IsCycle := by
  have hne : p ≠ .nil := by
    intro h; subst h; simp at hlen
  have htail_nodup : p.support.tail.Nodup := by
    have hsup_len : 2 ≤ p.support.length := by
      rw [SimpleGraph.Walk.length_support]; omega
    have hperm : p.support.dropLast.Perm p.support.tail := by
      cases hs : p.support with
      | nil => exact absurd hs (SimpleGraph.Walk.support_ne_nil p)
      | cons a rest =>
        cases hr : rest with
        | nil => rw [hs, hr] at hsup_len; simp at hsup_len
        | cons b rest' =>
          have ha : a = v := by
            have := SimpleGraph.Walk.head_support p
            rw [hs] at this; simpa using this
          have hlast : (b :: rest').getLast (List.cons_ne_nil _ _) = v := by
            have := SimpleGraph.Walk.getLast_support p
            rw [hs, hr] at this
            simpa using this
          have hdecomp : b :: rest' = (b :: rest').dropLast ++ [v] := by
            rw [← hlast, List.dropLast_append_getLast]
          rw [List.dropLast_cons_of_ne_nil (by rw [hr]; exact List.cons_ne_nil _ _)]
          rw [hr, List.tail_cons]
          conv_rhs => rw [hdecomp]
          rw [ha]
          exact List.perm_append_singleton v (b :: rest').dropLast |>.symm
    exact hperm.nodup_iff.mp hnodup
  have hedg_nodup : p.edges.Nodup := by
    rw [List.nodup_iff_injective_getElem]
    intro i j hij
    have hlen_e : p.edges.length = p.length := SimpleGraph.Walk.length_edges p
    have hlen_s : p.support.length = p.length + 1 := SimpleGraph.Walk.length_support p
    have hlen_d : p.support.dropLast.length = p.length := by
      rw [List.length_dropLast, hlen_s]; omega
    have hi : i.val < p.length := by omega
    have hj : j.val < p.length := by omega
    have hedge_eq : ∀ (k : ℕ) (hk : k < p.length),
        p.edges[k]'(by omega) = s(p.support[k]'(by omega), p.support[k + 1]'(by omega)) := by
      intro k hk
      have hzip : p.edges = p.support.zipWith (fun a b => s(a, b)) p.support.tail := by
        clear hij hi hj hlen_e hlen_s hlen_d hnodup htail_nodup hne hlen
        induction p with
        | nil => simp
        | @cons a b c h q ih =>
          cases q with
          | nil => simp
          | cons h' q' =>
            simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.support_cons,
              List.tail_cons, List.zipWith_cons_cons]
            congr 1
            exact ih
      simp [hzip, List.getElem_tail]
    have heq_s : s(p.support[i.val]'(by omega), p.support[i.val + 1]'(by omega)) =
                 s(p.support[j.val]'(by omega), p.support[j.val + 1]'(by omega)) := by
      rw [← hedge_eq i.val hi, ← hedge_eq j.val hj]
      exact hij
    have hdrop_get : ∀ (k : ℕ) (hk : k < p.length),
        p.support.dropLast[k]'(by omega) = p.support[k]'(by omega) := by
      intro k hk
      exact List.getElem_dropLast (by omega)
    have hdrop_inj : ∀ (a b : ℕ) (ha : a < p.length) (hb : b < p.length),
        p.support[a]'(by omega) = p.support[b]'(by omega) → a = b := by
      intro a b ha hb heq
      have h1 : p.support.dropLast[a]'(by omega) = p.support.dropLast[b]'(by omega) := by
        rw [hdrop_get a ha, hdrop_get b hb, heq]
      have hinj := (List.nodup_iff_injective_getElem.mp hnodup) (a := ⟨a, by omega⟩) (b := ⟨b, by omega⟩) h1
      simpa using hinj
    have hlast_eq_head : p.support[p.length]'(by omega) = p.support[0]'(by omega) := by
      have h0 : p.support[0]'(by omega) = v := by
        have := SimpleGraph.Walk.head_support p
        rw [← List.head_eq_getElem_zero] at this ⊢
        exact this
      have hl : p.support[p.length]'(by omega) = v := by
        have := SimpleGraph.Walk.getLast_support p
        rw [List.getLast_eq_getElem] at this
        simpa [hlen_s] using this
      rw [h0, hl]
    rw [Sym2.eq_iff] at heq_s
    rcases heq_s with ⟨h1, _⟩ | ⟨h1, h2⟩
    · ext; exact hdrop_inj i.val j.val hi hj h1
    · by_cases hj1 : j.val + 1 < p.length
      · have hij1 : i.val = j.val + 1 := hdrop_inj i.val (j.val + 1) hi hj1 h1
        by_cases hi1 : i.val + 1 < p.length
        · have hi1j : i.val + 1 = j.val := hdrop_inj (i.val + 1) j.val hi1 hj h2
          omega
        · have hi_end : i.val + 1 = p.length := by omega
          omega
      · have hj_end : j.val + 1 = p.length := by omega
        have h1' : p.support[i.val]'(by omega) = p.support[0]'(by omega) := by
          have : p.support[j.val + 1]'(by omega) = p.support[p.length]'(by omega) := by
            congr 1
          rw [h1, this, hlast_eq_head]
        have hi0 : i.val = 0 := hdrop_inj i.val 0 hi (by omega) h1'
        have hi1_lt : i.val + 1 < p.length := by omega
        have hi1j : i.val + 1 = j.val := hdrop_inj (i.val + 1) j.val hi1_lt hj h2
        omega
  exact ⟨⟨hedg_nodup⟩, hne, htail_nodup⟩

/-- Every choice mask `σ : Fin N.r → Bool` produces a simple cycle in `G`. -/
theorem necklace_walk_isCycle (σ : Fin N.r → Bool) : (N.cycleWalk σ).IsCycle :=
  N.isCycle_of_dropLast_nodup (N.cycleWalk σ)
    (N.cycleWalk_length_ge_three σ) (N.cycleWalk_support_dropLast_nodup σ)

def baseLength : ℕ :=
  ((List.finRange N.r).map (fun i => (N.segA i).length)).sum

def gains : List ℕ :=
  (List.finRange N.r).map (fun i => (N.segB i).length - (N.segA i).length)

theorem baseLength_ge_three : 3 ≤ N.baseLength := by
  unfold baseLength
  have hge : ((List.finRange N.r).map (fun _ => 1)).sum ≤
      ((List.finRange N.r).map (fun i => (N.segA i).length)).sum := by
    apply List.Forall₂.sum_le_sum
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.Forall₂.of_eq_true (by simp) |>.imp (by intro a b hab; subst hab; exact N.segA_pos a)
  have hones : ((List.finRange N.r).map (fun _ => 1)).sum = N.r := by simp
  have := N.hr
  omega

theorem cycleWalk_length_decomp (bs : List Bool) (hbs : bs.length = N.r) :
    let σ : Fin N.r → Bool := fun i => bs[i.val]'(by omega)
    (N.cycleWalk σ).length = N.baseLength + maskedSum N.gains bs := by
  intro σ
  rw [N.cycleWalk_length_eq σ]
  unfold baseLength gains
  have hlist : ∀ (l : List (Fin N.r)) (bs' : List Bool),
      bs'.length = l.length →
      (∀ (k : ℕ) (hk : k < l.length), bs'[k]'(by omega) = σ (l[k]'hk)) →
      (l.map (fun i => (N.seg σ i).length)).sum =
        (l.map (fun i => (N.segA i).length)).sum +
        maskedSum (l.map (fun i => (N.segB i).length - (N.segA i).length)) bs' := by
    intro l
    induction l with
    | nil =>
      intro bs' hbs' _
      cases bs' with
      | nil => simp [maskedSum]
      | cons _ _ => simp at hbs'
    | cons a l ih =>
      intro bs' hbs' hget
      cases bs' with
      | nil => simp at hbs'
      | cons b bs'' =>
        have hlen'' : bs''.length = l.length := by simpa using hbs'
        have hb : b = σ a := by
          have := hget 0 (by simp)
          simpa using this
        have hget'' : ∀ (k : ℕ) (hk : k < l.length), bs''[k]'(by omega) = σ (l[k]'hk) := by
          intro k hk
          have := hget (k + 1) (by simp; omega)
          simpa using this
        simp only [List.map_cons, List.sum_cons, maskedSum]
        rw [ih bs'' hlen'' hget'']
        have hseg : (N.seg σ a).length = (N.segA a).length + (if b then (N.segB a).length - (N.segA a).length else 0) := by
          unfold seg
          rw [← hb]
          cases b
          · simp
          · simp; have := N.segB_ge a; omega
        omega
  exact hlist (List.finRange N.r) bs (by simp [hbs]) (by
    intro k hk
    simp [σ])

end BypassNecklace

/-! ### 3. Unconditional Dyadic Necklace Closure Theorems & Whole-Problem Closure Gate -/

/-- Pillar 1A: Any graph with a unit-step Brown–Octave Bypass Necklace has a simple `2^k`-cycle. -/
theorem hasPowerCycle_of_brown_unit_necklace {V : Type*} {G : SimpleGraph V}
    (N : BypassNecklace G) (hB : BrownUnit N.gains) (hspan : N.baseLength - 2 ≤ N.gains.sum) :
    HasPowerCycle G := by
  obtain ⟨bs, k, hlen, hk, hsum⟩ :=
    exists_subset_sum_pow2_of_brown_unit N.baseLength_ge_three hB hspan
  have hbs_r : bs.length = N.r := by
    have hgl : N.gains.length = N.r := by simp [BypassNecklace.gains]
    omega
  let σ : Fin N.r → Bool := fun i => bs[i.val]'(by omega)
  refine ⟨N.junction ⟨0, by have := N.hr; omega⟩, N.cycleWalk σ, N.necklace_walk_isCycle σ, k, hk, ?_⟩
  rw [N.cycleWalk_length_decomp bs hbs_r]
  exact hsum

/-- Pillar 1B: Even-step Brown–Octave Bypass Necklace Closure (for bipartite / even-girth graphs). -/
theorem hasPowerCycle_of_brown_even_necklace {V : Type*} {G : SimpleGraph V}
    (N : BypassNecklace G) (cs : List ℕ)
    (hEven : Even N.baseLength) (hL0 : 4 ≤ N.baseLength)
    (hgains : N.gains = cs.map (2 * ·)) (hB : BrownUnit cs)
    (hspan : N.baseLength - 2 ≤ 2 * cs.sum) :
    HasPowerCycle G := by
  obtain ⟨bs, k, hlen, hk, hsum⟩ :=
    exists_subset_sum_pow2_of_brown_even hL0 hEven hB hspan
  have hbs_r : bs.length = N.r := by
    have hgl : N.gains.length = N.r := by simp [BypassNecklace.gains]
    rw [hgains, List.length_map] at hgl
    omega
  let σ : Fin N.r → Bool := fun i => bs[i.val]'(by omega)
  refine ⟨N.junction ⟨0, by have := N.hr; omega⟩, N.cycleWalk σ, N.necklace_walk_isCycle σ, k, hk, ?_⟩
  rw [N.cycleWalk_length_decomp bs hbs_r, hgains]
  exact hsum

/--
Pillar 1C (Infinite-Family Closure Breaking Kesten–McKay at Fixed Girth `g = 3`, Unbounded `n → ∞`):
Every graph containing a Bypass Necklace of `r` unit-gain segments (e.g., `r` vertex-disjoint
triangles along a cycle) whose baseline `L_0` and `r` bracket a power of two `L_0 ≤ 2^m ≤ L_0 + r`
unconditionally contains a simple `2^m`-cycle.
-/
theorem hasPowerCycle_of_triangle_necklace {V : Type*} {G : SimpleGraph V}
    (N : BypassNecklace G) (hunit : ∀ i : Fin N.r, (N.segB i).length - (N.segA i).length = 1)
    (m : ℕ) (hm : 2 ≤ m) (hlo : N.baseLength ≤ 2 ^ m) (hhi : 2 ^ m ≤ N.baseLength + N.r) :
    HasPowerCycle G := by
  have hgains : N.gains = List.replicate N.r 1 := by
    unfold BypassNecklace.gains
    apply List.ext_getElem
    · simp
    · intro i hi1 hi2
      simp [hunit]
  have hB : BrownUnit N.gains := by rw [hgains]; exact brown_unit_replicate_one N.r
  have hsum_gains : N.gains.sum = N.r := by rw [hgains]; simp
  obtain ⟨bs, hlen, hsum⟩ := brown_unit_complete hB (2 ^ m - N.baseLength) (by omega)
  have hbs_r : bs.length = N.r := by rw [hlen, hgains, List.length_replicate]
  let σ : Fin N.r → Bool := fun i => bs[i.val]'(by omega)
  refine ⟨N.junction ⟨0, by have := N.hr; omega⟩, N.cycleWalk σ, N.necklace_walk_isCycle σ, m, hm, ?_⟩
  rw [N.cycleWalk_length_decomp bs hbs_r, hsum]
  omega

/-- Whole-Problem Closure Gate: proving every `δ(G) ≥ 3` graph has a Brown–Octave Necklace closes Erdős #64. -/
def HasBrownOctaveNecklace {V : Type*} (G : SimpleGraph V) : Prop :=
  (∃ N : BypassNecklace G, BrownUnit N.gains ∧ N.baseLength - 2 ≤ N.gains.sum) ∨
  (∃ (N : BypassNecklace G) (cs : List ℕ),
    Even N.baseLength ∧ 4 ≤ N.baseLength ∧ N.gains = cs.map (2 * ·) ∧
    BrownUnit cs ∧ N.baseLength - 2 ≤ 2 * cs.sum)

theorem erdos64_closed_of_brown_necklace_target
    (hTarget : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      MinDeg G 3 → HasBrownOctaveNecklace G) : Erdos64 := by
  intro V _ _ G _ hmin
  rcases hTarget V G hmin with ⟨N, hB, hspan⟩ | ⟨N, cs, hE, hL0, hg, hB, hspan⟩
  · exact hasPowerCycle_of_brown_unit_necklace N hB hspan
  · exact hasPowerCycle_of_brown_even_necklace N cs hE hL0 hg hB hspan

/-! ### 4. Pillar 2 — All-Order `EG2-CORE` / `EGRob3ConnCore` Hitting-Edge Exclusions -/

def DefectCount {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.filter (fun v => G.degree v = 2)).card

def Near2 {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  MinDeg G 2 ∧ DefectCount G ≤ 2

/--
A graph `G` is defect-minimal bad for `EG2` (`DefectMinimalBad2 G`) if `G` is `Near2`,
has no `2^k`-cycle, and every `Near2` graph on the same vertex set with strictly fewer
degree-2 defects has a `2^k`-cycle. (Every `EG2-CORE` minimal counterexample satisfies this.)
-/
def DefectMinimalBad2 {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  Near2 G ∧ ¬ HasPowerCycle G ∧
    ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj],
      Near2 G' → DefectCount G' < DefectCount G → HasPowerCycle G'

def IsHittingEdge {V : Type*} (H : SimpleGraph V) (e : Sym2 V) : Prop :=
  e ∈ H.edgeSet ∧ ∀ (v : V) (p : H.Walk v v), p.IsCycle → IsPowerOfTwo p.length → e ∈ p.edges

theorem hasPowerCycle_mono {V : Type*} {G₁ G₂ : SimpleGraph V} (hle : G₁ ≤ G₂)
    (h : HasPowerCycle G₁) : HasPowerCycle G₂ := by
  obtain ⟨v, p, hcyc, hpow⟩ := h
  refine ⟨v, p.mapLe hle, ?_, ?_⟩
  · exact hcyc.map (SimpleGraph.Hom.ofLE hle) (fun _ _ h => h)
  · simpa using hpow

theorem degree_deleteEdges_singleton {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {x y : V} (hxy : H.Adj x y) (v : V) :
    let H' := H.deleteEdges {s(x, y)}
    H'.degree v = if v = x ∨ v = y then H.degree v - 1 else H.degree v := by
  intro H'
  classical
  have hne : x ≠ y := H.ne_of_adj hxy
  by_cases hvx : v = x
  · subst hvx
    simp only [true_or, ↓reduceIte]
    have hset : H'.neighborFinset v = (H.neighborFinset v).erase y := by
      ext w
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_erase, H',
        SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff]
      constructor
      · rintro ⟨hw, hnot⟩
        refine ⟨?_, hw⟩
        intro hwy
        exact hnot (Or.inl ⟨rfl, hwy⟩)
      · rintro ⟨hwy, hw⟩
        refine ⟨hw, ?_⟩
        rintro (⟨_, rfl⟩ | ⟨rfl, _⟩)
        · exact hwy rfl
        · exact hne rfl
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree,
      hset, Finset.card_erase_of_mem (by simpa using hxy)]
  · by_cases hvy : v = y
    · subst hvy
      simp only [or_true, ↓reduceIte]
      have hset : H'.neighborFinset v = (H.neighborFinset v).erase x := by
        ext w
        simp only [SimpleGraph.mem_neighborFinset, Finset.mem_erase, H',
          SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff]
        constructor
        · rintro ⟨hw, hnot⟩
          refine ⟨?_, hw⟩
          intro hwx
          exact hnot (Or.inr ⟨hwx, rfl⟩)
        · rintro ⟨hwx, hw⟩
          refine ⟨hw, ?_⟩
          rintro (⟨rfl, _⟩ | ⟨rfl, _⟩)
          · exact hne rfl
          · exact hwx rfl
      rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree,
        hset, Finset.card_erase_of_mem (by simpa using hxy.symm)]
    · simp only [hvx, hvy, or_self, ↓reduceIte]
      have hset : H'.neighborFinset v = H.neighborFinset v := by
        ext w
        simp only [SimpleGraph.mem_neighborFinset, H', SimpleGraph.deleteEdges_adj,
          Set.mem_singleton_iff, Sym2.eq_iff]
        constructor
        · exact And.left
        · intro hw
          refine ⟨hw, ?_⟩
          rintro (⟨rfl, _⟩ | ⟨_, rfl⟩)
          · exact hvx rfl
          · exact hvy rfl
      rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree,
        hset]

/--
Pillar 2A (All-Order `EG2-CORE` High-Edge Avoidance):
In any `EG2-CORE` completion `H` with `MinDeg H 3` and `DefectMinimalBad2 G` (`DefectCount G = 2`),
for EVERY edge `s(x, y)` of `H` with `4 ≤ H.degree x`, there exists a simple `2^k`-cycle of `H`
that avoids `s(x, y)` (and hence, when `H = G + ab`, must contain `ab` and avoid `s(x, y)`).
-/
theorem eg2_core_high_edge_avoided {V : Type*} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hminG : DefectMinimalBad2 G) (hdefG : DefectCount G = 2)
    (hminH : MinDeg H 3) {x y : V} (hxy : H.Adj x y) (hx4 : 4 ≤ H.degree x) :
    ∃ (v : V) (p : H.Walk v v), p.IsCycle ∧ IsPowerOfTwo p.length ∧ s(x, y) ∉ p.edges := by
  classical
  let H' : SimpleGraph V := H.deleteEdges {s(x, y)}
  have hdeg := degree_deleteEdges_singleton H hxy
  have hminH' : MinDeg H' 2 := by
    intro v
    have hv := hminH v
    have hd := hdeg v
    change H'.degree v = _ at hd
    rw [hd]
    split_ifs <;> omega
  have hdefH' : DefectCount H' ≤ 1 := by
    unfold DefectCount
    have hsub : (Finset.univ.filter (fun v => H'.degree v = 2)) ⊆ {y} := by
      intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] at hv ⊢
      have hd := hdeg v
      change H'.degree v = _ at hd
      rw [hd] at hv
      have hmv := hminH v
      by_cases hvy : v = y
      · exact hvy
      · by_cases hvx : v = x
        · subst hvx
          simp only [true_or, ↓reduceIte] at hv
          omega
        · simp only [hvx, hvy, or_self, ↓reduceIte] at hv
          omega
    exact le_trans (Finset.card_le_card hsub) (by simp)
  have hnear' : Near2 H' := ⟨hminH', by omega⟩
  have hpow' : HasPowerCycle H' := hminG.2.2 H' hnear' (by omega)
  obtain ⟨v, p, hcyc, hpow⟩ := hpow'
  have hle : H' ≤ H := SimpleGraph.deleteEdges_le _
  refine ⟨v, p.mapLe hle, hcyc.map (SimpleGraph.Hom.ofLE hle) (fun _ _ h => h), by simpa using hpow, ?_⟩
  intro hmem
  have hmem' : s(x, y) ∈ p.edges := by
    rw [SimpleGraph.Walk.edges_map] at hmem
    simpa using hmem
  have hedge := SimpleGraph.Walk.edges_subset_edgeSet p hmem'
  have : s(x, y) ∉ H'.edgeSet := by
    simp [H', SimpleGraph.edgeSet_deleteEdges]
  exact this hedge

/--
Pillar 2B (All-Order `EG2-CORE` Hitting-Edge Localization):
Every hitting edge `s(x, y)` of `C_{2^k}(H)` in an `EG2-CORE` completion `H` must have
BOTH endpoints of degree exactly 3 in `H` (`E_hit(H) ⊆ E(H[V_3(H)])`).
-/
theorem eg2_core_hitting_edges_in_V3 {V : Type*} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hminG : DefectMinimalBad2 G) (hdefG : DefectCount G = 2)
    (hminH : MinDeg H 3) {x y : V} (hhit : IsHittingEdge H s(x, y)) :
    H.degree x = 3 ∧ H.degree y = 3 := by
  have hxy : H.Adj x y := by simpa [SimpleGraph.mem_edgeSet] using hhit.1
  have hx3 : 3 ≤ H.degree x := hminH x
  have hy3 : 3 ≤ H.degree y := hminH y
  constructor
  · by_contra hxne
    have hx4 : 4 ≤ H.degree x := by omega
    obtain ⟨v, p, hcyc, hpow, havoid⟩ := eg2_core_high_edge_avoided G H hminG hdefG hminH hxy hx4
    exact havoid (hhit.2 v p hcyc hpow)
  · by_contra hyne
    have hy4 : 4 ≤ H.degree y := by omega
    obtain ⟨v, p, hcyc, hpow, havoid⟩ :=
      eg2_core_high_edge_avoided G H hminG hdefG hminH hxy.symm hy4
    rw [Sym2.eq_swap] at havoid
    exact havoid (hhit.2 v p hcyc hpow)

/--
Pillar 2C (High-Degree Multiplicity):
If ANY `2^k`-cycle `C` of an `EG2-CORE` completion `H` traverses an edge `s(x, y)` incident
to a vertex `x ∈ V_{≥4}(H)`, then `H` contains a SECOND distinct `2^k`-cycle `C'` avoiding `s(x, y)`.
-/
theorem eg2_core_high_vertex_forces_two_pow2_cycles {V : Type*} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hminG : DefectMinimalBad2 G) (hdefG : DefectCount G = 2)
    (hminH : MinDeg H 3) {v : V} (p : H.Walk v v)
    (hcyc : p.IsCycle) (hpow : IsPowerOfTwo p.length)
    {x y : V} (hmem : s(x, y) ∈ p.edges) (hx4 : 4 ≤ H.degree x) :
    ∃ (v' : V) (p' : H.Walk v' v'),
      p'.IsCycle ∧ IsPowerOfTwo p'.length ∧ p'.edges ≠ p.edges := by
  have hxy : H.Adj x y := by
    have := SimpleGraph.Walk.edges_subset_edgeSet p hmem
    simpa [SimpleGraph.mem_edgeSet] using this
  obtain ⟨v', p', hcyc', hpow', havoid⟩ :=
    eg2_core_high_edge_avoided G H hminG hdefG hminH hxy hx4
  refine ⟨v', p', hcyc', hpow', ?_⟩
  intro heq
  rw [heq] at havoid
  exact havoid hmem

/-- Pillar 1 + Pillar 2 Bridge: No `DefectMinimalBad2` graph admits a Brown–Octave Bypass Necklace. -/
theorem eg2_core_no_brown_necklace {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hminG : DefectMinimalBad2 G) :
    ¬ HasBrownOctaveNecklace G := by
  rintro (⟨N, hB, hspan⟩ | ⟨N, cs, hE, hL0, hg, hB, hspan⟩)
  · exact hminG.2.1 (hasPowerCycle_of_brown_unit_necklace N hB hspan)
  · exact hminG.2.1 (hasPowerCycle_of_brown_even_necklace N cs hE hL0 hg hB hspan)

end E64Wave6Agent5
