import Leaves
import Descent
import PairedShadow
import ClosedDefectCore

/-!
Erdős #64 — Wave 2 Agent #4: Unconditional All-Order Structural Theorems on `MinimalBad`.

All theorems below are proved unconditionally for arbitrary finite simple graphs `G`
satisfying `MinimalBad G` (using only standard axioms: `propext`, `Classical.choice`, `Quot.sound`).

Key theorems formalized:
1. `high_degree_independent`: `V_{\ge 4}` is an independent set in `MinimalBad G`.
2. `exists_low_degree_neighbor`: Every vertex in `MinimalBad G` has a neighbor of degree `≤ 3`.
3. `class_h_v3_ge_two_v4` & `class_h_v3_two_thirds`: In any Class `H` `MinimalBad G`,
   `2 * |V_{\ge 4}| ≤ |V_3|` and `2 * (|V| - 1) ≤ 3 * |V_3|`.
4. `dyadic_path_of_identify_power`: Unified vertex-identification cycle-lifting theorem.
5. `dyadic_path_of_no_common_neighbor`: Universal Dyadic Path Theorem (`dist_G(x, y) ≥ 3`)
   and non-triangle edge dyadic path theorem (`dist_G(x, y) = 1`, no common neighbor).
6. `non_triangle_edge_odd_power_cycle`: Every non-triangle edge `xy` in `MinimalBad G`
   lies on a simple cycle of length `2 ^ k + 1` (`k ≥ 2`).
7. `unified_bipartite_exclusion`: Unified exclusion of all bipartite `MinimalBad` graphs
   (covering all 6 bipartite leaves `C-B, S-B, H-B-*` in one short proof).
8. `class_h_common_neighbor_dyadic_path`: For `z` with `4 ≤ G.degree z` and non-adjacent
   `x, y ∈ N(z)`, `G` has a simple `x`–`y` path of length `2 ^ k` (`k ≥ 2`) avoiding `{xz, yz}`.
9. `cubic_triangle_free_two_path_mersenne` & `cubic_triangle_free_two_path_dyadic`:
   In every cubic triangle-free `MinimalBad G` (`C-N-2, C-N-3, C-N-R`), for every 2-path
   `u1 - v - u2`, `G - v` contains BOTH a simple `u1`–`u2` path of length `2 ^ k - 1` (`k ≥ 2`)
   AND a simple `u1`–`u2` path of length `2 ^ m` (`m ≥ 2`).
10. `all_pairs_dyadic_path_cubic_triangle_free`: In every cubic triangle-free `MinimalBad G`
    (`C-N-2, C-N-3, C-N-R`), EVERY pair of distinct vertices `x ≠ y` is joined by a simple
    `x`–`y` path of length `2 ^ k` for some `k ≥ 2`.
-/

namespace E64Wave2Agent4
open SimpleGraph Erdos64Closure E64Core E64Leaves Erdos64Paired Erdos64Descent E64DefectCore
open scoped BigOperators
universe u

/-! ### Part 1: High-Degree Independent Set & Class H Density Bounds -/

/-- In `MinimalBad G`, no two vertices of degree ≥ 4 are adjacent. -/
theorem high_degree_independent {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {u v : V} (huv : G.Adj u v) (hu : 4 ≤ G.degree u) :
    G.degree v ≤ 3 := by
  classical
  by_contra hbad
  have hv : 4 ≤ G.degree v := by omega
  obtain ⟨_, w, hw⟩ := hm.1
  let H := G \ SimpleGraph.edge u v
  let _ : DecidableRel H.Adj :=
    inferInstanceAs (DecidableRel (G \ SimpleGraph.edge u v).Adj)
  have hcard : 2 ≤ Fintype.card V := by
    have := G.degree_lt_card_verts u
    omega
  have hn : Near H := by
    apply near_of_except H w hcard
    intro x hx
    have hdeg := erase_edge_degree G u v huv x
    change H.degree x + (if x = u ∨ x = v then 1 else 0) = G.degree x at hdeg
    by_cases hxu : x = u
    · subst x
      simp only [true_or, ite_true] at hdeg
      omega
    by_cases hxv : x = v
    · subst x
      simp only [or_true, ite_true] at hdeg
      omega
    · have hneither : ¬(x = u ∨ x = v) := by tauto
      rw [ite_eq_right hneither, add_zero] at hdeg
      rw [hdeg]
      exact hw x hx
  have hEq : H = G := hm.2.2.2 H sdiff_le hn
  have he : H.Adj u v := hEq ▸ huv
  have hno : ¬H.Adj u v := by
    intro h
    have hs := (SimpleGraph.sdiff_adj G (SimpleGraph.edge u v) u v).mp h
    exact hs.2 ((SimpleGraph.edge_adj u v u v).mpr ⟨Or.inl ⟨rfl, rfl⟩, G.ne_of_adj huv⟩)
  exact hno he

/-- In `MinimalBad G`, every vertex has at least one neighbor of degree ≤ 3.
    Equivalently, no vertex has all its neighbors in `V_{\ge 4}`. -/
theorem exists_low_degree_neighbor {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (x : V) : ∃ y, G.Adj x y ∧ G.degree y ≤ 3 := by
  classical
  by_contra hbad
  push Not at hbad
  obtain ⟨⟨a, ha⟩, ⟨w, hw⟩⟩ := hm.1
  let W := {v : V // v ≠ x}
  let H := G.induce {v | v ≠ x}
  let _ : DecidableRel H.Adj := inferInstanceAs (DecidableRel (G.induce {v | v ≠ x}).Adj)
  have hV : 4 ≤ Fintype.card V := by
    have := G.degree_lt_card_verts a
    omega
  have hW : Fintype.card W + 1 = Fintype.card V := by
    rw [Fintype.card_subtype,
      show (Finset.univ.filter (fun v : V => v ≠ x)) = Finset.univ.erase x by ext v; simp]
    exact Finset.card_erase_add_one (Finset.mem_univ x)
  have hW2 : 2 ≤ Fintype.card ↑({v : V | v ≠ x} : Set V) := by
    have he : Fintype.card ↑({v : V | v ≠ x} : Set V) = Fintype.card W :=
      Fintype.card_congr (Equiv.refl _)
    omega
  have hdeg_ge3 : ∀ v : W, v.1 ≠ w → 3 ≤ H.degree v := by
    intro v hv
    have hd := induce_delete_degree G x v
    change H.degree v + (if G.Adj v.1 x then 1 else 0) = G.degree v.1 at hd
    by_cases hadj : G.Adj v.1 x
    · rw [ite_eq_left hadj] at hd
      have h4 := hbad v.1 hadj.symm
      omega
    · rw [ite_eq_right hadj, add_zero] at hd
      rw [hd]
      exact hw v.1 hv
  have hnear : Near H := by
    by_cases hwx : w = x
    · subst hwx
      obtain ⟨b, hbx⟩ : ∃ b : V, b ≠ w := by
        have hpos : 0 < G.degree w := by have := no_small_defect G hm w; omega
        obtain ⟨b, hwb⟩ := (G.degree_pos_iff_exists_adj w).mp hpos
        exact ⟨b, (G.ne_of_adj hwb).symm⟩
      apply near_of_except H (⟨b, hbx⟩ : W) hW2
      intro v _
      exact hdeg_ge3 v v.2
    · apply near_of_except H (⟨w, hwx⟩ : W) hW2
      intro v hv
      exact hdeg_ge3 v (fun h => hv (Subtype.ext h))
  have hpow : HasPower H := hm.2.2.1 W H (by omega) hnear
  exact hm.2.1 (power_induce G _ hpow)

/-- In any Class `H` (or one-defect) `MinimalBad G`, `2 * |V_{\ge 4}| ≤ |V_3|`. -/
theorem class_h_v3_ge_two_v4 {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {w : V} (hw : G.degree w = 2) (hrest : ∀ v, v ≠ w → 3 ≤ G.degree v) :
    2 * (Finset.univ.filter (fun v => 4 ≤ G.degree v)).card ≤
      (Finset.univ.filter (fun v => G.degree v = 3)).card := by
  classical
  let V4 := Finset.univ.filter (fun v : V => 4 ≤ G.degree v)
  let V3 := Finset.univ.filter (fun v : V => G.degree v = 3)
  have h_lower : 4 * V4.card ≤ ∑ z ∈ V4, ∑ x ∈ V3, if G.Adj z x then (1 : ℕ) else 0 := by
    calc 4 * V4.card = ∑ _z ∈ V4, (4 : ℕ) := by simp [Nat.mul_comm]
      _ ≤ ∑ z ∈ V4, G.degree z := by
          apply Finset.sum_le_sum
          intro z hz
          exact (Finset.mem_filter.mp hz).2
      _ = ∑ z ∈ V4, ∑ x ∈ V3, if G.Adj z x then (1 : ℕ) else 0 := by
          apply Finset.sum_congr rfl
          intro z hz
          have hz4 : 4 ≤ G.degree z := (Finset.mem_filter.mp hz).2
          have hsub : G.neighborFinset z ⊆ V3 := by
            intro x hx
            have hzx : G.Adj z x := (G.mem_neighborFinset z x).mp hx
            have hxle3 : G.degree x ≤ 3 := high_degree_independent G hm hzx hz4
            have hxw : x ≠ w := by
              intro h
              subst h
              have hz3 := defect_neighbor_cubic G hm hw hzx.symm
              omega
            have hxge3 : 3 ≤ G.degree x := hrest x hxw
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, by omega⟩
          rw [← G.card_neighborFinset_eq_degree, ← Finset.sum_filter]
          have hfilt : V3.filter (fun x => G.Adj z x) = G.neighborFinset z := by
            ext x
            simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
            constructor
            · exact fun h => h.2
            · exact fun h => ⟨hsub ((G.mem_neighborFinset z x).mpr h), h⟩
          rw [hfilt]
          simp
  have h_upper : (∑ x ∈ V3, ∑ z ∈ V4, if G.Adj z x then (1 : ℕ) else 0) ≤ 2 * V3.card := by
    calc (∑ x ∈ V3, ∑ z ∈ V4, if G.Adj z x then (1 : ℕ) else 0)
        ≤ ∑ _x ∈ V3, (2 : ℕ) := by
          apply Finset.sum_le_sum
          intro x hx
          have hx3 : G.degree x = 3 := (Finset.mem_filter.mp hx).2
          obtain ⟨y, hxy, hy3⟩ := exists_low_degree_neighbor G hm x
          have hsub : V4.filter (fun z => G.Adj z x) ⊆ (G.neighborFinset x).erase y := by
            intro z hz
            have hzm := Finset.mem_filter.mp hz
            have hz4 : 4 ≤ G.degree z := (Finset.mem_filter.mp hzm.1).2
            have hzy : z ≠ y := by intro h; subst h; omega
            exact Finset.mem_erase.mpr ⟨hzy, (G.mem_neighborFinset x z).mpr hzm.2.symm⟩
          rw [← Finset.sum_filter]
          simp only [Finset.sum_const, smul_eq_mul, mul_one]
          have hc1 := Finset.card_le_card hsub
          have hc2 := Finset.card_erase_add_one ((G.mem_neighborFinset x y).mpr hxy)
          rw [G.card_neighborFinset_eq_degree, hx3] at hc2
          omega
      _ = 2 * V3.card := by simp [Nat.mul_comm]
  have hcomm : (∑ z ∈ V4, ∑ x ∈ V3, if G.Adj z x then (1 : ℕ) else 0) =
      ∑ x ∈ V3, ∑ z ∈ V4, if G.Adj z x then (1 : ℕ) else 0 := Finset.sum_comm
  omega

/-- Corollary: In any Class `H` `MinimalBad G`, `2 * (|V| - 1) ≤ 3 * |V_3|`. -/
theorem class_h_v3_two_thirds {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {w : V} (hw : G.degree w = 2) (hrest : ∀ v, v ≠ w → 3 ≤ G.degree v) :
    2 * (Fintype.card V - 1) ≤
      3 * (Finset.univ.filter (fun v => G.degree v = 3)).card := by
  classical
  let V4 := Finset.univ.filter (fun v : V => 4 ≤ G.degree v)
  let V3 := Finset.univ.filter (fun v : V => G.degree v = 3)
  have hdisj : Disjoint V3 V4 := by
    rw [Finset.disjoint_left]
    intro v hv3 hv4
    have h1 := (Finset.mem_filter.mp hv3).2
    have h2 := (Finset.mem_filter.mp hv4).2
    omega
  have hunion : V3 ∪ V4 = Finset.univ.erase w := by
    ext v
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase, V3, V4]
    constructor
    · rintro (h | h) <;> (intro he; subst he; omega)
    · intro hvw
      have h3 := hrest v hvw
      omega
  have hcard : V3.card + V4.card + 1 = Fintype.card V := by
    have h1 := Finset.card_union_of_disjoint hdisj
    rw [hunion] at h1
    have h2 := Finset.card_erase_add_one (Finset.mem_univ w)
    rw [Finset.card_univ] at h2
    omega
  have h2 := class_h_v3_ge_two_v4 G hm hw hrest
  omega

/-! ### Part 2: Unified Vertex-Identification Cycle-Lifting Engine -/

/-- Identify `y` into `x` on the carrier `{v : V // v ≠ y}` (simplifying loops & parallel edges). -/
def identifyGraph {V : Type u} (G : SimpleGraph V) (x y : V) :
    SimpleGraph {v : V // v ≠ y} where
  Adj u v := u ≠ v ∧ (G.Adj u.1 v.1 ∨ (u.1 = x ∧ G.Adj y v.1) ∨ (v.1 = x ∧ G.Adj u.1 y))
  symm := by
    rintro u v ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr ⟨h1, h2.symm⟩)
    · exact Or.inr (Or.inl ⟨h1, h2.symm⟩)
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Lift a walk in `identifyGraph G x y` whose support avoids `⟨x, hxy⟩` directly into `G`. -/
def liftAvoidWalk {V : Type u} {G : SimpleGraph V} {x y : V} (hxy : x ≠ y) :
    ∀ {u v : {v : V // v ≠ y}} (p : (identifyGraph G x y).Walk u v),
      (⟨x, hxy⟩ : {v : V // v ≠ y}) ∉ p.support → G.Walk u.1 v.1
  | _, _, .nil, _ => .nil
  | u, _, .cons (v := b) h rest, hnot => by
    have hu : u ≠ ⟨x, hxy⟩ := fun he => hnot (by simp [he])
    have hb : b ≠ ⟨x, hxy⟩ := fun he => hnot (by simp [he])
    have hux : u.1 ≠ x := fun he => hu (Subtype.ext he)
    have hbx : b.1 ≠ x := fun he => hb (Subtype.ext he)
    have hG : G.Adj u.1 b.1 := by
      rcases h.2 with h1 | ⟨h1, _⟩ | ⟨h1, _⟩
      · exact h1
      · exact False.elim (hux h1)
      · exact False.elim (hbx h1)
    have hnot' : (⟨x, hxy⟩ : {v : V // v ≠ y}) ∉ rest.support := by
      intro hm
      exact hnot (by simp [hm])
    exact .cons hG (liftAvoidWalk hxy rest hnot')

theorem liftAvoidWalk_length {V : Type u} {G : SimpleGraph V} {x y : V} (hxy : x ≠ y)
    {u v : {v : V // v ≠ y}} (p : (identifyGraph G x y).Walk u v)
    (hnot : (⟨x, hxy⟩ : {v : V // v ≠ y}) ∉ p.support) :
    (liftAvoidWalk hxy p hnot).length = p.length := by
  induction p with
  | nil => rfl
  | cons h rest ih =>
    simp [liftAvoidWalk, ih]

theorem liftAvoidWalk_support {V : Type u} {G : SimpleGraph V} {x y : V} (hxy : x ≠ y)
    {u v : {v : V // v ≠ y}} (p : (identifyGraph G x y).Walk u v)
    (hnot : (⟨x, hxy⟩ : {v : V // v ≠ y}) ∉ p.support) :
    (liftAvoidWalk hxy p hnot).support = p.support.map Subtype.val := by
  induction p with
  | nil => rfl
  | cons h rest ih =>
    simp [liftAvoidWalk, ih]

/-- Helper: any vertex belonging to an edge of a walk belongs to the walk's support. -/
theorem mem_support_of_mem_edge {V : Type u} {G : SimpleGraph V} {u v w : V}
    (p : G.Walk u v) {e : Sym2 V} (he : e ∈ p.edges) (hw : w ∈ e) : w ∈ p.support := by
  induction p with
  | nil => simp at he
  | @cons a b c hab rest ih =>
    rw [Walk.edges_cons, List.mem_cons] at he
    rcases he with rfl | hrest
    · rcases Sym2.mem_iff.mp hw with rfl | rfl
      · simp
      · simp [Walk.start_mem_support]
    · exact List.mem_cons_of_mem a (ih hrest)

/-- Core lifting lemma: if `identifyGraph G x y` has a simple `2^k`-cycle (`k ≥ 2`)
    while `G` is power-free, then `G` contains a simple `x`–`y` path of length `2^k`
    whose edges avoid `s(x, z)` and `s(y, z)` for every common neighbor `z` of `x, y`. -/
theorem dyadic_path_of_identify_power {V : Type u} {G : SimpleGraph V}
    (hfree : ¬HasPower G) {x y : V} (hxy : x ≠ y)
    (hpow : HasPower (identifyGraph G x y)) :
    ∃ (k : ℕ) (p : G.Walk x y), 2 ≤ k ∧ p.IsPath ∧ p.length = 2 ^ k ∧
      (∀ z, G.Adj x z → G.Adj y z → s(x, z) ∉ p.edges ∧ s(y, z) ∉ p.edges) := by
  classical
  obtain ⟨k, v0, c, hk, hc, hlen⟩ := hpow
  let x' : {v : V // v ≠ y} := ⟨x, hxy⟩
  have hmem : x' ∈ c.support := by
    by_contra hnot
    let cG := liftAvoidWalk hxy c hnot
    have hsupp : cG.support.tail.Nodup := by
      have h1 : cG.support.tail = c.support.tail.map Subtype.val := by
        rw [← List.map_tail, ← liftAvoidWalk_support hxy c hnot]
      rw [h1]
      exact (List.nodup_map_iff Subtype.val_injective).mpr hc.support_nodup
    have hclen : 3 ≤ cG.length := by
      rw [liftAvoidWalk_length]
      exact hc.three_le_length
    have hnil : ¬cG.Nil := by
      intro h
      have := Walk.length_eq_zero_iff.mpr h
      omega
    have hcG : cG.IsCycle := by
      apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      refine ⟨Walk.IsPath.mk' ?_, hclen⟩
      rwa [Walk.support_tail_of_not_nil _ hnil]
    exact hfree ⟨k, v0.1, cG, hk, hcG, by rw [liftAvoidWalk_length, hlen]⟩
  let c' := c.rotate hmem
  have hc' : c'.IsCycle := hc.rotate hmem
  have hlen' : c'.length = 2 ^ k := by rw [Walk.length_rotate, hlen]
  have h3 : 3 ≤ c'.length := hc'.three_le_length
  cases hc_eq : c' with
  | nil =>
    rw [hc_eq] at h3
    simp at h3
  | @cons _ b _ e1 r =>
    have hrlen : 2 ≤ r.length := by
      rw [hc_eq, Walk.length_cons] at h3
      omega
    have hrevlen : 2 ≤ r.reverse.length := by simpa using hrlen
    cases hrev_eq : r.reverse with
    | nil =>
      rw [hrev_eq] at hrevlen
      simp at hrevlen
    | @cons _ b' _ e2 qrev =>
      let q := qrev.reverse
      have hr_eq : r = q.append (Walk.cons e2.symm Walk.nil) := by
        have h1 : r = r.reverse.reverse := r.reverse_reverse.symm
        rw [hrev_eq] at h1
        simpa [q] using h1
      have hqlen : q.length + 2 = 2 ^ k := by
        have h1 : c'.length = r.length + 1 := by rw [hc_eq, Walk.length_cons]
        have h2 : r.length = q.length + 1 := by rw [hr_eq, Walk.length_append]; simp
        omega
      have htail : c'.support.tail = q.support ++ [x'] := by
        rw [hc_eq, Walk.support_cons, List.tail_cons, hr_eq, Walk.support_append]
        simp
      have hnodup_all : (q.support ++ [x']).Nodup := by
        rw [← htail]
        exact hc'.support_nodup
      have hqnodup : q.support.Nodup := (List.nodup_append.mp hnodup_all).1
      have hnotx' : x' ∉ q.support := by
        intro hx
        exact (List.nodup_append.mp hnodup_all).2.2 x' hx (by simp) rfl
      let qG := liftAvoidWalk hxy q hnotx'
      have hqG_len : qG.length = q.length := liftAvoidWalk_length hxy q hnotx'
      have hqG_supp : qG.support = q.support.map Subtype.val := liftAvoidWalk_support hxy q hnotx'
      have hqG_nodup : qG.support.Nodup := by
        rw [hqG_supp]
        exact (List.nodup_map_iff Subtype.val_injective).mpr hqnodup
      have hnotx : x ∉ qG.support := by
        rw [hqG_supp, List.mem_map]
        rintro ⟨u, hu, hux⟩
        exact hnotx' ((Subtype.ext hux) ▸ hu)
      have hnoty : y ∉ qG.support := by
        rw [hqG_supp, List.mem_map]
        rintro ⟨u, _, huy⟩
        exact u.2 huy
      have h_no_same : ∀ (s : V), s ∉ qG.support → G.Adj s b.1 → G.Adj b'.1 s → False := by
        intro s hs hsb hb's
        let cyc : G.Walk s s := Walk.cons hsb (qG.append (Walk.cons hb's Walk.nil))
        have hcycsupp : cyc.support.tail = qG.support ++ [s] := by
          simp [cyc, Walk.support_cons, Walk.support_append]
        have hcycnodup : cyc.support.tail.Nodup := by
          rw [hcycsupp]
          exact List.nodup_append.mpr ⟨hqG_nodup, List.nodup_singleton s,
            fun a ha c hc hac => by
              simp only [List.mem_singleton] at hc
              subst hc; subst hac; exact hs ha⟩
        have hcyclen : cyc.length = 2 ^ k := by
          simp [cyc, Walk.length_cons, Walk.length_append, hqG_len]
          omega
        have hcyc3 : 3 ≤ cyc.length := by
          have : 4 ≤ 2 ^ k := by
            have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hk
            norm_num at this; exact this
          omega
        have hcycnil : ¬cyc.Nil := by simp [cyc]
        have hcyc_is : cyc.IsCycle := by
          apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
          refine ⟨Walk.IsPath.mk' ?_, hcyc3⟩
          rwa [Walk.support_tail_of_not_nil _ hcycnil]
        exact hfree ⟨k, s, cyc, hk, hcyc_is, hcyclen⟩
      have he1 : G.Adj x b.1 ∨ G.Adj y b.1 := by
        rcases e1.2 with h | ⟨_, h⟩ | ⟨hb, _⟩
        · exact Or.inl h
        · exact Or.inr h
        · exact False.elim (e1.1 (Subtype.ext hb.symm))
      have he2 : G.Adj x b'.1 ∨ G.Adj y b'.1 := by
        rcases e2.2 with h | ⟨_, h⟩ | ⟨hb', _⟩
        · exact Or.inl h
        · exact Or.inr h
        · exact False.elim (e2.1 (Subtype.ext hb'.symm))
      rcases he1 with h1x | h1y <;> rcases he2 with h2x | h2y
      · exact False.elim (h_no_same x hnotx h1x h2x.symm)
      · let p : G.Walk x y := Walk.cons h1x (qG.append (Walk.cons h2y.symm Walk.nil))
        have hpsupp : p.support = x :: (qG.support ++ [y]) := by
          simp [p, Walk.support_cons, Walk.support_append]
        have hpnodup : p.support.Nodup := by
          rw [hpsupp, List.nodup_cons]
          refine ⟨?_, List.nodup_append.mpr ⟨hqG_nodup, List.nodup_singleton y,
            fun a ha c hc hac => by
              simp only [List.mem_singleton] at hc
              subst hc; subst hac; exact hnoty ha⟩⟩
          simp [hnotx, hxy]
        have hplen : p.length = 2 ^ k := by
          simp [p, Walk.length_cons, Walk.length_append, hqG_len]
          omega
        refine ⟨k, p, hk, Walk.IsPath.mk' hpnodup, hplen, ?_⟩
        intro z hxz hyz
        have hpedges : p.edges = s(x, b.1) :: (qG.edges ++ [s(b'.1, y)]) := by
          simp [p, Walk.edges_cons, Walk.edges_append]
        have hbz : b.1 ≠ z := by
          intro h; subst h; exact h_no_same y hnoty hyz h2y.symm
        have hb'z : b'.1 ≠ z := by
          intro h; subst h; exact h_no_same x hnotx h1x hxz.symm
        constructor
        · intro hm
          rw [hpedges, List.mem_cons, List.mem_append, List.mem_singleton] at hm
          rcases hm with h | h | h
          · rcases Sym2.eq_iff.mp h with ⟨_, h2'⟩ | ⟨h1', _⟩
            · exact hbz h2'.symm
            · exact (G.ne_of_adj hxz) h1'.symm
          · exact hnotx (mem_support_of_mem_edge qG h (by simp))
          · rcases Sym2.eq_iff.mp h with ⟨_, h2'⟩ | ⟨h1', _⟩
            · exact hxy h2'
            · exact hxy h1'.symm
        · intro hm
          rw [hpedges, List.mem_cons, List.mem_append, List.mem_singleton] at hm
          rcases hm with h | h | h
          · rcases Sym2.eq_iff.mp h with ⟨h1', _⟩ | ⟨_, h2'⟩
            · exact hxy h1'.symm
            · exact hxy h2'
          · exact hnoty (mem_support_of_mem_edge qG h (by simp))
          · rcases Sym2.eq_iff.mp h with ⟨h1', _⟩ | ⟨_, h2'⟩
            · exact (G.ne_of_adj hyz) h1'
            · exact hb'z h2'.symm
      · let p_rev : G.Walk y x := Walk.cons h1y (qG.append (Walk.cons h2x.symm Walk.nil))
        have hpsupp : p_rev.support = y :: (qG.support ++ [x]) := by
          simp [p_rev, Walk.support_cons, Walk.support_append]
        have hpnodup : p_rev.support.Nodup := by
          rw [hpsupp, List.nodup_cons]
          refine ⟨?_, List.nodup_append.mpr ⟨hqG_nodup, List.nodup_singleton x,
            fun a ha c hc hac => by
              simp only [List.mem_singleton] at hc
              subst hc; subst hac; exact hnotx ha⟩⟩
          simp [hnoty, hxy.symm]
        have hprev_path : p_rev.IsPath := Walk.IsPath.mk' hpnodup
        let p := p_rev.reverse
        have hplen : p.length = 2 ^ k := by
          simp [p, p_rev, Walk.length_reverse, Walk.length_cons, Walk.length_append, hqG_len]
          omega
        refine ⟨k, p, hk, hprev_path.reverse, hplen, ?_⟩
        intro z hxz hyz
        have hpedges : p_rev.edges = s(y, b.1) :: (qG.edges ++ [s(b'.1, x)]) := by
          simp [p_rev, Walk.edges_cons, Walk.edges_append]
        have hbz : b.1 ≠ z := by
          intro h; subst h; exact h_no_same x hnotx hxz h2x.symm
        have hb'z : b'.1 ≠ z := by
          intro h; subst h; exact h_no_same y hnoty h1y hyz.symm
        constructor
        · intro hm
          rw [Walk.edges_reverse, List.mem_reverse, hpedges, List.mem_cons,
            List.mem_append, List.mem_singleton] at hm
          rcases hm with h | h | h
          · rcases Sym2.eq_iff.mp h with ⟨h1', _⟩ | ⟨_, h2'⟩
            · exact hxy h1'
            · exact hxy h2'.symm
          · exact hnotx (mem_support_of_mem_edge qG h (by simp))
          · rcases Sym2.eq_iff.mp h with ⟨_, h2'⟩ | ⟨h1', _⟩
            · exact (G.ne_of_adj hxz) h2'.symm
            · exact hb'z h1'.symm
        · intro hm
          rw [Walk.edges_reverse, List.mem_reverse, hpedges, List.mem_cons,
            List.mem_append, List.mem_singleton] at hm
          rcases hm with h | h | h
          · rcases Sym2.eq_iff.mp h with ⟨_, h2'⟩ | ⟨h1', _⟩
            · exact hbz h2'.symm
            · exact (G.ne_of_adj hyz) h1'.symm
          · exact hnoty (mem_support_of_mem_edge qG h (by simp))
          · rcases Sym2.eq_iff.mp h with ⟨_, h2'⟩ | ⟨h1', _⟩
            · exact hxy h2'.symm
            · exact hxy h1'
      · exact False.elim (h_no_same y hnoty h1y h2y.symm)

/-! ### Part 3: Degree Formulas for `identifyGraph` & Main Unconditional Corollaries -/

theorem identifyGraph_degree_ne {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {x y : V} (hxy : x ≠ y)
    (u : {v : V // v ≠ y}) (hux : u.1 ≠ x)
    (hdisj : ¬(G.Adj u.1 x ∧ G.Adj u.1 y)) :
    (identifyGraph G x y).degree u = G.degree u.1 := by
  classical
  let H := identifyGraph G x y
  let _ : DecidableRel H.Adj := Classical.decRel _
  let f : H.neighborSet u → G.neighborSet u.1 := fun w =>
    if hw : w.1.1 = x ∧ G.Adj u.1 y then ⟨y, hw.2⟩
    else ⟨w.1.1, by
      rcases w.2.2 with h | ⟨h1, _⟩ | ⟨h1, h2⟩
      · exact h
      · exact False.elim (hux h1)
      · exact False.elim (hw ⟨h1, h2⟩)⟩
  have hfinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    by_cases ha : a.1.1 = x ∧ G.Adj u.1 y <;> by_cases hb : b.1.1 = x ∧ G.Adj u.1 y
    · exact ha.1.trans hb.1.symm
    · have hv : y = b.1.1 := by simpa [f, ha, hb] using congrArg Subtype.val hab
      exact False.elim (b.1.2 hv.symm)
    · have hv : a.1.1 = y := by simpa [f, ha, hb] using congrArg Subtype.val hab
      exact False.elim (a.1.2 hv)
    · simpa [f, ha, hb] using congrArg Subtype.val hab
  have hfsurj : Function.Surjective f := by
    rintro ⟨z, huz⟩
    by_cases hzy : z = y
    · subst hzy
      have hne : u ≠ ⟨x, hxy⟩ := fun h => hux (congrArg Subtype.val h)
      refine ⟨⟨⟨x, hxy⟩, hne, Or.inr (Or.inr ⟨rfl, huz⟩)⟩, ?_⟩
      apply Subtype.ext
      simp [f, huz]
    · have hne : u ≠ ⟨z, hzy⟩ := fun h => (G.ne_of_adj huz) (congrArg Subtype.val h)
      refine ⟨⟨⟨z, hzy⟩, hne, Or.inl huz⟩, ?_⟩
      apply Subtype.ext
      by_cases hzx : z = x
      · subst hzx
        have hny : ¬G.Adj u.1 y := fun hy => hdisj ⟨huz, hy⟩
        simp [f, hny]
      · simp [f, hzx]
  have hc := Fintype.card_congr (Equiv.ofBijective f ⟨hfinj, hfsurj⟩)
  rwa [SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.card_neighborSet_eq_degree] at hc

theorem identifyGraph_degree_merged {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {x y : V} (hxy : x ≠ y)
    (hdisj : ∀ z, ¬(G.Adj x z ∧ G.Adj y z)) :
    (identifyGraph G x y).degree ⟨x, hxy⟩ =
      G.degree x + G.degree y - (if G.Adj x y then 2 else 0) := by
  classical
  let H := identifyGraph G x y
  let _ : DecidableRel H.Adj := Classical.decRel _
  let x' : {v : V // v ≠ y} := ⟨x, hxy⟩
  let A := (G.neighborFinset x).erase y
  let B := (G.neighborFinset y).erase x
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro z hzA hzB
    have h1 := (G.mem_neighborFinset x z).mp (Finset.mem_erase.mp hzA).2
    have h2 := (G.mem_neighborFinset y z).mp (Finset.mem_erase.mp hzB).2
    exact hdisj z ⟨h1, h2⟩
  let e : H.neighborSet x' ≃ ↥(A ∪ B) :=
    { toFun := fun w => ⟨w.1.1, by
        rw [Finset.mem_union]
        rcases w.2.2 with h | ⟨_, h⟩ | ⟨hwx, _⟩
        · left
          exact Finset.mem_erase.mpr ⟨w.1.2, (G.mem_neighborFinset x w.1.1).mpr h⟩
        · right
          have hwx : w.1.1 ≠ x := fun he => w.2.1 (Subtype.ext he.symm)
          exact Finset.mem_erase.mpr ⟨hwx, (G.mem_neighborFinset y w.1.1).mpr h⟩
        · exact False.elim (w.2.1 (Subtype.ext hwx.symm))⟩
      invFun := fun z => ⟨⟨z.1, by
        intro hzy
        rcases Finset.mem_union.mp z.2 with hA | hB
        · exact (Finset.mem_erase.mp hA).1 hzy
        · exact (G.loopless y) (hzy ▸ (G.mem_neighborFinset y z.1).mp (Finset.mem_erase.mp hB).2)⟩,
        by
          have hzx : z.1 ≠ x := by
            intro h
            rcases Finset.mem_union.mp z.2 with hA | hB
            · exact (G.loopless x) (h ▸ (G.mem_neighborFinset x z.1).mp (Finset.mem_erase.mp hA).2)
            · exact (Finset.mem_erase.mp hB).1 h
          refine ⟨fun h => hzx (congrArg Subtype.val h).symm, ?_⟩
          rcases Finset.mem_union.mp z.2 with hA | hB
          · exact Or.inl ((G.mem_neighborFinset x z.1).mp (Finset.mem_erase.mp hA).2)
          · exact Or.inr (Or.inl ⟨rfl, (G.mem_neighborFinset y z.1).mp (Finset.mem_erase.mp hB).2⟩)⟩
      left_inv := by intro w; apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := by intro z; apply Subtype.ext; rfl }
  have hc := Fintype.card_congr e
  rw [SimpleGraph.card_neighborSet_eq_degree, Fintype.card_coe,
    Finset.card_union_of_disjoint hAB] at hc
  by_cases hadj : G.Adj x y
  · have hA := Finset.card_erase_add_one ((G.mem_neighborFinset x y).mpr hadj)
    have hB := Finset.card_erase_add_one ((G.mem_neighborFinset y x).mpr hadj.symm)
    rw [G.card_neighborFinset_eq_degree] at hA hB
    rw [ite_eq_left hadj]
    omega
  · have hA : A = G.neighborFinset x := Finset.erase_eq_of_notMem
      (fun h => hadj ((G.mem_neighborFinset x y).mp h))
    have hB : B = G.neighborFinset y := Finset.erase_eq_of_notMem
      (fun h => hadj ((G.mem_neighborFinset y x).mp h).symm)
    rw [hA, hB, G.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree] at hc
    rw [ite_eq_right hadj]
    omega

/-- **Universal Dyadic Path Theorem (and Non-Triangle Edge Contraction)**:
    In ANY `MinimalBad G`, if `x ≠ y` have NO common neighbor in `G`
    (which holds both when `dist_G(x, y) ≥ 3` and when `xy` is a non-triangle edge),
    then `G` contains a simple `x`–`y` path of length `2 ^ k` (`k ≥ 2`). -/
theorem dyadic_path_of_no_common_neighbor {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {x y : V} (hxy : x ≠ y) (hdisj : ∀ z, ¬(G.Adj x z ∧ G.Adj y z)) :
    ∃ (k : ℕ) (p : G.Walk x y), 2 ≤ k ∧ p.IsPath ∧ p.length = 2 ^ k := by
  classical
  let W := {v : V // v ≠ y}
  let H := identifyGraph G x y
  let _ : DecidableRel H.Adj := Classical.decRel _
  obtain ⟨⟨a, ha⟩, ⟨w, hw⟩⟩ := hm.1
  have hV : 4 ≤ Fintype.card V := by
    have := G.degree_lt_card_verts a
    omega
  have hW : Fintype.card W + 1 = Fintype.card V := by
    rw [Fintype.card_subtype,
      show (Finset.univ.filter (fun v : V => v ≠ y)) = Finset.univ.erase y by ext v; simp]
    exact Finset.card_erase_add_one (Finset.mem_univ y)
  have hdx : 2 ≤ G.degree x := no_small_defect G hm x
  have hdy : 2 ≤ G.degree y := no_small_defect G hm y
  have hsum : 5 ≤ G.degree x + G.degree y := by
    by_cases hxw : x = w
    · have hyw : y ≠ w := fun h => hxy (hxw.trans h.symm)
      have := hw y hyw
      omega
    · have := hw x hxw
      omega
  have hdeg_merged : 3 ≤ H.degree ⟨x, hxy⟩ := by
    have hd := identifyGraph_degree_merged G hxy hdisj
    by_cases hadj : G.Adj x y
    · rw [ite_eq_left hadj] at hd; omega
    · rw [ite_eq_right hadj] at hd; omega
  have hdeg_other : ∀ u : W, u.1 ≠ x → H.degree u = G.degree u.1 := by
    intro u hux
    exact identifyGraph_degree_ne G hxy u hux (fun ⟨h1, h2⟩ => hdisj u.1 ⟨h1.symm, h2.symm⟩)
  have hnear : Near H := by
    by_cases hwy : w = y
    · subst hwy
      apply near_of_except H (⟨x, hxy⟩ : W) (by omega)
      intro u hu
      have hux : u.1 ≠ x := fun h => hu (Subtype.ext h)
      rw [hdeg_other u hux]
      exact hw u.1 u.2
    · apply near_of_except H (⟨w, hwy⟩ : W) (by omega)
      intro u hu
      by_cases hux : u.1 = x
      · have he : u = ⟨x, hxy⟩ := Subtype.ext hux
        rw [he]
        exact hdeg_merged
      · rw [hdeg_other u hux]
        exact hw u.1 (fun h => hu (Subtype.ext h))
  have hpow : HasPower H := hm.2.2.1 W H (by omega) hnear
  obtain ⟨k, p, hk, hp, hlen, _⟩ := dyadic_path_of_identify_power hm.2.1 hxy hpow
  exact ⟨k, p, hk, hp, hlen⟩

/-- **Edge-Contraction `(2^k + 1)`-Cycle Theorem**:
    Every non-triangle edge `xy` in `MinimalBad G` lies on a simple cycle of length `2 ^ k + 1` (`k ≥ 2`). -/
theorem non_triangle_edge_odd_power_cycle {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {x y : V} (hxy : G.Adj x y) (hnotri : ∀ z, ¬(G.Adj x z ∧ G.Adj y z)) :
    ∃ (k : ℕ) (c : G.Walk x x), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k + 1 ∧ s(x, y) ∈ c.edges := by
  obtain ⟨k, p, hk, hp, hlen⟩ := dyadic_path_of_no_common_neighbor G hm (G.ne_of_adj hxy) hnotri
  let q : G.Walk y x := Walk.cons hxy.symm Walk.nil
  have hq : q.IsPath := by
    apply Walk.IsPath.mk'
    simp [q, (G.ne_of_adj hxy).symm]
  have hdisj : p.support.tail.Disjoint q.support.tail := by
    intro v hv1 hv2
    have hvx : v = x := by simpa [q] using hv2
    subst hvx
    have hpnodup := hp.support_nodup
    have hpsupp := p.cons_tail_support
    rw [← hpsupp, List.nodup_cons] at hpnodup
    exact hpnodup.1 hv1
  have hlong : 1 < p.length ∨ 1 < q.length := by
    left
    have : 4 ≤ 2 ^ k := by
      have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hk
      norm_num at this; exact this
    omega
  refine ⟨k, p.append q, hk, hp.isCycle_append hq hdisj hlong, ?_, ?_⟩
  · simp [q, Walk.length_append, hlen]
  · simp [q, Walk.edges_append, Sym2.eq_swap]

/-- **Unified Bipartite Exclusion**:
    Every `MinimalBad G` is nonbipartite (covers all 6 bipartite leaves `C-B, S-B, H-B-*` at once). -/
theorem unified_bipartite_exclusion {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (hB : Bip G) : False := by
  obtain ⟨color, hproper⟩ := hB
  obtain ⟨⟨a, ha⟩, _⟩ := hm.1
  obtain ⟨b, hab⟩ := (G.degree_pos_iff_exists_adj a).mp (by omega)
  have hnotri : ∀ z, ¬(G.Adj a z ∧ G.Adj b z) := by
    intro z ⟨haz, hbz⟩
    have h1 := hproper a b hab
    have h2 := hproper a z haz
    have h3 := hproper b z hbz
    cases color a <;> cases color b <;> cases color z <;> simp_all
  obtain ⟨k, p, hk, _, hlen⟩ := dyadic_path_of_no_common_neighbor G hm (G.ne_of_adj hab) hnotri
  have hpar : ∀ {u v : V} (w : G.Walk u v), (w.length % 2 = 0) ↔ (color u = color v) := by
    intro u v w
    induction w with
    | nil => simp
    | @cons x y z hxy rest ih =>
      have hcol := hproper x y hxy
      simp only [Walk.length_cons]
      cases hx : color x <;> cases hy : color y <;> cases hz : color z <;> simp_all <;> omega
  have heven : p.length % 2 = 0 := by
    rw [hlen]
    cases k with
    | zero => omega
    | succ j => rw [pow_succ]; omega
  exact hproper a b hab ((hpar p).mp heven)

/-! ### Part 4: Class `H` High-Degree Common-Neighbor Dyadic Path Theorem -/

/-- In `MinimalBad G`, if `4 ≤ G.degree z` and `x, y` are distinct non-adjacent neighbors of `z`,
    then `G` contains a simple `x`–`y` path of length `2 ^ k` (`k ≥ 2`) avoiding `{xz, yz}`. -/
theorem class_h_common_neighbor_dyadic_path {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {z x y : V} (hz : 4 ≤ G.degree z) (hzx : G.Adj z x) (hzy : G.Adj z y)
    (hxy : x ≠ y) (hnxy : ¬G.Adj x y) :
    ∃ (k : ℕ) (p : G.Walk x y), 2 ≤ k ∧ p.IsPath ∧ p.length = 2 ^ k ∧
      s(x, z) ∉ p.edges ∧ s(y, z) ∉ p.edges := by
  classical
  have huniq : ∀ u, G.Adj x u → G.Adj y u → u = z := by
    intro u hxu hyu
    by_contra huz
    exact hm.2.1 (rectangle_power G (G.ne_of_adj hzx).symm hxy (G.ne_of_adj hxu)
      (G.ne_of_adj hzy) (Ne.symm huz) (G.ne_of_adj hyu).symm
      hzx.symm hzy hyu hxu.symm)
  let W := {v : V // v ≠ y}
  let H := identifyGraph G x y
  let _ : DecidableRel H.Adj := Classical.decRel _
  obtain ⟨⟨a, ha⟩, ⟨w, hw⟩⟩ := hm.1
  have hV : 4 ≤ Fintype.card V := by
    have := G.degree_lt_card_verts a
    omega
  have hW : Fintype.card W + 1 = Fintype.card V := by
    rw [Fintype.card_subtype,
      show (Finset.univ.filter (fun v : V => v ≠ y)) = Finset.univ.erase y by ext v; simp]
    exact Finset.card_erase_add_one (Finset.mem_univ y)
  have hdx : 2 ≤ G.degree x := no_small_defect G hm x
  have hdy : 2 ≤ G.degree y := no_small_defect G hm y
  have hzy_ne : z ≠ y := G.ne_of_adj hzy
  have hdeg_z : 3 ≤ H.degree ⟨z, hzy_ne⟩ := by
    let f : ↥((G.neighborFinset z).erase y) → H.neighborSet ⟨z, hzy_ne⟩ := fun u =>
      ⟨⟨u.1, (Finset.mem_erase.mp u.2).1⟩,
        ⟨fun h => (G.ne_of_adj ((G.mem_neighborFinset z u.1).mp (Finset.mem_erase.mp u.2).2))
          (congrArg Subtype.val h).symm,
         Or.inl ((G.mem_neighborFinset z u.1).mp (Finset.mem_erase.mp u.2).2)⟩⟩
    have hfinj : Function.Injective f := by
      intro u1 u2 he
      apply Subtype.ext
      exact congrArg (fun t : H.neighborSet ⟨z, hzy_ne⟩ => t.1.1) he
    have hc := Fintype.card_le_of_injective f hfinj
    rw [SimpleGraph.card_neighborSet_eq_degree, Fintype.card_coe] at hc
    have he := Finset.card_erase_add_one ((G.mem_neighborFinset z y).mpr hzy)
    rw [G.card_neighborFinset_eq_degree] at he
    omega
  have hdeg_merged : 3 ≤ H.degree ⟨x, hxy⟩ := by
    let A := G.neighborFinset x
    let B := (G.neighborFinset y).erase z
    have hAB : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro u huA huB
      have h1 := (G.mem_neighborFinset x u).mp huA
      have h2 := (G.mem_neighborFinset y u).mp (Finset.mem_erase.mp huB).2
      exact (Finset.mem_erase.mp huB).1 (huniq u h1 h2)
    let f : ↥(A ∪ B) → H.neighborSet ⟨x, hxy⟩ := fun u =>
      ⟨⟨u.1, by
        intro huy
        rcases Finset.mem_union.mp u.2 with hA | hB
        · exact hnxy (huy ▸ (G.mem_neighborFinset x u.1).mp hA)
        · exact (G.loopless y) (huy ▸ (G.mem_neighborFinset y u.1).mp (Finset.mem_erase.mp hB).2)⟩,
       ⟨by
          intro he
          have hux : u.1 = x := (congrArg Subtype.val he).symm
          rcases Finset.mem_union.mp u.2 with hA | hB
          · exact (G.loopless x) (hux ▸ (G.mem_neighborFinset x u.1).mp hA)
          · exact hnxy (hux ▸ (G.mem_neighborFinset y u.1).mp (Finset.mem_erase.mp hB).2).symm,
        by
          rcases Finset.mem_union.mp u.2 with hA | hB
          · exact Or.inl ((G.mem_neighborFinset x u.1).mp hA)
          · exact Or.inr (Or.inl ⟨rfl, (G.mem_neighborFinset y u.1).mp (Finset.mem_erase.mp hB).2⟩)⟩⟩
    have hfinj : Function.Injective f := by
      intro u1 u2 he
      apply Subtype.ext
      exact congrArg (fun t : H.neighborSet ⟨x, hxy⟩ => t.1.1) he
    have hc := Fintype.card_le_of_injective f hfinj
    rw [SimpleGraph.card_neighborSet_eq_degree, Fintype.card_coe,
      Finset.card_union_of_disjoint hAB] at hc
    have hBcard := Finset.card_erase_add_one ((G.mem_neighborFinset y z).mpr hzy.symm)
    rw [G.card_neighborFinset_eq_degree] at hBcard
    have hAcard : A.card = G.degree x := G.card_neighborFinset_eq_degree x
    omega
  have hdeg_other : ∀ u : W, u.1 ≠ x → u.1 ≠ z → H.degree u = G.degree u.1 := by
    intro u hux huz
    exact identifyGraph_degree_ne G hxy u hux (fun ⟨h1, h2⟩ => huz (huniq u.1 h1.symm h2.symm))
  have hnear : Near H := by
    by_cases hwy : w = y
    · subst hwy
      apply near_of_except H (⟨x, hxy⟩ : W) (by omega)
      intro u hu
      have hux : u.1 ≠ x := fun h => hu (Subtype.ext h)
      by_cases huz : u.1 = z
      · have he : u = ⟨z, hzy_ne⟩ := Subtype.ext huz
        rw [he]; exact hdeg_z
      · rw [hdeg_other u hux huz]
        exact hw u.1 u.2
    · apply near_of_except H (⟨w, hwy⟩ : W) (by omega)
      intro u hu
      by_cases hux : u.1 = x
      · have he : u = ⟨x, hxy⟩ := Subtype.ext hux
        rw [he]; exact hdeg_merged
      by_cases huz : u.1 = z
      · have he : u = ⟨z, hzy_ne⟩ := Subtype.ext huz
        rw [he]; exact hdeg_z
      · rw [hdeg_other u hux huz]
        exact hw u.1 (fun h => hu (Subtype.ext h))
  have hpow : HasPower H := hm.2.2.1 W H (by omega) hnear
  obtain ⟨k, p, hk, hp, hlen, havoid⟩ := dyadic_path_of_identify_power hm.2.1 hxy hpow
  obtain ⟨h1, h2⟩ := havoid z hzx.symm hzy.symm
  exact ⟨k, p, hk, hp, hlen, h1, h2⟩

/-! ### Part 5: Cubic Triangle-Free Bilateral 2-Path & All-Pairs Dyadic Path Theorems -/

/-- Helper: in a cubic graph, any two distinct neighbors `u1, u2` of `v` determine a unique
    third neighbor `u3` such that `N(v) = {u1, u2, u3}`. -/
theorem cubic_three_neighbors {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hC : Cubic G)
    {v u1 u2 : V} (hv1 : G.Adj v u1) (hv2 : G.Adj v u2) (h12 : u1 ≠ u2) :
    ∃ u3, G.Adj v u3 ∧ u3 ≠ u1 ∧ u3 ≠ u2 ∧
      ∀ x, G.Adj v x ↔ x = u1 ∨ x = u2 ∨ x = u3 := by
  classical
  have hncard : (G.neighborFinset v).card = 3 := by
    rw [G.card_neighborFinset_eq_degree, hC v]
  have h3ex : ∃ u3, G.Adj v u3 ∧ u3 ≠ u1 ∧ u3 ≠ u2 := by
    by_contra hbad
    have hsub : G.neighborFinset v ⊆ ({u1, u2} : Finset V) := by
      intro x hx
      have hxv := (G.mem_neighborFinset v x).mp hx
      by_cases h1 : x = u1
      · simp [h1]
      by_cases h2 : x = u2
      · simp [h2]
      exact False.elim (hbad ⟨x, hxv, h1, h2⟩)
    have hc := Finset.card_le_card hsub
    have h2 : ({u1, u2} : Finset V).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨u3, hv3, h31, h32⟩ := h3ex
  have hsub : ({u1, u2, u3} : Finset V) ⊆ G.neighborFinset v := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact (G.mem_neighborFinset v u1).mpr hv1
    · exact (G.mem_neighborFinset v u2).mpr hv2
    · exact (G.mem_neighborFinset v u3).mpr hv3
  have hcard3 : ({u1, u2, u3} : Finset V).card = 3 := by
    simp [h12, h31.symm, h32.symm]
  have heq : ({u1, u2, u3} : Finset V) = G.neighborFinset v :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  refine ⟨u3, hv3, h31, h32, fun x => ?_⟩
  rw [← G.mem_neighborFinset, ← heq]
  simp

/-- In a cubic triangle-free `MinimalBad G` (`C-N-2, C-N-3, C-N-R`), for every 2-path
    `u1 - v - u2`, `G - v` contains a simple `u1`–`u2` path of length `2 ^ k - 1` (`k ≥ 2`). -/
theorem cubic_triangle_free_two_path_mersenne {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (hC : Cubic G) (hN : ¬Triangle G)
    {v u1 u2 : V} (hv1 : G.Adj v u1) (hv2 : G.Adj v u2) (h12 : u1 ≠ u2) :
    ∃ (k : ℕ) (p : (G.induce {x | x ≠ v}).Walk ⟨u1, (G.ne_of_adj hv1).symm⟩ ⟨u2, (G.ne_of_adj hv2).symm⟩),
      2 ≤ k ∧ p.IsPath ∧ p.length = 2 ^ k - 1 := by
  classical
  have hn12 : ¬G.Adj u1 u2 := fun h => hN ⟨v, u1, u2, hv1, h, hv2.symm⟩
  obtain ⟨u3, hv3, h31, h32, hN_eq⟩ := cubic_three_neighbors G hC hv1 hv2 h12
  let W := {x : V // x ≠ v}
  let K : SimpleGraph W := G.induce {x | x ≠ v}
  let _ : DecidableRel K.Adj := inferInstanceAs (DecidableRel (G.induce {x | x ≠ v}).Adj)
  let U1 : W := ⟨u1, (G.ne_of_adj hv1).symm⟩
  let U2 : W := ⟨u2, (G.ne_of_adj hv2).symm⟩
  let U3 : W := ⟨u3, (G.ne_of_adj hv3).symm⟩
  have hU12 : U1 ≠ U2 := fun h => h12 (congrArg Subtype.val h)
  have hKnot : ¬K.Adj U1 U2 := hn12
  let H : SimpleGraph W := K ⊔ SimpleGraph.edge U1 U2
  let _ : DecidableRel H.Adj := Classical.decRel _
  have hV : 4 ≤ Fintype.card V := by
    have := G.degree_lt_card_verts v
    have := hC v
    omega
  have hW : Fintype.card W + 1 = Fintype.card V := by
    rw [Fintype.card_subtype,
      show (Finset.univ.filter (fun x : V => x ≠ v)) = Finset.univ.erase v by ext x; simp]
    exact Finset.card_erase_add_one (Finset.mem_univ v)
  have hda : H.degree U1 = K.degree U1 + 1 := degree_add_new_edge_left K U1 U2 hU12 hKnot
  have hdb : H.degree U2 = K.degree U2 + 1 := degree_add_new_edge_right K U1 U2 hU12 hKnot
  have hnear : Near H := by
    apply near_of_except H U3 (by omega)
    intro x hx
    have hd := induce_delete_degree G v x
    change K.degree x + (if G.Adj x.1 v then 1 else 0) = G.degree x.1 at hd
    rw [hC x.1] at hd
    by_cases hx1 : x = U1
    · subst hx1
      rw [ite_eq_left hv1.symm] at hd
      omega
    by_cases hx2 : x = U2
    · subst hx2
      rw [ite_eq_left hv2.symm] at hd
      omega
    · have hnot : ¬G.Adj x.1 v := by
        intro hadj
        rcases (hN_eq x.1).mp hadj.symm with h | h | h
        · exact hx1 (Subtype.ext h)
        · exact hx2 (Subtype.ext h)
        · exact hx (Subtype.ext h)
      rw [ite_eq_right hnot, add_zero] at hd
      have hk3 : 3 ≤ K.degree x := by omega
      exact hk3.trans (K.degree_le_of_le (v := x) (H := H) le_sup_left)
  obtain ⟨k, a, c, hk, hc, hlen⟩ := hm.2.2.1 W H (by omega) hnear
  have hKfree : ¬HasPower K := fun hp => hm.2.1 (power_induce G _ hp)
  have hedge : s(U1, U2) ∈ c.edges := by
    by_contra hno
    have htr : ∀ e ∈ c.edges, e ∈ K.edgeSet := by
      intro e he
      have hmem := c.edges_subset_edgeSet he
      rw [SimpleGraph.edgeSet_sup] at hmem
      rcases hmem with hk' | hed
      · exact hk'
      · rw [SimpleGraph.edgeSet_edge_of_ne hU12] at hed
        exact False.elim (hno ((Set.mem_singleton_iff.mp hed) ▸ he))
    exact hKfree ⟨k, a, c.transfer K htr, hk, hc.transfer htr, by simpa using hlen⟩
  have hU1mem : U1 ∈ c.support := mem_support_of_mem_edge c hedge (by simp)
  let c' := c.rotate hU1mem
  have hc' : c'.IsCycle := hc.rotate hU1mem
  have hlen' : c'.length = 2 ^ k := by rw [Walk.length_rotate, hlen]
  have hedge' : s(U1, U2) ∈ c'.edges := by
    have hperm := Walk.edges_rotate c hU1mem
    exact hperm.mem_iff.mpr hedge
  have htransfer_tail : ∀ (r : H.Walk U2 U1), r.IsPath → s(U1, U2) ∉ r.edges →
      r.length = 2 ^ k - 1 →
      ∃ p : K.Walk U1 U2, p.IsPath ∧ p.length = 2 ^ k - 1 := by
    intro r hr hno hrlen
    have htr : ∀ e ∈ r.reverse.edges, e ∈ K.edgeSet := by
      intro e he
      have hmem := r.reverse.edges_subset_edgeSet he
      rw [SimpleGraph.edgeSet_sup] at hmem
      rcases hmem with hk' | hed
      · exact hk'
      · rw [SimpleGraph.edgeSet_edge_of_ne hU12] at hed
        have he' : s(U1, U2) ∈ r.edges := by
          rw [Set.mem_singleton_iff.mp hed] at he
          rwa [Walk.edges_reverse, List.mem_reverse] at he
        exact False.elim (hno he')
    refine ⟨r.reverse.transfer K htr, hr.reverse.transfer htr, ?_⟩
    simpa using hrlen
  cases hc_eq : c' with
  | nil =>
    have := hc'.three_le_length
    rw [hc_eq] at this; simp at this
  | @cons _ b _ e1 r =>
    by_cases hb : b = U2
    · subst hb
      have hrnodup : (s(U1, U2) :: r.edges).Nodup := by
        have := hc'.isTrail.edges_nodup
        rwa [hc_eq, Walk.edges_cons] at this
      have hno : s(U1, U2) ∉ r.edges := (List.nodup_cons.mp hrnodup).1
      have hrpath : r.IsPath := by
        apply Walk.IsPath.mk'
        have := hc'.support_nodup
        rwa [hc_eq, Walk.support_cons, List.tail_cons] at this
      have hrlen : r.length = 2 ^ k - 1 := by
        rw [hc_eq, Walk.length_cons] at hlen'; omega
      obtain ⟨p, hp, hpl⟩ := htransfer_tail r hrpath hno hrlen
      exact ⟨k, p, hk, hp, hpl⟩
    · -- Then `s(U1, U2)` must be the last edge of `c'`, i.e. the first edge of `c'.reverse`!
      have hc'rev : c'.reverse.IsCycle := hc'.reverse
      have hlen_rev : c'.reverse.length = 2 ^ k := by simpa using hlen'
      cases hrev_eq : c'.reverse with
      | nil =>
        have := hc'rev.three_le_length
        rw [hrev_eq] at this; simp at this
      | @cons _ b' _ e2 r' =>
        have hb' : b' = U2 := by
          -- Every occurrence of `s(U1, U2)` in `c'.edges` must be at the start or end since `U1` appears once in `c'.support.tail`.
          have hmem_rev : s(U1, U2) ∈ c'.reverse.edges := by
            rw [Walk.edges_reverse, List.mem_reverse]; exact hedge'
          rw [hrev_eq, Walk.edges_cons, List.mem_cons] at hmem_rev
          rcases hmem_rev with hhead | htail
          · rcases Sym2.eq_iff.mp hhead with ⟨_, h2⟩ | ⟨h1, _⟩
            · exact h2.symm
            · exact False.elim (hU12 h1.symm)
          · -- If `s(U1, U2) ∈ r'.edges`, then `U1 ∈ r'.support` — check where `U1` can be!
            -- Wait: `r'` ends at `U1`, so `s(U1, U2)` could be the LAST edge of `r'`, which is the FIRST edge of `c'` = `s(U1, b)`!
            have h1 : c' = c'.reverse.reverse := c'.reverse_reverse.symm
            rw [hrev_eq, Walk.reverse_cons] at h1
            -- Actually simpler: `r'.reverse` starts at `U1` and ends at `b'`, and `r'.reverse` has `s(U1, b)` as its first edge?
            -- Let's check: `r'` has `s(U1, U2) ∈ r'.edges`. Write `r'.reverse = cons _ _`!
            cases hr'_eq : r'.reverse with
            | nil =>
              have := Walk.length_eq_zero_iff.mpr hr'_eq
              have h3 := hc'rev.three_le_length
              rw [hrev_eq, Walk.length_cons] at h3
              simp at this; omega
            | @cons _ b2 _ e3 rest =>
              have hb2 : b2 = b := by
                have h2 : c' = (Walk.cons e3 rest).append (Walk.cons e2.symm Walk.nil) := by
                  rw [h1, hr'_eq]
                rw [hc_eq, Walk.cons_append] at h2
                injection h2 with _ h2'
                exact h2'.symm
              subst hb2
              have hmem_rest : s(U1, U2) ∈ (Walk.cons e3 rest).edges := by
                rw [← hr'_eq, Walk.edges_reverse, List.mem_reverse]; exact htail
              rw [Walk.edges_cons, List.mem_cons] at hmem_rest
              rcases hmem_rest with hfirst | hinrest
              · rcases Sym2.eq_iff.mp hfirst with ⟨_, h2⟩ | ⟨h1', _⟩
                · exact False.elim (hb h2.symm)
                · exact False.elim (hU12 h1'.symm)
              · -- `U1 ∈ rest.support`, contradicting `c'.support.tail.Nodup`!
                have hU1_rest : U1 ∈ rest.support := mem_support_of_mem_edge rest hinrest (by simp)
                have hsupp_rev : c'.reverse.support.tail = rest.reverse.support ++ [U1] := by
                  have hr'_orig : r' = rest.reverse.append (Walk.cons e3.symm Walk.nil) := by
                    have := congrArg Walk.reverse hr'_eq
                    simpa using this
                  rw [hrev_eq, Walk.support_cons, List.tail_cons, hr'_orig, Walk.support_append]
                  simp
                have hnod := hc'rev.support_nodup
                rw [hsupp_rev, List.nodup_append] at hnod
                have hU1_rev : U1 ∈ rest.reverse.support := by
                  rw [Walk.support_reverse, List.mem_reverse]; exact hU1_rest
                exact False.elim (hnod.2.2 U1 hU1_rev (by simp) rfl)
        subst hb'
        have hrnodup : (s(U1, U2) :: r'.edges).Nodup := by
          have := hc'rev.isTrail.edges_nodup
          rwa [hrev_eq, Walk.edges_cons] at this
        have hno : s(U1, U2) ∉ r'.edges := (List.nodup_cons.mp hrnodup).1
        have hrpath : r'.IsPath := by
          apply Walk.IsPath.mk'
          have := hc'rev.support_nodup
          rwa [hrev_eq, Walk.support_cons, List.tail_cons] at this
        have hrlen : r'.length = 2 ^ k - 1 := by
          rw [hrev_eq, Walk.length_cons] at hlen_rev; omega
        obtain ⟨p, hp, hpl⟩ := htransfer_tail r' hrpath hno hrlen
        exact ⟨k, p, hk, hp, hpl⟩

/-- In a cubic triangle-free `MinimalBad G` (`C-N-2, C-N-3, C-N-R`), for every 2-path
    `u1 - v - u2`, `G - v` ALSO contains a simple `u1`–`u2` path of length `2 ^ m` (`m ≥ 2`). -/
theorem cubic_triangle_free_two_path_dyadic {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (hC : Cubic G) (hN : ¬Triangle G)
    {v u1 u2 : V} (hv1 : G.Adj v u1) (hv2 : G.Adj v u2) (h12 : u1 ≠ u2) :
    ∃ (m : ℕ) (p : (G.induce {x | x ≠ v}).Walk ⟨u1, (G.ne_of_adj hv1).symm⟩ ⟨u2, (G.ne_of_adj hv2).symm⟩),
      2 ≤ m ∧ p.IsPath ∧ p.length = 2 ^ m := by
  classical
  have hn12 : ¬G.Adj u1 u2 := fun h => hN ⟨v, u1, u2, hv1, h, hv2.symm⟩
  obtain ⟨u3, hv3, h31, h32, hN_eq⟩ := cubic_three_neighbors G hC hv1 hv2 h12
  let W := {x : V // x ≠ v}
  let K : SimpleGraph W := G.induce {x | x ≠ v}
  let _ : DecidableRel K.Adj := inferInstanceAs (DecidableRel (G.induce {x | x ≠ v}).Adj)
  let U1 : W := ⟨u1, (G.ne_of_adj hv1).symm⟩
  let U2 : W := ⟨u2, (G.ne_of_adj hv2).symm⟩
  let U3 : W := ⟨u3, (G.ne_of_adj hv3).symm⟩
  have hU12 : U1 ≠ U2 := fun h => h12 (congrArg Subtype.val h)
  have hU32 : U3 ≠ U2 := fun h => h32 (congrArg Subtype.val h)
  have hKfree : ¬HasPower K := fun hp => hm.2.1 (power_induce G _ hp)
  have hKdisj : ∀ z : W, ¬(K.Adj U1 z ∧ K.Adj U2 z) := by
    intro z ⟨h1, h2⟩
    exact hm.2.1 (rectangle_power G (G.ne_of_adj hv1) (G.ne_of_adj hv2) z.2.symm
      h12 (G.ne_of_adj h1) (G.ne_of_adj h2) hv1 h1 h2.symm hv2.symm)
  let W2 := {x : W // x ≠ U2}
  let H := identifyGraph K U1 U2
  let _ : DecidableRel H.Adj := Classical.decRel _
  have hV : 4 ≤ Fintype.card V := by
    have := G.degree_lt_card_verts v
    have := hC v
    omega
  have hW : Fintype.card W + 1 = Fintype.card V := by
    rw [Fintype.card_subtype,
      show (Finset.univ.filter (fun x : V => x ≠ v)) = Finset.univ.erase v by ext x; simp]
    exact Finset.card_erase_add_one (Finset.mem_univ v)
  have hW2 : Fintype.card W2 + 1 = Fintype.card W := by
    rw [Fintype.card_subtype,
      show (Finset.univ.filter (fun x : W => x ≠ U2)) = Finset.univ.erase U2 by ext x; simp]
    exact Finset.card_erase_add_one (Finset.mem_univ U2)
  have hKdeg1 : K.degree U1 = 2 := by
    have hd := induce_delete_degree G v U1
    change K.degree U1 + (if G.Adj u1 v then 1 else 0) = G.degree u1 at hd
    rw [ite_eq_left hv1.symm, hC u1] at hd; omega
  have hKdeg2 : K.degree U2 = 2 := by
    have hd := induce_delete_degree G v U2
    change K.degree U2 + (if G.Adj u2 v then 1 else 0) = G.degree u2 at hd
    rw [ite_eq_left hv2.symm, hC u2] at hd; omega
  have hdeg_merged : H.degree ⟨U1, hU12⟩ = 4 := by
    have hd := identifyGraph_degree_merged K hU12 hKdisj
    have hnot : ¬K.Adj U1 U2 := hn12
    rw [ite_eq_right hnot, hKdeg1, hKdeg2] at hd
    omega
  have hnear : Near H := by
    apply near_of_except H (⟨U3, hU32⟩ : W2) (by omega)
    intro x hx
    by_cases hx1 : x.1 = U1
    · have he : x = ⟨U1, hU12⟩ := Subtype.ext hx1
      rw [he, hdeg_merged]; decide
    · have hdeg := identifyGraph_degree_ne K hU12 x hx1 (fun ⟨h1, h2⟩ => hKdisj x.1 ⟨h1.symm, h2.symm⟩)
      rw [hdeg]
      have hd := induce_delete_degree G v x.1
      change K.degree x.1 + (if G.Adj x.1.1 v then 1 else 0) = G.degree x.1.1 at hd
      rw [hC x.1.1] at hd
      have hnot : ¬G.Adj x.1.1 v := by
        intro hadj
        rcases (hN_eq x.1.1).mp hadj.symm with h | h | h
        · exact hx1 (Subtype.ext h)
        · exact x.2 (Subtype.ext h)
        · exact hx (Subtype.ext (Subtype.ext h))
      rw [ite_eq_right hnot, add_zero] at hd
      omega
  have hpow : HasPower H := hm.2.2.1 W2 H (by omega) hnear
  obtain ⟨m, p, hm2, hp, hlen, _⟩ := dyadic_path_of_identify_power hKfree hU12 hpow
  exact ⟨m, p, hm2, hp, hlen⟩

/-- **All-Pairs Dyadic Path Theorem for Cubic Triangle-Free `MinimalBad`**:
    In every cubic triangle-free `MinimalBad G` (`C-N-2`, `C-N-3`, `C-N-R`),
    EVERY pair of distinct vertices `x ≠ y` is joined by a simple `x`–`y` path of
    length `2 ^ k` for some `k ≥ 2`. -/
theorem all_pairs_dyadic_path_cubic_triangle_free {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (hC : Cubic G) (hN : ¬Triangle G) {x y : V} (hxy : x ≠ y) :
    ∃ (k : ℕ) (p : G.Walk x y), 2 ≤ k ∧ p.IsPath ∧ p.length = 2 ^ k := by
  by_cases hcom : ∃ v, G.Adj x v ∧ G.Adj y v
  · obtain ⟨v, hxv, hyv⟩ := hcom
    obtain ⟨m, p, hm2, hp, hlen⟩ :=
      cubic_triangle_free_two_path_dyadic G hm hC hN hxv.symm hyv.symm hxy
    let f : G.induce {z | z ≠ v} →g G := ⟨Subtype.val, fun h => h⟩
    refine ⟨m, p.map f, hm2, ?_, by simpa using hlen⟩
    exact (Walk.isPath_map_iff_of_injective Subtype.val_injective).mpr hp
  · push Not at hcom
    exact dyadic_path_of_no_common_neighbor G hm hxy (fun z ⟨h1, h2⟩ => hcom z h1 h2)

#print axioms high_degree_independent
#print axioms exists_low_degree_neighbor
#print axioms class_h_v3_ge_two_v4
#print axioms class_h_v3_two_thirds
#print axioms dyadic_path_of_identify_power
#print axioms dyadic_path_of_no_common_neighbor
#print axioms non_triangle_edge_odd_power_cycle
#print axioms unified_bipartite_exclusion
#print axioms class_h_common_neighbor_dyadic_path
#print axioms cubic_triangle_free_two_path_mersenne
#print axioms cubic_triangle_free_two_path_dyadic
#print axioms all_pairs_dyadic_path_cubic_triangle_free
end E64Wave2Agent4
