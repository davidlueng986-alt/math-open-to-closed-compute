import Shadow
import Core
import Leaves
import Descent

/-!
Wave 4 Agent #5: Two-Defect Global Collapse (`EG2` ↔ `EGRob` ⟹ Full Erdős #64 CLOSED).

This module introduces the two-defect strengthening `Near2` / `EG2` and proves its exact
logical equivalence with Edge-Robust Erdős–Gyárfás (`EGRob`: every finite graph with
minimum degree ≥ 3 retains a 2^k-cycle after deleting any single edge, i.e. τ_e(C_{2^k}) ≥ 2).
Both statements unconditionally imply the full original Erdős–Gyárfás conjecture and
simultaneously close all 26 leaves of the 1-defect `MinimalBad` Closure DAG.

Moreover, any minimal counterexample `MinimalBad2` collapses unconditionally to a single
2-defect nonbipartite core (`EG2-CORE`):
- exact two defects u ≠ v (all cubic and 1-defect classes eliminated),
- defects are nonadjacent (¬G.Adj u v),
- all neighbors of u and v are cubic (degree = 3),
- high-degree vertices V_{≥4} form an independent set,
- nonbipartite (¬Bip G),
- no defect-free 2-edge cut (every nontrivial ≤ 2-edge cut separates u and v).

All proofs are all-order, with no sorry, no native_decide, and standard axioms only.
-/

namespace E64Wave4Agent5EG2
open SimpleGraph Erdos64Closure E64Core E64Leaves Erdos64Descent
universe u

/-- Two-defect Near predicate: at least 4 vertices, minimum degree ≥ 2,
and at most two vertices of degree < 3. -/
def Near2 {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop :=
  4 ≤ Fintype.card V ∧ (∀ v, 2 ≤ G.degree v) ∧
    ∃ u w : V, ∀ v, v ≠ u → v ≠ w → 3 ≤ G.degree v

/-- Order-minimal, then edge-minimal power-free Near2 graph. -/
def MinimalBad2 {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop :=
  Near2 G ∧ ¬HasPower G ∧
  (∀ (W : Type u) (H : SimpleGraph W) [Fintype W] [DecidableRel H.Adj],
    Fintype.card W < Fintype.card V → Near2 H → HasPower H) ∧
  (∀ (H : SimpleGraph V) [DecidableRel H.Adj], H ≤ G → Near2 H → H = G)

/-- Original Erdős #64 statement matching Formal Conjectures. -/
def Erdos64Original : Prop :=
  ∀ (V : Type u) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    G.minDegree ≥ 3 → HasPower G

/-- Two-Defect Erdős–Gyárfás Conjecture (`EG2`). -/
def EG2 : Prop :=
  ∀ (V : Type u) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    Near2 G → HasPower G

/-- Edge-Robust Erdős–Gyárfás Conjecture (`EGRob`): deleting any single edge from a
graph with δ(G) ≥ 3 still leaves a 2^k-cycle (equivalently τ_e(C_{2^k}(G)) ≥ 2). -/
def EGRob : Prop :=
  ∀ (V : Type u) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    G.minDegree ≥ 3 → ∀ a b : V, G.Adj a b → HasPower (G \ SimpleGraph.edge a b)

/-- Every finite graph with minimum degree ≥ 3 is Near2. -/
theorem near2_of_min_deg_three {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hmin : G.minDegree ≥ 3) :
    Near2 G := by
  rcases isEmpty_or_nonempty V with hempty | hne
  · let _ : IsEmpty V := hempty
    have hz : G.minDegree = 0 := SimpleGraph.minDegree_of_subsingleton G
    omega
  · obtain ⟨w⟩ := hne
    have hall : ∀ v, 3 ≤ G.degree v := fun v => hmin.trans (G.minDegree_le_degree v)
    have hcard : 4 ≤ Fintype.card V := by
      have h1 := hall w
      have h2 := G.degree_lt_card_verts w
      omega
    exact ⟨hcard, fun v => by have := hall v; omega, ⟨w, w, fun v _ _ => hall v⟩⟩

/-- Whole-Problem Closure Gate: `EG2` unconditionally implies full Erdős #64. -/
theorem eg2_implies_erdos64 : EG2.{u} → Erdos64Original.{u} := by
  intro heg V G _ _ hmin
  exact heg V G (near2_of_min_deg_three G hmin)

/-- Every 1-defect `MinimalBad` graph is `Near2`. -/
theorem near2_of_minimal_bad {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G) :
    Near2 G := by
  obtain ⟨⟨a, ha⟩, ⟨w, hw⟩⟩ := hm.1
  have hcard : 4 ≤ Fintype.card V := by
    have hlt := G.degree_lt_card_verts a
    omega
  exact ⟨hcard, no_small_defect G hm, ⟨w, w, fun v h1 _ => hw v h1⟩⟩

/-- `EG2` simultaneously closes all 26 leaves of the `MinimalBad` Closure DAG. -/
theorem eg2_closes_all_leaves : EG2.{u} → ∀ l : Leaf, Exclude.{u} l := by
  intro heg l V G _ _ hm _
  exact hm.2.1 (heg V G (near2_of_minimal_bad G hm))

/-- Order-minimal, then edge-minimal `MinimalBad2` selection. -/
theorem minimal_bad2_exists
    (bad : ∃ (V : Type u) (_ : Fintype V) (G : SimpleGraph V)
      (_ : DecidableRel G.Adj), Near2 G ∧ ¬HasPower G) :
    ∃ (V : Type u) (_ : Fintype V) (G : SimpleGraph V)
      (_ : DecidableRel G.Adj), MinimalBad2 G := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ (V : Type u) (f : Fintype V) (G : SimpleGraph V)
      (d : DecidableRel G.Adj), @Fintype.card V f = n ∧ @Near2 V f G d ∧ ¬HasPower G
  have hex : ∃ n, P n := by
    obtain ⟨V, f, G, d, h⟩ := bad
    exact ⟨@Fintype.card V f, V, f, G, d, rfl, h⟩
  obtain ⟨V, f, G, d, _, hn, hfree⟩ := Nat.find_spec hex
  let _ : Fintype V := f
  let _ : DecidableRel G.Adj := d
  let Q : ℕ → Prop := fun m =>
    ∃ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      H ≤ G ∧ @Near2 V f H dH ∧ @Finset.card (Sym2 V) H.edgeFinset = m
  have hQ : ∃ m, Q m := ⟨G.edgeFinset.card, G, d, le_rfl, hn, rfl⟩
  obtain ⟨H, dH, hHG, hnH, _⟩ := Nat.find_spec hQ
  let _ : DecidableRel H.Adj := dH
  refine ⟨V, f, H, dH, hnH, fun h => hfree (power_mono hHG h), ?_, ?_⟩
  · intro W J fW dJ hlt hnJ
    by_contra hJ
    have hp : P (@Fintype.card W fW) := ⟨W, fW, J, dJ, rfl, hnJ, hJ⟩
    have hmin := Nat.find_min' hex hp
    omega
  · intro J dJ hJ hnJ
    by_contra hneq
    have hstrict : J < H := lt_of_le_of_ne hJ hneq
    have hlt : J.edgeFinset.card < H.edgeFinset.card :=
      Finset.card_lt_card (SimpleGraph.edgeFinset_strict_mono hstrict)
    have hjQ : Q J.edgeFinset.card := ⟨J, dJ, hJ.trans hHG, hnJ, rfl⟩
    have hmin := Nat.find_min' hQ hjQ
    omega

/-- Helper: deleting an edge `ab` strictly decreases the graph. -/
private theorem sdiff_edge_ne {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) {a b : V} (hab : G.Adj a b) :
    G \ SimpleGraph.edge a b ≠ G := by
  intro hEq
  have he : (G \ SimpleGraph.edge a b).Adj a b := by
    rw [hEq]
    exact hab
  have hno := (SimpleGraph.sdiff_adj G (SimpleGraph.edge a b) a b).mp he
  exact hno.2 ((SimpleGraph.edge_adj a b a b).mpr ⟨Or.inl ⟨rfl, rfl⟩, G.ne_of_adj hab⟩)

/-- No `MinimalBad2` graph has minimum degree ≥ 3 (eliminates all cubic / 0-defect cases). -/
theorem minimal_bad2_not_all_ge_three {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad2 G) :
    ¬(∀ v, 3 ≤ G.degree v) := by
  classical
  intro hall
  have hposV : 0 < Fintype.card V := by have := hm.1.1; omega
  obtain ⟨a⟩ := Fintype.card_pos_iff.mp hposV
  have hpos : 0 < G.degree a := by have := hall a; omega
  obtain ⟨b, hab⟩ := (G.degree_pos_iff_exists_adj a).mp hpos
  let H := G \ SimpleGraph.edge a b
  let _ : DecidableRel H.Adj := inferInstanceAs (DecidableRel (G \ SimpleGraph.edge a b).Adj)
  have hdegH : ∀ v, H.degree v + (if v = a ∨ v = b then 1 else 0) = G.degree v :=
    erase_edge_degree G a b hab
  have hnH : Near2 H := by
    refine ⟨hm.1.1, ?_, ⟨a, b, ?_⟩⟩
    · intro v
      have hd := hdegH v
      have hv := hall v
      split_ifs at hd <;> omega
    · intro v hva hvb
      have hd := hdegH v
      simp only [hva, hvb, or_self, ↓reduceIte, add_zero] at hd
      rw [hd]
      exact hall v
  exact sdiff_edge_ne G hab (hm.2.2.2 H sdiff_le hnH)

/-- No `MinimalBad2` graph has at most one vertex of degree < 3 (eliminates all S/H 1-defect cases). -/
theorem minimal_bad2_not_one_defect {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad2 G) :
    ∀ w : V, ¬(∀ v, v ≠ w → 3 ≤ G.degree v) := by
  classical
  intro w hrest
  have hw2 : G.degree w = 2 := by
    have hge := hm.1.2.1 w
    by_contra hne
    have hge3 : 3 ≤ G.degree w := by omega
    apply minimal_bad2_not_all_ge_three G hm
    intro v
    by_cases hvw : v = w
    · subst v; exact hge3
    · exact hrest v hvw
  have hncard : (G.neighborFinset w).card = 2 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, hw2]
  obtain ⟨a, b, hab, hN⟩ := Finset.card_eq_two.mp hncard
  have hNbr (x : V) : G.Adj w x ↔ x = a ∨ x = b := by
    rw [← SimpleGraph.mem_neighborFinset, hN]
    simp
  have hwa : G.Adj w a := (hNbr a).mpr (Or.inl rfl)
  have hwb : G.Adj w b := (hNbr b).mpr (Or.inr rfl)
  have haw : a ≠ w := (G.ne_of_adj hwa).symm
  have hbw : b ≠ w := (G.ne_of_adj hwb).symm
  let W := {x : V // x ≠ w}
  let H : SimpleGraph W := G.induce {x | x ≠ w}
  let _ : DecidableRel H.Adj := inferInstanceAs (DecidableRel (G.induce {x | x ≠ w}).Adj)
  have hWcard : Fintype.card W + 1 = Fintype.card V := by
    rw [Fintype.card_subtype,
      show (Finset.univ.filter (fun x : V => x ≠ w)) = Finset.univ.erase w by ext x; simp]
    exact Finset.card_erase_add_one (Finset.mem_univ w)
  have hV5 : 5 ≤ Fintype.card V := by
    by_contra hlt
    have hV4 : Fintype.card V = 4 := by have := hm.1.1; omega
    have hex : ∃ c : V, c ≠ w ∧ c ≠ a ∧ c ≠ b := by
      by_contra hno
      push Not at hno
      have hsub : (Finset.univ : Finset V) ⊆ {w, a, b} := by
        intro x _
        simp only [Finset.mem_insert, Finset.mem_singleton]
        by_cases h1 : x = w
        · exact Or.inl h1
        · by_cases h2 : x = a
          · exact Or.inr (Or.inl h2)
          · exact Or.inr (Or.inr (hno x h1 h2))
      have hc := Finset.card_le_card hsub
      have h3 : ({w, a, b} : Finset V).card ≤ 3 := by
        have h1 := Finset.card_insert_le w ({a, b} : Finset V)
        have h2 := Finset.card_insert_le a ({b} : Finset V)
        simp only [Finset.card_singleton] at h2
        omega
      rw [Finset.card_univ] at hc
      omega
    obtain ⟨c, hcw, hca, hcb⟩ := hex
    have hcdeg : 3 ≤ G.degree c := hrest c hcw
    have hsub : G.neighborFinset c ⊆ Finset.univ.erase c := by
      intro x hx
      rw [Finset.mem_erase]
      exact ⟨(G.ne_of_adj ((G.mem_neighborFinset c x).mp hx)).symm, Finset.mem_univ x⟩
    have hcard_er : (Finset.univ.erase c).card = 3 := by
      have := Finset.card_erase_add_one (Finset.mem_univ c)
      rw [Finset.card_univ, hV4] at this
      omega
    have heq : G.neighborFinset c = Finset.univ.erase c := by
      apply Finset.eq_of_subset_of_card_le hsub
      rw [SimpleGraph.card_neighborFinset_eq_degree, hcard_er]
      exact hcdeg
    have hwc : w ∈ G.neighborFinset c := by
      rw [heq, Finset.mem_erase]
      exact ⟨Ne.symm hcw, Finset.mem_univ w⟩
    have hadj : G.Adj w c := ((G.mem_neighborFinset c w).mp hwc).symm
    rcases (hNbr c).mp hadj with rfl | rfl
    · exact hca rfl
    · exact hcb rfl
  let A : W := ⟨a, haw⟩
  let B : W := ⟨b, hbw⟩
  have hnH : Near2 H := by
    refine ⟨by omega, ?_, ⟨A, B, ?_⟩⟩
    · intro x
      have hd := induce_delete_degree G w x
      change H.degree x + (if G.Adj x.1 w then 1 else 0) = G.degree x.1 at hd
      have hx := hrest x.1 x.2
      split_ifs at hd <;> omega
    · intro x hxA hxB
      have hd := induce_delete_degree G w x
      change H.degree x + (if G.Adj x.1 w then 1 else 0) = G.degree x.1 at hd
      have hnot : ¬G.Adj x.1 w := by
        intro he
        rcases (hNbr x.1).mp he.symm with h | h
        · exact hxA (Subtype.ext h)
        · exact hxB (Subtype.ext h)
      rw [ite_eq_right hnot, add_zero] at hd
      rw [hd]
      exact hrest x.1 x.2
  have hpow : HasPower H := hm.2.2.1 W H (by omega) hnH
  exact hm.2.1 (power_induce G {x | x ≠ w} hpow)

/-- Exact Two-Defect Characterization: every `MinimalBad2` graph has
precisely two distinct degree-2 vertices `u ≠ v`, and all other vertices have degree ≥ 3. -/
theorem minimal_bad2_exact_two_defects {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad2 G) :
    ∃ u v : V, u ≠ v ∧ G.degree u = 2 ∧ G.degree v = 2 ∧
      ∀ x, x ≠ u → x ≠ v → 3 ≤ G.degree x := by
  obtain ⟨u, v, huv_rest⟩ := hm.1.2.2
  have huv : u ≠ v := by
    intro h
    subst h
    exact minimal_bad2_not_one_defect G hm u (fun x hx => huv_rest x hx hx)
  have hu2 : G.degree u = 2 := by
    have hge := hm.1.2.1 u
    by_contra hne
    have hge3 : 3 ≤ G.degree u := by omega
    apply minimal_bad2_not_one_defect G hm v
    intro x hxv
    by_cases hxu : x = u
    · subst x; exact hge3
    · exact huv_rest x hxu hxv
  have hv2 : G.degree v = 2 := by
    have hge := hm.1.2.1 v
    by_contra hne
    have hge3 : 3 ≤ G.degree v := by omega
    apply minimal_bad2_not_one_defect G hm u
    intro x hxu
    by_cases hxv : x = v
    · subst x; exact hge3
    · exact huv_rest x hxu hxv
  exact ⟨u, v, huv, hu2, hv2, huv_rest⟩

/-- Helper: degree formula in an induced subgraph `G.induce S`. -/
private theorem induce_degree_add_out {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Set V) [DecidablePred (· ∈ S)]
    (x : S) :
    (G.induce S).degree x +
      (Finset.univ.filter (fun y : V => y ∉ S ∧ G.Adj x.1 y)).card = G.degree x.1 := by
  classical
  have h1 : (G.induce S).degree x =
      (Finset.univ.filter (fun y : V => y ∈ S ∧ G.Adj x.1 y)).card := by
    let e : (G.induce S).neighborSet x ≃ {y : V // y ∈ S ∧ G.Adj x.1 y} :=
      { toFun := fun y => ⟨y.1.1, y.1.2, y.2⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_congr e, Fintype.card_subtype]
  rw [h1]
  have hdisj : Disjoint
      (Finset.univ.filter (fun y : V => y ∈ S ∧ G.Adj x.1 y))
      (Finset.univ.filter (fun y : V => y ∉ S ∧ G.Adj x.1 y)) := by
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    simp only [Finset.mem_filter] at hy1 hy2
    exact hy2.2.1 hy1.2.1
  rw [← Finset.card_union_of_disjoint hdisj]
  have hunion :
      (Finset.univ.filter (fun y : V => y ∈ S ∧ G.Adj x.1 y)) ∪
      (Finset.univ.filter (fun y : V => y ∉ S ∧ G.Adj x.1 y)) =
      G.neighborFinset x.1 := by
    ext y
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      SimpleGraph.mem_neighborFinset]
    tauto
  rw [hunion, SimpleGraph.card_neighborFinset_eq_degree]

/-- Helper: `Near2` holds on an induced proper subset `S` if every vertex in `S` has
degree ≥ 2, at most 2 vertices have degree < 3, and some vertex in `S` has degree ≥ 3. -/
private theorem not_minimal_bad2_of_proper_near2_induce {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad2 G)
    (S : Set V) [DecidablePred (· ∈ S)] (w0 : V) (hw0 : w0 ∉ S)
    (hge2 : ∀ x : S, 2 ≤ (G.induce S).degree x)
    (hdef : ∃ p q : S, ∀ x : S, x ≠ p → x ≠ q → 3 ≤ (G.induce S).degree x)
    (h3 : ∃ z : S, 3 ≤ (G.induce S).degree z) : False := by
  classical
  obtain ⟨z, hz⟩ := h3
  have hcard4 : 4 ≤ Fintype.card S := by
    have hlt := (G.induce S).degree_lt_card_verts z
    omega
  have hltV : Fintype.card S < Fintype.card V := by
    rw [Fintype.card_subtype]
    have hsub : Finset.univ.filter (fun x : V => x ∈ S) ⊂ Finset.univ := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.subset_univ _, ?_⟩
      intro heq
      have hmem : w0 ∈ Finset.univ.filter (fun x : V => x ∈ S) := by
        rw [heq]
        exact Finset.mem_univ w0
      simp only [Finset.mem_filter] at hmem
      exact hw0 hmem.2
    exact Finset.card_lt_card hsub
  have hnH : Near2 (G.induce S) := ⟨hcard4, hge2, hdef⟩
  exact hm.2.1 (power_induce G S (hm.2.2.1 S (G.induce S) hltV hnH))

/-- In every `MinimalBad2` graph, the two degree-2 defects `u` and `v` are nonadjacent. -/
theorem minimal_bad2_defects_nonadjacent {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad2 G)
    {u v : V} (huv : u ≠ v) (hu2 : G.degree u = 2) (hv2 : G.degree v = 2)
    (hrest : ∀ x, x ≠ u → x ≠ v → 3 ≤ G.degree x) :
    ¬G.Adj u v := by
  classical
  intro hadj
  have hub_ex : ∃ b, G.Adj u b ∧ b ≠ v := by
    have hcard : ((G.neighborFinset u).erase v).card = 1 := by
      have h1 := Finset.card_erase_add_one ((G.mem_neighborFinset u v).mpr hadj)
      rw [SimpleGraph.card_neighborFinset_eq_degree, hu2] at h1
      omega
    obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hcard
    have hmem : b ∈ (G.neighborFinset u).erase v := hb ▸ Finset.mem_singleton_self b
    rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hmem
    exact ⟨b, hmem.2, hmem.1⟩
  obtain ⟨b, hub, hbv⟩ := hub_ex
  have hbu : b ≠ u := (G.ne_of_adj hub).symm
  have hNu : ∀ x, G.Adj u x ↔ x = v ∨ x = b := by
    intro x
    have hsub : ({v, b} : Finset V) ⊆ G.neighborFinset u := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with h | h
      · rw [h]; exact (G.mem_neighborFinset u v).mpr hadj
      · rw [h]; exact (G.mem_neighborFinset u b).mpr hub
    have heq : ({v, b} : Finset V) = G.neighborFinset u := by
      apply Finset.eq_of_subset_of_card_le hsub
      rw [SimpleGraph.card_neighborFinset_eq_degree, hu2, Finset.card_pair (Ne.symm hbv)]
    rw [← SimpleGraph.mem_neighborFinset, ← heq]
    simp
  have hvc_ex : ∃ c, G.Adj v c ∧ c ≠ u := by
    have hcard : ((G.neighborFinset v).erase u).card = 1 := by
      have h1 := Finset.card_erase_add_one ((G.mem_neighborFinset v u).mpr hadj.symm)
      rw [SimpleGraph.card_neighborFinset_eq_degree, hv2] at h1
      omega
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcard
    have hmem : c ∈ (G.neighborFinset v).erase u := hc ▸ Finset.mem_singleton_self c
    rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hmem
    exact ⟨c, hmem.2, hmem.1⟩
  obtain ⟨c, hvc, hcu⟩ := hvc_ex
  have hcv : c ≠ v := (G.ne_of_adj hvc).symm
  have hNv : ∀ x, G.Adj v x ↔ x = u ∨ x = c := by
    intro x
    have hsub : ({u, c} : Finset V) ⊆ G.neighborFinset v := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with h | h
      · rw [h]; exact (G.mem_neighborFinset v u).mpr hadj.symm
      · rw [h]; exact (G.mem_neighborFinset v c).mpr hvc
    have heq : ({u, c} : Finset V) = G.neighborFinset v := by
      apply Finset.eq_of_subset_of_card_le hsub
      rw [SimpleGraph.card_neighborFinset_eq_degree, hv2, Finset.card_pair (Ne.symm hcu)]
    rw [← SimpleGraph.mem_neighborFinset, ← heq]
    simp
  by_cases hbc : b = c
  · subst hbc
    by_cases hb4 : 4 ≤ G.degree b
    · let S : Set V := {x | x ≠ u ∧ x ≠ v}
      have hout : ∀ x : S,
          (Finset.univ.filter (fun y : V => y ∉ S ∧ G.Adj x.1 y)).card ≤
          if x.1 = b then 2 else 0 := by
        intro x
        by_cases hxb : x.1 = b
        · rw [ite_eq_left hxb]
          have hsub : Finset.univ.filter (fun y : V => y ∉ S ∧ G.Adj x.1 y) ⊆ {u, v} := by
            intro y hy
            simp only [Finset.mem_filter, Set.mem_ofPred_eq, not_and_or, not_not, S] at hy
            simp only [Finset.mem_insert, Finset.mem_singleton]
            exact hy.2.1
          exact (Finset.card_le_card hsub).trans (by rw [Finset.card_pair huv])
        · rw [ite_eq_right hxb]
          rw [Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro y _ hy
          simp only [Set.mem_ofPred_eq, not_and_or, not_not, S] at hy
          rcases hy.1 with rfl | rfl
          · rcases (hNu x.1).mp hy.2.symm with h | h
            · exact x.2.2 h
            · exact hxb h
          · rcases (hNv x.1).mp hy.2.symm with h | h
            · exact x.2.1 h
            · exact hxb h
      have hge2 : ∀ x : S, 2 ≤ (G.induce S).degree x := by
        intro x
        have hd := induce_degree_add_out G S x
        have ho := hout x
        by_cases hxb : x.1 = b
        · rw [ite_eq_left hxb] at ho
          have hdeg : 4 ≤ G.degree x.1 := hxb.symm ▸ hb4
          omega
        · rw [ite_eq_right hxb] at ho
          have := hrest x.1 x.2.1 x.2.2
          omega
      have hdef : ∃ p q : S, ∀ x : S, x ≠ p → x ≠ q → 3 ≤ (G.induce S).degree x := by
        refine ⟨⟨b, hbu, hbv⟩, ⟨b, hbu, hbv⟩, ?_⟩
        intro x hxp _
        have hxb : x.1 ≠ b := fun h => hxp (Subtype.ext h)
        have hd := induce_degree_add_out G S x
        have ho := hout x
        rw [ite_eq_right hxb] at ho
        have := hrest x.1 x.2.1 x.2.2
        omega
      have h3 : ∃ z : S, 3 ≤ (G.induce S).degree z := by
        have hcard_b : ((G.neighborFinset b).filter (fun y => y ≠ u ∧ y ≠ v)).card ≥ 2 := by
          have hsub : G.neighborFinset b ⊆
              ((G.neighborFinset b).filter (fun y => y ≠ u ∧ y ≠ v)) ∪ {u, v} := by
            intro y hy
            by_cases hyu : y = u
            · simp [hyu]
            · by_cases hyv : y = v
              · simp [hyv]
              · simp [hy, hyu, hyv]
          have hc := Finset.card_le_card hsub
          have hle := Finset.card_union_le ((G.neighborFinset b).filter (fun y => y ≠ u ∧ y ≠ v)) {u, v}
          rw [SimpleGraph.card_neighborFinset_eq_degree] at hc
          rw [Finset.card_pair huv] at hle
          omega
        obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < ((G.neighborFinset b).filter (fun y => y ≠ u ∧ y ≠ v)).card)
        simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hz
        have hzb : z ≠ b := (G.ne_of_adj hz.1).symm
        let zs : S := ⟨z, hz.2.1, hz.2.2⟩
        refine ⟨zs, ?_⟩
        have hd := induce_degree_add_out G S zs
        have ho := hout zs
        have hzsb : zs.1 ≠ b := hzb
        rw [ite_eq_right hzsb] at ho
        have hz3 : 3 ≤ G.degree zs.1 := hrest z hz.2.1 hz.2.2
        omega
      exact not_minimal_bad2_of_proper_near2_induce G hm S u (by simp [S]) hge2 hdef h3
    · have hb3 : G.degree b = 3 := by have := hrest b hbu hbv; omega
      have hcard_z : (((G.neighborFinset b).erase u).erase v).card = 1 := by
        have h1 := Finset.card_erase_add_one ((G.mem_neighborFinset b u).mpr hub.symm)
        have hv_mem : v ∈ (G.neighborFinset b).erase u := by
          rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset]
          exact ⟨Ne.symm huv, hvc.symm⟩
        have h2 := Finset.card_erase_add_one hv_mem
        rw [SimpleGraph.card_neighborFinset_eq_degree, hb3] at h1
        omega
      obtain ⟨z, hz_eq⟩ := Finset.card_eq_one.mp hcard_z
      have hz_mem : z ∈ ((G.neighborFinset b).erase u).erase v :=
        hz_eq ▸ Finset.mem_singleton_self z
      simp only [Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hz_mem
      obtain ⟨hzv, hzu, hbz⟩ := hz_mem
      have hzb : z ≠ b := (G.ne_of_adj hbz).symm
      have hNb : ∀ y, G.Adj b y ↔ y = u ∨ y = v ∨ y = z := by
        intro y
        have hsub : ({u, v, z} : Finset V) ⊆ G.neighborFinset b := by
          intro t ht
          simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with h | h | h
          · rw [h]; exact (G.mem_neighborFinset b u).mpr hub.symm
          · rw [h]; exact (G.mem_neighborFinset b v).mpr hvc.symm
          · rw [h]; exact (G.mem_neighborFinset b z).mpr hbz
        have h3 : ({u, v, z} : Finset V).card = 3 := by
          simp [huv, Ne.symm hzu, Ne.symm hzv]
        have heq : ({u, v, z} : Finset V) = G.neighborFinset b := by
          apply Finset.eq_of_subset_of_card_le hsub
          rw [SimpleGraph.card_neighborFinset_eq_degree, hb3, h3]
        rw [← SimpleGraph.mem_neighborFinset, ← heq]
        simp
      let S : Set V := {x | x ≠ u ∧ x ≠ v ∧ x ≠ b}
      have hout : ∀ x : S,
          (Finset.univ.filter (fun y : V => y ∉ S ∧ G.Adj x.1 y)).card ≤
          if x.1 = z then 1 else 0 := by
        intro x
        by_cases hxz : x.1 = z
        · rw [ite_eq_left hxz]
          have hsub : Finset.univ.filter (fun y : V => y ∉ S ∧ G.Adj x.1 y) ⊆ {b} := by
            intro y hy
            simp only [Finset.mem_filter, Set.mem_ofPred_eq, not_and_or, not_not, S] at hy
            simp only [Finset.mem_singleton]
            rcases hy.2.1 with rfl | rfl | rfl
            · rcases (hNu x.1).mp hy.2.2.symm with h | h
              · exact absurd h x.2.2.1
              · exact absurd h x.2.2.2
            · rcases (hNv x.1).mp hy.2.2.symm with h | h
              · exact absurd h x.2.1
              · exact absurd h x.2.2.2
            · rfl
          exact (Finset.card_le_card hsub).trans (by simp)
        · rw [ite_eq_right hxz, Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro y _ hy
          simp only [Set.mem_ofPred_eq, not_and_or, not_not, S] at hy
          rcases hy.1 with rfl | rfl | rfl
          · rcases (hNu x.1).mp hy.2.symm with h | h
            · exact x.2.2.1 h
            · exact x.2.2.2 h
          · rcases (hNv x.1).mp hy.2.symm with h | h
            · exact x.2.1 h
            · exact x.2.2.2 h
          · rcases (hNb x.1).mp hy.2.symm with h | h | h
            · exact x.2.1 h
            · exact x.2.2.1 h
            · exact hxz h
      have hge2 : ∀ x : S, 2 ≤ (G.induce S).degree x := by
        intro x
        have hd := induce_degree_add_out G S x
        have ho := hout x
        have := hrest x.1 x.2.1 x.2.2.1
        split_ifs at ho <;> omega
      have hdef : ∃ p q : S, ∀ x : S, x ≠ p → x ≠ q → 3 ≤ (G.induce S).degree x := by
        refine ⟨⟨z, hzu, hzv, hzb⟩, ⟨z, hzu, hzv, hzb⟩, ?_⟩
        intro x hxp _
        have hxz : x.1 ≠ z := fun h => hxp (Subtype.ext h)
        have hd := induce_degree_add_out G S x
        have ho := hout x
        rw [ite_eq_right hxz] at ho
        have := hrest x.1 x.2.1 x.2.2.1
        omega
      have h3 : ∃ y : S, 3 ≤ (G.induce S).degree y := by
        have hdz : 2 ≤ (G.induce S).degree ⟨z, hzu, hzv, hzb⟩ := hge2 ⟨z, hzu, hzv, hzb⟩
        obtain ⟨y, hy⟩ := ((G.induce S).degree_pos_iff_exists_adj ⟨z, hzu, hzv, hzb⟩).mp (by omega)
        have hyz : y.1 ≠ z := fun h => ((G.induce S).ne_of_adj hy).symm (Subtype.ext h)
        refine ⟨y, ?_⟩
        have hd := induce_degree_add_out G S y
        have ho := hout y
        rw [ite_eq_right hyz] at ho
        have := hrest y.1 y.2.1 y.2.2.1
        omega
      exact not_minimal_bad2_of_proper_near2_induce G hm S u (by simp [S]) hge2 hdef h3
  · let S : Set V := {x | x ≠ u ∧ x ≠ v}
    have hout : ∀ x : S,
        (Finset.univ.filter (fun y : V => y ∉ S ∧ G.Adj x.1 y)).card ≤
        if x.1 = b ∨ x.1 = c then 1 else 0 := by
      intro x
      by_cases hxb : x.1 = b
      · rw [ite_eq_left (Or.inl hxb)]
        have hsub : Finset.univ.filter (fun y : V => y ∉ S ∧ G.Adj x.1 y) ⊆ {u} := by
          intro y hy
          simp only [Finset.mem_filter, Set.mem_ofPred_eq, not_and_or, not_not, S] at hy
          simp only [Finset.mem_singleton]
          rcases hy.2.1 with rfl | rfl
          · rfl
          · rcases (hNv x.1).mp hy.2.2.symm with h | h
            · exact absurd h x.2.1
            · exact absurd (hxb.symm.trans h) hbc
        exact (Finset.card_le_card hsub).trans (by simp)
      · by_cases hxc : x.1 = c
        · rw [ite_eq_left (Or.inr hxc)]
          have hsub : Finset.univ.filter (fun y : V => y ∉ S ∧ G.Adj x.1 y) ⊆ {v} := by
            intro y hy
            simp only [Finset.mem_filter, Set.mem_ofPred_eq, not_and_or, not_not, S] at hy
            simp only [Finset.mem_singleton]
            rcases hy.2.1 with rfl | rfl
            · rcases (hNu x.1).mp hy.2.2.symm with h | h
              · exact absurd h x.2.2
              · exact absurd (h.symm.trans hxc) hbc
            · rfl
          exact (Finset.card_le_card hsub).trans (by simp)
        · rw [ite_eq_right (by push Not; exact ⟨hxb, hxc⟩), Nat.le_zero,
            Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro y _ hy
          simp only [Set.mem_ofPred_eq, not_and_or, not_not, S] at hy
          rcases hy.1 with rfl | rfl
          · rcases (hNu x.1).mp hy.2.symm with h | h
            · exact x.2.2 h
            · exact hxb h
          · rcases (hNv x.1).mp hy.2.symm with h | h
            · exact x.2.1 h
            · exact hxc h
    have hge2 : ∀ x : S, 2 ≤ (G.induce S).degree x := by
      intro x
      have hd := induce_degree_add_out G S x
      have ho := hout x
      have := hrest x.1 x.2.1 x.2.2
      split_ifs at ho <;> omega
    have hdef : ∃ p q : S, ∀ x : S, x ≠ p → x ≠ q → 3 ≤ (G.induce S).degree x := by
      refine ⟨⟨b, hbu, hbv⟩, ⟨c, hcu, hcv⟩, ?_⟩
      intro x hxp hxq
      have hxb : x.1 ≠ b := fun h => hxp (Subtype.ext h)
      have hxc : x.1 ≠ c := fun h => hxq (Subtype.ext h)
      have hd := induce_degree_add_out G S x
      have ho := hout x
      rw [ite_eq_right (by push Not; exact ⟨hxb, hxc⟩)] at ho
      have := hrest x.1 x.2.1 x.2.2
      omega
    have h3 : ∃ z : S, 3 ≤ (G.induce S).degree z := by
      have hdb : 2 ≤ (G.induce S).degree ⟨b, hbu, hbv⟩ := hge2 ⟨b, hbu, hbv⟩
      have hcard_er : (((G.induce S).neighborFinset ⟨b, hbu, hbv⟩).erase ⟨c, hcu, hcv⟩).card ≥ 1 := by
        by_cases hmem : ⟨c, hcu, hcv⟩ ∈ (G.induce S).neighborFinset ⟨b, hbu, hbv⟩
        · have he := Finset.card_erase_add_one hmem
          rw [SimpleGraph.card_neighborFinset_eq_degree] at he
          omega
        · rw [Finset.erase_eq_of_notMem hmem, SimpleGraph.card_neighborFinset_eq_degree]
          omega
      obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < (((G.induce S).neighborFinset ⟨b, hbu, hbv⟩).erase ⟨c, hcu, hcv⟩).card)
      rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hz
      have hzc : z.1 ≠ c := fun h => hz.1 (Subtype.ext h)
      have hzb : z.1 ≠ b := fun h => ((G.induce S).ne_of_adj hz.2).symm (Subtype.ext h)
      refine ⟨z, ?_⟩
      have hd := induce_degree_add_out G S z
      have ho := hout z
      rw [ite_eq_right (by push Not; exact ⟨hzb, hzc⟩)] at ho
      have := hrest z.1 z.2.1 z.2.2
      omega
    exact not_minimal_bad2_of_proper_near2_induce G hm S u (by simp [S]) hge2 hdef h3

/-- Exact Whole-Problem Equivalence: `EG2 ↔ EGRob`. -/
theorem eg2_iff_eg_rob : EG2.{u} ↔ EGRob.{u} := by
  classical
  constructor
  · intro heg V G _ _ hmin a b hab
    have hnear := near2_of_min_deg_three G hmin
    have hall : ∀ v, 3 ≤ G.degree v := fun v => hmin.trans (G.minDegree_le_degree v)
    let H := G \ SimpleGraph.edge a b
    let _ : DecidableRel H.Adj := inferInstanceAs (DecidableRel (G \ SimpleGraph.edge a b).Adj)
    have hdegH : ∀ v, H.degree v + (if v = a ∨ v = b then 1 else 0) = G.degree v :=
      erase_edge_degree G a b hab
    have hnH : Near2 H := by
      refine ⟨hnear.1, ?_, ⟨a, b, ?_⟩⟩
      · intro v
        have hd := hdegH v
        have hv := hall v
        split_ifs at hd <;> omega
      · intro v hva hvb
        have hd := hdegH v
        simp only [hva, hvb, or_self, ↓reduceIte, add_zero] at hd
        rw [hd]
        exact hall v
    exact heg V H hnH
  · intro hrob
    by_contra hnot
    unfold EG2 at hnot
    push Not at hnot
    have hbad : ∃ (V : Type u) (_ : Fintype V) (G : SimpleGraph V)
        (_ : DecidableRel G.Adj), Near2 G ∧ ¬HasPower G := by
      obtain ⟨V, G, fV, dG, hn, hp⟩ := hnot
      exact ⟨V, fV, G, dG, hn, hp⟩
    obtain ⟨V, fV, G, dG, hm⟩ := minimal_bad2_exists hbad
    let _ : Fintype V := fV
    let _ : DecidableRel G.Adj := dG
    obtain ⟨u, v, huv, hu2, hv2, hrest⟩ := minimal_bad2_exact_two_defects G hm
    have hnotadj : ¬G.Adj u v := minimal_bad2_defects_nonadjacent G hm huv hu2 hv2 hrest
    let G' : SimpleGraph V := G ⊔ SimpleGraph.edge u v
    let _ : DecidableRel G'.Adj := inferInstanceAs (DecidableRel (G ⊔ SimpleGraph.edge u v).Adj)
    have hdu : G'.degree u = G.degree u + 1 := degree_add_new_edge_left G u v huv hnotadj
    have hdv : G'.degree v = G.degree v + 1 := degree_add_new_edge_right G u v huv hnotadj
    have hall' : ∀ x, 3 ≤ G'.degree x := by
      intro x
      by_cases hxu : x = u
      · subst x; omega
      · by_cases hxv : x = v
        · subst x; omega
        · exact (hrest x hxu hxv).trans (G.degree_le_of_le (v := x) (H := G') le_sup_left)
    have hnonempty : Nonempty V := Fintype.card_pos_iff.mp (by have := hm.1.1; omega)
    have hmin' : G'.minDegree ≥ 3 := by
      obtain ⟨x, hx⟩ := G'.exists_minimal_degree_vertex
      rw [← hx]
      exact hall' x
    have hadj' : G'.Adj u v := Or.inr ((SimpleGraph.edge_adj u v u v).mpr ⟨Or.inl ⟨rfl, rfl⟩, huv⟩)
    have hpow' : HasPower (G' \ SimpleGraph.edge u v) := hrob V G' hmin' u v hadj'
    have hEq : G' \ SimpleGraph.edge u v = G := by
      ext x y
      simp only [SimpleGraph.sdiff_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj, G']
      constructor
      · rintro ⟨h | h, hne⟩
        · exact h
        · exact absurd h hne
      · intro h
        refine ⟨Or.inl h, ?_⟩
        rintro ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, _⟩
        · exact hnotadj h
        · exact hnotadj h.symm
    rw [hEq] at hpow'
    exact hm.2.1 hpow'

/-- `EGRob` unconditionally implies full Erdős #64 and closes all 26 leaves. -/
theorem eg_rob_implies_erdos64 : EGRob.{u} → Erdos64Original.{u} :=
  fun h => eg2_implies_erdos64 (eg2_iff_eg_rob.mpr h)

theorem eg_rob_closes_all_leaves : EGRob.{u} → ∀ l : Leaf, Exclude.{u} l :=
  fun h => eg2_closes_all_leaves (eg2_iff_eg_rob.mpr h)

/-- Every neighbor of either degree-2 defect in `MinimalBad2` has degree exactly 3. -/
theorem minimal_bad2_defect_neighbors_cubic {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad2 G)
    {u v : V} (huv : u ≠ v) (hu2 : G.degree u = 2) (hv2 : G.degree v = 2)
    (hrest : ∀ x, x ≠ u → x ≠ v → 3 ≤ G.degree x)
    {a : V} (hua : G.Adj u a) :
    G.degree a = 3 := by
  classical
  have hnotadj : ¬G.Adj u v := minimal_bad2_defects_nonadjacent G hm huv hu2 hv2 hrest
  have hau : a ≠ u := (G.ne_of_adj hua).symm
  have hav : a ≠ v := fun h => hnotadj (h ▸ hua)
  have ha3 : 3 ≤ G.degree a := hrest a hau hav
  by_contra hne
  have ha4 : 4 ≤ G.degree a := by omega
  have hcard : ((G.neighborFinset u).erase a).card = 1 := by
    have h1 := Finset.card_erase_add_one ((G.mem_neighborFinset u a).mpr hua)
    rw [SimpleGraph.card_neighborFinset_eq_degree, hu2] at h1
    omega
  obtain ⟨b, hb_eq⟩ := Finset.card_eq_one.mp hcard
  have hb_mem : b ∈ (G.neighborFinset u).erase a := hb_eq ▸ Finset.mem_singleton_self b
  rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hb_mem
  obtain ⟨hba, hub⟩ := hb_mem
  have hbu : b ≠ u := (G.ne_of_adj hub).symm
  have hNu : ∀ x, G.Adj u x ↔ x = a ∨ x = b := by
    intro x
    have hsub : ({a, b} : Finset V) ⊆ G.neighborFinset u := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with h | h
      · rw [h]; exact (G.mem_neighborFinset u a).mpr hua
      · rw [h]; exact (G.mem_neighborFinset u b).mpr hub
    have heq : ({a, b} : Finset V) = G.neighborFinset u := by
      apply Finset.eq_of_subset_of_card_le hsub
      rw [SimpleGraph.card_neighborFinset_eq_degree, hu2, Finset.card_pair (Ne.symm hba)]
    rw [← SimpleGraph.mem_neighborFinset, ← heq]
    simp
  let S : Set V := {x | x ≠ u}
  have hge2 : ∀ x : S, 2 ≤ (G.induce S).degree x := by
    intro x
    have hd := induce_delete_degree G u x
    change (G.induce S).degree x + (if G.Adj x.1 u then 1 else 0) = G.degree x.1 at hd
    by_cases hxv : x.1 = v
    · have hno : ¬G.Adj x.1 u := fun h => hnotadj (hxv ▸ h.symm)
      rw [ite_eq_right hno, add_zero, hxv, hv2] at hd
      omega
    · have := hrest x.1 x.2 hxv
      split_ifs at hd <;> omega
  have hdef : ∃ p q : S, ∀ x : S, x ≠ p → x ≠ q → 3 ≤ (G.induce S).degree x := by
    refine ⟨⟨v, Ne.symm huv⟩, ⟨b, hbu⟩, ?_⟩
    intro x hxv hxb
    have hd := induce_delete_degree G u x
    change (G.induce S).degree x + (if G.Adj x.1 u then 1 else 0) = G.degree x.1 at hd
    by_cases hxa : x.1 = a
    · rw [hxa] at hd
      split_ifs at hd <;> omega
    · have hno : ¬G.Adj x.1 u := by
        intro he
        rcases (hNu x.1).mp he.symm with h | h
        · exact hxa h
        · exact hxb (Subtype.ext h)
      rw [ite_eq_right hno, add_zero] at hd
      rw [hd]
      exact hrest x.1 x.2 (fun h => hxv (Subtype.ext h))
  have h3 : ∃ z : S, 3 ≤ (G.induce S).degree z := by
    refine ⟨⟨a, hau⟩, ?_⟩
    have hd := induce_delete_degree G u ⟨a, hau⟩
    change (G.induce S).degree ⟨a, hau⟩ + (if G.Adj a u then 1 else 0) = G.degree a at hd
    split_ifs at hd <;> omega
  exact not_minimal_bad2_of_proper_near2_induce G hm S u (by simp [S]) hge2 hdef h3

/-- In `MinimalBad2`, vertices of degree ≥ 4 form an independent set. -/
theorem minimal_bad2_high_independent {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad2 G)
    {x y : V} (hx : 4 ≤ G.degree x) (hy : 4 ≤ G.degree y) :
    ¬G.Adj x y := by
  classical
  intro hxy
  obtain ⟨u, v, _, _, _, hrest⟩ := minimal_bad2_exact_two_defects G hm
  let H := G \ SimpleGraph.edge x y
  let _ : DecidableRel H.Adj := inferInstanceAs (DecidableRel (G \ SimpleGraph.edge x y).Adj)
  have hdegH : ∀ z, H.degree z + (if z = x ∨ z = y then 1 else 0) = G.degree z :=
    erase_edge_degree G x y hxy
  have hnH : Near2 H := by
    refine ⟨hm.1.1, ?_, ⟨u, v, ?_⟩⟩
    · intro z
      have hd := hdegH z
      by_cases hzx : z = x
      · subst z; simp at hd; omega
      · by_cases hzy : z = y
        · subst z; simp at hd; omega
        · simp [hzx, hzy] at hd; rw [hd]; exact hm.1.2.1 z
    · intro z hzu hzv
      have hd := hdegH z
      by_cases hzx : z = x
      · subst z; simp at hd; omega
      · by_cases hzy : z = y
        · subst z; simp at hd; omega
        · simp [hzx, hzy] at hd; rw [hd]; exact hrest z hzu hzv
  exact sdiff_edge_ne G hxy (hm.2.2.2 H sdiff_le hnH)

/-- Every `MinimalBad2` graph is nonbipartite. -/
theorem minimal_bad2_nonbipartite {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad2 G) :
    ¬Bip G := by
  classical
  intro hB
  obtain ⟨color, hproper⟩ := hB
  obtain ⟨u, v, huv, hu2, hv2, hrest⟩ := minimal_bad2_exact_two_defects G hm
  have hnotadj : ¬G.Adj u v := minimal_bad2_defects_nonadjacent G hm huv hu2 hv2 hrest
  have hncard : (G.neighborFinset u).card = 2 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, hu2]
  obtain ⟨a, b, hab, hN⟩ := Finset.card_eq_two.mp hncard
  have hNbr (x : V) : G.Adj u x ↔ x = a ∨ x = b := by
    rw [← SimpleGraph.mem_neighborFinset, hN]
    simp
  have hua : G.Adj u a := (hNbr a).mpr (Or.inl rfl)
  have hub : G.Adj u b := (hNbr b).mpr (Or.inr rfl)
  have hau : a ≠ u := (G.ne_of_adj hua).symm
  have hbu : b ≠ u := (G.ne_of_adj hub).symm
  have hav : a ≠ v := fun h => hnotadj (h ▸ hua)
  have hbv : b ≠ v := fun h => hnotadj (h ▸ hub)
  have hcol : color a = color b := by
    have h1 := hproper u a hua
    have h2 := hproper u b hub
    cases huc : color u <;> cases hac : color a <;>
      cases hbc : color b <;> simp_all
  let W := {x : V // x ≠ u}
  let K : SimpleGraph W := G.induce {x | x ≠ u}
  let A : W := ⟨a, hau⟩
  let B : W := ⟨b, hbu⟩
  let V0 : W := ⟨v, Ne.symm huv⟩
  have hAB : A ≠ B := fun h => hab (congrArg Subtype.val h)
  let _ : DecidableRel K.Adj := inferInstanceAs (DecidableRel (G.induce {x | x ≠ u}).Adj)
  let H : SimpleGraph W := K ⊔ SimpleGraph.edge A B
  let _ : DecidableRel H.Adj := inferInstanceAs (DecidableRel (K ⊔ SimpleGraph.edge A B).Adj)
  have hKnot : ¬K.Adj A B := fun h => hproper a b h hcol
  let c : W → Fin 2 := fun x => if color x.val = true then 1 else 0
  have hc (x y : W) (h : K.Adj x y) : c x ≠ c y := by
    have hp := hproper x.val y.val h
    cases hx : color x.val <;> cases hy : color y.val <;> simp_all [c]
  have hCAB : c A = c B := by
    change (if color a = true then (1 : Fin 2) else 0) =
      (if color b = true then (1 : Fin 2) else 0)
    rw [hcol]
  have hKfree : PowerFree K := by
    intro k x p hk hp hl
    exact hm.2.1 (power_induce G {x | x ≠ u} ⟨k, x, p, hk, hp, hl⟩)
  have hHfree : PowerFree H := same_color_edge_safe c hc A B hAB hCAB hKfree
  have hda : H.degree A = K.degree A + 1 := degree_add_new_edge_left K A B hAB hKnot
  have hdb : H.degree B = K.degree B + 1 := degree_add_new_edge_right K A B hAB hKnot
  have hrestH : ∀ x : W, x ≠ V0 → 3 ≤ H.degree x := by
    intro x hxV
    by_cases hxA : x = A
    · subst x
      have hd := induce_delete_degree G u A
      change K.degree A + (if G.Adj a u then 1 else 0) = G.degree a at hd
      rw [ite_eq_left hua.symm] at hd
      have hr := hrest a hau hav
      omega
    · by_cases hxB : x = B
      · subst x
        have hd := induce_delete_degree G u B
        change K.degree B + (if G.Adj b u then 1 else 0) = G.degree b at hd
        rw [ite_eq_left hub.symm] at hd
        have hr := hrest b hbu hbv
        omega
      · have hnot : ¬G.Adj x.val u := by
          intro he
          rcases (hNbr x.val).mp he.symm with h | h
          · exact hxA (Subtype.ext h)
          · exact hxB (Subtype.ext h)
        have hd := induce_delete_degree G u x
        change K.degree x + (if G.Adj x.val u then 1 else 0) = G.degree x.val at hd
        rw [ite_eq_right hnot, add_zero] at hd
        have hr : 3 ≤ K.degree x := by
          rw [hd]
          exact hrest x.val x.property (fun h => hxV (Subtype.ext h))
        exact hr.trans (K.degree_le_of_le (v := x) (H := H) le_sup_left)
  have hge2H : ∀ x : W, 2 ≤ H.degree x := by
    intro x
    by_cases hxV : x = V0
    · subst x
      have hd := induce_delete_degree G u V0
      change K.degree V0 + (if G.Adj v u then 1 else 0) = G.degree v at hd
      have hno : ¬G.Adj v u := fun h => hnotadj h.symm
      rw [ite_eq_right hno, add_zero, hv2] at hd
      have hle : K.degree V0 ≤ H.degree V0 := K.degree_le_of_le (v := V0) (H := H) le_sup_left
      omega
    · have := hrestH x hxV; omega
  have hcardW : 4 ≤ Fintype.card W := by
    have hA3 : 3 ≤ H.degree A := hrestH A (fun h => hav (congrArg Subtype.val h))
    have hlt := H.degree_lt_card_verts A
    omega
  have hWlt : Fintype.card W < Fintype.card V := by
    have h1 : Fintype.card W + 1 = Fintype.card V := by
      rw [Fintype.card_subtype,
        show (Finset.univ.filter (fun x : V => x ≠ u)) = Finset.univ.erase u by ext x; simp]
      exact Finset.card_erase_add_one (Finset.mem_univ u)
    omega
  have hnH : Near2 H := ⟨hcardW, hge2H, ⟨V0, V0, fun x h _ => hrestH x h⟩⟩
  obtain ⟨k, x, p, hk, hp, hl⟩ := hm.2.2.1 W H hWlt hnH
  exact hHfree k x p hk hp hl

/-- No defect-free 2-edge cut exists in `MinimalBad2`: every cut side `S` of size ≥ 2
avoiding both defects `u` and `v` has at least 3 outgoing edges. -/
theorem minimal_bad2_no_defect_free_two_cut {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad2 G)
    {u v : V} (hrest : ∀ x, x ≠ u → x ≠ v → 3 ≤ G.degree x)
    (S : Set V) (hS2 : 2 ≤ Nat.card S) (hu : u ∉ S) (hv : v ∉ S) :
    3 ≤ Nat.card {e : V × V // e.1 ∈ S ∧ e.2 ∉ S ∧ G.Adj e.1 e.2} := by
  classical
  by_contra hlt
  have hle2 : Nat.card {e : V × V // e.1 ∈ S ∧ e.2 ∉ S ∧ G.Adj e.1 e.2} ≤ 2 := by omega
  let outDeg : S → ℕ := fun x => (Finset.univ.filter (fun y : V => y ∉ S ∧ G.Adj x.1 y)).card
  have hsum : (∑ x : S, outDeg x) =
      Nat.card {e : V × V // e.1 ∈ S ∧ e.2 ∉ S ∧ G.Adj e.1 e.2} := by
    rw [Nat.card_eq_fintype_card]
    let e : {e : V × V // e.1 ∈ S ∧ e.2 ∉ S ∧ G.Adj e.1 e.2} ≃
        Σ x : S, {y : V // y ∉ S ∧ G.Adj x.1 y} :=
      { toFun := fun p => ⟨⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩⟩
        invFun := fun p => ⟨(p.1.1, p.2.1), p.1.2, p.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr e, Fintype.card_sigma]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Fintype.card_subtype]
  have hsum_le : (∑ x : S, outDeg x) ≤ 2 := by omega
  have hS3 : ∀ x : S, 3 ≤ G.degree x.1 := fun x =>
    hrest x.1 (fun h => hu (h ▸ x.2)) (fun h => hv (h ▸ x.2))
  have hScard2 : 2 ≤ Fintype.card S := by rwa [Nat.card_eq_fintype_card] at hS2
  by_cases hall1 : ∀ x : S, outDeg x ≤ 1
  · have hge2 : ∀ x : S, 2 ≤ (G.induce S).degree x := by
      intro x
      have hd := induce_degree_add_out G S x
      have ho := hall1 x
      have h3 := hS3 x
      change (G.induce S).degree x + outDeg x = G.degree x.1 at hd
      omega
    let B : Finset S := Finset.univ.filter (fun x : S => 1 ≤ outDeg x)
    have hBle2 : B.card ≤ 2 := by
      have h1 : B.card ≤ ∑ x ∈ B, outDeg x := by
        calc B.card = ∑ _x ∈ B, 1 := by simp
          _ ≤ ∑ x ∈ B, outDeg x := Finset.sum_le_sum (fun x hx => (Finset.mem_filter.mp hx).2)
      have h2 : ∑ x ∈ B, outDeg x ≤ ∑ x : S, outDeg x :=
        Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
      omega
    have hScard3 : 3 ≤ Fintype.card S := by
      by_contra hlt3
      have h2 : Fintype.card S = 2 := by omega
      obtain ⟨p⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card S)
      have hdeg_le : (G.induce S).degree p ≤ 1 := by
        have hlt := (G.induce S).degree_lt_card_verts p
        omega
      have hd := induce_degree_add_out G S p
      change (G.induce S).degree p + outDeg p = G.degree p.1 at hd
      have ho := hall1 p
      have h3 := hS3 p
      omega
    have h3 : ∃ z : S, 3 ≤ (G.induce S).degree z := by
      have hltB : B.card < (Finset.univ : Finset S).card := by
        rw [Finset.card_univ]; omega
      have hne : (Finset.univ \ B).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hemp
        have hsub : (Finset.univ : Finset S) ⊆ B := Finset.sdiff_eq_empty_iff_subset.mp hemp
        have := Finset.card_le_card hsub
        omega
      obtain ⟨z, hz⟩ := hne
      rw [Finset.mem_sdiff] at hz
      have hz0 : outDeg z = 0 := by
        have := hz.2
        simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at this
        omega
      refine ⟨z, ?_⟩
      have hd := induce_degree_add_out G S z
      change (G.induce S).degree z + outDeg z = G.degree z.1 at hd
      have h3z := hS3 z
      omega
    have hdef : ∃ p q : S, ∀ x : S, x ≠ p → x ≠ q → 3 ≤ (G.induce S).degree x := by
      obtain ⟨z0⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card S)
      have hBcases : B.card = 0 ∨ B.card = 1 ∨ B.card = 2 := by omega
      rcases hBcases with h0 | h1 | h2
      · refine ⟨z0, z0, fun x _ _ => ?_⟩
        have hxB : x ∉ B := by rw [Finset.card_eq_zero.mp h0]; simp
        simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hxB
        have hd := induce_degree_add_out G S x
        change (G.induce S).degree x + outDeg x = G.degree x.1 at hd
        have := hS3 x; omega
      · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h1
        refine ⟨p, p, fun x hxp _ => ?_⟩
        have hxB : x ∉ B := by rw [hp]; simp [hxp]
        simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hxB
        have hd := induce_degree_add_out G S x
        change (G.induce S).degree x + outDeg x = G.degree x.1 at hd
        have := hS3 x; omega
      · obtain ⟨p, q, _, hpq⟩ := Finset.card_eq_two.mp h2
        refine ⟨p, q, fun x hxp hxq => ?_⟩
        have hxB : x ∉ B := by rw [hpq]; simp [hxp, hxq]
        simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hxB
        have hd := induce_degree_add_out G S x
        change (G.induce S).degree x + outDeg x = G.degree x.1 at hd
        have := hS3 x; omega
    exact not_minimal_bad2_of_proper_near2_induce G hm S u hu hge2 hdef h3
  · push Not at hall1
    obtain ⟨a, ha2⟩ := hall1
    have ha_eq : outDeg a = 2 := by
      have hle : outDeg a ≤ ∑ x : S, outDeg x :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
      omega
    have hother0 : ∀ x : S, x ≠ a → outDeg x = 0 := by
      intro x hxa
      have hpair : outDeg a + outDeg x ≤ ∑ y : S, outDeg y := by
        have hsub : ({a, x} : Finset S) ⊆ Finset.univ := Finset.subset_univ _
        have hs : ∑ y ∈ ({a, x} : Finset S), outDeg y ≤ ∑ y ∈ (Finset.univ : Finset S), outDeg y :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
        rw [Finset.sum_pair (Ne.symm hxa)] at hs
        exact hs
      omega
    by_cases ha4 : 4 ≤ G.degree a.1
    · have hge2 : ∀ x : S, 2 ≤ (G.induce S).degree x := by
        intro x
        have hd := induce_degree_add_out G S x
        change (G.induce S).degree x + outDeg x = G.degree x.1 at hd
        by_cases hxa : x = a
        · subst x; omega
        · have h0 := hother0 x hxa; have := hS3 x; omega
      have hdef : ∃ p q : S, ∀ x : S, x ≠ p → x ≠ q → 3 ≤ (G.induce S).degree x := by
        refine ⟨a, a, fun x hxa _ => ?_⟩
        have hd := induce_degree_add_out G S x
        change (G.induce S).degree x + outDeg x = G.degree x.1 at hd
        have h0 := hother0 x hxa; have := hS3 x; omega
      have h3 : ∃ z : S, 3 ≤ (G.induce S).degree z := by
        have hne : (Finset.univ.erase a).Nonempty := by
          rw [← Finset.card_pos]
          have := Finset.card_erase_add_one (Finset.mem_univ a)
          rw [Finset.card_univ] at this
          omega
        obtain ⟨z, hz⟩ := hne
        have hza : z ≠ a := (Finset.mem_erase.mp hz).1
        refine ⟨z, ?_⟩
        have hd := induce_degree_add_out G S z
        change (G.induce S).degree z + outDeg z = G.degree z.1 at hd
        have h0 := hother0 z hza; have := hS3 z; omega
      exact not_minimal_bad2_of_proper_near2_induce G hm S u hu hge2 hdef h3
    · have ha3 : G.degree a.1 = 3 := by have := hS3 a; omega
      have hda1 : (G.induce S).degree a = 1 := by
        have hd := induce_degree_add_out G S a
        change (G.induce S).degree a + outDeg a = G.degree a.1 at hd
        omega
      obtain ⟨z, hz_eq⟩ := Finset.card_eq_one.mp
        (by rw [SimpleGraph.card_neighborFinset_eq_degree, hda1] : ((G.induce S).neighborFinset a).card = 1)
      have hza_adj : (G.induce S).Adj a z :=
        (SimpleGraph.mem_neighborFinset _ _ _).mp (hz_eq ▸ Finset.mem_singleton_self z)
      have hza : z ≠ a := ((G.induce S).ne_of_adj hza_adj).symm
      have hNa : ∀ x : S, (G.induce S).Adj a x → x = z := by
        intro x hax
        have hmem : x ∈ (G.induce S).neighborFinset a := (SimpleGraph.mem_neighborFinset _ _ _).mpr hax
        rw [hz_eq, Finset.mem_singleton] at hmem
        exact hmem
      let T : Set V := {x | x ∈ S ∧ x ≠ a.1}
      have hT3 : ∀ x : T, 3 ≤ G.degree x.1 := fun x => hS3 ⟨x.1, x.2.1⟩
      have houtT : ∀ x : T,
          (Finset.univ.filter (fun y : V => y ∉ T ∧ G.Adj x.1 y)).card ≤
          if x.1 = z.1 then 1 else 0 := by
        intro x
        have hxS : (⟨x.1, x.2.1⟩ : S) ≠ a := fun h => x.2.2 (congrArg Subtype.val h)
        have hx0 : outDeg ⟨x.1, x.2.1⟩ = 0 := hother0 ⟨x.1, x.2.1⟩ hxS
        have hnoOut : ∀ y, y ∉ S → ¬G.Adj x.1 y := by
          intro y hyS hadj
          have hpos : 0 < outDeg ⟨x.1, x.2.1⟩ := by
            rw [Finset.card_pos]
            exact ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ y, hyS, hadj⟩⟩
          omega
        by_cases hxz : x.1 = z.1
        · rw [ite_eq_left hxz]
          have hsub : Finset.univ.filter (fun y : V => y ∉ T ∧ G.Adj x.1 y) ⊆ {a.1} := by
            intro y hy
            simp only [Finset.mem_filter, Set.mem_ofPred_eq, not_and_or, not_not, T] at hy
            simp only [Finset.mem_singleton]
            rcases hy.2.1 with hyS | rfl
            · exact absurd hy.2.2 (hnoOut y hyS)
            · rfl
          exact (Finset.card_le_card hsub).trans (by simp)
        · rw [ite_eq_right hxz, Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro y _ hy
          simp only [Set.mem_ofPred_eq, not_and_or, not_not, T] at hy
          rcases hy.1 with hyS | rfl
          · exact hnoOut y hyS hy.2
          · have hax : (G.induce S).Adj a ⟨x.1, x.2.1⟩ := hy.2.symm
            have hEq := hNa ⟨x.1, x.2.1⟩ hax
            exact hxz (congrArg Subtype.val hEq)
      have hge2 : ∀ x : T, 2 ≤ (G.induce T).degree x := by
        intro x
        have hd := induce_degree_add_out G T x
        have ho := houtT x
        have h3x := hT3 x
        split_ifs at ho <;> omega
      have hzT : z.1 ∈ T := ⟨z.2, fun h => hza (Subtype.ext h)⟩
      have hdef : ∃ p q : T, ∀ x : T, x ≠ p → x ≠ q → 3 ≤ (G.induce T).degree x := by
        refine ⟨⟨z.1, hzT⟩, ⟨z.1, hzT⟩, fun x hxz _ => ?_⟩
        have hxz' : x.1 ≠ z.1 := fun h => hxz (Subtype.ext h)
        have hd := induce_degree_add_out G T x
        have ho := houtT x
        rw [ite_eq_right hxz'] at ho
        have h3x := hT3 x
        omega
      have h3 : ∃ y : T, 3 ≤ (G.induce T).degree y := by
        have hdz : 2 ≤ (G.induce T).degree ⟨z.1, hzT⟩ := hge2 ⟨z.1, hzT⟩
        obtain ⟨y, hy⟩ := ((G.induce T).degree_pos_iff_exists_adj ⟨z.1, hzT⟩).mp (by omega)
        have hyz : y.1 ≠ z.1 := fun h => ((G.induce T).ne_of_adj hy).symm (Subtype.ext h)
        refine ⟨y, ?_⟩
        have hd := induce_degree_add_out G T y
        have ho := houtT y
        rw [ite_eq_right hyz] at ho
        have h3y := hT3 y
        omega
      have huT : u ∉ T := fun h => hu h.1
      exact not_minimal_bad2_of_proper_near2_induce G hm T u huT hge2 hdef h3

#print axioms near2_of_min_deg_three
#print axioms eg2_implies_erdos64
#print axioms near2_of_minimal_bad
#print axioms eg2_closes_all_leaves
#print axioms minimal_bad2_exists
#print axioms minimal_bad2_not_all_ge_three
#print axioms minimal_bad2_not_one_defect
#print axioms minimal_bad2_exact_two_defects
#print axioms minimal_bad2_defects_nonadjacent
#print axioms eg2_iff_eg_rob
#print axioms eg_rob_implies_erdos64
#print axioms eg_rob_closes_all_leaves
#print axioms minimal_bad2_defect_neighbors_cubic
#print axioms minimal_bad2_high_independent
#print axioms minimal_bad2_nonbipartite
#print axioms minimal_bad2_no_defect_free_two_cut

end E64Wave4Agent5EG2
