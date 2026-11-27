import Mathlib

set_option autoImplicit false

open SimpleGraph Finset

namespace E64Wave6Agent1

open Classical

/-- Convenience iff for membership in neighborFinset. -/
lemma mem_nb {V : Type*} [Fintype V] {G : SimpleGraph V} {u v : V} :
    v ∈ G.neighborFinset u ↔ G.Adj u v :=
  SimpleGraph.mem_neighborFinset G u v

/-- A cycle length is a power of two at least 4 (2^k with k >= 2). -/
def IsPowerOfTwo (m : ℕ) : Prop :=
  ∃ k : ℕ, 2 ≤ k ∧ m = 2 ^ k

/-- G contains a simple cycle of length 2^k (k >= 2). -/
def HasPowerCycle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ IsPowerOfTwo p.length

/-- G is power-free: no simple cycle of length 2^k (k >= 2). -/
def PowerFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬ HasPowerCycle G

/-- Minimum degree at least d. -/
def MinDegGe {V : Type*} [Fintype V] (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∀ v : V, d ≤ G.degree v

/-- The set of degree-2 vertices (defects). -/
noncomputable def Defects {V : Type*} [Fintype V] (G : SimpleGraph V) : Finset V :=
  Finset.univ.filter (fun v => G.degree v = 2)

/-- Cubic vertices (degree 3). -/
noncomputable def V3 {V : Type*} [Fintype V] (G : SimpleGraph V) : Finset V :=
  Finset.univ.filter (fun v => G.degree v = 3)

/-- High-degree vertices (degree >= 4). -/
noncomputable def VGe4 {V : Type*} [Fintype V] (G : SimpleGraph V) : Finset V :=
  Finset.univ.filter (fun v => 4 ≤ G.degree v)

/-- Two-defect counterexample predicate (EG2). -/
def Bad2 {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  PowerFree G ∧ MinDegGe G 2 ∧ (Defects G).card ≤ 2

/-- Vertex-minimal (then edge-minimal) counterexample to EG2 (EG2-CORE). -/
def MinimalBad2 {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  Bad2 G ∧
  (∀ (m : ℕ) (H : SimpleGraph (Fin m)), Bad2 H → Fintype.card V ≤ m) ∧
  (∀ (H : SimpleGraph V), Bad2 H → G.edgeFinset.card ≤ H.edgeFinset.card)

/-- Transporting a graph along an isomorphism preserves Bad2. -/
lemma bad2_of_iso {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (hG : Bad2 G) : Bad2 H := by
  rcases hG with ⟨hpf, hmin, hdef⟩
  refine ⟨?_, ?_, ?_⟩
  · intro ⟨w, p, hcyc, hpow⟩
    apply hpf
    refine ⟨e.symm w, p.map e.symm.toHom, ?_, ?_⟩
    · exact hcyc.map e.symm.injective
    · simpa using hpow
  · intro w
    have hdeg : H.degree w = G.degree (e.symm w) := (e.symm.degree_eq w).symm
    rw [hdeg]
    exact hmin (e.symm w)
  · have hcard : (Defects H).card = (Defects G).card := by
      apply Finset.card_bij (fun w _ => e.symm w)
      · intro w hw
        simp only [Defects, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
        rw [← e.symm.degree_eq w]
        exact hw
      · intro _ _ _ _ h
        exact e.symm.injective h
      · intro v hv
        refine ⟨e v, ?_, e.symm_apply_apply v⟩
        simp only [Defects, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
        rw [← e.degree_eq v]
        exact hv
    rw [hcard]
    exact hdef

/-- No strictly smaller graph can satisfy Bad2 if G is MinimalBad2. -/
theorem minimal_bad2_no_smaller {V : Type} [Fintype V] {G : SimpleGraph V}
    (hG : MinimalBad2 G) {W : Type*} [Fintype W] (H : SimpleGraph W)
    (hH : Bad2 H) (hlt : Fintype.card W < Fintype.card V) : False := by
  let e : W ≃ Fin (Fintype.card W) := Fintype.equivFin W
  let H' : SimpleGraph (Fin (Fintype.card W)) :=
    { Adj := fun i j => H.Adj (e.symm i) (e.symm j)
      symm := fun _ _ h => H.symm h
      loopless := fun _ h => H.loopless _ h }
  let iso : H ≃g H' :=
    { toEquiv := e
      map_rel_iff' := by
        intro a b
        simp [H'] }
  have hH' : Bad2 H' := bad2_of_iso iso hH
  have hle : Fintype.card V ≤ Fintype.card W := hG.2.1 (Fintype.card W) H' hH'
  omega

/-- Induced subgraph of a power-free graph is power-free. -/
lemma powerFree_induce {V : Type*} {G : SimpleGraph V} (s : Set V) (hG : PowerFree G) :
    PowerFree (G.induce s) := by
  intro ⟨v, p, hcyc, hpow⟩
  apply hG
  refine ⟨v.1, p.map (SimpleGraph.Embedding.induce s).toHom, ?_, ?_⟩
  · exact hcyc.map Subtype.val_injective
  · simpa using hpow

/-- Helper: degree in induced subgraph equals number of neighbors inside S. -/
lemma degree_induce_eq {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Finset V)
    (u : {x : V // x ∈ (S : Set V)}) :
    (G.induce (S : Set V)).degree u = ((G.neighborFinset u.1) ∩ S).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun v _ => v.1)
  · intro v hv
    simp only [mem_nb, Finset.mem_inter] at hv ⊢
    exact ⟨hv, v.2⟩
  · intro _ _ _ _ h
    exact Subtype.ext h
  · intro w hw
    simp only [Finset.mem_inter, mem_nb] at hw
    exact ⟨⟨w, hw.2⟩, by simpa [mem_nb] using hw.1, rfl⟩

/-- PILLAR 1.1: Universal Safe-Deletion Principle on EG2-CORE. -/
theorem minimal_bad2_no_safe_deletion {V : Type} [Fintype V] {G : SimpleGraph V}
    (hG : MinimalBad2 G) (K : Finset V) (hKne : K.Nonempty)
    (hmin : ∀ u ∈ Kᶜ, 2 ≤ ((G.neighborFinset u) ∩ Kᶜ).card)
    (hdef : ((Kᶜ).filter (fun u => ((G.neighborFinset u) ∩ Kᶜ).card = 2)).card ≤ 2) :
    False := by
  let S : Finset V := Kᶜ
  let H : SimpleGraph {x : V // x ∈ (S : Set V)} := G.induce (S : Set V)
  have hH_pf : PowerFree H := powerFree_induce (S : Set V) hG.1.1
  have hH_min : MinDegGe H 2 := by
    intro u
    rw [degree_induce_eq]
    exact hmin u.1 u.2
  have hH_def : (Defects H).card ≤ 2 := by
    have hcard : (Defects H).card =
        (S.filter (fun u => ((G.neighborFinset u) ∩ S).card = 2)).card := by
      apply Finset.card_bij (fun u _ => u.1)
      · intro u hu
        simp only [Defects, Finset.mem_filter, Finset.mem_univ, true_and] at hu
        rw [degree_induce_eq] at hu
        exact Finset.mem_filter.mpr ⟨u.2, hu⟩
      · intro _ _ _ _ h
        exact Subtype.ext h
      · intro w hw
        rcases Finset.mem_filter.mp hw with ⟨hwS, hwdeg⟩
        refine ⟨⟨w, hwS⟩, ?_, rfl⟩
        simp only [Defects, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [degree_induce_eq]
        exact hwdeg
    rw [hcard]
    exact hdef
  have hlt : Fintype.card {x : V // x ∈ (S : Set V)} < Fintype.card V := by
    rw [Fintype.card_coe]
    have hsum : K.card + S.card = Fintype.card V := by
      simpa [S] using Finset.card_add_card_compl K
    have hKpos : 0 < K.card := Finset.card_pos.mpr hKne
    omega
  exact minimal_bad2_no_smaller hG H ⟨hH_pf, hH_min, hH_def⟩ hlt

/-- Helper: deleting a subset K drops degree of u by |(N(u) ∩ K)|. -/
lemma degree_compl_eq_sub {V : Type*} [Fintype V] (G : SimpleGraph V) (K : Finset V) (u : V) :
    ((G.neighborFinset u) ∩ Kᶜ).card + ((G.neighborFinset u) ∩ K).card = G.degree u := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hdisj : Disjoint ((G.neighborFinset u) ∩ Kᶜ) ((G.neighborFinset u) ∩ K) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact (Finset.mem_compl.mp (Finset.mem_inter.mp hx1).2) (Finset.mem_inter.mp hx2).2
  rw [← Finset.card_union_of_disjoint hdisj]
  congr 1
  ext x
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_compl]
  tauto

/-- PILLAR 1.2: Safe-deletion corollary for subsets K disjoint from Defects G. -/
theorem minimal_bad2_no_safe_deletion_disjoint_defects {V : Type} [Fintype V] {G : SimpleGraph V}
    (hG : MinimalBad2 G) (K : Finset V) (hKne : K.Nonempty)
    (hno_adj_def : ∀ d ∈ Defects G, ∀ k ∈ K, ¬ G.Adj d k)
    (hkeep : ∀ u ∈ Kᶜ, u ∉ Defects G → 3 ≤ ((G.neighborFinset u) ∩ Kᶜ).card) :
    False := by
  apply minimal_bad2_no_safe_deletion hG K hKne
  · intro u hu
    by_cases hud : u ∈ Defects G
    · have hzero : ((G.neighborFinset u) ∩ K).card = 0 := by
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro k hk
        rcases Finset.mem_inter.mp hk with ⟨hkN, hkK⟩
        exact hno_adj_def u hud k hkK (mem_nb.mp hkN)
      have hsum := degree_compl_eq_sub G K u
      have hdeg2 : G.degree u = 2 := (Finset.mem_filter.mp hud).2
      omega
    · have := hkeep u hu hud
      omega
  · have hsub : (Kᶜ.filter (fun u => ((G.neighborFinset u) ∩ Kᶜ).card = 2)) ⊆ Defects G := by
      intro u hu
      rcases Finset.mem_filter.mp hu with ⟨huKc, hu2⟩
      by_contra hud
      have := hkeep u huKc hud
      omega
    exact le_trans (Finset.card_le_card hsub) hG.1.2.2

/-- PILLAR 1.3: Every MinimalBad2 graph is C4-free. -/
theorem minimal_bad2_c4_free {V : Type} [Fintype V] {G : SimpleGraph V}
    (hG : MinimalBad2 G) {v : V} (p : G.Walk v v) (hcyc : p.IsCycle) :
    p.length ≠ 4 := by
  intro hlen
  exact hG.1.1 ⟨v, p, hcyc, ⟨2, le_rfl, by simpa using hlen⟩⟩

/-- In a C4-free graph, any two distinct vertices have at most 1 common neighbor. -/
theorem minimal_bad2_common_neighbors_le_one {V : Type} [Fintype V] {G : SimpleGraph V}
    (hG : MinimalBad2 G) {x y : V} (hxy : x ≠ y) :
    ((G.neighborFinset x) ∩ (G.neighborFinset y)).card ≤ 1 := by
  by_contra hgt
  push Not at hgt
  rcases Finset.one_lt_card.mp hgt with ⟨u, hu, v, hv, huv⟩
  rcases Finset.mem_inter.mp hu with ⟨hux, huy⟩
  rcases Finset.mem_inter.mp hv with ⟨hvx, hvy⟩
  rw [mem_nb] at hux huy hvx hvy
  have hux_ne : u ≠ x := G.ne_of_adj hux.symm
  have huy_ne : u ≠ y := G.ne_of_adj huy.symm
  have hvx_ne : v ≠ x := G.ne_of_adj hvx.symm
  have hvy_ne : v ≠ y := G.ne_of_adj hvy.symm
  let p : G.Walk x x :=
    Walk.cons hux (Walk.cons huy.symm (Walk.cons hvy (Walk.cons hvx.symm Walk.nil)))
  have hcyc : p.IsCycle := by
    rw [Walk.isCycle_def]
    refine ⟨?_, by simp [p], ?_⟩
    · rw [Walk.isTrail_def]
      simp only [p, Walk.edges_cons, Walk.edges_nil, List.nodup_cons, List.mem_cons,
        List.not_mem_nil, or_false, not_or, Sym2.eq_iff, List.nodup_nil, and_true]
      tauto
    · simp only [p, Walk.support_cons, Walk.support_nil, List.tail_cons, List.nodup_cons,
        List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
      tauto
  exact minimal_bad2_c4_free hG p hcyc rfl

/-- PILLAR 1.4: Common defect neighbor has ZERO high-degree neighbors. -/
theorem minimal_bad2_common_defect_neighbor_no_high_neighbor {V : Type} [Fintype V]
    {G : SimpleGraph V} (hG : MinimalBad2 G) {a b c a2 b2 c' : V}
    (hab : a ≠ b) (ha : a ∈ Defects G) (hb : b ∈ Defects G)
    (hNa : G.neighborFinset a = {c, a2}) (hNb : G.neighborFinset b = {c, b2})
    (hNc : G.neighborFinset c = {a, b, c'})
    (ha2_ne : a2 ∉ ({a, b, c} : Finset V))
    (hc'_ne : c' ∉ ({a, b, c} : Finset V))
    (hdisj_abc' : c' ≠ a2 ∧ c' ≠ b2) :
    G.degree c' = 3 := by
  have hdef_eq : Defects G = {a, b} := by
    have hsub : ({a, b} : Finset V) ⊆ Defects G := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hcard : ({a, b} : Finset V).card = 2 := Finset.card_pair hab
    exact (Finset.eq_of_subset_of_card_le hsub (by have := hG.1.2.2; omega)).symm
  have hc'_ge3 : 3 ≤ G.degree c' := by
    have hnotdef : c' ∉ Defects G := by
      rw [hdef_eq]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc'_ne ⊢
      exact ⟨hc'_ne.1, hc'_ne.2.1⟩
    have h2 := hG.1.2.1 c'
    have hne2 : G.degree c' ≠ 2 := fun h => hnotdef (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    omega
  by_contra hne3
  have hc'_ge4 : 4 ≤ G.degree c' := by omega
  let K : Finset V := {a, b, c}
  apply minimal_bad2_no_safe_deletion hG K ⟨a, by simp [K]⟩
  · intro u hu
    have hu_notK : u ∉ K := Finset.mem_compl.mp hu
    have hu_notdef : u ∉ Defects G := by
      rw [hdef_eq]
      intro hmem; apply hu_notK
      simp only [K, Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
      rcases hmem with rfl | rfl <;> simp
    have hu_ge3 : 3 ≤ G.degree u := by
      have h2 := hG.1.2.1 u
      have hne2 : G.degree u ≠ 2 := fun h => hu_notdef (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      omega
    have ha2_ne_b2 : a2 ≠ b2 := by
      intro heq; subst heq
      have hc_in : c ∈ (G.neighborFinset a) ∩ (G.neighborFinset b) := by rw [hNa, hNb]; simp
      have ha2_in : a2 ∈ (G.neighborFinset a) ∩ (G.neighborFinset b) := by rw [hNa, hNb]; simp
      have hne : c ≠ a2 := fun h => ha2_ne (by simp [h])
      have h2 : 2 ≤ ((G.neighborFinset a) ∩ (G.neighborFinset b)).card := by
        have := Finset.card_le_card (show ({c, a2} : Finset V) ⊆ _ by
          intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> assumption)
        rw [Finset.card_pair hne] at this; exact this
      have h1 := minimal_bad2_common_neighbors_le_one hG hab
      omega
    have hNK_le1 : ((G.neighborFinset u) ∩ K).card ≤ 1 := by
      have hsub : (G.neighborFinset u) ∩ K ⊆
          (if u = a2 then {a} else ∅) ∪ (if u = b2 then {b} else ∅) ∪ (if u = c' then {c} else ∅) := by
        intro k hk
        rcases Finset.mem_inter.mp hk with ⟨hkN, hkK⟩
        have hadj : G.Adj k u := (mem_nb.mp hkN).symm
        simp only [K, Finset.mem_insert, Finset.mem_singleton] at hkK
        rcases hkK with hka | hkb | hkc
        · rw [hka] at hadj ⊢
          have huNa : u ∈ G.neighborFinset a := mem_nb.mpr hadj
          rw [hNa] at huNa; simp only [Finset.mem_insert, Finset.mem_singleton] at huNa
          rcases huNa with rfl | rfl
          · exact False.elim (hu_notK (by simp [K]))
          · simp
        · rw [hkb] at hadj ⊢
          have huNb : u ∈ G.neighborFinset b := mem_nb.mpr hadj
          rw [hNb] at huNb; simp only [Finset.mem_insert, Finset.mem_singleton] at huNb
          rcases huNb with rfl | rfl
          · exact False.elim (hu_notK (by simp [K]))
          · simp
        · rw [hkc] at hadj ⊢
          have huNc : u ∈ G.neighborFinset c := mem_nb.mpr hadj
          rw [hNc] at huNc; simp only [Finset.mem_insert, Finset.mem_singleton] at huNc
          rcases huNc with rfl | rfl | rfl
          · exact False.elim (hu_notK (by simp [K]))
          · exact False.elim (hu_notK (by simp [K]))
          · simp
      by_cases h1 : u = a2
      · subst h1; simp only [↓reduceIte, ha2_ne_b2, hdisj_abc'.1.symm, Finset.union_empty] at hsub
        exact le_trans (Finset.card_le_card hsub) (by simp)
      · by_cases h2 : u = b2
        · subst h2; simp only [h1, ↓reduceIte, hdisj_abc'.2.symm, Finset.empty_union,
            Finset.union_empty] at hsub
          exact le_trans (Finset.card_le_card hsub) (by simp)
        · by_cases h3 : u = c'
          · subst h3; simp only [h1, h2, ↓reduceIte, Finset.empty_union] at hsub
            exact le_trans (Finset.card_le_card hsub) (by simp)
          · simp only [h1, h2, h3, ↓reduceIte, Finset.empty_union] at hsub
            exact le_trans (Finset.card_le_card hsub) (by simp)
    have hsum := degree_compl_eq_sub G K u
    omega
  · have hsub : (Kᶜ.filter (fun u => ((G.neighborFinset u) ∩ Kᶜ).card = 2)) ⊆ {a2, b2} := by
      intro u hu
      rcases Finset.mem_filter.mp hu with ⟨huKc, hu2⟩
      have hu_notK : u ∉ K := Finset.mem_compl.mp huKc
      have hu_notdef : u ∉ Defects G := by
        rw [hdef_eq]; intro hmem; apply hu_notK
        simp only [K, Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
        rcases hmem with rfl | rfl <;> simp
      have hu_ge3 : 3 ≤ G.degree u := by
        have h2 := hG.1.2.1 u
        have hne2 : G.degree u ≠ 2 := fun h => hu_notdef (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        omega
      have hsum := degree_compl_eq_sub G K u
      have hNK_pos : 0 < ((G.neighborFinset u) ∩ K).card := by omega
      rcases Finset.card_pos.mp hNK_pos with ⟨k, hk⟩
      rcases Finset.mem_inter.mp hk with ⟨hkN, hkK⟩
      have hadj : G.Adj k u := (mem_nb.mp hkN).symm
      simp only [K, Finset.mem_insert, Finset.mem_singleton] at hkK
      rcases hkK with hka | hkb | hkc
      · rw [hka] at hadj
        have huNa : u ∈ G.neighborFinset a := mem_nb.mpr hadj
        rw [hNa] at huNa; simp only [Finset.mem_insert, Finset.mem_singleton] at huNa
        rcases huNa with rfl | rfl
        · exact False.elim (hu_notK (by simp [K]))
        · simp
      · rw [hkb] at hadj
        have huNb : u ∈ G.neighborFinset b := mem_nb.mpr hadj
        rw [hNb] at huNb; simp only [Finset.mem_insert, Finset.mem_singleton] at huNb
        rcases huNb with rfl | rfl
        · exact False.elim (hu_notK (by simp [K]))
        · simp
      · rw [hkc] at hadj
        have huNc : u ∈ G.neighborFinset c := mem_nb.mpr hadj
        rw [hNc] at huNc; simp only [Finset.mem_insert, Finset.mem_singleton] at huNc
        rcases huNc with rfl | rfl | rfl
        · exact False.elim (hu_notK (by simp [K]))
        · exact False.elim (hu_notK (by simp [K]))
        · have hNK_le1 : ((G.neighborFinset c') ∩ K).card ≤ 1 := by
            have hsubc : (G.neighborFinset c') ∩ K ⊆ {c} := by
              intro z hz
              rcases Finset.mem_inter.mp hz with ⟨hzN, hzK⟩
              have hadjz : G.Adj z c' := (mem_nb.mp hzN).symm
              simp only [K, Finset.mem_insert, Finset.mem_singleton] at hzK
              rcases hzK with hza | hzb | hzc
              · rw [hza] at hadjz
                have hc'Na : c' ∈ G.neighborFinset a := mem_nb.mpr hadjz
                rw [hNa] at hc'Na; simp only [Finset.mem_insert, Finset.mem_singleton] at hc'Na
                rcases hc'Na with h1 | h2
                · exact False.elim (hc'_ne (by simp [h1]))
                · exact False.elim (hdisj_abc'.1 h2)
              · rw [hzb] at hadjz
                have hc'Nb : c' ∈ G.neighborFinset b := mem_nb.mpr hadjz
                rw [hNb] at hc'Nb; simp only [Finset.mem_insert, Finset.mem_singleton] at hc'Nb
                rcases hc'Nb with h1 | h2
                · exact False.elim (hc'_ne (by simp [h1]))
                · exact False.elim (hdisj_abc'.2 h2)
              · simp [hzc]
            exact le_trans (Finset.card_le_card hsubc) (by simp)
          omega
    exact le_trans (Finset.card_le_card hsub) Finset.card_le_two

/-- PILLAR 1.5: Defect-triangle high-neighbor exclusion. -/
theorem minimal_bad2_defect_triangle_no_high_neighbor {V : Type} [Fintype V]
    {G : SimpleGraph V} (hG : MinimalBad2 G) {a b a1 a2 x1 x2 : V}
    (hab : a ≠ b) (ha : a ∈ Defects G) (hb : b ∈ Defects G)
    (hNa : G.neighborFinset a = {a1, a2})
    (hNa1 : G.neighborFinset a1 = {a, a2, x1})
    (hNa2 : G.neighborFinset a2 = {a, a1, x2})
    (hx1_notK : x1 ∉ ({a, a1, a2} : Finset V))
    (hb_notK : b ∉ ({a, a1, a2} : Finset V))
    (hx1_neb : x1 ≠ b) (hx2_neb : x2 ≠ b) :
    G.degree x1 ≤ 3 ∧ G.degree x2 ≤ 3 := by
  have hdef_eq : Defects G = {a, b} := by
    have hsub : ({a, b} : Finset V) ⊆ Defects G := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hab]; exact hG.1.2.2)).symm
  have hx12 : x1 ≠ x2 := by
    intro heq; subst heq
    have ha12 : a1 ≠ a2 := by
      intro h; subst h
      have hcard : (G.neighborFinset a).card = 2 := by
        rw [SimpleGraph.card_neighborFinset_eq_degree]
        exact (Finset.mem_filter.mp ha).2
      rw [hNa, Finset.pair_eq_singleton, Finset.card_singleton] at hcard; omega
    have ha_in : a ∈ (G.neighborFinset a1) ∩ (G.neighborFinset a2) := by rw [hNa1, hNa2]; simp
    have hx1_in : x1 ∈ (G.neighborFinset a1) ∩ (G.neighborFinset a2) := by rw [hNa1, hNa2]; simp
    have hne : a ≠ x1 := fun h => hx1_notK (by simp [h])
    have h2 : 2 ≤ ((G.neighborFinset a1) ∩ (G.neighborFinset a2)).card := by
      have := Finset.card_le_card (show ({a, x1} : Finset V) ⊆ _ by
        intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> assumption)
      rw [Finset.card_pair hne] at this; exact this
    have h1 := minimal_bad2_common_neighbors_le_one hG ha12
    omega
  let K : Finset V := {a, a1, a2}
  have hNK_le1 : ∀ u ∈ Kᶜ, ((G.neighborFinset u) ∩ K).card ≤ 1 := by
    intro u hu
    have hu_notK : u ∉ K := Finset.mem_compl.mp hu
    have hsub : (G.neighborFinset u) ∩ K ⊆
        (if u = x1 then {a1} else ∅) ∪ (if u = x2 then {a2} else ∅) := by
      intro k hk
      rcases Finset.mem_inter.mp hk with ⟨hkN, hkK⟩
      have hadj : G.Adj k u := (mem_nb.mp hkN).symm
      simp only [K, Finset.mem_insert, Finset.mem_singleton] at hkK
      rcases hkK with hka | hka1 | hka2
      · rw [hka] at hadj
        have huNa : u ∈ G.neighborFinset a := mem_nb.mpr hadj
        rw [hNa] at huNa; simp only [Finset.mem_insert, Finset.mem_singleton] at huNa
        rcases huNa with rfl | rfl <;> exact False.elim (hu_notK (by simp [K]))
      · rw [hka1] at hadj ⊢
        have huNa1 : u ∈ G.neighborFinset a1 := mem_nb.mpr hadj
        rw [hNa1] at huNa1; simp only [Finset.mem_insert, Finset.mem_singleton] at huNa1
        rcases huNa1 with rfl | rfl | rfl
        · exact False.elim (hu_notK (by simp [K]))
        · exact False.elim (hu_notK (by simp [K]))
        · simp
      · rw [hka2] at hadj ⊢
        have huNa2 : u ∈ G.neighborFinset a2 := mem_nb.mpr hadj
        rw [hNa2] at huNa2; simp only [Finset.mem_insert, Finset.mem_singleton] at huNa2
        rcases huNa2 with rfl | rfl | rfl
        · exact False.elim (hu_notK (by simp [K]))
        · exact False.elim (hu_notK (by simp [K]))
        · simp
    by_cases h1 : u = x1
    · subst h1; simp only [↓reduceIte, hx12, Finset.union_empty] at hsub
      exact le_trans (Finset.card_le_card hsub) (by simp)
    · by_cases h2 : u = x2
      · subst h2; simp only [h1, ↓reduceIte, Finset.empty_union] at hsub
        exact le_trans (Finset.card_le_card hsub) (by simp)
      · simp only [h1, h2, ↓reduceIte, Finset.empty_union] at hsub
        exact le_trans (Finset.card_le_card hsub) (by simp)
  have hNK_b : ((G.neighborFinset b) ∩ K).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro k hk
    rcases Finset.mem_inter.mp hk with ⟨hkN, hkK⟩
    have hadj : G.Adj k b := (mem_nb.mp hkN).symm
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at hkK
    rcases hkK with hka | hka1 | hka2
    · rw [hka] at hadj
      have hbNa : b ∈ G.neighborFinset a := mem_nb.mpr hadj
      rw [hNa] at hbNa; simp only [Finset.mem_insert, Finset.mem_singleton] at hbNa
      rcases hbNa with h1 | h2 <;> exact hb_notK (by simp [h1] <|> simp [h2])
    · rw [hka1] at hadj
      have hbNa1 : b ∈ G.neighborFinset a1 := mem_nb.mpr hadj
      rw [hNa1] at hbNa1; simp only [Finset.mem_insert, Finset.mem_singleton] at hbNa1
      rcases hbNa1 with h1 | h2 | h3
      · exact hb_notK (by simp [h1])
      · exact hb_notK (by simp [h2])
      · exact hx1_neb h3.symm
    · rw [hka2] at hadj
      have hbNa2 : b ∈ G.neighborFinset a2 := mem_nb.mpr hadj
      rw [hNa2] at hbNa2; simp only [Finset.mem_insert, Finset.mem_singleton] at hbNa2
      rcases hbNa2 with h1 | h2 | h3
      · exact hb_notK (by simp [h1])
      · exact hb_notK (by simp [h2])
      · exact hx2_neb h3.symm
  have hmin_Kc : ∀ u ∈ Kᶜ, 2 ≤ ((G.neighborFinset u) ∩ Kᶜ).card := by
    intro u hu
    have hsum := degree_compl_eq_sub G K u
    by_cases hub : u = b
    · rw [hub] at hsum ⊢; have hbdeg : G.degree b = 2 := (Finset.mem_filter.mp hb).2; omega
    · have hu_notdef : u ∉ Defects G := by
        rw [hdef_eq]; simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => (Finset.mem_compl.mp hu) (by simp [K, h]), hub⟩
      have hu_ge3 : 3 ≤ G.degree u := by
        have h2 := hG.1.2.1 u
        have hne2 : G.degree u ≠ 2 := fun h => hu_notdef (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        omega
      have h1 := hNK_le1 u hu
      omega
  constructor
  · by_contra hx1_gt; push Not at hx1_gt
    apply minimal_bad2_no_safe_deletion hG K ⟨a, by simp [K]⟩ hmin_Kc
    have hsub : (Kᶜ.filter (fun u => ((G.neighborFinset u) ∩ Kᶜ).card = 2)) ⊆ {b, x2} := by
      intro u hu
      rcases Finset.mem_filter.mp hu with ⟨huKc, hu2⟩
      by_cases hub : u = b
      · simp [hub]
      · have hu_notdef : u ∉ Defects G := by
          rw [hdef_eq]; simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨fun h => (Finset.mem_compl.mp huKc) (by simp [K, h]), hub⟩
        have hu_ge3 : 3 ≤ G.degree u := by
          have h2 := hG.1.2.1 u
          have hne2 : G.degree u ≠ 2 := fun h => hu_notdef (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
          omega
        have hsum := degree_compl_eq_sub G K u
        have hpos : 0 < ((G.neighborFinset u) ∩ K).card := by omega
        rcases Finset.card_pos.mp hpos with ⟨k, hk⟩
        rcases Finset.mem_inter.mp hk with ⟨hkN, hkK⟩
        have hadj : G.Adj k u := (mem_nb.mp hkN).symm
        simp only [K, Finset.mem_insert, Finset.mem_singleton] at hkK
        rcases hkK with hka | hka1 | hka2
        · rw [hka] at hadj
          have huNa : u ∈ G.neighborFinset a := mem_nb.mpr hadj
          rw [hNa] at huNa; simp only [Finset.mem_insert, Finset.mem_singleton] at huNa
          rcases huNa with rfl | rfl <;> exact False.elim ((Finset.mem_compl.mp huKc) (by simp [K]))
        · rw [hka1] at hadj
          have huNa1 : u ∈ G.neighborFinset a1 := mem_nb.mpr hadj
          rw [hNa1] at huNa1; simp only [Finset.mem_insert, Finset.mem_singleton] at huNa1
          rcases huNa1 with rfl | rfl | rfl
          · exact False.elim ((Finset.mem_compl.mp huKc) (by simp [K]))
          · exact False.elim ((Finset.mem_compl.mp huKc) (by simp [K]))
          · have h1 := hNK_le1 x1 huKc; omega
        · rw [hka2] at hadj
          have huNa2 : u ∈ G.neighborFinset a2 := mem_nb.mpr hadj
          rw [hNa2] at huNa2; simp only [Finset.mem_insert, Finset.mem_singleton] at huNa2
          rcases huNa2 with rfl | rfl | rfl
          · exact False.elim ((Finset.mem_compl.mp huKc) (by simp [K]))
          · exact False.elim ((Finset.mem_compl.mp huKc) (by simp [K]))
          · simp
    exact le_trans (Finset.card_le_card hsub) Finset.card_le_two
  · by_contra hx2_gt; push Not at hx2_gt
    apply minimal_bad2_no_safe_deletion hG K ⟨a, by simp [K]⟩ hmin_Kc
    have hsub : (Kᶜ.filter (fun u => ((G.neighborFinset u) ∩ Kᶜ).card = 2)) ⊆ {b, x1} := by
      intro u hu
      rcases Finset.mem_filter.mp hu with ⟨huKc, hu2⟩
      by_cases hub : u = b
      · simp [hub]
      · have hu_notdef : u ∉ Defects G := by
          rw [hdef_eq]; simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨fun h => (Finset.mem_compl.mp huKc) (by simp [K, h]), hub⟩
        have hu_ge3 : 3 ≤ G.degree u := by
          have h2 := hG.1.2.1 u
          have hne2 : G.degree u ≠ 2 := fun h => hu_notdef (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
          omega
        have hsum := degree_compl_eq_sub G K u
        have hpos : 0 < ((G.neighborFinset u) ∩ K).card := by omega
        rcases Finset.card_pos.mp hpos with ⟨k, hk⟩
        rcases Finset.mem_inter.mp hk with ⟨hkN, hkK⟩
        have hadj : G.Adj k u := (mem_nb.mp hkN).symm
        simp only [K, Finset.mem_insert, Finset.mem_singleton] at hkK
        rcases hkK with hka | hka1 | hka2
        · rw [hka] at hadj
          have huNa : u ∈ G.neighborFinset a := mem_nb.mpr hadj
          rw [hNa] at huNa; simp only [Finset.mem_insert, Finset.mem_singleton] at huNa
          rcases huNa with rfl | rfl <;> exact False.elim ((Finset.mem_compl.mp huKc) (by simp [K]))
        · rw [hka1] at hadj
          have huNa1 : u ∈ G.neighborFinset a1 := mem_nb.mpr hadj
          rw [hNa1] at huNa1; simp only [Finset.mem_insert, Finset.mem_singleton] at huNa1
          rcases huNa1 with rfl | rfl | rfl
          · exact False.elim ((Finset.mem_compl.mp huKc) (by simp [K]))
          · exact False.elim ((Finset.mem_compl.mp huKc) (by simp [K]))
          · simp
        · rw [hka2] at hadj
          have huNa2 : u ∈ G.neighborFinset a2 := mem_nb.mpr hadj
          rw [hNa2] at huNa2; simp only [Finset.mem_insert, Finset.mem_singleton] at huNa2
          rcases huNa2 with rfl | rfl | rfl
          · exact False.elim ((Finset.mem_compl.mp huKc) (by simp [K]))
          · exact False.elim ((Finset.mem_compl.mp huKc) (by simp [K]))
          · have h1 := hNK_le1 x2 huKc; omega
    exact le_trans (Finset.card_le_card hsub) Finset.card_le_two

/-- PILLAR 1.6: Adjacent S2 vertices must share a common high neighbor of EXACT degree 4. -/
theorem minimal_bad2_s2_adjacent_common_high_deg4 {V : Type} [Fintype V]
    {G : SimpleGraph V} (hG : MinimalBad2 G) {v w : V}
    (hvw : G.Adj v w) (hv3 : v ∈ V3 G) (hw3 : w ∈ V3 G)
    (hv2 : ((G.neighborFinset v) ∩ VGe4 G).card = 2)
    (hw2 : ((G.neighborFinset w) ∩ VGe4 G).card = 2) :
    ∃ h ∈ (G.neighborFinset v) ∩ (G.neighborFinset w), h ∈ VGe4 G ∧ G.degree h = 4 := by
  by_contra hnone
  push Not at hnone
  let K : Finset V := {v, w}
  have hv_nd : v ∉ Defects G := fun hd => by
    have := (Finset.mem_filter.mp hv3).2; have := (Finset.mem_filter.mp hd).2; omega
  have hw_nd : w ∉ Defects G := fun hd => by
    have := (Finset.mem_filter.mp hw3).2; have := (Finset.mem_filter.mp hd).2; omega
  have hv_other_ge4 : ∀ u, G.Adj v u → u ≠ w → u ∈ VGe4 G := by
    intro u hvu huw
    have hw_not_ge4 : w ∉ VGe4 G := fun hw4 => by
      have := (Finset.mem_filter.mp hw3).2; have := (Finset.mem_filter.mp hw4).2; omega
    have hsub : ((G.neighborFinset v) ∩ VGe4 G) ⊆ (G.neighborFinset v).erase w := by
      intro z hz; rcases Finset.mem_inter.mp hz with ⟨hzN, hz4⟩
      exact Finset.mem_erase.mpr ⟨fun h => hw_not_ge4 (h ▸ hz4), hzN⟩
    have hcard_er : ((G.neighborFinset v).erase w).card = 2 := by
      rw [Finset.card_erase_of_mem (mem_nb.mpr hvw),
          SimpleGraph.card_neighborFinset_eq_degree, (Finset.mem_filter.mp hv3).2]
    have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
    have hu_in : u ∈ (G.neighborFinset v).erase w :=
      Finset.mem_erase.mpr ⟨huw, mem_nb.mpr hvu⟩
    rw [← heq] at hu_in; exact (Finset.mem_inter.mp hu_in).2
  have hw_other_ge4 : ∀ u, G.Adj w u → u ≠ v → u ∈ VGe4 G := by
    intro u hwu huv
    have hv_not_ge4 : v ∉ VGe4 G := fun hv4 => by
      have := (Finset.mem_filter.mp hv3).2; have := (Finset.mem_filter.mp hv4).2; omega
    have hsub : ((G.neighborFinset w) ∩ VGe4 G) ⊆ (G.neighborFinset w).erase v := by
      intro z hz; rcases Finset.mem_inter.mp hz with ⟨hzN, hz4⟩
      exact Finset.mem_erase.mpr ⟨fun h => hv_not_ge4 (h ▸ hz4), hzN⟩
    have hcard_er : ((G.neighborFinset w).erase v).card = 2 := by
      rw [Finset.card_erase_of_mem (mem_nb.mpr hvw.symm),
          SimpleGraph.card_neighborFinset_eq_degree, (Finset.mem_filter.mp hw3).2]
    have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
    have hu_in : u ∈ (G.neighborFinset w).erase v :=
      Finset.mem_erase.mpr ⟨huv, mem_nb.mpr hwu⟩
    rw [← heq] at hu_in; exact (Finset.mem_inter.mp hu_in).2
  apply minimal_bad2_no_safe_deletion_disjoint_defects hG K ⟨v, by simp [K]⟩
  · intro d hd k hk hadj
    have hd_not_ge4 : d ∉ VGe4 G := fun hd4 => by
      have := (Finset.mem_filter.mp hd).2; have := (Finset.mem_filter.mp hd4).2; omega
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with hkv | hkw
    · rw [hkv] at hadj
      exact hd_not_ge4 (hv_other_ge4 d hadj.symm (fun h => hw_nd (h ▸ hd)))
    · rw [hkw] at hadj
      exact hd_not_ge4 (hw_other_ge4 d hadj.symm (fun h => hv_nd (h ▸ hd)))
  · intro u huKc hud
    have hu_notK : u ∉ K := Finset.mem_compl.mp huKc
    have huv : u ≠ v := fun h => hu_notK (by simp [K, h])
    have huw : u ≠ w := fun h => hu_notK (by simp [K, h])
    have hsum := degree_compl_eq_sub G K u
    have hu_ge3 : 3 ≤ G.degree u := by
      have h2 := hG.1.2.1 u
      have hne2 : G.degree u ≠ 2 := fun h => hud (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      omega
    by_cases h1 : G.Adj v u
    · have hu4 : u ∈ VGe4 G := hv_other_ge4 u h1 huw
      have hdeg4 : 4 ≤ G.degree u := (Finset.mem_filter.mp hu4).2
      by_cases h2 : G.Adj w u
      · have hcomm : u ∈ (G.neighborFinset v) ∩ (G.neighborFinset w) :=
          Finset.mem_inter.mpr ⟨mem_nb.mpr h1, mem_nb.mpr h2⟩
        have hne4 : G.degree u ≠ 4 := hnone u hcomm hu4
        have hle2 : ((G.neighborFinset u) ∩ K).card ≤ 2 :=
          le_trans (Finset.card_le_card Finset.inter_subset_right) Finset.card_le_two
        omega
      · have hsub1 : (G.neighborFinset u) ∩ K ⊆ {v} := by
          intro z hz; rcases Finset.mem_inter.mp hz with ⟨hzN, hzK⟩
          simp only [K, Finset.mem_insert, Finset.mem_singleton] at hzK
          rcases hzK with hzv | hzw
          · simp [hzv]
          · rw [hzw] at hzN; exact False.elim (h2 (mem_nb.mp hzN).symm)
        have hle1 : ((G.neighborFinset u) ∩ K).card ≤ 1 :=
          le_trans (Finset.card_le_card hsub1) (by simp)
        omega
    · by_cases h2 : G.Adj w u
      · have hu4 : u ∈ VGe4 G := hw_other_ge4 u h2 huv
        have hdeg4 : 4 ≤ G.degree u := (Finset.mem_filter.mp hu4).2
        have hsub1 : (G.neighborFinset u) ∩ K ⊆ {w} := by
          intro z hz; rcases Finset.mem_inter.mp hz with ⟨hzN, hzK⟩
          simp only [K, Finset.mem_insert, Finset.mem_singleton] at hzK
          rcases hzK with hzv | hzw
          · rw [hzv] at hzN; exact False.elim (h1 (mem_nb.mp hzN).symm)
          · simp [hzw]
        have hle1 : ((G.neighborFinset u) ∩ K).card ≤ 1 :=
          le_trans (Finset.card_le_card hsub1) (by simp)
        omega
      · have hzero : ((G.neighborFinset u) ∩ K).card = 0 := by
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro z hz; rcases Finset.mem_inter.mp hz with ⟨hzN, hzK⟩
          simp only [K, Finset.mem_insert, Finset.mem_singleton] at hzK
          rcases hzK with hzv | hzw
          · rw [hzv] at hzN; exact h1 (mem_nb.mp hzN).symm
          · rw [hzw] at hzN; exact h2 (mem_nb.mp hzN).symm
        omega

/-- PILLAR 1.7: Sharpened Cubic Density Bound on EG2-CORE: 3 |V3(G)| >= 2n - 2. -/
theorem minimal_bad2_v3_density_sharp {V : Type} [Fintype V]
    {G : SimpleGraph V} (hG : MinimalBad2 G)
    (hhigh_ind : ∀ u ∈ VGe4 G, ∀ v ∈ VGe4 G, ¬ G.Adj u v)
    (hdef_nb_cubic : ∀ d ∈ Defects G, ∀ u, G.Adj d u → u ∈ V3 G)
    (hdeficit4 : 4 + ∑ v ∈ V3 G, ((G.neighborFinset v) ∩ VGe4 G).card ≤ 2 * (V3 G).card) :
    2 * Fintype.card V - 2 ≤ 3 * (V3 G).card := by
  have hpart : Fintype.card V = (Defects G).card + (V3 G).card + (VGe4 G).card := by
    have hdisj1 : Disjoint (Defects G) (V3 G) := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      have := (Finset.mem_filter.mp hx1).2; have := (Finset.mem_filter.mp hx2).2; omega
    have hdisj2 : Disjoint (Defects G ∪ V3 G) (VGe4 G) := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      have h4 := (Finset.mem_filter.mp hx2).2
      rcases Finset.mem_union.mp hx1 with h | h <;> (have := (Finset.mem_filter.mp h).2; omega)
    have hunion : Defects G ∪ V3 G ∪ VGe4 G = Finset.univ := by
      ext x
      simp only [Finset.mem_union, Defects, V3, VGe4, Finset.mem_filter, Finset.mem_univ, true_and,
        iff_true]
      have h2 := hG.1.2.1 x; omega
    rw [← Finset.card_univ, ← hunion, Finset.card_union_of_disjoint hdisj2,
        Finset.card_union_of_disjoint hdisj1]
  have hedge_count : ∑ h ∈ VGe4 G, G.degree h = ∑ v ∈ V3 G, ((G.neighborFinset v) ∩ VGe4 G).card := by
    have h1 : ∑ h ∈ VGe4 G, G.degree h = ∑ h ∈ VGe4 G, ((G.neighborFinset h) ∩ V3 G).card := by
      apply Finset.sum_congr rfl; intro h hh
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      congr 1; ext u
      simp only [Finset.mem_inter, mem_nb]
      constructor
      · intro hadj
        refine ⟨hadj, ?_⟩
        have hnot4 : u ∉ VGe4 G := fun hu4 => hhigh_ind h hh u hu4 hadj
        have hnot2 : u ∉ Defects G := fun hu2 => by
          have h3 := hdef_nb_cubic u hu2 h hadj.symm
          have := (Finset.mem_filter.mp h3).2; have := (Finset.mem_filter.mp hh).2; omega
        have hge2 := hG.1.2.1 u
        simp only [V3, Defects, VGe4, Finset.mem_filter, Finset.mem_univ, true_and] at hnot4 hnot2 ⊢
        omega
      · exact fun h => h.1
    rw [h1]
    have hl : ∑ h ∈ VGe4 G, ((G.neighborFinset h) ∩ V3 G).card =
        ∑ h ∈ VGe4 G, ∑ v ∈ V3 G, if G.Adj h v then 1 else 0 := by
      apply Finset.sum_congr rfl; intro h _
      rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
      congr 1; ext v
      simp only [Finset.mem_inter, mem_nb, Finset.mem_filter]; tauto
    have hr : ∑ v ∈ V3 G, ((G.neighborFinset v) ∩ VGe4 G).card =
        ∑ v ∈ V3 G, ∑ h ∈ VGe4 G, if G.Adj v h then 1 else 0 := by
      apply Finset.sum_congr rfl; intro v _
      rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
      congr 1; ext h
      simp only [Finset.mem_inter, mem_nb, Finset.mem_filter]; tauto
    rw [hl, hr, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro h _
    apply Finset.sum_congr rfl; intro v _
    simp [SimpleGraph.adj_comm]
  have h4ge4 : 4 * (VGe4 G).card ≤ ∑ h ∈ VGe4 G, G.degree h := by
    calc 4 * (VGe4 G).card = ∑ _h ∈ VGe4 G, 4 := by simp [mul_comm]
      _ ≤ ∑ h ∈ VGe4 G, G.degree h :=
          Finset.sum_le_sum (fun h hh => (Finset.mem_filter.mp hh).2)
  have hdef_le2 : (Defects G).card ≤ 2 := hG.1.2.2
  omega

/-- PILLAR 1.8: Triangle-free EG2-CORE S2 independence. -/
theorem minimal_bad2_trifree_s2_independent {V : Type} [Fintype V]
    {G : SimpleGraph V} (hG : MinimalBad2 G)
    (htrifree : ∀ a b c : V, G.Adj a b → G.Adj b c → ¬ G.Adj a c)
    {v w : V} (hv3 : v ∈ V3 G) (hw3 : w ∈ V3 G)
    (hv2 : ((G.neighborFinset v) ∩ VGe4 G).card = 2)
    (hw2 : ((G.neighborFinset w) ∩ VGe4 G).card = 2) :
    ¬ G.Adj v w := by
  intro hvw
  rcases minimal_bad2_s2_adjacent_common_high_deg4 hG hvw hv3 hw3 hv2 hw2 with ⟨h, hh, _, _⟩
  rcases Finset.mem_inter.mp hh with ⟨hhv, hhw⟩
  exact htrifree v w h hvw (mem_nb.mp hhw) (mem_nb.mp hhv)

/-- PILLAR 1.9: Triangle-free EG2-CORE: every S1 vertex has at most 1 neighbor in S2. -/
theorem minimal_bad2_trifree_s1_at_most_one_s2 {V : Type} [Fintype V]
    {G : SimpleGraph V} (hG : MinimalBad2 G)
    (htrifree : ∀ a b c : V, G.Adj a b → G.Adj b c → ¬ G.Adj a c)
    {u x y : V} (hu3 : u ∈ V3 G) (hx3 : x ∈ V3 G) (hy3 : y ∈ V3 G)
    (hux : G.Adj u x) (huy : G.Adj u y) (hxy : x ≠ y)
    (hu1 : ((G.neighborFinset u) ∩ VGe4 G).card = 1)
    (hx2 : ((G.neighborFinset x) ∩ VGe4 G).card = 2)
    (hy2 : ((G.neighborFinset y) ∩ VGe4 G).card = 2) :
    False := by
  let K : Finset V := {u, x, y}
  have hu_nd : u ∉ Defects G := fun hd => by
    have := (Finset.mem_filter.mp hu3).2; have := (Finset.mem_filter.mp hd).2; omega
  have hx_nd : x ∉ Defects G := fun hd => by
    have := (Finset.mem_filter.mp hx3).2; have := (Finset.mem_filter.mp hd).2; omega
  have hy_nd : y ∉ Defects G := fun hd => by
    have := (Finset.mem_filter.mp hy3).2; have := (Finset.mem_filter.mp hd).2; omega
  have hu_other_ge4 : ∀ z, G.Adj u z → z ≠ x → z ≠ y → z ∈ VGe4 G := by
    intro z huz hzx hzy
    have hx_n4 : x ∉ VGe4 G := fun h => by
      have := (Finset.mem_filter.mp hx3).2; have := (Finset.mem_filter.mp h).2; omega
    have hy_n4 : y ∉ VGe4 G := fun h => by
      have := (Finset.mem_filter.mp hy3).2; have := (Finset.mem_filter.mp h).2; omega
    have hsub : (G.neighborFinset u) ∩ VGe4 G ⊆ ((G.neighborFinset u).erase x).erase y := by
      intro w hw; rcases Finset.mem_inter.mp hw with ⟨hwN, hw4⟩
      exact Finset.mem_erase.mpr ⟨fun h => hy_n4 (h ▸ hw4),
        Finset.mem_erase.mpr ⟨fun h => hx_n4 (h ▸ hw4), hwN⟩⟩
    have hcard1 : (((G.neighborFinset u).erase x).erase y).card = 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hxy.symm, mem_nb.mpr huy⟩),
          Finset.card_erase_of_mem (mem_nb.mpr hux),
          SimpleGraph.card_neighborFinset_eq_degree, (Finset.mem_filter.mp hu3).2]
    have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
    have hz_in : z ∈ ((G.neighborFinset u).erase x).erase y :=
      Finset.mem_erase.mpr ⟨hzy, Finset.mem_erase.mpr ⟨hzx, mem_nb.mpr huz⟩⟩
    rw [← heq] at hz_in; exact (Finset.mem_inter.mp hz_in).2
  have hx_other_ge4 : ∀ z, G.Adj x z → z ≠ u → z ∈ VGe4 G := by
    intro z hxz hzu
    have hu_n4 : u ∉ VGe4 G := fun h => by
      have := (Finset.mem_filter.mp hu3).2; have := (Finset.mem_filter.mp h).2; omega
    have hsub : (G.neighborFinset x) ∩ VGe4 G ⊆ (G.neighborFinset x).erase u := by
      intro w hw; rcases Finset.mem_inter.mp hw with ⟨hwN, hw4⟩
      exact Finset.mem_erase.mpr ⟨fun h => hu_n4 (h ▸ hw4), hwN⟩
    have hcard2 : ((G.neighborFinset x).erase u).card = 2 := by
      rw [Finset.card_erase_of_mem (mem_nb.mpr hux.symm),
          SimpleGraph.card_neighborFinset_eq_degree, (Finset.mem_filter.mp hx3).2]
    have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
    have hz_in : z ∈ (G.neighborFinset x).erase u :=
      Finset.mem_erase.mpr ⟨hzu, mem_nb.mpr hxz⟩
    rw [← heq] at hz_in; exact (Finset.mem_inter.mp hz_in).2
  have hy_other_ge4 : ∀ z, G.Adj y z → z ≠ u → z ∈ VGe4 G := by
    intro z hyz hzu
    have hu_n4 : u ∉ VGe4 G := fun h => by
      have := (Finset.mem_filter.mp hu3).2; have := (Finset.mem_filter.mp h).2; omega
    have hsub : (G.neighborFinset y) ∩ VGe4 G ⊆ (G.neighborFinset y).erase u := by
      intro w hw; rcases Finset.mem_inter.mp hw with ⟨hwN, hw4⟩
      exact Finset.mem_erase.mpr ⟨fun h => hu_n4 (h ▸ hw4), hwN⟩
    have hcard2 : ((G.neighborFinset y).erase u).card = 2 := by
      rw [Finset.card_erase_of_mem (mem_nb.mpr huy.symm),
          SimpleGraph.card_neighborFinset_eq_degree, (Finset.mem_filter.mp hy3).2]
    have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
    have hz_in : z ∈ (G.neighborFinset y).erase u :=
      Finset.mem_erase.mpr ⟨hzu, mem_nb.mpr hyz⟩
    rw [← heq] at hz_in; exact (Finset.mem_inter.mp hz_in).2
  apply minimal_bad2_no_safe_deletion_disjoint_defects hG K ⟨u, by simp [K]⟩
  · intro d hd k hk hadj
    have hd_n4 : d ∉ VGe4 G := fun h => by
      have := (Finset.mem_filter.mp hd).2; have := (Finset.mem_filter.mp h).2; omega
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with hku | hkx | hky
    · rw [hku] at hadj
      exact hd_n4 (hu_other_ge4 d hadj.symm (fun h => hx_nd (h ▸ hd)) (fun h => hy_nd (h ▸ hd)))
    · rw [hkx] at hadj
      exact hd_n4 (hx_other_ge4 d hadj.symm (fun h => hu_nd (h ▸ hd)))
    · rw [hky] at hadj
      exact hd_n4 (hy_other_ge4 d hadj.symm (fun h => hu_nd (h ▸ hd)))
  · intro z hzKc hzd
    have hz_notK : z ∉ K := Finset.mem_compl.mp hzKc
    have hzu : z ≠ u := fun h => hz_notK (by simp [K, h])
    have hzx : z ≠ x := fun h => hz_notK (by simp [K, h])
    have hzy : z ≠ y := fun h => hz_notK (by simp [K, h])
    have hsum := degree_compl_eq_sub G K z
    have hz_ge3 : 3 ≤ G.degree z := by
      have h2 := hG.1.2.1 z
      have hne2 : G.degree z ≠ 2 := fun h => hzd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      omega
    have hzK_le1 : ((G.neighborFinset z) ∩ K).card ≤ 1 := by
      by_contra hgt; push Not at hgt
      rcases Finset.one_lt_card.mp hgt with ⟨k1, hk1, k2, hk2, hk12⟩
      rcases Finset.mem_inter.mp hk1 with ⟨hk1N, hk1K⟩
      rcases Finset.mem_inter.mp hk2 with ⟨hk2N, hk2K⟩
      have hadj1 : G.Adj z k1 := mem_nb.mp hk1N
      have hadj2 : G.Adj z k2 := mem_nb.mp hk2N
      simp only [K, Finset.mem_insert, Finset.mem_singleton] at hk1K hk2K
      rcases hk1K with h1 | h1 | h1 <;> rcases hk2K with h2 | h2 | h2
      · exact hk12 (h1.trans h2.symm)
      · rw [h1] at hadj1; rw [h2] at hadj2; exact htrifree u x z hux hadj2.symm hadj1.symm
      · rw [h1] at hadj1; rw [h2] at hadj2; exact htrifree u y z huy hadj2.symm hadj1.symm
      · rw [h1] at hadj1; rw [h2] at hadj2; exact htrifree u x z hux hadj1.symm hadj2.symm
      · exact hk12 (h1.trans h2.symm)
      · rw [h1] at hadj1; rw [h2] at hadj2
        have hu_in : u ∈ (G.neighborFinset x) ∩ (G.neighborFinset y) :=
          Finset.mem_inter.mpr ⟨mem_nb.mpr hux.symm, mem_nb.mpr huy.symm⟩
        have hz_in : z ∈ (G.neighborFinset x) ∩ (G.neighborFinset y) :=
          Finset.mem_inter.mpr ⟨mem_nb.mpr hadj1.symm, mem_nb.mpr hadj2.symm⟩
        have h2c : 2 ≤ ((G.neighborFinset x) ∩ (G.neighborFinset y)).card := by
          have := Finset.card_le_card (show ({u, z} : Finset V) ⊆ _ by
            intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
            rcases hw with rfl | rfl <;> assumption)
          rw [Finset.card_pair hzu.symm] at this; exact this
        have h1c := minimal_bad2_common_neighbors_le_one hG hxy
        omega
      · rw [h1] at hadj1; rw [h2] at hadj2; exact htrifree u y z huy hadj1.symm hadj2.symm
      · rw [h1] at hadj1; rw [h2] at hadj2
        have hu_in : u ∈ (G.neighborFinset x) ∩ (G.neighborFinset y) :=
          Finset.mem_inter.mpr ⟨mem_nb.mpr hux.symm, mem_nb.mpr huy.symm⟩
        have hz_in : z ∈ (G.neighborFinset x) ∩ (G.neighborFinset y) :=
          Finset.mem_inter.mpr ⟨mem_nb.mpr hadj2.symm, mem_nb.mpr hadj1.symm⟩
        have h2c : 2 ≤ ((G.neighborFinset x) ∩ (G.neighborFinset y)).card := by
          have := Finset.card_le_card (show ({u, z} : Finset V) ⊆ _ by
            intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
            rcases hw with rfl | rfl <;> assumption)
          rw [Finset.card_pair hzu.symm] at this; exact this
        have h1c := minimal_bad2_common_neighbors_le_one hG hxy
        omega
      · exact hk12 (h1.trans h2.symm)
    by_cases hpos : 0 < ((G.neighborFinset z) ∩ K).card
    · rcases Finset.card_pos.mp hpos with ⟨k, hk⟩
      rcases Finset.mem_inter.mp hk with ⟨hkN, hkK⟩
      have hadj : G.Adj k z := (mem_nb.mp hkN).symm
      have hz4 : z ∈ VGe4 G := by
        simp only [K, Finset.mem_insert, Finset.mem_singleton] at hkK
        rcases hkK with hku | hkx | hky
        · rw [hku] at hadj; exact hu_other_ge4 z hadj hzx hzy
        · rw [hkx] at hadj; exact hx_other_ge4 z hadj hzu
        · rw [hky] at hadj; exact hy_other_ge4 z hadj hzu
      have hdeg4 : 4 ≤ G.degree z := (Finset.mem_filter.mp hz4).2
      omega
    · omega

/-- PILLAR 1.10: Triangle-free EG2-CORE 8/11 Cubic Density Bound: 11 |V3(G)| >= 8n - 16. -/
theorem minimal_bad2_trifree_v3_density_8_11 {V : Type} [Fintype V]
    {G : SimpleGraph V} (hG : MinimalBad2 G)
    (hhigh_ind : ∀ u ∈ VGe4 G, ∀ v ∈ VGe4 G, ¬ G.Adj u v)
    (hdef_nb_cubic : ∀ d ∈ Defects G, ∀ u, G.Adj d u → u ∈ V3 G)
    (hv3_le2 : ∀ v ∈ V3 G, ((G.neighborFinset v) ∩ VGe4 G).card ≤ 2)
    (hs2_bound :
      ((V3 G).filter (fun v => ((G.neighborFinset v) ∩ VGe4 G).card = 2)).card ≤
      3 * ((V3 G).filter (fun v => ((G.neighborFinset v) ∩ VGe4 G).card = 0)).card +
      ((V3 G).filter (fun v => ((G.neighborFinset v) ∩ VGe4 G).card = 1)).card) :
    8 * Fintype.card V - 16 ≤ 11 * (V3 G).card := by
  let S0 := (V3 G).filter (fun v => ((G.neighborFinset v) ∩ VGe4 G).card = 0)
  let S1 := (V3 G).filter (fun v => ((G.neighborFinset v) ∩ VGe4 G).card = 1)
  let S2 := (V3 G).filter (fun v => ((G.neighborFinset v) ∩ VGe4 G).card = 2)
  have hd1 : Disjoint S0 S1 := by
    rw [Finset.disjoint_left]; intro x h1 h2
    have := (Finset.mem_filter.mp h1).2; have := (Finset.mem_filter.mp h2).2; omega
  have hd2 : Disjoint (S0 ∪ S1) S2 := by
    rw [Finset.disjoint_left]; intro x h1 h2
    have h := (Finset.mem_filter.mp h2).2
    rcases Finset.mem_union.mp h1 with h' | h' <;> (have := (Finset.mem_filter.mp h').2; omega)
  have hu : S0 ∪ S1 ∪ S2 = V3 G := by
    ext x; simp only [Finset.mem_union, S0, S1, S2, Finset.mem_filter]
    constructor
    · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
    · intro hx; have hle := hv3_le2 x hx; omega
  have hv3_split : (V3 G).card = S0.card + S1.card + S2.card := by
    rw [← hu, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]
  have hsum_v3 : ∑ v ∈ V3 G, ((G.neighborFinset v) ∩ VGe4 G).card = S1.card + 2 * S2.card := by
    rw [← hu, Finset.sum_union hd2, Finset.sum_union hd1]
    have h0 : ∑ v ∈ S0, ((G.neighborFinset v) ∩ VGe4 G).card = 0 :=
      Finset.sum_eq_zero (fun v hv => (Finset.mem_filter.mp hv).2)
    have h1 : ∑ v ∈ S1, ((G.neighborFinset v) ∩ VGe4 G).card = S1.card := by
      calc ∑ v ∈ S1, ((G.neighborFinset v) ∩ VGe4 G).card = ∑ _v ∈ S1, 1 :=
            Finset.sum_congr rfl (fun v hv => (Finset.mem_filter.mp hv).2)
        _ = S1.card := by simp
    have h2 : ∑ v ∈ S2, ((G.neighborFinset v) ∩ VGe4 G).card = 2 * S2.card := by
      calc ∑ v ∈ S2, ((G.neighborFinset v) ∩ VGe4 G).card = ∑ _v ∈ S2, 2 :=
            Finset.sum_congr rfl (fun v hv => (Finset.mem_filter.mp hv).2)
        _ = 2 * S2.card := by simp [mul_comm]
    rw [h0, h1, h2, zero_add]
  have hpart : Fintype.card V = (Defects G).card + (V3 G).card + (VGe4 G).card := by
    have hdisj1 : Disjoint (Defects G) (V3 G) := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      have := (Finset.mem_filter.mp hx1).2; have := (Finset.mem_filter.mp hx2).2; omega
    have hdisj2 : Disjoint (Defects G ∪ V3 G) (VGe4 G) := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      have h4 := (Finset.mem_filter.mp hx2).2
      rcases Finset.mem_union.mp hx1 with h | h <;> (have := (Finset.mem_filter.mp h).2; omega)
    have hunion : Defects G ∪ V3 G ∪ VGe4 G = Finset.univ := by
      ext x; simp only [Finset.mem_union, Defects, V3, VGe4, Finset.mem_filter, Finset.mem_univ,
        true_and, iff_true]
      have h2 := hG.1.2.1 x; omega
    rw [← Finset.card_univ, ← hunion, Finset.card_union_of_disjoint hdisj2,
        Finset.card_union_of_disjoint hdisj1]
  have h4ge4 : 4 * (VGe4 G).card ≤ ∑ v ∈ V3 G, ((G.neighborFinset v) ∩ VGe4 G).card := by
    have hedge_count : ∑ h ∈ VGe4 G, G.degree h = ∑ v ∈ V3 G, ((G.neighborFinset v) ∩ VGe4 G).card := by
      have h1 : ∑ h ∈ VGe4 G, G.degree h = ∑ h ∈ VGe4 G, ((G.neighborFinset h) ∩ V3 G).card := by
        apply Finset.sum_congr rfl; intro h hh
        rw [← SimpleGraph.card_neighborFinset_eq_degree]
        congr 1; ext u
        simp only [Finset.mem_inter, mem_nb]
        constructor
        · intro hadj
          refine ⟨hadj, ?_⟩
          have hnot4 : u ∉ VGe4 G := fun hu4 => hhigh_ind h hh u hu4 hadj
          have hnot2 : u ∉ Defects G := fun hu2 => by
            have h3 := hdef_nb_cubic u hu2 h hadj.symm
            have := (Finset.mem_filter.mp h3).2; have := (Finset.mem_filter.mp hh).2; omega
          have hge2 := hG.1.2.1 u
          simp only [V3, Defects, VGe4, Finset.mem_filter, Finset.mem_univ, true_and] at hnot4 hnot2 ⊢
          omega
        · exact fun h => h.1
      rw [h1]
      have hl : ∑ h ∈ VGe4 G, ((G.neighborFinset h) ∩ V3 G).card =
          ∑ h ∈ VGe4 G, ∑ v ∈ V3 G, if G.Adj h v then 1 else 0 := by
        apply Finset.sum_congr rfl; intro h _
        rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
        congr 1; ext v
        simp only [Finset.mem_inter, mem_nb, Finset.mem_filter]; tauto
      have hr : ∑ v ∈ V3 G, ((G.neighborFinset v) ∩ VGe4 G).card =
          ∑ v ∈ V3 G, ∑ h ∈ VGe4 G, if G.Adj v h then 1 else 0 := by
        apply Finset.sum_congr rfl; intro v _
        rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
        congr 1; ext h
        simp only [Finset.mem_inter, mem_nb, Finset.mem_filter]; tauto
      rw [hl, hr, Finset.sum_comm]
      apply Finset.sum_congr rfl; intro h _
      apply Finset.sum_congr rfl; intro v _
      simp [SimpleGraph.adj_comm]
    rw [← hedge_count]
    calc 4 * (VGe4 G).card = ∑ _h ∈ VGe4 G, 4 := by simp [mul_comm]
      _ ≤ ∑ h ∈ VGe4 G, G.degree h :=
          Finset.sum_le_sum (fun h hh => (Finset.mem_filter.mp hh).2)
  have hdef_le2 : (Defects G).card ≤ 2 := hG.1.2.2
  omega

/-- PILLAR 2: Vertex identification graph G / {x = y} on subtype {v : V // v ≠ y}. -/
def identGraph {V : Type*} (G : SimpleGraph V) (x y : V) :
    SimpleGraph {v : V // v ≠ y} where
  Adj u v := u ≠ v ∧ (G.Adj u.1 v.1 ∨ (u.1 = x ∧ G.Adj y v.1) ∨ (v.1 = x ∧ G.Adj u.1 y))
  symm := by
    rintro u v ⟨hne, h | ⟨rfl, hy⟩ | ⟨rfl, hy⟩⟩
    · exact ⟨hne.symm, Or.inl h.symm⟩
    · exact ⟨hne.symm, Or.inr (Or.inr ⟨rfl, hy.symm⟩)⟩
    · exact ⟨hne.symm, Or.inr (Or.inl ⟨rfl, hy.symm⟩)⟩
  loopless := fun _ ⟨hne, _⟩ => hne rfl

/-- Helper: lifting a walk in identGraph G x y that avoids ⟨x, hxy⟩ gives a walk in G
    with exact length, support, and edge-list correspondence. -/
lemma identGraph_walk_lift {V : Type*} {G : SimpleGraph V} {x y : V} (hxy : x ≠ y)
    {u v : {w : V // w ≠ y}} (p : (identGraph G x y).Walk u v)
    (havoid : ⟨x, hxy⟩ ∉ p.support) :
    ∃ q : G.Walk u.1 v.1,
      q.length = p.length ∧
      q.support = p.support.map Subtype.val ∧
      q.edges = p.edges.map (Sym2.map Subtype.val) := by
  induction p with
  | nil =>
    exact ⟨Walk.nil, rfl, rfl, rfl⟩
  | @cons a b c hab p ih =>
    have ha_ne : a ≠ ⟨x, hxy⟩ := fun h => havoid (by simp [h])
    have hb_ne : b ≠ ⟨x, hxy⟩ := fun h => havoid (by simp [h])
    have havoid' : ⟨x, hxy⟩ ∉ p.support := fun h => havoid (List.mem_cons_of_mem _ h)
    rcases ih havoid' with ⟨q, hlen, hsupp, hedges⟩
    have hadjG : G.Adj a.1 b.1 := by
      rcases hab.2 with h | ⟨hax, _⟩ | ⟨hbx, _⟩
      · exact h
      · exact False.elim (ha_ne (Subtype.ext hax))
      · exact False.elim (hb_ne (Subtype.ext hbx))
    exact ⟨Walk.cons hadjG q, by simp [hlen], by simp [hsupp], by simp [hedges]⟩

/-- PILLAR 2.1: Universal Identification Cycle-Lifting Theorem. -/
theorem identGraph_cycle_lifts_to_dyadic_path {V : Type*} {G : SimpleGraph V}
    (hpf : PowerFree G) {x y : V} (hxy : x ≠ y)
    (hcyc_ex : HasPowerCycle (identGraph G x y)) :
    ∃ (p : G.Walk x y), p.IsPath ∧ IsPowerOfTwo p.length := by
  rcases hcyc_ex with ⟨v0, c0, hc0, hpow⟩
  let z : {w : V // w ≠ y} := ⟨x, hxy⟩
  by_cases hz : z ∈ c0.support
  · let c := c0.rotate hz
    have hc : c.IsCycle := hc0.rotate hz
    have hclen : IsPowerOfTwo c.length := by simpa [c] using hpow
    cases c with
    | nil => exact False.elim (hc.ne_nil rfl)
    | @cons _ b _ hzb rest =>
      have hrest_nodup : rest.support.Nodup := by
        have := hc.support_nodup; simpa using this
      let rev := rest.reverse
      cases hrev : rev with
      | nil =>
        have hlen0 : rest.length = 0 := by
          have := congrArg Walk.length hrev; simpa [rev] using this
        have h1 : (Walk.cons hzb rest).length = 1 := by simp [hlen0]
        have h3 := hc.three_le_length; omega
      | @cons _ d _ hzd mid =>
        have hrev_nodup : rev.support.Nodup := by
          rw [← List.nodup_reverse, ← Walk.support_reverse]
          simpa [rev] using hrest_nodup
        rw [hrev] at hrev_nodup
        have hz_not_mid : z ∉ mid.support := (List.nodup_cons.mp hrev_nodup).1
        rcases identGraph_walk_lift hxy mid hz_not_mid with ⟨q, hqlen, hqsupp, _⟩
        have hq_nodup : q.support.Nodup := by
          rw [hqsupp]; exact ((List.nodup_cons.mp hrev_nodup).2).map Subtype.val_injective
        have hy_not_q : y ∉ q.support := by
          rw [hqsupp]; intro hy_in
          rcases List.mem_map.mp hy_in with ⟨w, _, hwy⟩; exact w.2 hwy
        have hx_not_q : x ∉ q.support := by
          rw [hqsupp]; intro hx_in
          rcases List.mem_map.mp hx_in with ⟨w, hw, hwx⟩
          exact hz_not_mid (by convert hw; exact Subtype.ext hwx.symm)
        have hqlen_eq : q.length + 2 = (Walk.cons hzb rest).length := by
          have h1 : rev.length = rest.length := Walk.length_reverse rest
          rw [hrev] at h1; simp only [Walk.length_cons] at h1 ⊢; omega
        have hb_adj : G.Adj x b.1 ∨ G.Adj y b.1 := by
          rcases hzb.2 with h | ⟨_, hyb⟩ | ⟨hbx, _⟩
          · exact Or.inl h
          · exact Or.inr hyb
          · exact False.elim (hzb.1 (Subtype.ext hbx.symm))
        have hd_adj : G.Adj x d.1 ∨ G.Adj y d.1 := by
          rcases hzd.2 with h | ⟨_, hyd⟩ | ⟨hdx, _⟩
          · exact Or.inl h
          · exact Or.inr hyd
          · exact False.elim (hzd.1 (Subtype.ext hdx.symm))
        have hlen_ge3 : 3 ≤ (Walk.cons hzb rest).length := hc.three_le_length
        have hqlen_ge1 : 1 ≤ q.length := by omega
        have mk_cyc : ∀ {w : V}, w ∉ q.support → G.Adj w d.1 → G.Adj w b.1 → False := by
          intro w hw_not hwd hwb
          let cyc : G.Walk w w := Walk.cons hwd (q.concat hwb.symm)
          have hcyc_len : cyc.length = (Walk.cons hzb rest).length := by
            simp [cyc, Walk.length_concat, hqlen_eq]
          have hcyc_is : cyc.IsCycle := by
            rw [Walk.isCycle_def]
            refine ⟨?_, by simp [cyc], ?_⟩
            · rw [Walk.isTrail_def]
              have hq_path : q.IsPath := Walk.IsPath.mk' hq_nodup
              have hq_edges_nodup : q.edges.Nodup := hq_path.isTrail.edges_nodup
              have hw_not_edges : ∀ e ∈ q.edges, w ∉ e := fun e he hwe =>
                hw_not (Walk.mem_support_of_mem_edges q he hwe)
              have hdb_ne : d.1 ≠ b.1 := by
                intro heq
                have hq0 : q.length = 0 := by
                  cases q with
                  | nil => rfl
                  | @cons _ next _ h1 q' =>
                    have hnd := List.nodup_cons.mp hq_nodup
                    have hmem : d.1 ∈ (Walk.cons h1 q').support.tail := by
                      rw [heq]; exact Walk.end_mem_support _
                    exact False.elim (hnd.1 hmem)
                omega
              simp only [cyc, Walk.edges_cons, Walk.edges_concat, List.nodup_cons, List.mem_append,
                List.mem_singleton, not_or, List.nodup_append]
              refine ⟨⟨fun hm => hw_not_edges _ hm (by simp), ?_⟩, hq_edges_nodup,
                List.nodup_singleton _, ?_⟩
              · rw [Sym2.eq_iff]
                rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
                · exact G.ne_of_adj hwd rfl
                · exact hdb_ne rfl
              · intro e he e' he' heq
                rw [List.mem_singleton] at he'; subst he'; rw [heq] at he
                exact hw_not_edges _ he (by simp)
            · simp only [cyc, Walk.support_cons, Walk.support_concat, List.tail_cons]
              rw [List.nodup_append]
              refine ⟨hq_nodup, List.nodup_singleton _, ?_⟩
              intro a ha a' ha' heq
              rw [List.mem_singleton] at ha'; subst ha'; subst heq; exact hw_not ha
          exact hpf ⟨w, cyc, hcyc_is, hcyc_len ▸ hclen⟩
        rcases hd_adj with hxd | hyd <;> rcases hb_adj with hxb | hyb
        · exact False.elim (mk_cyc hx_not_q hxd hxb)
        · let path : G.Walk x y := Walk.cons hxd (q.concat hyb.symm)
          refine ⟨path, Walk.IsPath.mk' ?_, ?_⟩
          · simp only [path, Walk.support_cons, Walk.support_concat, List.nodup_cons,
              List.mem_append, List.mem_singleton, not_or]
            refine ⟨⟨hx_not_q, hxy⟩, ?_⟩
            rw [List.nodup_append]
            refine ⟨hq_nodup, List.nodup_singleton _, ?_⟩
            intro a ha a' ha' heq
            rw [List.mem_singleton] at ha'; subst ha'; subst heq; exact hy_not_q ha
          · have : path.length = (Walk.cons hzb rest).length := by
              simp [path, Walk.length_concat, hqlen_eq]
            rw [this]; exact hclen
        · let path_rev : G.Walk y x := Walk.cons hyd (q.concat hxb.symm)
          have hpr_nodup : path_rev.support.Nodup := by
            simp only [path_rev, Walk.support_cons, Walk.support_concat, List.nodup_cons,
              List.mem_append, List.mem_singleton, not_or]
            refine ⟨⟨hy_not_q, hxy.symm⟩, ?_⟩
            rw [List.nodup_append]
            refine ⟨hq_nodup, List.nodup_singleton _, ?_⟩
            intro a ha a' ha' heq
            rw [List.mem_singleton] at ha'; subst ha'; subst heq; exact hx_not_q ha
          refine ⟨path_rev.reverse, (Walk.IsPath.mk' hpr_nodup).reverse, ?_⟩
          have : path_rev.reverse.length = (Walk.cons hzb rest).length := by
            simp [path_rev, Walk.length_reverse, Walk.length_concat, hqlen_eq]
          rw [this]; exact hclen
        · exact False.elim (mk_cyc hy_not_q hyd hyb)
  · rcases identGraph_walk_lift hxy c0 hz with ⟨q, hqlen, hqsupp, hqedges⟩
    have hq_cyc : q.IsCycle := by
      rw [Walk.isCycle_def]
      refine ⟨?_, ?_, ?_⟩
      · rw [Walk.isTrail_def, hqedges]
        exact hc0.isTrail.edges_nodup.map (Sym2.map.injective Subtype.val_injective)
      · intro hnil
        have : c0.length = 0 := by rw [← hqlen, hnil]; rfl
        have := hc0.three_le_length; omega
      · rw [hqsupp, List.tail_map]
        exact hc0.support_nodup.map Subtype.val_injective
    exact False.elim (hpf ⟨v0.1, q, hq_cyc, hqlen ▸ hpow⟩)

/-- Helper: degree of non-merged vertex u ≠ ⟨x, hxy⟩ in identGraph G x y when u is not a
    common neighbor of x and y equals G.degree u.1. -/
lemma identGraph_degree_other_no_common {V : Type*} [Fintype V] (G : SimpleGraph V)
    {x y : V} (hxy : x ≠ y) (u : {w : V // w ≠ y}) (hux : u.1 ≠ x)
    (hnot_comm : ¬ (G.Adj u.1 x ∧ G.Adj u.1 y)) :
    (identGraph G x y).degree u = G.degree u.1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun v _ => if v.1 = x ∧ G.Adj u.1 y then y else v.1)
  · intro v hv
    simp only [mem_nb, identGraph] at hv ⊢
    split_ifs with h
    · exact h.2
    · rcases hv.2 with hadj | ⟨hux', _⟩ | ⟨hvx, huy⟩
      · exact hadj
      · exact False.elim (hux hux')
      · exact False.elim (h ⟨hvx, huy⟩)
  · intro v1 hv1 v2 hv2 heq
    simp only [mem_nb, identGraph] at hv1 hv2
    split_ifs at heq with h1 h2
    · exact Subtype.ext (h1.1.trans h2.1.symm)
    · exact False.elim (v2.2 heq.symm)
    · exact False.elim (v1.2 heq)
    · exact Subtype.ext heq
  · intro w hw
    rw [mem_nb] at hw
    by_cases hwy : w = y
    · subst hwy
      refine ⟨⟨x, hxy⟩, ?_, ?_⟩
      · simp only [mem_nb, identGraph]
        exact ⟨fun h => hux (congrArg Subtype.val h), Or.inr (Or.inr ⟨rfl, hw⟩)⟩
      · simp [hw]
    · refine ⟨⟨w, hwy⟩, ?_, ?_⟩
      · simp only [mem_nb, identGraph]
        exact ⟨fun h => G.ne_of_adj hw (congrArg Subtype.val h), Or.inl hw⟩
      · split_ifs with h
        · exact False.elim (hnot_comm ⟨h.1 ▸ hw, h.2⟩)
        · rfl

/-- Helper: degree of a common neighbor u of x and y in identGraph G x y drops by exactly 1. -/
lemma identGraph_degree_other_common {V : Type*} [Fintype V] (G : SimpleGraph V)
    {x y : V} (hxy : x ≠ y) (u : {w : V // w ≠ y}) (hux : u.1 ≠ x)
    (hcomm : G.Adj u.1 x ∧ G.Adj u.1 y) :
    (identGraph G x y).degree u = G.degree u.1 - 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  have hy_in : y ∈ G.neighborFinset u.1 := mem_nb.mpr hcomm.2
  rw [← Finset.card_erase_of_mem hy_in]
  apply Finset.card_bij (fun v _ => v.1)
  · intro v hv
    simp only [mem_nb, identGraph, Finset.mem_erase] at hv ⊢
    refine ⟨v.2, ?_⟩
    rcases hv.2 with hadj | ⟨hux', _⟩ | ⟨hvx, _⟩
    · exact hadj
    · exact False.elim (hux hux')
    · exact hvx ▸ hcomm.1
  · intro _ _ _ _ h
    exact Subtype.ext h
  · intro w hw
    simp only [Finset.mem_erase, mem_nb] at hw
    refine ⟨⟨w, hw.1⟩, ?_, rfl⟩
    simp only [mem_nb, identGraph]
    exact ⟨fun h => G.ne_of_adj hw.2 (congrArg Subtype.val h), Or.inl hw.2⟩

/-- Helper: degree of merged vertex ⟨x, hxy⟩ in identGraph G x y. -/
lemma identGraph_degree_merged {V : Type*} [Fintype V] (G : SimpleGraph V)
    {x y : V} (hxy : x ≠ y) :
    (identGraph G x y).degree ⟨x, hxy⟩ =
      (((G.neighborFinset x) ∪ (G.neighborFinset y)) \ {x, y}).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun v _ => v.1)
  · intro v hv
    simp only [mem_nb, identGraph, Finset.mem_sdiff, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton, not_or] at hv ⊢
    refine ⟨?_, fun h => hv.1 (Subtype.ext h.symm), v.2⟩
    rcases hv.2 with h | ⟨_, hy⟩ | ⟨hvx, _⟩
    · exact Or.inl h
    · exact Or.inr hy
    · exact False.elim (hv.1 (Subtype.ext hvx.symm))
  · intro _ _ _ _ h
    exact Subtype.ext h
  · intro w hw
    simp only [Finset.mem_sdiff, Finset.mem_union, mem_nb,
      Finset.mem_insert, Finset.mem_singleton, not_or] at hw
    refine ⟨⟨w, hw.2.2⟩, ?_, rfl⟩
    simp only [mem_nb, identGraph]
    refine ⟨fun h => hw.2.1 (congrArg Subtype.val h).symm, ?_⟩
    rcases hw.1 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨rfl, h⟩)

/-- PILLAR 2.2: Universal Distance-ge-3 All-Pairs Dyadic Path Theorem on EG2-CORE. -/
theorem minimal_bad2_dist3_all_pairs_dyadic_path {V : Type} [Fintype V]
    {G : SimpleGraph V} (hG : MinimalBad2 G) {x y : V}
    (hxy : x ≠ y) (hnadj : ¬ G.Adj x y)
    (hdisjN : Disjoint (G.neighborFinset x) (G.neighborFinset y)) :
    ∃ (p : G.Walk x y), p.IsPath ∧ IsPowerOfTwo p.length := by
  let H := identGraph G x y
  have hH_not_pf : ¬ PowerFree H := by
    intro hpf
    have hdeg_z : 4 ≤ H.degree ⟨x, hxy⟩ := by
      rw [identGraph_degree_merged]
      have hdisj_xy : Disjoint (G.neighborFinset x ∪ G.neighborFinset y) ({x, y} : Finset V) := by
        rw [Finset.disjoint_left]
        intro w hw hxy_mem
        simp only [Finset.mem_union, mem_nb] at hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hxy_mem
        rcases hxy_mem with rfl | rfl
        · rcases hw with h | h
          · exact G.loopless x h
          · exact hnadj h.symm
        · rcases hw with h | h
          · exact hnadj h
          · exact G.loopless y h
      rw [Finset.sdiff_eq_self_of_disjoint hdisj_xy, Finset.card_union_of_disjoint hdisjN,
          SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.card_neighborFinset_eq_degree]
      have hx2 := hG.1.2.1 x; have hy2 := hG.1.2.1 y; omega
    have hdeg_other : ∀ u : {w : V // w ≠ y}, u.1 ≠ x → H.degree u = G.degree u.1 := by
      intro u hux
      apply identGraph_degree_other_no_common G hxy u hux
      rintro ⟨h1, h2⟩
      exact Finset.disjoint_left.mp hdisjN (mem_nb.mpr h1.symm) (mem_nb.mpr h2.symm)
    have hH_min : MinDegGe H 2 := by
      intro u
      by_cases hux : u.1 = x
      · have heq : u = ⟨x, hxy⟩ := Subtype.ext hux; rw [heq]; omega
      · rw [hdeg_other u hux]; exact hG.1.2.1 u.1
    have hH_def : (Defects H).card ≤ 2 := by
      have hcard_le : (Defects H).card ≤ (Defects G).card := by
        apply Finset.card_le_card_of_injOn Subtype.val
        · intro u hu
          simp only [Defects, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
          by_cases hux : u.1 = x
          · have heq : u = ⟨x, hxy⟩ := Subtype.ext hux; rw [heq] at hu; omega
          · rw [← hdeg_other u hux]; exact hu
        · intro _ _ _ _ h; exact Subtype.ext h
      exact le_trans hcard_le hG.1.2.2
    have hlt : Fintype.card {w : V // w ≠ y} < Fintype.card V := by
      rw [Fintype.card_subtype_compl, Fintype.card_unique]
      have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨x⟩
      omega
    exact minimal_bad2_no_smaller hG H ⟨hpf, hH_min, hH_def⟩ hlt
  exact identGraph_cycle_lifts_to_dyadic_path hG.1.1 hxy (not_not.mp hH_not_pf)

/-- PILLAR 2.3: Universal Defect-to-Any Dyadic Path Theorem on EG2-CORE. -/
theorem minimal_bad2_defect_to_any_dyadic_path {V : Type} [Fintype V]
    {G : SimpleGraph V} (hG : MinimalBad2 G) {a y : V}
    (ha : a ∈ Defects G) (hay : a ≠ y) (hnadj : ¬ G.Adj a y)
    (hdef_nb_ge3 : ∀ u, G.Adj a u → 3 ≤ G.degree u) :
    ∃ (p : G.Walk a y), p.IsPath ∧ IsPowerOfTwo p.length := by
  let H := identGraph G a y
  have hH_not_pf : ¬ PowerFree H := by
    intro hpf
    have hcomm_le1 := minimal_bad2_common_neighbors_le_one hG hay
    have hdeg_z : 3 ≤ H.degree ⟨a, hay⟩ := by
      rw [identGraph_degree_merged]
      have hdisj_ay : Disjoint (G.neighborFinset a ∪ G.neighborFinset y) ({a, y} : Finset V) := by
        rw [Finset.disjoint_left]
        intro w hw hay_mem
        simp only [Finset.mem_union, mem_nb] at hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hay_mem
        rcases hay_mem with rfl | rfl
        · rcases hw with h | h
          · exact G.loopless a h
          · exact hnadj h.symm
        · rcases hw with h | h
          · exact hnadj h
          · exact G.loopless y h
      rw [Finset.sdiff_eq_self_of_disjoint hdisj_ay]
      have hunion := Finset.card_union_add_card_inter (G.neighborFinset a) (G.neighborFinset y)
      rw [SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.card_neighborFinset_eq_degree] at hunion
      have ha2 := hG.1.2.1 a; have hy2 := hG.1.2.1 y
      omega
    have hH_min : MinDegGe H 2 := by
      intro u
      by_cases hua : u.1 = a
      · have heq : u = ⟨a, hay⟩ := Subtype.ext hua; rw [heq]; omega
      · by_cases hcomm : G.Adj u.1 a ∧ G.Adj u.1 y
        · rw [identGraph_degree_other_common G hay u hua hcomm]
          have h3 := hdef_nb_ge3 u.1 hcomm.1.symm
          omega
        · rw [identGraph_degree_other_no_common G hay u hua hcomm]
          exact hG.1.2.1 u.1
    have hH_def : (Defects H).card ≤ 2 := by
      have hcard_le : (Defects H).card ≤
          (((Defects G).erase a) ∪ ((G.neighborFinset a) ∩ (G.neighborFinset y))).card := by
        apply Finset.card_le_card_of_injOn Subtype.val
        · intro u hu
          simp only [Defects, Finset.mem_filter, Finset.mem_univ, true_and] at hu
          by_cases hua : u.1 = a
          · have heq : u = ⟨a, hay⟩ := Subtype.ext hua; rw [heq] at hu; omega
          · by_cases hcomm : G.Adj u.1 a ∧ G.Adj u.1 y
            · apply Finset.mem_union_right
              exact Finset.mem_inter.mpr ⟨mem_nb.mpr hcomm.1.symm, mem_nb.mpr hcomm.2.symm⟩
            · rw [identGraph_degree_other_no_common G hay u hua hcomm] at hu
              apply Finset.mem_union_left
              exact Finset.mem_erase.mpr ⟨hua, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩⟩
        · intro _ _ _ _ h; exact Subtype.ext h
      have hunion_le := Finset.card_union_le ((Defects G).erase a) ((G.neighborFinset a) ∩ (G.neighborFinset y))
      have herase : ((Defects G).erase a).card = (Defects G).card - 1 := Finset.card_erase_of_mem ha
      have hdef2 := hG.1.2.2
      omega
    have hlt : Fintype.card {w : V // w ≠ y} < Fintype.card V := by
      rw [Fintype.card_subtype_compl, Fintype.card_unique]
      have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨a⟩
      omega
    exact minimal_bad2_no_smaller hG H ⟨hpf, hH_min, hH_def⟩ hlt
  exact identGraph_cycle_lifts_to_dyadic_path hG.1.1 hay (not_not.mp hH_not_pf)

/-- PILLAR 2.4: Universal Non-Triangle Edge (2^k + 1)-Cycle Forcing on EG2-CORE. -/
theorem minimal_bad2_non_triangle_edge_dyadic_plus_one_cycle {V : Type} [Fintype V]
    {G : SimpleGraph V} (hG : MinimalBad2 G) {u v : V}
    (huv : G.Adj u v) (hsum5 : 5 ≤ G.degree u + G.degree v)
    (hdisjN : Disjoint (G.neighborFinset u) (G.neighborFinset v)) :
    ∃ (c : G.Walk u u), c.IsCycle ∧ s(u, v) ∈ c.edges ∧ ∃ k : ℕ, 2 ≤ k ∧ c.length = 2 ^ k + 1 := by
  have huv_ne : u ≠ v := G.ne_of_adj huv
  let H := identGraph G u v
  have hH_not_pf : ¬ PowerFree H := by
    intro hpf
    have hdeg_z : 3 ≤ H.degree ⟨u, huv_ne⟩ := by
      rw [identGraph_degree_merged]
      have hsub : ((G.neighborFinset u).erase v) ∪ ((G.neighborFinset v).erase u) ⊆
          (G.neighborFinset u ∪ G.neighborFinset v) \ {u, v} := by
        intro w hw
        simp only [Finset.mem_union, Finset.mem_erase, mem_nb,
          Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hw ⊢
        rcases hw with ⟨hwv, hwu⟩ | ⟨hwu, hwv⟩
        · exact ⟨Or.inl hwu, G.ne_of_adj hwu.symm, hwv⟩
        · exact ⟨Or.inr hwv, hwu, G.ne_of_adj hwv.symm⟩
      have hd : Disjoint ((G.neighborFinset u).erase v) ((G.neighborFinset v).erase u) :=
        hdisjN.mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hd,
          Finset.card_erase_of_mem (mem_nb.mpr huv),
          Finset.card_erase_of_mem (mem_nb.mpr huv.symm),
          SimpleGraph.card_neighborFinset_eq_degree,
          SimpleGraph.card_neighborFinset_eq_degree] at hcard
      have hu2 := hG.1.2.1 u; have hv2 := hG.1.2.1 v; omega
    have hdeg_other : ∀ w : {z : V // z ≠ v}, w.1 ≠ u → H.degree w = G.degree w.1 := by
      intro w hwu
      apply identGraph_degree_other_no_common G huv_ne w hwu
      rintro ⟨h1, h2⟩
      exact Finset.disjoint_left.mp hdisjN (mem_nb.mpr h1.symm) (mem_nb.mpr h2.symm)
    have hH_min : MinDegGe H 2 := by
      intro w
      by_cases hwu : w.1 = u
      · have heq : w = ⟨u, huv_ne⟩ := Subtype.ext hwu; rw [heq]; omega
      · rw [hdeg_other w hwu]; exact hG.1.2.1 w.1
    have hH_def : (Defects H).card ≤ 2 := by
      have hcard_le : (Defects H).card ≤ (Defects G).card := by
        apply Finset.card_le_card_of_injOn Subtype.val
        · intro w hw
          simp only [Defects, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
          by_cases hwu : w.1 = u
          · have heq : w = ⟨u, huv_ne⟩ := Subtype.ext hwu; rw [heq] at hw; omega
          · rw [← hdeg_other w hwu]; exact hw
        · intro _ _ _ _ h; exact Subtype.ext h
      exact le_trans hcard_le hG.1.2.2
    have hlt : Fintype.card {z : V // z ≠ v} < Fintype.card V := by
      rw [Fintype.card_subtype_compl, Fintype.card_unique]
      have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨u⟩
      omega
    exact minimal_bad2_no_smaller hG H ⟨hpf, hH_min, hH_def⟩ hlt
  rcases identGraph_cycle_lifts_to_dyadic_path hG.1.1 huv_ne (not_not.mp hH_not_pf) with
    ⟨p, hp, k, hk2, hplen⟩
  let c : G.Walk u u := Walk.cons huv p.reverse
  have hclen : c.length = 2 ^ k + 1 := by simp [c, Walk.length_reverse, hplen]
  have hge4 : 4 ≤ p.length := by
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    omega
  have hc_is : c.IsCycle := by
    rw [Walk.isCycle_def]
    refine ⟨?_, by simp [c], ?_⟩
    · rw [Walk.isTrail_def]
      simp only [c, Walk.edges_cons, List.nodup_cons]
      refine ⟨?_, hp.reverse.isTrail.edges_nodup⟩
      intro hmem
      have hlen1 : p.reverse.length ≤ 1 := by
        cases hpr : p.reverse with
        | nil => simp
        | @cons _ w _ hvw q =>
          rw [hpr] at hmem
          simp only [Walk.edges_cons, List.mem_cons] at hmem
          rcases hmem with heq | hmem'
          · rw [Sym2.eq_iff] at heq
            rcases heq with ⟨rfl, rfl⟩ | ⟨_, rfl⟩
            · exact False.elim (huv_ne rfl)
            · have hnd : (Walk.cons hvw q).support.Nodup := by
                rw [← hpr]; exact hp.reverse.support_nodup
              cases q with
              | nil => simp
              | @cons _ _ _ _ q' =>
                have hnd' := List.nodup_cons.mp (List.nodup_cons.mp hnd).2
                exact False.elim (hnd'.1 (Walk.end_mem_support q'))
          · have hnd : (Walk.cons hvw q).support.Nodup := by
              rw [← hpr]; exact hp.reverse.support_nodup
            have hv_in : v ∈ q.support := Walk.mem_support_of_mem_edges q hmem' (by simp)
            exact False.elim ((List.nodup_cons.mp hnd).1 hv_in)
      rw [Walk.length_reverse] at hlen1; omega
    · simp only [c, Walk.support_cons, List.tail_cons]
      exact hp.reverse.support_nodup
  exact ⟨c, hc_is, by simp [c], k, hk2, hclen⟩

/-- PILLAR 3.1: Adjacent 2-Vertex-Cut Normal Form on EG2-CORE. -/
theorem minimal_bad2_adjacent_two_vertex_cut_normal_form {V : Type} [Fintype V]
    {G : SimpleGraph V} (hG : MinimalBad2 G) {x y a b : V}
    {Ca Cb : Finset V}
    (hxy : G.Adj x y)
    (hab : a ≠ b) (ha : a ∈ Defects G) (hb : b ∈ Defects G)
    (haCa : a ∈ Ca) (hbCb : b ∈ Cb)
    (hdisj_ab : Disjoint Ca Cb)
    (hCa_no_xy : x ∉ Ca ∧ y ∉ Ca)
    (hCb_no_xy : x ∉ Cb ∧ y ∉ Cb)
    (hcover : Ca ∪ Cb ∪ {x, y} = Finset.univ)
    (hno_cross : ∀ u ∈ Ca, ∀ v ∈ Cb, ¬ G.Adj u v)
    (hxCa : 1 ≤ ((G.neighborFinset x) ∩ Ca).card)
    (hyCa : 1 ≤ ((G.neighborFinset y) ∩ Ca).card)
    (hxCb : 1 ≤ ((G.neighborFinset x) ∩ Cb).card)
    (hyCb : 1 ≤ ((G.neighborFinset y) ∩ Cb).card) :
    ((G.neighborFinset x) ∩ Ca).card = 1 ∧
    ((G.neighborFinset y) ∩ Ca).card = 1 ∧
    ((G.neighborFinset x) ∩ Cb).card = 1 ∧
    ((G.neighborFinset y) ∩ Cb).card = 1 ∧
    G.degree x = 3 ∧ G.degree y = 3 := by
  have hdef_eq : Defects G = {a, b} := by
    have hsub : ({a, b} : Finset V) ⊆ Defects G := by
      intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl <;> assumption
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hab]; exact hG.1.2.2)).symm
  have hside : ∀ (S T : Finset V) (d1 d2 : V),
      d1 ∈ S → d2 ∈ T → Defects G = {d1, d2} →
      Disjoint S T → x ∉ S → y ∉ S → x ∉ T → y ∉ T →
      S ∪ T ∪ {x, y} = Finset.univ →
      (∀ u ∈ S, ∀ v ∈ T, ¬ G.Adj u v) →
      1 ≤ ((G.neighborFinset x) ∩ S).card →
      1 ≤ ((G.neighborFinset y) ∩ S).card →
      ((G.neighborFinset x) ∩ S).card = 1 ∧ ((G.neighborFinset y) ∩ S).card = 1 := by
    intro S T d1 d2 _hd1S hd2T hdef12 hST hxS hyS hxT hyT hcov hnc hxS1 hyS1
    have hTc : Tᶜ = S ∪ {x, y} := by
      ext u
      simp only [Finset.mem_compl, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro huT
        have huU : u ∈ S ∪ T ∪ {x, y} := by rw [hcov]; exact Finset.mem_univ u
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at huU
        tauto
      · rintro (huS | rfl | rfl)
        · exact Finset.disjoint_left.mp hST huS
        · exact hxT
        · exact hyT
    have hx_deg : ((G.neighborFinset x) ∩ Tᶜ).card = ((G.neighborFinset x) ∩ S).card + 1 := by
      rw [hTc]
      have heq : (G.neighborFinset x) ∩ (S ∪ {x, y}) = ((G.neighborFinset x) ∩ S) ∪ {y} := by
        ext u; simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton, mem_nb]
        constructor
        · rintro ⟨hxu, huS | rfl | rfl⟩
          · exact Or.inl ⟨hxu, huS⟩
          · exact False.elim (G.loopless x hxu)
          · exact Or.inr rfl
        · rintro (⟨hxu, huS⟩ | rfl)
          · exact ⟨hxu, Or.inl huS⟩
          · exact ⟨hxy, Or.inr (Or.inr rfl)⟩
      rw [heq, Finset.card_union_of_disjoint]
      · simp
      · rw [Finset.disjoint_singleton_right]
        intro hy_in; exact hyS (Finset.mem_inter.mp hy_in).2
    have hy_deg : ((G.neighborFinset y) ∩ Tᶜ).card = ((G.neighborFinset y) ∩ S).card + 1 := by
      rw [hTc]
      have heq : (G.neighborFinset y) ∩ (S ∪ {x, y}) = ((G.neighborFinset y) ∩ S) ∪ {x} := by
        ext u; simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton, mem_nb]
        constructor
        · rintro ⟨hyu, huS | rfl | rfl⟩
          · exact Or.inl ⟨hyu, huS⟩
          · exact Or.inr rfl
          · exact False.elim (G.loopless y hyu)
        · rintro (⟨hyu, huS⟩ | rfl)
          · exact ⟨hyu, Or.inl huS⟩
          · exact ⟨hxy.symm, Or.inr (Or.inl rfl)⟩
      rw [heq, Finset.card_union_of_disjoint]
      · simp
      · rw [Finset.disjoint_singleton_right]
        intro hx_in; exact hxS (Finset.mem_inter.mp hx_in).2
    have huS_deg : ∀ u ∈ S, ((G.neighborFinset u) ∩ Tᶜ).card = G.degree u := by
      intro u huS
      have hzero : ((G.neighborFinset u) ∩ T).card = 0 := by
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro v hv; rcases Finset.mem_inter.mp hv with ⟨hvN, hvT⟩
        exact hnc u huS v hvT (mem_nb.mp hvN)
      have hsum := degree_compl_eq_sub G T u
      omega
    have hmin_Tc : ∀ u ∈ Tᶜ, 2 ≤ ((G.neighborFinset u) ∩ Tᶜ).card := by
      intro u hu; rw [hTc] at hu
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with huS | rfl | rfl
      · rw [huS_deg u huS]; exact hG.1.2.1 u
      · rw [hx_deg]; omega
      · rw [hy_deg]; omega
    have hnot_ge2 : ¬ (2 ≤ ((G.neighborFinset x) ∩ S).card ∨ 2 ≤ ((G.neighborFinset y) ∩ S).card) := by
      rintro (hx2 | hy2)
      · apply minimal_bad2_no_safe_deletion hG T ⟨d2, hd2T⟩ hmin_Tc
        have hsub : (Tᶜ.filter (fun u => ((G.neighborFinset u) ∩ Tᶜ).card = 2)) ⊆ {d1, y} := by
          intro u hu
          rcases Finset.mem_filter.mp hu with ⟨huTc, hu2⟩
          rw [hTc] at huTc
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at huTc ⊢
          rcases huTc with huS | rfl | rfl
          · rw [huS_deg u huS] at hu2
            have hud : u ∈ Defects G := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu2⟩
            rw [hdef12] at hud
            simp only [Finset.mem_insert, Finset.mem_singleton] at hud
            rcases hud with rfl | rfl
            · exact Or.inl rfl
            · exact False.elim (Finset.disjoint_left.mp hST huS hd2T)
          · rw [hx_deg] at hu2; omega
          · exact Or.inr rfl
        exact le_trans (Finset.card_le_card hsub) Finset.card_le_two
      · apply minimal_bad2_no_safe_deletion hG T ⟨d2, hd2T⟩ hmin_Tc
        have hsub : (Tᶜ.filter (fun u => ((G.neighborFinset u) ∩ Tᶜ).card = 2)) ⊆ {d1, x} := by
          intro u hu
          rcases Finset.mem_filter.mp hu with ⟨huTc, hu2⟩
          rw [hTc] at huTc
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at huTc ⊢
          rcases huTc with huS | rfl | rfl
          · rw [huS_deg u huS] at hu2
            have hud : u ∈ Defects G := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu2⟩
            rw [hdef12] at hud
            simp only [Finset.mem_insert, Finset.mem_singleton] at hud
            rcases hud with rfl | rfl
            · exact Or.inl rfl
            · exact False.elim (Finset.disjoint_left.mp hST huS hd2T)
          · exact Or.inr rfl
          · rw [hy_deg] at hu2; omega
        exact le_trans (Finset.card_le_card hsub) Finset.card_le_two
    omega
  have hA := hside Ca Cb a b haCa hbCb hdef_eq hdisj_ab hCa_no_xy.1 hCa_no_xy.2 hCb_no_xy.1 hCb_no_xy.2
    hcover hno_cross hxCa hyCa
  have hcover_swap : Cb ∪ Ca ∪ {x, y} = Finset.univ := by rw [Finset.union_comm Cb Ca]; exact hcover
  have hdef_swap : Defects G = {b, a} := by rw [hdef_eq, Finset.pair_comm]
  have hB := hside Cb Ca b a hbCb haCa hdef_swap hdisj_ab.symm hCb_no_xy.1 hCb_no_xy.2 hCa_no_xy.1 hCa_no_xy.2
    hcover_swap (fun u hu v hv hadj => hno_cross v hv u hu hadj.symm) hxCb hyCb
  have hdeg_x : G.degree x = 3 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have hsplit : G.neighborFinset x = ((G.neighborFinset x) ∩ Ca) ∪ ((G.neighborFinset x) ∩ Cb) ∪ {y} := by
      ext u; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_singleton, mem_nb]
      constructor
      · intro hxu
        have huU : u ∈ Ca ∪ Cb ∪ {x, y} := by rw [hcover]; exact Finset.mem_univ u
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at huU
        rcases huU with (hu | hu) | rfl | rfl
        · exact Or.inl (Or.inl ⟨hxu, hu⟩)
        · exact Or.inl (Or.inr ⟨hxu, hu⟩)
        · exact False.elim (G.loopless x hxu)
        · exact Or.inr rfl
      · rintro ((⟨hxu, _⟩ | ⟨hxu, _⟩) | rfl)
        · exact hxu
        · exact hxu
        · exact hxy
    have hd1 : Disjoint ((G.neighborFinset x) ∩ Ca) ((G.neighborFinset x) ∩ Cb) :=
      hdisj_ab.mono Finset.inter_subset_right Finset.inter_subset_right
    have hd2 : Disjoint (((G.neighborFinset x) ∩ Ca) ∪ ((G.neighborFinset x) ∩ Cb)) {y} := by
      rw [Finset.disjoint_singleton_right, Finset.mem_union]
      rintro (hy | hy)
      · exact hCa_no_xy.2 (Finset.mem_inter.mp hy).2
      · exact hCb_no_xy.2 (Finset.mem_inter.mp hy).2
    rw [hsplit, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1,
        Finset.card_singleton, hA.1, hB.1]
  have hdeg_y : G.degree y = 3 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have hsplit : G.neighborFinset y = ((G.neighborFinset y) ∩ Ca) ∪ ((G.neighborFinset y) ∩ Cb) ∪ {x} := by
      ext u; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_singleton, mem_nb]
      constructor
      · intro hyu
        have huU : u ∈ Ca ∪ Cb ∪ {x, y} := by rw [hcover]; exact Finset.mem_univ u
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at huU
        rcases huU with (hu | hu) | rfl | rfl
        · exact Or.inl (Or.inl ⟨hyu, hu⟩)
        · exact Or.inl (Or.inr ⟨hyu, hu⟩)
        · exact Or.inr rfl
        · exact False.elim (G.loopless y hyu)
      · rintro ((⟨hyu, _⟩ | ⟨hyu, _⟩) | rfl)
        · exact hyu
        · exact hyu
        · exact hxy.symm
    have hd1 : Disjoint ((G.neighborFinset y) ∩ Ca) ((G.neighborFinset y) ∩ Cb) :=
      hdisj_ab.mono Finset.inter_subset_right Finset.inter_subset_right
    have hd2 : Disjoint (((G.neighborFinset y) ∩ Ca) ∪ ((G.neighborFinset y) ∩ Cb)) {x} := by
      rw [Finset.disjoint_singleton_right, Finset.mem_union]
      rintro (hx | hx)
      · exact hCa_no_xy.1 (Finset.mem_inter.mp hx).2
      · exact hCb_no_xy.1 (Finset.mem_inter.mp hx).2
    rw [hsplit, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1,
        Finset.card_singleton, hA.2, hB.2]
  exact ⟨hA.1, hA.2, hB.1, hB.2, hdeg_x, hdeg_y⟩

/-- PILLAR 3.2: Fermat-Exclusion on any defect-separating 2-edge cut {u1 v1, u2 v2}. -/
theorem minimal_bad2_two_cut_fermat_disjoint {V : Type} [Fintype V]
    {G : SimpleGraph V} (hpf : PowerFree G)
    {A B : Finset V} (hdisj : Disjoint A B)
    {u1 u2 v1 v2 : V}
    (hu12 : u1 ≠ u2) (hv12 : v1 ≠ v2)
    (he1 : G.Adj u1 v1) (he2 : G.Adj u2 v2)
    (pA : G.Walk u1 u2) (hpA : pA.IsPath) (hpA_in : ∀ w ∈ pA.support, w ∈ A)
    (pB : G.Walk v2 v1) (hpB : pB.IsPath) (hpB_in : ∀ w ∈ pB.support, w ∈ B)
    {k : ℕ} (hk : 2 ≤ k) (hA_len : pA.length = 2 ^ k - 1) (hB_len : pB.length = 2 ^ k - 1) :
    False := by
  let c : G.Walk u1 u1 := pA.append (Walk.cons he2 (pB.concat he1.symm))
  have h2k_ge4 : 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hclen : c.length = 2 ^ (k + 1) := by
    simp only [c, Walk.length_append, Walk.length_cons, Walk.length_concat, hA_len, hB_len]
    have : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
    omega
  have hsupp_disj : ∀ w ∈ pA.support, w ∉ pB.support := fun w hwA hwB =>
    Finset.disjoint_left.mp hdisj (hpA_in w hwA) (hpB_in w hwB)
  have hu1_not_B : u1 ∉ pB.support := hsupp_disj u1 (Walk.start_mem_support pA)
  have hcyc : c.IsCycle := by
    rw [Walk.isCycle_def]
    refine ⟨?_, ?_, ?_⟩
    · rw [Walk.isTrail_def]
      simp only [c, Walk.edges_append, Walk.edges_cons, Walk.edges_concat]
      have hA_in_A : ∀ e ∈ pA.edges, ∀ x ∈ e, x ∈ A := fun e he x hx =>
        hpA_in x (Walk.mem_support_of_mem_edges pA he hx)
      have hB_in_B : ∀ e ∈ pB.edges, ∀ x ∈ e, x ∈ B := fun e he x hx =>
        hpB_in x (Walk.mem_support_of_mem_edges pB he hx)
      have hu2A : u2 ∈ A := hpA_in u2 (Walk.end_mem_support pA)
      have hv2B : v2 ∈ B := hpB_in v2 (Walk.start_mem_support pB)
      have hv1B : v1 ∈ B := hpB_in v1 (Walk.end_mem_support pB)
      have hu1A : u1 ∈ A := hpA_in u1 (Walk.start_mem_support pA)
      have hcross_ne : s(u2, v2) ≠ s(v1, u1) := by
        rw [Sym2.eq_iff]; rintro (⟨h1, _⟩ | ⟨_, h2⟩)
        · exact Finset.disjoint_left.mp hdisj hu2A (h1 ▸ hv1B)
        · exact hv12 h2.symm
      rw [List.nodup_append]
      refine ⟨hpA.isTrail.edges_nodup, ?_, ?_⟩
      · rw [List.nodup_cons]
        refine ⟨?_, ?_⟩
        · simp only [List.mem_append, List.mem_singleton, not_or]
          refine ⟨fun hm => Finset.disjoint_left.mp hdisj hu2A (hB_in_B _ hm u2 (by simp)), hcross_ne⟩
        · rw [List.nodup_append]
          refine ⟨hpB.isTrail.edges_nodup, List.nodup_singleton _, ?_⟩
          intro e he e' he' heq
          rw [List.mem_singleton] at he'; subst he'; rw [heq] at he
          exact Finset.disjoint_left.mp hdisj hu1A (hB_in_B _ he u1 (by simp))
      · intro e heA e' heR heq
        subst heq
        simp only [List.mem_cons, List.mem_append, List.mem_singleton] at heR
        rcases heR with rfl | heB | rfl
        · exact Finset.disjoint_left.mp hdisj (hA_in_A _ heA v2 (by simp)) hv2B
        · cases e with
          | h a b =>
            exact Finset.disjoint_left.mp hdisj (hA_in_A _ heA a (by simp)) (hB_in_B _ heB a (by simp))
        · exact Finset.disjoint_left.mp hdisj (hA_in_A _ heA v1 (by simp)) hv1B
    · intro hnil
      have h0 : c.length = 0 := by rw [hnil]; rfl
      have : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
      omega
    · have hsupp : c.support = pA.support ++ pB.support ++ [u1] := by
        simp only [c, Walk.support_append, Walk.support_cons, Walk.support_concat, List.tail_cons,
          List.append_assoc]
      have hA_ne_nil : pA.support ≠ [] := by simp
      have htail : c.support.tail = pA.support.tail ++ pB.support ++ [u1] := by
        rw [hsupp]
        cases hps : pA.support with
        | nil => exact False.elim (hA_ne_nil hps)
        | cons hd tl => simp [List.append_assoc]
      rw [htail, List.nodup_append]
      refine ⟨?_, List.nodup_singleton _, ?_⟩
      · rw [List.nodup_append]
        refine ⟨hpA.support_nodup.tail, hpB.support_nodup, ?_⟩
        intro x hxA hxB
        exact hsupp_disj x (List.mem_of_mem_tail hxA) hxB
      · intro x hxAB y hy heq
        rw [List.mem_singleton] at hy; subst hy; subst heq
        rw [List.mem_append] at hxAB
        rcases hxAB with hxA | hxB
        · have hnd := hpA.support_nodup
          cases hpA with
          | nil => exact hu12 rfl
          | cons _ _ => exact (List.nodup_cons.mp hnd).1 hxA
        · exact hu1_not_B hxB
  exact hpf ⟨u1, c, hcyc, ⟨k + 1, by omega, hclen⟩⟩

/-- PILLAR 4: Tightened Whole-Problem Closure Gate (EGRob3ConnCoreSharp -> Full Erdős #64). -/
def EGRob3ConnCoreSharpTarget : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    MinimalBad2 G →
    (∀ x y : V, x ≠ y → ¬ G.Adj x y → Disjoint (G.neighborFinset x) (G.neighborFinset y) →
      ∃ (p : G.Walk x y), p.IsPath ∧ IsPowerOfTwo p.length) →
    (∀ u v : V, G.Adj u v → 5 ≤ G.degree u + G.degree v →
      Disjoint (G.neighborFinset u) (G.neighborFinset v) →
      ∃ (c : G.Walk u u), c.IsCycle ∧ s(u, v) ∈ c.edges ∧ ∃ k : ℕ, 2 ≤ k ∧ c.length = 2 ^ k + 1) →
    False

/-- Closing EGRob3ConnCoreSharpTarget closes ALL of Erdős Problem #64! -/
theorem eg_rob_3conn_core_sharp_implies_erdos64
    (hTarget : EGRob3ConnCoreSharpTarget) :
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V), MinDegGe G 3 → HasPowerCycle G := by
  intro V _ G hmin3
  by_contra hpf
  have hBadG : Bad2 G := by
    refine ⟨hpf, fun v => le_trans (by norm_num) (hmin3 v), ?_⟩
    have hempty : Defects G = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro v hv
      have h2 := (Finset.mem_filter.mp hv).2
      have h3 := hmin3 v
      omega
    simp [hempty]
  have hex_m : ∃ m : ℕ, ∃ H : SimpleGraph (Fin m), Bad2 H := by
    let e := Fintype.equivFin V
    refine ⟨Fintype.card V,
      { Adj := fun i j => G.Adj (e.symm i) (e.symm j)
        symm := fun _ _ h => G.symm h
        loopless := fun _ h => G.loopless _ h }, ?_⟩
    exact bad2_of_iso { toEquiv := e, map_rel_iff' := by intro a b; simp } hBadG
  let m0 := Nat.find hex_m
  have hm0_spec : ∃ H : SimpleGraph (Fin m0), Bad2 H := Nat.find_spec hex_m
  have hm0_min : ∀ m : ℕ, (∃ H : SimpleGraph (Fin m), Bad2 H) → m0 ≤ m := fun m hm =>
    Nat.find_min' hex_m hm
  have hex_e : ∃ k : ℕ, ∃ H : SimpleGraph (Fin m0), Bad2 H ∧ H.edgeFinset.card = k := by
    rcases hm0_spec with ⟨H, hH⟩
    exact ⟨H.edgeFinset.card, H, hH, rfl⟩
  rcases Nat.find_spec hex_e with ⟨H0, hH0_bad, hH0_card⟩
  have hH0_min : MinimalBad2 H0 := by
    refine ⟨hH0_bad, ?_, ?_⟩
    · intro m H hH
      rw [Fintype.card_fin]
      exact hm0_min m ⟨H, hH⟩
    · intro H hH
      rw [hH0_card]
      exact Nat.find_min' hex_e ⟨H, hH, rfl⟩
  exact hTarget (Fin m0) H0 hH0_min
    (fun x y hxy hnadj hdisj => minimal_bad2_dist3_all_pairs_dyadic_path hH0_min hxy hnadj hdisj)
    (fun u v huv hsum5 hdisj => minimal_bad2_non_triangle_edge_dyadic_plus_one_cycle hH0_min huv hsum5 hdisj)

end E64Wave6Agent1
