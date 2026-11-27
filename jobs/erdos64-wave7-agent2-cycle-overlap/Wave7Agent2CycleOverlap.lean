import Mathlib

open SimpleGraph Classical
open scoped BigOperators

namespace E64Wave7Agent2

/-!
# Erdős Problem #64 — Wave 7 Agent #2
Same-Scale (2^k + 1)-Cycle Overlap Obstructions, Exact C5-Overlap Rigidity & Blockades,
Unconditional All-C5 Refutation of Triangle-Free `MinimalBad2`,
V_{>=4}-Mediated Distance-2 Dyadic Path Forcing, and Girth >= 6 Cubic Density 20/27.
-/

def IsPowerOfTwo (n : ℕ) : Prop :=
  ∃ k : ℕ, 2 ≤ k ∧ n = 2 ^ k

def HasPowerCycle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ IsPowerOfTwo p.length

def PowerFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬ HasPowerCycle G

def MinDegGe {V : Type*} [Fintype V] (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∀ v : V, d ≤ G.degree v

noncomputable def Defects {V : Type*} [Fintype V] (G : SimpleGraph V) : Finset V :=
  Finset.univ.filter (fun v => G.degree v = 2)

noncomputable def V3 {V : Type*} [Fintype V] (G : SimpleGraph V) : Finset V :=
  Finset.univ.filter (fun v => G.degree v = 3)

noncomputable def VGe4 {V : Type*} [Fintype V] (G : SimpleGraph V) : Finset V :=
  Finset.univ.filter (fun v => 4 ≤ G.degree v)

def Bad2 {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  PowerFree G ∧ MinDegGe G 2 ∧ (Defects G).card ≤ 2

def MinimalBad2 {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  Bad2 G ∧
  (∀ (m : ℕ) (H : SimpleGraph (Fin m)), Bad2 H → Fintype.card V ≤ m) ∧
  (∀ (H : SimpleGraph V), Bad2 H → G.edgeFinset.card ≤ H.edgeFinset.card)

def TriangleFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ a b c : V, G.Adj a b → G.Adj b c → ¬ G.Adj a c

lemma mem_nb {V : Type*} [Fintype V] {G : SimpleGraph V} {u v : V} :
    v ∈ G.neighborFinset u ↔ G.Adj u v := by
  rw [SimpleGraph.mem_neighborFinset]

lemma list_tail_map {α β : Type*} (f : α → β) (l : List α) :
    (l.map f).tail = l.tail.map f := by
  cases l <;> rfl

/-! ## Helper lemmas for MinimalBad2 & Safe Deletion -/

lemma bad2_of_iso {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (hG : Bad2 G) : Bad2 H := by
  rcases hG with ⟨hpf, hmin, hdef⟩
  refine ⟨?_, ?_, ?_⟩
  · intro ⟨v, p, hcyc, hpow⟩
    apply hpf
    refine ⟨e.symm v, p.map e.symm.toHom, hcyc.map e.symm.injective, ?_⟩
    simpa using hpow
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
    omega

lemma minimal_bad2_no_smaller {V : Type} [Fintype V] {G : SimpleGraph V}
    (hG : MinimalBad2 G) {W : Type*} [Fintype W] (H : SimpleGraph W)
    (hH : Bad2 H) (hlt : Fintype.card W < Fintype.card V) : False := by
  let e := Fintype.equivFin W
  let H' : SimpleGraph (Fin (Fintype.card W)) := SimpleGraph.comap e.symm H
  let iso : H ≃g H' := {
    toEquiv := e
    map_rel_iff' := by
      intro a b
      simp [H', SimpleGraph.comap]
  }
  have hH' : Bad2 H' := bad2_of_iso iso hH
  have hle : Fintype.card V ≤ Fintype.card W := hG.2.1 (Fintype.card W) H' hH'
  omega

lemma powerFree_induce {V : Type*} {G : SimpleGraph V} (s : Set V) (hG : PowerFree G) :
    PowerFree (G.induce s) := by
  intro ⟨v, p, hcyc, hpow⟩
  apply hG
  refine ⟨v.1, p.map (SimpleGraph.Embedding.induce s).toHom, ?_, ?_⟩
  · exact hcyc.map Subtype.val_injective
  · rw [Walk.length_map]; exact hpow

lemma degree_induce_eq {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Finset V)
    (u : {x : V // x ∈ (S : Set V)}) :
    (G.induce (S : Set V)).degree u = ((G.neighborFinset u.1) ∩ S).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun v _ => v.1)
  · intro v hv
    rw [Finset.mem_inter, mem_nb]
    exact ⟨mem_nb.mp hv, v.2⟩
  · intro _ _ _ _ h
    exact Subtype.ext h
  · intro w hw
    rw [Finset.mem_inter, mem_nb] at hw
    exact ⟨⟨w, hw.2⟩, mem_nb.mpr hw.1, rfl⟩

lemma minimal_bad2_no_safe_deletion {V : Type} [Fintype V] {G : SimpleGraph V}
    (hG : MinimalBad2 G) (K : Finset V) (hKne : K.Nonempty)
    (hmin : ∀ u ∈ Kᶜ, 2 ≤ ((G.neighborFinset u) ∩ Kᶜ).card)
    (hdef : (Kᶜ.filter (fun u => ((G.neighborFinset u) ∩ Kᶜ).card = 2)).card ≤ 2) :
    False := by
  let S : Finset V := Kᶜ
  let H := G.induce (S : Set V)
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
    have hcard_coe : Fintype.card {x : V // x ∈ (S : Set V)} = S.card := Fintype.card_coe S
    rw [hcard_coe]
    have hcardS : S.card = Fintype.card V - K.card := by
      simp [S, Finset.card_compl]
    have hKpos : 0 < K.card := Finset.card_pos.mpr hKne
    have hKle : K.card ≤ Fintype.card V := Finset.card_le_univ K
    omega
  exact minimal_bad2_no_smaller hG H ⟨hH_pf, hH_min, hH_def⟩ hlt

lemma degree_compl_eq_sub {V : Type*} [Fintype V] (G : SimpleGraph V) (K : Finset V) (u : V) :
    ((G.neighborFinset u) ∩ Kᶜ).card + ((G.neighborFinset u) ∩ K).card = G.degree u := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext v
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_compl]
    tauto
  · rw [Finset.disjoint_left]
    intro v hv1 hv2
    exact (Finset.mem_compl.mp (Finset.mem_inter.mp hv1).2) (Finset.mem_inter.mp hv2).2

lemma minimal_bad2_no_safe_deletion_disjoint_defects {V : Type} [Fintype V] {G : SimpleGraph V}
    (hG : MinimalBad2 G) (K : Finset V) (hKne : K.Nonempty)
    (hno_adj_def : ∀ d ∈ Defects G, ∀ k ∈ K, ¬ G.Adj d k)
    (hkeep : ∀ u ∈ Kᶜ, u ∉ Defects G → 3 ≤ ((G.neighborFinset u) ∩ Kᶜ).card) :
    False := by
  apply minimal_bad2_no_safe_deletion hG K hKne
  · intro u hu
    by_cases hd : u ∈ Defects G
    · have hzero : ((G.neighborFinset u) ∩ K).card = 0 := by
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro k hk
        rcases Finset.mem_inter.mp hk with ⟨hkN, hkK⟩
        exact hno_adj_def u hd k hkK (mem_nb.mp hkN)
      have hsum := degree_compl_eq_sub G K u
      have h2 := (Finset.mem_filter.mp hd).2
      omega
    · have h3 := hkeep u hu hd
      omega
  · have hsub : Kᶜ.filter (fun u => ((G.neighborFinset u) ∩ Kᶜ).card = 2) ⊆ Defects G := by
      intro u hu
      rcases Finset.mem_filter.mp hu with ⟨huK, hu2⟩
      by_contra hnd
      have h3 := hkeep u huK hnd
      omega
    exact le_trans (Finset.card_le_card hsub) hG.1.2.2

/-! ## PILLAR 1: General Same-Scale & Mixed-Scale (2^k + 1)-Cycle Overlap Obstructions -/

lemma cycle_of_internally_disjoint_paths {V : Type*} {G : SimpleGraph V} {u v : V}
    (huv : u ≠ v) (p1 p2 : G.Walk u v) (hp1 : p1.IsPath) (hp2 : p2.IsPath)
    (hlen1 : 2 ≤ p1.length) (hlen2 : 2 ≤ p2.length)
    (hdisj : ∀ w, w ∈ p1.support → w ∈ p2.support → w = u ∨ w = v) :
    ∃ (c : G.Walk u u), c.IsCycle ∧ c.length = p1.length + p2.length := by
  let c : G.Walk u u := p1.append p2.reverse
  refine ⟨c, ?_, by simp [c, Walk.length_append, Walk.length_reverse]⟩
  have hsupp_eq : c.support.tail = p1.support.tail ++ p2.reverse.support.tail := by
    have h := Walk.support_append p1 p2.reverse
    rw [show c = p1.append p2.reverse from rfl, h]
    cases hp1s : p1.support with
    | nil => exact False.elim (Walk.support_ne_nil p1 hp1s)
    | cons a l => simp
  have hnodup_tail : c.support.tail.Nodup := by
    rw [hsupp_eq, List.nodup_append]
    refine ⟨hp1.support_nodup.tail, hp2.reverse.support_nodup.tail, ?_⟩
    intro x hx1 y hx2 hxy
    subst hxy
    have hx1' : x ∈ p1.support := List.mem_of_mem_tail hx1
    have hx2' : x ∈ p2.support := by
      have : x ∈ p2.reverse.support := List.mem_of_mem_tail hx2
      rwa [Walk.support_reverse, List.mem_reverse] at this
    have hxu : x ≠ u := by
      intro h; subst h
      have h1 := hp1.support_nodup
      cases hp1w : p1 with
      | nil => exact huv rfl
      | @cons _ b _ hab q =>
        rw [hp1w] at h1 hx1
        simp only [Walk.support_cons, List.tail_cons, List.nodup_cons] at h1 hx1
        exact h1.1 hx1
    have hxv : x ≠ v := by
      intro h; subst h
      have h2 := hp2.reverse.support_nodup
      cases hp2w : p2.reverse with
      | nil => exact huv.symm rfl
      | @cons _ b _ hab q =>
        rw [hp2w] at h2 hx2
        simp only [Walk.support_cons, List.tail_cons, List.nodup_cons] at h2 hx2
        exact h2.1 hx2
    rcases hdisj x hx1' hx2' with rfl | rfl
    · exact hxu rfl
    · exact hxv rfl
  have htrail : c.IsTrail := by
    rw [Walk.isTrail_def]
    simp only [c, Walk.edges_append, List.nodup_append]
    refine ⟨hp1.isTrail.edges_nodup, hp2.reverse.isTrail.edges_nodup, ?_⟩
    intro e he1 e' he2 hee'
    subst hee'
    induction e using Sym2.ind with
    | _ x y =>
      have hx1 : x ∈ p1.support := Walk.mem_support_of_mem_edges p1 he1 (by simp)
      have hy1 : y ∈ p1.support := Walk.mem_support_of_mem_edges p1 he1 (by simp)
      have hx2 : x ∈ p2.support := by
        have := Walk.mem_support_of_mem_edges p2.reverse he2 (by simp)
        rwa [Walk.support_reverse, List.mem_reverse] at this
      have hy2 : y ∈ p2.support := by
        have := Walk.mem_support_of_mem_edges p2.reverse he2 (by simp)
        rwa [Walk.support_reverse, List.mem_reverse] at this
      have hxy_ne : x ≠ y := G.ne_of_adj (Walk.adj_of_mem_edges p1 he1)
      have hpair : (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
        rcases hdisj x hx1 hx2 with rfl | rfl <;> rcases hdisj y hy1 hy2 with rfl | rfl
        · exact False.elim (hxy_ne rfl)
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, rfl⟩
        · exact False.elim (hxy_ne rfl)
      have hsuv : s(u, v) ∈ p1.edges := by
        rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact he1
        · rwa [Sym2.eq_swap] at he1
      have hlen_le1 : p1.length ≤ 1 := by
        cases hp1w : p1 with
        | nil => simp
        | @cons _ w _ huw q =>
          rw [hp1w] at hsuv
          simp only [Walk.edges_cons, List.mem_cons] at hsuv
          rcases hsuv with heq | hmem'
          · rw [Sym2.eq_iff] at heq
            rcases heq with ⟨_, rfl⟩ | ⟨huv', _⟩
            · have hnd : (Walk.cons huw q).support.Nodup := by
                rw [← hp1w]; exact hp1.support_nodup
              cases q with
              | nil => simp
              | @cons _ z _ hvz q' =>
                have hnd' := List.nodup_cons.mp (List.nodup_cons.mp hnd).2
                exact False.elim (hnd'.1 (Walk.end_mem_support q'))
            · exact False.elim (huv huv')
          · have hnd : (Walk.cons huw q).support.Nodup := by
              rw [← hp1w]; exact hp1.support_nodup
            have hu_in : u ∈ q.support := Walk.mem_support_of_mem_edges q hmem' (by simp)
            exact False.elim ((List.nodup_cons.mp hnd).1 hu_in)
      omega
  rw [Walk.isCycle_def]
  refine ⟨htrail, ?_, hnodup_tail⟩
  intro hnil
  have : c.length = 0 := by rw [hnil]; rfl
  simp only [c, Walk.length_append, Walk.length_reverse] at this
  omega

/-- PILLAR 1.1: General Same-Scale (2^k + 1)-Cycle Single-Edge Overlap Obstruction. -/
theorem same_scale_dyadic_plus_one_no_single_edge_overlap {V : Type*} {G : SimpleGraph V}
    (hpf : PowerFree G) {u v : V} (huv : u ≠ v) {k : ℕ} (hk : 2 ≤ k)
    (p1 p2 : G.Walk u v) (hp1 : p1.IsPath) (hp2 : p2.IsPath)
    (hl1 : p1.length = 2 ^ k) (hl2 : p2.length = 2 ^ k)
    (hdisj : ∀ w, w ∈ p1.support → w ∈ p2.support → w = u ∨ w = v) :
    False := by
  have h2k : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  rcases cycle_of_internally_disjoint_paths huv p1 p2 hp1 hp2 (by omega) (by omega) hdisj with
    ⟨c, hc, hclen⟩
  apply hpf
  refine ⟨u, c, hc, k + 1, by omega, ?_⟩
  rw [hclen, hl1, hl2, pow_succ]
  omega

/-- PILLAR 1.2: General Same-Scale (2^k + 1)-Cycle Path-Overlap Spectrum Exclusion. -/
theorem same_scale_dyadic_plus_one_path_overlap_exclusion {V : Type*} {G : SimpleGraph V}
    (hpf : PowerFree G) {u v : V} (huv : u ≠ v) {k l m : ℕ}
    (hm_lo : 2 ≤ m)
    (p1 p2 : G.Walk u v) (hp1 : p1.IsPath) (hp2 : p2.IsPath)
    (hl1 : p1.length + l = 2 ^ k + 1) (hl2 : p2.length + l = 2 ^ k + 1)
    (hdisj : ∀ w, w ∈ p1.support → w ∈ p2.support → w = u ∨ w = v)
    (hl_eq : l + 2 ^ (m - 1) = 2 ^ k + 1) :
    False := by
  have h2m1 : 2 ≤ 2 ^ (m - 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hp1_eq : p1.length = 2 ^ (m - 1) := by omega
  have hp2_eq : p2.length = 2 ^ (m - 1) := by omega
  rcases cycle_of_internally_disjoint_paths huv p1 p2 hp1 hp2 (by omega) (by omega) hdisj with
    ⟨c, hc, hclen⟩
  apply hpf
  refine ⟨u, c, hc, m, hm_lo, ?_⟩
  have hm_eq : m = (m - 1) + 1 := by omega
  rw [hclen, hp1_eq, hp2_eq]
  conv_rhs => rw [hm_eq, pow_succ]
  omega

/-- PILLAR 1.3: General Mixed-Scale (2^{k1}+1, 2^{k2}+1)-Cycle Path-Overlap Exclusion. -/
theorem mixed_scale_dyadic_plus_one_path_overlap_exclusion {V : Type*} {G : SimpleGraph V}
    (hpf : PowerFree G) {u v : V} (huv : u ≠ v) {k1 k2 l : ℕ}
    (hk2 : 2 ≤ k2) (hk12 : k2 < k1)
    (p1 p2 : G.Walk u v) (hp1 : p1.IsPath) (hp2 : p2.IsPath)
    (hl1 : p1.length + l = 2 ^ k1 + 1) (hl2 : p2.length + l = 2 ^ k2 + 1)
    (hdisj : ∀ w, w ∈ p1.support → w ∈ p2.support → w = u ∨ w = v)
    (hl_eq : l = 2 ^ (k2 - 1) + 1) :
    False := by
  have hpow2 : 2 ^ k2 = 2 * 2 ^ (k2 - 1) := by
    have h1 : 2 ^ k2 = 2 ^ (k2 - 1) * 2 := by
      conv_lhs => rw [show k2 = (k2 - 1) + 1 by omega]
      rw [pow_succ]
    omega
  have h2k2_1 : 2 ≤ 2 ^ (k2 - 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (k2 - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpow_lt : 2 ^ k2 < 2 ^ k1 := Nat.pow_lt_pow_right (by norm_num) hk12
  rcases cycle_of_internally_disjoint_paths huv p1 p2 hp1 hp2 (by omega) (by omega) hdisj with
    ⟨c, hc, hclen⟩
  apply hpf
  refine ⟨u, c, hc, k1, by omega, ?_⟩
  omega

/-! ## PILLAR 2: Exact C5-Overlap Rigidity, Blockades & Unconditional All-C5 Refutation -/

def IsC4 {V : Type*} (G : SimpleGraph V) (a b c d : V) : Prop :=
  G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d

def IsC5 {V : Type*} (G : SimpleGraph V) (v0 v1 v2 v3 v4 : V) : Prop :=
  G.Adj v0 v1 ∧ G.Adj v1 v2 ∧ G.Adj v2 v3 ∧ G.Adj v3 v4 ∧ G.Adj v4 v0 ∧
  v0 ≠ v1 ∧ v0 ≠ v2 ∧ v0 ≠ v3 ∧ v0 ≠ v4 ∧
  v1 ≠ v2 ∧ v1 ≠ v3 ∧ v1 ≠ v4 ∧
  v2 ≠ v3 ∧ v2 ≠ v4 ∧
  v3 ≠ v4

def IsC8 {V : Type*} (G : SimpleGraph V) (v0 v1 v2 v3 v4 v5 v6 v7 : V) : Prop :=
  G.Adj v0 v1 ∧ G.Adj v1 v2 ∧ G.Adj v2 v3 ∧ G.Adj v3 v4 ∧
  G.Adj v4 v5 ∧ G.Adj v5 v6 ∧ G.Adj v6 v7 ∧ G.Adj v7 v0 ∧
  ([v0, v1, v2, v3, v4, v5, v6, v7] : List V).Nodup

theorem powerFree_no_c4 {V : Type*} {G : SimpleGraph V} (hpf : PowerFree G)
    {a b c d : V} (h : IsC4 G a b c d) : False := by
  rcases h with ⟨hab, hbc, hcd, hda, h1, h2, h3, h4, h5, h6⟩
  let p : G.Walk a a := Walk.cons hab (Walk.cons hbc (Walk.cons hcd (Walk.cons hda Walk.nil)))
  have hcyc : p.IsCycle := by
    rw [Walk.isCycle_def]
    refine ⟨?_, by simp [p], ?_⟩
    · rw [Walk.isTrail_def]
      simp only [p, Walk.edges_cons, Walk.edges_nil, List.nodup_cons, List.mem_cons,
        List.not_mem_nil, or_false, not_or, not_false_eq_true, Sym2.eq_iff, List.nodup_nil, and_true]
      tauto
    · simp only [p, Walk.support_cons, Walk.support_nil, List.tail_cons, List.nodup_cons,
        List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil, and_true]
      tauto
  exact hpf ⟨a, p, hcyc, 2, le_rfl, rfl⟩

theorem powerFree_no_c8 {V : Type*} {G : SimpleGraph V} (hpf : PowerFree G)
    {v0 v1 v2 v3 v4 v5 v6 v7 : V} (h : IsC8 G v0 v1 v2 v3 v4 v5 v6 v7) : False := by
  rcases h with ⟨h01, h12, h23, h34, h45, h56, h67, h70, hnd⟩
  let p1 : G.Walk v0 v4 := Walk.cons h01 (Walk.cons h12 (Walk.cons h23 (Walk.cons h34 Walk.nil)))
  let p2 : G.Walk v0 v4 :=
    Walk.cons h70.symm (Walk.cons h67.symm (Walk.cons h56.symm (Walk.cons h45.symm Walk.nil)))
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    not_false_eq_true, List.nodup_nil, and_true] at hnd
  rcases hnd with ⟨⟨h01n, h02n, h03n, h04n, h05n, h06n, h07n⟩,
    ⟨h12n, h13n, h14n, h15n, h16n, h17n⟩,
    ⟨h23n, h24n, h25n, h26n, h27n⟩,
    ⟨h34n, h35n, h36n, h37n⟩,
    ⟨h45n, h46n, h47n⟩, ⟨h56n, h57n⟩, h67n⟩
  have hp1 : p1.IsPath := Walk.IsPath.mk' (by
    simp only [p1, Walk.support_cons, Walk.support_nil, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil, and_true]
    tauto)
  have hp2 : p2.IsPath := Walk.IsPath.mk' (by
    simp only [p2, Walk.support_cons, Walk.support_nil, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil, and_true]
    refine ⟨⟨h07n, h06n, h05n, h04n⟩, ⟨fun h => h67n h.symm, fun h => h57n h.symm, fun h => h47n h.symm⟩,
      ⟨fun h => h56n h.symm, fun h => h46n h.symm⟩, fun h => h45n h.symm⟩)
  have hdisj : ∀ w, w ∈ p1.support → w ∈ p2.support → w = v0 ∨ w = v4 := by
    intro w hw1 hw2
    simp only [p1, p2, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hw1 hw2
    rcases hw1 with rfl | rfl | rfl | rfl | rfl <;>
    rcases hw2 with h | h | h | h | h
    all_goals first
      | exact Or.inl rfl | exact Or.inr rfl
      | exact False.elim (h07n h) | exact False.elim (h06n h) | exact False.elim (h05n h)
      | exact False.elim (h04n h) | exact False.elim (h01n h.symm) | exact False.elim (h17n h)
      | exact False.elim (h16n h) | exact False.elim (h15n h) | exact False.elim (h14n h)
      | exact False.elim (h02n h.symm) | exact False.elim (h27n h) | exact False.elim (h26n h)
      | exact False.elim (h25n h) | exact False.elim (h24n h) | exact False.elim (h03n h.symm)
      | exact False.elim (h37n h) | exact False.elim (h36n h) | exact False.elim (h35n h)
      | exact False.elim (h34n h)
  rcases cycle_of_internally_disjoint_paths h04n p1 p2 hp1 hp2 (by simp [p1]) (by simp [p2])
    hdisj with ⟨c, hc, hclen⟩
  exact hpf ⟨v0, c, hc, 3, by norm_num, by simp [hclen, p1, p2]⟩

lemma isC5_no_chord {V : Type*} {G : SimpleGraph V} (hpf : PowerFree G)
    {v0 v1 v2 v3 v4 : V} (h : IsC5 G v0 v1 v2 v3 v4) :
    ¬ G.Adj v0 v2 ∧ ¬ G.Adj v1 v3 ∧ ¬ G.Adj v2 v4 ∧ ¬ G.Adj v3 v0 ∧ ¬ G.Adj v4 v1 := by
  rcases h with ⟨h01, h12, h23, h34, h40, h01n, h02n, h03n, h04n, h12n, h13n, h14n, h23n, h24n, h34n⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h02; exact powerFree_no_c4 hpf ⟨h02, h23, h34, h40, h02n, h03n, h04n, h23n, h24n, h34n⟩
  · intro h13; exact powerFree_no_c4 hpf ⟨h13, h34, h40, h01, h13n, h14n, h01n.symm, h34n, h03n.symm, h04n.symm⟩
  · intro h24; exact powerFree_no_c4 hpf ⟨h24, h40, h01, h12, h24n, h02n.symm, h12n.symm, h04n.symm, h14n.symm, h01n⟩
  · intro h30; exact powerFree_no_c4 hpf ⟨h30, h01, h12, h23, h03n.symm, h13n.symm, h23n.symm, h01n, h02n, h12n⟩
  · intro h41; exact powerFree_no_c4 hpf ⟨h41, h12, h23, h34, h14n.symm, h24n.symm, h34n.symm, h12n, h13n, h23n⟩

lemma powerFree_common_neighbor_unique {V : Type*} {G : SimpleGraph V} (hpf : PowerFree G)
    {x y z1 z2 : V} (hxy : x ≠ y)
    (hx1 : G.Adj x z1) (hy1 : G.Adj y z1) (hx2 : G.Adj x z2) (hy2 : G.Adj y z2) :
    z1 = z2 := by
  by_contra hne
  exact powerFree_no_c4 hpf ⟨hx1, hy1.symm, hy2, hx2.symm,
    G.ne_of_adj hx1, hxy, G.ne_of_adj hx2, G.ne_of_adj hy1.symm, hne, G.ne_of_adj hy2⟩

/-- PILLAR 2.1: Exact C5-Overlap Rigidity in ANY PowerFree graph (no triangle-free needed!). -/
theorem c5_overlap_rigidity {V : Type*} {G : SimpleGraph V} (hpf : PowerFree G)
    {u v a b c a' b' c' : V}
    (h1 : IsC5 G u v a b c) (h2 : IsC5 G u v a' b' c')
    (hdiff : a ≠ a' ∨ c ≠ c') :
    (a = a' ∧ b' ≠ b ∧ b' ≠ c ∧ c' ≠ b ∧ c' ≠ c) ∨
    (c = c' ∧ a' ≠ a ∧ a' ≠ b ∧ b' ≠ a ∧ b' ≠ b) := by
  have hnc1 := isC5_no_chord hpf h1
  rcases h1 with ⟨huv, hva, hab, hbc, hcu, huvn, huan, hubn, hucn, hvan, hvbn, hvcn, habn, hacn, hbcn⟩
  rcases h2 with ⟨_, hva', ha'b', hb'c', hc'u, _, hua'n, hub'n, huc'n, hva'n, hvb'n, hvc'n, ha'b'n, ha'c'n, hb'c'n⟩
  by_cases haa' : a = a'
  · subst haa'
    have hcc' : c ≠ c' := by rcases hdiff with h | h; exact False.elim (h rfl); exact h
    have hbb' : b ≠ b' := by
      intro hb_eq; subst hb_eq
      exact hcc' (powerFree_common_neighbor_unique hpf hubn hcu.symm hbc hc'u.symm hb'c')
    have hb'c : b' ≠ c := by
      intro heq; subst heq; exact hnc1.2.2.1 ha'b'
    have hc'b : c' ≠ b := by
      intro heq; subst heq; exact hnc1.2.2.2.1 hc'u
    exact Or.inl ⟨rfl, hbb'.symm, hb'c, hc'b, hcc'.symm⟩
  · by_cases hcc' : c = c'
    · subst hcc'
      have hbb' : b ≠ b' := by
        intro hb_eq; subst hb_eq
        exact haa' (powerFree_common_neighbor_unique hpf hvbn hva hab.symm hva' ha'b'.symm)
      have ha'b : a' ≠ b := by
        intro heq; subst heq; exact hnc1.2.1 hva'
      have hb'a : b' ≠ a := by
        intro heq; subst heq; exact hnc1.2.2.1 hb'c'.symm
      exact Or.inr ⟨rfl, fun h => haa' h.symm, ha'b, hb'a, hbb'.symm⟩
    · have ha'b : a' ≠ b := by
        intro heq; subst heq; exact hnc1.2.1 hva'
      have ha'c : a' ≠ c := by
        intro heq; subst heq; exact hnc1.2.2.2.2 hva'.symm
      have hc'a : c' ≠ a := by
        intro heq; subst heq; exact hnc1.1 hc'u.symm
      have hc'b : c' ≠ b := by
        intro heq; subst heq; exact hnc1.2.2.2.1 hc'u
      have hb'a : b' ≠ a := by
        intro heq
        have hac' : G.Adj a c' := heq ▸ hb'c'
        exact powerFree_no_c4 hpf ⟨hva, hac', hc'u, huv,
          hvan, hvc'n, huvn.symm, hc'a.symm, huan.symm, huc'n.symm⟩
      have hb'b : b' ≠ b := by
        intro heq
        have ha'b_adj : G.Adj a' b := heq ▸ ha'b'
        exact powerFree_no_c4 hpf ⟨hva, hab, ha'b_adj.symm, hva'.symm,
          hvan, hvbn, hva'n, habn, haa', ha'b.symm⟩
      have hb'c : b' ≠ c := by
        intro heq
        have hca' : G.Adj c a' := (heq ▸ ha'b').symm
        exact powerFree_no_c4 hpf ⟨hcu.symm, hca', hva'.symm, huv.symm,
          hucn, hua'n, huvn, ha'c.symm, hvcn.symm, hva'n.symm⟩
      exact False.elim (powerFree_no_c8 hpf (v0 := u) (v1 := c) (v2 := b) (v3 := a)
        (v4 := v) (v5 := a') (v6 := b') (v7 := c') ⟨hcu.symm, hbc.symm, hab.symm, hva.symm,
          hva', ha'b', hb'c', hc'u, by
          simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
            not_false_eq_true, List.nodup_nil, and_true]
          exact ⟨⟨hucn, hubn, huan, huvn, hua'n, hub'n, huc'n⟩,
            ⟨hbcn.symm, hacn.symm, hvcn.symm, ha'c.symm, hb'c.symm, hcc'⟩,
            ⟨habn.symm, hvbn.symm, ha'b.symm, hb'b.symm, hc'b.symm⟩,
            ⟨hvan.symm, haa', hb'a.symm, hc'a.symm⟩,
            ⟨hva'n, hvb'n, hvc'n⟩, ⟨ha'b'n, ha'c'n⟩, hb'c'n⟩⟩)

/-- PILLAR 2.2: C5-Star Obstruction on any edge u-v of a PowerFree graph. -/
theorem c5_star_obstruction {V : Type*} {G : SimpleGraph V} (hpf : PowerFree G)
    {u v a b c a' b' c' : V}
    (h1 : IsC5 G u v a b c) (h2 : IsC5 G u v a' b' c') :
    a = a' ∨ c = c' := by
  by_contra h
  push Not at h
  rcases c5_overlap_rigidity hpf h1 h2 (Or.inl h.1) with ⟨ha, _⟩ | ⟨hc, _⟩
  · exact h.1 ha
  · exact h.2 hc

lemma isC5_rot {V : Type*} {G : SimpleGraph V} {v0 v1 v2 v3 v4 : V}
    (h : IsC5 G v0 v1 v2 v3 v4) : IsC5 G v1 v2 v3 v4 v0 := by
  rcases h with ⟨h01, h12, h23, h34, h40, h01n, h02n, h03n, h04n, h12n, h13n, h14n, h23n, h24n, h34n⟩
  exact ⟨h12, h23, h34, h40, h01, h12n, h13n, h14n, h01n.symm, h23n, h24n, h02n.symm, h34n, h03n.symm, h04n.symm⟩

lemma isC5_rev {V : Type*} {G : SimpleGraph V} {v0 v1 v2 v3 v4 : V}
    (h : IsC5 G v0 v1 v2 v3 v4) : IsC5 G v0 v4 v3 v2 v1 := by
  rcases h with ⟨h01, h12, h23, h34, h40, h01n, h02n, h03n, h04n, h12n, h13n, h14n, h23n, h24n, h34n⟩
  exact ⟨h40.symm, h34.symm, h23.symm, h12.symm, h01.symm,
    h04n, h03n, h02n, h01n, h34n.symm, h24n.symm, h14n.symm, h23n.symm, h13n.symm, h12n.symm⟩

lemma mem_of_degree_three {V : Type*} [Fintype V] {G : SimpleGraph V} {v x y z w : V}
    (hdeg : G.degree v = 3)
    (hvx : G.Adj v x) (hvy : G.Adj v y) (hvz : G.Adj v z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hvw : G.Adj v w) :
    w = x ∨ w = y ∨ w = z := by
  have hsub : ({x, y, z} : Finset V) ⊆ G.neighborFinset v := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rw [mem_nb]
    rcases hu with rfl | rfl | rfl <;> assumption
  have hcard3 : ({x, y, z} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hyz]
    simp [hxy, hxz]
  have heq : ({x, y, z} : Finset V) = G.neighborFinset v :=
    Finset.eq_of_subset_of_card_le hsub (by rw [SimpleGraph.card_neighborFinset_eq_degree, hdeg, hcard3])
  have hw : w ∈ ({x, y, z} : Finset V) := by
    rw [heq, mem_nb]; exact hvw
  simpa using hw

/-- PILLAR 2.3: Strong Spine-Edge C5-Blockade (NO triangle-free needed, ARBITRARY deg(w)!). -/
theorem theta233_strong_spine_edge_c5_blockade {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hpf : PowerFree G)
    {a u w v2 v3 c1 c2 t p q r : V}
    (hC1 : IsC5 G u a w c1 v2) (hC2 : IsC5 G u a w c2 v3)
    (hv23 : v2 ≠ v3)
    (hdega : G.degree a = 3) (hdegu : G.degree u = 3)
    (hat : G.Adj a t) (htu : t ≠ u) (htw : t ≠ w)
    (hC3 : IsC5 G a t p q r) :
    False := by
  have hrig_ua := c5_overlap_rigidity hpf hC1 hC2 (Or.inr hv23)
  have hdisj_theta : c2 ≠ c1 ∧ c2 ≠ v2 ∧ v3 ≠ c1 ∧ v3 ≠ v2 := by
    rcases hrig_ua with ⟨_, h1, h2, h3, h4⟩ | ⟨heq, _⟩
    · exact ⟨h1, h2, h3, h4⟩
    · exact False.elim (hv23 heq)
  rcases hdisj_theta with ⟨hc21, hc2v2, hv3c1, _⟩
  rcases hC1 with ⟨hua, haw, hwc1, hc1v2, hv2u, huan, huwn, huc1n, huv2n, hawn, hac1n, hav2n, hwc1n, hwv2n, hc1v2n⟩
  rcases hC2 with ⟨_, _, hwc2, hc2v3, hv3u, _, _, huc2n, huv3n, _, hac2n, hav3n, hwc2n, hwv3n, hc2v3n⟩
  have hr_nb : r = u ∨ r = w ∨ r = t :=
    mem_of_degree_three hdega hua.symm haw hat huan.symm htu.symm htw.symm hC3.2.2.2.2.1.symm
  rcases hr_nb with hr | hr | hr
  · subst r
    have hq_nb : q = a ∨ q = v2 ∨ q = v3 :=
      mem_of_degree_three hdegu hua hv2u.symm hv3u.symm hav2n hav3n hv23 hC3.2.2.2.1.symm
    rcases hq_nb with hq | hq | hq
    · subst q; exact hC3.2.2.2.2.2.2.2.1 rfl
    · subst q
      rcases hC3 with ⟨_, htp, hpv2, _, _, hatn, hapn, _, _, htpn, htv2n, _, hpv2n, hpun, _⟩
      have hnc2 := isC5_no_chord hpf ⟨hua, haw, hwc2, hc2v3, hv3u, huan, huwn, huc2n, huv3n, hawn, hac2n, hav3n, hwc2n, hwv3n, hc2v3n⟩
      have htc2 : t ≠ c2 := by intro heq; subst heq; exact hnc2.2.1 hat
      have htv3 : t ≠ v3 := by intro heq; subst heq; exact hnc2.2.2.2.2 hat.symm
      have hpw : p ≠ w := by
        intro heq; subst heq
        exact powerFree_no_c4 hpf ⟨hua, haw, hpv2, hv2u, huan, huwn, huv2n, hawn, hav2n, hwv2n⟩
      have hpc2 : p ≠ c2 := by
        intro heq; subst heq
        exact powerFree_no_c4 hpf ⟨hc1v2, hwc1.symm, hwc2, hpv2.symm, hc1v2n.symm, hwv2n.symm, hc2v2.symm, hwc1n.symm, hc21.symm, hwc2n⟩
      have hpv3 : p ≠ v3 := by
        intro heq; subst heq
        exact powerFree_no_c4 hpf ⟨hat, htp, hv3u, hua, hatn, hav3n, huan.symm, htpn, htu, huv3n.symm⟩
      exact powerFree_no_c8 hpf (v0 := t) (v1 := a) (v2 := w) (v3 := c2)
        (v4 := v3) (v5 := u) (v6 := v2) (v7 := p)
        ⟨hat.symm, haw, hwc2, hc2v3, hv3u, hv2u.symm, hpv2.symm, htp.symm, by
          simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
            not_false_eq_true, List.nodup_nil, and_true]
          exact ⟨⟨hatn.symm, htw, htc2, htv3, htu, htv2n, htpn⟩,
            ⟨hawn, hac2n, hav3n, huan.symm, hav2n, hapn⟩,
            ⟨hwc2n, hwv3n, huwn.symm, hwv2n, hpw.symm⟩,
            ⟨hc2v3n, huc2n.symm, hc2v2, hpc2.symm⟩,
            ⟨huv3n.symm, hv23.symm, hpv3.symm⟩,
            ⟨huv2n, hpun.symm⟩, hpv2n.symm⟩⟩
    · subst q
      rcases hC3 with ⟨_, htp, hpv3, _, _, hatn, hapn, _, _, htpn, htv3n, _, hpv3n, hpun, _⟩
      have hnc1 := isC5_no_chord hpf ⟨hua, haw, hwc1, hc1v2, hv2u, huan, huwn, huc1n, huv2n, hawn, hac1n, hav2n, hwc1n, hwv2n, hc1v2n⟩
      have htc1 : t ≠ c1 := by intro heq; subst heq; exact hnc1.2.1 hat
      have htv2 : t ≠ v2 := by intro heq; subst heq; exact hnc1.2.2.2.2 hat.symm
      have hpw : p ≠ w := by
        intro heq; subst heq
        exact powerFree_no_c4 hpf ⟨hua, haw, hpv3, hv3u, huan, huwn, huv3n, hawn, hav3n, hwv3n⟩
      have hpc1 : p ≠ c1 := by
        intro heq; subst heq
        exact powerFree_no_c4 hpf ⟨hc2v3, hwc2.symm, hwc1, hpv3.symm, hc2v3n.symm, hwv3n.symm, hv3c1, hwc2n.symm, hc21, hwc1n⟩
      have hpv2 : p ≠ v2 := by
        intro heq; subst heq
        exact powerFree_no_c4 hpf ⟨hat, htp, hv2u, hua, hatn, hav2n, huan.symm, htpn, htu, huv2n.symm⟩
      exact powerFree_no_c8 hpf (v0 := t) (v1 := a) (v2 := w) (v3 := c1)
        (v4 := v2) (v5 := u) (v6 := v3) (v7 := p)
        ⟨hat.symm, haw, hwc1, hc1v2, hv2u, hv3u.symm, hpv3.symm, htp.symm, by
          simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
            not_false_eq_true, List.nodup_nil, and_true]
          exact ⟨⟨hatn.symm, htw, htc1, htv2, htu, htv3n, htpn⟩,
            ⟨hawn, hac1n, hav2n, huan.symm, hav3n, hapn⟩,
            ⟨hwc1n, hwv2n, huwn.symm, hwv3n, hpw.symm⟩,
            ⟨hc1v2n, huc1n.symm, hv3c1.symm, hpc1.symm⟩,
            ⟨huv2n.symm, hv23, hpv2.symm⟩,
            ⟨huv3n, hpun.symm⟩, hpv3n.symm⟩⟩
  · subst r
    have hC1_aw : IsC5 G a w c1 v2 u := isC5_rot ⟨hua, haw, hwc1, hc1v2, hv2u, huan, huwn, huc1n, huv2n, hawn, hac1n, hav2n, hwc1n, hwv2n, hc1v2n⟩
    have hC2_aw : IsC5 G a w c2 v3 u := isC5_rot ⟨hua, haw, hwc2, hc2v3, hv3u, huan, huwn, huc2n, huv3n, hawn, hac2n, hav3n, hwc2n, hwv3n, hc2v3n⟩
    have hC3_aw : IsC5 G a w q p t := isC5_rev hC3
    have hq1 : c1 = q := by
      rcases c5_star_obstruction hpf hC1_aw hC3_aw with h | h
      · exact h
      · exact False.elim (htu h.symm)
    have hq2 : c2 = q := by
      rcases c5_star_obstruction hpf hC2_aw hC3_aw with h | h
      · exact h
      · exact False.elim (htu h.symm)
    exact hc21 (hq2.trans hq1.symm)
  · subst r; exact hC3.2.2.2.2.2.2.2.2.2.2.2.1 rfl

/-- PILLAR 2.4: Rim-Edge C5-Blockade (triangle-free PowerFree, ARBITRARY deg(a) and deg(c1)!). -/
theorem theta233_rim_edge_c5_blockade {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hpf : PowerFree G) (htri : TriangleFree G)
    {a u w v2 v3 c1 c2 z p q r : V}
    (hC1 : IsC5 G u a w c1 v2) (hC2 : IsC5 G u a w c2 v3)
    (hv23 : v2 ≠ v3)
    (hdegu : G.degree u = 3) (hdegw : G.degree w = 3) (hdegv2 : G.degree v2 = 3)
    (hv2z : G.Adj v2 z) (hzu : z ≠ u) (hzc1 : z ≠ c1)
    (hC3 : IsC5 G v2 z p q r) :
    False := by
  have hrig_ua := c5_overlap_rigidity hpf hC1 hC2 (Or.inr hv23)
  have hdisj_theta : c2 ≠ c1 ∧ c2 ≠ v2 ∧ v3 ≠ c1 ∧ v3 ≠ v2 := by
    rcases hrig_ua with ⟨_, h1, h2, h3, h4⟩ | ⟨heq, _⟩
    · exact ⟨h1, h2, h3, h4⟩
    · exact False.elim (hv23 heq)
  rcases hdisj_theta with ⟨hc21, hc2v2, hv3c1, _⟩
  rcases hC1 with ⟨hua, haw, hwc1, hc1v2, hv2u, huan, huwn, huc1n, huv2n, hawn, hac1n, hav2n, hwc1n, hwv2n, hc1v2n⟩
  rcases hC2 with ⟨_, _, hwc2, hc2v3, hv3u, _, _, huc2n, huv3n, _, hac2n, hav3n, hwc2n, hwv3n, hc2v3n⟩
  have hr_nb : r = u ∨ r = c1 ∨ r = z :=
    mem_of_degree_three hdegv2 hv2u hc1v2.symm hv2z huc1n hzu.symm hzc1.symm hC3.2.2.2.2.1.symm
  rcases hr_nb with hr | hr | hr
  · subst r
    have hq_nb : q = a ∨ q = v2 ∨ q = v3 :=
      mem_of_degree_three hdegu hua hv2u.symm hv3u.symm hav2n hav3n hv23 hC3.2.2.2.1.symm
    rcases hq_nb with hq | hq | hq
    · subst q
      rcases hC3 with ⟨_, hzp, hpa, _, _, hv2zn, hv2pn, _, _, hzpn, hzan, _, hpan, hpun, _⟩
      have hzw : z ≠ w := by
        intro heq; subst heq
        exact powerFree_no_c4 hpf ⟨hv2u, hua, haw, hv2z.symm, huv2n.symm, hav2n.symm, hwv2n.symm, huan, huwn, hawn⟩
      have hzc2 : z ≠ c2 := by
        intro heq; subst heq
        exact powerFree_no_c4 hpf ⟨hv2z, hwc2.symm, hwc1, hc1v2, hc2v2.symm, hwv2n.symm, hc1v2n.symm, hwc2n.symm, hc21, hwc1n⟩
      have hzv3 : z ≠ v3 := by
        intro heq; subst heq
        exact htri u v2 v3 hv2u.symm hv2z hv3u.symm
      have hpw : p ≠ w := by
        intro heq; subst heq
        exact powerFree_no_c4 hpf ⟨hv2z, hzp, hwc1, hc1v2, hv2zn, hwv2n.symm, hc1v2n.symm, hzw, hzc1, hwc1n⟩
      have hpc2 : p ≠ c2 := by
        intro heq; subst heq
        exact htri a w c2 haw hwc2 hpa.symm
      have hpv3 : p ≠ v3 := by
        intro heq; subst heq
        exact htri a u v3 hua.symm hv3u.symm hpa.symm
      exact powerFree_no_c8 hpf (v0 := z) (v1 := p) (v2 := a) (v3 := w)
        (v4 := c2) (v5 := v3) (v6 := u) (v7 := v2)
        ⟨hzp, hpa, haw, hwc2, hc2v3, hv3u, hv2u.symm, hv2z, by
          simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
            not_false_eq_true, List.nodup_nil, and_true]
          exact ⟨⟨hzpn, hzan, hzw, hzc2, hzv3, hzu, hv2zn.symm⟩,
            ⟨hpan, hpw, hpc2, hpv3, hpun, hv2pn.symm⟩,
            ⟨hawn, hac2n, hav3n, huan.symm, hav2n⟩,
            ⟨hwc2n, hwv3n, huwn.symm, hwv2n⟩,
            ⟨hc2v3n, huc2n.symm, hc2v2⟩,
            ⟨huv3n.symm, hv23.symm⟩, huv2n⟩⟩
    · subst q; exact hC3.2.2.2.2.2.2.2.1 rfl
    · subst q
      have hC1_uv2 : IsC5 G u v2 c1 w a := isC5_rev ⟨hua, haw, hwc1, hc1v2, hv2u, huan, huwn, huc1n, huv2n, hawn, hac1n, hav2n, hwc1n, hwv2n, hc1v2n⟩
      have hC3_uv2 : IsC5 G u v2 z p v3 := isC5_rot (isC5_rot (isC5_rot (isC5_rot hC3)))
      rcases c5_star_obstruction hpf hC1_uv2 hC3_uv2 with h | h
      · exact hzc1 h.symm
      · exact hav3n h
  · subst r
    have hC1_c1v2 : IsC5 G c1 v2 u a w :=
      isC5_rot (isC5_rot (isC5_rot ⟨hua, haw, hwc1, hc1v2, hv2u, huan, huwn, huc1n, huv2n, hawn, hac1n, hav2n, hwc1n, hwv2n, hc1v2n⟩))
    have hC3_c1v2 : IsC5 G c1 v2 z p q := isC5_rot (isC5_rot (isC5_rot (isC5_rot hC3)))
    have hqw : q = w := by
      rcases c5_star_obstruction hpf hC1_c1v2 hC3_c1v2 with h | h
      · exact False.elim (hzu h.symm)
      · exact h.symm
    subst q
    have hp_nb : p = a ∨ p = c1 ∨ p = c2 :=
      mem_of_degree_three hdegw haw.symm hwc1 hwc2 hac1n hac2n hc21.symm hC3.2.2.1.symm
    rcases hp_nb with hp | hp | hp
    · subst p
      exact powerFree_no_c4 hpf ⟨hv2z, hC3.2.1, hua.symm, hv2u.symm,
        hC3.2.2.2.2.2.1, hav2n.symm, huv2n.symm, hC3.2.2.2.2.2.2.2.2.2.1, hzu, huan.symm⟩
    · subst p; exact hC3.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl
    · subst p
      rcases hC3 with ⟨_, hzc2, _, _, _, hv2zn, _, _, _, hzc2n, _, _, _, _, _⟩
      have hzv3 : z ≠ v3 := by
        intro heq; subst heq; exact htri u v2 v3 hv2u.symm hv2z hv3u.symm
      have hza : z ≠ a := by
        intro heq; subst heq; exact htri u a v2 hua hv2z.symm hv2u.symm
      have hzw : z ≠ w := by
        intro heq; subst heq
        exact powerFree_no_c4 hpf ⟨hv2u, hua, haw, hv2z.symm, huv2n.symm, hav2n.symm, hwv2n.symm, huan, huwn, hawn⟩
      exact powerFree_no_c8 hpf (v0 := z) (v1 := c2) (v2 := v3) (v3 := u)
        (v4 := a) (v5 := w) (v6 := c1) (v7 := v2)
        ⟨hzc2, hc2v3, hv3u, hua, haw, hwc1, hc1v2, hv2z, by
          simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
            not_false_eq_true, List.nodup_nil, and_true]
          exact ⟨⟨hzc2n, hzv3, hzu, hza, hzw, hzc1, hv2zn.symm⟩,
            ⟨hc2v3n, huc2n.symm, hac2n.symm, hwc2n.symm, hc21, hc2v2⟩,
            ⟨huv3n.symm, hav3n.symm, hwv3n.symm, hv3c1, hv23.symm⟩,
            ⟨huan, huwn, huc1n, huv2n⟩,
            ⟨hawn, hac1n, hav2n⟩,
            ⟨hwc1n, hwv2n⟩, hc1v2n⟩⟩
  · subst r; exact hC3.2.2.2.2.2.2.2.2.2.2.2.1 rfl

lemma degree_three_all_c5_forces_theta233 {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hpf : PowerFree G) {u : V} (hdegu : G.degree u = 3)
    (hc5 : ∀ v, G.Adj u v → ∃ x y z, IsC5 G u v x y z) :
    ∃ a w v2 v3 c1 c2 : V,
      IsC5 G u a w c1 v2 ∧ IsC5 G u a w c2 v3 ∧ v2 ≠ v3 := by
  have hcard : (G.neighborFinset u).card = 3 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, hdegu]
  rcases Finset.card_eq_three.mp hcard with ⟨n1, n2, n3, h12, h13, h23, hNu⟩
  have hn1 : G.Adj u n1 := mem_nb.mp (by rw [hNu]; simp)
  have hn2 : G.Adj u n2 := mem_nb.mp (by rw [hNu]; simp)
  have hn3 : G.Adj u n3 := mem_nb.mp (by rw [hNu]; simp)
  rcases hc5 n1 hn1 with ⟨x1, y1, z1, hC1⟩
  have hz1_mem : z1 ∈ ({n1, n2, n3} : Finset V) := by
    rw [← hNu, mem_nb]; exact hC1.2.2.2.2.1.symm
  have hz1_ne1 : z1 ≠ n1 := hC1.2.2.2.2.2.2.2.2.2.2.2.1.symm
  have pick_third : ∀ (p q r : V), G.Adj u p → G.Adj u q → G.Adj u r →
      p ≠ q → p ≠ r → q ≠ r →
      (∀ v, G.Adj u v → v = p ∨ v = q ∨ v = r) →
      (∃ x y, IsC5 G u p x y q) →
      ∃ a w v2 v3 c1 c2 : V, IsC5 G u a w c1 v2 ∧ IsC5 G u a w c2 v3 ∧ v2 ≠ v3 := by
    intro p q r hp hq hr hpq hpr hqr hall ⟨x, y, hCp⟩
    rcases hc5 r hr with ⟨xr, yr, zr, hCr⟩
    have hzr : zr = p ∨ zr = q ∨ zr = r := hall zr hCr.2.2.2.2.1.symm
    rcases hzr with hzr | hzr | hzr
    · subst zr
      have hCr' : IsC5 G u p yr xr r := isC5_rev hCr
      rcases c5_overlap_rigidity hpf hCp hCr' (Or.inr hqr) with ⟨hx, _⟩ | ⟨heq, _⟩
      · subst yr; exact ⟨p, x, q, r, y, xr, hCp, hCr', hqr⟩
      · exact False.elim (hqr heq)
    · subst zr
      have hCp' : IsC5 G u q y x p := isC5_rev hCp
      have hCr' : IsC5 G u q yr xr r := isC5_rev hCr
      rcases c5_overlap_rigidity hpf hCp' hCr' (Or.inr hpr) with ⟨hy, _⟩ | ⟨heq, _⟩
      · subst yr; exact ⟨q, y, p, r, x, xr, hCp', hCr', hpr⟩
      · exact False.elim (hpr heq)
    · subst zr; exact False.elim (hCr.2.2.2.2.2.2.2.2.2.2.2.1 rfl)
  have hall : ∀ v, G.Adj u v → v = n1 ∨ v = n2 ∨ v = n3 := fun v hv =>
    mem_of_degree_three hdegu hn1 hn2 hn3 h12 h13 h23 hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz1_mem
  rcases hz1_mem with hz | hz | hz
  · exact False.elim (hz1_ne1 hz)
  · subst z1; exact pick_third n1 n2 n3 hn1 hn2 hn3 h12 h13 h23 hall ⟨x1, y1, hC1⟩
  · subst z1; exact pick_third n1 n3 n2 hn1 hn3 hn2 h13 h12 h23.symm
      (fun v hv => by rcases hall v hv with h | h | h <;> tauto) ⟨x1, y1, hC1⟩

/-- PILLAR 2.5: Unconditional Cubic All-C5 Refutation. -/
theorem cubic_all_c5_refutation {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hpf : PowerFree G) {u : V} (hdegu : G.degree u = 3)
    (hnb3 : ∀ v, G.Adj u v → G.degree v = 3)
    (hc5_u : ∀ v, G.Adj u v → ∃ x y z, IsC5 G u v x y z)
    (hc5_nb : ∀ v, G.Adj u v → ∀ t, G.Adj v t → ∃ x y z, IsC5 G v t x y z) :
    False := by
  rcases degree_three_all_c5_forces_theta233 hpf hdegu hc5_u with
    ⟨a, w, v2, v3, c1, c2, hC1, hC2, hv23⟩
  have hua : G.Adj u a := hC1.1
  have hdega : G.degree a = 3 := hnb3 a hua
  have hcard2 : ({u, w} : Finset V).card = 2 := Finset.card_pair hC1.2.2.2.2.2.2.1
  have hlt : ({u, w} : Finset V).card < (G.neighborFinset a).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, hdega, hcard2]; omega
  rcases Finset.exists_mem_notMem_of_card_lt_card hlt with ⟨t, htN, htnot⟩
  have hat : G.Adj a t := mem_nb.mp htN
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at htnot
  rcases hc5_nb a hua t hat with ⟨p, q, r, hC3⟩
  exact theta233_strong_spine_edge_c5_blockade hpf hC1 hC2 hv23 hdega hdegu hat htnot.1 htnot.2 hC3

/-- PILLAR 2.6: Unconditional All-C5 Refutation of Triangle-Free MinimalBad2 / EGRob3ConnCoreSharpTarget. -/
theorem trifree_minimal_bad2_all_c5_refutation {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hpf : PowerFree G) (htri : TriangleFree G)
    (hmin : MinDegGe G 2)
    (hhigh_ind : ∀ x ∈ VGe4 G, ∀ y ∈ VGe4 G, ¬ G.Adj x y)
    (hdef_nb_v3 : ∀ d ∈ Defects G, ∀ x, G.Adj d x → x ∈ V3 G)
    (hv3_ne : (V3 G).Nonempty)
    (hall_c5 : ∀ x ∈ V3 G, ∀ y, G.Adj x y → ∃ p q r, IsC5 G x y p q r) :
    False := by
  rcases hv3_ne with ⟨u, hu3⟩
  have hdegu : G.degree u = 3 := (Finset.mem_filter.mp hu3).2
  rcases degree_three_all_c5_forces_theta233 hpf hdegu (hall_c5 u hu3) with
    ⟨a, w, v2, v3, c1, c2, hC1, hC2, hv23⟩
  have haw : G.Adj a w := hC1.2.1
  have ha_ne3 : G.degree a ≠ 3 := by
    intro hdega
    have ha3 : a ∈ V3 G := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdega⟩
    have hlt : ({u, w} : Finset V).card < (G.neighborFinset a).card := by
      rw [Finset.card_pair hC1.2.2.2.2.2.2.1, SimpleGraph.card_neighborFinset_eq_degree, hdega]; omega
    rcases Finset.exists_mem_notMem_of_card_lt_card hlt with ⟨t, htN, htnot⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at htnot
    rcases hall_c5 a ha3 t (mem_nb.mp htN) with ⟨p, q, r, hC3⟩
    exact theta233_strong_spine_edge_c5_blockade hpf hC1 hC2 hv23 hdega hdegu
      (mem_nb.mp htN) htnot.1 htnot.2 hC3
  have hrig := c5_overlap_rigidity hpf hC1 hC2 (Or.inr hv23)
  have hdisj : c2 ≠ c1 ∧ c2 ≠ v2 ∧ v3 ≠ c1 ∧ v3 ≠ v2 := by
    rcases hrig with ⟨_, h1, h2, h3, h4⟩ | ⟨heq, _⟩
    · exact ⟨h1, h2, h3, h4⟩
    · exact False.elim (hv23 heq)
  have hw_deg3 : G.degree w = 3 := by
    have ha2 := hmin a
    by_cases ha_def : a ∈ Defects G
    · exact (Finset.mem_filter.mp (hdef_nb_v3 a ha_def w haw)).2
    · have ha4 : a ∈ VGe4 G := by
        have hne2 : G.degree a ≠ 2 := fun h => ha_def (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
      have hw_not4 : w ∉ VGe4 G := fun hw4 => hhigh_ind a ha4 w hw4 haw
      have hw_not2 : w ∉ Defects G := fun hw2 => by
        have := (Finset.mem_filter.mp (hdef_nb_v3 w hw2 a haw.symm)).2
        have := (Finset.mem_filter.mp ha4).2; omega
      have hw2 := hmin w
      simp only [VGe4, Defects, Finset.mem_filter, Finset.mem_univ, true_and] at hw_not4 hw_not2
      omega
  have hv2_not3 : v2 ∉ V3 G := by
    intro hv23'
    have hdegv2 : G.degree v2 = 3 := (Finset.mem_filter.mp hv23').2
    have hlt : ({u, c1} : Finset V).card < (G.neighborFinset v2).card := by
      rw [Finset.card_pair hC1.2.2.2.2.2.2.2.1, SimpleGraph.card_neighborFinset_eq_degree, hdegv2]; omega
    rcases Finset.exists_mem_notMem_of_card_lt_card hlt with ⟨z, hzN, hznot⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hznot
    rcases hall_c5 v2 hv23' z (mem_nb.mp hzN) with ⟨p, q, r, hC3⟩
    exact theta233_rim_edge_c5_blockade hpf htri hC1 hC2 hv23 hdegu hw_deg3 hdegv2
      (mem_nb.mp hzN) hznot.1 hznot.2 hC3
  have hc1_not3 : c1 ∉ V3 G := by
    intro hc13
    have hdegc1 : G.degree c1 = 3 := (Finset.mem_filter.mp hc13).2
    have hC1' : IsC5 G w a u v2 c1 := isC5_rot (isC5_rot (isC5_rot (isC5_rev hC1)))
    have hC2' : IsC5 G w a u v3 c2 := isC5_rot (isC5_rot (isC5_rot (isC5_rev hC2)))
    have hlt : ({w, v2} : Finset V).card < (G.neighborFinset c1).card := by
      rw [Finset.card_pair hC1'.2.2.2.2.2.2.2.1, SimpleGraph.card_neighborFinset_eq_degree, hdegc1]; omega
    rcases Finset.exists_mem_notMem_of_card_lt_card hlt with ⟨z, hzN, hznot⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hznot
    rcases hall_c5 c1 hc13 z (mem_nb.mp hzN) with ⟨p, q, r, hC3⟩
    exact theta233_rim_edge_c5_blockade hpf htri hC1' hC2' hdisj.1.symm hw_deg3 hdegu hdegc1
      (mem_nb.mp hzN) hznot.1 hznot.2 hC3
  have not_def_of_adj_not_v3 : ∀ {x y : V}, G.Adj x y → y ∉ V3 G → x ∉ Defects G :=
    fun hxy hy3 hxd => hy3 (hdef_nb_v3 _ hxd _ hxy)
  have hv2_4 : v2 ∈ VGe4 G := by
    have hnd := not_def_of_adj_not_v3 hC1.2.2.2.1.symm hc1_not3
    have h2 := hmin v2
    simp only [V3, Defects, VGe4, Finset.mem_filter, Finset.mem_univ, true_and] at hv2_not3 hnd ⊢
    omega
  have hc1_4 : c1 ∈ VGe4 G := by
    have hnd := not_def_of_adj_not_v3 hC1.2.2.2.1 hv2_not3
    have h2 := hmin c1
    simp only [V3, Defects, VGe4, Finset.mem_filter, Finset.mem_univ, true_and] at hc1_not3 hnd ⊢
    omega
  exact hhigh_ind c1 hc1_4 v2 hv2_4 hC1.2.2.2.1

/-! ## PILLAR 3: Universal V_{>=4}-Mediated Distance-2 Dyadic Path Forcing (`MinimalBad2`) -/

def identGraph {V : Type*} (G : SimpleGraph V) (x y : V) :
    SimpleGraph {w : V // w ≠ y} where
  Adj u v := u ≠ v ∧ (G.Adj u.1 v.1 ∨ (u.1 = x ∧ G.Adj y v.1) ∨ (v.1 = x ∧ G.Adj u.1 y))
  symm := ⟨by
    intro u v ⟨hne, h⟩
    rcases h with h | ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact ⟨hne.symm, Or.inl h.symm⟩
    · exact ⟨hne.symm, Or.inr (Or.inr ⟨hx, hy.symm⟩)⟩
    · exact ⟨hne.symm, Or.inr (Or.inl ⟨hx, hy.symm⟩)⟩⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

lemma identGraph_walk_lift {V : Type*} {G : SimpleGraph V} {x y : V} (hxy : x ≠ y)
    {u v : {w : V // w ≠ y}} (p : (identGraph G x y).Walk u v)
    (havoid : ⟨x, hxy⟩ ∉ p.support) :
    ∃ q : G.Walk u.1 v.1,
      q.length = p.length ∧
      q.support = p.support.map Subtype.val ∧
      q.edges = p.edges.map (Sym2.map Subtype.val) := by
  induction p with
  | nil => exact ⟨Walk.nil, rfl, rfl, rfl⟩
  | @cons a b c hab p ih =>
    have ha_ne : a ≠ ⟨x, hxy⟩ := fun h => havoid (by simp [h])
    have hb_ne : b ≠ ⟨x, hxy⟩ := fun h => havoid (List.mem_cons_of_mem _ (h ▸ Walk.start_mem_support p))
    have havoid' : ⟨x, hxy⟩ ∉ p.support := fun h => havoid (List.mem_cons_of_mem _ h)
    rcases ih havoid' with ⟨q, hlen, hsupp, hedges⟩
    have hadjG : G.Adj a.1 b.1 := by
      rcases hab.2 with h | ⟨hax, _⟩ | ⟨hbx, _⟩
      · exact h
      · exact False.elim (ha_ne (Subtype.ext hax))
      · exact False.elim (hb_ne (Subtype.ext hbx))
    exact ⟨Walk.cons hadjG q, by simp [hlen], by simp [hsupp], by simp [hedges]⟩

lemma identGraph_cycle_lifts_to_dyadic_path {V : Type*} {G : SimpleGraph V}
    (hpf : PowerFree G) {x y : V} (hxy : x ≠ y)
    (hcyc_ex : HasPowerCycle (identGraph G x y)) :
    ∃ (p : G.Walk x y), p.IsPath ∧ IsPowerOfTwo p.length := by
  rcases hcyc_ex with ⟨v0, c0, hc0, hpow⟩
  let z : {w : V // w ≠ y} := ⟨x, hxy⟩
  by_cases hz : z ∈ c0.support
  · let c := c0.rotate z hz
    have hc : c.IsCycle := hc0.rotate hz
    have hclen : IsPowerOfTwo c.length := by simpa [c, Walk.length_rotate] using hpow
    cases c with
    | nil => exact False.elim (hc.ne_nil rfl)
    | @cons _ b _ hzb rest =>
      have hrest_nodup : rest.support.Nodup := by have := hc.support_nodup; simpa using this
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
                    have hend : b.1 ∈ (Walk.cons h1 q').support.tail := by
                      simpa using Walk.end_mem_support q'
                    rw [← heq] at hend
                    exact False.elim (hnd.1 hend)
                omega
              simp only [cyc, Walk.edges_cons, Walk.edges_concat, List.concat_eq_append,
                List.nodup_cons, List.mem_append, List.mem_singleton, not_or, List.nodup_append]
              refine ⟨⟨fun hm => hw_not_edges _ hm (by simp), ?_⟩, hq_edges_nodup, by simp, ?_⟩
              · rw [Sym2.eq_iff]; rintro (⟨_, h2⟩ | ⟨_, h2⟩)
                · exact G.ne_of_adj hwd h2.symm
                · exact hdb_ne h2
              · intro e he e' he' heq
                rw [List.mem_singleton] at he'; subst he'; subst heq
                exact hw_not_edges _ he (by simp)
            · simp only [cyc, Walk.support_cons, Walk.support_concat, List.concat_eq_append,
                List.tail_cons]
              rw [List.nodup_append]
              refine ⟨hq_nodup, by simp, ?_⟩
              intro a ha a' ha' heq
              rw [List.mem_singleton] at ha'; subst ha'; subst heq; exact hw_not ha
          exact hpf ⟨w, cyc, hcyc_is, hcyc_len ▸ hclen⟩
        rcases hd_adj with hxd | hyd <;> rcases hb_adj with hxb | hyb
        · exact False.elim (mk_cyc hx_not_q hxd hxb)
        · let path : G.Walk x y := Walk.cons hxd (q.concat hyb.symm)
          refine ⟨path, Walk.IsPath.mk' ?_, ?_⟩
          · simp only [path, Walk.support_cons, Walk.support_concat, List.concat_eq_append,
              List.nodup_cons, List.mem_append, List.mem_singleton, not_or]
            refine ⟨⟨hx_not_q, hxy⟩, ?_⟩
            rw [List.nodup_append]
            refine ⟨hq_nodup, by simp, ?_⟩
            intro a ha a' ha' heq
            rw [List.mem_singleton] at ha'; subst ha'; subst heq; exact hy_not_q ha
          · have : path.length = (Walk.cons hzb rest).length := by
              simp [path, Walk.length_concat, hqlen_eq]
            rw [this]; exact hclen
        · let path_rev : G.Walk y x := Walk.cons hyd (q.concat hxb.symm)
          have hpr_nodup : path_rev.support.Nodup := by
            simp only [path_rev, Walk.support_cons, Walk.support_concat, List.concat_eq_append,
              List.nodup_cons, List.mem_append, List.mem_singleton, not_or]
            refine ⟨⟨hy_not_q, hxy.symm⟩, ?_⟩
            rw [List.nodup_append]
            refine ⟨hq_nodup, by simp, ?_⟩
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
      · rw [hqsupp, list_tail_map]
        exact hc0.support_nodup.map Subtype.val_injective
    exact False.elim (hpf ⟨v0.1, q, hq_cyc, hqlen ▸ hpow⟩)

lemma identGraph_degree_other_no_common {V : Type*} [Fintype V] (G : SimpleGraph V)
    {x y : V} (hxy : x ≠ y) (u : {w : V // w ≠ y}) (hux : u.1 ≠ x)
    (hnot_comm : ¬ (G.Adj u.1 x ∧ G.Adj u.1 y)) :
    (identGraph G x y).degree u = G.degree u.1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun v _ => if v.1 = x ∧ G.Adj u.1 y then y else v.1)
  · intro v hv
    rw [mem_nb] at hv ⊢
    split_ifs with h
    · exact h.2
    · rcases hv.2 with hadj | ⟨hux', _⟩ | ⟨hvx, huy⟩
      · exact hadj
      · exact False.elim (hux hux')
      · exact False.elim (h ⟨hvx, huy⟩)
  · intro v1 hv1 v2 hv2 heq
    rw [mem_nb] at hv1 hv2
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
      · rw [mem_nb]
        exact ⟨fun h => hux (congrArg Subtype.val h), Or.inr (Or.inr ⟨rfl, hw⟩)⟩
      · simp [hw]
    · refine ⟨⟨w, hwy⟩, ?_, ?_⟩
      · rw [mem_nb]
        exact ⟨fun h => G.ne_of_adj hw (congrArg Subtype.val h), Or.inl hw⟩
      · split_ifs with h
        · exact False.elim (hnot_comm ⟨h.1 ▸ hw, h.2⟩)
        · rfl

lemma identGraph_degree_other_common {V : Type*} [Fintype V] (G : SimpleGraph V)
    {x y : V} (hxy : x ≠ y) (u : {w : V // w ≠ y}) (hux : u.1 ≠ x)
    (hcomm : G.Adj u.1 x ∧ G.Adj u.1 y) :
    (identGraph G x y).degree u + 1 = G.degree u.1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  have hy_in : y ∈ G.neighborFinset u.1 := mem_nb.mpr hcomm.2
  rw [← Finset.card_erase_add_one hy_in]
  congr 1
  apply Finset.card_bij (fun v _ => v.1)
  · intro v hv
    rw [mem_nb] at hv
    refine Finset.mem_erase.mpr ⟨v.2, mem_nb.mpr ?_⟩
    rcases hv.2 with hadj | ⟨hux', _⟩ | ⟨hvx, _⟩
    · exact hadj
    · exact False.elim (hux hux')
    · rw [hvx]; exact hcomm.1
  · intro _ _ _ _ h; exact Subtype.ext h
  · intro w hw
    rcases Finset.mem_erase.mp hw with ⟨hwy, hwN⟩
    have hadj : G.Adj u.1 w := mem_nb.mp hwN
    refine ⟨⟨w, hwy⟩, ?_, rfl⟩
    rw [mem_nb]
    exact ⟨fun h => G.ne_of_adj hadj (congrArg Subtype.val h), Or.inl hadj⟩

lemma identGraph_degree_merged {V : Type*} [Fintype V] (G : SimpleGraph V)
    {x y : V} (hxy : x ≠ y) :
    (identGraph G x y).degree ⟨x, hxy⟩ =
      (((G.neighborFinset x) ∪ (G.neighborFinset y)) \ {x, y}).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun v _ => v.1)
  · intro v hv
    rw [mem_nb] at hv
    simp only [Finset.mem_sdiff, Finset.mem_union, mem_nb,
      Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨?_, fun h => hv.1 (Subtype.ext h.symm), v.2⟩
    rcases hv.2 with h | ⟨_, hy⟩ | ⟨hvx, _⟩
    · exact Or.inl h
    · exact Or.inr hy
    · exact False.elim (hv.1 (Subtype.ext hvx.symm))
  · intro _ _ _ _ h; exact Subtype.ext h
  · intro w hw
    simp only [Finset.mem_sdiff, Finset.mem_union, mem_nb,
      Finset.mem_insert, Finset.mem_singleton, not_or] at hw
    refine ⟨⟨w, hw.2.2⟩, ?_, rfl⟩
    rw [mem_nb]
    refine ⟨fun h => hw.2.1 (congrArg Subtype.val h).symm, ?_⟩
    rcases hw.1 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨rfl, h⟩)

lemma dyadic_path_avoids_common_nb_edges {V : Type*} {G : SimpleGraph V}
    (hpf : PowerFree G) {u v w : V}
    (huw : G.Adj u w) (hwv : G.Adj w v)
    (p : G.Walk u v) (hp : p.IsPath) (hpow : IsPowerOfTwo p.length) :
    s(u, w) ∉ p.edges ∧ s(w, v) ∉ p.edges := by
  rcases hpow with ⟨k, hk, hplen⟩
  have hge4 : 4 ≤ p.length := by
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  constructor
  · intro hmem
    cases p with
    | nil => simp at hmem
    | @cons _ b _ hub q =>
      simp only [Walk.edges_cons, List.mem_cons] at hmem
      rcases hmem with heq | hmem'
      · rw [Sym2.eq_iff] at heq
        rcases heq with ⟨_, rfl⟩ | ⟨hbu, _⟩
        · have hq_path : q.IsPath := hp.of_cons
          have hq_len : q.length + 1 = 2 ^ k := by simp only [Walk.length_cons] at hplen; omega
          have hq_ge3 : 3 ≤ q.length := by omega
          let cyc : G.Walk w w := Walk.cons hwv q.reverse
          have hcyc_is : cyc.IsCycle := by
            rw [Walk.isCycle_def]
            refine ⟨?_, by simp [cyc], ?_⟩
            · rw [Walk.isTrail_def]
              simp only [cyc, Walk.edges_cons, List.nodup_cons]
              refine ⟨?_, hq_path.reverse.isTrail.edges_nodup⟩
              intro hmemq
              have hlen1 : q.reverse.length ≤ 1 := by
                cases hqr : q.reverse with
                | nil => simp
                | @cons _ x _ hvx r =>
                  rw [hqr] at hmemq
                  simp only [Walk.edges_cons, List.mem_cons] at hmemq
                  rcases hmemq with heq2 | hmem2
                  · rw [Sym2.eq_iff] at heq2
                    rcases heq2 with ⟨hvw, _⟩ | ⟨_, rfl⟩
                    · exact False.elim (G.ne_of_adj hwv hvw.symm)
                    · have hnd : (Walk.cons hvx r).support.Nodup := by
                        rw [← hqr]; exact hq_path.reverse.support_nodup
                      cases r with
                      | nil => simp
                      | @cons _ y _ hwy r' =>
                        have hnd' := List.nodup_cons.mp (List.nodup_cons.mp hnd).2
                        exact False.elim (hnd'.1 (Walk.end_mem_support r'))
                  · have hnd : (Walk.cons hvx r).support.Nodup := by
                      rw [← hqr]; exact hq_path.reverse.support_nodup
                    have hv_in : v ∈ r.support := Walk.mem_support_of_mem_edges r hmem2 (by simp)
                    exact False.elim ((List.nodup_cons.mp hnd).1 hv_in)
              rw [Walk.length_reverse] at hlen1; omega
            · simp only [cyc, Walk.support_cons, List.tail_cons]
              exact hq_path.reverse.support_nodup
          exact hpf ⟨w, cyc, hcyc_is, k, hk, by simp [cyc, Walk.length_reverse, hq_len]⟩
        · exact G.ne_of_adj hub hbu.symm
      · have hnd := List.nodup_cons.mp hp.support_nodup
        exact hnd.1 (Walk.mem_support_of_mem_edges q hmem' (by simp))
  · intro hmem
    have hmem_rev : s(v, w) ∈ p.reverse.edges := by
      rw [Walk.edges_reverse, List.mem_reverse, Sym2.eq_swap]; exact hmem
    have hpr_len : p.reverse.length = 2 ^ k := by rw [Walk.length_reverse, hplen]
    cases hpr : p.reverse with
    | nil => rw [hpr] at hmem_rev; simp at hmem_rev
    | @cons _ b _ hvb q =>
      rw [hpr] at hmem_rev hpr_len
      simp only [Walk.edges_cons, List.mem_cons] at hmem_rev
      have hp_rev : (Walk.cons hvb q).IsPath := by rw [← hpr]; exact hp.reverse
      rcases hmem_rev with heq | hmem'
      · rw [Sym2.eq_iff] at heq
        rcases heq with ⟨_, rfl⟩ | ⟨hbv, _⟩
        · have hq_path : q.IsPath := hp_rev.of_cons
          have hq_len : q.length + 1 = 2 ^ k := by simp only [Walk.length_cons] at hpr_len; omega
          have hq_ge3 : 3 ≤ q.length := by omega
          let cyc : G.Walk w w := Walk.cons huw.symm q.reverse
          have hcyc_is : cyc.IsCycle := by
            rw [Walk.isCycle_def]
            refine ⟨?_, by simp [cyc], ?_⟩
            · rw [Walk.isTrail_def]
              simp only [cyc, Walk.edges_cons, List.nodup_cons]
              refine ⟨?_, hq_path.reverse.isTrail.edges_nodup⟩
              intro hmemq
              have hlen1 : q.reverse.length ≤ 1 := by
                cases hqr : q.reverse with
                | nil => simp
                | @cons _ x _ hux r =>
                  rw [hqr] at hmemq
                  simp only [Walk.edges_cons, List.mem_cons] at hmemq
                  rcases hmemq with heq2 | hmem2
                  · rw [Sym2.eq_iff] at heq2
                    rcases heq2 with ⟨hwu, _⟩ | ⟨_, rfl⟩
                    · exact False.elim (G.ne_of_adj huw hwu)
                    · have hnd : (Walk.cons hux r).support.Nodup := by
                        rw [← hqr]; exact hq_path.reverse.support_nodup
                      cases r with
                      | nil => simp
                      | @cons _ y _ hwy r' =>
                        have hnd' := List.nodup_cons.mp (List.nodup_cons.mp hnd).2
                        exact False.elim (hnd'.1 (Walk.end_mem_support r'))
                  · have hnd : (Walk.cons hux r).support.Nodup := by
                      rw [← hqr]; exact hq_path.reverse.support_nodup
                    have hu_in : u ∈ r.support := Walk.mem_support_of_mem_edges r hmem2 (by simp)
                    exact False.elim ((List.nodup_cons.mp hnd).1 hu_in)
              rw [Walk.length_reverse] at hlen1; omega
            · simp only [cyc, Walk.support_cons, List.tail_cons]
              exact hq_path.reverse.support_nodup
          exact hpf ⟨w, cyc, hcyc_is, k, hk, by simp [cyc, Walk.length_reverse, hq_len]⟩
        · exact G.ne_of_adj hvb hbv.symm
      · have hnd := List.nodup_cons.mp hp_rev.support_nodup
        exact hnd.1 (Walk.mem_support_of_mem_edges q hmem' (by simp))

/-- PILLAR 3.1: Universal V_{>=4}-Mediated Distance-2 Dyadic Path Forcing on MinimalBad2. -/
theorem minimal_bad2_vge4_dist2_dyadic_path {V : Type} [Fintype V]
    {G : SimpleGraph V} (hG : MinimalBad2 G) {w u v : V}
    (hw4 : w ∈ VGe4 G) (hwu : G.Adj w u) (hwv : G.Adj w v)
    (huv : u ≠ v) (hnadj : ¬ G.Adj u v) :
    ∃ (p : G.Walk u v), p.IsPath ∧ IsPowerOfTwo p.length ∧
      s(u, w) ∉ p.edges ∧ s(w, v) ∉ p.edges := by
  let H := identGraph G u v
  have hH_not_pf : ¬ PowerFree H := by
    intro hpf
    have hcomm_uniq : ∀ z : V, G.Adj z u → G.Adj z v → z = w := fun z hzu hzv =>
      powerFree_common_neighbor_unique hG.1.1 huv hzu.symm hzv.symm hwu.symm hwv.symm
    have hdeg_z : 3 ≤ H.degree ⟨u, huv⟩ := by
      rw [identGraph_degree_merged]
      have hdisj_uv : Disjoint (G.neighborFinset u ∪ G.neighborFinset v) ({u, v} : Finset V) := by
        rw [Finset.disjoint_left]
        intro x hx huv_mem
        simp only [Finset.mem_union, mem_nb] at hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at huv_mem
        rcases huv_mem with rfl | rfl
        · rcases hx with h | h; exact G.loopless u h; exact hnadj h.symm
        · rcases hx with h | h; exact hnadj h; exact G.loopless v h
      rw [Finset.sdiff_eq_self_of_disjoint hdisj_uv]
      have hinter : (G.neighborFinset u) ∩ (G.neighborFinset v) = {w} := by
        ext z
        simp only [Finset.mem_inter, mem_nb, Finset.mem_singleton]
        exact ⟨fun ⟨h1, h2⟩ => hcomm_uniq z h1.symm h2.symm, fun h => h ▸ ⟨hwu.symm, hwv.symm⟩⟩
      have hunion := Finset.card_union_add_card_inter (G.neighborFinset u) (G.neighborFinset v)
      rw [hinter, Finset.card_singleton, SimpleGraph.card_neighborFinset_eq_degree,
          SimpleGraph.card_neighborFinset_eq_degree] at hunion
      have hu2 := hG.1.2.1 u
      have hv2 := hG.1.2.1 v
      omega
    have hdeg_other : ∀ x : {z : V // z ≠ v}, x.1 ≠ u →
        (x.1 = w → 3 ≤ H.degree x) ∧ (x.1 ≠ w → H.degree x = G.degree x.1) := by
      intro x hxu
      constructor
      · intro hxw
        have hcomm : G.Adj x.1 u ∧ G.Adj x.1 v := by rw [hxw]; exact ⟨hwu, hwv⟩
        have h := identGraph_degree_other_common G huv x hxu hcomm
        have hw_ge4 : 4 ≤ G.degree w := (Finset.mem_filter.mp hw4).2
        rw [hxw] at h; omega
      · intro hxw
        apply identGraph_degree_other_no_common G huv x hxu
        rintro ⟨h1, h2⟩; exact hxw (hcomm_uniq x.1 h1 h2)
    have hH_min : MinDegGe H 2 := by
      intro x
      by_cases hxu : x.1 = u
      · have heq : x = ⟨u, huv⟩ := Subtype.ext hxu; rw [heq]; omega
      · by_cases hxw : x.1 = w
        · have := (hdeg_other x hxu).1 hxw; omega
        · rw [(hdeg_other x hxu).2 hxw]; exact hG.1.2.1 x.1
    have hH_def : (Defects H).card ≤ 2 := by
      have hcard_le : (Defects H).card ≤ (Defects G).card := by
        apply Finset.card_le_card_of_injOn Subtype.val
        · intro x hx
          simp only [Defects, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          by_cases hxu : x.1 = u
          · have heq : x = ⟨u, huv⟩ := Subtype.ext hxu; rw [heq] at hx; omega
          · by_cases hxw : x.1 = w
            · have := (hdeg_other x hxu).1 hxw; omega
            · rw [← (hdeg_other x hxu).2 hxw]; exact hx
        · intro _ _ _ _ h; exact Subtype.ext h
      exact le_trans hcard_le hG.1.2.2
    have hlt : Fintype.card {z : V // z ≠ v} < Fintype.card V := by
      rw [Fintype.card_subtype_compl, Fintype.card_unique]
      have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨u⟩
      omega
    exact minimal_bad2_no_smaller hG H ⟨hpf, hH_min, hH_def⟩ hlt
  have hcyc : HasPowerCycle H := not_not.mp hH_not_pf
  rcases identGraph_cycle_lifts_to_dyadic_path hG.1.1 huv hcyc with ⟨p, hp, hpow⟩
  have havoid := dyadic_path_avoids_common_nb_edges hG.1.1 hwu.symm hwv p hp hpow
  exact ⟨p, hp, hpow, havoid.1, havoid.2⟩

/-! ## PILLAR 4: Sharpened Safe-Deletion & Girth >= 6 Cubic Density 20/27 -/

/-- PILLAR 4.1: In ANY MinimalBad2 graph (even WITH triangles!), every V3 vertex has <= 2 neighbors in S2. -/
theorem minimal_bad2_s0_at_most_two_s2 {V : Type} [Fintype V]
    {G : SimpleGraph V} (hG : MinimalBad2 G)
    {u x y z : V}
    (hu3 : u ∈ V3 G) (hx3 : x ∈ V3 G) (hy3 : y ∈ V3 G) (hz3 : z ∈ V3 G)
    (hx2 : ((G.neighborFinset x) ∩ VGe4 G).card = 2)
    (hy2 : ((G.neighborFinset y) ∩ VGe4 G).card = 2)
    (hz2 : ((G.neighborFinset z) ∩ VGe4 G).card = 2)
    (hux : G.Adj u x) (huy : G.Adj u y) (huz : G.Adj u z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    False := by
  let K : Finset V := {u, x, y, z}
  have hu_nd : u ∉ Defects G := fun h => by
    have := (Finset.mem_filter.mp hu3).2; have := (Finset.mem_filter.mp h).2; omega
  have hx_nd : x ∉ Defects G := fun h => by
    have := (Finset.mem_filter.mp hx3).2; have := (Finset.mem_filter.mp h).2; omega
  have hy_nd : y ∉ Defects G := fun h => by
    have := (Finset.mem_filter.mp hy3).2; have := (Finset.mem_filter.mp h).2; omega
  have hz_nd : z ∉ Defects G := fun h => by
    have := (Finset.mem_filter.mp hz3).2; have := (Finset.mem_filter.mp h).2; omega
  have hu_n4 : u ∉ VGe4 G := fun h => by
    have := (Finset.mem_filter.mp hu3).2; have := (Finset.mem_filter.mp h).2; omega
  have s2_other_ge4 : ∀ {s : V}, s ∈ V3 G → ((G.neighborFinset s) ∩ VGe4 G).card = 2 →
      G.Adj u s → ∀ w, G.Adj s w → w ≠ u → w ∈ VGe4 G := by
    intro s hs3 hs2 hus w hsw hwu
    have hsub : (G.neighborFinset s) ∩ VGe4 G ⊆ (G.neighborFinset s).erase u := by
      intro t ht; rcases Finset.mem_inter.mp ht with ⟨htN, ht4⟩
      exact Finset.mem_erase.mpr ⟨fun h => hu_n4 (h ▸ ht4), htN⟩
    have hcard2 : ((G.neighborFinset s).erase u).card = 2 := by
      rw [Finset.card_erase_of_mem (mem_nb.mpr hus.symm),
          SimpleGraph.card_neighborFinset_eq_degree, (Finset.mem_filter.mp hs3).2]
    have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
    have hw_in : w ∈ (G.neighborFinset s).erase u :=
      Finset.mem_erase.mpr ⟨hwu, mem_nb.mpr hsw⟩
    rw [← heq] at hw_in; exact (Finset.mem_inter.mp hw_in).2
  have hu_all : ∀ w, G.Adj u w → w ∈ K := fun w huw => by
    rcases mem_of_degree_three (Finset.mem_filter.mp hu3).2 hux huy huz hxy hxz hyz huw with
      rfl | rfl | rfl <;> simp [K]
  apply minimal_bad2_no_safe_deletion_disjoint_defects hG K ⟨u, by simp [K]⟩
  · intro d hd k hk hadj
    have hd_n4 : d ∉ VGe4 G := fun h => by
      have := (Finset.mem_filter.mp hd).2; have := (Finset.mem_filter.mp h).2; omega
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · have := hu_all d hadj.symm
      simp only [K, Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl | rfl | rfl <;> first | exact hu_nd hd | exact hx_nd hd | exact hy_nd hd | exact hz_nd hd
    · exact hd_n4 (s2_other_ge4 hx3 hx2 hux d hadj.symm (fun h => hu_nd (h ▸ hd)))
    · exact hd_n4 (s2_other_ge4 hy3 hy2 huy d hadj.symm (fun h => hu_nd (h ▸ hd)))
    · exact hd_n4 (s2_other_ge4 hz3 hz2 huz d hadj.symm (fun h => hu_nd (h ▸ hd)))
  · intro w hwK hwd
    have hw_notK : w ∉ K := Finset.mem_compl.mp hwK
    have hsum := degree_compl_eq_sub G K w
    have hw_ge3 : 3 ≤ G.degree w := by
      have h2 := hG.1.2.1 w
      have hne2 : G.degree w ≠ 2 := fun h => hwd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      omega
    have hwK_le1 : ((G.neighborFinset w) ∩ K).card ≤ 1 := by
      by_contra hgt; push Not at hgt
      rcases Finset.one_lt_card.mp hgt with ⟨k1, hk1, k2, hk2, hk12⟩
      rcases Finset.mem_inter.mp hk1 with ⟨hk1N, hk1K⟩
      rcases Finset.mem_inter.mp hk2 with ⟨hk2N, hk2K⟩
      have h1 : G.Adj w k1 := mem_nb.mp hk1N
      have h2 : G.Adj w k2 := mem_nb.mp hk2N
      have hwu_ne : w ≠ u := fun h => hw_notK (by simp [K, h])
      simp only [K, Finset.mem_insert, Finset.mem_singleton] at hk1K hk2K
      rcases hk1K with rfl | rfl | rfl | rfl
      · exact hw_notK (hu_all w h1.symm)
      all_goals rcases hk2K with rfl | rfl | rfl | rfl
      · exact hw_notK (hu_all w h2.symm)
      · exact hk12 rfl
      · exact hwu_ne (powerFree_common_neighbor_unique hG.1.1 hxy h1.symm h2.symm hux.symm huy.symm)
      · exact hwu_ne (powerFree_common_neighbor_unique hG.1.1 hxz h1.symm h2.symm hux.symm huz.symm)
      · exact hw_notK (hu_all w h2.symm)
      · exact hwu_ne (powerFree_common_neighbor_unique hG.1.1 hxy.symm h1.symm h2.symm huy.symm hux.symm)
      · exact hk12 rfl
      · exact hwu_ne (powerFree_common_neighbor_unique hG.1.1 hyz h1.symm h2.symm huy.symm huz.symm)
      · exact hw_notK (hu_all w h2.symm)
      · exact hwu_ne (powerFree_common_neighbor_unique hG.1.1 hxz.symm h1.symm h2.symm huz.symm hux.symm)
      · exact hwu_ne (powerFree_common_neighbor_unique hG.1.1 hyz.symm h1.symm h2.symm huz.symm huy.symm)
      · exact hk12 rfl
    by_cases h0 : ((G.neighborFinset w) ∩ K).card = 0
    · omega
    · have hne0 : ((G.neighborFinset w) ∩ K).Nonempty := Finset.card_pos.mp (by omega)
      rcases hne0 with ⟨k, hk⟩
      rcases Finset.mem_inter.mp hk with ⟨hkN, hkK⟩
      have hwk : G.Adj w k := mem_nb.mp hkN
      have hwu_ne : w ≠ u := fun h => hw_notK (by simp [K, h])
      have hw4 : w ∈ VGe4 G := by
        simp only [K, Finset.mem_insert, Finset.mem_singleton] at hkK
        rcases hkK with rfl | rfl | rfl | rfl
        · exact False.elim (hw_notK (hu_all w hwk.symm))
        · exact s2_other_ge4 hx3 hx2 hux w hwk.symm hwu_ne
        · exact s2_other_ge4 hy3 hy2 huy w hwk.symm hwu_ne
        · exact s2_other_ge4 hz3 hz2 huz w hwk.symm hwu_ne
      have hdeg4 : 4 ≤ G.degree w := (Finset.mem_filter.mp hw4).2
      omega

/-- PILLAR 4.2: Adjacent S1b vertices in triangle-free MinimalBad2 force a common degree-4
    neighbor of their S2-neighbors (forming a C5 = u-v-y-w-x-u). -/
theorem minimal_bad2_trifree_adjacent_s1b_forces_c5_deg4 {V : Type} [Fintype V]
    {G : SimpleGraph V} (hG : MinimalBad2 G) (htri : TriangleFree G)
    {u v x y : V}
    (hu3 : u ∈ V3 G) (hv3 : v ∈ V3 G) (hx3 : x ∈ V3 G) (hy3 : y ∈ V3 G)
    (hu1 : ((G.neighborFinset u) ∩ VGe4 G).card = 1)
    (hv1 : ((G.neighborFinset v) ∩ VGe4 G).card = 1)
    (hx2 : ((G.neighborFinset x) ∩ VGe4 G).card = 2)
    (hy2 : ((G.neighborFinset y) ∩ VGe4 G).card = 2)
    (huv : G.Adj u v) (hux : G.Adj u x) (hvy : G.Adj v y) :
    ∃ w : V, G.Adj w x ∧ G.Adj w y ∧ G.degree w = 4 ∧ IsC5 G u v y w x := by
  have huv_ne : u ≠ v := G.ne_of_adj huv
  have hux_ne : u ≠ x := G.ne_of_adj hux
  have hvy_ne : v ≠ y := G.ne_of_adj hvy
  have hx_ne_v : x ≠ v := by intro h; subst h; omega
  have hy_ne_u : y ≠ u := by intro h; subst h; omega
  have hxy_ne : x ≠ y := by intro h; subst h; exact htri u v x huv hvy.symm hux
  let K : Finset V := {u, v, x, y}
  have hu_nd : u ∉ Defects G := fun h => by
    have := (Finset.mem_filter.mp hu3).2; have := (Finset.mem_filter.mp h).2; omega
  have hv_nd : v ∉ Defects G := fun h => by
    have := (Finset.mem_filter.mp hv3).2; have := (Finset.mem_filter.mp h).2; omega
  have hx_nd : x ∉ Defects G := fun h => by
    have := (Finset.mem_filter.mp hx3).2; have := (Finset.mem_filter.mp h).2; omega
  have hy_nd : y ∉ Defects G := fun h => by
    have := (Finset.mem_filter.mp hy3).2; have := (Finset.mem_filter.mp h).2; omega
  have hu_n4 : u ∉ VGe4 G := fun h => by
    have := (Finset.mem_filter.mp hu3).2; have := (Finset.mem_filter.mp h).2; omega
  have hv_n4 : v ∉ VGe4 G := fun h => by
    have := (Finset.mem_filter.mp hv3).2; have := (Finset.mem_filter.mp h).2; omega
  have hx_n4 : x ∉ VGe4 G := fun h => by
    have := (Finset.mem_filter.mp hx3).2; have := (Finset.mem_filter.mp h).2; omega
  have hy_n4 : y ∉ VGe4 G := fun h => by
    have := (Finset.mem_filter.mp hy3).2; have := (Finset.mem_filter.mp h).2; omega
  have s1_other_ge4 : ∀ {a b c : V}, a ∈ V3 G → ((G.neighborFinset a) ∩ VGe4 G).card = 1 →
      G.Adj a b → G.Adj a c → b ≠ c → b ∉ VGe4 G → c ∉ VGe4 G →
      ∀ w, G.Adj a w → w ≠ b → w ≠ c → w ∈ VGe4 G := by
    intro a b c ha3 ha1 hab hac hbc hb4 hc4 w haw hwb hwc
    have hsub : (G.neighborFinset a) ∩ VGe4 G ⊆ ((G.neighborFinset a).erase b).erase c := by
      intro t ht; rcases Finset.mem_inter.mp ht with ⟨htN, ht4⟩
      exact Finset.mem_erase.mpr ⟨fun h => hc4 (h ▸ ht4), Finset.mem_erase.mpr ⟨fun h => hb4 (h ▸ ht4), htN⟩⟩
    have hcard1 : (((G.neighborFinset a).erase b).erase c).card = 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hbc.symm, mem_nb.mpr hac⟩),
          Finset.card_erase_of_mem (mem_nb.mpr hab),
          SimpleGraph.card_neighborFinset_eq_degree, (Finset.mem_filter.mp ha3).2]
    have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
    have hw_in : w ∈ ((G.neighborFinset a).erase b).erase c :=
      Finset.mem_erase.mpr ⟨hwc, Finset.mem_erase.mpr ⟨hwb, mem_nb.mpr haw⟩⟩
    rw [← heq] at hw_in; exact (Finset.mem_inter.mp hw_in).2
  have s2_other_ge4 : ∀ {s a : V}, s ∈ V3 G → ((G.neighborFinset s) ∩ VGe4 G).card = 2 →
      G.Adj s a → a ∉ VGe4 G → ∀ w, G.Adj s w → w ≠ a → w ∈ VGe4 G := by
    intro s a hs3 hs2 hsa ha4 w hsw hwa
    have hsub : (G.neighborFinset s) ∩ VGe4 G ⊆ (G.neighborFinset s).erase a := by
      intro t ht; rcases Finset.mem_inter.mp ht with ⟨htN, ht4⟩
      exact Finset.mem_erase.mpr ⟨fun h => ha4 (h ▸ ht4), htN⟩
    have hcard2 : ((G.neighborFinset s).erase a).card = 2 := by
      rw [Finset.card_erase_of_mem (mem_nb.mpr hsa),
          SimpleGraph.card_neighborFinset_eq_degree, (Finset.mem_filter.mp hs3).2]
    have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
    have hw_in : w ∈ (G.neighborFinset s).erase a :=
      Finset.mem_erase.mpr ⟨hwa, mem_nb.mpr hsw⟩
    rw [← heq] at hw_in; exact (Finset.mem_inter.mp hw_in).2
  by_contra hnone
  push Not at hnone
  apply minimal_bad2_no_safe_deletion_disjoint_defects hG K ⟨u, by simp [K]⟩
  · intro d hd k hk hadj
    have hd_n4 : d ∉ VGe4 G := fun h => by
      have := (Finset.mem_filter.mp hd).2; have := (Finset.mem_filter.mp h).2; omega
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact hd_n4 (s1_other_ge4 hu3 hu1 huv hux hx_ne_v.symm hv_n4 hx_n4 d hadj.symm
        (fun h => hv_nd (h ▸ hd)) (fun h => hx_nd (h ▸ hd)))
    · exact hd_n4 (s1_other_ge4 hv3 hv1 huv.symm hvy hy_ne_u.symm hu_n4 hy_n4 d hadj.symm
        (fun h => hu_nd (h ▸ hd)) (fun h => hy_nd (h ▸ hd)))
    · exact hd_n4 (s2_other_ge4 hx3 hx2 hux.symm hu_n4 d hadj.symm (fun h => hu_nd (h ▸ hd)))
    · exact hd_n4 (s2_other_ge4 hy3 hy2 hvy.symm hv_n4 d hadj.symm (fun h => hv_nd (h ▸ hd)))
  · intro w hwK hwd
    have hw_notK : w ∉ K := Finset.mem_compl.mp hwK
    have hsum := degree_compl_eq_sub G K w
    have hw_ge3 : 3 ≤ G.degree w := by
      have h2 := hG.1.2.1 w
      have hne2 : G.degree w ≠ 2 := fun h => hwd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      omega
    have hwu_ne : w ≠ u := fun h => hw_notK (by simp [K, h])
    have hwv_ne : w ≠ v := fun h => hw_notK (by simp [K, h])
    have hwx_ne : w ≠ x := fun h => hw_notK (by simp [K, h])
    have hwy_ne : w ≠ y := fun h => hw_notK (by simp [K, h])
    by_cases h0 : ((G.neighborFinset w) ∩ K).card = 0
    · omega
    · rcases Finset.card_pos.mp (by omega : 0 < ((G.neighborFinset w) ∩ K).card) with ⟨k, hk⟩
      rcases Finset.mem_inter.mp hk with ⟨hkN, hkK⟩
      have hwk : G.Adj w k := mem_nb.mp hkN
      have hw4 : w ∈ VGe4 G := by
        simp only [K, Finset.mem_insert, Finset.mem_singleton] at hkK
        rcases hkK with rfl | rfl | rfl | rfl
        · exact s1_other_ge4 hu3 hu1 huv hux hx_ne_v.symm hv_n4 hx_n4 w hwk.symm hwv_ne hwx_ne
        · exact s1_other_ge4 hv3 hv1 huv.symm hvy hy_ne_u.symm hu_n4 hy_n4 w hwk.symm hwu_ne hwy_ne
        · exact s2_other_ge4 hx3 hx2 hux.symm hu_n4 w hwk.symm hwu_ne
        · exact s2_other_ge4 hy3 hy2 hvy.symm hv_n4 w hwk.symm hwv_ne
      have hdeg4 : 4 ≤ G.degree w := (Finset.mem_filter.mp hw4).2
      by_cases hle1 : ((G.neighborFinset w) ∩ K).card ≤ 1
      · omega
      · push Not at hle1
        have hwx : G.Adj w x := by
          rcases Finset.one_lt_card.mp hle1 with ⟨k1, hk1, k2, hk2, hk12⟩
          rcases Finset.mem_inter.mp hk1 with ⟨h1N, h1K⟩
          rcases Finset.mem_inter.mp hk2 with ⟨h2N, h2K⟩
          have h1 := mem_nb.mp h1N
          have h2 := mem_nb.mp h2N
          simp only [K, Finset.mem_insert, Finset.mem_singleton] at h1K h2K
          rcases h1K with rfl | rfl | rfl | rfl <;> rcases h2K with rfl | rfl | rfl | rfl
          · exact False.elim (hk12 rfl)
          · exact False.elim (htri w u v h1 huv h2)
          · exact False.elim (htri w u x h1 hux h2)
          · exact False.elim (powerFree_no_c4 hG.1.1 ⟨h1, huv, hvy, h2.symm, hwu_ne, hwv_ne, hwy_ne, huv_ne, hy_ne_u.symm, hvy_ne⟩)
          · exact False.elim (htri w v u h1 huv.symm h2)
          · exact False.elim (hk12 rfl)
          · exact False.elim (powerFree_no_c4 hG.1.1 ⟨h1, huv.symm, hux, h2.symm, hwv_ne, hwu_ne, hwx_ne, huv_ne.symm, hx_ne_v.symm, hux_ne⟩)
          · exact False.elim (htri w v y h1 hvy h2)
          · exact h1
          · exact h1
          · exact False.elim (hk12 rfl)
          · exact h1
          · exact False.elim (powerFree_no_c4 hG.1.1 ⟨h2, huv, hvy, h1.symm, hwu_ne, hwv_ne, hwy_ne, huv_ne, hy_ne_u.symm, hvy_ne⟩)
          · exact False.elim (htri w v y h2 hvy h1)
          · exact h2
          · exact False.elim (hk12 rfl)
        have hwy : G.Adj w y := by
          rcases Finset.one_lt_card.mp hle1 with ⟨k1, hk1, k2, hk2, hk12⟩
          rcases Finset.mem_inter.mp hk1 with ⟨h1N, h1K⟩
          rcases Finset.mem_inter.mp hk2 with ⟨h2N, h2K⟩
          have h1 := mem_nb.mp h1N
          have h2 := mem_nb.mp h2N
          simp only [K, Finset.mem_insert, Finset.mem_singleton] at h1K h2K
          rcases h1K with rfl | rfl | rfl | rfl <;> rcases h2K with rfl | rfl | rfl | rfl
          · exact False.elim (hk12 rfl)
          · exact False.elim (htri w u v h1 huv h2)
          · exact False.elim (htri w u x h1 hux h2)
          · exact False.elim (powerFree_no_c4 hG.1.1 ⟨h1, huv, hvy, h2.symm, hwu_ne, hwv_ne, hwy_ne, huv_ne, hy_ne_u.symm, hvy_ne⟩)
          · exact False.elim (htri w v u h1 huv.symm h2)
          · exact False.elim (hk12 rfl)
          · exact False.elim (powerFree_no_c4 hG.1.1 ⟨h1, huv.symm, hux, h2.symm, hwv_ne, hwu_ne, hwx_ne, huv_ne.symm, hx_ne_v.symm, hux_ne⟩)
          · exact False.elim (htri w v y h1 hvy h2)
          · exact False.elim (htri w u x h2 hux h1)
          · exact False.elim (powerFree_no_c4 hG.1.1 ⟨h2, huv.symm, hux, h1.symm, hwv_ne, hwu_ne, hwx_ne, huv_ne.symm, hx_ne_v.symm, hux_ne⟩)
          · exact False.elim (hk12 rfl)
          · exact h2
          · exact h1
          · exact h1
          · exact h1
          · exact False.elim (hk12 rfl)
        have hsub2 : (G.neighborFinset w) ∩ K ⊆ {x, y} := by
          intro t ht; rcases Finset.mem_inter.mp ht with ⟨htN, htK⟩
          have hwt := mem_nb.mp htN
          simp only [K, Finset.mem_insert, Finset.mem_singleton] at htK ⊢
          rcases htK with rfl | rfl | rfl | rfl
          · exact False.elim (htri w u x hwt hux hwx)
          · exact False.elim (htri w v y hwt hvy hwy)
          · exact Or.inl rfl
          · exact Or.inr rfl
        have hle2 : ((G.neighborFinset w) ∩ K).card ≤ 2 :=
          le_trans (Finset.card_le_card hsub2) Finset.card_le_two
        have hc5 : IsC5 G u v y w x :=
          ⟨huv, hvy, hwy.symm, hwx, hux.symm,
            huv_ne, hy_ne_u.symm, hwu_ne.symm, hux_ne,
            hvy_ne, hwv_ne.symm, hx_ne_v.symm,
            hwy_ne.symm, hxy_ne.symm, hwx_ne⟩
        have hne4 : G.degree w ≠ 4 := fun h4 => hnone w hwx hwy h4 hc5
        omega

/-- PILLAR 4.3: In girth >= 6 (C3-free and C5-free) MinimalBad2, S1b is an independent set. -/
theorem minimal_bad2_girth6_s1b_independent {V : Type} [Fintype V]
    {G : SimpleGraph V} (hG : MinimalBad2 G)
    (htri : TriangleFree G) (hc5free : ∀ a b c d e : V, ¬ IsC5 G a b c d e)
    {u v x y : V}
    (hu3 : u ∈ V3 G) (hv3 : v ∈ V3 G) (hx3 : x ∈ V3 G) (hy3 : y ∈ V3 G)
    (hu1 : ((G.neighborFinset u) ∩ VGe4 G).card = 1)
    (hv1 : ((G.neighborFinset v) ∩ VGe4 G).card = 1)
    (hx2 : ((G.neighborFinset x) ∩ VGe4 G).card = 2)
    (hy2 : ((G.neighborFinset y) ∩ VGe4 G).card = 2)
    (hux : G.Adj u x) (hvy : G.Adj v y) :
    ¬ G.Adj u v := by
  intro huv
  rcases minimal_bad2_trifree_adjacent_s1b_forces_c5_deg4 hG htri hu3 hv3 hx3 hy3 hu1 hv1 hx2 hy2
    huv hux hvy with ⟨w, _, _, _, hc5⟩
  exact hc5free u v y w x hc5

/-- PILLAR 4.4: Sharpened Girth >= 6 Cubic Density 20/27 on MinimalBad2:
    27 * |V3(G)| >= 20 * n - 52 (strictly tightening 8/11 to 20/27!). -/
theorem minimal_bad2_girth6_v3_density_20_27 {V : Type} [Fintype V]
    {G : SimpleGraph V} (hG : MinimalBad2 G)
    (hhigh_ind : ∀ u ∈ VGe4 G, ∀ v ∈ VGe4 G, ¬ G.Adj u v)
    (hdef_nb_v3 : ∀ d ∈ Defects G, ∀ u, G.Adj d u → u ∈ V3 G)
    (hv3_le2 : ∀ v ∈ V3 G, ((G.neighborFinset v) ∩ VGe4 G).card ≤ 2)
    (hs2_ind : ∀ u ∈ V3 G, ((G.neighborFinset u) ∩ VGe4 G).card = 2 →
      ∀ v ∈ V3 G, ((G.neighborFinset v) ∩ VGe4 G).card = 2 → ¬ G.Adj u v)
    (hs1_le1 : ∀ u ∈ V3 G, ((G.neighborFinset u) ∩ VGe4 G).card = 1 →
      ((G.neighborFinset u) ∩ ((V3 G).filter (fun v => ((G.neighborFinset v) ∩ VGe4 G).card = 2))).card ≤ 1)
    (hs0_le2 : ∀ u ∈ V3 G, ((G.neighborFinset u) ∩ VGe4 G).card = 0 →
      ((G.neighborFinset u) ∩ ((V3 G).filter (fun v => ((G.neighborFinset v) ∩ VGe4 G).card = 2))).card ≤ 2)
    (hs1b_ind : ∀ u ∈ V3 G, ((G.neighborFinset u) ∩ VGe4 G).card = 1 →
      ((G.neighborFinset u) ∩ ((V3 G).filter (fun v => ((G.neighborFinset v) ∩ VGe4 G).card = 2))).card = 1 →
      ∀ v ∈ V3 G, ((G.neighborFinset v) ∩ VGe4 G).card = 1 →
      ((G.neighborFinset v) ∩ ((V3 G).filter (fun w => ((G.neighborFinset w) ∩ VGe4 G).card = 2))).card = 1 →
      ¬ G.Adj u v) :
    20 * Fintype.card V ≤ 27 * (V3 G).card + 52 := by
  let S0 := (V3 G).filter (fun v => ((G.neighborFinset v) ∩ VGe4 G).card = 0)
  let S2 := (V3 G).filter (fun v => ((G.neighborFinset v) ∩ VGe4 G).card = 2)
  let S1 := (V3 G).filter (fun v => ((G.neighborFinset v) ∩ VGe4 G).card = 1)
  let S1a := S1.filter (fun v => ((G.neighborFinset v) ∩ S2).card = 0)
  let S1b := S1.filter (fun v => ((G.neighborFinset v) ∩ S2).card = 1)
  have dc : ∀ (A B : Finset V),
      ∑ a ∈ A, ((G.neighborFinset a) ∩ B).card = ∑ b ∈ B, ((G.neighborFinset b) ∩ A).card := by
    intro A B
    have hl : ∑ a ∈ A, ((G.neighborFinset a) ∩ B).card =
        ∑ a ∈ A, ∑ b ∈ B, if G.Adj a b then 1 else 0 := by
      apply Finset.sum_congr rfl; intro a _
      rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
      congr 1; ext b; simp only [Finset.mem_inter, mem_nb, Finset.mem_filter]; tauto
    have hr : ∑ b ∈ B, ((G.neighborFinset b) ∩ A).card =
        ∑ b ∈ B, ∑ a ∈ A, if G.Adj b a then 1 else 0 := by
      apply Finset.sum_congr rfl; intro b _
      rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
      congr 1; ext a; simp only [Finset.mem_inter, mem_nb, Finset.mem_filter]; tauto
    rw [hl, hr, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro a _
    simp [SimpleGraph.adj_comm]
  have hpart : Fintype.card V = (Defects G).card + (V3 G).card + (VGe4 G).card := by
    have hd1 : Disjoint (Defects G) (V3 G) := by
      rw [Finset.disjoint_left]; intro x h1 h2
      have := (Finset.mem_filter.mp h1).2; have := (Finset.mem_filter.mp h2).2; omega
    have hd2 : Disjoint (Defects G ∪ V3 G) (VGe4 G) := by
      rw [Finset.disjoint_left]; intro x h1 h2
      have h4 := (Finset.mem_filter.mp h2).2
      rcases Finset.mem_union.mp h1 with h | h <;> (have := (Finset.mem_filter.mp h).2; omega)
    have hunion : Defects G ∪ V3 G ∪ VGe4 G = Finset.univ := by
      ext x; simp only [Finset.mem_union, Defects, V3, VGe4, Finset.mem_filter, Finset.mem_univ,
        true_and, iff_true]
      have := hG.1.2.1 x; omega
    rw [← Finset.card_univ, ← hunion, Finset.card_union_of_disjoint hd2,
        Finset.card_union_of_disjoint hd1]
  have hd01 : Disjoint S0 S1 := by
    rw [Finset.disjoint_left]; intro x h1 h2
    have := (Finset.mem_filter.mp h1).2; have := (Finset.mem_filter.mp h2).2; omega
  have hd01_2 : Disjoint (S0 ∪ S1) S2 := by
    rw [Finset.disjoint_left]; intro x h1 h2
    have h2' := (Finset.mem_filter.mp h2).2
    rcases Finset.mem_union.mp h1 with h | h <;> (have := (Finset.mem_filter.mp h).2; omega)
  have hu3 : S0 ∪ S1 ∪ S2 = V3 G := by
    ext x; simp only [Finset.mem_union, S0, S1, S2, Finset.mem_filter]
    constructor
    · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
    · intro hx; have := hv3_le2 x hx; omega
  have hd_ab : Disjoint S1a S1b := by
    rw [Finset.disjoint_left]; intro x h1 h2
    have := (Finset.mem_filter.mp h1).2; have := (Finset.mem_filter.mp h2).2; omega
  have hu1 : S1a ∪ S1b = S1 := by
    ext x; simp only [Finset.mem_union, S1a, S1b, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro hx
      have h1 := hs1_le1 x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2
      omega
  have hv3_card : (V3 G).card = S0.card + S1a.card + S1b.card + S2.card := by
    rw [← hu3, Finset.card_union_of_disjoint hd01_2, Finset.card_union_of_disjoint hd01,
        ← hu1, Finset.card_union_of_disjoint hd_ab]; omega
  have h4ge4 : 4 * (VGe4 G).card ≤ S1a.card + S1b.card + 2 * S2.card := by
    have hsum_v3 : ∑ v ∈ V3 G, ((G.neighborFinset v) ∩ VGe4 G).card = S1a.card + S1b.card + 2 * S2.card := by
      rw [← hu3, Finset.sum_union hd01_2, Finset.sum_union hd01, ← hu1, Finset.sum_union hd_ab]
      have h0 : ∑ v ∈ S0, ((G.neighborFinset v) ∩ VGe4 G).card = 0 :=
        Finset.sum_eq_zero (fun v hv => (Finset.mem_filter.mp hv).2)
      have h1a : ∑ v ∈ S1a, ((G.neighborFinset v) ∩ VGe4 G).card = S1a.card := by
        calc ∑ v ∈ S1a, ((G.neighborFinset v) ∩ VGe4 G).card
            = ∑ _v ∈ S1a, 1 := Finset.sum_congr rfl (fun v hv => (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).2)
          _ = S1a.card := by simp
      have h1b : ∑ v ∈ S1b, ((G.neighborFinset v) ∩ VGe4 G).card = S1b.card := by
        calc ∑ v ∈ S1b, ((G.neighborFinset v) ∩ VGe4 G).card
            = ∑ _v ∈ S1b, 1 := Finset.sum_congr rfl (fun v hv => (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).2)
          _ = S1b.card := by simp
      have h2 : ∑ v ∈ S2, ((G.neighborFinset v) ∩ VGe4 G).card = 2 * S2.card := by
        calc ∑ v ∈ S2, ((G.neighborFinset v) ∩ VGe4 G).card
            = ∑ _v ∈ S2, 2 := Finset.sum_congr rfl (fun v hv => (Finset.mem_filter.mp hv).2)
          _ = 2 * S2.card := by simp [mul_comm]
      omega
    have hedge : ∑ h ∈ VGe4 G, G.degree h = ∑ v ∈ V3 G, ((G.neighborFinset v) ∩ VGe4 G).card := by
      rw [← dc (VGe4 G) (V3 G)]
      apply Finset.sum_congr rfl; intro h hh
      rw [← SimpleGraph.card_neighborFinset_eq_degree]; congr 1; ext u
      simp only [Finset.mem_inter, mem_nb, and_iff_left_iff_imp]
      intro hadj
      have hn4 : u ∉ VGe4 G := fun hu4 => hhigh_ind h hh u hu4 hadj
      have hn2 : u ∉ Defects G := fun hu2 => by
        have := (Finset.mem_filter.mp (hdef_nb_v3 u hu2 h hadj.symm)).2
        have := (Finset.mem_filter.mp hh).2; omega
      have h2 := hG.1.2.1 u
      simp only [V3, Defects, VGe4, Finset.mem_filter, Finset.mem_univ, true_and] at hn4 hn2 ⊢
      omega
    have h4 : 4 * (VGe4 G).card ≤ ∑ h ∈ VGe4 G, G.degree h := by
      calc 4 * (VGe4 G).card = ∑ _h ∈ VGe4 G, 4 := by simp [mul_comm]
        _ ≤ ∑ h ∈ VGe4 G, G.degree h := Finset.sum_le_sum (fun h hh => (Finset.mem_filter.mp hh).2)
    omega
  let eS0_S2 := ∑ v ∈ S0, ((G.neighborFinset v) ∩ S2).card
  let eD_S2 := ∑ d ∈ Defects G, ((G.neighborFinset d) ∩ S2).card
  have hS2_eq : S2.card = eS0_S2 + S1b.card + eD_S2 := by
    have h1 : S2.card = ∑ x ∈ S2, ((G.neighborFinset x) ∩ (S0 ∪ S1b ∪ Defects G)).card := by
      symm
      calc ∑ x ∈ S2, ((G.neighborFinset x) ∩ (S0 ∪ S1b ∪ Defects G)).card
          = ∑ _x ∈ S2, 1 := by
            apply Finset.sum_congr rfl; intro x hx
            have hx3 := (Finset.mem_filter.mp hx).1
            have hx2 := (Finset.mem_filter.mp hx).2
            have hdeg3 : G.degree x = 3 := (Finset.mem_filter.mp hx3).2
            have hsplit : (G.neighborFinset x) ∩ (S0 ∪ S1b ∪ Defects G) =
                (G.neighborFinset x) \ ((G.neighborFinset x) ∩ VGe4 G) := by
              ext y
              simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff, mem_nb]
              constructor
              · rintro ⟨hxy, (hy | hy) | hy⟩
                · exact ⟨hxy, fun h => by
                    have := (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).2
                    have := (Finset.mem_filter.mp h.2).2; omega⟩
                · exact ⟨hxy, fun h => by
                    have := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).1).2
                    have := (Finset.mem_filter.mp h.2).2; omega⟩
                · exact ⟨hxy, fun h => by
                    have := (Finset.mem_filter.mp hy).2
                    have := (Finset.mem_filter.mp h.2).2; omega⟩
              · rintro ⟨hxy, hyn4⟩
                refine ⟨hxy, ?_⟩
                have hyn4' : y ∉ VGe4 G := fun h => hyn4 ⟨hxy, h⟩
                by_cases hyd : y ∈ Defects G
                · exact Or.inr hyd
                · have hy3 : y ∈ V3 G := by
                    have := hG.1.2.1 y
                    simp only [V3, Defects, VGe4, Finset.mem_filter, Finset.mem_univ, true_and] at hyn4' hyd ⊢
                    omega
                  have hy_in : y ∈ S0 ∪ S1 ∪ S2 := by rw [hu3]; exact hy3
                  simp only [Finset.mem_union] at hy_in
                  rcases hy_in with (hy0 | hy1) | hy2
                  · exact Or.inl (Or.inl hy0)
                  · have hy_ab : y ∈ S1a ∪ S1b := by rw [hu1]; exact hy1
                    rcases Finset.mem_union.mp hy_ab with hya | hyb
                    · have h0 := (Finset.mem_filter.mp hya).2
                      have hpos : 0 < ((G.neighborFinset y) ∩ S2).card :=
                        Finset.card_pos.mpr ⟨x, Finset.mem_inter.mpr ⟨mem_nb.mpr hxy.symm, hx⟩⟩
                      omega
                    · exact Or.inl (Or.inr hyb)
                  · exact False.elim (hs2_ind x hx3 hx2 y hy3 (Finset.mem_filter.mp hy2).2 hxy)
            rw [hsplit, Finset.card_sdiff (Finset.inter_subset_left),
                SimpleGraph.card_neighborFinset_eq_degree, hdeg3, hx2]
        _ = S2.card := by simp
    rw [h1]
    have hd_0_1b : Disjoint S0 S1b := hd01.mono_right (Finset.filter_subset _ _)
    have hd_01b_D : Disjoint (S0 ∪ S1b) (Defects G) := by
      rw [Finset.disjoint_left]; intro y hy1 hy2
      have := (Finset.mem_filter.mp hy2).2
      rcases Finset.mem_union.mp hy1 with h | h
      · have := (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2; omega
      · have := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1).2; omega
    have hsum_split : ∑ x ∈ S2, ((G.neighborFinset x) ∩ (S0 ∪ S1b ∪ Defects G)).card =
        (∑ x ∈ S2, ((G.neighborFinset x) ∩ S0).card) +
        (∑ x ∈ S2, ((G.neighborFinset x) ∩ S1b).card) +
        (∑ x ∈ S2, ((G.neighborFinset x) ∩ Defects G).card) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro x _
      rw [Finset.inter_union_distrib_left, Finset.inter_union_distrib_left,
          Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
      · exact hd_0_1b.mono Finset.inter_subset_right Finset.inter_subset_right
      · exact hd_01b_D.mono (Finset.union_subset (Finset.inter_subset_right.trans Finset.subset_union_left)
          (Finset.inter_subset_right.trans Finset.subset_union_right)) Finset.inter_subset_right
    rw [hsum_split, dc S2 S0, dc S2 S1b, dc S2 (Defects G)]
    have h1b_eq : ∑ v ∈ S1b, ((G.neighborFinset v) ∩ S2).card = S1b.card := by
      calc ∑ v ∈ S1b, ((G.neighborFinset v) ∩ S2).card
          = ∑ _v ∈ S1b, 1 := Finset.sum_congr rfl (fun v hv => (Finset.mem_filter.mp hv).2)
        _ = S1b.card := by simp
    omega
  let eS0_S1b := ∑ v ∈ S0, ((G.neighborFinset v) ∩ S1b).card
  let eS1a_S1b := ∑ v ∈ S1a, ((G.neighborFinset v) ∩ S1b).card
  let eD_S1b := ∑ d ∈ Defects G, ((G.neighborFinset d) ∩ S1b).card
  have hS1b_eq : S1b.card = eS0_S1b + eS1a_S1b + eD_S1b := by
    have h1 : S1b.card = ∑ x ∈ S1b, ((G.neighborFinset x) ∩ (S0 ∪ S1a ∪ Defects G)).card := by
      symm
      calc ∑ x ∈ S1b, ((G.neighborFinset x) ∩ (S0 ∪ S1a ∪ Defects G)).card
          = ∑ _x ∈ S1b, 1 := by
            apply Finset.sum_congr rfl; intro x hx
            have hx1 := (Finset.mem_filter.mp hx).1
            have hx3 := (Finset.mem_filter.mp hx1).1
            have hx_g4 := (Finset.mem_filter.mp hx1).2
            have hx_s2 := (Finset.mem_filter.mp hx).2
            have hdeg3 : G.degree x = 3 := (Finset.mem_filter.mp hx3).2
            have hdisj_g4_s2 : Disjoint ((G.neighborFinset x) ∩ VGe4 G) ((G.neighborFinset x) ∩ S2) := by
              rw [Finset.disjoint_left]; intro y hy1 hy2
              have := (Finset.mem_filter.mp (Finset.mem_inter.mp hy1).2).2
              have := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_inter.mp hy2).2).1).2; omega
            have hsplit : (G.neighborFinset x) ∩ (S0 ∪ S1a ∪ Defects G) =
                (G.neighborFinset x) \ (((G.neighborFinset x) ∩ VGe4 G) ∪ ((G.neighborFinset x) ∩ S2)) := by
              ext y
              simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff, mem_nb]
              constructor
              · rintro ⟨hxy, (hy | hy) | hy⟩
                · refine ⟨hxy, ?_⟩; rintro (⟨_, h⟩ | ⟨_, h⟩)
                  · have := (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).2
                    have := (Finset.mem_filter.mp h).2; omega
                  · have := (Finset.mem_filter.mp hy).2
                    have := (Finset.mem_filter.mp h).2; omega
                · refine ⟨hxy, ?_⟩; rintro (⟨_, h⟩ | ⟨_, h⟩)
                  · have := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).1).2
                    have := (Finset.mem_filter.mp h).2; omega
                  · have := (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).2
                    have := (Finset.mem_filter.mp h).2; omega
                · refine ⟨hxy, ?_⟩; rintro (⟨_, h⟩ | ⟨_, h⟩)
                  · have := (Finset.mem_filter.mp hy).2
                    have := (Finset.mem_filter.mp h).2; omega
                  · have := (Finset.mem_filter.mp hy).2
                    have := (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2; omega
              · rintro ⟨hxy, hnot⟩
                refine ⟨hxy, ?_⟩
                have hyn4 : y ∉ VGe4 G := fun h => hnot (Or.inl ⟨hxy, h⟩)
                have hyn2 : y ∉ S2 := fun h => hnot (Or.inr ⟨hxy, h⟩)
                by_cases hyd : y ∈ Defects G
                · exact Or.inr hyd
                · have hy3 : y ∈ V3 G := by
                    have := hG.1.2.1 y
                    simp only [V3, Defects, VGe4, Finset.mem_filter, Finset.mem_univ, true_and] at hyn4 hyd ⊢
                    omega
                  have hy_in : y ∈ S0 ∪ S1 ∪ S2 := by rw [hu3]; exact hy3
                  simp only [Finset.mem_union] at hy_in
                  rcases hy_in with (hy0 | hy1) | hy2
                  · exact Or.inl (Or.inl hy0)
                  · have hy_ab : y ∈ S1a ∪ S1b := by rw [hu1]; exact hy1
                    rcases Finset.mem_union.mp hy_ab with hya | hyb
                    · exact Or.inl (Or.inr hya)
                    · have hy1' := (Finset.mem_filter.mp hyb).1
                      have hy_g4 := (Finset.mem_filter.mp hy1').2
                      have hy_s2 := (Finset.mem_filter.mp hyb).2
                      exact False.elim (hs1b_ind x hx3 hx_g4 hx_s2 y hy3 hy_g4 hy_s2 hxy)
                  · exact False.elim (hyn2 hy2)
            rw [hsplit, Finset.card_sdiff (Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left),
                Finset.card_union_of_disjoint hdisj_g4_s2,
                SimpleGraph.card_neighborFinset_eq_degree, hdeg3, hx_g4, hx_s2]
        _ = S1b.card := by simp
    rw [h1]
    have hd_0_1a : Disjoint S0 S1a := hd01.mono_right (Finset.filter_subset _ _)
    have hd_01a_D : Disjoint (S0 ∪ S1a) (Defects G) := by
      rw [Finset.disjoint_left]; intro y hy1 hy2
      have := (Finset.mem_filter.mp hy2).2
      rcases Finset.mem_union.mp hy1 with h | h
      · have := (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2; omega
      · have := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1).2; omega
    have hsum_split : ∑ x ∈ S1b, ((G.neighborFinset x) ∩ (S0 ∪ S1a ∪ Defects G)).card =
        (∑ x ∈ S1b, ((G.neighborFinset x) ∩ S0).card) +
        (∑ x ∈ S1b, ((G.neighborFinset x) ∩ S1a).card) +
        (∑ x ∈ S1b, ((G.neighborFinset x) ∩ Defects G).card) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro x _
      rw [Finset.inter_union_distrib_left, Finset.inter_union_distrib_left,
          Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
      · exact hd_0_1a.mono Finset.inter_subset_right Finset.inter_subset_right
      · exact hd_01a_D.mono (Finset.union_subset (Finset.inter_subset_right.trans Finset.subset_union_left)
          (Finset.inter_subset_right.trans Finset.subset_union_right)) Finset.inter_subset_right
    rw [hsum_split, dc S1b S0, dc S1b S1a, dc S1b (Defects G)]
  have heS0_S2_le : eS0_S2 ≤ 2 * S0.card := by
    calc eS0_S2 ≤ ∑ _v ∈ S0, 2 :=
          Finset.sum_le_sum (fun v hv => hs0_le2 v (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hv).2)
      _ = 2 * S0.card := by simp [mul_comm]
  have heS0_tot : eS0_S1b + eS0_S2 ≤ 3 * S0.card := by
    have hd_1b_2 : Disjoint S1b S2 :=
      hd01_2.mono_left (Finset.subset_union_right.trans' (Finset.filter_subset _ _))
    calc eS0_S1b + eS0_S2
        = ∑ v ∈ S0, (((G.neighborFinset v) ∩ S1b).card + ((G.neighborFinset v) ∩ S2).card) :=
          (Finset.sum_add_distrib).symm
      _ ≤ ∑ v ∈ S0, (G.neighborFinset v).card := by
          apply Finset.sum_le_sum; intro v _
          rw [← Finset.card_union_of_disjoint (hd_1b_2.mono Finset.inter_subset_right Finset.inter_subset_right)]
          exact Finset.card_le_card (Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left)
      _ = ∑ _v ∈ S0, 3 := by
          apply Finset.sum_congr rfl; intro v hv
          rw [SimpleGraph.card_neighborFinset_eq_degree]
          exact (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).2
      _ = 3 * S0.card := by simp [mul_comm]
  have heS1a_le : eS1a_S1b ≤ 2 * S1a.card := by
    calc eS1a_S1b ≤ ∑ _v ∈ S1a, 2 := by
          apply Finset.sum_le_sum; intro v hv
          have hv1 := (Finset.mem_filter.mp hv).1
          have hv3 := (Finset.mem_filter.mp hv1).1
          have hdeg3 : G.degree v = 3 := (Finset.mem_filter.mp hv3).2
          have hv_g4 : ((G.neighborFinset v) ∩ VGe4 G).card = 1 := (Finset.mem_filter.mp hv1).2
          have hd_1b_g4 : Disjoint ((G.neighborFinset v) ∩ S1b) ((G.neighborFinset v) ∩ VGe4 G) := by
            rw [Finset.disjoint_left]; intro y hy1 hy2
            have := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_inter.mp hy1).2).1).1).2
            have := (Finset.mem_filter.mp (Finset.mem_inter.mp hy2).2).2; omega
          have hle3 : ((G.neighborFinset v) ∩ S1b).card + ((G.neighborFinset v) ∩ VGe4 G).card ≤ 3 := by
            rw [← Finset.card_union_of_disjoint hd_1b_g4]
            calc (((G.neighborFinset v) ∩ S1b) ∪ ((G.neighborFinset v) ∩ VGe4 G)).card
                ≤ (G.neighborFinset v).card := Finset.card_le_card (Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left)
              _ = 3 := by rw [SimpleGraph.card_neighborFinset_eq_degree, hdeg3]
          omega
      _ = 2 * S1a.card := by simp [mul_comm]
  have heD_tot : eD_S1b + eD_S2 ≤ 4 := by
    have hd_1b_2 : Disjoint S1b S2 :=
      hd01_2.mono_left (Finset.subset_union_right.trans' (Finset.filter_subset _ _))
    have hle : eD_S1b + eD_S2 ≤ 2 * (Defects G).card := by
      calc eD_S1b + eD_S2
          = ∑ d ∈ Defects G, (((G.neighborFinset d) ∩ S1b).card + ((G.neighborFinset d) ∩ S2).card) :=
            (Finset.sum_add_distrib).symm
        _ ≤ ∑ d ∈ Defects G, (G.neighborFinset d).card := by
            apply Finset.sum_le_sum; intro d _
            rw [← Finset.card_union_of_disjoint (hd_1b_2.mono Finset.inter_subset_right Finset.inter_subset_right)]
            exact Finset.card_le_card (Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left)
        _ = ∑ _d ∈ Defects G, 2 := by
            apply Finset.sum_congr rfl; intro d hd
            rw [SimpleGraph.card_neighborFinset_eq_degree]
            exact (Finset.mem_filter.mp hd).2
        _ = 2 * (Defects G).card := by simp [mul_comm]
    have hdef2 := hG.1.2.2
    omega
  have hdef2 := hG.1.2.2
  omega

end E64Wave7Agent2
