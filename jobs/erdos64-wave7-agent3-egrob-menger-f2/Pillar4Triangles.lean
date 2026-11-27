import Mathlib

open Classical
open SimpleGraph

namespace E64Wave7Agent3P4

/-!
# Wave 7 Agent #3 — Pillar 4: Universal Triangle Contraction & High-Apex Base Forcing
-/

def IsPowerOfTwo (L : ℕ) : Prop := ∃ k : ℕ, 2 ≤ k ∧ L = 2 ^ k

def HasPowerCycle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ IsPowerOfTwo p.length

def PowerFree {V : Type*} (G : SimpleGraph V) : Prop := ¬ HasPowerCycle G

def MinDegGe {V : Type*} [Fintype V] (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∀ v : V, d ≤ G.degree v

def Defects {V : Type*} [Fintype V] (G : SimpleGraph V) : Finset V :=
  Finset.univ.filter (fun v => G.degree v = 2)

def V3 {V : Type*} [Fintype V] (G : SimpleGraph V) : Finset V :=
  Finset.univ.filter (fun v => G.degree v = 3)

def VGe4 {V : Type*} [Fintype V] (G : SimpleGraph V) : Finset V :=
  Finset.univ.filter (fun v => 4 ≤ G.degree v)

def Bad2 {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  PowerFree G ∧ MinDegGe G 2 ∧ (Defects G).card ≤ 2

def MinimalBad2 {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  Bad2 G ∧
  (∀ (m : ℕ) (H : SimpleGraph (Fin m)), Bad2 H → Fintype.card V ≤ m) ∧
  (∀ (H : SimpleGraph V), Bad2 H → G.edgeFinset.card ≤ H.edgeFinset.card)

lemma bad2_of_iso {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (hG : Bad2 G) : Bad2 H := by
  rcases hG with ⟨hpf, hmin, hdef⟩
  refine ⟨?_, ?_, ?_⟩
  · intro ⟨w, p, hcyc, hpow⟩
    apply hpf; refine ⟨e.symm w, p.map e.symm.toHom, hcyc.map e.symm.injective, by simpa using hpow⟩
  · intro w; rw [(e.symm.degree_eq w).symm]; exact hmin (e.symm w)
  · have hcard : (Defects H).card = (Defects G).card := by
      apply Finset.card_bij (fun w _ => e.symm w)
      · intro w hw; simp only [Defects, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
        rw [← e.symm.degree_eq w]; exact hw
      · intro _ _ _ _ h; exact e.symm.injective h
      · intro v hv; refine ⟨e v, ?_, e.symm_apply_apply v⟩
        simp only [Defects, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
        rw [e.degree_eq v]; exact hv
    omega

lemma minimal_bad2_no_smaller {V : Type} [Fintype V] {G : SimpleGraph V}
    (hG : MinimalBad2 G) {W : Type} [Fintype W] (H : SimpleGraph W)
    (hH : Bad2 H) (hlt : Fintype.card W < Fintype.card V) : False := by
  let e : W ≃ Fin (Fintype.card W) := Fintype.equivFin W
  let H' : SimpleGraph (Fin (Fintype.card W)) := H.map e.toEmbedding
  have iso : H ≃g H' :=
    { toEquiv := e
      map_rel_iff' := by
        intro u v; simp only [H', SimpleGraph.map_adj, Equiv.coe_toEmbedding]
        constructor
        · rintro ⟨a, b, hab, ha, hb⟩; rw [← e.injective ha, ← e.injective hb]; exact hab
        · intro huv; exact ⟨u, v, huv, rfl, rfl⟩ }
  have hH' : Bad2 H' := bad2_of_iso iso hH
  have hle : Fintype.card V ≤ Fintype.card W := hG.2.1 (Fintype.card W) H' hH'
  omega

lemma powerFree_induce {V : Type*} {G : SimpleGraph V} (s : Set V) (hG : PowerFree G) :
    PowerFree (G.induce s) := by
  intro ⟨v, p, hcyc, hpow⟩
  apply hG; refine ⟨v.1, p.map (SimpleGraph.Embedding.induce s).toHom, hcyc.map Subtype.val_injective, by simpa using hpow⟩

lemma degree_induce_eq {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Finset V)
    (u : {x : V // x ∈ (S : Set V)}) :
    (G.induce (S : Set V)).degree u = ((G.neighborFinset u.1) ∩ S).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun v _ => v.1)
  · intro v hv; simp only [SimpleGraph.mem_neighborFinset, Finset.mem_inter] at hv ⊢; exact ⟨hv, v.2⟩
  · intro _ _ _ _ h; exact Subtype.ext h
  · intro w hw; simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hw
    exact ⟨⟨w, hw.2⟩, by simpa [SimpleGraph.mem_neighborFinset] using hw.1, rfl⟩

lemma degree_compl_eq_sub {V : Type*} [Fintype V] (G : SimpleGraph V) (K : Finset V) (u : V) :
    ((G.neighborFinset u) ∩ Kᶜ).card + ((G.neighborFinset u) ∩ K).card = G.degree u := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← Finset.card_union_of_disjoint]
  · congr 1; ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_compl]; tauto
  · rw [Finset.disjoint_left]; intro x hx1 hx2
    exact (Finset.mem_compl.mp (Finset.mem_inter.mp hx1).2) (Finset.mem_inter.mp hx2).2

lemma minimal_bad2_no_safe_deletion {V : Type} [Fintype V] {G : SimpleGraph V}
    (hG : MinimalBad2 G) (K : Finset V) (hKne : K.Nonempty)
    (hmin : ∀ u ∈ Kᶜ, 2 ≤ ((G.neighborFinset u) ∩ Kᶜ).card)
    (hdef : (Kᶜ.filter (fun u => ((G.neighborFinset u) ∩ Kᶜ).card = 2)).card ≤ 2) :
    False := by
  let H := G.induce (Kᶜ : Set V)
  have hH_pf : PowerFree H := powerFree_induce (Kᶜ : Set V) hG.1.1
  have hH_min : MinDegGe H 2 := by intro u; rw [degree_induce_eq]; exact hmin u.1 u.2
  have hH_def : (Defects H).card ≤ 2 := by
    have hcard : (Defects H).card =
        (Kᶜ.filter (fun u => ((G.neighborFinset u) ∩ Kᶜ).card = 2)).card := by
      apply Finset.card_bij (fun u _ => u.1)
      · intro u hu; simp only [Defects, Finset.mem_filter, Finset.mem_univ, true_and] at hu
        rw [degree_induce_eq] at hu; exact Finset.mem_filter.mpr ⟨u.2, hu⟩
      · intro _ _ _ _ h; exact Subtype.ext h
      · intro w hw; rcases Finset.mem_filter.mp hw with ⟨hwS, hwdeg⟩
        refine ⟨⟨w, hwS⟩, ?_, rfl⟩
        simp only [Defects, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [degree_induce_eq]; exact hwdeg
    rw [hcard]; exact hdef
  have hlt : Fintype.card {x : V // x ∈ (Kᶜ : Set V)} < Fintype.card V := by
    rw [Fintype.card_coe]; have h1 := Finset.card_compl_add_card K
    have h2 : 0 < K.card := Finset.card_pos.mpr hKne; omega
  exact minimal_bad2_no_smaller hG H ⟨hH_pf, hH_min, hH_def⟩ hlt

lemma mem_support_of_edge {V : Type*} {G : SimpleGraph V} {u v w : V} {e : Sym2 V}
    (p : G.Walk u v) (he : e ∈ p.edges) (hw : w ∈ e) : w ∈ p.support := by
  induction p with
  | nil => simp at he
  | @cons a b c hab rest ih =>
    simp only [Walk.edges_cons, List.mem_cons] at he
    rcases he with rfl | h'
    · simp only [Sym2.mem_iff] at hw
      rcases hw with rfl | rfl
      · exact Walk.start_mem_support _
      · exact List.mem_cons_of_mem _ (Walk.start_mem_support _)
    · exact List.mem_cons_of_mem _ (ih h')

lemma walk_adj_of_mem_edges {V : Type*} {G : SimpleGraph V} {u v x y : V}
    (p : G.Walk u v) (h : s(x, y) ∈ p.edges) : G.Adj x y := by
  induction p with
  | nil => simp at h
  | @cons a b c hab rest ih =>
    simp only [Walk.edges_cons, List.mem_cons] at h
    rcases h with heq | h'
    · rw [Sym2.eq_iff] at heq; rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hab
      · exact hab.symm
    · exact ih h'

lemma isPath_mem_edges_endpoints_length_one {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hp : p.IsPath) (hmem : s(u, v) ∈ p.edges) : p.length = 1 := by
  cases p with
  | nil => simp at hmem
  | @cons _ w _ huw q =>
    simp only [Walk.edges_cons, List.mem_cons] at hmem
    rcases hmem with heq | hmem'
    · rw [Sym2.eq_iff] at heq; rcases heq with ⟨_, rfl⟩ | ⟨hvu, rfl⟩
      · cases q with
        | nil => rfl
        | @cons _ z _ hvz q' =>
          have hnd := List.nodup_cons.mp (List.nodup_cons.mp hp.support_nodup).2
          exact False.elim (hnd.1 (Walk.end_mem_support q'))
      · exact False.elim (G.ne_of_adj huw hvu.symm)
    · have hu_in : u ∈ q.support := mem_support_of_edge q hmem' (by simp)
      exact False.elim ((List.nodup_cons.mp hp.support_nodup).1 hu_in)

lemma two_internally_disjoint_paths_cycle {V : Type*} {G : SimpleGraph V} {u v : V}
    (p q : G.Walk u v) (hp : p.IsPath) (hq : q.IsPath)
    (hp1 : 1 ≤ p.length) (hq1 : 1 ≤ q.length) (hsum3 : 3 ≤ p.length + q.length)
    (hdisj : ∀ w, w ∈ p.support → w ∈ q.support → w = u ∨ w = v) :
    (p.append q.reverse).IsCycle ∧ (p.append q.reverse).length = p.length + q.length := by
  let c : G.Walk u u := p.append q.reverse
  have hlen : c.length = p.length + q.length := by simp [c, Walk.length_append, Walk.length_reverse]
  have hqr_len : 1 ≤ q.reverse.length := by rw [Walk.length_reverse]; exact hq1
  have hqr_path : q.reverse.IsPath := hq.reverse
  refine ⟨?_, hlen⟩
  rw [Walk.isCycle_def]
  refine ⟨?_, ?_, ?_⟩
  · rw [Walk.isTrail_def]; simp only [Walk.edges_append]; rw [List.nodup_append]
    refine ⟨hp.isTrail.edges_nodup, hqr_path.isTrail.edges_nodup, ?_⟩
    intro e he1 e' he2 heq; subst heq
    have he2q : e ∈ q.edges := by simpa [Walk.edges_reverse] using he2
    refine Sym2.ind (fun x y => ?_) e he1 he2q
    intro hxy1 hxy2
    have hx_p : x ∈ p.support := mem_support_of_edge p hxy1 (by simp)
    have hy_p : y ∈ p.support := mem_support_of_edge p hxy1 (by simp)
    have hx_q : x ∈ q.support := mem_support_of_edge q hxy2 (by simp)
    have hy_q : y ∈ q.support := mem_support_of_edge q hxy2 (by simp)
    have hxy_ne : x ≠ y := G.ne_of_adj (walk_adj_of_mem_edges p hxy1)
    have hxe : x = u ∨ x = v := hdisj x hx_p hx_q
    have hye : y = u ∨ y = v := hdisj y hy_p hy_q
    have hsuv_p : s(u, v) ∈ p.edges := by
      rcases hxe with rfl | rfl <;> rcases hye with rfl | rfl
      · exact False.elim (hxy_ne rfl)
      · exact hxy1
      · rwa [Sym2.eq_swap] at hxy1
      · exact False.elim (hxy_ne rfl)
    have hsuv_q : s(u, v) ∈ q.edges := by
      rcases hxe with rfl | rfl <;> rcases hye with rfl | rfl
      · exact False.elim (hxy_ne rfl)
      · exact hxy2
      · rwa [Sym2.eq_swap] at hxy2
      · exact False.elim (hxy_ne rfl)
    have hp_one := isPath_mem_edges_endpoints_length_one p hp hsuv_p
    have hq_one := isPath_mem_edges_endpoints_length_one q hq hsuv_q
    omega
  · intro hnil
    have h0 : (p.append q.reverse).length = 0 := by rw [hnil]; rfl
    rw [Walk.length_append, Walk.length_reverse] at h0; omega
  · have hsupp : c.support = p.support ++ q.reverse.support.tail := Walk.support_append p q.reverse
    have htail : c.support.tail = p.support.tail ++ q.reverse.support.tail := by
      rw [hsupp]; cases p with
      | nil => simp at hp1
      | cons _ _ => simp [Walk.support_cons]
    rw [htail, List.nodup_append]
    have hp_tail_nd : p.support.tail.Nodup := by
      cases p with | nil => simp at hp1 | cons _ _ => exact (List.nodup_cons.mp hp.support_nodup).2
    have hqr_tail_nd : q.reverse.support.tail.Nodup := by
      cases hqr : q.reverse with
      | nil => rw [hqr] at hqr_len; simp at hqr_len
      | cons _ _ => have hnd := hqr_path.support_nodup; rw [hqr] at hnd; exact (List.nodup_cons.mp hnd).2
    refine ⟨hp_tail_nd, hqr_tail_nd, ?_⟩
    intro w hw1 w' hw2 heq; subst heq
    have hw_p : w ∈ p.support := by
      cases p with | nil => simp at hp1 | cons _ _ => exact List.mem_cons_of_mem _ hw1
    have hw_qr : w ∈ q.reverse.support := by
      cases hqr : q.reverse with | nil => rw [hqr] at hqr_len; simp at hqr_len | cons _ _ => rw [hqr] at hw2; exact List.mem_cons_of_mem _ hw2
    have hw_q : w ∈ q.support := by simpa [Walk.support_reverse] using hw_qr
    rcases hdisj w hw_p hw_q with rfl | rfl
    · cases p with | nil => simp at hp1 | cons _ _ => exact (List.nodup_cons.mp hp.support_nodup).1 hw1
    · cases hqr : q.reverse with
      | nil => rw [hqr] at hqr_len; simp at hqr_len
      | cons _ _ => have hnd := hqr_path.support_nodup; rw [hqr] at hnd; rw [hqr] at hw2; exact (List.nodup_cons.mp hnd).1 hw2

lemma powerfree_common_neighbors_le_one {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hpf : PowerFree G) {x y : V} (hxy : x ≠ y) :
    ((G.neighborFinset x) ∩ (G.neighborFinset y)).card ≤ 1 := by
  by_contra hgt; push_neg at hgt
  rcases Finset.one_lt_card.mp hgt with ⟨u, hu, v, hv, huv⟩
  rcases Finset.mem_inter.mp hu with ⟨hux, huy⟩
  rcases Finset.mem_inter.mp hv with ⟨hvx, hvy⟩
  rw [SimpleGraph.mem_neighborFinset] at hux huy hvx hvy
  let p1 : G.Walk x y := Walk.cons hux (Walk.cons huy.symm Walk.nil)
  let p2 : G.Walk x y := Walk.cons hvx (Walk.cons hvy.symm Walk.nil)
  have hp1 : p1.IsPath := Walk.IsPath.mk' (by
    simp only [p1, Walk.support_cons, Walk.support_nil, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
    exact ⟨⟨G.ne_of_adj hux, hxy⟩, G.ne_of_adj huy.symm⟩)
  have hp2 : p2.IsPath := Walk.IsPath.mk' (by
    simp only [p2, Walk.support_cons, Walk.support_nil, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
    exact ⟨⟨G.ne_of_adj hvx, hxy⟩, G.ne_of_adj hvy.symm⟩)
  have hdisj : ∀ w, w ∈ p1.support → w ∈ p2.support → w = x ∨ w = y := by
    intro w hw1 hw2
    simp only [p1, p2, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hw1 hw2
    rcases hw1 with rfl | rfl | rfl
    · exact Or.inl rfl
    · rcases hw2 with h | h | h
      · exact Or.inl h
      · exact False.elim (huv h)
      · exact Or.inr h
    · exact Or.inr rfl
  rcases two_internally_disjoint_paths_cycle p1 p2 hp1 hp2 (by simp [p1]) (by simp [p2])
      (by simp [p1, p2]) hdisj with ⟨hc, hcl⟩
  exact hpf ⟨x, p1.append p2.reverse, hc, 2, le_rfl, by simpa [p1, p2] using hcl⟩

def identGraph {V : Type*} (G : SimpleGraph V) (x y : V) :
    SimpleGraph {w : V // w ≠ y} where
  Adj u v := u ≠ v ∧ (G.Adj u.1 v.1 ∨ (u.1 = x ∧ G.Adj y v.1) ∨ (v.1 = x ∧ G.Adj u.1 y))
  symm := by
    intro u v ⟨hne, h⟩; refine ⟨hne.symm, ?_⟩
    rcases h with h | ⟨rfl, hy⟩ | ⟨rfl, hy⟩
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr ⟨rfl, hy.symm⟩)
    · exact Or.inr (Or.inl ⟨rfl, hy.symm⟩)
  loopless := fun _ ⟨hne, _⟩ => hne rfl

lemma identGraph_walk_lift {V : Type*} {G : SimpleGraph V} {x y : V} (hxy : x ≠ y)
    {u v : {w : V // w ≠ y}} (p : (identGraph G x y).Walk u v)
    (havoid : ⟨x, hxy⟩ ∉ p.support) :
    ∃ q : G.Walk u.1 v.1, q.length = p.length ∧ q.support = p.support.map Subtype.val ∧
      q.edges = p.edges.map (Sym2.map Subtype.val) := by
  induction p with
  | nil => exact ⟨Walk.nil, rfl, rfl, rfl⟩
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

lemma identGraph_cycle_lifts_to_dyadic_path {V : Type*} {G : SimpleGraph V}
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
      have hrest_nodup : rest.support.Nodup := by have := hc.support_nodup; simpa using this
      let rev := rest.reverse
      cases hrev : rev with
      | nil =>
        have hlen0 : rest.length = 0 := by have := congrArg Walk.length hrev; simpa [rev] using this
        have h3 := hc.three_le_length; simp only [Walk.length_cons, hlen0] at h3; omega
      | @cons _ d _ hzd mid =>
        have hrev_nodup : rev.support.Nodup := by
          rw [← List.nodup_reverse, ← Walk.support_reverse]; simpa [rev] using hrest_nodup
        rw [hrev] at hrev_nodup
        have hz_not_mid : z ∉ mid.support := (List.nodup_cons.mp hrev_nodup).1
        rcases identGraph_walk_lift hxy mid hz_not_mid with ⟨q, hqlen, hqsupp, _⟩
        have hq_nodup : q.support.Nodup := by
          rw [hqsupp]; exact ((List.nodup_cons.mp hrev_nodup).2).map Subtype.val_injective
        have hy_not_q : y ∉ q.support := by
          rw [hqsupp]; intro hy_in; rcases List.mem_map.mp hy_in with ⟨w, _, hwy⟩; exact w.2 hwy
        have hx_not_q : x ∉ q.support := by
          rw [hqsupp]; intro hx_in; rcases List.mem_map.mp hx_in with ⟨w, hw, hwx⟩
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
          have hcyc_len : cyc.length = (Walk.cons hzb rest).length := by simp [cyc, Walk.length_concat, hqlen_eq]
          have hcyc_is : cyc.IsCycle := by
            rw [Walk.isCycle_def]
            refine ⟨?_, by simp [cyc], ?_⟩
            · rw [Walk.isTrail_def]
              have hq_path : q.IsPath := Walk.IsPath.mk' hq_nodup
              have hq_edges_nodup : q.edges.Nodup := hq_path.isTrail.edges_nodup
              have hw_not_edges : ∀ e ∈ q.edges, w ∉ e := fun e he hwe =>
                hw_not (mem_support_of_edge q he hwe)
              have hdb_ne : d.1 ≠ b.1 := by
                intro heq
                have hq0 : q.length = 0 := by
                  cases q with
                  | nil => rfl
                  | @cons _ next _ h1 q' =>
                    have hnd := List.nodup_cons.mp hq_nodup
                    have hlast_in : b.1 ∈ q'.support := Walk.end_mem_support q'
                    rw [← heq] at hlast_in; exact False.elim (hnd.1 hlast_in)
                omega
              simp only [cyc, Walk.edges_cons, Walk.edges_concat, List.nodup_cons,
                List.mem_append, List.mem_singleton, not_or]
              refine ⟨⟨fun h => hw_not_edges _ h (by simp), ?_⟩, ?_⟩
              · intro heq; rw [Sym2.eq_iff] at heq
                rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                · exact G.ne_of_adj hwd rfl
                · exact hdb_ne rfl
              · rw [List.nodup_append]
                refine ⟨hq_edges_nodup, List.nodup_singleton _, ?_⟩
                intro e he e' he' heq
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
          · have : path.length = (Walk.cons hzb rest).length := by simp [path, Walk.length_concat, hqlen_eq]
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
      rw [Walk.isCycle_def]; refine ⟨?_, ?_, ?_⟩
      · rw [Walk.isTrail_def, hqedges]
        exact hc0.isTrail.edges_nodup.map (Sym2.map.injective Subtype.val_injective)
      · intro hnil; have : c0.length = 0 := by rw [← hqlen, hnil]; rfl
        have := hc0.three_le_length; omega
      · rw [hqsupp, List.tail_map]; exact hc0.support_nodup.map Subtype.val_injective
    exact False.elim (hpf ⟨v0.1, q, hq_cyc, hqlen ▸ hpow⟩)

lemma identGraph_degree_other_no_common {V : Type*} [Fintype V] (G : SimpleGraph V)
    {x y : V} (hxy : x ≠ y) (u : {w : V // w ≠ y}) (hux : u.1 ≠ x)
    (hnot_comm : ¬ (G.Adj u.1 x ∧ G.Adj u.1 y)) :
    (identGraph G x y).degree u = G.degree u.1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun v _ => if v.1 = x ∧ G.Adj u.1 y then y else v.1)
  · intro v hv; simp only [SimpleGraph.mem_neighborFinset, identGraph] at hv ⊢
    split_ifs with h
    · exact h.2
    · rcases hv.2 with hadj | ⟨hux', _⟩ | ⟨hvx, huy⟩
      · exact hadj
      · exact False.elim (hux hux')
      · exact False.elim (h ⟨hvx, huy⟩)
  · intro v1 hv1 v2 hv2 heq
    simp only [SimpleGraph.mem_neighborFinset, identGraph] at hv1 hv2
    split_ifs at heq with h1 h2
    · exact Subtype.ext (h1.1.trans h2.1.symm)
    · exact False.elim (v2.2 heq.symm)
    · exact False.elim (v1.2 heq)
    · exact Subtype.ext heq
  · intro w hw; rw [SimpleGraph.mem_neighborFinset] at hw
    by_cases hwy : w = y
    · subst hwy; refine ⟨⟨x, hxy⟩, ?_, by simp [hw]⟩
      simp only [SimpleGraph.mem_neighborFinset, identGraph]
      exact ⟨fun h => hux (congrArg Subtype.val h), Or.inr (Or.inr ⟨rfl, hw⟩)⟩
    · refine ⟨⟨w, hwy⟩, ?_, ?_⟩
      · simp only [SimpleGraph.mem_neighborFinset, identGraph]
        exact ⟨fun h => G.ne_of_adj hw (congrArg Subtype.val h), Or.inl hw⟩
      · split_ifs with h
        · exact False.elim (hnot_comm ⟨h.1 ▸ hw, h.2⟩)
        · rfl

lemma identGraph_degree_other_common {V : Type*} [Fintype V] (G : SimpleGraph V)
    {x y : V} (hxy : x ≠ y) (u : {w : V // w ≠ y}) (hux : u.1 ≠ x)
    (hcomm : G.Adj u.1 x ∧ G.Adj u.1 y) :
    (identGraph G x y).degree u + 1 = G.degree u.1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  have hy_in : y ∈ G.neighborFinset u.1 := SimpleGraph.mem_neighborFinset.mpr hcomm.2
  rw [← Finset.card_erase_add_one hy_in]; congr 1
  apply Finset.card_bij (fun v _ => v.1)
  · intro v hv; simp only [SimpleGraph.mem_neighborFinset, identGraph, Finset.mem_erase] at hv ⊢
    refine ⟨v.2, ?_⟩
    rcases hv.2 with hadj | ⟨hux', _⟩ | ⟨hvx, _⟩
    · exact hadj
    · exact False.elim (hux hux')
    · exact hvx ▸ hcomm.1
  · intro _ _ _ _ h; exact Subtype.ext h
  · intro w hw; simp only [Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hw
    refine ⟨⟨w, hw.1⟩, ?_, rfl⟩
    simp only [SimpleGraph.mem_neighborFinset, identGraph]
    exact ⟨fun h => G.ne_of_adj hw.2 (congrArg Subtype.val h), Or.inl hw.2⟩

lemma identGraph_degree_merged {V : Type*} [Fintype V] (G : SimpleGraph V)
    {x y : V} (hxy : x ≠ y) :
    (identGraph G x y).degree ⟨x, hxy⟩ =
      (((G.neighborFinset x) ∪ (G.neighborFinset y)) \ {x, y}).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun v _ => v.1)
  · intro v hv
    simp only [SimpleGraph.mem_neighborFinset, identGraph, Finset.mem_sdiff, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton, not_or] at hv ⊢
    refine ⟨?_, fun h => hv.1 (Subtype.ext h.symm), v.2⟩
    rcases hv.2 with h | ⟨_, hy⟩ | ⟨hvx, _⟩
    · exact Or.inl h
    · exact Or.inr hy
    · exact False.elim (hv.1 (Subtype.ext hvx.symm))
  · intro _ _ _ _ h; exact Subtype.ext h
  · intro w hw
    simp only [Finset.mem_sdiff, Finset.mem_union, SimpleGraph.mem_neighborFinset,
      Finset.mem_insert, Finset.mem_singleton, not_or] at hw
    refine ⟨⟨w, hw.2.2⟩, ?_, rfl⟩
    simp only [SimpleGraph.mem_neighborFinset, identGraph]
    refine ⟨fun h => hw.2.1 (congrArg Subtype.val h).symm, ?_⟩
    rcases hw.1 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨rfl, h⟩)

/-- PILLAR 4.1: High-Apex Triangle Base-Edge `(2^k + 1)`-Cycle Forcing. -/
theorem minimal_bad2_high_apex_triangle_base_dyadic_plus_one_cycle {V : Type} [Fintype V]
    {G : SimpleGraph V} (hG : MinimalBad2 G) {h u v : V}
    (hhu : G.Adj h u) (hhv : G.Adj h v) (huv : G.Adj u v)
    (hh4 : h ∈ VGe4 G) (hu3 : u ∈ V3 G) (hv3 : v ∈ V3 G) :
    ∃ (c : G.Walk u u), c.IsCycle ∧ s(u, v) ∈ c.edges ∧ ∃ k : ℕ, 2 ≤ k ∧ c.length = 2 ^ k + 1 := by
  have huv_ne : u ≠ v := G.ne_of_adj huv
  have hhu_ne : h ≠ u := G.ne_of_adj hhu
  have hhv_ne : h ≠ v := G.ne_of_adj hhv
  have hcomm_uniq : ∀ w : V, G.Adj w u → G.Adj w v → w = h := by
    intro w hwu hwv; by_contra hwh
    have hw_in : w ∈ (G.neighborFinset u) ∩ (G.neighborFinset v) :=
      Finset.mem_inter.mpr ⟨SimpleGraph.mem_neighborFinset.mpr hwu.symm, SimpleGraph.mem_neighborFinset.mpr hwv.symm⟩
    have hh_in : h ∈ (G.neighborFinset u) ∩ (G.neighborFinset v) :=
      Finset.mem_inter.mpr ⟨SimpleGraph.mem_neighborFinset.mpr hhu.symm, SimpleGraph.mem_neighborFinset.mpr hhv.symm⟩
    have h2 : 2 ≤ ((G.neighborFinset u) ∩ (G.neighborFinset v)).card := by
      have := Finset.card_le_card (show ({w, h} : Finset V) ⊆ _ by
        intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> assumption)
      rw [Finset.card_pair hwh] at this; exact this
    have h1 := powerfree_common_neighbors_le_one hG.1.1 huv_ne; omega
  let H := identGraph G u v
  have hdeg_z : H.degree ⟨u, huv_ne⟩ = 3 := by
    rw [identGraph_degree_merged]
    have hinter : (G.neighborFinset u) ∩ (G.neighborFinset v) = {h} := by
      ext w; simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2⟩; exact hcomm_uniq w h1.symm h2.symm
      · rintro rfl; exact ⟨hhu.symm, hhv.symm⟩
    have hunion_card : ((G.neighborFinset u) ∪ (G.neighborFinset v)).card = 5 := by
      have h1 := Finset.card_union_add_card_inter (G.neighborFinset u) (G.neighborFinset v)
      rw [hinter, Finset.card_singleton, SimpleGraph.card_neighborFinset_eq_degree,
          SimpleGraph.card_neighborFinset_eq_degree,
          (Finset.mem_filter.mp hu3).2, (Finset.mem_filter.mp hv3).2] at h1; omega
    have hsub_uv : ({u, v} : Finset V) ⊆ (G.neighborFinset u) ∪ (G.neighborFinset v) := by
      intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      simp only [Finset.mem_union, SimpleGraph.mem_neighborFinset]
      rcases hw with rfl | rfl
      · exact Or.inr huv.symm
      · exact Or.inl huv
    have hsd := Finset.card_sdiff_add_card_eq_card hsub_uv
    rw [Finset.card_pair huv_ne, hunion_card] at hsd; omega
  have hdeg_h : 3 ≤ H.degree ⟨h, hhv_ne⟩ := by
    have h1 := identGraph_degree_other_common G huv_ne ⟨h, hhv_ne⟩ hhu_ne ⟨hhu, hhv⟩
    have h4 : 4 ≤ G.degree h := (Finset.mem_filter.mp hh4).2; omega
  have hdeg_other : ∀ w : {z : V // z ≠ v}, w.1 ≠ u → w.1 ≠ h → H.degree w = G.degree w.1 := by
    intro w hwu hwh; apply identGraph_degree_other_no_common G huv_ne w hwu
    rintro ⟨h1, h2⟩; exact hwh (hcomm_uniq w.1 h1 h2)
  have hH_not_pf : ¬ PowerFree H := by
    intro hH_pf
    have hH_min : MinDegGe H 2 := by
      intro w
      by_cases hwu : w.1 = u
      · have : w = ⟨u, huv_ne⟩ := Subtype.ext hwu; rw [this, hdeg_z]; omega
      · by_cases hwh : w.1 = h
        · have : w = ⟨h, hhv_ne⟩ := Subtype.ext hwh; rw [this]; omega
        · rw [hdeg_other w hwu hwh]; exact hG.1.2.1 w.1
    have hH_def : (Defects H).card ≤ 2 := by
      have hcard_le : (Defects H).card ≤ (Defects G).card := by
        apply Finset.card_le_card_of_injOn Subtype.val
        · intro w hw
          simp only [Defects, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
          by_cases hwu : w.1 = u
          · have : w = ⟨u, huv_ne⟩ := Subtype.ext hwu; rw [this, hdeg_z] at hw; omega
          · by_cases hwh : w.1 = h
            · have : w = ⟨h, hhv_ne⟩ := Subtype.ext hwh; rw [this] at hw; omega
            · rw [← hdeg_other w hwu hwh]; exact hw
        · intro _ _ _ _ heq; exact Subtype.ext heq
      exact le_trans hcard_le hG.1.2.2
    have hlt : Fintype.card {z : V // z ≠ v} < Fintype.card V := by
      rw [Fintype.card_subtype_compl, Fintype.card_unique]
      have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨u⟩; omega
    exact minimal_bad2_no_smaller hG H ⟨hH_pf, hH_min, hH_def⟩ hlt
  have hcyc : HasPowerCycle H := not_not.mp hH_not_pf
  rcases identGraph_cycle_lifts_to_dyadic_path hG.1.1 huv_ne hcyc with ⟨p, hp, k, hk2, hplen⟩
  let c : G.Walk u u := Walk.cons huv p.reverse
  have hge4 : 4 ≤ 2 ^ k := calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
  have hc_is : c.IsCycle := by
    rw [Walk.isCycle_def]; refine ⟨?_, by simp [c], ?_⟩
    · rw [Walk.isTrail_def]; simp only [c, Walk.edges_cons, List.nodup_cons]
      refine ⟨?_, hp.reverse.isTrail.edges_nodup⟩
      intro hmem
      have hmem_p : s(u, v) ∈ p.edges := by simpa [Walk.edges_reverse] using hmem
      have h1 := isPath_mem_edges_endpoints_length_one p hp hmem_p; omega
    · simp only [c, Walk.support_cons, List.tail_cons]; exact hp.reverse.support_nodup
  exact ⟨c, hc_is, by simp [c], k, hk2, by simp [c, Walk.length_reverse, hplen]⟩

/-- PILLAR 4.2: Pure Cubic Triangle External-Neighborhood Obstruction. -/
theorem minimal_bad2_cubic_triangle_external_not_all_high {V : Type} [Fintype V]
    {G : SimpleGraph V} (hG : MinimalBad2 G) {u v w xu xv xw : V}
    (hNu : G.neighborFinset u = {v, w, xu})
    (hNv : G.neighborFinset v = {u, w, xv})
    (hNw : G.neighborFinset w = {u, v, xw})
    (huv_ne : u ≠ v) (hvw_ne : v ≠ w) (hwu_ne : w ≠ u) :
    ¬ (xu ∈ VGe4 G ∧ xv ∈ VGe4 G ∧ xw ∈ VGe4 G) := by
  rintro ⟨hxu4, hxv4, hxw4⟩
  let K : Finset V := {u, v, w}
  have hK_le1 : ∀ z ∈ Kᶜ, ((G.neighborFinset z) ∩ K).card ≤ 1 := by
    intro z hz; by_contra hgt; push_neg at hgt
    rcases Finset.one_lt_card.mp hgt with ⟨k1, hk1, k2, hk2, hk12⟩
    rcases Finset.mem_inter.mp hk1 with ⟨hk1N, hk1K⟩
    rcases Finset.mem_inter.mp hk2 with ⟨hk2N, hk2K⟩
    have hadj1 : G.Adj z k1 := SimpleGraph.mem_neighborFinset.mp hk1N
    have hadj2 : G.Adj z k2 := SimpleGraph.mem_neighborFinset.mp hk2N
    have hz_notK : z ∉ K := Finset.mem_compl.mp hz
    have htri : ∀ a b c : V, a ≠ b → c ≠ z → G.Adj a c → G.Adj b c → G.Adj z a → G.Adj z b → False := by
      intro a b c hab hcz hac hbc hza hzb
      have h1 : c ∈ (G.neighborFinset a) ∩ (G.neighborFinset b) :=
        Finset.mem_inter.mpr ⟨SimpleGraph.mem_neighborFinset.mpr hac, SimpleGraph.mem_neighborFinset.mpr hbc⟩
      have h2 : z ∈ (G.neighborFinset a) ∩ (G.neighborFinset b) :=
        Finset.mem_inter.mpr ⟨SimpleGraph.mem_neighborFinset.mpr hza.symm, SimpleGraph.mem_neighborFinset.mpr hzb.symm⟩
      have hcard2 : 2 ≤ ((G.neighborFinset a) ∩ (G.neighborFinset b)).card := by
        have := Finset.card_le_card (show ({c, z} : Finset V) ⊆ _ by
          intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl <;> assumption)
        rw [Finset.card_pair hcz] at this; exact this
      have hle1 := powerfree_common_neighbors_le_one hG.1.1 hab; omega
    have huv : G.Adj u v := SimpleGraph.mem_neighborFinset.mp (by rw [hNu]; simp)
    have hvw : G.Adj v w := SimpleGraph.mem_neighborFinset.mp (by rw [hNv]; simp)
    have hwu : G.Adj w u := SimpleGraph.mem_neighborFinset.mp (by rw [hNw]; simp)
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at hk1K hk2K
    rcases hk1K with rfl | rfl | rfl <;> rcases hk2K with rfl | rfl | rfl
    · exact hk12 rfl
    · exact htri u v w huv_ne (fun h => hz_notK (by simp [K, h])) hwu.symm hvw hadj1 hadj2
    · exact htri u w v hwu_ne.symm (fun h => hz_notK (by simp [K, h])) huv hvw.symm hadj1 hadj2
    · exact htri v u w huv_ne.symm (fun h => hz_notK (by simp [K, h])) hvw hwu.symm hadj1 hadj2
    · exact hk12 rfl
    · exact htri v w u hvw_ne (fun h => hz_notK (by simp [K, h])) huv.symm hwu hadj1 hadj2
    · exact htri w u v hwu_ne (fun h => hz_notK (by simp [K, h])) hvw.symm huv hadj1 hadj2
    · exact htri w v u hvw_ne.symm (fun h => hz_notK (by simp [K, h])) hwu huv.symm hadj1 hadj2
    · exact hk12 rfl
  have hnb_in_ext : ∀ z ∈ Kᶜ, ((G.neighborFinset z) ∩ K).card ≠ 0 → z = xu ∨ z = xv ∨ z = xw := by
    intro z hz hne0
    rcases Finset.card_pos.mp (Nat.pos_of_ne_zero hne0) with ⟨k, hk⟩
    rcases Finset.mem_inter.mp hk with ⟨hkN, hkK⟩
    have hadj : G.Adj k z := (SimpleGraph.mem_neighborFinset.mp hkN).symm
    have hz_notK : z ∉ K := Finset.mem_compl.mp hz
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at hkK
    rcases hkK with rfl | rfl | rfl
    · have hzN : z ∈ G.neighborFinset u := SimpleGraph.mem_neighborFinset.mpr hadj
      rw [hNu] at hzN; simp only [Finset.mem_insert, Finset.mem_singleton] at hzN
      rcases hzN with rfl | rfl | rfl
      · exact False.elim (hz_notK (by simp [K]))
      · exact False.elim (hz_notK (by simp [K]))
      · exact Or.inl rfl
    · have hzN : z ∈ G.neighborFinset v := SimpleGraph.mem_neighborFinset.mpr hadj
      rw [hNv] at hzN; simp only [Finset.mem_insert, Finset.mem_singleton] at hzN
      rcases hzN with rfl | rfl | rfl
      · exact False.elim (hz_notK (by simp [K]))
      · exact False.elim (hz_notK (by simp [K]))
      · exact Or.inr (Or.inl rfl)
    · have hzN : z ∈ G.neighborFinset w := SimpleGraph.mem_neighborFinset.mpr hadj
      rw [hNw] at hzN; simp only [Finset.mem_insert, Finset.mem_singleton] at hzN
      rcases hzN with rfl | rfl | rfl
      · exact False.elim (hz_notK (by simp [K]))
      · exact False.elim (hz_notK (by simp [K]))
      · exact Or.inr (Or.inr rfl)
  apply minimal_bad2_no_safe_deletion hG K ⟨u, by simp [K]⟩
  · intro z hz
    have hsum := degree_compl_eq_sub G K z
    by_cases h0 : ((G.neighborFinset z) ∩ K).card = 0
    · have := hG.1.2.1 z; omega
    · have h1 := hK_le1 z hz
      rcases hnb_in_ext z hz h0 with rfl | rfl | rfl
      · have := (Finset.mem_filter.mp hxu4).2; omega
      · have := (Finset.mem_filter.mp hxv4).2; omega
      · have := (Finset.mem_filter.mp hxw4).2; omega
  · have hsub : (Kᶜ.filter (fun z => ((G.neighborFinset z) ∩ Kᶜ).card = 2)) ⊆ Defects G := by
      intro z hz; rcases Finset.mem_filter.mp hz with ⟨hzK, hz2⟩
      have hsum := degree_compl_eq_sub G K z
      by_cases h0 : ((G.neighborFinset z) ∩ K).card = 0
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
      · have h1 := hK_le1 z hzK
        rcases hnb_in_ext z hzK h0 with rfl | rfl | rfl
        · have := (Finset.mem_filter.mp hxu4).2; omega
        · have := (Finset.mem_filter.mp hxv4).2; omega
        · have := (Finset.mem_filter.mp hxw4).2; omega
    exact le_trans (Finset.card_le_card hsub) hG.1.2.2

def contractTriangle {V : Type*} (G : SimpleGraph V) (u v w : V) :
    SimpleGraph {z : V // z ≠ v ∧ z ≠ w} where
  Adj a b := a ≠ b ∧ (G.Adj a.1 b.1 ∨
    (a.1 = u ∧ (G.Adj v b.1 ∨ G.Adj w b.1)) ∨
    (b.1 = u ∧ (G.Adj a.1 v ∨ G.Adj a.1 w)))
  symm := by
    intro a b ⟨hne, h⟩; refine ⟨hne.symm, ?_⟩
    rcases h with h | ⟨rfl, h1 | h2⟩ | ⟨rfl, h1 | h2⟩
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr ⟨rfl, Or.inl h1.symm⟩)
    · exact Or.inr (Or.inr ⟨rfl, Or.inr h2.symm⟩)
    · exact Or.inr (Or.inl ⟨rfl, Or.inl h1.symm⟩)
    · exact Or.inr (Or.inl ⟨rfl, Or.inr h2.symm⟩)
  loopless := fun _ ⟨hne, _⟩ => hne rfl

lemma contractTriangle_walk_lift {V : Type*} {G : SimpleGraph V} {u v w : V}
    (huv : u ≠ v) (huw : u ≠ w)
    {a b : {z : V // z ≠ v ∧ z ≠ w}} (p : (contractTriangle G u v w).Walk a b)
    (havoid : ⟨u, ⟨huv, huw⟩⟩ ∉ p.support) :
    ∃ q : G.Walk a.1 b.1, q.length = p.length ∧ q.support = p.support.map Subtype.val ∧
      q.edges = p.edges.map (Sym2.map Subtype.val) := by
  induction p with
  | nil => exact ⟨Walk.nil, rfl, rfl, rfl⟩
  | @cons x y z hxy rest ih =>
    have hx_ne : x ≠ ⟨u, ⟨huv, huw⟩⟩ := fun h => havoid (by simp [h])
    have hy_ne : y ≠ ⟨u, ⟨huv, huw⟩⟩ := fun h => havoid (by simp [h])
    have havoid' : ⟨u, ⟨huv, huw⟩⟩ ∉ rest.support := fun h => havoid (List.mem_cons_of_mem _ h)
    rcases ih havoid' with ⟨q, hlen, hsupp, hedges⟩
    have hadjG : G.Adj x.1 y.1 := by
      rcases hxy.2 with h | ⟨hxu, _⟩ | ⟨hyu, _⟩
      · exact h
      · exact False.elim (hx_ne (Subtype.ext hxu))
      · exact False.elim (hy_ne (Subtype.ext hyu))
    exact ⟨Walk.cons hadjG q, by simp [hlen], by simp [hsupp], by simp [hedges]⟩

/-- PILLAR 4.3: Pure Cubic Triangle Dual-Cycle Lifting Theorem. -/
theorem minimal_bad2_cubic_triangle_dual_cycle_lifting {V : Type} [Fintype V]
    {G : SimpleGraph V} (hG : MinimalBad2 G) {u v w xu xv xw : V}
    (hNu : G.neighborFinset u = {v, w, xu})
    (hNv : G.neighborFinset v = {u, w, xv})
    (hNw : G.neighborFinset w = {u, v, xw})
    (huv_ne : u ≠ v) (hvw_ne : v ≠ w) (hwu_ne : w ≠ u)
    (hxu_not : xu ∉ ({u, v, w} : Finset V))
    (hxv_not : xv ∉ ({u, v, w} : Finset V))
    (hxw_not : xw ∉ ({u, v, w} : Finset V)) :
    ∃ (k : ℕ), 2 ≤ k ∧
      (∃ (s1 : V) (c1 : G.Walk s1 s1), c1.IsCycle ∧ c1.length = 2 ^ k + 1) ∧
      (∃ (s2 : V) (c2 : G.Walk s2 s2), c2.IsCycle ∧ c2.length = 2 ^ k + 2) := by
  have huv : G.Adj u v := SimpleGraph.mem_neighborFinset.mp (by rw [hNu]; simp)
  have hvw : G.Adj v w := SimpleGraph.mem_neighborFinset.mp (by rw [hNv]; simp)
  have hwu : G.Adj w u := SimpleGraph.mem_neighborFinset.mp (by rw [hNw]; simp)
  have huxu : G.Adj u xu := SimpleGraph.mem_neighborFinset.mp (by rw [hNu]; simp)
  have hvxv : G.Adj v xv := SimpleGraph.mem_neighborFinset.mp (by rw [hNv]; simp)
  have hwxw : G.Adj w xw := SimpleGraph.mem_neighborFinset.mp (by rw [hNw]; simp)
  have htri_disj : ∀ a b c z : V, a ≠ b → c ≠ z → G.Adj a c → G.Adj b c → G.Adj a z → G.Adj b z → False := by
    intro a b c z hab hcz hac hbc haz hbz
    have h1 : c ∈ (G.neighborFinset a) ∩ (G.neighborFinset b) :=
      Finset.mem_inter.mpr ⟨SimpleGraph.mem_neighborFinset.mpr hac, SimpleGraph.mem_neighborFinset.mpr hbc⟩
    have h2 : z ∈ (G.neighborFinset a) ∩ (G.neighborFinset b) :=
      Finset.mem_inter.mpr ⟨SimpleGraph.mem_neighborFinset.mpr haz, SimpleGraph.mem_neighborFinset.mpr hbz⟩
    have hcard2 : 2 ≤ ((G.neighborFinset a) ∩ (G.neighborFinset b)).card := by
      have := Finset.card_le_card (show ({c, z} : Finset V) ⊆ _ by
        intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl <;> assumption)
      rw [Finset.card_pair hcz] at this; exact this
    have hle1 := powerfree_common_neighbors_le_one hG.1.1 hab; omega
  have hxuv : xu ≠ xv := fun h => htri_disj u v w xu huv_ne (fun he => hxu_not (by simp [he])) hwu.symm hvw huxu (h ▸ hvxv)
  have hxvw : xv ≠ xw := fun h => htri_disj v w u xv hvw_ne (fun he => hxv_not (by simp [he])) huv.symm hwu hvxv (h ▸ hwxw)
  have hxwu : xw ≠ xu := fun h => htri_disj w u v xw hwu_ne (fun he => hxw_not (by simp [he])) hvw.symm huv hwxw (h ▸ huxu)
  let H := contractTriangle G u v w
  let t : {z : V // z ≠ v ∧ z ≠ w} := ⟨u, ⟨huv_ne, hwu_ne.symm⟩⟩
  have hno_two_in_T : ∀ z : V, z ∉ ({u, v, w} : Finset V) →
      ¬ (G.Adj z u ∧ G.Adj z v) ∧ ¬ (G.Adj z v ∧ G.Adj z w) ∧ ¬ (G.Adj z w ∧ G.Adj z u) := by
    intro z hz; refine ⟨?_, ?_, ?_⟩
    · rintro ⟨h1, h2⟩; exact htri_disj u v w z huv_ne (fun he => hz (by simp [he])) hwu.symm hvw h1.symm h2.symm
    · rintro ⟨h1, h2⟩; exact htri_disj v w u z hvw_ne (fun he => hz (by simp [he])) huv.symm hwu h1.symm h2.symm
    · rintro ⟨h1, h2⟩; exact htri_disj w u v z hwu_ne (fun he => hz (by simp [he])) hvw.symm huv h1.symm h2.symm
  have hdeg_other : ∀ a : {z : V // z ≠ v ∧ z ≠ w}, a ≠ t → H.degree a = G.degree a.1 := by
    intro a hat
    have hau : a.1 ≠ u := fun h => hat (Subtype.ext h)
    have ha_notT : a.1 ∉ ({u, v, w} : Finset V) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hau, a.2.1, a.2.2⟩
    have hno2 := hno_two_in_T a.1 ha_notT
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
    apply Finset.card_bij (fun b _ =>
      if b = t ∧ G.Adj a.1 v then v else if b = t ∧ G.Adj a.1 w then w else b.1)
    · intro b hb; simp only [SimpleGraph.mem_neighborFinset, H, contractTriangle] at hb ⊢
      split_ifs with h1 h2
      · exact h1.2
      · exact h2.2
      · rcases hb.2 with hGadj | ⟨h1', _⟩ | ⟨hbu, hvw'⟩
        · exact hGadj
        · exact False.elim (hau h1')
        · have hbt : b = t := Subtype.ext hbu
          rcases hvw' with hv' | hw'
          · exact False.elim (h1 ⟨hbt, hv'⟩)
          · exact False.elim (h2 ⟨hbt, hw'⟩)
    · intro b1 _ b2 _ heq
      split_ifs at heq with h1a h1b h2a h2b h2c h2d
      · exact h1a.1.trans h2a.1.symm
      · exact False.elim (hvw_ne heq)
      · exact False.elim (b2.2.1 heq.symm)
      · exact False.elim (hvw_ne heq.symm)
      · exact h1b.1.trans h2c.1.symm
      · exact False.elim (b2.2.2 heq.symm)
      · exact False.elim (b1.2.1 heq)
      · exact False.elim (b1.2.2 heq)
      · exact Subtype.ext heq
    · intro y hy; rw [SimpleGraph.mem_neighborFinset] at hy
      by_cases hyv : y = v
      · subst hyv; refine ⟨t, ?_, by simp [hy]⟩
        simp only [SimpleGraph.mem_neighborFinset, H, contractTriangle]
        exact ⟨hat, Or.inr (Or.inr ⟨rfl, Or.inl hy⟩)⟩
      · by_cases hyw : y = w
        · subst hyw; refine ⟨t, ?_, ?_⟩
          · simp only [SimpleGraph.mem_neighborFinset, H, contractTriangle]
            exact ⟨hat, Or.inr (Or.inr ⟨rfl, Or.inr hy⟩)⟩
          · have hnotv : ¬ G.Adj a.1 v := fun hv' => hno2.2.1 ⟨hv', hy⟩
            simp [hnotv, hy]
        · refine ⟨⟨y, ⟨hyv, hyw⟩⟩, ?_, ?_⟩
          · simp only [SimpleGraph.mem_neighborFinset, H, contractTriangle]
            exact ⟨fun h => G.ne_of_adj hy (congrArg Subtype.val h), Or.inl hy⟩
          · by_cases hyu : y = u
            · subst hyu
              have hnotv : ¬ G.Adj a.1 v := fun hv' => hno2.1 ⟨hy, hv'⟩
              have hnotw : ¬ G.Adj a.1 w := fun hw' => hno2.2.2 ⟨hw', hy⟩
              simp [hnotv, hnotw]
            · have hnet : (⟨y, ⟨hyv, hyw⟩⟩ : {z : V // z ≠ v ∧ z ≠ w}) ≠ t :=
                fun h => hyu (congrArg Subtype.val h)
              simp [hnet]
  have hdeg_t : H.degree t = 3 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have hxu_ok : xu ≠ v ∧ xu ≠ w := ⟨fun h => hxu_not (by simp [h]), fun h => hxu_not (by simp [h])⟩
    have hxv_ok : xv ≠ v ∧ xv ≠ w := ⟨fun h => hxv_not (by simp [h]), fun h => hxv_not (by simp [h])⟩
    have hxw_ok : xw ≠ v ∧ xw ≠ w := ⟨fun h => hxw_not (by simp [h]), fun h => hxw_not (by simp [h])⟩
    have heq : H.neighborFinset t = {⟨xu, hxu_ok⟩, ⟨xv, hxv_ok⟩, ⟨xw, hxw_ok⟩} := by
      ext b; simp only [SimpleGraph.mem_neighborFinset, H, contractTriangle, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hnet, hGadj | ⟨_, hv' | hw'⟩ | ⟨hbu, _⟩⟩
        · have hbN : b.1 ∈ G.neighborFinset u := SimpleGraph.mem_neighborFinset.mpr hGadj
          rw [hNu] at hbN; simp only [Finset.mem_insert, Finset.mem_singleton] at hbN
          rcases hbN with h | h | h
          · exact False.elim (b.2.1 h)
          · exact False.elim (b.2.2 h)
          · exact Or.inl (Subtype.ext h)
        · have hbN : b.1 ∈ G.neighborFinset v := SimpleGraph.mem_neighborFinset.mpr hv'
          rw [hNv] at hbN; simp only [Finset.mem_insert, Finset.mem_singleton] at hbN
          rcases hbN with h | h | h
          · exact False.elim (hnet (Subtype.ext h.symm))
          · exact False.elim (b.2.2 h)
          · exact Or.inr (Or.inl (Subtype.ext h))
        · have hbN : b.1 ∈ G.neighborFinset w := SimpleGraph.mem_neighborFinset.mpr hw'
          rw [hNw] at hbN; simp only [Finset.mem_insert, Finset.mem_singleton] at hbN
          rcases hbN with h | h | h
          · exact False.elim (hnet (Subtype.ext h.symm))
          · exact False.elim (b.2.1 h)
          · exact Or.inr (Or.inr (Subtype.ext h))
        · exact False.elim (hnet (Subtype.ext hbu.symm))
      · rintro (rfl | rfl | rfl)
        · exact ⟨fun h => hxu_not (by simp [congrArg Subtype.val h]), Or.inl huxu⟩
        · exact ⟨fun h => hxv_not (by simp [congrArg Subtype.val h]), Or.inr (Or.inl ⟨rfl, Or.inl hvxv⟩)⟩
        · exact ⟨fun h => hxw_not (by simp [congrArg Subtype.val h]), Or.inr (Or.inl ⟨rfl, Or.inr hwxw⟩)⟩
    rw [heq]
    have h12 : (⟨xu, hxu_ok⟩ : {z : V // z ≠ v ∧ z ≠ w}) ≠ ⟨xv, hxv_ok⟩ := fun h => hxuv (congrArg Subtype.val h)
    have h13 : (⟨xu, hxu_ok⟩ : {z : V // z ≠ v ∧ z ≠ w}) ≠ ⟨xw, hxw_ok⟩ := fun h => hxwu (congrArg Subtype.val h).symm
    have h23 : (⟨xv, hxv_ok⟩ : {z : V // z ≠ v ∧ z ≠ w}) ≠ ⟨xw, hxw_ok⟩ := fun h => hxvw (congrArg Subtype.val h)
    rw [Finset.card_insert_of_notMem (by simp [h12, h13]), Finset.card_pair h23]
  have hH_not_pf : ¬ PowerFree H := by
    intro hH_pf
    have hH_min : MinDegGe H 2 := by
      intro a; by_cases hat : a = t
      · rw [hat, hdeg_t]; omega
      · rw [hdeg_other a hat]; exact hG.1.2.1 a.1
    have hH_def : (Defects H).card ≤ 2 := by
      have hcard_le : (Defects H).card ≤ (Defects G).card := by
        apply Finset.card_le_card_of_injOn Subtype.val
        · intro a ha; simp only [Defects, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
          by_cases hat : a = t
          · rw [hat, hdeg_t] at ha; omega
          · rw [← hdeg_other a hat]; exact ha
        · intro _ _ _ _ heq; exact Subtype.ext heq
      exact le_trans hcard_le hG.1.2.2
    have hlt : Fintype.card {z : V // z ≠ v ∧ z ≠ w} < Fintype.card V := by
      have hcard_eq : Fintype.card {z : V // z ≠ v ∧ z ≠ w} = (({v, w} : Finset V)ᶜ).card := by
        rw [← Fintype.card_coe]
        exact Fintype.card_congr
          { toFun := fun a => ⟨a.1, by simp [a.2.1, a.2.2]⟩
            invFun := fun a => ⟨a.1, by
              have := a.2; simp only [Finset.mem_coe, Finset.mem_compl, Finset.mem_insert,
                Finset.mem_singleton, not_or] at this; exact this⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
      rw [hcard_eq]; have h1 := Finset.card_compl_add_card ({v, w} : Finset V)
      rw [Finset.card_pair hvw_ne] at h1; omega
    exact minimal_bad2_no_smaller hG H ⟨hH_pf, hH_min, hH_def⟩ hlt
  have hcyc : HasPowerCycle H := not_not.mp hH_not_pf
  rcases hcyc with ⟨v0, c0, hc0, k, hk2, hc0len⟩
  have ht_in : t ∈ c0.support := by
    by_contra havoid
    rcases contractTriangle_walk_lift huv_ne hwu_ne.symm c0 havoid with ⟨q, hqlen, hqsupp, hqedges⟩
    have hq_cyc : q.IsCycle := by
      rw [Walk.isCycle_def]; refine ⟨?_, ?_, ?_⟩
      · rw [Walk.isTrail_def, hqedges]; exact hc0.isTrail.edges_nodup.map (Sym2.map.injective Subtype.val_injective)
      · intro hnil; have : c0.length = 0 := by rw [← hqlen, hnil]; rfl
        have := hc0.three_le_length; omega
      · rw [hqsupp, List.tail_map]; exact hc0.support_nodup.map Subtype.val_injective
    exact hG.1.1 ⟨v0.1, q, hq_cyc, k, hk2, hqlen.trans hc0len⟩
  let c := c0.rotate ht_in
  have hc : c.IsCycle := hc0.rotate ht_in
  have hclen : c.length = 2 ^ k := by simpa [c] using hc0len
  cases c with
  | nil => exact False.elim (hc.ne_nil rfl)
  | @cons _ b _ htb rest =>
    have hrest_nd : rest.support.Nodup := by have := hc.support_nodup; simpa using this
    let rev := rest.reverse
    cases hrev : rev with
    | nil =>
      have hlen0 : rest.length = 0 := by have := congrArg Walk.length hrev; simpa [rev] using this
      have h3 := hc.three_le_length; simp only [Walk.length_cons, hlen0] at h3; omega
    | @cons _ d _ htd mid =>
      have hrev_nd : rev.support.Nodup := by
        rw [← List.nodup_reverse, ← Walk.support_reverse]; simpa [rev] using hrest_nd
      rw [hrev] at hrev_nd
      have ht_not_mid : t ∉ mid.support := (List.nodup_cons.mp hrev_nd).1
      rcases contractTriangle_walk_lift huv_ne hwu_ne.symm mid ht_not_mid with ⟨q, hqlen, hqsupp, _⟩
      have hq_path : q.IsPath := Walk.IsPath.mk' (by
        rw [hqsupp]; exact ((List.nodup_cons.mp hrev_nd).2).map Subtype.val_injective)
      have hqlen_eq : q.length = 2 ^ k - 2 := by
        have h1 : rev.length = rest.length := Walk.length_reverse rest
        rw [hrev] at h1; simp only [Walk.length_cons] at h1 hclen; omega
      have hT_not_q : u ∉ q.support ∧ v ∉ q.support ∧ w ∉ q.support := by
        rw [hqsupp]; refine ⟨?_, ?_, ?_⟩
        · intro h; rcases List.mem_map.mp h with ⟨z, hz, hzu⟩
          exact ht_not_mid (by convert hz; exact Subtype.ext hzu.symm)
        · intro h; rcases List.mem_map.mp h with ⟨z, _, hzv⟩; exact z.2.1 hzv
        · intro h; rcases List.mem_map.mp h with ⟨z, _, hzw⟩; exact z.2.2 hzw
      have hdb_ne : d.1 ≠ b.1 := by
        intro heq
        have hge4 : 4 ≤ 2 ^ k := calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
        have hq0 : q.length = 0 := by
          cases q with
          | nil => rfl
          | @cons _ _ _ _ q' =>
            have hnd := List.nodup_cons.mp hq_path.support_nodup
            have hlast : b.1 ∈ q'.support := Walk.end_mem_support q'
            rw [← heq] at hlast; exact False.elim (hnd.1 hlast)
        omega
      have lift_pair : ∀ (p1 p2 p3 : V), p1 ≠ p2 → p2 ≠ p3 → p3 ≠ p1 →
          p1 ∉ q.support → p2 ∉ q.support → p3 ∉ q.support →
          G.Adj d.1 p1 → G.Adj p2 b.1 → G.Adj p1 p2 → G.Adj p1 p3 → G.Adj p3 p2 →
          (∃ (s1 : V) (c1 : G.Walk s1 s1), c1.IsCycle ∧ c1.length = 2 ^ k + 1) ∧
          (∃ (s2 : V) (c2 : G.Walk s2 s2), c2.IsCycle ∧ c2.length = 2 ^ k + 2) := by
        intro p1 p2 p3 h12 h23 h31 hp1q hp2q hp3q hdp1 hp2b hp12 hp13 hp32
        have hge4 : 4 ≤ 2 ^ k := calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
        let r1 : G.Walk d.1 b.1 := Walk.cons hdp1 (Walk.cons hp12 (Walk.cons hp2b Walk.nil))
        have hr1_path : r1.IsPath := Walk.IsPath.mk' (by
          simp only [r1, Walk.support_cons, Walk.support_nil, List.nodup_cons, List.mem_cons,
            List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
          refine ⟨⟨fun h => hp1q (h ▸ Walk.start_mem_support q),
                   fun h => hp2q (h ▸ Walk.start_mem_support q), hdb_ne⟩,
                  ⟨h12, fun h => hp1q (h ▸ Walk.end_mem_support q)⟩,
                  fun h => hp2q (h ▸ Walk.end_mem_support q)⟩)
        have hdisj1 : ∀ z, z ∈ q.support → z ∈ r1.support → z = d.1 ∨ z = b.1 := by
          intro z hzq hzr
          simp only [r1, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hzr
          rcases hzr with rfl | rfl | rfl | rfl
          · exact Or.inl rfl
          · exact False.elim (hp1q hzq)
          · exact False.elim (hp2q hzq)
          · exact Or.inr rfl
        rcases two_internally_disjoint_paths_cycle q r1 hq_path hr1_path (by omega)
            (by simp [r1]) (by simp [r1]; omega) hdisj1 with ⟨hc1, hcl1⟩
        let r2 : G.Walk d.1 b.1 :=
          Walk.cons hdp1 (Walk.cons hp13 (Walk.cons hp32 (Walk.cons hp2b Walk.nil)))
        have hr2_path : r2.IsPath := Walk.IsPath.mk' (by
          simp only [r2, Walk.support_cons, Walk.support_nil, List.nodup_cons, List.mem_cons,
            List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
          refine ⟨⟨fun h => hp1q (h ▸ Walk.start_mem_support q),
                   fun h => hp3q (h ▸ Walk.start_mem_support q),
                   fun h => hp2q (h ▸ Walk.start_mem_support q), hdb_ne⟩,
                  ⟨h31.symm, h12, fun h => hp1q (h ▸ Walk.end_mem_support q)⟩,
                  ⟨h23.symm, fun h => hp3q (h ▸ Walk.end_mem_support q)⟩,
                  fun h => hp2q (h ▸ Walk.end_mem_support q)⟩)
        have hdisj2 : ∀ z, z ∈ q.support → z ∈ r2.support → z = d.1 ∨ z = b.1 := by
          intro z hzq hzr
          simp only [r2, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hzr
          rcases hzr with rfl | rfl | rfl | rfl | rfl
          · exact Or.inl rfl
          · exact False.elim (hp1q hzq)
          · exact False.elim (hp3q hzq)
          · exact False.elim (hp2q hzq)
          · exact Or.inr rfl
        rcases two_internally_disjoint_paths_cycle q r2 hq_path hr2_path (by omega)
            (by simp [r2]) (by simp [r2]; omega) hdisj2 with ⟨hc2, hcl2⟩
        exact ⟨⟨d.1, q.append r1.reverse, hc1, by rw [hcl1, hqlen_eq]; simp [r1]; omega⟩,
               ⟨d.1, q.append r2.reverse, hc2, by rw [hcl2, hqlen_eq]; simp [r2]; omega⟩⟩
      have get_att : ∀ (z : {x : V // x ≠ v ∧ x ≠ w}), H.Adj t z →
          (z.1 = xu ∧ G.Adj u z.1) ∨ (z.1 = xv ∧ G.Adj v z.1) ∨ (z.1 = xw ∧ G.Adj w z.1) := by
        intro z htz
        rcases htz.2 with h1 | ⟨_, h2 | h3⟩ | ⟨hzu, _⟩
        · have hzN : z.1 ∈ G.neighborFinset u := SimpleGraph.mem_neighborFinset.mpr h1
          rw [hNu] at hzN; simp only [Finset.mem_insert, Finset.mem_singleton] at hzN
          rcases hzN with h | h | h
          · exact False.elim (z.2.1 h)
          · exact False.elim (z.2.2 h)
          · exact Or.inl ⟨h, h1⟩
        · have hzN : z.1 ∈ G.neighborFinset v := SimpleGraph.mem_neighborFinset.mpr h2
          rw [hNv] at hzN; simp only [Finset.mem_insert, Finset.mem_singleton] at hzN
          rcases hzN with h | h | h
          · exact False.elim (htz.1 (Subtype.ext h.symm))
          · exact False.elim (z.2.2 h)
          · exact Or.inr (Or.inl ⟨h, h2⟩)
        · have hzN : z.1 ∈ G.neighborFinset w := SimpleGraph.mem_neighborFinset.mpr h3
          rw [hNw] at hzN; simp only [Finset.mem_insert, Finset.mem_singleton] at hzN
          rcases hzN with h | h | h
          · exact False.elim (htz.1 (Subtype.ext h.symm))
          · exact False.elim (z.2.1 h)
          · exact Or.inr (Or.inr ⟨h, h3⟩)
        · exact False.elim (htz.1 (Subtype.ext hzu.symm))
      refine ⟨k, hk2, ?_⟩
      rcases get_att d htd with ⟨hdxu, hdu⟩ | ⟨hdxv, hdv⟩ | ⟨hdxw, hdw⟩ <;>
      rcases get_att b htb with ⟨hbxu, hbu⟩ | ⟨hbxv, hbv⟩ | ⟨hbxw, hbw⟩
      · exact False.elim (hdb_ne (hdxu.trans hbxu.symm))
      · exact lift_pair u v w huv_ne hvw_ne hwu_ne hT_not_q.1 hT_not_q.2.1 hT_not_q.2.2
          hdu.symm hbv huv hwu.symm hvw.symm
      · exact lift_pair u w v hwu_ne.symm hvw_ne.symm huv_ne.symm hT_not_q.1 hT_not_q.2.2 hT_not_q.2.1
          hdu.symm hbw hwu.symm huv hvw
      · exact lift_pair v u w huv_ne.symm hwu_ne.symm hvw_ne.symm hT_not_q.2.1 hT_not_q.1 hT_not_q.2.2
          hdv.symm hbu huv.symm hvw hwu
      · exact False.elim (hdb_ne (hdxv.trans hbxv.symm))
      · exact lift_pair v w u hvw_ne hwu_ne huv_ne hT_not_q.2.1 hT_not_q.2.2 hT_not_q.1
          hdv.symm hbw hvw huv.symm hwu.symm
      · exact lift_pair w u v hwu_ne huv_ne hvw_ne hT_not_q.2.2 hT_not_q.1 hT_not_q.2.1
          hdw.symm hbu hwu hvw.symm huv.symm
      · exact lift_pair w v u hvw_ne.symm huv_ne.symm hwu_ne.symm hT_not_q.2.2 hT_not_q.2.1 hT_not_q.1
          hdw.symm hbv hvw.symm hwu huv
      · exact False.elim (hdb_ne (hdxw.trans hbxw.symm))

end E64Wave7Agent3P4
