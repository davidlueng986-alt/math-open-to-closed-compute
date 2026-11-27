import Mathlib

open Classical
open SimpleGraph

namespace E64Wave7Agent3P2

noncomputable section

/-!
# Wave 7 Agent #3 — Pillar 2: Tutte Cleavage Torso & Contraction Forcing on `MinimalBad2`
-/

def IsPowerOfTwo (L : ℕ) : Prop := ∃ k : ℕ, 2 ≤ k ∧ L = 2 ^ k

def HasPowerCycle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ IsPowerOfTwo p.length

def PowerFree {V : Type*} (G : SimpleGraph V) : Prop := ¬ HasPowerCycle G

def MinDegGe {V : Type*} [Fintype V] (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∀ v : V, d ≤ G.degree v

def Defects {V : Type*} [Fintype V] (G : SimpleGraph V) : Finset V :=
  Finset.univ.filter (fun v => G.degree v = 2)

def Bad2 {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  PowerFree G ∧ MinDegGe G 2 ∧ (Defects G).card ≤ 2

def MinimalBad2 {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  Bad2 G ∧
  (∀ (m : ℕ) (H : SimpleGraph (Fin m)), Bad2 H → Fintype.card V ≤ m) ∧
  (∀ (H : SimpleGraph V), Bad2 H → G.edgeFinset.card ≤ H.edgeFinset.card)

lemma tail_map {α β : Type*} (f : α → β) (l : List α) :
    (l.map f).tail = l.tail.map f := by
  cases l <;> rfl

lemma mem_edges_rotate {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u u) (hv : v ∈ p.support) {e : Sym2 V} :
    e ∈ (p.rotate v hv).edges ↔ e ∈ p.edges := by
  have h1 : (p.rotate v hv).edges = (p.dropUntil v hv).edges ++ (p.takeUntil v hv).edges := by
    simp only [Walk.rotate, Walk.edges_append]
  have h2 : p.edges = (p.takeUntil v hv).edges ++ (p.dropUntil v hv).edges := by
    have hspec := Walk.take_spec p hv
    have := congrArg Walk.edges hspec
    simpa [Walk.edges_append] using this.symm
  rw [h1, h2, List.mem_append, List.mem_append, or_comm]

def addEdge {V : Type*} (G : SimpleGraph V) (a b : V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ (G.Adj u v ∨ (u = a ∧ v = b) ∨ (u = b ∧ v = a))
  symm := ⟨by
    intro u v ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    rcases h with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

lemma bad2_of_iso {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (hG : Bad2 G) : Bad2 H := by
  rcases hG with ⟨hpf, hmin, hdef⟩
  refine ⟨?_, ?_, ?_⟩
  · intro ⟨w, p, hcyc, hpow⟩
    apply hpf
    refine ⟨e.symm w, p.map e.symm.toHom, hcyc.map e.symm.injective, ?_⟩
    rw [Walk.length_map]; exact hpow
  · intro w
    have hdeg : H.degree w = G.degree (e.symm w) := (e.symm.degree_eq w).symm
    rw [hdeg]; exact hmin (e.symm w)
  · have hcard : (Defects H).card = (Defects G).card := by
      apply Finset.card_bij (fun w _ => e.symm w)
      · intro w hw
        simp only [Defects, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
        rw [e.symm.degree_eq w]; exact hw
      · intro _ _ _ _ h; exact e.symm.injective h
      · intro v hv
        refine ⟨e v, ?_, e.symm_apply_apply v⟩
        simp only [Defects, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
        rw [e.degree_eq v]; exact hv
    omega

lemma minimal_bad2_no_smaller {V : Type} [Fintype V] {G : SimpleGraph V}
    (hG : MinimalBad2 G) {W : Type} [Fintype W] (H : SimpleGraph W)
    (hH : Bad2 H) (hlt : Fintype.card W < Fintype.card V) : False := by
  let e : W ≃ Fin (Fintype.card W) := Fintype.equivFin W
  let H' : SimpleGraph (Fin (Fintype.card W)) :=
    { Adj := fun i j => H.Adj (e.symm i) (e.symm j)
      symm := ⟨fun _ _ h => h.symm⟩
      loopless := ⟨fun _ h => H.loopless _ h⟩ }
  have iso : H ≃g H' :=
    { toEquiv := e
      map_rel_iff' := by intro u v; simp [H'] }
  have hH' : Bad2 H' := bad2_of_iso iso hH
  have hle : Fintype.card V ≤ Fintype.card W := hG.2.1 (Fintype.card W) H' hH'
  omega

lemma powerFree_induce {V : Type*} {G : SimpleGraph V} (s : Set V) (hG : PowerFree G) :
    PowerFree (G.induce s) := by
  intro ⟨v, p, hcyc, hpow⟩
  apply hG
  refine ⟨v.1, p.map (SimpleGraph.Embedding.induce s).toHom, hcyc.map Subtype.val_injective, ?_⟩
  rw [Walk.length_map]; exact hpow

lemma degree_induce_eq {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Finset V)
    (u : {x : V // x ∈ (S : Set V)}) :
    (G.induce (S : Set V)).degree u = ((G.neighborFinset u.1) ∩ S).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun v _ => v.1)
  · intro v hv
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_inter] at hv ⊢
    exact ⟨hv, v.2⟩
  · intro _ _ _ _ h; exact Subtype.ext h
  · intro w hw
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hw
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
  let S : Finset V := Kᶜ
  let H := G.induce (S : Set V)
  have hH_pf : PowerFree H := powerFree_induce (S : Set V) hG.1.1
  have hH_min : MinDegGe H 2 := by
    intro u; change 2 ≤ (G.induce (S : Set V)).degree u
    rw [degree_induce_eq]; exact hmin u.1 (Finset.mem_coe.mp u.2)
  have hH_def : (Defects H).card ≤ 2 := by
    have hcard : (Defects H).card =
        (S.filter (fun u => ((G.neighborFinset u) ∩ S).card = 2)).card := by
      apply Finset.card_bij (fun u _ => u.1)
      · intro u hu
        simp only [Defects, Finset.mem_filter, Finset.mem_univ, true_and] at hu
        change (G.induce (S : Set V)).degree u = 2 at hu
        rw [degree_induce_eq] at hu
        exact Finset.mem_filter.mpr ⟨Finset.mem_coe.mp u.2, hu⟩
      · intro _ _ _ _ h; exact Subtype.ext h
      · intro w hw
        rcases Finset.mem_filter.mp hw with ⟨hwS, hwdeg⟩
        refine ⟨⟨w, Finset.mem_coe.mpr hwS⟩, ?_, rfl⟩
        simp only [Defects, Finset.mem_filter, Finset.mem_univ, true_and]
        change (G.induce (S : Set V)).degree ⟨w, Finset.mem_coe.mpr hwS⟩ = 2
        rw [degree_induce_eq]; exact hwdeg
    rw [hcard]; exact hdef
  have hlt : Fintype.card {x : V // x ∈ (S : Set V)} < Fintype.card V := by
    have hcard_S : Fintype.card {x : V // x ∈ (S : Set V)} = S.card := by
      rw [Fintype.card_subtype]; congr 1; ext z; simp
    rw [hcard_S]
    have h1 := Finset.card_compl_add_card K
    have h2 : 0 < K.card := Finset.card_pos.mpr hKne
    omega
  exact minimal_bad2_no_smaller hG H ⟨hH_pf, hH_min, hH_def⟩ hlt

lemma walk_adj_of_mem_edges {V : Type*} {G : SimpleGraph V} {u v x y : V}
    (p : G.Walk u v) (h : s(x, y) ∈ p.edges) : G.Adj x y := by
  induction p with
  | nil => simp at h
  | @cons a b c hab rest ih =>
    simp only [Walk.edges_cons, List.mem_cons] at h
    rcases h with heq | h'
    · rw [Sym2.eq_iff] at heq
      rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
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
    · rw [Sym2.eq_iff] at heq
      rcases heq with ⟨_, rfl⟩ | ⟨hvu, rfl⟩
      · cases q with
        | nil => rfl
        | @cons _ z _ hvz q' =>
          have hnd := List.nodup_cons.mp (List.nodup_cons.mp hp.support_nodup).2
          exact False.elim (hnd.1 (Walk.end_mem_support q'))
      · exact False.elim (G.ne_of_adj huw hvu)
    · have hu_in : u ∈ q.support := Walk.mem_support_of_mem_edges q hmem' (by simp)
      exact False.elim ((List.nodup_cons.mp hp.support_nodup).1 hu_in)

lemma two_internally_disjoint_paths_cycle {V : Type*} {G : SimpleGraph V} {u v : V}
    (p q : G.Walk u v) (hp : p.IsPath) (hq : q.IsPath)
    (hp1 : 1 ≤ p.length) (hq1 : 1 ≤ q.length) (hsum3 : 3 ≤ p.length + q.length)
    (hdisj : ∀ w, w ∈ p.support → w ∈ q.support → w = u ∨ w = v) :
    (p.append q.reverse).IsCycle ∧ (p.append q.reverse).length = p.length + q.length := by
  let c : G.Walk u u := p.append q.reverse
  have hlen : c.length = p.length + q.length := by
    simp [c, Walk.length_append, Walk.length_reverse]
  have hp_ne : ¬ p.Nil := fun h => by have := Walk.length_eq_zero_iff.mpr h; omega
  have hqr_ne : ¬ q.reverse.Nil := fun h => by
    have : q.reverse.length = 0 := Walk.length_eq_zero_iff.mpr h
    rw [Walk.length_reverse] at this; omega
  have hqr_path : q.reverse.IsPath := hq.reverse
  refine ⟨?_, hlen⟩
  rw [Walk.isCycle_def]
  refine ⟨?_, ?_, ?_⟩
  · rw [Walk.isTrail_def]
    simp only [c, Walk.edges_append]
    rw [List.nodup_append]
    refine ⟨hp.isTrail.edges_nodup, hqr_path.isTrail.edges_nodup, ?_⟩
    intro e he1 e' he2 heq
    subst heq
    have he2q : e ∈ q.edges := by simpa [Walk.edges_reverse] using he2
    refine Sym2.ind (fun x y => ?_) e he1 he2q
    intro hxy1 hxy2
    have hx_p : x ∈ p.support := Walk.mem_support_of_mem_edges p hxy1 (by simp)
    have hy_p : y ∈ p.support := Walk.mem_support_of_mem_edges p hxy1 (by simp)
    have hx_q : x ∈ q.support := Walk.mem_support_of_mem_edges q hxy2 (by simp)
    have hy_q : y ∈ q.support := Walk.mem_support_of_mem_edges q hxy2 (by simp)
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
    have : c.length = 0 := Walk.length_eq_zero_iff.mpr hnil
    omega
  · have hsupp : c.support = p.support ++ q.reverse.support.tail := Walk.support_append p q.reverse
    have htail : c.support.tail = p.support.tail ++ q.reverse.support.tail := by
      rw [hsupp]
      cases p with
      | nil => exact False.elim (hp_ne rfl)
      | cons _ _ => simp [Walk.support_cons]
    rw [htail, List.nodup_append]
    have hp_tail_nd : p.support.tail.Nodup := by
      cases p with
      | nil => exact False.elim (hp_ne rfl)
      | cons _ _ => exact (List.nodup_cons.mp hp.support_nodup).2
    have hqr_tail_nd : q.reverse.support.tail.Nodup := by
      cases hqr : q.reverse with
      | nil => exact False.elim (hqr_ne hqr)
      | cons _ _ =>
        have hnd := hqr_path.support_nodup; rw [hqr] at hnd
        exact (List.nodup_cons.mp hnd).2
    refine ⟨hp_tail_nd, hqr_tail_nd, ?_⟩
    intro w hw1 w' hw2 heq
    subst heq
    have hw_p : w ∈ p.support := by
      cases p with
      | nil => exact False.elim (hp_ne rfl)
      | cons _ _ => exact List.mem_cons_of_mem _ hw1
    have hw_qr : w ∈ q.reverse.support := by
      cases hqr : q.reverse with
      | nil => exact False.elim (hqr_ne hqr)
      | cons _ _ => rw [hqr] at hw2; exact List.mem_cons_of_mem _ hw2
    have hw_q : w ∈ q.support := by simpa [Walk.support_reverse] using hw_qr
    rcases hdisj w hw_p hw_q with rfl | rfl
    · cases p with
      | nil => exact False.elim (hp_ne rfl)
      | cons _ _ => exact (List.nodup_cons.mp hp.support_nodup).1 hw1
    · cases hqr : q.reverse with
      | nil => exact False.elim (hqr_ne hqr)
      | cons _ _ =>
        have hnd := hqr_path.support_nodup; rw [hqr] at hnd; rw [hqr] at hw2
        exact (List.nodup_cons.mp hnd).1 hw2

lemma addEdge_walk_lift {V : Type*} {G : SimpleGraph V} {x y : V}
    {u v : V} (p : (addEdge G x y).Walk u v) (havoid : s(x, y) ∉ p.edges) :
    ∃ q : G.Walk u v, q.length = p.length ∧ q.support = p.support ∧ q.edges = p.edges := by
  induction p with
  | nil => exact ⟨Walk.nil, rfl, rfl, rfl⟩
  | @cons a b c hab rest ih =>
    have hne_e : s(x, y) ≠ s(a, b) := fun h => havoid (by simp [h])
    have havoid' : s(x, y) ∉ rest.edges := fun h => havoid (List.mem_cons_of_mem _ h)
    rcases ih havoid' with ⟨q, hlen, hsupp, hedges⟩
    have hadjG : G.Adj a b := by
      rcases hab.2 with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h
      · exact False.elim (hne_e rfl)
      · exact False.elim (hne_e Sym2.eq_swap)
    exact ⟨Walk.cons hadjG q, by simp [hlen], by simp [hsupp], by simp [hedges]⟩

lemma addEdge_cycle_lifts_to_fermat_path {V : Type*} {G : SimpleGraph V}
    (hpf : PowerFree G) {x y : V} (hxy : x ≠ y)
    (hcyc_ex : HasPowerCycle (addEdge G x y)) :
    ∃ (p : G.Walk x y), p.IsPath ∧ ∃ k : ℕ, 2 ≤ k ∧ p.length = 2 ^ k - 1 := by
  rcases hcyc_ex with ⟨v0, c0, hc0, k, hk2, hc0len⟩
  have hmem_e : s(x, y) ∈ c0.edges := by
    by_contra havoid
    rcases addEdge_walk_lift c0 havoid with ⟨q, hqlen, hqsupp, hqedges⟩
    have hq_cyc : q.IsCycle := by
      rw [Walk.isCycle_def]
      refine ⟨?_, ?_, ?_⟩
      · rw [Walk.isTrail_def, hqedges]; exact hc0.isTrail.edges_nodup
      · intro hnil
        have : c0.length = 0 := by rw [← hqlen, hnil]; rfl
        have := hc0.three_le_length; omega
      · rw [hqsupp]; exact hc0.support_nodup
    exact hpf ⟨v0, q, hq_cyc, k, hk2, hqlen.trans hc0len⟩
  have hx_in : x ∈ c0.support := Walk.mem_support_of_mem_edges c0 hmem_e (by simp)
  let c := c0.rotate x hx_in
  have hc : c.IsCycle := hc0.rotate hx_in
  have hclen : c.length = 2 ^ k := by simpa [c] using hc0len
  have hmem_ec : s(x, y) ∈ c.edges := (mem_edges_rotate c0 hx_in).mpr hmem_e
  have lift_from_start : ∀ (d : (addEdge G x y).Walk x x), d.IsCycle → d.length = 2 ^ k →
      ∀ (hd : ∃ (h1 : (addEdge G x y).Adj x y) (rest : (addEdge G x y).Walk y x),
        d = Walk.cons h1 rest),
      ∃ (p : G.Walk x y), p.IsPath ∧ ∃ k' : ℕ, 2 ≤ k' ∧ p.length = 2 ^ k' - 1 := by
    intro d hd hdlen ⟨h1, rest, hdeq⟩
    subst hdeq
    have havoid : s(x, y) ∉ rest.edges := (List.nodup_cons.mp hd.isTrail.edges_nodup).1
    rcases addEdge_walk_lift rest havoid with ⟨q, hqlen, hqsupp, _⟩
    have hq_nd : q.support.Nodup := by
      rw [hqsupp]; have := hd.support_nodup; simpa [Walk.support_cons] using this
    refine ⟨q.reverse, (Walk.IsPath.mk' hq_nd).reverse, k, hk2, ?_⟩
    rw [Walk.length_reverse, hqlen]
    simp only [Walk.length_cons] at hdlen; omega
  cases hc_eq : c with
  | nil => exact False.elim (hc.ne_nil hc_eq)
  | @cons _ b _ hxb rest =>
    by_cases hby : b = y
    · subst hby; exact lift_from_start c hc hclen ⟨hxb, rest, hc_eq⟩
    · have hrev_cyc : c.reverse.IsCycle := hc.reverse
      have hrev_len : c.reverse.length = 2 ^ k := by rw [Walk.length_reverse]; exact hclen
      cases hcr : c.reverse with
      | nil => exact False.elim (hrev_cyc.ne_nil hcr)
      | @cons _ b' _ hxb' rest' =>
        have hb'y : b' = y := by
          have hmem_r : s(x, y) ∈ c.reverse.edges := by simpa [Walk.edges_reverse] using hmem_ec
          rw [hcr] at hmem_r
          simp only [Walk.edges_cons, List.mem_cons] at hmem_r
          rcases hmem_r with heq | hmem_rest'
          · rw [Sym2.eq_iff] at heq
            rcases heq with ⟨_, rfl⟩ | ⟨h1, _⟩
            · rfl
            · exact False.elim (hxy h1.symm)
          · have hrest'_path : rest'.IsPath := Walk.IsPath.mk' (by
              have := hrev_cyc.support_nodup; rw [hcr] at this; simpa [Walk.support_cons] using this)
            have hmem_rr : s(x, y) ∈ rest'.reverse.edges := by
              simpa [Walk.edges_reverse] using hmem_rest'
            have h1 : (Walk.cons hxb' rest').reverse = rest'.reverse.concat hxb'.symm := by
              simp [Walk.reverse_cons]
            rw [← hcr, Walk.reverse_reverse, hc_eq] at h1
            cases hrr : rest'.reverse with
            | nil => rw [hrr] at hmem_rr; simp at hmem_rr
            | @cons _ z _ hxz q =>
              rw [hrr] at hmem_rr h1
              simp only [Walk.concat_cons] at h1
              have hzb : z = b := by
                have hsupp := congrArg Walk.support h1
                simp only [Walk.support_cons] at hsupp
                exact (List.cons.inj (List.cons.inj hsupp).2).1.symm
              simp only [Walk.edges_cons, List.mem_cons] at hmem_rr
              rcases hmem_rr with heq | hmq
              · rw [Sym2.eq_iff] at heq
                rcases heq with ⟨_, rfl⟩ | ⟨hxy', _⟩
                · exact False.elim (hby hzb.symm)
                · exact False.elim (hxy hxy'.symm)
              · have hx_in' : x ∈ q.support := Walk.mem_support_of_mem_edges q hmq (by simp)
                have hnd := hrest'_path.reverse.support_nodup
                rw [hrr] at hnd
                exact False.elim ((List.nodup_cons.mp hnd).1 hx_in')
        subst hb'y
        exact lift_from_start c.reverse hrev_cyc hrev_len ⟨hxb', rest', hcr⟩

def identGraph {V : Type*} (G : SimpleGraph V) (x y : V) :
    SimpleGraph {w : V // w ≠ y} where
  Adj u v := u ≠ v ∧ (G.Adj u.1 v.1 ∨ (u.1 = x ∧ G.Adj y v.1) ∨ (v.1 = x ∧ G.Adj u.1 y))
  symm := ⟨by
    intro u v ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    rcases h with h | ⟨rfl, hy⟩ | ⟨rfl, hy⟩
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr ⟨rfl, hy.symm⟩)
    · exact Or.inr (Or.inl ⟨rfl, hy.symm⟩)⟩
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
    have hclen : IsPowerOfTwo c.length := by simpa [c] using hpow
    cases c with
    | nil => exact False.elim (hc.ne_nil rfl)
    | @cons _ b _ hzb rest =>
      have hrest_nodup : rest.support.Nodup := by have := hc.support_nodup; simpa using this
      let rev := rest.reverse
      cases hrev : rev with
      | nil =>
        have hlen0 : rest.length = 0 := by
          have := congrArg Walk.length hrev; simpa [rev] using this
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
      · rw [hqsupp, tail_map]
        exact hc0.support_nodup.map Subtype.val_injective
    exact False.elim (hpf ⟨v0.1, q, hq_cyc, hqlen ▸ hpow⟩)

lemma identGraph_degree_other_no_common {V : Type*} [Fintype V] (G : SimpleGraph V)
    {x y : V} (hxy : x ≠ y) (u : {w : V // w ≠ y}) (hux : u.1 ≠ x)
    (hnot_comm : ¬ (G.Adj u.1 x ∧ G.Adj u.1 y)) :
    (identGraph G x y).degree u = G.degree u.1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun v _ => if v.1 = x ∧ G.Adj u.1 y then y else v.1)
  · intro v hv
    rw [SimpleGraph.mem_neighborFinset] at hv ⊢
    dsimp only [identGraph] at hv
    split_ifs with h
    · exact h.2
    · rcases hv.2 with hadj | ⟨hux', _⟩ | ⟨hvx, huy⟩
      · exact hadj
      · exact False.elim (hux hux')
      · exact False.elim (h ⟨hvx, huy⟩)
  · intro v1 _ v2 _ heq
    split_ifs at heq with h1 h2
    · exact Subtype.ext (h1.1.trans h2.1.symm)
    · exact False.elim (v2.2 heq.symm)
    · exact False.elim (v1.2 heq)
    · exact Subtype.ext heq
  · intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    by_cases hwy : w = y
    · subst hwy
      refine ⟨⟨x, hxy⟩, ?_, ?_⟩
      · rw [SimpleGraph.mem_neighborFinset]
        exact ⟨fun h => hux (congrArg Subtype.val h), Or.inr (Or.inr ⟨rfl, hw⟩)⟩
      · simp [hw]
    · refine ⟨⟨w, hwy⟩, ?_, ?_⟩
      · rw [SimpleGraph.mem_neighborFinset]
        exact ⟨fun h => G.ne_of_adj hw (congrArg Subtype.val h), Or.inl hw⟩
      · split_ifs with h
        · exact False.elim (hnot_comm ⟨h.1 ▸ hw, h.2⟩)
        · rfl

lemma identGraph_degree_merged {V : Type*} [Fintype V] (G : SimpleGraph V)
    {x y : V} (hxy : x ≠ y) :
    (identGraph G x y).degree ⟨x, hxy⟩ =
      (((G.neighborFinset x) ∪ (G.neighborFinset y)) \ {x, y}).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun v _ => v.1)
  · intro v hv
    rw [SimpleGraph.mem_neighborFinset] at hv
    dsimp only [identGraph] at hv
    simp only [Finset.mem_sdiff, Finset.mem_union, SimpleGraph.mem_neighborFinset,
      Finset.mem_insert, Finset.mem_singleton, not_or]
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
    rw [SimpleGraph.mem_neighborFinset]
    refine ⟨fun h => hw.2.1 (congrArg Subtype.val h).symm, ?_⟩
    rcases hw.1 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨rfl, h⟩)

/-- PILLAR 2.1: Tutte Cleavage Torso Fermat-Path Theorem. -/
theorem minimal_bad2_nonadj_two_cut_torso_fermat_path {V : Type} [Fintype V]
    {G : SimpleGraph V} (hG : MinimalBad2 G) {x y a b : V} {Ca Cb : Finset V}
    (hxy_ne : x ≠ y) (hxy_nadj : ¬ G.Adj x y)
    (hab : a ≠ b) (ha : a ∈ Defects G) (hb : b ∈ Defects G)
    (haCa : a ∈ Ca) (hbCb : b ∈ Cb)
    (hdisj_ab : Disjoint Ca Cb)
    (hCa_no_xy : x ∉ Ca ∧ y ∉ Ca) (hCb_no_xy : x ∉ Cb ∧ y ∉ Cb)
    (hcover : Ca ∪ Cb ∪ {x, y} = Finset.univ)
    (hno_cross : ∀ u ∈ Ca, ∀ v ∈ Cb, ¬ G.Adj u v)
    (hxCa1 : 1 ≤ ((G.neighborFinset x) ∩ Ca).card)
    (hyCa1 : 1 ≤ ((G.neighborFinset y) ∩ Ca).card)
    (hmax2 : 2 ≤ ((G.neighborFinset x) ∩ Ca).card ∨ 2 ≤ ((G.neighborFinset y) ∩ Ca).card) :
    ∃ (p : G.Walk x y), p.IsPath ∧ (∀ w ∈ p.support, w ∈ Ca ∨ w = x ∨ w = y) ∧
      ∃ k : ℕ, 2 ≤ k ∧ p.length = 2 ^ k - 1 := by
  have hdef_eq : Defects G = {a, b} := by
    have hsub : ({a, b} : Finset V) ⊆ Defects G := by
      intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl <;> assumption
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hab]; exact hG.1.2.2)).symm
  let S : Finset V := Ca ∪ {x, y}
  have hxS : x ∈ (S : Set V) := by simp [S]
  have hyS : y ∈ (S : Set V) := by simp [S]
  let GS := G.induce (S : Set V)
  let H := addEdge GS ⟨x, hxS⟩ ⟨y, hyS⟩
  have hGS_pf : PowerFree GS := powerFree_induce (S : Set V) hG.1.1
  have hS_deg_u : ∀ u ∈ Ca, ((G.neighborFinset u) ∩ S).card = G.degree u := by
    intro u huCa
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    congr 1; ext w
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, and_iff_left_iff_imp]
    intro hadj
    have hwU : w ∈ Ca ∪ Cb ∪ {x, y} := by rw [hcover]; exact Finset.mem_univ w
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hwU
    simp only [S, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    rcases hwU with (h | h) | rfl | rfl
    · exact Or.inl h
    · exact False.elim (hno_cross u huCa w h hadj)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have hH_deg_other : ∀ u : {z : V // z ∈ (S : Set V)}, u.1 ∈ Ca → H.degree u = G.degree u.1 := by
    intro u huCa
    have hux : u ≠ ⟨x, hxS⟩ := fun h => by
      have h1 : u.1 = x := congrArg Subtype.val h
      exact hCa_no_xy.1 (h1 ▸ huCa)
    have huy : u ≠ ⟨y, hyS⟩ := fun h => by
      have h1 : u.1 = y := congrArg Subtype.val h
      exact hCa_no_xy.2 (h1 ▸ huCa)
    have hdeg_eq : H.degree u = GS.degree u := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
      congr 1; ext v
      simp only [SimpleGraph.mem_neighborFinset, H, addEdge]
      constructor
      · rintro ⟨_, h | ⟨h1, _⟩ | ⟨h1, _⟩⟩
        · exact h
        · exact False.elim (hux h1)
        · exact False.elim (huy h1)
      · intro h; exact ⟨GS.ne_of_adj h, Or.inl h⟩
    rw [hdeg_eq, degree_induce_eq, hS_deg_u u.1 huCa]
  have hH_deg_x : H.degree ⟨x, hxS⟩ = ((G.neighborFinset x) ∩ Ca).card + 1 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have heq : H.neighborFinset ⟨x, hxS⟩ = (GS.neighborFinset ⟨x, hxS⟩) ∪ {⟨y, hyS⟩} := by
      ext v
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_union, Finset.mem_singleton, H, addEdge]
      constructor
      · rintro ⟨_, h | ⟨_, rfl⟩ | ⟨h1, _⟩⟩
        · exact Or.inl h
        · exact Or.inr rfl
        · exact False.elim (hxy_ne (congrArg Subtype.val h1))
      · rintro (h | rfl)
        · exact ⟨GS.ne_of_adj h, Or.inl h⟩
        · exact ⟨fun h => hxy_ne (congrArg Subtype.val h), Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    rw [heq, Finset.card_union_of_disjoint]
    · simp only [Finset.card_singleton, SimpleGraph.card_neighborFinset_eq_degree]
      rw [degree_induce_eq]
      congr 1; congr 1; ext w
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, S, Finset.mem_union,
        Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hw, h | rfl | rfl⟩
        · exact ⟨hw, h⟩
        · exact False.elim (G.loopless x hw)
        · exact False.elim (hxy_nadj hw)
      · rintro ⟨hw, h⟩; exact ⟨hw, Or.inl h⟩
    · rw [Finset.disjoint_singleton_right, SimpleGraph.mem_neighborFinset]; exact hxy_nadj
  have hH_deg_y : H.degree ⟨y, hyS⟩ = ((G.neighborFinset y) ∩ Ca).card + 1 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have heq : H.neighborFinset ⟨y, hyS⟩ = (GS.neighborFinset ⟨y, hyS⟩) ∪ {⟨x, hxS⟩} := by
      ext v
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_union, Finset.mem_singleton, H, addEdge]
      constructor
      · rintro ⟨_, h | ⟨h1, _⟩ | ⟨_, rfl⟩⟩
        · exact Or.inl h
        · exact False.elim (hxy_ne (congrArg Subtype.val h1).symm)
        · exact Or.inr rfl
      · rintro (h | rfl)
        · exact ⟨GS.ne_of_adj h, Or.inl h⟩
        · exact ⟨fun h => hxy_ne (congrArg Subtype.val h).symm, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
    rw [heq, Finset.card_union_of_disjoint]
    · simp only [Finset.card_singleton, SimpleGraph.card_neighborFinset_eq_degree]
      rw [degree_induce_eq]
      congr 1; congr 1; ext w
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, S, Finset.mem_union,
        Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hw, h | rfl | rfl⟩
        · exact ⟨hw, h⟩
        · exact False.elim (hxy_nadj hw.symm)
        · exact False.elim (G.loopless y hw)
      · rintro ⟨hw, h⟩; exact ⟨hw, Or.inl h⟩
    · rw [Finset.disjoint_singleton_right, SimpleGraph.mem_neighborFinset]
      exact fun h => hxy_nadj h.symm
  have hH_not_pf : ¬ PowerFree H := by
    intro hH_pf
    have hH_min : MinDegGe H 2 := by
      intro u
      have huS : u.1 ∈ Ca ∨ u.1 = x ∨ u.1 = y := by
        have := u.2; simp only [S, Finset.mem_coe, Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton] at this; exact this
      rcases huS with huCa | hux | huy
      · rw [hH_deg_other u huCa]; exact hG.1.2.1 u.1
      · have : u = ⟨x, hxS⟩ := Subtype.ext hux; rw [this, hH_deg_x]; omega
      · have : u = ⟨y, hyS⟩ := Subtype.ext huy; rw [this, hH_deg_y]; omega
    have hH_def : (Defects H).card ≤ 2 := by
      rcases hmax2 with hx2 | hy2
      · have hsub : Defects H ⊆ {⟨a, by simp [S, haCa]⟩, ⟨y, hyS⟩} := by
          intro u hu
          have hdeg2 : H.degree u = 2 := (Finset.mem_filter.mp hu).2
          have huS : u.1 ∈ Ca ∨ u.1 = x ∨ u.1 = y := by
            have := u.2; simp only [S, Finset.mem_coe, Finset.mem_union, Finset.mem_insert,
              Finset.mem_singleton] at this; exact this
          rcases huS with huCa | hux | huy
          · rw [hH_deg_other u huCa] at hdeg2
            have hud : u.1 ∈ Defects G := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdeg2⟩
            rw [hdef_eq] at hud
            simp only [Finset.mem_insert, Finset.mem_singleton] at hud ⊢
            rcases hud with hua | hub
            · exact Or.inl (Subtype.ext hua)
            · exact False.elim (Finset.disjoint_left.mp hdisj_ab (hub ▸ huCa) hbCb)
          · have : u = ⟨x, hxS⟩ := Subtype.ext hux; rw [this, hH_deg_x] at hdeg2; omega
          · exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr (Subtype.ext huy))
        exact le_trans (Finset.card_le_card hsub) Finset.card_le_two
      · have hsub : Defects H ⊆ {⟨a, by simp [S, haCa]⟩, ⟨x, hxS⟩} := by
          intro u hu
          have hdeg2 : H.degree u = 2 := (Finset.mem_filter.mp hu).2
          have huS : u.1 ∈ Ca ∨ u.1 = x ∨ u.1 = y := by
            have := u.2; simp only [S, Finset.mem_coe, Finset.mem_union, Finset.mem_insert,
              Finset.mem_singleton] at this; exact this
          rcases huS with huCa | hux | huy
          · rw [hH_deg_other u huCa] at hdeg2
            have hud : u.1 ∈ Defects G := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdeg2⟩
            rw [hdef_eq] at hud
            simp only [Finset.mem_insert, Finset.mem_singleton] at hud ⊢
            rcases hud with hua | hub
            · exact Or.inl (Subtype.ext hua)
            · exact False.elim (Finset.disjoint_left.mp hdisj_ab (hub ▸ huCa) hbCb)
          · exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr (Subtype.ext hux))
          · have : u = ⟨y, hyS⟩ := Subtype.ext huy; rw [this, hH_deg_y] at hdeg2; omega
        exact le_trans (Finset.card_le_card hsub) Finset.card_le_two
    have hlt : Fintype.card {z : V // z ∈ (S : Set V)} < Fintype.card V := by
      have hcard_S : Fintype.card {z : V // z ∈ (S : Set V)} = S.card := by
        rw [Fintype.card_subtype]; congr 1; ext z; simp
      rw [hcard_S]
      have hb_notS : b ∉ S := by
        simp only [S, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨Finset.disjoint_right.mp hdisj_ab hbCb,
               fun h => hCb_no_xy.1 (h ▸ hbCb), fun h => hCb_no_xy.2 (h ▸ hbCb)⟩
      exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
        ⟨Finset.subset_univ S, fun h => hb_notS (h ▸ Finset.mem_univ b)⟩)
    exact minimal_bad2_no_smaller hG H ⟨hH_pf, hH_min, hH_def⟩ hlt
  have hcyc : HasPowerCycle H := not_not.mp hH_not_pf
  have hxy_sub_ne : (⟨x, hxS⟩ : {z : V // z ∈ (S : Set V)}) ≠ ⟨y, hyS⟩ :=
    fun h => hxy_ne (congrArg Subtype.val h)
  rcases addEdge_cycle_lifts_to_fermat_path hGS_pf hxy_sub_ne hcyc with ⟨pS, hpS, k, hk2, hplen⟩
  let p : G.Walk x y := pS.map (SimpleGraph.Embedding.induce (S : Set V)).toHom
  refine ⟨p, hpS.map Subtype.val_injective, ?_, k, hk2, by dsimp only [p]; rw [Walk.length_map]; exact hplen⟩
  intro w hw
  dsimp only [p] at hw
  rw [Walk.support_map] at hw
  rcases List.mem_map.mp hw with ⟨u, _, rfl⟩
  have := u.2
  simp only [S, Finset.mem_coe, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at this
  exact this

/-- PILLAR 2.2: One-Sided Non-Adjacent 2-Cut Cubic Normal Form. -/
theorem minimal_bad2_nonadj_two_cut_one_sided_cubic {V : Type} [Fintype V]
    {G : SimpleGraph V} (hG : MinimalBad2 G) {x y a b : V} {Ca Cb : Finset V}
    (hab : a ≠ b) (ha : a ∈ Defects G) (hb : b ∈ Defects G)
    (haCa : a ∈ Ca) (hbCb : b ∈ Cb)
    (hdisj_ab : Disjoint Ca Cb)
    (hCa_no_xy : x ∉ Ca ∧ y ∉ Ca) (hCb_no_xy : x ∉ Cb ∧ y ∉ Cb)
    (hcover : Ca ∪ Cb ∪ {x, y} = Finset.univ)
    (hno_cross : ∀ u ∈ Ca, ∀ v ∈ Cb, ¬ G.Adj u v)
    (hxCa1 : ((G.neighborFinset x) ∩ Ca).card = 1)
    (hyCa1 : ((G.neighborFinset y) ∩ Ca).card = 1) :
    G.degree x = 3 ∧ G.degree y = 3 := by
  have hdef_eq : Defects G = {a, b} := by
    have hsub : ({a, b} : Finset V) ⊆ Defects G := by
      intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl <;> assumption
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hab]; exact hG.1.2.2)).symm
  have hx_not_def : x ∉ Defects G := by
    rw [hdef_eq]; simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => hCa_no_xy.1 (h ▸ haCa), fun h => hCb_no_xy.1 (h ▸ hbCb)⟩
  have hy_not_def : y ∉ Defects G := by
    rw [hdef_eq]; simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => hCa_no_xy.2 (h ▸ haCa), fun h => hCb_no_xy.2 (h ▸ hbCb)⟩
  have hx_ge3 : 3 ≤ G.degree x := by
    have h2 := hG.1.2.1 x
    have hne : G.degree x ≠ 2 := fun h => hx_not_def (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    omega
  have hy_ge3 : 3 ≤ G.degree y := by
    have h2 := hG.1.2.1 y
    have hne : G.degree y ≠ 2 := fun h => hy_not_def (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    omega
  have hCa_c : Caᶜ = Cb ∪ {x, y} := by
    ext u; simp only [Finset.mem_compl, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hu
      have hU : u ∈ Ca ∪ Cb ∪ {x, y} := by rw [hcover]; exact Finset.mem_univ u
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hU; tauto
    · rintro (huCb | rfl | rfl)
      · exact Finset.disjoint_right.mp hdisj_ab huCb
      · exact hCa_no_xy.1
      · exact hCa_no_xy.2
  have huCb_deg : ∀ u ∈ Cb, ((G.neighborFinset u) ∩ Caᶜ).card = G.degree u := by
    intro u huCb
    have h0 : ((G.neighborFinset u) ∩ Ca).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro v hv; rcases Finset.mem_inter.mp hv with ⟨hvN, hvCa⟩
      exact hno_cross v hvCa u huCb ((SimpleGraph.mem_neighborFinset G u v).mp hvN).symm
    have hsum := degree_compl_eq_sub G Ca u; omega
  have hx_c_deg : ((G.neighborFinset x) ∩ Caᶜ).card = G.degree x - 1 := by
    have hsum := degree_compl_eq_sub G Ca x; omega
  have hy_c_deg : ((G.neighborFinset y) ∩ Caᶜ).card = G.degree y - 1 := by
    have hsum := degree_compl_eq_sub G Ca y; omega
  have hmin_c : ∀ u ∈ Caᶜ, 2 ≤ ((G.neighborFinset u) ∩ Caᶜ).card := by
    intro u hu; rw [hCa_c] at hu
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with huCb | rfl | rfl
    · rw [huCb_deg u huCb]; exact hG.1.2.1 u
    · omega
    · omega
  constructor
  · by_contra hx_ne3
    have hx_ge4 : 4 ≤ G.degree x := by omega
    apply minimal_bad2_no_safe_deletion hG Ca ⟨a, haCa⟩ hmin_c
    have hsub : (Caᶜ.filter (fun u => ((G.neighborFinset u) ∩ Caᶜ).card = 2)) ⊆ {b, y} := by
      intro u hu; rcases Finset.mem_filter.mp hu with ⟨huC, hu2⟩
      rw [hCa_c] at huC; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at huC ⊢
      rcases huC with huCb | rfl | rfl
      · rw [huCb_deg u huCb] at hu2
        have hud : u ∈ Defects G := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu2⟩
        rw [hdef_eq] at hud; simp only [Finset.mem_insert, Finset.mem_singleton] at hud
        rcases hud with rfl | rfl
        · exact False.elim (Finset.disjoint_left.mp hdisj_ab haCa huCb)
        · exact Or.inl rfl
      · omega
      · exact Or.inr rfl
    exact le_trans (Finset.card_le_card hsub) Finset.card_le_two
  · by_contra hy_ne3
    have hy_ge4 : 4 ≤ G.degree y := by omega
    apply minimal_bad2_no_safe_deletion hG Ca ⟨a, haCa⟩ hmin_c
    have hsub : (Caᶜ.filter (fun u => ((G.neighborFinset u) ∩ Caᶜ).card = 2)) ⊆ {b, x} := by
      intro u hu; rcases Finset.mem_filter.mp hu with ⟨huC, hu2⟩
      rw [hCa_c] at huC; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at huC ⊢
      rcases huC with huCb | rfl | rfl
      · rw [huCb_deg u huCb] at hu2
        have hud : u ∈ Defects G := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu2⟩
        rw [hdef_eq] at hud; simp only [Finset.mem_insert, Finset.mem_singleton] at hud
        rcases hud with rfl | rfl
        · exact False.elim (Finset.disjoint_left.mp hdisj_ab haCa huCb)
        · exact Or.inl rfl
      · exact Or.inr rfl
      · omega
    exact le_trans (Finset.card_le_card hsub) Finset.card_le_two

/-- PILLAR 2.3: Tutte Contracted Cleavage Dyadic-Path Theorem. -/
theorem minimal_bad2_nonadj_two_cut_contraction_dyadic_path {V : Type} [Fintype V]
    {G : SimpleGraph V} (hG : MinimalBad2 G) {x y a b : V} {Ca Cb : Finset V}
    (hxy_ne : x ≠ y) (hxy_nadj : ¬ G.Adj x y)
    (hab : a ≠ b) (ha : a ∈ Defects G) (hb : b ∈ Defects G)
    (haCa : a ∈ Ca) (hbCb : b ∈ Cb)
    (hdisj_ab : Disjoint Ca Cb)
    (hCa_no_xy : x ∉ Ca ∧ y ∉ Ca) (hCb_no_xy : x ∉ Cb ∧ y ∉ Cb)
    (hcover : Ca ∪ Cb ∪ {x, y} = Finset.univ)
    (hno_cross : ∀ u ∈ Ca, ∀ v ∈ Cb, ¬ G.Adj u v)
    (hxCa1 : 1 ≤ ((G.neighborFinset x) ∩ Ca).card)
    (hyCa1 : 1 ≤ ((G.neighborFinset y) ∩ Ca).card)
    (hno_comm_Ca : ∀ w ∈ Ca, ¬ (G.Adj w x ∧ G.Adj w y)) :
    ∃ (p : G.Walk x y), p.IsPath ∧ (∀ w ∈ p.support, w ∈ Ca ∨ w = x ∨ w = y) ∧
      IsPowerOfTwo p.length := by
  have hdef_eq : Defects G = {a, b} := by
    have hsub : ({a, b} : Finset V) ⊆ Defects G := by
      intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl <;> assumption
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hab]; exact hG.1.2.2)).symm
  let S : Finset V := Ca ∪ {x, y}
  have hxS : x ∈ (S : Set V) := by simp [S]
  have hyS : y ∈ (S : Set V) := by simp [S]
  let GS := G.induce (S : Set V)
  let xS : {z : V // z ∈ (S : Set V)} := ⟨x, hxS⟩
  let yS : {z : V // z ∈ (S : Set V)} := ⟨y, hyS⟩
  have hxyS_ne : xS ≠ yS := fun h => hxy_ne (congrArg Subtype.val h)
  let H := identGraph GS xS yS
  have hGS_pf : PowerFree GS := powerFree_induce (S : Set V) hG.1.1
  have hS_deg_u : ∀ u ∈ Ca, ((G.neighborFinset u) ∩ S).card = G.degree u := by
    intro u huCa
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    congr 1; ext w
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, and_iff_left_iff_imp]
    intro hadj
    have hwU : w ∈ Ca ∪ Cb ∪ {x, y} := by rw [hcover]; exact Finset.mem_univ w
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hwU
    simp only [S, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    rcases hwU with (h | h) | rfl | rfl
    · exact Or.inl h
    · exact False.elim (hno_cross u huCa w h hadj)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have hdeg_other : ∀ u : {w : {z : V // z ∈ (S : Set V)} // w ≠ yS}, u.1 ≠ xS →
      H.degree u = G.degree u.1.1 := by
    intro u hux
    have huCa : u.1.1 ∈ Ca := by
      have := u.1.2
      simp only [S, Finset.mem_coe, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h | h | h
      · exact h
      · exact False.elim (hux (Subtype.ext h))
      · exact False.elim (u.2 (Subtype.ext h))
    have h1 := identGraph_degree_other_no_common GS hxyS_ne u hux (hno_comm_Ca u.1.1 huCa)
    change (identGraph GS xS yS).degree u = G.degree u.1.1
    rw [h1, degree_induce_eq, hS_deg_u u.1.1 huCa]
  have hdeg_merged : 2 ≤ H.degree ⟨xS, hxyS_ne⟩ := by
    change 2 ≤ (identGraph GS xS yS).degree ⟨xS, hxyS_ne⟩
    rw [identGraph_degree_merged]
    have hdisjN : Disjoint (GS.neighborFinset xS) (GS.neighborFinset yS) := by
      rw [Finset.disjoint_left]; intro w hwx hwy
      rw [SimpleGraph.mem_neighborFinset] at hwx hwy
      have hwCa : w.1 ∈ Ca := by
        have := w.2
        simp only [S, Finset.mem_coe, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h | h | h
        · exact h
        · exact False.elim (G.loopless x (h ▸ hwx))
        · exact False.elim (hxy_nadj (h ▸ hwx))
      exact hno_comm_Ca w.1 hwCa ⟨hwx.symm, hwy.symm⟩
    have hdisj_xy : Disjoint (GS.neighborFinset xS ∪ GS.neighborFinset yS) ({xS, yS} : Finset _) := by
      rw [Finset.disjoint_left]; intro w hw hmem
      simp only [Finset.mem_union, SimpleGraph.mem_neighborFinset] at hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl
      · rcases hw with h | h
        · exact GS.loopless xS h
        · exact hxy_nadj h.symm
      · rcases hw with h | h
        · exact hxy_nadj h
        · exact GS.loopless yS h
    rw [Finset.sdiff_eq_self_of_disjoint hdisj_xy, Finset.card_union_of_disjoint hdisjN,
        SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.card_neighborFinset_eq_degree,
        degree_induce_eq, degree_induce_eq]
    have hx_ge := le_trans hxCa1 (Finset.card_le_card (Finset.inter_subset_inter_left (Finset.subset_union_left : Ca ⊆ S)))
    have hy_ge := le_trans hyCa1 (Finset.card_le_card (Finset.inter_subset_inter_left (Finset.subset_union_left : Ca ⊆ S)))
    omega
  have hH_not_pf : ¬ PowerFree H := by
    intro hH_pf
    have hH_min : MinDegGe H 2 := by
      intro u
      by_cases hux : u.1 = xS
      · have : u = ⟨xS, hxyS_ne⟩ := Subtype.ext hux; rw [this]; exact hdeg_merged
      · rw [hdeg_other u hux]; exact hG.1.2.1 u.1.1
    have hH_def : (Defects H).card ≤ 2 := by
      have ha_ne_y : (⟨a, by simp [S, haCa]⟩ : {z : V // z ∈ (S : Set V)}) ≠ yS := fun h => by
        have h1 : a = y := congrArg Subtype.val h
        exact hCa_no_xy.2 (h1 ▸ haCa)
      have hsub : Defects H ⊆ {⟨⟨a, by simp [S, haCa]⟩, ha_ne_y⟩, ⟨xS, hxyS_ne⟩} := by
        intro u hu
        have hdeg2 : H.degree u = 2 := (Finset.mem_filter.mp hu).2
        by_cases hux : u.1 = xS
        · exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr (Subtype.ext hux))
        · rw [hdeg_other u hux] at hdeg2
          have hud : u.1.1 ∈ Defects G := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdeg2⟩
          rw [hdef_eq] at hud; simp only [Finset.mem_insert, Finset.mem_singleton] at hud
          rcases hud with hua | hub
          · exact Finset.mem_insert.mpr (Or.inl (Subtype.ext (Subtype.ext hua)))
          · have huCa : u.1.1 ∈ Ca := by
              have := u.1.2
              simp only [S, Finset.mem_coe, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at this
              rcases this with h | h | h
              · exact h
              · exact False.elim (hux (Subtype.ext h))
              · exact False.elim (u.2 (Subtype.ext h))
            exact False.elim (Finset.disjoint_left.mp hdisj_ab (hub ▸ huCa) hbCb)
      exact le_trans (Finset.card_le_card hsub) Finset.card_le_two
    have hlt : Fintype.card {w : {z : V // z ∈ (S : Set V)} // w ≠ yS} < Fintype.card V := by
      have h1 : Fintype.card {w : {z : V // z ∈ (S : Set V)} // w = yS} = 1 := Fintype.card_unique
      have h2 : Fintype.card {z : V // z ∈ (S : Set V)} = S.card := by
        rw [Fintype.card_subtype]; congr 1; ext z; simp
      rw [Fintype.card_subtype_compl, h1, h2]
      have hS_le : S.card ≤ Fintype.card V := Finset.card_le_univ S
      have hS_pos : 0 < S.card := Finset.card_pos.mpr ⟨x, by simp [S]⟩
      omega
    exact minimal_bad2_no_smaller hG H ⟨hH_pf, hH_min, hH_def⟩ hlt
  have hcyc : HasPowerCycle H := not_not.mp hH_not_pf
  rcases identGraph_cycle_lifts_to_dyadic_path hGS_pf hxyS_ne hcyc with ⟨pS, hpS, hpow⟩
  let p : G.Walk x y := pS.map (SimpleGraph.Embedding.induce (S : Set V)).toHom
  refine ⟨p, hpS.map Subtype.val_injective, ?_, by dsimp only [p]; rw [Walk.length_map]; exact hpow⟩
  intro w hw
  dsimp only [p] at hw
  rw [Walk.support_map] at hw
  rcases List.mem_map.mp hw with ⟨u, _, rfl⟩
  have := u.2
  simp only [S, Finset.mem_coe, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at this
  exact this

/-- PILLAR 2.4: Tutte 2-Cut Dyadic Scale Asymmetry Theorem (`ka ≠ kb`). -/
theorem minimal_bad2_nonadj_two_cut_scale_asymmetry {V : Type} [Fintype V]
    {G : SimpleGraph V} (hG : MinimalBad2 G) {x y a b : V} {Ca Cb : Finset V}
    (hxy_ne : x ≠ y) (hxy_nadj : ¬ G.Adj x y)
    (hab : a ≠ b) (ha : a ∈ Defects G) (hb : b ∈ Defects G)
    (haCa : a ∈ Ca) (hbCb : b ∈ Cb)
    (hdisj_ab : Disjoint Ca Cb)
    (hCa_no_xy : x ∉ Ca ∧ y ∉ Ca) (hCb_no_xy : x ∉ Cb ∧ y ∉ Cb)
    (hcover : Ca ∪ Cb ∪ {x, y} = Finset.univ)
    (hno_cross : ∀ u ∈ Ca, ∀ v ∈ Cb, ¬ G.Adj u v)
    (hxCa1 : 1 ≤ ((G.neighborFinset x) ∩ Ca).card)
    (hyCa1 : 1 ≤ ((G.neighborFinset y) ∩ Ca).card)
    (hxCb1 : 1 ≤ ((G.neighborFinset x) ∩ Cb).card)
    (hyCb1 : 1 ≤ ((G.neighborFinset y) ∩ Cb).card)
    (hno_comm : ∀ w : V, ¬ (G.Adj w x ∧ G.Adj w y)) :
    ∃ (pa pb : G.Walk x y) (ka kb : ℕ),
      pa.IsPath ∧ pb.IsPath ∧
      (∀ w ∈ pa.support, w ∈ Ca ∨ w = x ∨ w = y) ∧
      (∀ w ∈ pb.support, w ∈ Cb ∨ w = x ∨ w = y) ∧
      2 ≤ ka ∧ 2 ≤ kb ∧ pa.length = 2 ^ ka ∧ pb.length = 2 ^ kb ∧ ka ≠ kb := by
  rcases minimal_bad2_nonadj_two_cut_contraction_dyadic_path hG hxy_ne hxy_nadj hab ha hb
      haCa hbCb hdisj_ab hCa_no_xy hCb_no_xy hcover hno_cross hxCa1 hyCa1
      (fun w _ => hno_comm w) with ⟨pa, hpa, hpa_in, ka, hka, hpalen⟩
  have hcover_b : Cb ∪ Ca ∪ {x, y} = Finset.univ := by rw [Finset.union_comm Cb Ca]; exact hcover
  rcases minimal_bad2_nonadj_two_cut_contraction_dyadic_path hG hxy_ne hxy_nadj hab.symm hb ha
      hbCb haCa hdisj_ab.symm hCb_no_xy hCa_no_xy hcover_b
      (fun u hu v hv hadj => hno_cross v hv u hu hadj.symm) hxCb1 hyCb1
      (fun w _ => hno_comm w) with ⟨pb, hpb, hpb_in, kb, hkb, hpblen⟩
  refine ⟨pa, pb, ka, kb, hpa, hpb, hpa_in, hpb_in, hka, hkb, hpalen, hpblen, ?_⟩
  intro heq; subst heq
  have hge4 : 4 ≤ 2 ^ ka := calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ ka := Nat.pow_le_pow_right (by norm_num) hka
  have hdisj_supp : ∀ w, w ∈ pa.support → w ∈ pb.support → w = x ∨ w = y := by
    intro w hwp hwq
    rcases hpa_in w hwp with hwCa | hxy
    · rcases hpb_in w hwq with hwCb | hxy
      · exact False.elim (Finset.disjoint_left.mp hdisj_ab hwCa hwCb)
      · exact hxy
    · exact hxy
  rcases two_internally_disjoint_paths_cycle pa pb hpa hpb (by omega) (by omega) (by omega) hdisj_supp
    with ⟨hcyc, hclen⟩
  apply hG.1.1
  refine ⟨x, pa.append pb.reverse, hcyc, ka + 1, by omega, ?_⟩
  rw [hclen, hpalen, hpblen, pow_succ]; omega

/-- PILLAR 2.5: Defect Dual-Cycle Forcing (Non-Adjacent Neighbors). -/
theorem minimal_bad2_defect_nonadj_neighbors_dual_cycles {V : Type} [Fintype V]
    {G : SimpleGraph V} (hG : MinimalBad2 G) {a b a1 a2 : V}
    (hab : a ≠ b) (ha : a ∈ Defects G) (hb : b ∈ Defects G)
    (ha12 : a1 ≠ a2) (ha12_nadj : ¬ G.Adj a1 a2)
    (hNa : G.neighborFinset a = {a1, a2})
    (hb_not : b ≠ a1 ∧ b ≠ a2)
    (ha1_deg : G.degree a1 = 3) (ha2_deg : G.degree a2 = 3)
    (hno_comm_other : ∀ w : V, w ≠ a → ¬ (G.Adj w a1 ∧ G.Adj w a2)) :
    (∃ (c1 : G.Walk a a) (k1 : ℕ), c1.IsCycle ∧ 2 ≤ k1 ∧ c1.length = 2 ^ k1 + 1) ∧
    (∃ (c2 : G.Walk a a) (k2 : ℕ), c2.IsCycle ∧ 2 ≤ k2 ∧ c2.length = 2 ^ k2 + 2) := by
  let Ca : Finset V := {a}
  let Cb : Finset V := ({a, a1, a2} : Finset V)ᶜ
  have haa1 : G.Adj a a1 := (SimpleGraph.mem_neighborFinset G a a1).mp (by rw [hNa]; simp)
  have haa2 : G.Adj a a2 := (SimpleGraph.mem_neighborFinset G a a2).mp (by rw [hNa]; simp)
  have ha1_ne_a : a1 ≠ a := (G.ne_of_adj haa1).symm
  have ha2_ne_a : a2 ≠ a := (G.ne_of_adj haa2).symm
  have hbCb : b ∈ Cb := by
    simp only [Cb, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hab.symm, hb_not.1, hb_not.2⟩
  have hdisj : Disjoint Cb Ca := by
    rw [Finset.disjoint_right]; intro w hw
    rw [Finset.mem_singleton] at hw; subst hw; simp [Cb]
  have hCb_no : a1 ∉ Cb ∧ a2 ∉ Cb := by simp [Cb]
  have hCa_no : a1 ∉ Ca ∧ a2 ∉ Ca := ⟨by simp [Ca, ha1_ne_a], by simp [Ca, ha2_ne_a]⟩
  have hcover : Cb ∪ Ca ∪ {a1, a2} = Finset.univ := by
    ext u; simp only [Cb, Ca, Finset.mem_union, Finset.mem_compl, Finset.mem_insert,
      Finset.mem_singleton, Finset.mem_univ, iff_true]; tauto
  have hno_cross : ∀ u ∈ Cb, ∀ v ∈ Ca, ¬ G.Adj u v := by
    intro u huCb v hvCa hadj
    have hveq : v = a := Finset.mem_singleton.mp hvCa
    subst hveq
    have huN : u ∈ G.neighborFinset a := (SimpleGraph.mem_neighborFinset G a u).mpr hadj.symm
    rw [hNa] at huN; simp only [Finset.mem_insert, Finset.mem_singleton] at huN
    simp only [Cb, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at huCb
    rcases huN with rfl | rfl
    · exact huCb.2.1 rfl
    · exact huCb.2.2 rfl
  have ha1_Cb : ((G.neighborFinset a1) ∩ Cb).card = 2 := by
    have heq : (G.neighborFinset a1) ∩ Cb = (G.neighborFinset a1).erase a := by
      ext w
      simp only [Finset.mem_inter, Finset.mem_erase, SimpleGraph.mem_neighborFinset,
        Cb, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]
      constructor
      · rintro ⟨hw, hwa, _, _⟩; exact ⟨hwa, hw⟩
      · rintro ⟨hwa, hw⟩
        exact ⟨hw, hwa, G.ne_of_adj hw.symm, fun h => ha12_nadj (h ▸ hw)⟩
    rw [heq, Finset.card_erase_of_mem ((SimpleGraph.mem_neighborFinset G a1 a).mpr haa1.symm),
        SimpleGraph.card_neighborFinset_eq_degree, ha1_deg]
  have ha2_Cb : ((G.neighborFinset a2) ∩ Cb).card = 2 := by
    have heq : (G.neighborFinset a2) ∩ Cb = (G.neighborFinset a2).erase a := by
      ext w
      simp only [Finset.mem_inter, Finset.mem_erase, SimpleGraph.mem_neighborFinset,
        Cb, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]
      constructor
      · rintro ⟨hw, hwa, _, _⟩; exact ⟨hwa, hw⟩
      · rintro ⟨hwa, hw⟩
        exact ⟨hw, hwa, fun h => ha12_nadj (h ▸ hw).symm, G.ne_of_adj hw.symm⟩
    rw [heq, Finset.card_erase_of_mem ((SimpleGraph.mem_neighborFinset G a2 a).mpr haa2.symm),
        SimpleGraph.card_neighborFinset_eq_degree, ha2_deg]
  have close_via_a : ∀ (p : G.Walk a1 a2), p.IsPath → a ∉ p.support → 1 ≤ p.length →
      ∃ c : G.Walk a a, c.IsCycle ∧ c.length = p.length + 2 := by
    intro p hp ha_not hp1
    let q : G.Walk a1 a2 := Walk.cons haa1.symm (Walk.cons haa2 Walk.nil)
    have hq_path : q.IsPath := Walk.IsPath.mk' (by
      simp only [q, Walk.support_cons, Walk.support_nil, List.nodup_cons, List.mem_cons,
        List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil, and_true]
      exact ⟨⟨ha1_ne_a, ha12⟩, ha2_ne_a.symm⟩)
    have hdisj_pq : ∀ w, w ∈ p.support → w ∈ q.support → w = a1 ∨ w = a2 := by
      intro w hwp hwq
      simp only [q, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hwq
      rcases hwq with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact False.elim (ha_not hwp)
      · exact Or.inr rfl
    rcases two_internally_disjoint_paths_cycle p q hp hq_path hp1 (by simp [q])
        (by simp [q]; omega) hdisj_pq with ⟨hcyc, hclen⟩
    have ha_in_c : a ∈ (p.append q.reverse).support := by
      rw [Walk.support_append]
      exact List.mem_append_right _ (by simp [q])
    refine ⟨(p.append q.reverse).rotate a ha_in_c, hcyc.rotate ha_in_c, ?_⟩
    simpa [q] using hclen
  constructor
  · rcases minimal_bad2_nonadj_two_cut_torso_fermat_path hG ha12 ha12_nadj hab.symm hb ha
        hbCb (Finset.mem_singleton_self a) hdisj hCb_no hCa_no hcover hno_cross
        (by omega) (by omega) (Or.inl (by omega)) with ⟨p1, hp1, hp1_in, k1, hk1, hp1len⟩
    have ha_not1 : a ∉ p1.support := by
      intro ha_in
      rcases hp1_in a ha_in with h | h | h
      · exact (Finset.mem_compl.mp h) (by simp)
      · exact ha1_ne_a h.symm
      · exact ha2_ne_a h.symm
    have hge4 : 4 ≤ 2 ^ k1 := calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k1 := Nat.pow_le_pow_right (by norm_num) hk1
    rcases close_via_a p1 hp1 ha_not1 (by omega) with ⟨c1, hc1, hc1len⟩
    exact ⟨c1, k1, hc1, hk1, by omega⟩
  · rcases minimal_bad2_nonadj_two_cut_contraction_dyadic_path hG ha12 ha12_nadj hab.symm hb ha
        hbCb (Finset.mem_singleton_self a) hdisj hCb_no hCa_no hcover hno_cross
        (by omega) (by omega) (fun w hw => hno_comm_other w (fun h => (Finset.mem_compl.mp hw) (by simp [h])))
        with ⟨p2, hp2, hp2_in, k2, hk2, hp2len⟩
    have ha_not2 : a ∉ p2.support := by
      intro ha_in
      rcases hp2_in a ha_in with h | h | h
      · exact (Finset.mem_compl.mp h) (by simp)
      · exact ha1_ne_a h.symm
      · exact ha2_ne_a h.symm
    have hge4 : 4 ≤ 2 ^ k2 := calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k2 := Nat.pow_le_pow_right (by norm_num) hk2
    rcases close_via_a p2 hp2 ha_not2 (by omega) with ⟨c2, hc2, hc2len⟩
    exact ⟨c2, k2, hc2, hk2, by omega⟩

end

end E64Wave7Agent3P2
