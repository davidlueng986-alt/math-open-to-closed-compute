import Core
import Descent
import ClassHSharpCode

/-!
# Wave 3 Agent #2 — Module 3: New Local-Global Cycle & Path Forcing Reductions
-/

namespace E64Wave3Local
open SimpleGraph Erdos64Closure E64Core Erdos64Descent E64Wave3ClassH
universe u

private lemma path_of_cycle_with_edge {W : Type u} [DecidableEq W]
    {G H : SimpleGraph W} (u v : W) (huv : u ≠ v)
    (hsub : ∀ x y, H.Adj x y → G.Adj x y ∨ s(x, y) = s(u, v))
    {v0 : W} (c : H.Walk v0 v0) (hcyc : c.IsCycle) (hmem : s(u, v) ∈ c.edges) :
    ∃ p : G.Walk u v, p.IsPath ∧ p.length + 1 = c.length := by
  classical
  have humem : u ∈ c.support := Walk.fst_mem_support_of_mem_edges c hmem
  let c1 := c.rotate humem
  have hc1 : c1.IsCycle := hcyc.rotate humem
  have hlen1 : c1.length = c.length := Walk.length_rotate c humem
  have hmem1 : s(u, v) ∈ c1.edges := (Walk.edges_rotate c humem).mem_iff.mpr hmem
  cases hc1_eq : c1 with
  | nil => exact False.elim (hc1.ne_nil hc1_eq)
  | @cons _ w _ huw p1 =>
    by_cases hwv : w = v
    · subst hwv
      have hnotmem : s(u, v) ∉ p1.edges := by
        have hnd := hc1.isTrail.edges_nodup
        rw [hc1_eq, Walk.edges_cons, List.nodup_cons] at hnd
        exact hnd.1
      have htrans : ∀ e ∈ p1.edges, e ∈ G.edgeSet := by
        intro e he
        induction e using Sym2.ind with
        | _ x y =>
          have hH : H.Adj x y := p1.edges_subset_edgeSet he
          rcases hsub x y hH with hG | heq
          · exact hG
          · exact False.elim (hnotmem (heq ▸ he))
      let q : G.Walk v u := p1.transfer G htrans
      have hq_path : q.IsPath := by
        refine Walk.IsPath.mk' ?_
        have hnd := hc1.support_nodup
        rw [hc1_eq, Walk.support_cons, List.tail_cons] at hnd
        simpa [q] using hnd
      refine ⟨q.reverse, hq_path.reverse, ?_⟩
      simp only [Walk.length_reverse, q, Walk.length_transfer]
      have hl : c1.length = p1.length + 1 := by rw [hc1_eq, Walk.length_cons]
      omega
    · let c2 := c1.reverse
      have hc2 : c2.IsCycle := hc1.reverse
      have hlen2 : c2.length = c.length := by rw [Walk.length_reverse, hlen1]
      have hmem2 : s(u, v) ∈ c2.edges := by
        rw [Walk.edges_reverse, List.mem_reverse]; exact hmem1
      cases hc2_eq : c2 with
      | nil => exact False.elim (hc2.ne_nil hc2_eq)
      | @cons _ w2 _ huw2 p2 =>
        have hw2v : w2 = v := by
          by_contra hne
          have hp1_path : p1.IsPath := by
            refine Walk.IsPath.mk' ?_
            have hnd := hc1.support_nodup
            rw [hc1_eq, Walk.support_cons, List.tail_cons] at hnd
            exact hnd
          have hp1r_path : p1.reverse.IsPath := hp1_path.reverse
          cases hpr : p1.reverse with
          | nil =>
            have : p1 = Walk.nil := by have := congrArg Walk.reverse hpr; simpa using this
            rw [this] at hc1_eq
            exact H.ne_of_adj huw rfl
          | @cons _ w3 _ huw3 p3 =>
            have hc2_alt : c2 = Walk.cons huw3 (p3.concat huw.symm) := by
              change c1.reverse = _
              rw [hc1_eq, Walk.reverse_cons, hpr, Walk.cons_concat]
            have hw3_eq : w3 = w2 := by
              have h1 := congrArg Walk.support (hc2_eq.symm.trans hc2_alt)
              simp only [Walk.support_cons] at h1
              have h2 := congrArg List.tail h1
              simp only [List.tail_cons] at h2
              have h3 := congrArg List.head? h2
              simp only [Walk.head?_support] at h3
              exact (Option.some.inj h3).symm
            have hmem_pr : s(u, v) ∈ p1.reverse.edges := by
              rw [Walk.edges_reverse, List.mem_reverse]
              rw [hc1_eq, Walk.edges_cons, List.mem_cons] at hmem1
              rcases hmem1 with heq | hp
              · rw [Sym2.eq_iff] at heq
                rcases heq with ⟨_, rfl⟩ | ⟨h1, _⟩
                · exact False.elim (hwv rfl)
                · exact False.elim (huv h1)
              · exact hp
            rw [hpr, Walk.edges_cons, List.mem_cons] at hmem_pr
            rcases hmem_pr with heq | hp3
            · rw [Sym2.eq_iff] at heq
              rcases heq with ⟨_, rfl⟩ | ⟨h1, _⟩
              · exact hne hw3_eq.symm
              · exact huv h1
            · have hu_p3 : u ∈ p3.support := Walk.fst_mem_support_of_mem_edges p3 hp3
              have hnd_pr := hp1r_path.support_nodup
              rw [hpr, Walk.support_cons, List.nodup_cons] at hnd_pr
              exact hnd_pr.1 hu_p3
        subst hw2v
        have hnotmem : s(u, v) ∉ p2.edges := by
          have hnd := hc2.isTrail.edges_nodup
          rw [hc2_eq, Walk.edges_cons, List.nodup_cons] at hnd
          exact hnd.1
        have htrans : ∀ e ∈ p2.edges, e ∈ G.edgeSet := by
          intro e he
          induction e using Sym2.ind with
          | _ x y =>
            have hH : H.Adj x y := p2.edges_subset_edgeSet he
            rcases hsub x y hH with hG | heq
            · exact hG
            · exact False.elim (hnotmem (heq ▸ he))
        let q : G.Walk v u := p2.transfer G htrans
        have hq_path : q.IsPath := by
          refine Walk.IsPath.mk' ?_
          have hnd := hc2.support_nodup
          rw [hc2_eq, Walk.support_cons, List.tail_cons] at hnd
          simpa [q] using hnd
        refine ⟨q.reverse, hq_path.reverse, ?_⟩
        simp only [Walk.length_reverse, q, Walk.length_transfer]
        have hl : c2.length = p2.length + 1 := by rw [hc2_eq, Walk.length_cons]
        omega

/-- Theorem 1 (2-Edge Y-Reduction in Triangle-Free MinimalBad):
    For every degree-3 vertex v with distinct neighbors a, b, c in a triangle-free MinimalBad G,
    G - v contains a simple a-b path OR a simple b-c path of length 2^k - 1 (k ≥ 2). -/
theorem trifree_two_edge_y_reduction {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (htf : ∀ x y z : V, G.Adj x y → G.Adj y z → ¬G.Adj x z)
    (v a b c : V) (hv : G.degree v = 3)
    (hva : G.Adj v a) (hvb : G.Adj v b) (hvc : G.Adj v c)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ∃ k : ℕ, 2 ≤ k ∧
      ((∃ p : (G.induce {x : V | x ≠ v}).Walk ⟨a, (G.ne_of_adj hva).symm⟩ ⟨b, (G.ne_of_adj hvb).symm⟩,
          p.IsPath ∧ p.length + 1 = 2 ^ k) ∨
       (∃ p : (G.induce {x : V | x ≠ v}).Walk ⟨b, (G.ne_of_adj hvb).symm⟩ ⟨c, (G.ne_of_adj hvc).symm⟩,
          p.IsPath ∧ p.length + 1 = 2 ^ k)) := by
  classical
  let Sv : Set V := {x : V | x ≠ v}
  let G0 := G.induce Sv
  let _ : DecidableRel G0.Adj := inferInstanceAs (DecidableRel (G.induce Sv).Adj)
  let a' : Sv := ⟨a, (G.ne_of_adj hva).symm⟩
  let b' : Sv := ⟨b, (G.ne_of_adj hvb).symm⟩
  let c' : Sv := ⟨c, (G.ne_of_adj hvc).symm⟩
  have hab' : a' ≠ b' := fun h => hab (congrArg Subtype.val h)
  have hbc' : b' ≠ c' := fun h => hbc (congrArg Subtype.val h)
  have hac' : a' ≠ c' := fun h => hac (congrArg Subtype.val h)
  have hnab : ¬G0.Adj a' b' := htf a v b hva.symm hvb
  have hnbc : ¬G0.Adj b' c' := htf b v c hvb.symm hvc
  let H1 := G0 ⊔ SimpleGraph.edge a' b'
  let H := H1 ⊔ SimpleGraph.edge b' c'
  let _ : DecidableRel H1.Adj := inferInstanceAs (DecidableRel (G0 ⊔ SimpleGraph.edge a' b').Adj)
  let _ : DecidableRel H.Adj := inferInstanceAs (DecidableRel (H1 ⊔ SimpleGraph.edge b' c').Adj)
  have hnab_H1 : ¬H1.Adj b' c' := by
    intro h
    rcases (SimpleGraph.sup_adj G0 (SimpleGraph.edge a' b') b' c').mp h with h0 | he
    · exact hnbc h0
    · rcases (SimpleGraph.edge_adj a' b' b' c').mp he |>.1 with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact hab' h1.symm
      · exact hac' h2.symm
  have hdeg_ge : ∀ u : Sv, G.degree u.1 ≤ H.degree u := by
    intro u
    have hd0 := induce_delete_degree G v u
    change G0.degree u + (if G.Adj u.1 v then 1 else 0) = G.degree u.1 at hd0
    have hle1 : G0.degree u ≤ H1.degree u := G0.degree_le_of_le (H := H1) le_sup_left
    have hle2 : H1.degree u ≤ H.degree u := H1.degree_le_of_le (H := H) le_sup_left
    by_cases hua : u = a'
    · subst hua
      have hda := degree_add_new_edge_left G0 a' b' hab' hnab
      simp [hva.symm] at hd0; omega
    by_cases hub : u = b'
    · subst hub
      have hdb := degree_add_new_edge_right G0 a' b' hab' hnab
      simp [hvb.symm] at hd0; omega
    by_cases huc : u = c'
    · subst huc
      have hdc := degree_add_new_edge_right H1 b' c' hbc' hnab_H1
      simp [hvc.symm] at hd0; omega
    have hnv : ¬G.Adj u.1 v := by
      intro huv
      have hsub : ({a, b, c} : Finset V) ⊆ G.neighborFinset v := by
        intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with h | h | h
        · rw [h]; exact (G.mem_neighborFinset v a).mpr hva
        · rw [h]; exact (G.mem_neighborFinset v b).mpr hvb
        · rw [h]; exact (G.mem_neighborFinset v c).mpr hvc
      have hcard3 : ({a, b, c} : Finset V).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]
      have heq : ({a, b, c} : Finset V) = G.neighborFinset v :=
        Finset.eq_of_subset_of_card_le hsub (by rw [SimpleGraph.card_neighborFinset_eq_degree, hv, hcard3])
      have hmem : u.1 ∈ ({a, b, c} : Finset V) := heq.symm ▸ (G.mem_neighborFinset v u.1).mpr huv.symm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h | h
      · exact hua (Subtype.ext h)
      · exact hub (Subtype.ext h)
      · exact huc (Subtype.ext h)
    simp [hnv] at hd0; omega
  have hWlt : Fintype.card Sv < Fintype.card V := by
    rw [Fintype.card_subtype, show (Finset.univ.filter fun x : V => x ∈ Sv) = Finset.univ.erase v by ext x; simp [Sv]]
    have := Finset.card_erase_add_one (Finset.mem_univ v); omega
  have hWge2 : 2 ≤ Fintype.card Sv := by
    have hVge4 : 4 ≤ Fintype.card V := by have := G.degree_lt_card_verts v; omega
    rw [Fintype.card_subtype, show (Finset.univ.filter fun x : V => x ∈ Sv) = Finset.univ.erase v by ext x; simp [Sv]]
    have := Finset.card_erase_add_one (Finset.mem_univ v); omega
  have hnear : Near H := by
    obtain ⟨_, w, hw⟩ := hm.1
    by_cases hwv : w = v
    · exact near_of_except H a' hWge2 (fun u _ => (hw u.1 (hwv ▸ u.2)).trans (hdeg_ge u))
    · exact near_of_except H ⟨w, hwv⟩ hWge2 (fun u hu => (hw u.1 (fun h => hu (Subtype.ext h))).trans (hdeg_ge u))
  obtain ⟨k, v0, cyc, hk, hcyc, hlen⟩ := hm.2.2.1 Sv H hWlt hnear
  have hpow4 : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by decide
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
  by_cases h1 : s(a', b') ∈ cyc.edges
  · by_cases h2 : s(b', c') ∈ cyc.edges
    · have hbmem : b' ∈ cyc.support := Walk.snd_mem_support_of_mem_edges cyc h1
      let cyc1 := cyc.rotate hbmem
      have hcyc1 : cyc1.IsCycle := hcyc.rotate hbmem
      have hlen1 : cyc1.length = 2 ^ k := (Walk.length_rotate cyc hbmem).trans hlen
      have h1' : s(a', b') ∈ cyc1.edges := (Walk.edges_rotate cyc hbmem).mem_iff.mpr h1
      have h2' : s(b', c') ∈ cyc1.edges := (Walk.edges_rotate cyc hbmem).mem_iff.mpr h2
      cases hceq : cyc1 with
      | nil => exact False.elim (hcyc1.ne_nil hceq)
      | @cons _ u1 _ hbu1 p1 =>
        have hp1_path : p1.IsPath := by
          refine Walk.IsPath.mk' ?_
          have hnd := hcyc1.support_nodup
          rw [hceq, Walk.support_cons, List.tail_cons] at hnd
          exact hnd
        cases hpr : p1.reverse with
        | nil =>
          have : p1 = Walk.nil := by have := congrArg Walk.reverse hpr; simpa using this
          rw [this] at hceq; exact False.elim (H.ne_of_adj hbu1 rfl)
        | @cons _ u2 _ hbu2 q_rev =>
          let q := q_rev.reverse
          have hb_not_q : b' ∉ q.support := by
            have hnd := hp1_path.reverse.support_nodup
            rw [hpr, Walk.support_cons, List.nodup_cons] at hnd
            simpa [q, Walk.support_reverse] using hnd.1
          have hp1_eq : p1 = q.concat hbu2.symm := by
            have := congrArg Walk.reverse hpr
            simpa [q, Walk.reverse_cons] using this
          have hq_no1 : s(a', b') ∉ q.edges := fun hm => hb_not_q (Walk.snd_mem_support_of_mem_edges q hm)
          have hq_no2 : s(b', c') ∉ q.edges := fun hm => hb_not_q (Walk.fst_mem_support_of_mem_edges q hm)
          have hedges_eq : cyc1.edges = s(b', u1) :: (q.edges ++ [s(u2, b')]) := by
            rw [hceq, hp1_eq, Walk.edges_cons, Walk.edges_concat]
          have hu12 : (u1 = a' ∧ u2 = c') ∨ (u1 = c' ∧ u2 = a') := by
            rw [hedges_eq, List.mem_cons, List.mem_append, List.mem_singleton] at h1' h2'
            have h1_or : s(a', b') = s(b', u1) ∨ s(a', b') = s(u2, b') := by
              rcases h1' with h | h | h
              · exact Or.inl h
              · exact False.elim (hq_no1 h)
              · exact Or.inr h
            have h2_or : s(b', c') = s(b', u1) ∨ s(b', c') = s(u2, b') := by
              rcases h2' with h | h | h
              · exact Or.inl h
              · exact False.elim (hq_no2 h)
              · exact Or.inr h
            have h1_u : u1 = a' ∨ u2 = a' := by
              rcases h1_or with h | h <;> rw [Sym2.eq_iff] at h
              · rcases h with ⟨h1, _⟩ | ⟨_, rfl⟩
                · exact False.elim (hab' h1)
                · exact Or.inl rfl
              · rcases h with ⟨rfl, _⟩ | ⟨_, h2⟩
                · exact Or.inr rfl
                · exact False.elim (hab' h2.symm)
            have h2_u : u1 = c' ∨ u2 = c' := by
              rcases h2_or with h | h <;> rw [Sym2.eq_iff] at h
              · rcases h with ⟨_, rfl⟩ | ⟨h1, _⟩
                · exact Or.inl rfl
                · exact False.elim (hbc' h1.symm)
              · rcases h with ⟨h1, _⟩ | ⟨_, rfl⟩
                · exact False.elim (hbc' h1.symm)
                · exact Or.inr rfl
            rcases h1_u with rfl | rfl <;> rcases h2_u with h | h
            · exact False.elim (hac' h)
            · exact Or.inl ⟨rfl, h⟩
            · exact Or.inr ⟨h, rfl⟩
            · exact False.elim (hac' h)
          have hq_G0 : ∀ e ∈ q.edges, e ∈ G0.edgeSet := by
            intro e he
            induction e using Sym2.ind with
            | _ x y =>
              have hH : H.Adj x y := q.edges_subset_edgeSet he
              rcases (SimpleGraph.sup_adj H1 (SimpleGraph.edge b' c') x y).mp hH with hH1 | he2
              · rcases (SimpleGraph.sup_adj G0 (SimpleGraph.edge a' b') x y).mp hH1 with hG0 | he1
                · exact hG0
                · rcases (SimpleGraph.edge_adj a' b' x y).mp he1 |>.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                  · exact False.elim (hq_no1 he)
                  · exact False.elim (hq_no1 (Sym2.eq_swap ▸ he))
              · rcases (SimpleGraph.edge_adj b' c' x y).mp he2 |>.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                · exact False.elim (hq_no2 he)
                · exact False.elim (hq_no2 (Sym2.eq_swap ▸ he))
          let qG : G.Walk u1.1 u2.1 := (q.transfer G0 hq_G0).map ⟨Subtype.val, fun h => h⟩
          have hqG_nodup : qG.support.Nodup := by
            have hnd : q.support.Nodup := by
              have h := hp1_path.reverse.support_nodup
              rw [hpr, Walk.support_cons, List.nodup_cons] at h
              simpa [q, Walk.support_reverse] using h.2
            simpa [qG, Walk.support_map] using hnd.map Subtype.val_injective
          have hv_not_qG : v ∉ qG.support := by
            intro hvmem
            rw [Walk.support_map, List.mem_map] at hvmem
            obtain ⟨x, _, hxv⟩ := hvmem
            exact x.2 hxv
          have hqG_len : qG.length + 2 = 2 ^ k := by
            have hl1 : cyc1.length = q.length + 2 := by
              rw [hceq, hp1_eq, Walk.length_cons, Walk.length_concat]
            simpa [qG] using (hl1.symm.trans hlen1).symm
          have hv_u1 : G.Adj v u1.1 := by rcases hu12 with ⟨rfl, _⟩ | ⟨rfl, _⟩; exact hva; exact hvc
          have hv_u2 : G.Adj u2.1 v := by rcases hu12 with ⟨_, rfl⟩ | ⟨_, rfl⟩; exact hvc.symm; exact hva.symm
          let badC : G.Walk v v := Walk.cons hv_u1 (qG.concat hv_u2)
          have hbad_len : badC.length = 2 ^ k := by
            simp only [badC, Walk.length_cons, Walk.length_concat]; omega
          have hbad_tail : badC.support.tail = qG.support ++ [v] := by
            simp only [badC, Walk.support_cons, List.tail_cons, Walk.support_concat]
          have hbad_nodup : badC.support.tail.Nodup := by
            rw [hbad_tail]
            exact List.nodup_append.mpr ⟨hqG_nodup, List.nodup_singleton v,
              fun x hx1 hx2 => hv_not_qG ((List.mem_singleton.mp hx2) ▸ hx1)⟩
          exact False.elim (hm.2.1 ⟨k, v, badC, hk, isCycle_of_support_tail_nodup badC hbad_nodup (by omega), hbad_len⟩)
    · have hsub : ∀ x y, H1.Adj x y → G0.Adj x y ∨ s(x, y) = s(a', b') := by
        intro x y h
        rcases (SimpleGraph.sup_adj G0 (SimpleGraph.edge a' b') x y).mp h with h0 | he
        · exact Or.inl h0
        · rcases (SimpleGraph.edge_adj a' b' x y).mp he |>.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inr rfl
          · exact Or.inr Sym2.eq_swap
      have htrans1 : ∀ e ∈ cyc.edges, e ∈ H1.edgeSet := by
        intro e he
        induction e using Sym2.ind with
        | _ x y =>
          have hH := cyc.edges_subset_edgeSet he
          rcases (SimpleGraph.sup_adj H1 (SimpleGraph.edge b' c') x y).mp hH with h1' | he2
          · exact h1'
          · rcases (SimpleGraph.edge_adj b' c' x y).mp he2 |>.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact False.elim (h2 he)
            · exact False.elim (h2 (Sym2.eq_swap ▸ he))
      let cycH1 := cyc.transfer H1 htrans1
      obtain ⟨p, hp, hplen⟩ := path_of_cycle_with_edge a' b' hab' hsub cycH1 (hcyc.transfer htrans1)
        (by simpa [cycH1] using h1)
      exact ⟨k, hk, Or.inl ⟨p, hp, by simpa [cycH1, hlen] using hplen⟩⟩
  · by_cases h2 : s(b', c') ∈ cyc.edges
    · let H2 := G0 ⊔ SimpleGraph.edge b' c'
      have hsub : ∀ x y, H2.Adj x y → G0.Adj x y ∨ s(x, y) = s(b', c') := by
        intro x y h
        rcases (SimpleGraph.sup_adj G0 (SimpleGraph.edge b' c') x y).mp h with h0 | he
        · exact Or.inl h0
        · rcases (SimpleGraph.edge_adj b' c' x y).mp he |>.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inr rfl
          · exact Or.inr Sym2.eq_swap
      have htrans2 : ∀ e ∈ cyc.edges, e ∈ H2.edgeSet := by
        intro e he
        induction e using Sym2.ind with
        | _ x y =>
          have hH := cyc.edges_subset_edgeSet he
          rcases (SimpleGraph.sup_adj H1 (SimpleGraph.edge b' c') x y).mp hH with h1' | he2
          · rcases (SimpleGraph.sup_adj G0 (SimpleGraph.edge a' b') x y).mp h1' with h0 | he1
            · exact (SimpleGraph.sup_adj G0 (SimpleGraph.edge b' c') x y).mpr (Or.inl h0)
            · rcases (SimpleGraph.edge_adj a' b' x y).mp he1 |>.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact False.elim (h1 he)
              · exact False.elim (h1 (Sym2.eq_swap ▸ he))
          · exact (SimpleGraph.sup_adj G0 (SimpleGraph.edge b' c') x y).mpr (Or.inr he2)
      let cycH2 := cyc.transfer H2 htrans2
      obtain ⟨p, hp, hplen⟩ := path_of_cycle_with_edge b' c' hbc' hsub cycH2 (hcyc.transfer htrans2)
        (by simpa [cycH2] using h2)
      exact ⟨k, hk, Or.inr ⟨p, hp, by simpa [cycH2, hlen] using hplen⟩⟩
    · have htrans0 : ∀ e ∈ cyc.edges, e ∈ G0.edgeSet := by
        intro e he
        induction e using Sym2.ind with
        | _ x y =>
          have hH := cyc.edges_subset_edgeSet he
          rcases (SimpleGraph.sup_adj H1 (SimpleGraph.edge b' c') x y).mp hH with h1' | he2
          · rcases (SimpleGraph.sup_adj G0 (SimpleGraph.edge a' b') x y).mp h1' with h0 | he1
            · exact h0
            · rcases (SimpleGraph.edge_adj a' b' x y).mp he1 |>.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact False.elim (h1 he)
              · exact False.elim (h1 (Sym2.eq_swap ▸ he))
          · rcases (SimpleGraph.edge_adj b' c' x y).mp he2 |>.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact False.elim (h2 he)
            · exact False.elim (h2 (Sym2.eq_swap ▸ he))
      exact False.elim (hm.2.1 (power_induce G _ ⟨k, v0, cyc.transfer G0 htrans0, hk, hcyc.transfer htrans0, by simpa using hlen⟩))

/-- Theorem 2 (Class H High-Neighbor Suppression):
    For any degree-3 vertex v adjacent to x ∈ V_{≥4} with other two non-adjacent neighbors a, c,
    G - v contains a simple a-c path of length 2^k - 1 (k ≥ 2). -/
theorem class_h_high_neighbor_suppression {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (v x a c : V) (hv : G.degree v = 3) (hx : 4 ≤ G.degree x)
    (hvx : G.Adj v x) (hva : G.Adj v a) (hvc : G.Adj v c)
    (hxa : x ≠ a) (hxc : x ≠ c) (hac : a ≠ c) (hnac : ¬G.Adj a c) :
    ∃ (k : ℕ) (p : (G.induce {u : V | u ≠ v}).Walk ⟨a, (G.ne_of_adj hva).symm⟩ ⟨c, (G.ne_of_adj hvc).symm⟩),
      2 ≤ k ∧ p.IsPath ∧ p.length + 1 = 2 ^ k := by
  classical
  let Sv : Set V := {u : V | u ≠ v}
  let G0 := G.induce Sv
  let _ : DecidableRel G0.Adj := inferInstanceAs (DecidableRel (G.induce Sv).Adj)
  let a' : Sv := ⟨a, (G.ne_of_adj hva).symm⟩
  let c' : Sv := ⟨c, (G.ne_of_adj hvc).symm⟩
  have hac' : a' ≠ c' := fun h => hac (congrArg Subtype.val h)
  let H := G0 ⊔ SimpleGraph.edge a' c'
  let _ : DecidableRel H.Adj := inferInstanceAs (DecidableRel (G0 ⊔ SimpleGraph.edge a' c').Adj)
  have hdeg_ge : ∀ u : Sv, u.1 ≠ x → G.degree u.1 ≤ H.degree u := by
    intro u hux
    have hd0 := induce_delete_degree G v u
    change G0.degree u + (if G.Adj u.1 v then 1 else 0) = G.degree u.1 at hd0
    have hle : G0.degree u ≤ H.degree u := G0.degree_le_of_le (H := H) le_sup_left
    by_cases hua : u = a'
    · subst hua
      have hda := degree_add_new_edge_left G0 a' c' hac' hnac
      simp [hva.symm] at hd0; omega
    by_cases huc : u = c'
    · subst huc
      have hdc := degree_add_new_edge_right G0 a' c' hac' hnac
      simp [hvc.symm] at hd0; omega
    have hnv : ¬G.Adj u.1 v := by
      intro huv
      have hsub : ({x, a, c} : Finset V) ⊆ G.neighborFinset v := by
        intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with h | h | h
        · rw [h]; exact (G.mem_neighborFinset v x).mpr hvx
        · rw [h]; exact (G.mem_neighborFinset v a).mpr hva
        · rw [h]; exact (G.mem_neighborFinset v c).mpr hvc
      have hcard3 : ({x, a, c} : Finset V).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hxa, hxc]), Finset.card_pair hac]
      have heq : ({x, a, c} : Finset V) = G.neighborFinset v :=
        Finset.eq_of_subset_of_card_le hsub (by rw [SimpleGraph.card_neighborFinset_eq_degree, hv, hcard3])
      have hmem : u.1 ∈ ({x, a, c} : Finset V) := heq.symm ▸ (G.mem_neighborFinset v u.1).mpr huv.symm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h | h
      · exact hux h
      · exact hua (Subtype.ext h)
      · exact huc (Subtype.ext h)
    simp [hnv] at hd0; omega
  have hdeg_x : 3 ≤ H.degree ⟨x, (G.ne_of_adj hvx).symm⟩ := by
    have hd0 := induce_delete_degree G v ⟨x, (G.ne_of_adj hvx).symm⟩
    change G0.degree ⟨x, (G.ne_of_adj hvx).symm⟩ + (if G.Adj x v then 1 else 0) = G.degree x at hd0
    have hle : G0.degree ⟨x, (G.ne_of_adj hvx).symm⟩ ≤ H.degree ⟨x, (G.ne_of_adj hvx).symm⟩ :=
      G0.degree_le_of_le (H := H) le_sup_left
    simp [hvx.symm] at hd0; omega
  have hWlt : Fintype.card Sv < Fintype.card V := by
    rw [Fintype.card_subtype, show (Finset.univ.filter fun u : V => u ∈ Sv) = Finset.univ.erase v by ext u; simp [Sv]]
    have := Finset.card_erase_add_one (Finset.mem_univ v); omega
  have hWge2 : 2 ≤ Fintype.card Sv := by
    have hVge4 : 4 ≤ Fintype.card V := by have := G.degree_lt_card_verts v; omega
    rw [Fintype.card_subtype, show (Finset.univ.filter fun u : V => u ∈ Sv) = Finset.univ.erase v by ext u; simp [Sv]]
    have := Finset.card_erase_add_one (Finset.mem_univ v); omega
  have hnear : Near H := by
    obtain ⟨_, w, hw⟩ := hm.1
    by_cases hwv : w = v
    · apply near_of_except H a' hWge2
      intro u _
      by_cases hux : u.1 = x
      · have : u = ⟨x, (G.ne_of_adj hvx).symm⟩ := Subtype.ext hux
        rw [this]; exact hdeg_x
      · exact (hw u.1 (hwv ▸ u.2)).trans (hdeg_ge u hux)
    · apply near_of_except H ⟨w, hwv⟩ hWge2
      intro u hu
      by_cases hux : u.1 = x
      · have : u = ⟨x, (G.ne_of_adj hvx).symm⟩ := Subtype.ext hux
        rw [this]; exact hdeg_x
      · exact (hw u.1 (fun h => hu (Subtype.ext h))).trans (hdeg_ge u hux)
  obtain ⟨k, v0, cyc, hk, hcyc, hlen⟩ := hm.2.2.1 Sv H hWlt hnear
  have hsub : ∀ u1 u2, H.Adj u1 u2 → G0.Adj u1 u2 ∨ s(u1, u2) = s(a', c') := by
    intro u1 u2 h
    rcases (SimpleGraph.sup_adj G0 (SimpleGraph.edge a' c') u1 u2).mp h with h0 | he
    · exact Or.inl h0
    · rcases (SimpleGraph.edge_adj a' c' u1 u2).mp he |>.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr rfl
      · exact Or.inr Sym2.eq_swap
  have hmem : s(a', c') ∈ cyc.edges := by
    by_contra hnot
    have htrans : ∀ e ∈ cyc.edges, e ∈ G0.edgeSet := by
      intro e he
      induction e using Sym2.ind with
      | _ u1 u2 =>
        rcases hsub u1 u2 (cyc.edges_subset_edgeSet he) with h0 | heq
        · exact h0
        · exact False.elim (hnot (heq ▸ he))
    exact hm.2.1 (power_induce G _ ⟨k, v0, cyc.transfer G0 htrans, hk, hcyc.transfer htrans, by simpa using hlen⟩)
  obtain ⟨p, hp, hplen⟩ := path_of_cycle_with_edge a' c' hac' hsub cyc hcyc hmem
  exact ⟨k, p, hk, hp, by omega⟩

private def contractEdge {V : Type u} [DecidableEq V] (G : SimpleGraph V) (y1 y2 : V) :
    SimpleGraph ↑({u : V | u ≠ y2} : Set V) where
  Adj a b := a ≠ b ∧
    if a.1 = y1 then (G.Adj y1 b.1 ∨ G.Adj y2 b.1)
    else if b.1 = y1 then (G.Adj a.1 y1 ∨ G.Adj a.1 y2)
    else G.Adj a.1 b.1
  symm := ⟨by
    intro a b ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    by_cases ha : a.1 = y1 <;> by_cases hb : b.1 = y1
    · exact False.elim (hne (Subtype.ext (ha.trans hb.symm)))
    · simp only [ha, hb, ite_true, ite_false] at h ⊢
      exact h.imp SimpleGraph.Adj.symm SimpleGraph.Adj.symm
    · simp only [ha, hb, ite_true, ite_false] at h ⊢
      exact h.imp SimpleGraph.Adj.symm SimpleGraph.Adj.symm
    · simp only [ha, hb, ite_false] at h ⊢
      exact h.symm⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

/-- Theorem 3 (Class H High-Triangle Edge Contraction, H-T-2 / H-T-3):
    For any triangle {x, y1, y2} with d(x) ≥ 4, d(y1) = d(y2) = 3, and external neighbors z1 of y1
    and z2 of y2, G - {y1, y2} contains a simple z1-z2 path of length 2^k - 2 (k ≥ 2). -/
theorem class_h_high_triangle_contraction {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (x y1 y2 z1 z2 : V)
    (hx : 4 ≤ G.degree x) (hy1 : G.degree y1 = 3) (hy2 : G.degree y2 = 3)
    (hxy1 : G.Adj x y1) (hxy2 : G.Adj x y2) (hy12 : G.Adj y1 y2)
    (hy1z1 : G.Adj y1 z1) (hz1x : z1 ≠ x) (hz1y2 : z1 ≠ y2)
    (hy2z2 : G.Adj y2 z2) (hz2x : z2 ≠ x) (hz2y1 : z2 ≠ y1) :
    ∃ (k : ℕ) (p : (G.induce {u : V | u ≠ y1 ∧ u ≠ y2}).Walk
        ⟨z1, ⟨(G.ne_of_adj hy1z1).symm, hz1y2⟩⟩
        ⟨z2, ⟨hz2y1, (G.ne_of_adj hy2z2).symm⟩⟩),
      2 ≤ k ∧ p.IsPath ∧ p.length + 2 = 2 ^ k := by
  classical
  have hc4 := minimal_bad_noC4 G hm
  have hy1_ne_y2 : y1 ≠ y2 := G.ne_of_adj hy12
  have hx_ne_y1 : x ≠ y1 := G.ne_of_adj hxy1
  have hx_ne_y2 : x ≠ y2 := G.ne_of_adj hxy2
  have hz1_ne_z2 : z1 ≠ z2 := by
    intro heq; subst heq
    have hsub : ({x, z1} : Finset V) ⊆ G.neighborFinset y1 ∩ G.neighborFinset y2 := by
      intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with h | h
      · rw [h]; exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset y1 x).mpr hxy1.symm, (G.mem_neighborFinset y2 x).mpr hxy2.symm⟩
      · rw [h]; exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset y1 z1).mpr hy1z1, (G.mem_neighborFinset y2 z1).mpr hy2z2⟩
    have hc := (Finset.card_le_card hsub).trans (hc4 y1 y2 hy1_ne_y2)
    rw [Finset.card_pair hz1x.symm] at hc; omega
  have hNy1 : G.neighborFinset y1 = {x, y2, z1} := by
    apply (Finset.eq_of_subset_of_card_le _ (by
      rw [SimpleGraph.card_neighborFinset_eq_degree, hy1,
        Finset.card_insert_of_notMem (by simp [hx_ne_y2, hz1x.symm]), Finset.card_pair hz1y2.symm])).symm
    intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with h | h | h
    · rw [h]; exact (G.mem_neighborFinset y1 x).mpr hxy1.symm
    · rw [h]; exact (G.mem_neighborFinset y1 y2).mpr hy12
    · rw [h]; exact (G.mem_neighborFinset y1 z1).mpr hy1z1
  have hNy2 : G.neighborFinset y2 = {x, y1, z2} := by
    apply (Finset.eq_of_subset_of_card_le _ (by
      rw [SimpleGraph.card_neighborFinset_eq_degree, hy2,
        Finset.card_insert_of_notMem (by simp [hx_ne_y1, hz2x.symm]), Finset.card_pair hz2y1.symm])).symm
    intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with h | h | h
    · rw [h]; exact (G.mem_neighborFinset y2 x).mpr hxy2.symm
    · rw [h]; exact (G.mem_neighborFinset y2 y1).mpr hy12.symm
    · rw [h]; exact (G.mem_neighborFinset y2 z2).mpr hy2z2
  let Sy2 : Set V := {u : V | u ≠ y2}
  let H := contractEdge G y1 y2
  let _ : DecidableRel H.Adj := inferInstanceAs (DecidableRel (contractEdge G y1 y2).Adj)
  let u0 : Sy2 := ⟨y1, hy1_ne_y2⟩
  let x' : Sy2 := ⟨x, hx_ne_y2⟩
  let z1' : Sy2 := ⟨z1, hz1y2⟩
  let z2' : Sy2 := ⟨z2, (G.ne_of_adj hy2z2).symm⟩
  have hNu0 : H.neighborFinset u0 = {x', z1', z2'} := by
    ext t
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton, H, contractEdge, u0]
    constructor
    · rintro ⟨hne, h1 | h2⟩
      · have hmem : t.1 ∈ ({x, y2, z1} : Finset V) := hNy1 ▸ (G.mem_neighborFinset y1 t.1).mpr h1
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with h | h | h
        · exact Or.inl (Subtype.ext h)
        · exact False.elim (t.2 h)
        · exact Or.inr (Or.inl (Subtype.ext h))
      · have hmem : t.1 ∈ ({x, y1, z2} : Finset V) := hNy2 ▸ (G.mem_neighborFinset y2 t.1).mpr h2
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with h | h | h
        · exact Or.inl (Subtype.ext h)
        · exact False.elim (hne (Subtype.ext h.symm))
        · exact Or.inr (Or.inr (Subtype.ext h))
    · rintro (rfl | rfl | rfl)
      · exact ⟨fun h => hx_ne_y1 (congrArg Subtype.val h).symm, Or.inl hxy1.symm⟩
      · exact ⟨fun h => (G.ne_of_adj hy1z1) (congrArg Subtype.val h), Or.inl hy1z1⟩
      · exact ⟨fun h => hz2y1 (congrArg Subtype.val h).symm, Or.inr hy2z2⟩
  have hdu0 : H.degree u0 = 3 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hNu0,
      Finset.card_insert_of_notMem (by simp [x', z1', z2', hz1x.symm, hz2x.symm, Subtype.ext_iff]),
      Finset.card_pair (fun h => hz1_ne_z2 (congrArg Subtype.val h))]
  have hdeg_other : ∀ v : Sy2, v ≠ u0 → v ≠ x' → H.degree v = G.degree v.1 := by
    intro v hvu hvx
    have hv1 : v.1 ≠ y1 := fun h => hvu (Subtype.ext h)
    have hvx1 : v.1 ≠ x := fun h => hvx (Subtype.ext h)
    have hnot_both : ¬(G.Adj v.1 y1 ∧ G.Adj v.1 y2) := by
      rintro ⟨h1, h2⟩
      have hm1 : v.1 ∈ ({x, y2, z1} : Finset V) := hNy1 ▸ (G.mem_neighborFinset y1 v.1).mpr h1.symm
      have hm2 : v.1 ∈ ({x, y1, z2} : Finset V) := hNy2 ▸ (G.mem_neighborFinset y2 v.1).mpr h2.symm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm1 hm2
      rcases hm1 with h | h | h
      · exact hvx1 h
      · exact v.2 h
      · rcases hm2 with h' | h' | h'
        · exact hvx1 h'
        · exact hv1 h'
        · exact hz1_ne_z2 (h.symm.trans h')
    let e : H.neighborSet v ≃ G.neighborSet v.1 :=
      { toFun := fun t =>
          if ht : t.1.1 = y1 then
            if h1 : G.Adj v.1 y1 then ⟨y1, h1⟩
            else ⟨y2, by
              have hadj := t.2.2
              simp only [hv1, ht, ite_false, ite_true] at hadj
              exact hadj.resolve_left h1⟩
          else ⟨t.1.1, by
            have hadj := t.2.2
            simp only [hv1, ht, ite_false] at hadj
            exact hadj⟩
        invFun := fun t =>
          if ht : t.1 = y2 then ⟨u0, ⟨hvu, by simp [hv1, u0, ht ▸ t.2]⟩⟩
          else if ht1 : t.1 = y1 then ⟨u0, ⟨hvu, by simp [hv1, u0, ht1 ▸ t.2]⟩⟩
          else ⟨⟨t.1, ht⟩, ⟨fun h => ht1 (congrArg Subtype.val h).symm, by
            simp only [hv1, ht1, ite_false]; exact t.2⟩⟩
        left_inv := by
          intro t
          apply Subtype.ext
          by_cases ht : t.1.1 = y1
          · by_cases h1 : G.Adj v.1 y1
            · simp [ht, h1, hy1_ne_y2, u0, Subtype.ext_iff]
            · simp [ht, h1, u0, Subtype.ext_iff]
          · have ht2 : t.1.1 ≠ y2 := t.1.2
            simp [ht, ht2]
        right_inv := by
          intro t
          apply Subtype.ext
          by_cases ht : t.1 = y2
          · have h1 : ¬G.Adj v.1 y1 := fun h => hnot_both ⟨h, ht ▸ t.2⟩
            simp [ht, h1, u0]
          · by_cases ht1 : t.1 = y1
            · have h1 : G.Adj v.1 y1 := ht1 ▸ t.2
              simp [ht, ht1, h1, u0]
            · simp [ht, ht1] }
    have hc := Fintype.card_congr e
    rwa [SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.card_neighborSet_eq_degree] at hc
  have hdeg_x' : 3 ≤ H.degree x' := by
    have hsub : insert u0 ((G.neighborFinset x |>.erase y1 |>.erase y2).attach.image
        fun t => (⟨t.1, (Finset.mem_erase.mp t.2).1⟩ : Sy2)) ⊆ H.neighborFinset x' := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at ht
      rcases ht with rfl | ⟨a, ha, rfl⟩
      · exact (H.mem_neighborFinset x' u0).mpr ⟨fun h => hx_ne_y1 (congrArg Subtype.val h), by simp [x', u0, hx_ne_y1, hxy1]⟩
      · have ha2 : a ≠ y2 := (Finset.mem_erase.mp ha).1
        have ha1 : a ≠ y1 := (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1
        have hxa : G.Adj x a := (G.mem_neighborFinset x a).mp (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).2
        exact (H.mem_neighborFinset x' ⟨a, ha2⟩).mpr ⟨fun h => (G.ne_of_adj hxa) (congrArg Subtype.val h),
          by simp [x', hx_ne_y1, ha1, hxa]⟩
    have hnot_u0 : u0 ∉ ((G.neighborFinset x |>.erase y1 |>.erase y2).attach.image
        fun t => (⟨t.1, (Finset.mem_erase.mp t.2).1⟩ : Sy2)) := by
      simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists, not_exists]
      intro a ha heq
      have ha1 : a ≠ y1 := (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1
      exact ha1 (congrArg Subtype.val heq)
    have hc := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hnot_u0, Finset.card_image_of_injective _ (fun _ _ h => Subtype.ext (congrArg Subtype.val h)),
      Finset.card_attach, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hy1_ne_y2.symm, (G.mem_neighborFinset x y2).mpr hxy2⟩),
      Finset.card_erase_of_mem ((G.mem_neighborFinset x y1).mpr hxy1),
      SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.card_neighborFinset_eq_degree] at hc
    omega
  have hWlt : Fintype.card Sy2 < Fintype.card V := by
    rw [Fintype.card_subtype, show (Finset.univ.filter fun u : V => u ∈ Sy2) = Finset.univ.erase y2 by ext u; simp [Sy2]]
    have := Finset.card_erase_add_one (Finset.mem_univ y2); omega
  have hWge2 : 2 ≤ Fintype.card Sy2 := by
    have hVge4 : 4 ≤ Fintype.card V := by have := G.degree_lt_card_verts x; omega
    rw [Fintype.card_subtype, show (Finset.univ.filter fun u : V => u ∈ Sy2) = Finset.univ.erase y2 by ext u; simp [Sy2]]
    have := Finset.card_erase_add_one (Finset.mem_univ y2); omega
  have hnear : Near H := by
    obtain ⟨_, w, hw⟩ := hm.1
    by_cases hwy2 : w = y2
    · apply near_of_except H u0 hWge2
      intro v hv
      by_cases hvx : v = x'
      · rw [hvx]; exact hdeg_x'
      · rw [hdeg_other v hv hvx]; exact hw v.1 (hwy2 ▸ v.2)
    · apply near_of_except H ⟨w, hwy2⟩ hWge2
      intro v hv
      by_cases hvu : v = u0
      · rw [hvu, hdu0]
      by_cases hvx : v = x'
      · rw [hvx]; exact hdeg_x'
      · rw [hdeg_other v hvu hvx]; exact hw v.1 (fun h => hv (Subtype.ext h))
  obtain ⟨k, v0, cyc, hk, hcyc, hlen⟩ := hm.2.2.1 Sy2 H hWlt hnear
  have hpow4 : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by decide
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
  have hu0_mem : u0 ∈ cyc.support := by
    by_contra hnot
    have htrans : ∀ e ∈ cyc.edges, e ∈ (G.induce Sy2).edgeSet := by
      intro e he
      induction e using Sym2.ind with
      | _ a b =>
        have ha : a ≠ u0 := fun h => hnot (h ▸ Walk.fst_mem_support_of_mem_edges cyc he)
        have hb : b ≠ u0 := fun h => hnot (h ▸ Walk.snd_mem_support_of_mem_edges cyc he)
        have hadj := (cyc.edges_subset_edgeSet he).2
        have ha1 : a.1 ≠ y1 := fun h => ha (Subtype.ext h)
        have hb1 : b.1 ≠ y1 := fun h => hb (Subtype.ext h)
        simp only [ha1, hb1, ite_false] at hadj
        exact hadj
    exact hm.2.1 (power_induce G _ ⟨k, v0, cyc.transfer (G.induce Sy2) htrans, hk,
      hcyc.transfer htrans, by simpa using hlen⟩)
  let c1 := cyc.rotate hu0_mem
  have hc1 : c1.IsCycle := hcyc.rotate hu0_mem
  have hlen1 : c1.length = 2 ^ k := (Walk.length_rotate cyc hu0_mem).trans hlen
  cases hc1_eq : c1 with
  | nil => exact False.elim (hc1.ne_nil hc1_eq)
  | @cons _ a1 _ ha1 p1 =>
    have hp1_path : p1.IsPath := by
      refine Walk.IsPath.mk' ?_
      have hnd := hc1.support_nodup
      rw [hc1_eq, Walk.support_cons, List.tail_cons] at hnd
      exact hnd
    cases hpr : p1.reverse with
    | nil =>
      have : p1 = Walk.nil := by have := congrArg Walk.reverse hpr; simpa using this
      rw [this] at hc1_eq; exact False.elim (H.ne_of_adj ha1 rfl)
    | @cons _ a2 _ ha2 q_rev =>
      let q := q_rev.reverse
      have hp1_eq : p1 = q.concat ha2.symm := by
        have := congrArg Walk.reverse hpr; simpa [q, Walk.reverse_cons] using this
      have hu0_not_q : u0 ∉ q.support := by
        have hnd := hp1_path.reverse.support_nodup
        rw [hpr, Walk.support_cons, List.nodup_cons] at hnd
        simpa [q, Walk.support_reverse] using hnd.1
      have hq_nodup : q.support.Nodup := by
        have hnd := hp1_path.reverse.support_nodup
        rw [hpr, Walk.support_cons, List.nodup_cons] at hnd
        simpa [q, Walk.support_reverse] using hnd.2
      have hq_len : q.length + 2 = 2 ^ k := by
        have hl : c1.length = q.length + 2 := by rw [hc1_eq, hp1_eq, Walk.length_cons, Walk.length_concat]
        omega
      have hq_G : ∀ e ∈ q.edges, e ∈ (G.induce Sy2).edgeSet := by
        intro e he
        induction e using Sym2.ind with
        | _ a b =>
          have ha : a ≠ u0 := fun h => hu0_not_q (h ▸ Walk.fst_mem_support_of_mem_edges q he)
          have hb : b ≠ u0 := fun h => hu0_not_q (h ▸ Walk.snd_mem_support_of_mem_edges q he)
          have hadj := (q.edges_subset_edgeSet he).2
          have ha1' : a.1 ≠ y1 := fun h => ha (Subtype.ext h)
          have hb1' : b.1 ≠ y1 := fun h => hb (Subtype.ext h)
          simp only [ha1', hb1', ite_false] at hadj
          exact hadj
      let qG : G.Walk a1.1 a2.1 := (q.transfer (G.induce Sy2) hq_G).map ⟨Subtype.val, fun h => h⟩
      have hqG_nodup : qG.support.Nodup := by
        simpa [qG, Walk.support_map] using hq_nodup.map Subtype.val_injective
      have hy1_not_qG : y1 ∉ qG.support := by
        intro hm1; rw [Walk.support_map, List.mem_map] at hm1
        obtain ⟨t, ht, ht1⟩ := hm1; exact hu0_not_q ((show t = u0 from Subtype.ext ht1) ▸ ht)
      have hy2_not_qG : y2 ∉ qG.support := by
        intro hm2; rw [Walk.support_map, List.mem_map] at hm2
        obtain ⟨t, _, ht2⟩ := hm2; exact t.2 ht2
      have hqG_len : qG.length + 2 = 2 ^ k := by simpa [qG] using hq_len
      have hno_close : ∀ y : V, y ∉ qG.support → G.Adj y a1.1 → G.Adj a2.1 y → False := by
        intro y hynot hy_a1 ha2_y
        let badC : G.Walk y y := Walk.cons hy_a1 (qG.concat ha2_y)
        have hbad_len : badC.length = 2 ^ k := by simp only [badC, Walk.length_cons, Walk.length_concat]; omega
        have hbad_tail : badC.support.tail = qG.support ++ [y] := by
          simp only [badC, Walk.support_cons, List.tail_cons, Walk.support_concat]
        have hbad_nodup : badC.support.tail.Nodup := by
          rw [hbad_tail]
          exact List.nodup_append.mpr ⟨hqG_nodup, List.nodup_singleton y,
            fun t ht1 ht2 => hynot ((List.mem_singleton.mp ht2) ▸ ht1)⟩
        exact hm.2.1 ⟨k, y, badC, hk, isCycle_of_support_tail_nodup badC hbad_nodup (by omega), hbad_len⟩
      have ha1_mem : a1 = x' ∨ a1 = z1' ∨ a1 = z2' := by
        have := hNu0 ▸ (H.mem_neighborFinset u0 a1).mpr ha1; simpa using this
      have ha2_mem : a2 = x' ∨ a2 = z1' ∨ a2 = z2' := by
        have := hNu0 ▸ (H.mem_neighborFinset u0 a2).mpr ha2; simpa using this
      have ha1_ne_a2 : a1 ≠ a2 := by
        intro heq; subst heq
        cases hqeq : q with
        | nil => simp [hqeq] at hq_len; omega
        | cons hstep qrest =>
          rw [hqeq, Walk.support_cons, List.nodup_cons] at hq_nodup
          exact hq_nodup.1 Walk.end_mem_support
      rcases ha1_mem with rfl | rfl | rfl <;> rcases ha2_mem with rfl | rfl | rfl
      · exact False.elim (ha1_ne_a2 rfl)
      · exact False.elim (hno_close y1 hy1_not_qG hxy1.symm hy1z1.symm)
      · exact False.elim (hno_close y2 hy2_not_qG hxy2.symm hy2z2.symm)
      · exact False.elim (hno_close y1 hy1_not_qG hy1z1 hxy1)
      · exact False.elim (ha1_ne_a2 rfl)
      · let S := {u : V | u ≠ y1 ∧ u ≠ y2}
        have hlift_S : ∀ {a b : V} (p : G.Walk a b), y1 ∉ p.support → y2 ∉ p.support →
            ∃ (ha : a ∈ S) (hb : b ∈ S) (p' : (G.induce S).Walk ⟨a, ha⟩ ⟨b, hb⟩),
              p'.length = p.length ∧ p'.support.map Subtype.val = p.support := by
          intro a b p
          induction p with
          | nil =>
            intro h1 h2
            have ha : a ∈ S := ⟨fun h => h1 (by simp [h]), fun h => h2 (by simp [h])⟩
            exact ⟨ha, ha, Walk.nil, rfl, rfl⟩
          | @cons u v w huv p ih =>
            intro h1 h2
            simp only [Walk.support_cons, List.mem_cons, not_or] at h1 h2
            obtain ⟨hv, hw, p', hlen', hsupp'⟩ := ih h1.2 h2.2
            have hu : u ∈ S := ⟨Ne.symm h1.1, Ne.symm h2.1⟩
            exact ⟨hu, hw, Walk.cons huv p', by simp [hlen'], by simp [hsupp']⟩
        obtain ⟨hz1S, hz2S, p', hp'len, hp'supp⟩ := hlift_S qG hy1_not_qG hy2_not_qG
        have hp'_path : p'.IsPath := Walk.IsPath.mk' (List.Nodup.of_map Subtype.val (hp'supp.symm ▸ hqG_nodup))
        exact ⟨k, p', hk, hp'_path, by omega⟩
      · exact False.elim (hno_close y2 hy2_not_qG hy2z2 hxy2)
      · let S := {u : V | u ≠ y1 ∧ u ≠ y2}
        have hlift_S : ∀ {a b : V} (p : G.Walk a b), y1 ∉ p.support → y2 ∉ p.support →
            ∃ (ha : a ∈ S) (hb : b ∈ S) (p' : (G.induce S).Walk ⟨a, ha⟩ ⟨b, hb⟩),
              p'.length = p.length ∧ p'.support.map Subtype.val = p.support := by
          intro a b p
          induction p with
          | nil =>
            intro h1 h2
            have ha : a ∈ S := ⟨fun h => h1 (by simp [h]), fun h => h2 (by simp [h])⟩
            exact ⟨ha, ha, Walk.nil, rfl, rfl⟩
          | @cons u v w huv p ih =>
            intro h1 h2
            simp only [Walk.support_cons, List.mem_cons, not_or] at h1 h2
            obtain ⟨hv, hw, p', hlen', hsupp'⟩ := ih h1.2 h2.2
            have hu : u ∈ S := ⟨Ne.symm h1.1, Ne.symm h2.1⟩
            exact ⟨hu, hw, Walk.cons huv p', by simp [hlen'], by simp [hsupp']⟩
        obtain ⟨hz2S, hz1S, p', hp'len, hp'supp⟩ := hlift_S qG hy1_not_qG hy2_not_qG
        have hp'_path : p'.IsPath := Walk.IsPath.mk' (List.Nodup.of_map Subtype.val (hp'supp.symm ▸ hqG_nodup))
        exact ⟨k, p'.reverse, hk, hp'_path.reverse, by simp [Walk.length_reverse, hp'len]; omega⟩
      · exact False.elim (ha1_ne_a2 rfl)

#print axioms trifree_two_edge_y_reduction
#print axioms class_h_high_neighbor_suppression
#print axioms class_h_high_triangle_contraction

end E64Wave3Local
