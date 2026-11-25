import Leaves

/-!
Wave 2 Agent #5 — Connectivity, Biconnectivity (No Cut-Vertex), and No-Bridge Theorems
for MinimalBad(G) graphs. All proofs are unconditional and all-order.
-/

namespace E64Wave2Conn
open SimpleGraph Erdos64Closure E64Core E64Leaves
universe u

/-- No MinimalBad(G) graph has a cut-vertex: for any vertex v and any decomposition
V = A ∪ B with A ∩ B = {v}, |A| >= 2, |B| >= 2, there is an edge between A \ {v} and B \ {v}. -/
theorem minimal_bad_no_cut_vertex {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hm : MinimalBad G) (v : V) (A B : Finset V)
    (hcover : A ∪ B = Finset.univ)
    (hinter : A ∩ B = {v})
    (hA2 : 2 ≤ A.card) (hB2 : 2 ≤ B.card) :
    ∃ a ∈ A.erase v, ∃ b ∈ B.erase v, G.Adj a b := by
  classical
  by_contra hno
  push_neg at hno
  obtain ⟨_, w, hw⟩ := hm.1
  have kill_side : ∀ (S T : Finset V),
      S ∪ T = Finset.univ → S ∩ T = {v} → 2 ≤ S.card → 2 ≤ T.card →
      (∀ a ∈ S.erase v, ∀ b ∈ T.erase v, ¬ G.Adj a b) →
      w ∉ S.erase v → False := by
    intro S T hcov hint hS2 hT2 hnoedge hw_not
    have hvS : v ∈ S := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).1
    have hvT : v ∈ T := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).2
    let W := {x : V // x ∈ (S : Set V)}
    let H : SimpleGraph W := G.induce (S : Set V)
    let _ : DecidableRel H.Adj := inferInstanceAs (DecidableRel (G.induce (S : Set V)).Adj)
    have hWcard : Fintype.card W = S.card := Fintype.card_coe S
    have hTne : (T.erase v).Nonempty := by
      have hc := Finset.card_erase_add_one hvT
      exact Finset.card_pos.mp (by omega)
    obtain ⟨t0, ht0⟩ := hTne
    have ht0_notS : t0 ∉ S := by
      intro hS
      have hm_int : t0 ∈ S ∩ T := Finset.mem_inter.mpr ⟨hS, (Finset.mem_erase.mp ht0).2⟩
      rw [hint, Finset.mem_singleton] at hm_int
      exact (Finset.mem_erase.mp ht0).1 hm_int
    have hlt : Fintype.card W < Fintype.card V := by
      rw [hWcard]
      exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
        ⟨Finset.subset_univ S, fun heq => ht0_notS (heq ▸ Finset.mem_univ t0)⟩)
    have hnear : Near H := by
      apply near_of_except H ⟨v, hvS⟩ (by omega)
      intro x hxv
      have hx_ne : x.1 ≠ v := fun h => hxv (Subtype.ext h)
      have hx_erase : x.1 ∈ S.erase v := Finset.mem_erase.mpr ⟨hx_ne, x.2⟩
      have hx_new : x.1 ≠ w := fun h => hw_not (h ▸ hx_erase)
      have hnb_sub : ∀ y, G.Adj x.1 y → y ∈ S := by
        intro y hxy
        by_contra hyS
        have hy_univ : y ∈ S ∪ T := hcov ▸ Finset.mem_univ y
        have hyT : y ∈ T := (Finset.mem_union.mp hy_univ).resolve_left hyS
        have hyv : y ≠ v := fun h => hyS (h ▸ hvS)
        exact hnoedge x.1 hx_erase y (Finset.mem_erase.mpr ⟨hyv, hyT⟩) hxy
      let e : H.neighborSet x ≃ G.neighborSet x.1 :=
        { toFun := fun y => ⟨y.1.1, y.2⟩
          invFun := fun y => ⟨⟨y.1, hnb_sub y.1 y.2⟩, y.2⟩
          left_inv := by intro y; rfl
          right_inv := by intro y; rfl }
      have hdeg_eq : H.degree x = G.degree x.1 := by
        rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
        exact Fintype.card_congr e
      rw [hdeg_eq]
      exact hw x.1 hx_new
    exact hm.2.1 (power_induce G (S : Set V) (hm.2.2.1 W H hlt hnear))
  by_cases hwA : w ∈ A.erase v
  · have hwB : w ∉ B.erase v := by
      intro hwB
      have hmem : w ∈ A ∩ B := Finset.mem_inter.mpr
        ⟨(Finset.mem_erase.mp hwA).2, (Finset.mem_erase.mp hwB).2⟩
      rw [hinter, Finset.mem_singleton] at hmem
      exact (Finset.mem_erase.mp hwA).1 hmem
    exact kill_side B A (by rw [Finset.union_comm]; exact hcover)
      (by rw [Finset.inter_comm]; exact hinter) hB2 hA2
      (fun b hb a ha hba => hno a ha b hb hba.symm) hwB
  · exact kill_side A B hcover hinter hA2 hB2 hno hwA

/-- Every MinimalBad(G) graph has no bridge and is connected: every nontrivial
bipartition (S, S^c) with |S| >= 1 and |S^c| >= 1 has at least 2 crossing edges. -/
theorem minimal_bad_two_edge_connected {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hm : MinimalBad G) (S : Finset V)
    (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) :
    2 ≤ (Finset.univ.filter (fun e : V × V => e.1 ∈ S ∧ e.2 ∉ S ∧ G.Adj e.1 e.2)).card := by
  classical
  by_contra hlt
  let E := Finset.univ.filter (fun e : V × V => e.1 ∈ S ∧ e.2 ∉ S ∧ G.Adj e.1 e.2)
  have hE1 : E.card ≤ 1 := by omega
  obtain ⟨_, w, hw⟩ := hm.1
  have kill_side : ∀ (T : Finset V), T.Nonempty → Tᶜ.Nonempty → w ∉ T →
      (Finset.univ.filter (fun e : V × V => e.1 ∈ T ∧ e.2 ∉ T ∧ G.Adj e.1 e.2)).card ≤ 1 →
      False := by
    intro T hT hTc hwT hcut1
    let ET := Finset.univ.filter (fun e : V × V => e.1 ∈ T ∧ e.2 ∉ T ∧ G.Adj e.1 e.2)
    by_cases hT1 : T.card = 1
    · obtain ⟨x, hxT⟩ := Finset.card_eq_one.mp hT1
      have hdeg_le : G.degree x ≤ 1 := by
        let f : G.neighborSet x → {e : V × V // e ∈ ET} := fun y =>
          ⟨(x, y.1), Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hxT], by
            intro hyT
            rw [hxT, Finset.mem_singleton] at hyT
            exact (G.ne_of_adj y.2) hyT.symm, y.2⟩⟩
        have hf : Function.Injective f := by
          intro a b hab
          apply Subtype.ext
          exact congrArg (fun p => p.1.2) hab
        have hc := Fintype.card_le_of_injective f hf
        rw [SimpleGraph.card_neighborSet_eq_degree, Fintype.card_coe] at hc
        exact hc.trans hcut1
      have h2 := no_small_defect G hm x
      omega
    · have hT2 : 2 ≤ T.card := by
        have hp := Finset.card_pos.mpr hT
        omega
      let W := {x : V // x ∈ (T : Set V)}
      let H : SimpleGraph W := G.induce (T : Set V)
      let _ : DecidableRel H.Adj := inferInstanceAs (DecidableRel (G.induce (T : Set V)).Adj)
      have hWcard : Fintype.card W = T.card := Fintype.card_coe T
      obtain ⟨t0, ht0⟩ := hTc
      have ht0_notT : t0 ∉ T := Finset.mem_compl.mp ht0
      have hltV : Fintype.card W < Fintype.card V := by
        rw [hWcard]
        exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
          ⟨Finset.subset_univ T, fun heq => ht0_notT (heq ▸ Finset.mem_univ t0)⟩)
      have hnear : Near H := by
        by_cases hET : ET = ∅
        · obtain ⟨u0, hu0⟩ := hT
          apply near_of_except H ⟨u0, hu0⟩ (by omega)
          intro x _
          have hsub : ∀ y, G.Adj x.1 y → y ∈ T := by
            intro y hxy
            by_contra hyT
            have hmem : (x.1, y) ∈ ET := Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2, hyT, hxy⟩
            simp [hET] at hmem
          let e : H.neighborSet x ≃ G.neighborSet x.1 :=
            { toFun := fun y => ⟨y.1.1, y.2⟩
              invFun := fun y => ⟨⟨y.1, hsub y.1 y.2⟩, y.2⟩
              left_inv := by intro y; rfl
              right_inv := by intro y; rfl }
          have hdeg_eq : H.degree x = G.degree x.1 := by
            rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
            exact Fintype.card_congr e
          rw [hdeg_eq]
          exact hw x.1 (fun h => hwT (h ▸ x.2))
        · obtain ⟨e0, he0⟩ := Finset.nonempty_iff_ne_empty.mpr hET
          have he0_mem := Finset.mem_filter.mp he0
          have hu0T : e0.1 ∈ T := he0_mem.2.1
          apply near_of_except H ⟨e0.1, hu0T⟩ (by omega)
          intro x hxu
          have hx_ne : x.1 ≠ e0.1 := fun h => hxu (Subtype.ext h)
          have hsub : ∀ y, G.Adj x.1 y → y ∈ T := by
            intro y hxy
            by_contra hyT
            have hmem : (x.1, y) ∈ ET := Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2, hyT, hxy⟩
            have hne_e : (x.1, y) ≠ e0 := fun h => hx_ne (congrArg Prod.fst h)
            have h2 : ({(x.1, y), e0} : Finset (V × V)).card = 2 := by simp [hne_e]
            have hle := Finset.card_le_card (Finset.insert_subset hmem (Finset.singleton_subset_iff.mpr he0))
            omega
          let e : H.neighborSet x ≃ G.neighborSet x.1 :=
            { toFun := fun y => ⟨y.1.1, y.2⟩
              invFun := fun y => ⟨⟨y.1, hsub y.1 y.2⟩, y.2⟩
              left_inv := by intro y; rfl
              right_inv := by intro y; rfl }
          have hdeg_eq : H.degree x = G.degree x.1 := by
            rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
            exact Fintype.card_congr e
          rw [hdeg_eq]
          exact hw x.1 (fun h => hwT (h ▸ x.2))
      exact hm.2.1 (power_induce G (T : Set V) (hm.2.2.1 W H hltV hnear))
  by_cases hwS : w ∈ S
  · have hwSc : w ∉ Sᶜ := fun h => (Finset.mem_compl.mp h) hwS
    have hcard_swap :
        (Finset.univ.filter (fun e : V × V => e.1 ∈ Sᶜ ∧ e.2 ∉ Sᶜ ∧ G.Adj e.1 e.2)).card = E.card := by
      let f : {e : V × V // e ∈ Finset.univ.filter (fun e : V × V => e.1 ∈ Sᶜ ∧ e.2 ∉ Sᶜ ∧ G.Adj e.1 e.2)} ≃
              {e : V × V // e ∈ E} :=
        { toFun := fun p => ⟨(p.1.2, p.1.1), by
            have hp := (Finset.mem_filter.mp p.2).2
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hp.2.1,
              Finset.mem_compl.mp hp.1, hp.2.2.symm⟩⟩
          invFun := fun p => ⟨(p.1.2, p.1.1), by
            have hp := (Finset.mem_filter.mp p.2).2
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_compl.mpr hp.2.1,
              by simpa using hp.1, hp.2.2.symm⟩⟩
          left_inv := by intro p; apply Subtype.ext; exact Prod.swap_swap p.1
          right_inv := by intro p; apply Subtype.ext; exact Prod.swap_swap p.1 }
      rw [← Fintype.card_coe, ← Fintype.card_coe]
      exact Fintype.card_congr f
    exact kill_side Sᶜ hSc (by simpa using hS) hwSc (by omega)
  · exact kill_side S hS hSc hwS hE1

#print axioms minimal_bad_no_cut_vertex
#print axioms minimal_bad_two_edge_connected
end E64Wave2Conn
