import Leaves

namespace E64DefectCore
open SimpleGraph Erdos64Closure E64Core E64Leaves
universe u

/-- Edge minimality in the one-defect class forces every neighbor of the
    degree-two vertex to be cubic. Deleting a defect--high edge keeps Near. -/
theorem defect_neighbor_cubic {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {w b : V} (hw : G.degree w = 2) (hwb : G.Adj w b) :
    G.degree b = 3 := by
  classical
  obtain ⟨_,r,hr⟩ := hm.1
  have hrw : r=w := by
    by_contra hne
    have := hr w (Ne.symm hne)
    omega
  subst r
  have hbw : b≠w := (G.ne_of_adj hwb).symm
  have hb := hr b hbw
  by_contra hne
  have hhigh : 4≤G.degree b := by omega
  let H := G \ SimpleGraph.edge w b
  let _ : DecidableRel H.Adj :=
    inferInstanceAs (DecidableRel (G \ SimpleGraph.edge w b).Adj)
  have hcard : 2 ≤ Fintype.card V := by
    have := G.degree_lt_card_verts b
    omega
  have hn : Near H := by
    apply near_of_except H w hcard
    intro v hv
    have hdeg := erase_edge_degree G w b hwb v
    change H.degree v + (if v=w ∨ v=b then 1 else 0) = G.degree v at hdeg
    by_cases hvb : v=b
    · subst v
      simp at hdeg
      omega
    · simp [hv,hvb] at hdeg
      rw [hdeg]
      exact hr v hv
  have hEq : H=G := hm.2.2.2 H sdiff_le hn
  have he : H.Adj w b := hEq ▸ hwb
  have hno : ¬H.Adj w b := by
    intro h
    have hn := (SimpleGraph.sdiff_adj G (SimpleGraph.edge w b) w b).mp h
    exact hn.2 ((SimpleGraph.edge_adj w b w b).mpr
      ⟨Or.inl ⟨rfl,rfl⟩,G.ne_of_adj hwb⟩)
  exact hno he

/-- The cut at two adjacent vertices of degrees two and three is nontrivial
    and has at most three edges, with exactly the DAG's counting convention. -/
theorem adjacent_two_three_cut {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {w b : V} (hwb : G.Adj w b) (hw : G.degree w=2)
    (hb : G.degree b=3) : SmallCut G 3 := by
  classical
  have hne := G.ne_of_adj hwb
  let S : Set V := {w,b}
  have hS : Nat.card S = 2 := by
    have hfin : S.Finite := Set.toFinite S
    rw [Nat.card_eq_card_finite_toFinset hfin]
    have he : hfin.toFinset = ({w,b} : Finset V) := by
      ext v
      simp [S]
    rw [he]
    simp [hne]
  have hScomp : Nat.card (Sᶜ : Set V) = Fintype.card V - 2 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_compl_set]
    have hsc : Fintype.card S=2 := by
      simpa only [Nat.card_eq_fintype_card] using hS
    rw [hsc]
  have hV : 4≤Fintype.card V := by
    have := G.degree_lt_card_verts b
    omega
  let A := ↥((G.neighborFinset w).erase b)
  let D := ↥((G.neighborFinset b).erase w)
  have hA : Fintype.card A = 1 := by
    change Fintype.card ↥((G.neighborFinset w).erase b)=1
    rw [Fintype.card_coe]
    have hc := Finset.card_erase_add_one ((G.mem_neighborFinset w b).mpr hwb)
    rw [G.card_neighborFinset_eq_degree,hw] at hc
    omega
  have hD : Fintype.card D = 2 := by
    change Fintype.card ↥((G.neighborFinset b).erase w)=2
    rw [Fintype.card_coe]
    have hc := Finset.card_erase_add_one ((G.mem_neighborFinset b w).mpr hwb.symm)
    rw [G.card_neighborFinset_eq_degree,hb] at hc
    omega
  let B := {e : V×V // e.1∈S ∧ e.2∉S ∧ G.Adj e.1 e.2}
  let f : B → A ⊕ D := fun e =>
    if he : e.1.1=w then
      Sum.inl ⟨e.1.2,by
        apply Finset.mem_erase.mpr
        have hnot : e.1.2≠w ∧ e.1.2≠b := by simpa [S] using e.2.2.1
        exact ⟨hnot.2,(G.mem_neighborFinset w e.1.2).mpr (he ▸ e.2.2.2)⟩⟩
    else
      Sum.inr ⟨e.1.2,by
        have hfirst : e.1.1=b := by
          have hs : e.1.1=w ∨ e.1.1=b := by simpa [S] using e.2.1
          exact hs.resolve_left he
        apply Finset.mem_erase.mpr
        have hnot : e.1.2≠w ∧ e.1.2≠b := by simpa [S] using e.2.2.1
        exact ⟨hnot.1,(G.mem_neighborFinset b e.1.2).mpr (hfirst ▸ e.2.2.2)⟩⟩
  let r : A ⊕ D → V×V := Sum.elim (fun x => (w,x.1)) (fun x => (b,x.1))
  have hrec (e : B) : r (f e)=e.1 := by
    by_cases he : e.1.1=w
    · apply Prod.ext <;> simp [f,r,he]
    · have hfirst : e.1.1=b := by
        have hs : e.1.1=w ∨ e.1.1=b := by simpa [S] using e.2.1
        exact hs.resolve_left he
      apply Prod.ext <;> simp [f,r,he,hfirst]
  have hinj : Function.Injective f := by
    intro p q he
    apply Subtype.ext
    rw [← hrec p,← hrec q,he]
  have hcut := Nat.card_le_card_of_injective f hinj
  have ht : Nat.card (A ⊕ D)=3 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_sum,hA,hD]
  refine ⟨S,by omega,by omega,?_⟩
  change Nat.card B≤3
  omega

/-- Full all-order exclusion mechanism for every one-defect core leaf. -/
theorem defect_forces_small_cut {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {w : V} (hw : G.degree w=2) : SmallCut G 3 := by
  obtain ⟨b,hwb⟩ := (G.degree_pos_iff_exists_adj w).mp (by omega)
  exact adjacent_two_three_cut G hwb hw (defect_neighbor_cubic G hm hw hwb)

theorem exclude_st_core : Exclude.{u} (Leaf.st .core) := by
  intro V G _ _ hm hleaf
  obtain ⟨⟨w,hw,_⟩,_,_,_,hcut⟩ := hleaf
  exact hcut (defect_forces_small_cut G hm hw)

theorem exclude_sn_core : Exclude.{u} (Leaf.sn .core) := by
  intro V G _ _ hm hleaf
  obtain ⟨⟨w,hw,_⟩,_,_,_,hcut⟩ := hleaf
  exact hcut (defect_forces_small_cut G hm hw)

theorem exclude_hb_core4 : Exclude.{u} (Leaf.hb .core4) := by
  intro V G _ _ hm hleaf
  obtain ⟨⟨w,hw,_,_⟩,_,_,hcut,_⟩ := hleaf
  exact hcut (defect_forces_small_cut G hm hw)

theorem exclude_hb_core5 : Exclude.{u} (Leaf.hb .core5) := by
  intro V G _ _ hm hleaf
  obtain ⟨⟨w,hw,_,_⟩,_,_,hcut,_⟩ := hleaf
  exact hcut (defect_forces_small_cut G hm hw)

theorem exclude_ht_core4 : Exclude.{u} (Leaf.ht .core4) := by
  intro V G _ _ hm hleaf
  obtain ⟨⟨w,hw,_,_⟩,_,_,_,hcut,_⟩ := hleaf
  exact hcut (defect_forces_small_cut G hm hw)

theorem exclude_ht_core5 : Exclude.{u} (Leaf.ht .core5) := by
  intro V G _ _ hm hleaf
  obtain ⟨⟨w,hw,_,_⟩,_,_,_,hcut,_⟩ := hleaf
  exact hcut (defect_forces_small_cut G hm hw)

theorem exclude_hn_core4 : Exclude.{u} (Leaf.hn .core4) := by
  intro V G _ _ hm hleaf
  obtain ⟨⟨w,hw,_,_⟩,_,_,_,hcut,_⟩ := hleaf
  exact hcut (defect_forces_small_cut G hm hw)

theorem exclude_hn_core5 : Exclude.{u} (Leaf.hn .core5) := by
  intro V G _ _ hm hleaf
  obtain ⟨⟨w,hw,_,_⟩,_,_,_,hcut,_⟩ := hleaf
  exact hcut (defect_forces_small_cut G hm hw)

#print axioms defect_neighbor_cubic
#print axioms adjacent_two_three_cut
#print axioms defect_forces_small_cut
#print axioms exclude_st_core
#print axioms exclude_sn_core
#print axioms exclude_hb_core4
#print axioms exclude_hb_core5
#print axioms exclude_ht_core4
#print axioms exclude_ht_core5
#print axioms exclude_hn_core4
#print axioms exclude_hn_core5
end E64DefectCore
