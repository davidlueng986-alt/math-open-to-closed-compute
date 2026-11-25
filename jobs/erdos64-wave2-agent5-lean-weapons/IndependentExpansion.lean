import Leaves
import Incidence

/-!
Wave 2 Agent #5 — Independent-Set F2 Expansion & Dual-Kernel Weight-Drop Theorems.
All theorems are unconditional, all-order results for MinimalBad(G) graphs,
built directly on the verified Erdos64Incidence / Erdos64Paired kernel.
-/

namespace E64Wave2Indep
open SimpleGraph Erdos64Closure E64Core E64Leaves Erdos64Paired Erdos64Incidence
open scoped BigOperators
universe u

/-- Neighborhood finset of a vertex subset I in G. -/
def nbh {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (I : Finset V) : Finset V :=
  Finset.univ.filter (fun y => ∃ x ∈ I, G.Adj x y)

/-- Strict F2-shadow Hall expansion: in any MinimalBad(G), every nonempty
independent set I of cubic vertices whose neighbors all have degree <= 3
satisfies |N(I)| >= |I| + 2. Applies to all cubic (C-*) and subcubic (S-*) leaves. -/
theorem indep_neighborhood_expansion {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hm : MinimalBad G) (I : Finset V)
    (hne : I.Nonempty)
    (hind : ∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y)
    (hdegI : ∀ x ∈ I, G.degree x = 3)
    (hdegN : ∀ y ∈ nbh G I, G.degree y ≤ 3) :
    I.card + 2 ≤ (nbh G I).card := by
  classical
  by_contra hlt
  have hcodim_nat : (nbh G I).card ≤ I.card + 1 := by omega
  let X := {x : V // x ∈ I}
  let Y := {y : V // y ∈ nbh G I}
  let R : X → Y → Prop := fun x y => G.Adj x.1 y.1
  let _ : DecidableRel R := fun x y => Classical.propDecidable (R x y)
  have hsep : ∀ (x : X) (y : Y), x.1 ≠ y.1 := by
    intro x y heq
    have hy : ∃ a ∈ I, G.Adj a y.1 := (Finset.mem_filter.mp y.2).2
    obtain ⟨a, ha, hay⟩ := hy
    rw [← heq] at hay
    exact hind a ha x.1 x.2 hay
  obtain ⟨x0, hx0⟩ := hne
  have hX : Nonempty X := ⟨⟨x0, hx0⟩⟩
  have hpos0 : 0 < G.degree x0 := by rw [hdegI x0 hx0]; decide
  obtain ⟨y0, hxy0⟩ := (G.degree_pos_iff_exists_adj x0).mp hpos0
  have hy0 : y0 ∈ nbh G I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, x0, hx0, hxy0⟩
  have hY : Nonempty Y := ⟨⟨y0, hy0⟩⟩
  have hsize : Fintype.card X < Fintype.card V := by
    apply Fintype.card_lt_of_injective_not_surjective (fun x : X => x.1) Subtype.val_injective
    intro hsurj
    obtain ⟨x, hx⟩ := hsurj y0
    exact hsep x ⟨y0, hy0⟩ hx
  have hXcard : Fintype.card X = I.card := Fintype.card_coe I
  have hYcard : Fintype.card Y = (nbh G I).card := Fintype.card_coe (nbh G I)
  have hcodim : Fintype.card Y ≤ Fintype.card X + 1 := by omega
  have hbranch (x : X) : Fintype.card {y : Y // R x y} = 3 := by
    let e : {y : Y // R x y} ≃ G.neighborSet x.1 :=
      { toFun := fun y => ⟨y.1.1, y.2⟩
        invFun := fun z => ⟨⟨z.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.1, x.2, z.2⟩⟩, z.2⟩
        left_inv := by intro y; rfl
        right_inv := by intro z; rfl }
    rw [Fintype.card_congr e, SimpleGraph.card_neighborSet_eq_degree, hdegI x.1 x.2]
  have hmid (y : Y) : Fintype.card {x : X // R x y} ≤ 3 := by
    let f : {x : X // R x y} → G.neighborSet y.1 := fun x => ⟨x.1.1, x.2.symm⟩
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg Subtype.val hab
    have hc := Fintype.card_le_of_injective f hf
    rw [SimpleGraph.card_neighborSet_eq_degree] at hc
    exact hc.trans (hdegN y.1 y.2)
  have hs := safe_step_of_low_codim_incidence G
      (fun x : X => x.1) (fun y : Y => y.1)
      Subtype.val_injective Subtype.val_injective hsep R
      (fun _ _ h => h) hX hY hsize hcodim hbranch hmid hm.2.1
  exact no_safe_step G hm hs

/-- No nonzero kernel vector for the F2 incidence map of an independent set
of cubic vertices in a MinimalBad(G) graph. -/
theorem indep_syndrome_no_kernel {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hm : MinimalBad G) (I : Finset V)
    (hind : ∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y)
    (hdegI : ∀ x ∈ I, G.degree x = 3)
    (hdegN : ∀ y ∈ nbh G I, G.degree y ≤ 3)
    (z : {x : V // x ∈ I} → ZMod 2) (hz : z ≠ 0) :
    syndrome (fun (x : {x : V // x ∈ I}) (y : {y : V // y ∈ nbh G I}) => G.Adj x.1 y.1) z ≠ 0 := by
  classical
  intro hzero
  let X := {x : V // x ∈ I}
  let Y := {y : V // y ∈ nbh G I}
  let R : X → Y → Prop := fun x y => G.Adj x.1 y.1
  let _ : DecidableRel R := fun x y => Classical.propDecidable (R x y)
  obtain ⟨w⟩ := support_nonempty z hz
  have hpos0 : 0 < G.degree w.1.1 := by rw [hdegI w.1.1 w.1.2]; decide
  obtain ⟨y0, hxy0⟩ := (G.degree_pos_iff_exists_adj w.1.1).mp hpos0
  have hy0 : y0 ∈ nbh G I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, w.1.1, w.1.2, hxy0⟩
  have hY : Nonempty Y := ⟨⟨y0, hy0⟩⟩
  have hsep : ∀ (x : X) (y : Y), x.1 ≠ y.1 := by
    intro x y heq
    obtain ⟨a, ha, hay⟩ := (Finset.mem_filter.mp y.2).2
    rw [← heq] at hay
    exact hind a ha x.1 x.2 hay
  have hsize : Fintype.card X < Fintype.card V := by
    apply Fintype.card_lt_of_injective_not_surjective (fun x : X => x.1) Subtype.val_injective
    intro hsurj
    obtain ⟨x, hx⟩ := hsurj y0
    exact hsep x ⟨y0, hy0⟩ hx
  have hbranch (x : X) : Fintype.card {y : Y // R x y} = 3 := by
    let e : {y : Y // R x y} ≃ G.neighborSet x.1 :=
      { toFun := fun y => ⟨y.1.1, y.2⟩
        invFun := fun u => ⟨⟨u.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.1, x.2, u.2⟩⟩, u.2⟩
        left_inv := by intro y; rfl
        right_inv := by intro u; rfl }
    rw [Fintype.card_congr e, SimpleGraph.card_neighborSet_eq_degree, hdegI x.1 x.2]
  have hmid (y : Y) : Fintype.card {x : X // R x y} ≤ 3 := by
    let f : {x : X // R x y} → G.neighborSet y.1 := fun x => ⟨x.1.1, x.2.symm⟩
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext; apply Subtype.ext; exact congrArg Subtype.val hab
    have hc := Fintype.card_le_of_injective f hf
    rw [SimpleGraph.card_neighborSet_eq_degree] at hc
    exact hc.trans (hdegN y.1 y.2)
  let S := Support z
  let R0 : S → Y → Prop := fun x y => R x.1 y
  let _ : DecidableRel R0 := fun x y => Classical.propDecidable (R0 x y)
  let f0 : S → V := fun x => x.1.1
  have hf0 : Function.Injective f0 := fun _ _ h => Subtype.ext (Subtype.ext h)
  have hsize0 : Fintype.card S < Fintype.card V := (Fintype.card_subtype_le _).trans_lt hsize
  have hrow (y : Y) : Fintype.card {x // R0 x y} = 0 ∨ Fintype.card {x // R0 x y} = 2 := by
    have hm' := support_row_mod R z y
    have hzy : syndrome R z y = 0 := by
      have h0 := congrFun hzero y
      simpa [R] using h0
    rw [hzy] at hm'
    simp only [ZMod.val_zero] at hm'
    have hb := (support_row_le R z y).trans (hmid y)
    change Fintype.card {x : Support z // R x.1 y} = 0 ∨ Fintype.card {x : Support z // R x.1 y} = 2
    omega
  have hdeg (x : S) : 3 ≤ Fintype.card {y // R0 x y} := by
    have hh := hbranch x.1
    change 3 ≤ Fintype.card {y : Y // R x.1 y}
    omega
  have hs := safe_step_of_rows G f0 (fun y : Y => y.1) hf0 Subtype.val_injective
      (fun x y => hsep x.1 y) R0 (fun _ _ h => h) hY hsize0 hrow w
      (fun x => (by decide : 2 ≤ 3).trans (hdeg x)) (fun x _ => hdeg x) hm.2.1
  exact no_safe_step G hm hs

/-- Dual-Kernel Weight-Drop Theorem (NEW Wave 2):
In any cubic MinimalBad(G), for any independent set I and any subset S disjoint from I
such that every x in I has an even number of neighbors in S (i.e. S in ker(A^T)),
if S contains at least one vertex having all 3 neighbors in I (i.e. S meets J_3),
then S must contain at least TWO vertices outside J_3. -/
theorem dual_kernel_non_j3_ge_two {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hm : MinimalBad G) (hC : Cubic G)
    (I S : Finset V)
    (hdisj : Disjoint S I)
    (heven : ∀ x ∈ I, (G.neighborFinset x ∩ S).card % 2 = 0)
    (ha_ex : ∃ a ∈ S, (G.neighborFinset a ∩ I).card = 3) :
    2 ≤ (S.filter (fun y => (G.neighborFinset y ∩ I).card ≠ 3)).card := by
  classical
  by_contra hlt
  let B := S.filter (fun y => (G.neighborFinset y ∩ I).card ≠ 3)
  have hBcard : B.card ≤ 1 := by omega
  obtain ⟨a0, ha0S, ha0deg⟩ := ha_ex
  have hI_nonempty : I.Nonempty := by
    have hpos : 0 < (G.neighborFinset a0 ∩ I).card := by omega
    obtain ⟨x0, hx0⟩ := Finset.card_pos.mp hpos
    exact ⟨x0, (Finset.mem_inter.mp hx0).2⟩
  obtain ⟨x0, hx0I⟩ := hI_nonempty
  let X := {y : V // y ∈ S}
  let Y := {x : V // x ∈ I}
  let R : X → Y → Prop := fun y x => G.Adj y.1 x.1
  let _ : DecidableRel R := fun y x => Classical.propDecidable (R y x)
  have hsep : ∀ (y : X) (x : Y), y.1 ≠ x.1 := by
    intro y x heq
    exact Finset.disjoint_left.mp hdisj y.2 (heq ▸ x.2)
  have hsize : Fintype.card X < Fintype.card V := by
    apply Fintype.card_lt_of_injective_not_surjective (fun y : X => y.1) Subtype.val_injective
    intro hsurj
    obtain ⟨y, hy⟩ := hsurj x0
    exact hsep y ⟨x0, hx0I⟩ hy
  have hrow (x : Y) :
      (Finset.univ.filter (fun y : X => R y x)).card = 0 ∨
      (Finset.univ.filter (fun y : X => R y x)).card = 2 := by
    let e : {y : X // R y x} ≃ {v : V // v ∈ G.neighborFinset x.1 ∩ S} :=
      { toFun := fun y => ⟨y.1.1, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x.1 y.1.1).mpr y.2.symm, y.1.2⟩⟩
        invFun := fun v => ⟨⟨v.1, (Finset.mem_inter.mp v.2).2⟩, ((G.mem_neighborFinset x.1 v.1).mp (Finset.mem_inter.mp v.2).1).symm⟩
        left_inv := by intro y; rfl
        right_inv := by intro v; rfl }
    have hc : (Finset.univ.filter (fun y : X => R y x)).card = (G.neighborFinset x.1 ∩ S).card := by
      rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_coe]
    have hle : (G.neighborFinset x.1 ∩ S).card ≤ 3 := by
      have h1 := Finset.card_le_card (Finset.inter_subset_left (s₁ := G.neighborFinset x.1) (s₂ := S))
      rw [G.card_neighborFinset_eq_degree, hC x.1] at h1
      exact h1
    have hev := heven x.1 x.2
    omega
  have hp : Paired R := paired_of_two_rows R hrow
  have hdeg_eq (y : X) : Fintype.card {x : Y // R y x} = (G.neighborFinset y.1 ∩ I).card := by
    let e : {x : Y // R y x} ≃ {v : V // v ∈ G.neighborFinset y.1 ∩ I} :=
      { toFun := fun x => ⟨x.1.1, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset y.1 x.1.1).mpr x.2, x.1.2⟩⟩
        invFun := fun v => ⟨⟨v.1, (Finset.mem_inter.mp v.2).2⟩, (G.mem_neighborFinset y.1 v.1).mp (Finset.mem_inter.mp v.2).1⟩
        left_inv := by intro x; rfl
        right_inv := by intro v; rfl }
    rw [Fintype.card_congr e, Fintype.card_coe]
  have hdeg_of_not_B (y : X) (hy : y.1 ∉ B) : 3 ≤ Fintype.card {x : Y // R y x} := by
    rw [hdeg_eq]
    have h3 : (G.neighborFinset y.1 ∩ I).card = 3 := by
      by_contra hne3
      exact hy (Finset.mem_filter.mpr ⟨y.2, hne3⟩)
    omega
  have hdegrees : ∃ a w : X,
      3 ≤ Fintype.card {x : Y // R a x} ∧
      ∀ y : X, y ≠ w → 3 ≤ Fintype.card {x : Y // R y x} := by
    by_cases hBempty : B = ∅
    · refine ⟨⟨a0, ha0S⟩, ⟨a0, ha0S⟩, ?_, ?_⟩
      · rw [hdeg_eq]; omega
      · intro y _
        apply hdeg_of_not_B y
        simp [hBempty]
    · obtain ⟨w0, hw0B⟩ := Finset.nonempty_iff_ne_empty.mpr hBempty
      have hw0S : w0 ∈ S := (Finset.mem_filter.mp hw0B).1
      refine ⟨⟨a0, ha0S⟩, ⟨w0, hw0S⟩, ?_, ?_⟩
      · rw [hdeg_eq]; omega
      · intro y hyw
        apply hdeg_of_not_B y
        intro hyB
        have hsub : ({w0, y.1} : Finset V) ⊆ B := by
          intro t ht
          simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl
          · exact hw0B
          · exact hyB
        have hne : w0 ≠ y.1 := fun h => hyw (Subtype.ext h.symm)
        have h2 : ({w0, y.1} : Finset V).card = 2 := by simp [hne]
        have hle := Finset.card_le_card hsub
        omega
  have hs := safe_step_of_paired_incidence G
      (fun y : X => y.1) (fun x : Y => x.1)
      Subtype.val_injective Subtype.val_injective hsep R
      (fun _ _ h => h) hp ⟨⟨x0, hx0I⟩⟩ hsize hdegrees hm.2.1
  exact no_safe_step G hm hs

#print axioms indep_neighborhood_expansion
#print axioms indep_syndrome_no_kernel
#print axioms dual_kernel_non_j3_ge_two
end E64Wave2Indep
