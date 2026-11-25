import Leaves
import Incidence
import BipartiteDegree

namespace E64Closed
open SimpleGraph Erdos64Closure E64Core E64Leaves Erdos64Incidence
universe u

/-- Entire C-B closure leaf: every bipartite cubic hypothetical minimal
counterexample has a strictly smaller safe near graph. -/
theorem exclude_cb : Exclude.{u} Leaf.cb := by
  classical
  intro V G _ _ hm hleaf
  obtain ⟨hC,color,hproper⟩ := hleaf
  let X := {v : V // color v=false}
  let Y := {v : V // color v=true}
  let R : X → Y → Prop := fun a b => G.Adj a.1 b.1
  let _ : DecidableRel R := fun a b => Classical.propDecidable (R a b)
  have hbal := E64Bipartite.side_balance G color hproper
  have h0 := E64Bipartite.side_cubic G color false hC
  have h1 := E64Bipartite.side_cubic G color true hC
  have hcard : E64Bipartite.sideCard color false = E64Bipartite.sideCard color true := by omega
  have hXcard : Fintype.card X = E64Bipartite.sideCard color false := by
    change Fintype.card {v : V // color v=false} = _
    rw [Fintype.card_subtype]
    rfl
  have hYcard : Fintype.card Y = E64Bipartite.sideCard color true := by
    change Fintype.card {v : V // color v=true} = _
    rw [Fintype.card_subtype]
    rfl
  have hXY : Fintype.card X = Fintype.card Y := by omega
  obtain ⟨v,hv⟩ := hm.1.1
  have hvpos : 0 < G.degree v := by omega
  obtain ⟨w,hvw⟩ := (G.degree_pos_iff_exists_adj v).mp hvpos
  have hp := hproper v w hvw
  have hXYnonempty : Nonempty X ∧ Nonempty Y := by
    cases hvC : color v <;> cases hwC : color w
    · simp [hvC,hwC] at hp
    · exact ⟨⟨⟨v,hvC⟩⟩,⟨⟨w,hwC⟩⟩⟩
    · exact ⟨⟨⟨w,hwC⟩⟩,⟨⟨v,hvC⟩⟩⟩
    · simp [hvC,hwC] at hp
  have hsep (x : X) (y : Y) : x.1 ≠ y.1 := by
    intro he
    have hx := x.2
    rw [he,y.2] at hx
    contradiction
  have hsize : Fintype.card X < Fintype.card V := by
    apply Fintype.card_lt_of_injective_not_surjective (fun x : X => x.1) Subtype.val_injective
    intro hs
    obtain ⟨y⟩ := hXYnonempty.2
    obtain ⟨x,hx⟩ := hs y.1
    exact hsep x y hx
  have hbranch (x : X) : Fintype.card {y // R x y}=3 := by
    let e : {y : Y // R x y} ≃ G.neighborSet x.1 :=
      { toFun := fun y => ⟨y.1.1,y.2⟩
        invFun := fun z => ⟨⟨z.1,by
          have hz := hproper x.1 z.1 z.2
          rw [x.2] at hz
          cases hcz : color z.1 <;> simp_all⟩,z.2⟩
        left_inv := by intro z; rfl
        right_inv := by intro z; rfl }
    have hc := Fintype.card_congr e
    rw [SimpleGraph.card_neighborSet_eq_degree,hC] at hc
    exact hc
  have hmid (y : Y) : Fintype.card {x // R x y}≤3 := by
    let e : {x : X // R x y} ≃ G.neighborSet y.1 :=
      { toFun := fun x => ⟨x.1.1,(show G.Adj x.1.1 y.1 from x.2).symm⟩
        invFun := fun z => ⟨⟨z.1,by
          have hz := hproper y.1 z.1 z.2
          rw [y.2] at hz
          cases hcz : color z.1 <;> simp_all⟩,(show G.Adj y.1 z.1 from z.2).symm⟩
        left_inv := by intro z; rfl
        right_inv := by intro z; rfl }
    have hc := Fintype.card_congr e
    rw [SimpleGraph.card_neighborSet_eq_degree,hC] at hc
    exact hc.le
  have hs := safe_step_of_low_codim_incidence G
      (fun x : X => x.1) (fun y : Y => y.1)
      Subtype.val_injective Subtype.val_injective hsep R
      (fun _ _ h => h) hXYnonempty.1 hXYnonempty.2
      hsize (by omega) hbranch hmid hm.2.1
  exact no_safe_step G hm hs

theorem exclude_sb : Exclude.{u} Leaf.sb := by
  intro V G _ _ _ hleaf
  obtain ⟨⟨w,hw,hrest⟩,color,hproper⟩ := hleaf
  exact E64Bipartite.no_bipartite_one_defect G color hproper w hw hrest

#print axioms exclude_cb
#print axioms exclude_sb
end E64Closed

