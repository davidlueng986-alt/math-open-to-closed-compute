import Leaves
import Descent

/-!
Complete exclusion of all bipartite one-defect minimal Near counterexamples.
The reduction suppresses the degree-two defect, replacing its two edges by
one edge between same-color vertices. Every newly created cycle is odd.
This discharges every H-B leaf at arbitrary order, without cut assumptions.
-/
namespace E64BipartiteDefect
open SimpleGraph Erdos64Closure E64Core E64Leaves Erdos64Descent
universe u

theorem exclude_bipartite_defect {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hm : MinimalBad G) (hB : Bip G)
    (w : V) (hw : G.degree w = 2)
    (hrest : ∀ v, v ≠ w → 3 ≤ G.degree v) : False := by
  classical
  obtain ⟨color,hproper⟩ := hB
  have hncard : (G.neighborFinset w).card = 2 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, hw]
  obtain ⟨a,b,hab,hN⟩ := Finset.card_eq_two.mp hncard
  have hNbr (x : V) : G.Adj w x ↔ x = a ∨ x = b := by
    rw [← SimpleGraph.mem_neighborFinset, hN]
    simp
  have hwa : G.Adj w a := (hNbr a).mpr (Or.inl rfl)
  have hwb : G.Adj w b := (hNbr b).mpr (Or.inr rfl)
  have haw : a ≠ w := (G.ne_of_adj hwa).symm
  have hbw : b ≠ w := (G.ne_of_adj hwb).symm
  have hcol : color a = color b := by
    have h1 := hproper w a hwa
    have h2 := hproper w b hwb
    cases hwc : color w <;> cases hac : color a <;>
      cases hbc : color b <;> simp_all
  let W := {x : V // x ≠ w}
  let K : SimpleGraph W := G.induce {x | x ≠ w}
  let A : W := ⟨a,haw⟩
  let B : W := ⟨b,hbw⟩
  have hAB : A ≠ B := fun h => hab (congrArg Subtype.val h)
  let _ : DecidableRel K.Adj := fun x y => Classical.propDecidable (K.Adj x y)
  let H : SimpleGraph W := K ⊔ SimpleGraph.edge A B
  let _ : DecidableRel H.Adj := fun x y => Classical.propDecidable (H.Adj x y)
  have hKnot : ¬K.Adj A B := by
    intro h
    exact hproper a b h hcol
  let c : W → Fin 2 := fun x => if color x.val = true then 1 else 0
  have hc (x y : W) (h : K.Adj x y) : c x ≠ c y := by
    have hp := hproper x.val y.val h
    cases hx : color x.val <;> cases hy : color y.val <;>
      simp_all [c]
  have hCAB : c A = c B := by
    change (if color a = true then (1 : Fin 2) else 0) =
      (if color b = true then (1 : Fin 2) else 0)
    rw [hcol]
  have hKfree : PowerFree K := by
    intro k v p hk hp hl
    exact hm.2.1 (power_induce G {x | x ≠ w} ⟨k,v,p,hk,hp,hl⟩)
  have hHfree : PowerFree H :=
    same_color_edge_safe c hc A B hAB hCAB hKfree
  have hda : H.degree A = K.degree A + 1 :=
    degree_add_new_edge_left K A B hAB hKnot
  have hdb : H.degree B = K.degree B + 1 :=
    degree_add_new_edge_right K A B hAB hKnot
  have hall : ∀ v : W, 3 ≤ H.degree v := by
    intro v
    by_cases hva : v = A
    · subst v
      have hd := induce_delete_degree G w A
      change K.degree A + (if G.Adj a w then 1 else 0) = G.degree a at hd
      rw [if_pos hwa.symm] at hd
      have hr := hrest a haw
      omega
    by_cases hvb : v = B
    · subst v
      have hd := induce_delete_degree G w B
      change K.degree B + (if G.Adj b w then 1 else 0) = G.degree b at hd
      rw [if_pos hwb.symm] at hd
      have hr := hrest b hbw
      omega
    have hnot : ¬G.Adj v.val w := by
      intro he
      rcases (hNbr v.val).mp he.symm with h | h
      · exact hva (Subtype.ext h)
      · exact hvb (Subtype.ext h)
    have hd := induce_delete_degree G w v
    change K.degree v + (if G.Adj v.val w then 1 else 0) = G.degree v.val at hd
    rw [if_neg hnot,add_zero] at hd
    have hr : 3 ≤ K.degree v := by
      rw [hd]
      exact hrest v.val v.property
    exact hr.trans (K.degree_le_of_le (v := v)
      (H := K ⊔ SimpleGraph.edge A B) le_sup_left)
  have hnear : Near H := ⟨⟨A,hall A⟩,⟨A,fun v _ => hall v⟩⟩
  have hW : Fintype.card W + 1 = Fintype.card V := by
    rw [Fintype.card_subtype,
      show (Finset.univ.filter (fun x : V => x ≠ w)) =
        Finset.univ.erase w by ext x; simp]
    exact Finset.card_erase_add_one (Finset.mem_univ w)
  obtain ⟨k,v,p,hk,hp,hl⟩ := hm.2.2.1 W H (by omega) hnear
  exact hHfree k v p hk hp hl

/-- All four H-B terminal classes, with no order or degree bound. -/
theorem exclude_hb (s : HighSeparation) : Exclude.{u} (Leaf.hb s) := by
  intro V G _ _ hm hleaf
  obtain ⟨⟨w,hw,hrest,_⟩,hB,_⟩ := hleaf
  exact exclude_bipartite_defect G hm hB w hw hrest

/-- The same suppression argument also covers the S-B class. -/
theorem exclude_sb : Exclude.{u} Leaf.sb := by
  intro V G _ _ hm hleaf
  obtain ⟨⟨w,hw,hrest⟩,hB⟩ := hleaf
  apply exclude_bipartite_defect G hm hB w hw
  intro v hv
  exact (hrest v hv).ge

#print axioms exclude_bipartite_defect
#print axioms exclude_hb
#print axioms exclude_sb
end E64BipartiteDefect

