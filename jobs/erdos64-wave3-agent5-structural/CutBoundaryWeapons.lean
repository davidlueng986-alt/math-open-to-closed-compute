import Core
import Leaves
import PairedShadow

/-!
Erdos 64 (Wave 3, Agent #5): Cut-Boundary Exclusion Weapons for Front 1 (`CUT`).
Proves (unconditionally, all finite orders, standard axioms only):
1. `wfree_2cut_matching_and_cubic_boundary`: On any w-free side B (|B| >= 2, |Bᶜ| >= 1) of a
   2-edge cut E(B, Bᶜ) in ANY MinimalBad(G), the two cut edges hit TWO DISTINCT vertices of B
   and BOTH boundary vertices have degree EXACTLY 3 (ruling out V_{>=4} from every w-free 2-cut
   boundary, and proving every cubic 2-cut is a matching).
2. `wfree_3cut_at_most_one_high_boundary`: On any w-free side B (|B| >= 2, |Bᶜ| >= 1) of a
   3-edge cut E(B, Bᶜ) in ANY MinimalBad(G), at most ONE single-cut-edge boundary vertex in B
   can have degree >= 4.
-/

namespace E64CutBoundary
open SimpleGraph Erdos64Closure E64Core E64Leaves Erdos64Paired
universe u

variable {V : Type u}

/-- Exact degree loss of a vertex `v ∈ B` in `G.induce B`: it equals the number of neighbors
    of `v` outside `B`. -/
private theorem induce_degree_add_out [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : Set V) [DecidablePred (· ∈ B)]
    [DecidableRel (G.induce B).Adj] (v : B) :
    (G.induce B).degree v + ((G.neighborFinset v.1).filter (fun x => x ∉ B)).card = G.degree v.1 := by
  classical
  let e : G.neighborSet v.1 ≃
      (G.induce B).neighborSet v ⊕ {x : V // x ∈ (G.neighborFinset v.1).filter (fun x => x ∉ B)} :=
    { toFun := fun u =>
        if h : u.1 ∈ B then
          Sum.inl ⟨⟨u.1, h⟩, u.2⟩
        else
          Sum.inr ⟨u.1, Finset.mem_filter.mpr ⟨(G.mem_neighborFinset v.1 u.1).mpr u.2, h⟩⟩
      invFun := Sum.elim
        (fun u => ⟨u.1.1, u.2⟩)
        (fun u => ⟨u.1, (G.mem_neighborFinset v.1 u.1).mp (Finset.mem_filter.mp u.2).1⟩)
      left_inv := by
        intro u
        by_cases h : u.1 ∈ B <;> simp [h]
      right_inv := by
        rintro (u | u)
        · simp [u.1.2]
        · have hnot : u.1 ∉ B := (Finset.mem_filter.mp u.2).2
          simp [hnot] }
  have hc := Fintype.card_congr e
  rw [SimpleGraph.card_neighborSet_eq_degree, Fintype.card_sum,
    SimpleGraph.card_neighborSet_eq_degree, Fintype.card_coe] at hc
  exact hc.symm

/-- NEW (Wave 3, Agent #5): On any w-free side B (|B| >= 2, |Bᶜ| >= 1) of a 2-edge cut in
    ANY MinimalBad(G), the two cut edges hit two distinct vertices of B AND both boundary
    vertices have degree exactly 3. -/
theorem wfree_2cut_matching_and_cubic_boundary [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (B : Set V) [DecidablePred (· ∈ B)]
    (hB2 : 2 ≤ Fintype.card B) (hBout : ∃ z : V, z ∉ B)
    (hwfree : ∀ v : B, 3 ≤ G.degree v.1)
    (u₁ u₂ : B) (v₁ v₂ : V)
    (hcut : ∀ u : B, ∀ v : V, v ∉ B → G.Adj u.1 v → (u = u₁ ∧ v = v₁) ∨ (u = u₂ ∧ v = v₂)) :
    u₁ ≠ u₂ ∧ G.degree u₁.1 = 3 ∧ G.degree u₂.1 = 3 := by
  classical
  let H := G.induce B
  let _ : DecidableRel H.Adj := fun a b => Classical.dec _
  have hcard_lt : Fintype.card B < Fintype.card V := by
    obtain ⟨z, hz⟩ := hBout
    apply Fintype.card_lt_of_injective_not_surjective (fun x : B => x.1) Subtype.val_injective
    intro hsurj
    obtain ⟨x, hx⟩ := hsurj z
    exact hz (hx ▸ x.2)
  have hout_zero : ∀ u : B, u ≠ u₁ → u ≠ u₂ → 3 ≤ H.degree u := by
    intro u hu1 hu2
    have hd := induce_degree_add_out G B u
    have hemp : (G.neighborFinset u.1).filter (fun x => x ∉ B) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x hx hnotB
      rcases hcut u x hnotB ((G.mem_neighborFinset u.1 x).mp hx) with ⟨h, _⟩ | ⟨h, _⟩
      · exact hu1 h
      · exact hu2 h
    rw [hemp, Finset.card_empty, add_zero] at hd
    rw [hd]; exact hwfree u
  have hne : u₁ ≠ u₂ := by
    intro heq
    subst heq
    have hnear : Near H := near_of_except H u₁ hB2 (fun u hu => hout_zero u hu hu)
    exact hm.2.1 (power_induce G B (hm.2.2.1 B H hcard_lt hnear))
  have ho1 : ((G.neighborFinset u₁.1).filter (fun x => x ∉ B)).card ≤ 1 := by
    have hsub : (G.neighborFinset u₁.1).filter (fun x => x ∉ B) ⊆ {v₁} := by
      intro x hx
      have hmem := Finset.mem_filter.mp hx
      rcases hcut u₁ x hmem.2 ((G.mem_neighborFinset u₁.1 x).mp hmem.1) with ⟨_, rfl⟩ | ⟨h, _⟩
      · simp
      · exact False.elim (hne h)
    exact (Finset.card_le_card hsub).trans (by simp)
  have ho2 : ((G.neighborFinset u₂.1).filter (fun x => x ∉ B)).card ≤ 1 := by
    have hsub : (G.neighborFinset u₂.1).filter (fun x => x ∉ B) ⊆ {v₂} := by
      intro x hx
      have hmem := Finset.mem_filter.mp hx
      rcases hcut u₂ x hmem.2 ((G.mem_neighborFinset u₂.1 x).mp hmem.1) with ⟨h, _⟩ | ⟨_, rfl⟩
      · exact False.elim (hne h.symm)
      · simp
    exact (Finset.card_le_card hsub).trans (by simp)
  have hu1_3 : G.degree u₁.1 = 3 := by
    have hge := hwfree u₁
    by_contra hne3
    have hge4 : 4 ≤ G.degree u₁.1 := by omega
    have hu1_H : 3 ≤ H.degree u₁ := by
      have hd := induce_degree_add_out G B u₁
      omega
    have hnear : Near H := near_of_except H u₂ hB2 (fun u hu => by
      by_cases hu1 : u = u₁
      · rw [hu1]; exact hu1_H
      · exact hout_zero u hu1 hu)
    exact hm.2.1 (power_induce G B (hm.2.2.1 B H hcard_lt hnear))
  have hu2_3 : G.degree u₂.1 = 3 := by
    have hge := hwfree u₂
    by_contra hne3
    have hge4 : 4 ≤ G.degree u₂.1 := by omega
    have hu2_H : 3 ≤ H.degree u₂ := by
      have hd := induce_degree_add_out G B u₂
      omega
    have hnear : Near H := near_of_except H u₁ hB2 (fun u hu => by
      by_cases hu2 : u = u₂
      · rw [hu2]; exact hu2_H
      · exact hout_zero u hu hu2)
    exact hm.2.1 (power_induce G B (hm.2.2.1 B H hcard_lt hnear))
  exact ⟨hne, hu1_3, hu2_3⟩

/-- NEW (Wave 3, Agent #5): On any w-free side B (|B| >= 2, |Bᶜ| >= 1) of a 3-edge cut in
    ANY MinimalBad(G), two distinct single-cut-edge boundary vertices u₁, u₂ in B cannot BOTH
    have degree >= 4. -/
theorem wfree_3cut_at_most_one_high_boundary [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (B : Set V) [DecidablePred (· ∈ B)]
    (hB2 : 2 ≤ Fintype.card B) (hBout : ∃ z : V, z ∉ B)
    (hwfree : ∀ v : B, 3 ≤ G.degree v.1)
    (u₁ u₂ u₃ : B)
    (hcut : ∀ u : B, ∀ v : V, v ∉ B → G.Adj u.1 v → u = u₁ ∨ u = u₂ ∨ u = u₃)
    (ho1 : ((G.neighborFinset u₁.1).filter (fun x => x ∉ B)).card ≤ 1)
    (ho2 : ((G.neighborFinset u₂.1).filter (fun x => x ∉ B)).card ≤ 1) :
    ¬ (4 ≤ G.degree u₁.1 ∧ 4 ≤ G.degree u₂.1) := by
  classical
  rintro ⟨h1, h2⟩
  let H := G.induce B
  let _ : DecidableRel H.Adj := fun a b => Classical.dec _
  have hcard_lt : Fintype.card B < Fintype.card V := by
    obtain ⟨z, hz⟩ := hBout
    apply Fintype.card_lt_of_injective_not_surjective (fun x : B => x.1) Subtype.val_injective
    intro hsurj
    obtain ⟨x, hx⟩ := hsurj z
    exact hz (hx ▸ x.2)
  have hu1_H : 3 ≤ H.degree u₁ := by
    have hd := induce_degree_add_out G B u₁; omega
  have hu2_H : 3 ≤ H.degree u₂ := by
    have hd := induce_degree_add_out G B u₂; omega
  have hnear : Near H := near_of_except H u₃ hB2 (fun u hu3 => by
    by_cases hu1 : u = u₁
    · rw [hu1]; exact hu1_H
    · by_cases hu2 : u = u₂
      · rw [hu2]; exact hu2_H
      · have hd := induce_degree_add_out G B u
        have hemp : (G.neighborFinset u.1).filter (fun x => x ∉ B) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro x hx hnotB
          rcases hcut u x hnotB ((G.mem_neighborFinset u.1 x).mp hx) with h | h | h
          · exact hu1 h
          · exact hu2 h
          · exact hu3 h
        rw [hemp, Finset.card_empty, add_zero] at hd
        rw [hd]; exact hwfree u)
  exact hm.2.1 (power_induce G B (hm.2.2.1 B H hcard_lt hnear))

#print axioms wfree_2cut_matching_and_cubic_boundary
#print axioms wfree_3cut_at_most_one_high_boundary

end E64CutBoundary
