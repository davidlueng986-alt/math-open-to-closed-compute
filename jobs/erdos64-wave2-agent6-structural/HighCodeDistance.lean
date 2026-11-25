import Core
import Leaves
import Incidence
import ClosedDefectCore

/-!
Erdos 64 (Wave 2, Agent #6): Strengthened Class H F2 Incidence Code Distance.
Proves (unconditionally, all finite orders, standard axioms only):
1. V_{>=4} is an independent set in every MinimalBad(G).
2. Every neighbor of V_{>=4} in MinimalBad(G) has degree exactly 3.
3. Weighted Code-Distance Theorem: for any subset S ⊆ V_{>=4} with |S| ≥ 2 and
   all degrees in S ≥ d (d ≥ 4), the F2 syndrome weight is at least 2d - 4.
4. Strict improvement over Wave 1's d_min ≥ 3: for every nonzero z : V_{>=4} → ZMod 2,
   the F2 incidence code weight is at least 4 (d_min(col(M)) ≥ 4).
-/

namespace E64HighCode
open SimpleGraph Erdos64Closure E64Core E64Leaves Erdos64Paired Erdos64Incidence E64DefectCore
open scoped BigOperators
universe u

variable {V : Type u}

/-- In any MinimalBad(G), no two vertices of degree >= 4 are adjacent. -/
theorem high_independent [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {a b : V} (ha : 4 ≤ G.degree a) (hb : 4 ≤ G.degree b) : ¬ G.Adj a b := by
  classical
  intro hab
  obtain ⟨_, w, hw⟩ := hm.1
  have hcard : 2 ≤ Fintype.card V := by
    have := G.degree_lt_card_verts a
    omega
  let H := G \ SimpleGraph.edge a b
  let _ : DecidableRel H.Adj := inferInstanceAs (DecidableRel (G \ SimpleGraph.edge a b).Adj)
  have hnear : Near H := by
    apply near_of_except H w hcard
    intro v hv
    have hdeg := erase_edge_degree G a b hab v
    change H.degree v + (if v = a ∨ v = b then 1 else 0) = G.degree v at hdeg
    by_cases hva : v = a
    · subst v; simp at hdeg; omega
    · by_cases hvb : v = b
      · subst v; simp at hdeg; omega
      · simp [hva, hvb] at hdeg; rw [hdeg]; exact hw v hv
  have hEq : H = G := hm.2.2.2 H sdiff_le hnear
  have he : H.Adj a b := hEq ▸ hab
  have hno : ¬ H.Adj a b := by
    intro h
    have hn := (SimpleGraph.sdiff_adj G (SimpleGraph.edge a b) a b).mp h
    exact hn.2 ((SimpleGraph.edge_adj a b a b).mpr ⟨Or.inl ⟨rfl, rfl⟩, G.ne_of_adj hab⟩)
  exact hno he

/-- In any MinimalBad(G), every neighbor of a vertex of degree >= 4 has degree exactly 3. -/
theorem high_neighbor_cubic [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {a y : V} (ha : 4 ≤ G.degree a) (hay : G.Adj a y) : G.degree y = 3 := by
  have hy2 := no_small_defect G hm y
  have hy_not2 : G.degree y ≠ 2 := by
    intro hyw
    have := defect_neighbor_cubic G hm hyw hay.symm
    omega
  have hy_not4 : ¬ 4 ≤ G.degree y := fun hy4 => high_independent G hm ha hy4 hay
  omega

/-- Weighted F2 Code-Distance Theorem for Class H:
    Let V₄ = {v // 4 ≤ deg v}, V₃ = {v // deg v = 3}, and M be the F2 incidence matrix.
    For any z : V₄ → ZMod 2 whose support S has |S| ≥ 2 and ∀ x ∈ S, d ≤ deg x (d ≥ 4),
    the Hamming weight of M z is at least 2d - 4. -/
theorem high_code_weight_ge_two_sub_four [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (hH : HighDefect G) (d : ℕ) (hd : 4 ≤ d)
    (z : {v : V // 4 ≤ G.degree v} → ZMod 2)
    (hS2 : 2 ≤ Fintype.card (Support z))
    (hdegS : ∀ x : Support z, d ≤ G.degree x.1.1) :
    let V₄ := {v : V // 4 ≤ G.degree v}
    let V₃ := {v : V // G.degree v = 3}
    let R : V₄ → V₃ → Prop := fun a y => G.Adj a.1 y.1
    letI : DecidableRel R := fun a y => Classical.dec _
    2 * d - 4 ≤ Fintype.card {y : V₃ // syndrome R z y = 1} := by
  classical
  intro V₄ V₃ R
  by_contra hlt
  have hOlt : Fintype.card {y : V₃ // syndrome R z y = 1} < 2 * d - 4 := by omega
  let S := Support z
  let O := {y : V₃ // syndrome R z y = 1}
  have hex : ∀ y : O, ∃ x : S, R x.1 y.1 := by
    intro y
    have hmod := support_row_mod R z y.1
    rw [y.2] at hmod
    have hpos : 0 < Fintype.card {x : S // R x.1 y.1} := by
      have : (1 : ZMod 2).val = 1 := rfl
      omega
    obtain ⟨⟨x, hx⟩⟩ := Fintype.card_pos_iff.mp hpos
    exact ⟨x, hx⟩
  choose pick hpick using hex
  let R' : S → V₃ → Prop := fun x y => R x.1 y ∧ ∀ hy : syndrome R z y = 1, pick ⟨y, hy⟩ ≠ x
  let _ : DecidableRel R' := fun x y => Classical.dec _
  have hrow : ∀ y : V₃, Fintype.card {x : S // R' x y} = 0 ∨ Fintype.card {x : S // R' x y} = 2 := by
    intro y
    have hle3 : Fintype.card {x : S // R x.1 y} ≤ 3 := by
      let emb : {x : S // R x.1 y} → G.neighborSet y.1 := fun x => ⟨x.1.1.1, x.2.symm⟩
      have hinj : Function.Injective emb := by
        intro a b h
        apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
        exact congrArg Subtype.val h
      have hc := Fintype.card_le_of_injective emb hinj
      rw [SimpleGraph.card_neighborSet_eq_degree, y.2] at hc
      exact hc
    have hmod := support_row_mod R z y
    rcases field_cases (syndrome R z y) with h0 | h1
    · have heq : Fintype.card {x : S // R' x y} = Fintype.card {x : S // R x.1 y} := by
        apply Fintype.card_congr
        exact Equiv.subtypeEquivRight (fun x => by simp [R', h0])
      rw [h0] at hmod
      have : (0 : ZMod 2).val = 0 := rfl
      omega
    · have heq : Fintype.card {x : S // R' x y} = Fintype.card {x : S // R x.1 y ∧ x ≠ pick ⟨y, h1⟩} := by
        apply Fintype.card_congr
        refine Equiv.subtypeEquivRight (fun x => ?_)
        constructor
        · rintro ⟨hr, hne⟩; exact ⟨hr, (hne h1).symm⟩
        · rintro ⟨hr, hne⟩; exact ⟨hr, fun _ => hne.symm⟩
      rw [heq]
      have hrem := card_remove_one (fun x : S => R x.1 y) (pick ⟨y, h1⟩) (hpick ⟨y, h1⟩)
      rw [h1] at hmod
      have : (1 : ZMod 2).val = 1 := rfl
      omega
  let del : S → ℕ := fun x => Fintype.card {y : O // pick y = x}
  have hsum_del : ∑ x : S, del x = Fintype.card O := by
    have e : (Σ x : S, {y : O // pick y = x}) ≃ O :=
      { toFun := fun p => p.2.1
        invFun := fun y => ⟨pick y, ⟨y, rfl⟩⟩
        left_inv := by rintro ⟨x, ⟨y, rfl⟩⟩; rfl
        right_inv := by intro y; rfl }
    rw [← Fintype.card_congr e, Fintype.card_sigma]
  have hone : ∃ w : S, ∀ x : S, x ≠ w → del x < d - 2 := by
    by_cases hex2 : ∃ w : S, d - 2 ≤ del w
    · obtain ⟨w, hw⟩ := hex2
      refine ⟨w, fun x hxw => ?_⟩
      by_contra hge
      have hxge : d - 2 ≤ del x := by omega
      have hle : del x + del w ≤ ∑ t : S, del t := by
        have hsub : ({x, w} : Finset S) ⊆ Finset.univ := Finset.subset_univ _
        have hsum := Finset.sum_le_sum_of_subset (f := del) hsub
        rw [Finset.sum_pair hxw] at hsum
        exact hsum
      omega
    · push Not at hex2
      obtain ⟨w⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card S)
      exact ⟨w, fun x _ => hex2 x⟩
  obtain ⟨w, hw⟩ := hone
  have hdeg_eq : ∀ x : S, Fintype.card {y : V₃ // R' x y} + del x = G.degree x.1.1 := by
    intro x
    let e_all : {y : V₃ // R x.1 y} ≃ G.neighborSet x.1.1 :=
      { toFun := fun y => ⟨y.1.1, y.2⟩
        invFun := fun z => ⟨⟨z.1, high_neighbor_cubic G hm x.1.2 z.2⟩, z.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hall : Fintype.card {y : V₃ // R x.1 y} = G.degree x.1.1 := by
      rw [Fintype.card_congr e_all, SimpleGraph.card_neighborSet_eq_degree]
    let e_split : {y : V₃ // R x.1 y} ≃ {y : V₃ // R' x y} ⊕ {y : O // pick y = x} :=
      { toFun := fun y =>
          if h : ∃ hy : syndrome R z y.1 = 1, pick ⟨y.1, hy⟩ = x then
            Sum.inr ⟨⟨y.1, h.1⟩, h.2⟩
          else
            Sum.inl ⟨y.1, ⟨y.2, fun hy heq => h ⟨hy, heq⟩⟩⟩
        invFun := Sum.elim
          (fun y => ⟨y.1, y.2.1⟩)
          (fun y => ⟨y.1.1, y.2 ▸ hpick y.1⟩)
        left_inv := by
          intro y
          by_cases h : ∃ hy : syndrome R z y.1 = 1, pick ⟨y.1, hy⟩ = x
          · simp [h]
          · simp [h]
        right_inv := by
          rintro (y | y)
          · have hnot : ¬ ∃ hy : syndrome R z y.1 = 1, pick ⟨y.1, hy⟩ = x :=
              fun ⟨hy, heq⟩ => y.2.2 hy heq
            simp [hnot]
          · have hex' : ∃ hy : syndrome R z y.1.1 = 1, pick ⟨y.1.1, hy⟩ = x := ⟨y.1.2, y.2⟩
            simp [hex'] }
    have hc := Fintype.card_congr e_split
    rw [hall, Fintype.card_sum] at hc
    exact hc.symm
  have hex_a : ∃ a : S, a ≠ w := by
    by_contra h
    have hinj : Function.Injective (fun _ : S => ()) := by
      intro p q _
      have hp : p = w := by by_contra hn; exact h ⟨p, hn⟩
      have hq : q = w := by by_contra hn; exact h ⟨q, hn⟩
      exact hp.trans hq.symm
    have hc := Fintype.card_le_of_injective _ hinj
    simp at hc; omega
  obtain ⟨a, haw⟩ := hex_a
  have hV₃ : Nonempty V₃ := by
    have hpos : 0 < G.degree a.1.1 := by have := a.1.2; omega
    obtain ⟨y, hay⟩ := (G.degree_pos_iff_exists_adj a.1.1).mp hpos
    exact ⟨⟨y, high_neighbor_cubic G hm a.1.2 hay⟩⟩
  obtain ⟨w₀, hw₀, _, _⟩ := hH
  have hsize : Fintype.card S < Fintype.card V := by
    apply Fintype.card_lt_of_injective_not_surjective (fun x : S => x.1.1)
      (fun p q h => Subtype.ext (Subtype.ext h))
    intro hsurj
    obtain ⟨x, hx⟩ := hsurj w₀
    have := x.1.2
    rw [hx, hw₀] at this
    omega
  have hstep : SafeStep G := by
    apply safe_step_of_paired_incidence G (fun x : S => x.1.1) (fun y : V₃ => y.1)
      (fun p q h => Subtype.ext (Subtype.ext h)) Subtype.val_injective
      (fun x y heq => by have h1 := x.1.2; have h2 := y.2; rw [heq] at h1; omega)
      R' (fun _ _ h => h.1)
      (paired_of_two_rows R' (fun y => by simpa only [Fintype.card_subtype] using hrow y))
      hV₃ hsize ?_ hm.2.1
    refine ⟨a, w, ?_, ?_⟩
    · have h1 := hdeg_eq a; have h2 := hw a haw; have h3 := hdegS a; omega
    · intro x hxw
      have h1 := hdeg_eq x; have h2 := hw x hxw; have h3 := hdegS x; omega
  exact no_safe_step G hm hstep

/-- NEW (Wave 2, Agent #6): Class H Strengthened Code Distance d_min(col(M)) ≥ 4
    (strictly improving Wave 1's d_min ≥ 3). -/
theorem high_code_dist_ge_four [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (hH : HighDefect G)
    (z : {v : V // 4 ≤ G.degree v} → ZMod 2) (hz : z ≠ 0) :
    let V₄ := {v : V // 4 ≤ G.degree v}
    let V₃ := {v : V // G.degree v = 3}
    let R : V₄ → V₃ → Prop := fun a y => G.Adj a.1 y.1
    letI : DecidableRel R := fun a y => Classical.dec _
    4 ≤ Fintype.card {y : V₃ // syndrome R z y = 1} := by
  classical
  intro V₄ V₃ R
  by_cases hS2 : 2 ≤ Fintype.card (Support z)
  · have h := high_code_weight_ge_two_sub_four G hm hH 4 le_rfl z hS2 (fun x => x.1.2)
    simpa using h
  · obtain ⟨x₀⟩ := support_nonempty z hz
    have huniq : ∀ x : Support z, x = x₀ := by
      intro x
      by_contra hne
      have h2 : 2 ≤ Fintype.card (Support z) := by
        let f : Bool → Support z := fun b => if b then x else x₀
        have hf : Function.Injective f := by
          intro p q he; cases p <;> cases q <;> simp_all [f]
        have hc := Fintype.card_le_of_injective f hf
        simp at hc; omega
      omega
    have hz_eq : z = Erdos64Binary.unit x₀.1 := by
      ext a
      by_cases ha : a = x₀.1
      · subst a; simp [Erdos64Binary.unit, x₀.2]
      · simp only [Erdos64Binary.unit, if_neg ha]
        rcases field_cases (z a) with h0 | h1
        · exact h0
        · exact False.elim (ha (congrArg Subtype.val (huniq ⟨a, h1⟩)))
    let e : {y : V₃ // syndrome R z y = 1} ≃ G.neighborSet x₀.1.1 :=
      { toFun := fun y => ⟨y.1.1, by
          have hy := y.2
          rw [hz_eq, syndrome_unit] at hy
          by_contra hna
          simp [R, hna] at hy⟩
        invFun := fun u => ⟨⟨u.1, high_neighbor_cubic G hm x₀.1.2 u.2⟩, by
          rw [hz_eq, syndrome_unit]
          simp [R, u.2]⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr e, SimpleGraph.card_neighborSet_eq_degree]
    exact x₀.1.2

#print axioms high_independent
#print axioms high_neighbor_cubic
#print axioms high_code_weight_ge_two_sub_four
#print axioms high_code_dist_ge_four

end E64HighCode
