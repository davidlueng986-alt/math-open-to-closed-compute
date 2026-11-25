import Core
import Leaves
import PairedShadow
import ClosedDefectCore
import Identification
import HighCodeDistance

/-!
Erdos 64 (Wave 3, Agent #5): Class H & One-Defect Structural Weapons.
Proves (unconditionally, all finite orders, standard axioms only):
1. `class_h_no_defect_triangle_adj_high` (NEW): No defect triangle {w, b₁, b₂} in H-T-2
   can be adjacent to any vertex x ∈ V_{>=4}.
2. `class_h_defect_to_high_neighbor_dyadic_path` (NEW): For every x ∈ V_{>=4} and every
   y ∈ N(x) \ N(w) in Class H, G - xy contains a simple w-y path of length 2^k (k >= 2).
3. `class_h_defect_neighbor_high_edge_fermat` (NEW): If b₁ ∈ N(w) is adjacent to x ∈ V_{>=4},
   then G - xb₁ contains a simple w-b₁ path of length 2^k (k >= 2) (forming a (2^k + 1)-cycle
   through the edge wb₁).
4. `defect_suppression_dyadic_path` (First Lean 4.36 verification): For any MinimalBad(G)
   with deg(w)=2 and non-adjacent neighbors b₁, b₂, G - w contains a simple b₁-b₂ path of
   length 2^k (k >= 2).
5. `class_h_double_edge_deletion_path` (NEW): If b₁ ∈ N(w) is adjacent to x₁ ∈ V_{>=4}, then
   for every other edge x₂y₂ incident to V_{>=4} (with x₁ ≠ x₂ or deg(x₁) >= 5),
   G - w - x₁b₁ - x₂y₂ STILL contains a simple b₁-b₂ path of length 2^k (k >= 2).
-/

namespace E64ClassH
open SimpleGraph Erdos64Closure E64Core E64Leaves Erdos64Paired E64DefectCore
open E64Identification E64HighCode
universe u

variable {V : Type u}

/-- Helper: in MinimalBad(G), a degree-2 vertex w has exactly its two distinct neighbors. -/
private theorem deg2_neighbors_eq [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {w b₁ b₂ z : V}
    (hw : G.degree w = 2) (hb₁ : G.Adj w b₁) (hb₂ : G.Adj w b₂) (hne : b₁ ≠ b₂)
    (hz : G.Adj w z) : z = b₁ ∨ z = b₂ := by
  classical
  by_contra h
  push Not at h
  have hs : ({b₁, b₂, z} : Finset V) ⊆ G.neighborFinset w := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact (G.mem_neighborFinset w _).mpr hb₁
    · exact (G.mem_neighborFinset w _).mpr hb₂
    · exact (G.mem_neighborFinset w _).mpr hz
  have hc := Finset.card_le_card hs
  have h3 : ({b₁, b₂, z} : Finset V).card = 3 := by
    simp [hne, Ne.symm h.1, Ne.symm h.2]
  rw [h3, G.card_neighborFinset_eq_degree, hw] at hc
  omega

/-- Helper: a degree-3 vertex a with two distinct neighbors b, c has at most one third neighbor. -/
private theorem deg3_third_unique [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {a b c x y : V}
    (ha : G.degree a = 3) (hab : G.Adj a b) (hac : G.Adj a c) (hbc : b ≠ c)
    (hax : G.Adj a x) (hay : G.Adj a y)
    (hxb : x ≠ b) (hxc : x ≠ c) (hyb : y ≠ b) (hyc : y ≠ c) : x = y := by
  classical
  by_contra hxy
  have hs : ({b, c, x, y} : Finset V) ⊆ G.neighborFinset a := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact (G.mem_neighborFinset a _).mpr hab
    · exact (G.mem_neighborFinset a _).mpr hac
    · exact (G.mem_neighborFinset a _).mpr hax
    · exact (G.mem_neighborFinset a _).mpr hay
  have hc := Finset.card_le_card hs
  have h4 : ({b, c, x, y} : Finset V).card = 4 := by
    simp [hbc, Ne.symm hxb, Ne.symm hxc, Ne.symm hyb, Ne.symm hyc, hxy]
  rw [h4, G.card_neighborFinset_eq_degree, ha] at hc
  omega

/-- NEW (Wave 3, Agent #5): No defect triangle {w, b₁, b₂} in Class H can be adjacent to V_{>=4}. -/
theorem class_h_no_defect_triangle_adj_high [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {w b₁ b₂ x : V} (hw : G.degree w = 2)
    (hwb₁ : G.Adj w b₁) (hwb₂ : G.Adj w b₂) (hb₁b₂ : G.Adj b₁ b₂)
    (hx4 : 4 ≤ G.degree x) : ¬ G.Adj b₁ x := by
  classical
  intro hb₁x
  have hdb₁ : G.degree b₁ = 3 := defect_neighbor_cubic G hm hw hwb₁
  have hdb₂ : G.degree b₂ = 3 := defect_neighbor_cubic G hm hw hwb₂
  have hb₁ne : b₁ ≠ b₂ := G.ne_of_adj hb₁b₂
  have hxw : x ≠ w := by intro h; subst h; omega
  have hxb₁ : x ≠ b₁ := (G.ne_of_adj hb₁x).symm
  have hxb₂ : x ≠ b₂ := by intro h; subst h; omega
  let S : Set V := {v | v ≠ w ∧ v ≠ b₁ ∧ v ≠ b₂}
  let H := G.induce S
  let _ : DecidableRel H.Adj := fun a b => Classical.dec _
  have hcard_lt : Fintype.card S < Fintype.card V := by
    apply Fintype.card_lt_of_injective_not_surjective (fun v : S => v.1) Subtype.val_injective
    intro hsurj
    obtain ⟨v, hv⟩ := hsurj w
    exact v.2.1 hv
  have hxS : x ∈ S := ⟨hxw, hxb₁, hxb₂⟩
  have hdeg_drop : ∀ v : S,
      H.degree v + (if G.Adj v.1 b₁ ∨ G.Adj v.1 b₂ then 1 else 0) = G.degree v.1 := by
    intro v
    have hnw : ¬ G.Adj v.1 w := fun h => by
      rcases deg2_neighbors_eq G hw hwb₁ hwb₂ hb₁ne h.symm with h' | h'
      · exact v.2.2.1 h'
      · exact v.2.2.2 h'
    have hnboth : ¬ (G.Adj v.1 b₁ ∧ G.Adj v.1 b₂) := by
      rintro ⟨h1, h2⟩
      exact hm.2.1 (rectangle_power G (G.ne_of_adj hwb₁) v.2.1.symm (G.ne_of_adj hwb₂)
        (G.ne_of_adj h1).symm hb₁ne (G.ne_of_adj h2) hwb₁ h1.symm h2 hwb₂.symm)
    let e : H.neighborSet v ≃ {u : V // G.Adj v.1 u ∧ u ≠ b₁ ∧ u ≠ b₂} :=
      { toFun := fun u => ⟨u.1.1, u.2, u.1.2.2.1, u.1.2.2.2⟩
        invFun := fun u => ⟨⟨u.1, fun h => hnw (h ▸ u.2.1), u.2.2.1, u.2.2.2⟩, u.2.1⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hc := Fintype.card_congr e
    rw [SimpleGraph.card_neighborSet_eq_degree, Fintype.card_subtype] at hc
    by_cases h1 : G.Adj v.1 b₁
    · have h2 : ¬ G.Adj v.1 b₂ := fun h => hnboth ⟨h1, h⟩
      have hs : (Finset.univ.filter (fun u : V => G.Adj v.1 u ∧ u ≠ b₁ ∧ u ≠ b₂)) =
          (G.neighborFinset v.1).erase b₁ := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
          SimpleGraph.mem_neighborFinset]
        constructor
        · rintro ⟨hu, hu1, _⟩; exact ⟨hu1, hu⟩
        · rintro ⟨hu1, hu⟩; exact ⟨hu, hu1, fun h => h2 (h ▸ hu)⟩
      rw [hs] at hc
      simp only [h1, true_or, ↓reduceIte]
      rw [hc, ← G.card_neighborFinset_eq_degree]
      exact Finset.card_erase_add_one ((G.mem_neighborFinset v.1 b₁).mpr h1)
    · by_cases h2 : G.Adj v.1 b₂
      · have hs : (Finset.univ.filter (fun u : V => G.Adj v.1 u ∧ u ≠ b₁ ∧ u ≠ b₂)) =
            (G.neighborFinset v.1).erase b₂ := by
          ext u
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
            SimpleGraph.mem_neighborFinset]
          constructor
          · rintro ⟨hu, _, hu2⟩; exact ⟨hu2, hu⟩
          · rintro ⟨hu2, hu⟩; exact ⟨hu, fun h => h1 (h ▸ hu), hu2⟩
        rw [hs] at hc
        simp only [h2, or_true, ↓reduceIte]
        rw [hc, ← G.card_neighborFinset_eq_degree]
        exact Finset.card_erase_add_one ((G.mem_neighborFinset v.1 b₂).mpr h2)
      · have hs : (Finset.univ.filter (fun u : V => G.Adj v.1 u ∧ u ≠ b₁ ∧ u ≠ b₂)) =
            G.neighborFinset v.1 := by
          ext u
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset]
          constructor
          · exact fun h => h.1
          · intro hu; exact ⟨hu, fun h => h1 (h ▸ hu), fun h => h2 (h ▸ hu)⟩
        rw [hs] at hc
        simp only [h1, h2, or_self, ↓reduceIte, add_zero]
        rw [hc, G.card_neighborFinset_eq_degree]
  have hxdeg : 3 ≤ H.degree ⟨x, hxS⟩ := by
    have hd := hdeg_drop ⟨x, hxS⟩
    dsimp only at hd
    omega
  obtain ⟨_, w', hw'⟩ := hm.1
  have hww : w' = w := by
    by_contra hne; have := hw' w (Ne.symm hne); omega
  subst w'
  have hnear : Near H := by
    refine ⟨⟨⟨x, hxS⟩, hxdeg⟩, ?_⟩
    by_cases hex : ∃ z : S, G.Adj z.1 b₂
    · obtain ⟨z, hz⟩ := hex
      refine ⟨z, fun v hv => ?_⟩
      have hnv1 : v.1 ≠ x → ¬ G.Adj v.1 b₁ := by
        intro hne h1
        exact hne (deg3_third_unique G hdb₁ hwb₁.symm hb₁b₂ (G.ne_of_adj hwb₂) h1.symm hb₁x
          v.2.1 v.2.2.2 hxw hxb₂)
      have hnv2 : ¬ G.Adj v.1 b₂ := by
        intro h2
        exact hv (Subtype.ext (deg3_third_unique G hdb₂ hwb₂.symm hb₁b₂.symm (G.ne_of_adj hwb₁)
          h2.symm hz.symm v.2.1 v.2.2.1 z.2.1 z.2.2.1))
      by_cases hvx : v.1 = x
      · have : v = ⟨x, hxS⟩ := Subtype.ext hvx
        rw [this]; exact hxdeg
      · have hd := hdeg_drop v
        have hnv1' := hnv1 hvx
        simp only [hnv1', hnv2, or_self, ↓reduceIte, add_zero] at hd
        rw [hd]; exact hw' v.1 v.2.1
    · push Not at hex
      refine ⟨⟨x, hxS⟩, fun v hv => ?_⟩
      have hvx : v.1 ≠ x := fun h => hv (Subtype.ext h)
      have hnv1 : ¬ G.Adj v.1 b₁ := fun h1 =>
        hvx (deg3_third_unique G hdb₁ hwb₁.symm hb₁b₂ (G.ne_of_adj hwb₂) h1.symm hb₁x
          v.2.1 v.2.2.2 hxw hxb₂)
      have hnv2 : ¬ G.Adj v.1 b₂ := hex v
      have hd := hdeg_drop v
      simp only [hnv1, hnv2, or_self, ↓reduceIte, add_zero] at hd
      rw [hd]; exact hw' v.1 v.2.1
  have hpow : HasPower H := hm.2.2.1 S H hcard_lt hnear
  exact hm.2.1 (power_induce G S hpow)

/-- NEW (Wave 3, Agent #5): Class H Universal Defect-to-High-Neighbor Dyadic Path Theorem.
    For every x ∈ V_{>=4} and every y ∈ N(x) with ¬G.Adj w y, G - xy contains a simple
    w-y path of length 2^k (k >= 2). -/
theorem class_h_defect_to_high_neighbor_dyadic_path [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {w x y : V} (hw : G.degree w = 2) (hx4 : 4 ≤ G.degree x)
    (hxy : G.Adj x y) (hnwy : ¬ G.Adj w y) :
    ∃ (k : ℕ) (p : (G \ SimpleGraph.edge x y).Walk w y),
      2 ≤ k ∧ p.IsPath ∧ p.length = 2 ^ k := by
  classical
  let G' := G \ SimpleGraph.edge x y
  let _ : DecidableRel G'.Adj := inferInstanceAs (DecidableRel (G \ SimpleGraph.edge x y).Adj)
  have hG'free : ¬ HasPower G' := fun h => hm.2.1 (power_mono sdiff_le h)
  have hdy : G.degree y = 3 := high_neighbor_cubic G hm hx4 hxy
  have hwy : w ≠ y := by intro h; subst h; omega
  have hwx : w ≠ x := by intro h; subst h; omega
  have hG'w : G'.degree w = 2 := by
    have := erase_edge_degree G x y hxy w
    change G'.degree w + (if w = x ∨ w = y then 1 else 0) = G.degree w at this
    simp [hwx, hwy] at this; omega
  have hG'y : G'.degree y = 2 := by
    have := erase_edge_degree G x y hxy y
    change G'.degree y + (if y = x ∨ y = y then 1 else 0) = G.degree y at this
    simp at this; omega
  have hG'other : ∀ v : V, v ≠ w → v ≠ y → 3 ≤ G'.degree v := by
    obtain ⟨_, w', hw'⟩ := hm.1
    have hww : w' = w := by by_contra hne; have := hw' w (Ne.symm hne); omega
    subst w'
    intro v hvw hvy
    have hd := erase_edge_degree G x y hxy v
    change G'.degree v + (if v = x ∨ v = y then 1 else 0) = G.degree v at hd
    by_cases hvx : v = x
    · subst hvx; simp at hd; omega
    · simp [hvx, hvy] at hd; rw [hd]; exact hw' v hvw
  have hnadj' : ¬ G'.Adj w y := fun h => hnwy h.1
  let H := identify G' w y
  let _ : DecidableRel H.Adj := fun a b => Classical.dec _
  let W : {z : V // z ≠ y} := ⟨w, hwy⟩
  have hnear : Near H := by
    by_cases hcom : ∃ u, G'.Adj w u ∧ G'.Adj y u
    · obtain ⟨u, hwu, hyu⟩ := hcom
      have huy : u ≠ y := (G'.ne_of_adj hyu).symm
      let U : {z : V // z ≠ y} := ⟨u, huy⟩
      have huniq : ∀ z, G'.Adj w z ∧ G'.Adj y z → z = u :=
        fun z hz => unique_common_neighbor hG'free hwy hz.1 hz.2 hwu hyu
      have hWdeg : H.degree W + 1 = G'.degree w + G'.degree y := by
        rw [identify_degree_merged_ge G' hwy]
        have hwnot : w ∉ G'.neighborFinset w ∪ G'.neighborFinset y := by
          simp only [Finset.mem_union, SimpleGraph.mem_neighborFinset, not_or]
          exact ⟨G'.loopless.irrefl w, fun h => hnadj' h.symm⟩
        have hynot : y ∉ (G'.neighborFinset w ∪ G'.neighborFinset y).erase w := by
          simp only [Finset.mem_erase, Finset.mem_union, SimpleGraph.mem_neighborFinset, not_and, not_or]
          intro _; exact ⟨hnadj', G'.loopless.irrefl y⟩
        rw [Finset.erase_eq_of_notMem hynot, Finset.erase_eq_of_notMem hwnot]
        have hinter : G'.neighborFinset w ∩ G'.neighborFinset y = {u} := by
          ext z
          simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
          exact ⟨huniq z, fun hz => hz ▸ ⟨hwu, hyu⟩⟩
        have hcu := Finset.card_union_add_card_inter (G'.neighborFinset w) (G'.neighborFinset y)
        rw [hinter, Finset.card_singleton, G'.card_neighborFinset_eq_degree,
          G'.card_neighborFinset_eq_degree] at hcu
        exact hcu
      have hW3 : 3 ≤ H.degree W := by omega
      refine ⟨⟨W, hW3⟩, ⟨U, fun v hv => ?_⟩⟩
      by_cases hvW : v = W
      · rw [hvW]; exact hW3
      · rw [identify_degree_other_of_not_common G' hwy v (fun h => hvW (Subtype.ext h))
          (fun hc => hv (Subtype.ext (huniq v.1 hc)))]
        exact hG'other v.1 (fun h => hvW (Subtype.ext h)) v.2
    · push Not at hcom
      have hWdeg : H.degree W = G'.degree w + G'.degree y := by
        rw [identify_degree_merged_ge G' hwy]
        have hdisj : Disjoint (G'.neighborFinset w) (G'.neighborFinset y) := by
          rw [Finset.disjoint_left]
          intro u hwu hyu
          exact hcom u ((G'.mem_neighborFinset w u).mp hwu) ((G'.mem_neighborFinset y u).mp hyu)
        have hwnot : w ∉ G'.neighborFinset w ∪ G'.neighborFinset y := by
          simp only [Finset.mem_union, SimpleGraph.mem_neighborFinset, not_or]
          exact ⟨G'.loopless.irrefl w, fun h => hnadj' h.symm⟩
        have hynot : y ∉ (G'.neighborFinset w ∪ G'.neighborFinset y).erase w := by
          simp only [Finset.mem_erase, Finset.mem_union, SimpleGraph.mem_neighborFinset, not_and, not_or]
          intro _; exact ⟨hnadj', G'.loopless.irrefl y⟩
        rw [Finset.erase_eq_of_notMem hynot, Finset.erase_eq_of_notMem hwnot,
          Finset.card_union_of_disjoint hdisj,
          G'.card_neighborFinset_eq_degree, G'.card_neighborFinset_eq_degree]
      have hW3 : 3 ≤ H.degree W := by omega
      refine ⟨⟨W, hW3⟩, ⟨W, fun v hv => ?_⟩⟩
      rw [identify_degree_other_of_not_common G' hwy v (fun h => hv (Subtype.ext h))
        (fun ⟨h1, h2⟩ => hcom v.1 h1 h2)]
      exact hG'other v.1 (fun h => hv (Subtype.ext h)) v.2
  have hpow : HasPower H := hm.2.2.1 _ H (card_sub_lt y) hnear
  exact dyadic_path_of_identify hwy hG'free hpow

/-- NEW (Wave 3, Agent #5): Class H Defect-Neighbor High-Edge Fermat Cycle Theorem.
    If b₁ ∈ N(w) is adjacent to x ∈ V_{>=4}, then G - xb₁ contains a simple w-b₁ path of
    length 2^k (k >= 2), closing with wb₁ to a (2^k + 1)-cycle. -/
theorem class_h_defect_neighbor_high_edge_fermat [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {w b₁ x : V} (hw : G.degree w = 2) (hwb₁ : G.Adj w b₁)
    (hx4 : 4 ≤ G.degree x) (hxb₁ : G.Adj x b₁) :
    ∃ (k : ℕ) (c : (G \ SimpleGraph.edge x b₁).Walk w b₁),
      2 ≤ k ∧ c.IsPath ∧ c.length = 2 ^ k := by
  classical
  let G' := G \ SimpleGraph.edge x b₁
  let _ : DecidableRel G'.Adj := inferInstanceAs (DecidableRel (G \ SimpleGraph.edge x b₁).Adj)
  have hG'free : ¬ HasPower G' := fun h => hm.2.1 (power_mono sdiff_le h)
  have hne : w ≠ b₁ := G.ne_of_adj hwb₁
  have hwx : w ≠ x := by intro h; subst h; omega
  have hxb₁_ne : x ≠ b₁ := G.ne_of_adj hxb₁
  have hntri : ∀ u, ¬ (G'.Adj w u ∧ G'.Adj b₁ u) := by
    rintro u ⟨hwu, hb₁u⟩
    exact class_h_no_defect_triangle_adj_high G hm hw hwb₁ hwu.1 hb₁u.1 hx4 hxb₁.symm
  have hG'other : ∀ v : V, v ≠ w → v ≠ b₁ → 3 ≤ G'.degree v := by
    obtain ⟨_, w', hw'⟩ := hm.1
    have hww : w' = w := by by_contra hne'; have := hw' w (Ne.symm hne'); omega
    subst w'
    intro v hvw hvb₁
    have hd := erase_edge_degree G x b₁ hxb₁ v
    change G'.degree v + (if v = x ∨ v = b₁ then 1 else 0) = G.degree v at hd
    by_cases hvx : v = x
    · subst hvx; simp at hd; omega
    · simp [hvx, hvb₁] at hd; rw [hd]; exact hw' v hvw
  let H := identify G' w b₁
  let _ : DecidableRel H.Adj := fun a b => Classical.dec _
  let W : {z : V // z ≠ b₁} := ⟨w, hne⟩
  let X : {z : V // z ≠ b₁} := ⟨x, hxb₁_ne⟩
  have hXdeg : 3 ≤ H.degree X := by
    rw [identify_degree_other_of_not_common G' hne X hwx.symm (hntri x)]
    exact hG'other x hwx.symm hxb₁_ne
  have hnear : Near H := by
    refine ⟨⟨X, hXdeg⟩, ⟨W, fun v hv => ?_⟩⟩
    rw [identify_degree_other_of_not_common G' hne v (fun h => hv (Subtype.ext h)) (hntri v.1)]
    exact hG'other v.1 (fun h => hv (Subtype.ext h)) v.2
  have hpow : HasPower H := hm.2.2.1 _ H (card_sub_lt b₁) hnear
  exact dyadic_path_of_identify hne hG'free hpow

/-- First Lean 4.36 verification: Defect-Suppression Dyadic Path Theorem (for all 6
    non-defect-triangle one-defect leaves S-T-3, S-N-2, S-N-3, H-T-3, H-N-2, H-N-3). -/
theorem defect_suppression_dyadic_path [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {w b₁ b₂ : V} (hw : G.degree w = 2)
    (hwb₁ : G.Adj w b₁) (hwb₂ : G.Adj w b₂) (hne : b₁ ≠ b₂) (hnadj : ¬ G.Adj b₁ b₂) :
    let G₁ := G.induce {v : V | v ≠ w}
    ∃ (k : ℕ) (p : G₁.Walk ⟨b₁, (G.ne_of_adj hwb₁).symm⟩ ⟨b₂, (G.ne_of_adj hwb₂).symm⟩),
      2 ≤ k ∧ p.IsPath ∧ p.length = 2 ^ k := by
  classical
  let G₁ := G.induce {x : V | x ≠ w}
  have hG₁free : ¬ HasPower G₁ := fun h => hm.2.1 (power_induce G {x : V | x ≠ w} h)
  let B₁ : {x : V // x ≠ w} := ⟨b₁, (G.ne_of_adj hwb₁).symm⟩
  let B₂ : {x : V // x ≠ w} := ⟨b₂, (G.ne_of_adj hwb₂).symm⟩
  have hBne : B₁ ≠ B₂ := fun h => hne (congrArg Subtype.val h)
  have hBnadj : ¬ G₁.Adj B₁ B₂ := hnadj
  have hBnocom : ∀ u : {x : V // x ≠ w}, ¬ (G₁.Adj B₁ u ∧ G₁.Adj B₂ u) := by
    rintro u ⟨h1, h2⟩
    have huw : u.1 = w := unique_common_neighbor hm.2.1 hne h1 h2 hwb₁.symm hwb₂.symm
    exact u.2 huw
  have hB₁deg : G₁.degree B₁ = 2 := by
    have h1 := induce_delete_degree G w B₁
    have h2 := defect_neighbor_cubic G hm hw hwb₁
    have hwb₁' : G.Adj B₁.1 w := hwb₁.symm
    simp only [hwb₁', ↓reduceIte] at h1
    change G₁.degree B₁ + 1 = G.degree b₁ at h1
    omega
  have hB₂deg : G₁.degree B₂ = 2 := by
    have h1 := induce_delete_degree G w B₂
    have h2 := defect_neighbor_cubic G hm hw hwb₂
    have hwb₂' : G.Adj B₂.1 w := hwb₂.symm
    simp only [hwb₂', ↓reduceIte] at h1
    change G₁.degree B₂ + 1 = G.degree b₂ at h1
    omega
  have hG₁other : ∀ v : {x : V // x ≠ w}, v ≠ B₁ → v ≠ B₂ → 3 ≤ G₁.degree v := by
    obtain ⟨_, w', hw'⟩ := hm.1
    have hww : w' = w := by by_contra hne'; have := hw' w (Ne.symm hne'); omega
    subst w'
    intro v hv1 hv2
    have hnw : ¬ G.Adj v.1 w := fun h => by
      rcases deg2_neighbors_eq G hw hwb₁ hwb₂ hne h.symm with h' | h'
      · exact hv1 (Subtype.ext h')
      · exact hv2 (Subtype.ext h')
    have h1 := induce_delete_degree G w v
    simp only [hnw, ↓reduceIte, add_zero] at h1
    change G₁.degree v = G.degree v.1 at h1
    rw [h1]; exact hw' v.1 v.2
  let H := identify G₁ B₁ B₂
  let _ : DecidableRel H.Adj := fun a b => Classical.dec _
  let X : {z : {x : V // x ≠ w} // z ≠ B₂} := ⟨B₁, hBne⟩
  have hXdeg : H.degree X = G₁.degree B₁ + G₁.degree B₂ := by
    rw [identify_degree_merged_ge G₁ hBne]
    have hdisj : Disjoint (G₁.neighborFinset B₁) (G₁.neighborFinset B₂) := by
      rw [Finset.disjoint_left]
      intro u h1 h2
      exact hBnocom u ⟨(G₁.mem_neighborFinset B₁ u).mp h1, (G₁.mem_neighborFinset B₂ u).mp h2⟩
    have h1not : B₁ ∉ G₁.neighborFinset B₁ ∪ G₁.neighborFinset B₂ := by
      simp only [Finset.mem_union, SimpleGraph.mem_neighborFinset, not_or]
      exact ⟨G₁.loopless.irrefl B₁, fun h => hBnadj h.symm⟩
    have h2not : B₂ ∉ (G₁.neighborFinset B₁ ∪ G₁.neighborFinset B₂).erase B₁ := by
      simp only [Finset.mem_erase, Finset.mem_union, SimpleGraph.mem_neighborFinset, not_and, not_or]
      intro _; exact ⟨hBnadj, G₁.loopless.irrefl B₂⟩
    rw [Finset.erase_eq_of_notMem h2not, Finset.erase_eq_of_notMem h1not,
      Finset.card_union_of_disjoint hdisj,
      G₁.card_neighborFinset_eq_degree, G₁.card_neighborFinset_eq_degree]
  have hX3 : 3 ≤ H.degree X := by omega
  have hnear : Near H := by
    refine ⟨⟨X, hX3⟩, ⟨X, fun v hv => ?_⟩⟩
    rw [identify_degree_other_of_not_common G₁ hBne v (fun h => hv (Subtype.ext h)) (hBnocom v.1)]
    exact hG₁other v.1 (fun h => hv (Subtype.ext h)) v.2
  have hcard_lt : Fintype.card {z : {x : V // x ≠ w} // z ≠ B₂} < Fintype.card V := by
    have h1 : Fintype.card {z : {x : V // x ≠ w} // z ≠ B₂} < Fintype.card {x : V // x ≠ w} :=
      card_sub_lt B₂
    have h2 : Fintype.card {x : V // x ≠ w} < Fintype.card V := card_sub_lt w
    omega
  have hpow : HasPower H := hm.2.2.1 _ H hcard_lt hnear
  exact dyadic_path_of_identify hBne hG₁free hpow

/-- NEW (Wave 3, Agent #5): Class H Double-Edge-Deletion Dyadic Path Theorem.
    If b₁ ∈ N(w) is adjacent to x₁ ∈ V_{>=4}, then for EVERY other edge x₂y₂ incident to V_{>=4}
    (with x₁ ≠ x₂ or deg(x₁) >= 5), deleting w, x₁b₁, AND x₂y₂ STILL leaves a simple b₁-b₂ path
    of length 2^k (k >= 2). -/
theorem class_h_double_edge_deletion_path [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {w b₁ b₂ x₁ x₂ y₂ : V} (hw : G.degree w = 2)
    (hwb₁ : G.Adj w b₁) (hwb₂ : G.Adj w b₂) (hne : b₁ ≠ b₂)
    (hx₁4 : 4 ≤ G.degree x₁) (hx₁b₁ : G.Adj x₁ b₁)
    (hx₂4 : 4 ≤ G.degree x₂) (hx₂y₂ : G.Adj x₂ y₂)
    (hdiff : s(x₁, b₁) ≠ s(x₂, y₂))
    (hdeg_compat : x₁ ≠ x₂ ∨ 5 ≤ G.degree x₁) :
    let G₁ := G.induce {v : V | v ≠ w}
    have hx₁w : x₁ ≠ w := by intro h; subst h; omega
    have hx₂w : x₂ ≠ w := by intro h; subst h; omega
    have hy₂w : y₂ ≠ w := by
      intro h; subst h
      have := defect_neighbor_cubic G hm hw hx₂y₂.symm; omega
    let G₂ := (G₁ \ SimpleGraph.edge ⟨x₁, hx₁w⟩ ⟨b₁, (G.ne_of_adj hwb₁).symm⟩) \
                SimpleGraph.edge ⟨x₂, hx₂w⟩ ⟨y₂, hy₂w⟩
    ∃ (k : ℕ) (p : G₂.Walk ⟨b₁, (G.ne_of_adj hwb₁).symm⟩ ⟨b₂, (G.ne_of_adj hwb₂).symm⟩),
      2 ≤ k ∧ p.IsPath ∧ p.length = 2 ^ k := by
  classical
  have hnadj : ¬ G.Adj b₁ b₂ := fun h =>
    class_h_no_defect_triangle_adj_high G hm hw hwb₁ hwb₂ h hx₁4 hx₁b₁.symm
  have hx₁w : x₁ ≠ w := by intro h; subst h; omega
  have hx₂w : x₂ ≠ w := by intro h; subst h; omega
  have hy₂w : y₂ ≠ w := by
    intro h; subst h
    have := defect_neighbor_cubic G hm hw hx₂y₂.symm; omega
  let G₁ := G.induce {x : V | x ≠ w}
  let B₁ : {x : V // x ≠ w} := ⟨b₁, (G.ne_of_adj hwb₁).symm⟩
  let B₂ : {x : V // x ≠ w} := ⟨b₂, (G.ne_of_adj hwb₂).symm⟩
  let X₁ : {x : V // x ≠ w} := ⟨x₁, hx₁w⟩
  let X₂ : {x : V // x ≠ w} := ⟨x₂, hx₂w⟩
  let Y₂ : {x : V // x ≠ w} := ⟨y₂, hy₂w⟩
  let G₁' := G₁ \ SimpleGraph.edge X₁ B₁
  let _ : DecidableRel G₁'.Adj := inferInstanceAs (DecidableRel (G₁ \ SimpleGraph.edge X₁ B₁).Adj)
  let G₂ := G₁' \ SimpleGraph.edge X₂ Y₂
  let _ : DecidableRel G₂.Adj := inferInstanceAs (DecidableRel (G₁' \ SimpleGraph.edge X₂ Y₂).Adj)
  have hG₂free : ¬ HasPower G₂ := fun h =>
    hm.2.1 (power_induce G {x : V | x ≠ w} (power_mono (sdiff_le.trans sdiff_le) h))
  have hBne : B₁ ≠ B₂ := fun h => hne (congrArg Subtype.val h)
  have hBnadj : ¬ G₂.Adj B₁ B₂ := fun h => hnadj h.1.1
  have hBnocom : ∀ u : {x : V // x ≠ w}, ¬ (G₂.Adj B₁ u ∧ G₂.Adj B₂ u) := by
    rintro u ⟨h1, h2⟩
    have huw : u.1 = w := unique_common_neighbor hm.2.1 hne h1.1.1 h2.1.1 hwb₁.symm hwb₂.symm
    exact u.2 huw
  have he1 : G₁.Adj X₁ B₁ := hx₁b₁
  have he2 : G₁'.Adj X₂ Y₂ := by
    refine ⟨hx₂y₂, ?_⟩
    intro hadj
    have hsym := (SimpleGraph.edge_adj X₁ B₁ X₂ Y₂).mp hadj
    rcases hsym.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have h1' : x₂ = x₁ := congrArg Subtype.val h1
      have h2' : y₂ = b₁ := congrArg Subtype.val h2
      exact hdiff (by rw [h1', h2'])
    · have h1' : x₂ = b₁ := congrArg Subtype.val h1
      have h2' : y₂ = x₁ := congrArg Subtype.val h2
      exact hdiff (by rw [h1', h2', Sym2.eq_swap])
  have hG₁'deg : ∀ v : {x : V // x ≠ w},
      G₁'.degree v + (if v = X₁ ∨ v = B₁ then 1 else 0) = G₁.degree v :=
    fun v => erase_edge_degree G₁ X₁ B₁ he1 v
  have hG₂deg : ∀ v : {x : V // x ≠ w},
      G₂.degree v + (if v = X₂ ∨ v = Y₂ then 1 else 0) = G₁'.degree v :=
    fun v => erase_edge_degree G₁' X₂ Y₂ he2 v
  have hdb₁ : G.degree b₁ = 3 := defect_neighbor_cubic G hm hw hwb₁
  have hdb₂ : G.degree b₂ = 3 := defect_neighbor_cubic G hm hw hwb₂
  have hdy₂ : G.degree y₂ = 3 := high_neighbor_cubic G hm hx₂4 hx₂y₂
  have hX₁neB₁ : X₁ ≠ B₁ := G₁.ne_of_adj he1
  have hX₁neB₂ : X₁ ≠ B₂ := by
    intro h; have heq : x₁ = b₂ := congrArg Subtype.val h; rw [heq] at hx₁4; omega
  have hX₂neB₁ : X₂ ≠ B₁ := by
    intro h; have heq : x₂ = b₁ := congrArg Subtype.val h; rw [heq] at hx₂4; omega
  have hX₂neB₂ : X₂ ≠ B₂ := by
    intro h; have heq : x₂ = b₂ := congrArg Subtype.val h; rw [heq] at hx₂4; omega
  have hX₁neY₂ : X₁ ≠ Y₂ := by
    intro h; have heq : x₁ = y₂ := congrArg Subtype.val h; rw [heq] at hx₁4; omega
  have hX₁nw : ¬ G.Adj X₁.1 w := fun h => by
    have := defect_neighbor_cubic G hm hw h.symm; change G.degree x₁ = 3 at this; omega
  have hX₁G₂ : 3 ≤ G₂.degree X₁ := by
    have d1 := induce_delete_degree G w X₁
    simp only [hX₁nw, ↓reduceIte, add_zero] at d1
    change G₁.degree X₁ = G.degree x₁ at d1
    have d2 := hG₁'deg X₁
    simp only [true_or, ↓reduceIte] at d2
    have d3 := hG₂deg X₁
    rcases hdeg_compat with hne12 | hge5
    · have hX12 : X₁ ≠ X₂ := fun h => hne12 (congrArg Subtype.val h)
      simp only [hX12, hX₁neY₂, or_self, ↓reduceIte, add_zero] at d3
      omega
    · by_cases h12 : X₁ = X₂
      · simp only [h12, true_or, ↓reduceIte] at d3; omega
      · simp only [h12, hX₁neY₂, or_self, ↓reduceIte, add_zero] at d3; omega
  have hG₂other : ∀ v : {x : V // x ≠ w}, v ≠ B₁ → v ≠ B₂ → v ≠ Y₂ → 3 ≤ G₂.degree v := by
    obtain ⟨_, w', hw'⟩ := hm.1
    have hww : w' = w := by by_contra hne'; have := hw' w (Ne.symm hne'); omega
    subst w'
    intro v hv1 hv2 hvY
    have hnw : ¬ G.Adj v.1 w := fun h => by
      rcases deg2_neighbors_eq G hw hwb₁ hwb₂ hne h.symm with h' | h'
      · exact hv1 (Subtype.ext h')
      · exact hv2 (Subtype.ext h')
    by_cases hvX₁ : v = X₁
    · rw [hvX₁]; exact hX₁G₂
    · have d1 := induce_delete_degree G w v
      simp only [hnw, ↓reduceIte, add_zero] at d1
      change G₁.degree v = G.degree v.1 at d1
      have d2 := hG₁'deg v
      simp only [hvX₁, hv1, or_self, ↓reduceIte, add_zero] at d2
      have d3 := hG₂deg v
      by_cases hvX₂ : v = X₂
      · rw [hvX₂] at d1 d2 d3 ⊢
        simp only [true_or, ↓reduceIte] at d3
        change G₁.degree X₂ = G.degree x₂ at d1
        omega
      · simp only [hvX₂, hvY, or_self, ↓reduceIte, add_zero] at d3
        rw [d3, d2, d1]; exact hw' v.1 v.2
  let H := identify G₂ B₁ B₂
  let _ : DecidableRel H.Adj := fun a b => Classical.dec _
  let B : {z : {x : V // x ≠ w} // z ≠ B₂} := ⟨B₁, hBne⟩
  let X₁' : {z : {x : V // x ≠ w} // z ≠ B₂} := ⟨X₁, hX₁neB₂⟩
  have hX₁'deg : 3 ≤ H.degree X₁' := by
    rw [identify_degree_other_of_not_common G₂ hBne X₁' hX₁neB₁ (hBnocom X₁)]
    exact hX₁G₂
  have hBdeg : H.degree B = G₂.degree B₁ + G₂.degree B₂ := by
    rw [identify_degree_merged_ge G₂ hBne]
    have hdisj : Disjoint (G₂.neighborFinset B₁) (G₂.neighborFinset B₂) := by
      rw [Finset.disjoint_left]
      intro u h1 h2
      exact hBnocom u ⟨(G₂.mem_neighborFinset B₁ u).mp h1, (G₂.mem_neighborFinset B₂ u).mp h2⟩
    have h1not : B₁ ∉ G₂.neighborFinset B₁ ∪ G₂.neighborFinset B₂ := by
      simp only [Finset.mem_union, SimpleGraph.mem_neighborFinset, not_or]
      exact ⟨G₂.loopless.irrefl B₁, fun h => hBnadj h.symm⟩
    have h2not : B₂ ∉ (G₂.neighborFinset B₁ ∪ G₂.neighborFinset B₂).erase B₁ := by
      simp only [Finset.mem_erase, Finset.mem_union, SimpleGraph.mem_neighborFinset, not_and, not_or]
      intro _; exact ⟨hBnadj, G₂.loopless.irrefl B₂⟩
    rw [Finset.erase_eq_of_notMem h2not, Finset.erase_eq_of_notMem h1not,
      Finset.card_union_of_disjoint hdisj,
      G₂.card_neighborFinset_eq_degree, G₂.card_neighborFinset_eq_degree]
  have hB₁G₁' : G₁'.degree B₁ = 1 := by
    have d1 := induce_delete_degree G w B₁
    have hwb₁' : G.Adj B₁.1 w := hwb₁.symm
    simp only [hwb₁', ↓reduceIte] at d1
    change G₁.degree B₁ + 1 = G.degree b₁ at d1
    have d2 := hG₁'deg B₁
    simp only [or_true, ↓reduceIte] at d2
    omega
  have hB₂G₁' : G₁'.degree B₂ = 2 := by
    have d1 := induce_delete_degree G w B₂
    have hwb₂' : G.Adj B₂.1 w := hwb₂.symm
    simp only [hwb₂', ↓reduceIte] at d1
    change G₁.degree B₂ + 1 = G.degree b₂ at d1
    have d2 := hG₁'deg B₂
    simp only [hX₁neB₂.symm, hBne.symm, or_self, ↓reduceIte, add_zero] at d2
    omega
  have hnear : Near H := by
    refine ⟨⟨X₁', hX₁'deg⟩, ?_⟩
    by_cases hY₂B : Y₂ = B₁ ∨ Y₂ = B₂
    · refine ⟨B, fun v hv => ?_⟩
      rw [identify_degree_other_of_not_common G₂ hBne v (fun h => hv (Subtype.ext h)) (hBnocom v.1)]
      have hv1 : v.1 ≠ B₁ := fun h => hv (Subtype.ext h)
      have hv2 : v.1 ≠ B₂ := v.2
      have hvY : v.1 ≠ Y₂ := by
        rcases hY₂B with h | h
        · rw [h]; exact hv1
        · rw [h]; exact hv2
      exact hG₂other v.1 hv1 hv2 hvY
    · push Not at hY₂B
      have hB3 : 3 ≤ H.degree B := by
        have dB₁ := hG₂deg B₁
        simp only [hX₂neB₁.symm, Ne.symm hY₂B.1, or_self, ↓reduceIte, add_zero] at dB₁
        have dB₂ := hG₂deg B₂
        simp only [hX₂neB₂.symm, Ne.symm hY₂B.2, or_self, ↓reduceIte, add_zero] at dB₂
        omega
      refine ⟨⟨Y₂, hY₂B.2⟩, fun v hv => ?_⟩
      by_cases hvB : v = B
      · rw [hvB]; exact hB3
      · rw [identify_degree_other_of_not_common G₂ hBne v (fun h => hvB (Subtype.ext h)) (hBnocom v.1)]
        exact hG₂other v.1 (fun h => hvB (Subtype.ext h)) v.2 (fun h => hv (Subtype.ext h))
  have hcard_lt : Fintype.card {z : {x : V // x ≠ w} // z ≠ B₂} < Fintype.card V := by
    have h1 : Fintype.card {z : {x : V // x ≠ w} // z ≠ B₂} < Fintype.card {x : V // x ≠ w} :=
      card_sub_lt B₂
    have h2 : Fintype.card {x : V // x ≠ w} < Fintype.card V := card_sub_lt w
    omega
  have hpow : HasPower H := hm.2.2.1 _ H hcard_lt hnear
  exact dyadic_path_of_identify hBne hG₂free hpow

#print axioms class_h_no_defect_triangle_adj_high
#print axioms class_h_defect_to_high_neighbor_dyadic_path
#print axioms class_h_defect_neighbor_high_edge_fermat
#print axioms defect_suppression_dyadic_path
#print axioms class_h_double_edge_deletion_path

end E64ClassH
