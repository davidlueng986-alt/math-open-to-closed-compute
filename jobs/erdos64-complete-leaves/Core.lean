import Shadow

namespace E64Core
open SimpleGraph Erdos64Closure
universe u

-- A minimal near counterexample. Edge minimality is on the SAME
-- carrier, so one may delete any edge if the near condition survives.
def MinimalBad {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop :=
  Near G ∧ ¬HasPower G ∧
  (∀ (W : Type u) (H : SimpleGraph W) [Fintype W] [DecidableRel H.Adj],
    Fintype.card W < Fintype.card V → Near H → HasPower H) ∧
  (∀ (H : SimpleGraph V) [DecidableRel H.Adj], H ≤ G → Near H → H = G)

theorem power_mono {V : Type u} {G H : SimpleGraph V}
    (h : H ≤ G) : HasPower H → HasPower G := by
  rintro ⟨k,v,c,hk,hc,hl⟩
  exact ⟨k,v,c.mapLe h,hk,(Walk.isCycle_mapLe h).mpr hc,by simpa using hl⟩

/-- Order-minimal, then edge-minimal counterexample selection.
No finite bound on the order is assumed. -/
theorem minimal_bad_exists
    (bad : ∃ (V : Type u) (_ : Fintype V) (G : SimpleGraph V)
       (_ : DecidableRel G.Adj), Near G ∧ ¬HasPower G) :
    ∃ (V : Type u) (_ : Fintype V) (G : SimpleGraph V)
       (_ : DecidableRel G.Adj), MinimalBad G := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ (V : Type u) (f : Fintype V) (G : SimpleGraph V)
      (d : DecidableRel G.Adj), @Fintype.card V f = n ∧ @Near V G f d ∧ ¬HasPower G
  have hex : ∃ n, P n := by
    obtain ⟨V,f,G,d,h⟩ := bad
    exact ⟨@Fintype.card V f,V,f,G,d,rfl,h⟩
  obtain ⟨V,f,G,d,hcard,hn,hfree⟩ := Nat.find_spec hex
  let _ : Fintype V := f
  let _ : DecidableRel G.Adj := d
  let Q : ℕ → Prop := fun m =>
    ∃ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      H ≤ G ∧ @Near V H f dH ∧ @Finset.card (Sym2 V) H.edgeFinset = m
  have hQ : ∃ m, Q m := ⟨G.edgeFinset.card,G,d,le_rfl,hn,rfl⟩
  obtain ⟨H,dH,hHG,hnH,hcount⟩ := Nat.find_spec hQ
  let _ : DecidableRel H.Adj := dH
  refine ⟨V,f,H,dH,hnH,fun h => hfree (power_mono hHG h),?_,?_⟩
  · intro W J fW dJ hlt hnJ
    by_contra hJ
    have hp : P (@Fintype.card W fW) :=
      ⟨W,fW,J,dJ,rfl,hnJ,hJ⟩
    have hmin := Nat.find_min' hex hp
    omega
  · intro J dJ hJ hnJ
    by_contra hneq
    have hstrict : J < H := lt_of_le_of_ne hJ hneq
    have hlt : J.edgeFinset.card < H.edgeFinset.card :=
      Finset.card_lt_card (SimpleGraph.edgeFinset_strict_mono hstrict)
    have hjQ : Q J.edgeFinset.card := ⟨J,dJ,hJ.trans hHG,hnJ,rfl⟩
    have hmin := Nat.find_min' hQ hjQ
    omega

theorem no_safe_step {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (h : MinimalBad G) : ¬SafeStep G := by
  rintro ⟨W,H,fw,dh,hlt,hn,ht⟩
  let _ : Fintype W := fw
  let _ : DecidableRel H.Adj := dh
  exact h.2.1 (ht (h.2.2.1 W H hlt hn))

/-- If all except one vertex have large degree, and there are at
least two vertices, the separate high-degree condition follows. -/
theorem near_of_except {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (w : V) (hcard : 2 ≤ Fintype.card V)
    (h : ∀ v, v ≠ w → 3 ≤ G.degree v) : Near G := by
  classical
  have hex : ∃ v : V, v ≠ w := by
    by_contra hh
    have hinj : Function.Injective (fun _ : V => ()) := by
      intro a b _
      have ha : a = w := by by_contra hn; exact hh ⟨a,hn⟩
      have hb : b = w := by by_contra hn; exact hh ⟨b,hn⟩
      exact ha.trans hb.symm
    have hc := Fintype.card_le_of_injective _ hinj
    simp at hc
    omega
  obtain ⟨v,hv⟩ := hex
  exact ⟨⟨v,h v hv⟩,⟨w,h⟩⟩

/-- Delete an edge. Exact degree formula, not a heuristic bound. -/
theorem erase_edge_degree {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) (hab : G.Adj a b)
    (x : V) :
    (G \ SimpleGraph.edge a b).degree x +
      (if x=a ∨ x=b then 1 else 0) = G.degree x := by
  classical
  have hne : a ≠ b := G.ne_of_adj hab
  let H := G \ SimpleGraph.edge a b
  change H.degree x + (if x=a ∨ x=b then 1 else 0) = G.degree x
  by_cases ha : x=a
  · subst x
    have hs : H.neighborFinset a = (G.neighborFinset a).erase b := by
      ext y
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_erase, H,
        SimpleGraph.sdiff_adj, SimpleGraph.edge_adj]
      aesop
    rw [← SimpleGraph.card_neighborFinset_eq_degree,hs]
    simp only [true_or, if_true]
    rw [Finset.card_erase_add_one (G.mem_neighborFinset a b |>.mpr hab),
      SimpleGraph.card_neighborFinset_eq_degree]
  · by_cases hb : x=b
    · subst x
      have hs : H.neighborFinset b = (G.neighborFinset b).erase a := by
        ext y
        simp only [SimpleGraph.mem_neighborFinset, Finset.mem_erase, H,
          SimpleGraph.sdiff_adj, SimpleGraph.edge_adj]
        aesop
      rw [← SimpleGraph.card_neighborFinset_eq_degree,hs]
      simp only [or_true, if_true]
      rw [Finset.card_erase_add_one (G.mem_neighborFinset b a |>.mpr hab.symm),
        SimpleGraph.card_neighborFinset_eq_degree]
    · have hs : H.neighborFinset x = G.neighborFinset x := by
        ext y
        simp [H,SimpleGraph.edge_adj,ha,hb]
      rw [← SimpleGraph.card_neighborFinset_eq_degree,hs,
        SimpleGraph.card_neighborFinset_eq_degree]
      simp [ha,hb]

theorem no_high_when_no_defect {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (hall : ∀ v, 3 ≤ G.degree v) : ∀ v, G.degree v=3 := by
  classical
  intro a
  by_contra hne
  have ha := hall a
  have hpos : 0 < G.degree a := by omega
  obtain ⟨b,hab⟩ := (G.degree_pos_iff_exists_adj a).mp hpos
  let H := G \ SimpleGraph.edge a b
  let _ : DecidableRel H.Adj := inferInstanceAs (DecidableRel (G \ SimpleGraph.edge a b).Adj)
  have hcard : 2 ≤ Fintype.card V := by
    have := G.degree_lt_card_verts a
    omega
  have hn : Near H := by
    apply near_of_except H b hcard
    intro v hv
    have hdeg := erase_edge_degree G a b hab v
    change H.degree v + (if v=a ∨ v=b then 1 else 0) = G.degree v at hdeg
    by_cases hva : v=a
    · subst v
      simp at hdeg
      omega
    · simp [hva,hv] at hdeg
      rw [hdeg]
      exact hall v
  have hEq : H=G := hm.2.2.2 H sdiff_le hn
  have he : H.Adj a b := hEq ▸ hab
  have hno : ¬H.Adj a b := by
    intro h
    have hn := (SimpleGraph.sdiff_adj G (SimpleGraph.edge a b) a b).mp h
    exact hn.2 ((SimpleGraph.edge_adj a b a b).mpr ⟨Or.inl ⟨rfl,rfl⟩, G.ne_of_adj hab⟩)
  exact hno he

/-- All vertices other than the designated removed vertex retain
every neighbor except possibly that vertex. -/
theorem induce_delete_degree {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : V)
    (v : {x : V // x ≠ w}) :
    (G.induce {x | x ≠ w}).degree v + (if G.Adj v.1 w then 1 else 0)
       = G.degree v.1 := by
  classical
  let e : (G.induce {x | x ≠ w}).neighborSet v ≃
      {x : V // G.Adj v.1 x ∧ x ≠ w} :=
    { toFun := fun x => ⟨x.1.1,x.2,x.1.2⟩
      invFun := fun x => ⟨⟨x.1,x.2.2⟩,x.2.1⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  have hc := Fintype.card_congr e
  rw [SimpleGraph.card_neighborSet_eq_degree, Fintype.card_subtype] at hc
  have hs : (Finset.univ.filter (fun x : V => G.Adj v.1 x ∧ x ≠ w))
      = (G.neighborFinset v.1).erase w := by
    ext x
    simp [and_comm]
  rw [hs] at hc
  by_cases h : G.Adj v.1 w
  · rw [if_pos h,hc, ← G.card_neighborFinset_eq_degree]
    exact Finset.card_erase_add_one ((G.mem_neighborFinset v.1 w).mpr h)
  · rw [if_neg h,add_zero,hc,Finset.erase_eq_of_notMem]
    · exact G.card_neighborFinset_eq_degree _
    · exact fun hm => h ((G.mem_neighborFinset v.1 w).mp hm)

theorem power_induce {V : Type u} (G : SimpleGraph V) (S : Set V) :
    HasPower (G.induce S) → HasPower G := by
  rintro ⟨k,v,c,hk,hc,hl⟩
  let f : G.induce S →g G := ⟨Subtype.val,fun h => h⟩
  exact ⟨k,v.val,c.map f,hk,(Walk.isCycle_map_iff_of_injective Subtype.val_injective).mpr hc,
    by simpa using hl⟩

/-- Eliminate the two terminal defect cases 0 and 1. -/
theorem no_small_defect {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G) :
    ∀ w, 2 ≤ G.degree w := by
  classical
  intro w
  by_contra hbad
  have hsmall : G.degree w ≤ 1 := by omega
  obtain ⟨⟨a,ha⟩,⟨r,hr⟩⟩ := hm.1
  have hrw : r=w := by
    by_contra h
    have := hr w (Ne.symm h)
    omega
  subst r
  let W := {x : V // x ≠ w}
  let H := G.induce {x | x ≠ w}
  let _ : DecidableRel H.Adj := inferInstanceAs (DecidableRel (G.induce {x | x ≠ w}).Adj)
  have haW : a≠w := by
    intro h
    subst a
    omega
  have hV : 4 ≤ Fintype.card V := by have := G.degree_lt_card_verts a; omega
  have hW : Fintype.card W + 1 = Fintype.card V := by
    rw [Fintype.card_subtype, show (Finset.univ.filter (fun x : V => x ≠ w)) = Finset.univ.erase w by ext x; simp]
    exact Finset.card_erase_add_one (Finset.mem_univ w)
  have hW2 : 2 ≤ Fintype.card ↑({x : V | x ≠ w} : Set V) := by
    have he : Fintype.card ↑({x : V | x ≠ w} : Set V) = Fintype.card W :=
      Fintype.card_congr (Equiv.refl _)
    omega
  have hnear : Near H := by
    by_cases hz : G.degree w=0
    · apply near_of_except H (⟨a,haW⟩ : W) hW2
      intro v _
      have hv := hr v.val v.property
      have hna : ¬G.Adj v.val w := by
        intro he
        have := he.degree_pos_right
        omega
      have hd := induce_delete_degree G w v
      change H.degree v + (if G.Adj v.val w then 1 else 0) = G.degree v.val at hd
      simp [hna] at hd
      omega
    · have h1 : G.degree w=1 := by omega
      obtain ⟨b,hwb,huniq⟩ := (G.degree_eq_one_iff_existsUnique_adj (v := w)).mp h1
      have hb : b≠w := (G.ne_of_adj hwb).symm
      apply near_of_except H (⟨b,hb⟩ : W) hW2
      intro v hv
      have hnv : v.val ≠ b := fun h => hv (Subtype.ext h)
      have hna : ¬G.Adj v.val w := fun h => hnv (huniq v.val h.symm)
      have h0 := hr v.val v.property
      have hd := induce_delete_degree G w v
      change H.degree v + (if G.Adj v.val w then 1 else 0) = G.degree v.val at hd
      simp [hna] at hd
      omega
  have hpow : HasPower H := hm.2.2.1 W H (by omega) hnear
  exact hm.2.1 (power_induce G _ hpow)

/-- If a near counterexample is minimal, the original three degree
classes are exhaustive. This proves the actual graph classification. -/
theorem degree_partition {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hm : MinimalBad G) :
    (∀ v, G.degree v=3) ∨
    (∃ w, G.degree w=2 ∧ ∀ v, v≠w → G.degree v=3) ∨
    (∃ w, G.degree w=2 ∧ (∀ v, v≠w → 3≤G.degree v) ∧ ∃ a, 4≤G.degree a) := by
  by_cases h : ∀ v, 3≤G.degree v
  · exact Or.inl (no_high_when_no_defect G hm h)
  · push Not at h
    obtain ⟨w,hw⟩ := h
    have hw2 := no_small_defect G hm w
    have he : G.degree w=2 := by omega
    obtain ⟨_,r,hr⟩ := hm.1
    have hrw : r=w := by
      by_contra hne
      have := hr w (Ne.symm hne)
      omega
    subst r
    by_cases hh : ∃ a, 4≤G.degree a
    · exact Or.inr (Or.inr ⟨w,he,hr,hh⟩)
    · right; left
      refine ⟨w,he,?_⟩
      intro v hv
      have h1 := hr v hv
      have h2 : ¬4≤G.degree v := fun h => hh ⟨v,h⟩
      omega

/-- Closure from a genuinely exhaustive exclusion of minimal Near
counterexamples. This is a logical assembler only; the exclusion is
an explicit argument, not proved by this declaration. -/
theorem near_from_core_exclusion
    (hex : ∀ (V : Type u) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
      MinimalBad G → False) :
    ∀ (V : Type u) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
      Near G → HasPower G := by
  intro V G f d hn
  by_contra h
  obtain ⟨W,fw,H,dh,hm⟩ := minimal_bad_exists
    (⟨V,f,G,d,hn,h⟩ : ∃ (V : Type u) (_ : Fintype V) (G : SimpleGraph V)
       (_ : DecidableRel G.Adj), Near G ∧ ¬HasPower G)
  exact @hex W H fw dh hm

#print axioms minimal_bad_exists
#print axioms no_safe_step
#print axioms erase_edge_degree
#print axioms no_high_when_no_defect
#print axioms induce_delete_degree
#print axioms no_small_defect
#print axioms degree_partition
#print axioms near_from_core_exclusion
end E64Core

