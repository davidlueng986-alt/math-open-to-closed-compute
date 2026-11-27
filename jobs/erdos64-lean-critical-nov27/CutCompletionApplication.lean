import MinimalCutCompletion
import ConnectivityAndCuts
import CutBoundaryWeapons

namespace E64MinimalCut
open SimpleGraph Erdos64Closure E64Core E64Leaves
universe u

/-- A SmallCut witness can always be chosen inclusion-minimal. This is
well-founded minimization, not a finite-order restriction or enumeration. -/
theorem select_minimal_two_cut {V : Type u} [Fintype V]
    (G : SimpleGraph V) (hcut : SmallCut G 2) :
    ∃ A : Set V, 2 ≤ Nat.card A ∧ 2 ≤ Nat.card (Aᶜ : Set V) ∧
      Nat.card (Boundary G A) ≤ 2 ∧
      ∀ T : Set V, T ⊆ A → T ≠ A →
        2 ≤ Nat.card T → 2 ≤ Nat.card (Tᶜ : Set V) →
        Nat.card (Boundary G T) ≤ 2 → False := by
  classical
  let P : ℕ → Prop := fun n => ∃ A : Set V,
    2 ≤ Nat.card A ∧ 2 ≤ Nat.card (Aᶜ : Set V) ∧
    Nat.card (Boundary G A) ≤ 2 ∧ Nat.card A = n
  have hex : ∃ n, P n := by
    obtain ⟨A, hA, hAc, hB⟩ := hcut
    exact ⟨Nat.card A, A, hA, hAc, hB, rfl⟩
  obtain ⟨A, hA, hAc, hB, hN⟩ := Nat.find_spec hex
  refine ⟨A, hA, hAc, hB, ?_⟩
  intro T hTA hne hT hTc hBT
  have hp : P (Nat.card T) := ⟨T, hT, hTc, hBT, rfl⟩
  have hmin := Nat.find_min' hex hp
  have hlt : Nat.card T < Nat.card A := by
    let f : T → A := fun z => ⟨z.1, hTA z.2⟩
    have hf : Function.Injective f := by
      intro p q h
      exact Subtype.ext (congrArg (fun z : A => z.1) h)
    have hns : ¬ Function.Surjective f := by
      intro hs
      apply hne
      apply Set.Subset.antisymm hTA
      intro z hz
      obtain ⟨t, ht⟩ := hs ⟨z, hz⟩
      have hv : t.1 = z := congrArg (fun q : A => q.1) ht
      exact hv ▸ t.2
    simpa only [Nat.card_eq_fintype_card] using
      Fintype.card_lt_of_injective_not_surjective f hf hns
  omega

/-- Every cubic MinimalBad graph in either low2 leaf has a genuinely
smaller cubic three-edge-connected completion, and all of that completion's
power cycles are forced to use the new edge. -/
theorem cubic_minimal_bad_two_cut_normal_form
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hm : MinimalBad G) (hG : Cubic G) (hcutG : SmallCut G 2) :
    ∃ (A : Set V) (a b : A) (x y : V),
      2 ≤ Nat.card A ∧ 2 ≤ Nat.card (Aᶜ : Set V) ∧
      Nat.card (Boundary G A) = 2 ∧
      a ≠ b ∧ x ∉ A ∧ y ∉ A ∧ x ≠ y ∧
      G.Adj a.1 x ∧ G.Adj b.1 y ∧
      (∀ z : A, ∀ t : V, t ∉ A → G.Adj z.1 t →
        (z = a ∧ t = x) ∨ (z = b ∧ t = y)) ∧
      SideMinimal G A ∧ ¬G.Adj a.1 b.1 ∧
      (∀ z : A, Nat.card ((Completion G A a b).neighborSet z) = 3) ∧
      (∀ S : Set A, S.Nonempty → Sᶜ.Nonempty →
        3 ≤ Nat.card (Boundary (Completion G A a b) S)) ∧
      HasPower (Completion G A a b) ∧ ¬HasPower (G.induce A) := by
  classical
  obtain ⟨A, hA, hAc, hB, hmin⟩ := select_minimal_two_cut G hcutG
  have hAne : A.Nonempty := by
    by_contra h
    have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    simp [he] at hA
  have hAcne : (Aᶜ : Set V).Nonempty := by
    by_contra h
    have he : (Aᶜ : Set V) = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    simp [he] at hAc
  have hlower : 2 ≤ Nat.card (Boundary G A) := by
    have hs : A.toFinset.Nonempty := by
      obtain ⟨z, hz⟩ := hAne
      exact ⟨z, by simpa using hz⟩
    have hsc : (A.toFinset)ᶜ.Nonempty := by
      obtain ⟨z, hz⟩ := hAcne
      exact ⟨z, by simpa using hz⟩
    have hh := E64Wave2Conn.minimal_bad_two_edge_connected G hm A.toFinset hs hsc
    simpa only [Boundary, Nat.card_eq_fintype_card, Fintype.card_subtype,
      Set.mem_toFinset] using hh
  have hcard : Nat.card (Boundary G A) = 2 := by omega
  have hU : (Finset.univ : Finset (Boundary G A)).card = 2 := by
    rw [Finset.card_univ]
    simpa only [Nat.card_eq_fintype_card] using hcard
  obtain ⟨p, q, _, hu⟩ := Finset.card_eq_two.mp hU
  let a : A := ⟨p.1.1, p.2.1⟩
  let b : A := ⟨q.1.1, q.2.1⟩
  let x := p.1.2
  let y := q.1.2
  have hx : x ∉ A := p.2.2.1
  have hy : y ∉ A := q.2.2.1
  have hax : G.Adj a.1 x := p.2.2.2
  have hby : G.Adj b.1 y := q.2.2.2
  have hcut : ∀ z : A, ∀ t : V, t ∉ A → G.Adj z.1 t →
      (z = a ∧ t = x) ∨ (z = b ∧ t = y) := by
    intro z t ht hzt
    let e : Boundary G A := ⟨(z.1, t), z.2, ht, hzt⟩
    have he : e = p ∨ e = q := by
      have hh : e ∈ (Finset.univ : Finset (Boundary G A)) := Finset.mem_univ e
      rw [hu] at hh
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hh
    rcases he with he | he
    · exact Or.inl ⟨Subtype.ext (congrArg (fun r : Boundary G A => r.1.1) he),
        congrArg (fun r : Boundary G A => r.1.2) he⟩
    · exact Or.inr ⟨Subtype.ext (congrArg (fun r : Boundary G A => r.1.1) he),
        congrArg (fun r : Boundary G A => r.1.2) he⟩
  have hA2 : 2 ≤ Fintype.card A := by
    simpa only [Nat.card_eq_fintype_card] using hA
  have hab : a ≠ b :=
    (E64CutBoundary.wfree_2cut_matching_and_cubic_boundary G hm A hA2 ⟨x, hx⟩
      (fun z => (hG z.1).ge) a b x y hcut).1
  let a' : (Aᶜ : Set V) := ⟨x, hx⟩
  let b' : (Aᶜ : Set V) := ⟨y, hy⟩
  have hcutc : ∀ z : (Aᶜ : Set V), ∀ t : V, t ∉ (Aᶜ : Set V) → G.Adj z.1 t →
      (z = a' ∧ t = a.1) ∨ (z = b' ∧ t = b.1) := by
    intro z t ht hzt
    have htA : t ∈ A := by simpa using ht
    rcases hcut ⟨t, htA⟩ z.1 z.2 hzt.symm with ⟨he, hz⟩ | ⟨he, hz⟩
    · exact Or.inl ⟨Subtype.ext hz, congrArg Subtype.val he⟩
    · exact Or.inr ⟨Subtype.ext hz, congrArg Subtype.val he⟩
  have hAc2 : 2 ≤ Fintype.card (Aᶜ : Set V) := by
    simpa only [Nat.card_eq_fintype_card] using hAc
  have hxy : x ≠ y := by
    have hab' :=
      (E64CutBoundary.wfree_2cut_matching_and_cubic_boundary G hm (Aᶜ : Set V)
        hAc2 ⟨a.1, by simpa using a.2⟩ (fun z => (hG z.1).ge) a' b' a.1 b.1 hcutc).1
    intro h
    exact hab' (Subtype.ext h)
  have hsm : SideMinimal G A := side_minimal_of_nontrivial_minimal G hG A hAc hmin
  obtain ⟨hnadj, hcubic, hthree⟩ :=
    minimal_cut_completion G hG A a b hab x y hx hy hax hby hcut hsm
  let H := Completion G A a b
  let _ : DecidableRel H.Adj := Classical.decRel _
  have hdegree : ∀ z : A, H.degree z = 3 := hcubic
  have hnc : ∀ z : A, Nat.card (H.neighborSet z) = 3 := by
    intro z
    rw [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree]
    exact hdegree z
  have hn : Near H := ⟨⟨a, (hdegree a).ge⟩, ⟨a, fun z _ => (hdegree z).ge⟩⟩
  have hsmall : Fintype.card A < Fintype.card V := by
    apply Fintype.card_lt_of_injective_not_surjective
      (fun z : A => z.1) Subtype.val_injective
    intro hs
    obtain ⟨z, hz⟩ := hs x
    exact hx (hz ▸ z.2)
  have hpower : HasPower H := hm.2.2.1 A H hsmall hn
  have hfree : ¬HasPower (G.induce A) := fun hp => hm.2.1 (power_induce G A hp)
  exact ⟨A, a, b, x, y, hA, hAc, hcard, hab, hx, hy, hxy, hax, hby,
    hcut, hsm, hnadj, hnc, hthree, hpower, hfree⟩

#print axioms select_minimal_two_cut
#print axioms cubic_minimal_bad_two_cut_normal_form

end E64MinimalCut


