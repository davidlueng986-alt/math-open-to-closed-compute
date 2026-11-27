import MinimalCutCompletion
import ConnectivityAndCuts
import IdentificationAndContraction
import CutBoundaryWeapons

/-!
# Erdős Problem #64 — Wave 7 Agent #5: Universal 6-Leaf `*-2` Normal Form,
# High-Edge Avoidance, Port-Spectrum Forcing, and Official DAG Closure Gates

Generalizes `CutCompletionApplication.lean` (previously cubic-only: `C-T-2`, `C-N-2`)
to **ALL SIX** open `*-2` terminal leaves of the official 26-leaf DAG (`C-T-2`, `C-N-2`,
`S-T-2`, `S-N-2`, `H-T-2`, `H-N-2`), adding:
1. Universal $w$-free minimal two-cut normal form (`wfree_minimal_bad_two_cut_normal_form`)
   working with arbitrary high-degree vertices ($V_{\ge 4}$) and a degree-2 defect $w$.
2. High-edge avoidance & $V_3$-localization of all hitting edges in the completed side $H_A$
   (`wfree_two_cut_high_edge_avoided`, `wfree_two_cut_hitting_edges_in_V3`).
3. Multi-operation port-spectrum forcing ($2^r - 1 \in P_A$ and $2^t \in P_A$) and
   cross-side Fermat disjointness (`two_cut_no_matching_port_sum_pow2`, `two_cut_fermat_disjoint`).
4. Exact 6-leaf closure gates wired directly to `E64Leaves.Exclude`:
   - `exclude_all_six_low2_of_no_cubic_hitting_edge_3ec`
   - `exclude_all_six_low2_of_port_sync`

All 14 theorems are all-order, sorry-free, zero-`native_decide`, and depend solely on
standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace E64Wave7Agent5
open SimpleGraph Erdos64Closure E64Core E64Leaves Erdos64Descent Erdos64Paired
open E64MinimalCut E64Wave2Conn E64Wave2Ident E64CutBoundary
open scoped Sym2
universe u

/-! ## Pillar 1: Universal `w`-Free Minimal 2-Cut Normal Form (All 6 `*-2` Leaves) -/

/-- In ANY `MinimalBad G` with `SmallCut G 2` (cubic, subcubic-defect, or high-defect),
there exists a `w`-free nontrivial 2-cut side `A` of minimum cardinality. -/
theorem select_minimal_wfree_two_cut {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hm : MinimalBad G) (hcut : SmallCut G 2) :
    ∃ A : Set V,
      2 ≤ Nat.card A ∧ 2 ≤ Nat.card (Aᶜ : Set V) ∧
      Nat.card (Boundary G A) ≤ 2 ∧
      (∀ v : A, 3 ≤ G.degree v.1) ∧
      ∀ T : Set V, T ⊆ A → T ≠ A →
        2 ≤ Nat.card T → 2 ≤ Nat.card (Tᶜ : Set V) →
        Nat.card (Boundary G T) ≤ 2 → False := by
  classical
  obtain ⟨_, w, hw⟩ := hm.1
  let P : ℕ → Prop := fun n => ∃ A : Set V,
    2 ≤ Nat.card A ∧ 2 ≤ Nat.card (Aᶜ : Set V) ∧
    Nat.card (Boundary G A) ≤ 2 ∧ (∀ v : A, 3 ≤ G.degree v.1) ∧ Nat.card A = n
  have hex : ∃ n, P n := by
    obtain ⟨S, hS, hSc, hB⟩ := hcut
    by_cases hwS : w ∈ S
    · refine ⟨Nat.card (Sᶜ : Set V), Sᶜ, hSc, ?_, ?_, ?_, rfl⟩
      · simpa using hS
      · let e : Boundary G Sᶜ ≃ Boundary G S :=
          { toFun := fun p => ⟨(p.1.2, p.1.1), by simpa using p.2.2.1, p.2.1, p.2.2.2.symm⟩
            invFun := fun p => ⟨(p.1.2, p.1.1), p.2.2.1, by simpa using p.2.1, p.2.2.2.symm⟩
            left_inv := fun p => Subtype.ext rfl
            right_inv := fun p => Subtype.ext rfl }
        simpa only [Nat.card_congr e] using hB
      · intro v
        exact hw v.1 (fun h => v.2 (h ▸ hwS))
    · exact ⟨Nat.card S, S, hS, hSc, hB, fun v => hw v.1 (fun h => hwS (h ▸ v.2)), rfl⟩
  obtain ⟨A, hA, hAc, hB, hwfree, hN⟩ := Nat.find_spec hex
  refine ⟨A, hA, hAc, hB, hwfree, ?_⟩
  intro T hTA hne hT hTc hBT
  have hTwfree : ∀ v : T, 3 ≤ G.degree v.1 := fun v => hwfree ⟨v.1, hTA v.2⟩
  have hp : P (Nat.card T) := ⟨T, hT, hTc, hBT, hTwfree, rfl⟩
  have hmin := Nat.find_min' hex hp
  have hlt : Nat.card T < Nat.card A := by
    let f : T → A := fun z => ⟨z.1, hTA z.2⟩
    have hf : Function.Injective f := fun p q h =>
      Subtype.ext (congrArg (fun z : A => z.1) h)
    have hns : ¬ Function.Surjective f := by
      intro hs
      apply hne
      apply Set.Subset.antisymm hTA
      intro z hz
      obtain ⟨t, ht⟩ := hs ⟨z, hz⟩
      have htz : t.1 = z := congrArg Subtype.val ht
      exact htz ▸ t.2
    simpa only [Nat.card_eq_fintype_card] using
      Fintype.card_lt_of_injective_not_surjective f hf hns
  omega

/-- Inclusion-minimality among nontrivial 2-cuts on a `w`-free side `A` implies `SideMinimal G A`
(singletons have degree `≥ 3`). -/
theorem wfree_side_minimal {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Set V) (hAc : 2 ≤ Nat.card (Aᶜ : Set V))
    (hwfree : ∀ v : A, 3 ≤ G.degree v.1)
    (hmin : ∀ T : Set V, T ⊆ A → T ≠ A →
      2 ≤ Nat.card T → 2 ≤ Nat.card (Tᶜ : Set V) →
      Nat.card (Boundary G T) ≤ 2 → False) : SideMinimal G A := by
  classical
  intro T hTA hT hne
  by_contra hn
  have hc : Nat.card (Boundary G T) ≤ 2 := by omega
  have hTc : 2 ≤ Nat.card (Tᶜ : Set V) := by
    let f : (Aᶜ : Set V) → (Tᶜ : Set V) := fun z => ⟨z.1, fun hz => z.2 (hTA hz)⟩
    have hf : Function.Injective f := fun p q h =>
      Subtype.ext (congrArg (fun z : (Tᶜ : Set V) => z.1) h)
    exact hAc.trans (Nat.card_le_card_of_injective f hf)
  by_cases hT2 : 2 ≤ Nat.card T
  · exact hmin T hTA hne hT2 hTc hc
  obtain ⟨z, hz⟩ := hT
  have huniq : ∀ v ∈ T, v = z := by
    intro v hv
    by_contra hvz
    let f : Bool → T := fun b => if b then ⟨v, hv⟩ else ⟨z, hz⟩
    have hf : Function.Injective f := by
      intro p q hpq
      cases p <;> cases q <;> simp_all [f, Subtype.ext_iff]
    have hcard := Nat.card_le_card_of_injective f hf
    have hbool : Nat.card Bool = 2 := by rw [Nat.card_eq_fintype_card]; decide
    omega
  have hTsing : T = {z} := by
    ext v
    constructor
    · intro hv; exact huniq v hv
    · intro hv; exact (show v = z from hv).symm ▸ hz
  rw [hTsing, boundary_singleton_card] at hc
  have hdz : 3 ≤ G.degree z := hwfree ⟨z, hTA hz⟩
  omega

private theorem deg3_third_unique {V : Type u} [Fintype V] [DecidableEq V]
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

/-- On a `SideMinimal` `w`-free side `A`, the two cubic ports `a, b` cannot be adjacent,
even when `A` contains vertices of degree `≥ 4`. -/
theorem wfree_minimal_side_ports_nonadjacent {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Set V) (a b : A) (hab : a ≠ b) (x y : V)
    (hx : x ∉ A) (hy : y ∉ A) (hax : G.Adj a.1 x) (hby : G.Adj b.1 y)
    (hda : G.degree a.1 = 3) (hdb : G.degree b.1 = 3)
    (hcut : ∀ z : A, ∀ t : V, t ∉ A → G.Adj z.1 t →
      (z = a ∧ t = x) ∨ (z = b ∧ t = y))
    (hmin : SideMinimal G A) : ¬ G.Adj a.1 b.1 := by
  classical
  intro hadj
  have habv : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
  let T : Set V := {z | z ∈ A ∧ z ≠ a.1 ∧ z ≠ b.1}
  have hTsub : T ⊆ A := fun z hz => hz.1
  have hTne : T.Nonempty := by
    by_contra hn
    have hs : G.neighborFinset a.1 ⊆ {b.1, x} := by
      intro z hz
      have haz := (G.mem_neighborFinset a.1 z).mp hz
      by_cases hzA : z ∈ A
      · by_cases hzb : z = b.1
        · simp [hzb]
        · have hza : z ≠ a.1 := (G.ne_of_adj haz).symm
          exact False.elim (hn ⟨z, hzA, hza, hzb⟩)
      · rcases hcut a z hzA haz with ⟨_, rfl⟩ | ⟨ha, _⟩
        · simp
        · exact False.elim (hab ha)
    have hc := Finset.card_le_card hs
    have hb_x : b.1 ≠ x := fun h => hx (h ▸ b.2)
    rw [G.card_neighborFinset_eq_degree, hda] at hc
    have hp : ({b.1, x} : Finset V).card = 2 := by simp [hb_x]
    omega
  have hTproper : T ≠ A := by
    intro h
    have haT : a.1 ∈ T := h.symm ▸ a.2
    exact haT.2.1 rfl
  have hend (e : Boundary G T) : e.1.2 = a.1 ∨ e.1.2 = b.1 := by
    by_cases hEA : e.1.2 ∈ A
    · by_contra h
      exact e.2.2.1 ⟨hEA, fun h1 => h (Or.inl h1), fun h2 => h (Or.inr h2)⟩
    · rcases hcut ⟨e.1.1, e.2.1.1⟩ e.1.2 hEA e.2.2.2 with ⟨h, _⟩ | ⟨h, _⟩
      · exact False.elim (e.2.1.2.1 (congrArg Subtype.val h))
      · exact False.elim (e.2.1.2.2 (congrArg Subtype.val h))
  let f : Boundary G T → Bool := fun e => if e.1.2 = a.1 then true else false
  have hf : Function.Injective f := by
    intro p q hpq
    have hends : p.1.2 = q.1.2 := by
      rcases hend p with hp | hp <;> rcases hend q with hq | hq
      · exact hp.trans hq.symm
      · simp [f, hp, hq, habv.symm] at hpq
      · simp [f, hp, hq, habv.symm] at hpq
      · exact hp.trans hq.symm
    apply Subtype.ext
    apply Prod.ext
    · rcases hend p with hp | hp
      · have hq : q.1.2 = a.1 := hends.symm.trans hp
        apply deg3_third_unique G hda hadj hax (fun h => hx (h ▸ b.2))
        · simpa [hp] using p.2.2.2.symm
        · simpa [hq] using q.2.2.2.symm
        · exact p.2.1.2.2
        · exact fun h => hx (h ▸ p.2.1.1)
        · exact q.2.1.2.2
        · exact fun h => hx (h ▸ q.2.1.1)
      · have hq : q.1.2 = b.1 := hends.symm.trans hp
        apply deg3_third_unique G hdb hadj.symm hby (fun h => hy (h ▸ a.2))
        · simpa [hp] using p.2.2.2.symm
        · simpa [hq] using q.2.2.2.symm
        · exact p.2.1.2.1
        · exact fun h => hy (h ▸ p.2.1.1)
        · exact q.2.1.2.1
        · exact fun h => hy (h ▸ q.2.1.1)
    · exact hends
  have hc := Nat.card_le_card_of_injective f hf
  have hb : Nat.card Bool = 2 := by rw [Nat.card_eq_fintype_card]; decide
  have hl := hmin T hTsub hTne hTproper
  omega

private theorem induce_degree_add_out_local {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Set V) [DecidablePred (· ∈ A)]
    [DecidableRel (G.induce A).Adj] (v : A) :
    (G.induce A).degree v + ((G.neighborFinset v.1).filter (fun x => x ∉ A)).card =
      G.degree v.1 := by
  classical
  let e : G.neighborSet v.1 ≃
      (G.induce A).neighborSet v ⊕ {x : V // x ∈ (G.neighborFinset v.1).filter (fun x => x ∉ A)} :=
    { toFun := fun z =>
        if h : z.1 ∈ A then Sum.inl ⟨⟨z.1, h⟩, z.2⟩
        else Sum.inr ⟨z.1, Finset.mem_filter.mpr ⟨(G.mem_neighborFinset v.1 z.1).mpr z.2, h⟩⟩
      invFun := Sum.elim (fun z => ⟨z.1.1, z.2⟩)
        (fun z => ⟨z.1, (G.mem_neighborFinset v.1 z.1).mp (Finset.mem_filter.mp z.2).1⟩)
      left_inv := fun z => by by_cases h : z.1 ∈ A <;> simp [h]
      right_inv := by
        rintro (z | z)
        · simp [z.1.2]
        · have hn : z.1 ∉ A := (Finset.mem_filter.mp z.2).2
          simp [hn] }
  have hc := Fintype.card_congr e
  rw [SimpleGraph.card_neighborSet_eq_degree, Fintype.card_sum,
    SimpleGraph.card_neighborSet_eq_degree, Fintype.card_coe] at hc
  exact hc.symm

/-- Exact vertex-by-vertex degree preservation in `Completion G A a b` (without assuming `Cubic G`):
every vertex `z : A` has the exact same degree in `Completion G A a b` as in `G`. -/
theorem wfree_completion_degrees {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Set V) (a b : A) (hab : a ≠ b) (x y : V)
    (hx : x ∉ A) (hy : y ∉ A) (hax : G.Adj a.1 x) (hby : G.Adj b.1 y)
    (hcut : ∀ z : A, ∀ t : V, t ∉ A → G.Adj z.1 t →
      (z = a ∧ t = x) ∨ (z = b ∧ t = y))
    (hnadj : ¬ G.Adj a.1 b.1) (z : A) :
    Nat.card ((Completion G A a b).neighborSet z) = G.degree z.1 := by
  classical
  let K := G.induce A
  let H := Completion G A a b
  have hout_a : ((G.neighborFinset a.1).filter (fun t => t ∉ A)) = {x} := by
    ext t
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
    constructor
    · rintro ⟨hat, ht⟩
      rcases hcut a t ht hat with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · exact False.elim (hab h)
    · rintro rfl; exact ⟨hax, hx⟩
  have hout_b : ((G.neighborFinset b.1).filter (fun t => t ∉ A)) = {y} := by
    ext t
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
    constructor
    · rintro ⟨hbt, ht⟩
      rcases hcut b t ht hbt with ⟨h, _⟩ | ⟨_, h⟩
      · exact False.elim (hab h.symm)
      · exact h
    · rintro rfl; exact ⟨hby, hy⟩
  by_cases hza : z = a
  · rw [hza]
    have hd := induce_degree_add_out_local G A a
    rw [hout_a, Finset.card_singleton] at hd
    have ha := degree_add_new_edge_left K a b hab hnadj
    have ha' : Nat.card (H.neighborSet a) = K.degree a + 1 := by
      rw [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree]
      convert ha; rfl
    exact ha'.trans hd
  by_cases hzb : z = b
  · rw [hzb]
    have hd := induce_degree_add_out_local G A b
    rw [hout_b, Finset.card_singleton] at hd
    have hb := degree_add_new_edge_right K a b hab hnadj
    have hb' : Nat.card (H.neighborSet b) = K.degree b + 1 := by
      rw [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree]
      convert hb; rfl
    exact hb'.trans hd
  have hout : ((G.neighborFinset z.1).filter (fun t => t ∉ A)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro t ht hn
    rcases hcut z t hn ((G.mem_neighborFinset z.1 t).mp ht) with ⟨h, _⟩ | ⟨h, _⟩
    · exact hza h
    · exact hzb h
  have hd := induce_degree_add_out_local G A z
  rw [hout, Finset.card_empty, add_zero] at hd
  let e : H.neighborSet z ≃ K.neighborSet z :=
    { toFun := fun t => ⟨t.1, by
        rcases t.2 with h | h
        · exact h
        · rcases ((SimpleGraph.edge_adj a b z t.1).mp h).1 with ⟨hza', _⟩ | ⟨hzb', _⟩
          · exact False.elim (hza hza')
          · exact False.elim (hzb hzb')⟩
      invFun := fun t => ⟨t.1, Or.inl t.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have heq : Nat.card (H.neighborSet z) = Nat.card (K.neighborSet z) := Nat.card_congr e
  have hKdeg : Nat.card (K.neighborSet z) = G.degree z.1 := by
    rw [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree]
    exact hd
  exact heq.trans hKdeg

/-- **Universal 6-Leaf `*-2` Normal Form** (`C-T-2`, `C-N-2`, `S-T-2`, `S-N-2`, `H-T-2`, `H-N-2`):
Every `MinimalBad G` with `SmallCut G 2` admits a strictly smaller, 3-edge-connected,
`δ ≥ 3` completion `H_A = G[A] + ab` whose virtual edge `ab` has both endpoints of degree 3,
satisfies `HasPower H_A`, and `¬HasPower (G.induce A)`. -/
theorem wfree_minimal_bad_two_cut_normal_form
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hm : MinimalBad G) (hcutG : SmallCut G 2) :
    ∃ (A : Set V) (a b : A) (x y : V),
      2 ≤ Nat.card A ∧ 2 ≤ Nat.card (Aᶜ : Set V) ∧
      Nat.card (Boundary G A) = 2 ∧
      (∀ v : A, 3 ≤ G.degree v.1) ∧
      a ≠ b ∧ x ∉ A ∧ y ∉ A ∧ x ≠ y ∧
      G.Adj a.1 x ∧ G.Adj b.1 y ∧
      G.degree a.1 = 3 ∧ G.degree b.1 = 3 ∧
      (∀ z : A, ∀ t : V, t ∉ A → G.Adj z.1 t →
        (z = a ∧ t = x) ∨ (z = b ∧ t = y)) ∧
      SideMinimal G A ∧ ¬G.Adj a.1 b.1 ∧
      (∀ z : A, Nat.card ((Completion G A a b).neighborSet z) = G.degree z.1) ∧
      (∀ S : Set A, S.Nonempty → Sᶜ.Nonempty →
        3 ≤ Nat.card (Boundary (Completion G A a b) S)) ∧
      HasPower (Completion G A a b) ∧ ¬HasPower (G.induce A) := by
  classical
  obtain ⟨A, hA, hAc, hB, hwfree, hmin⟩ := select_minimal_wfree_two_cut G hm hcutG
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
      obtain ⟨z, hz⟩ := hAne; exact ⟨z, by simpa using hz⟩
    have hsc : (A.toFinset)ᶜ.Nonempty := by
      obtain ⟨z, hz⟩ := hAcne; exact ⟨z, by simpa using hz⟩
    have hh := minimal_bad_two_edge_connected G hm A.toFinset hs hsc
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
  have hA2 : 2 ≤ Fintype.card A := by simpa only [Nat.card_eq_fintype_card] using hA
  obtain ⟨hab, hda, hdb⟩ :=
    wfree_2cut_matching_and_cubic_boundary G hm A hA2 ⟨x, hx⟩ hwfree a b x y hcut
  -- Prove x ≠ y using 2-connectivity (minimal_bad_no_cut_vertex)
  have hxy : x ≠ y := by
    intro heq
    let S1 : Finset V := insert x A.toFinset
    let S2 : Finset V := (A.toFinset)ᶜ
    have hcov : S1 ∪ S2 = Finset.univ := by
      ext v; simp [S1, S2]
    have hint : S1 ∩ S2 = {x} := by
      ext v
      simp only [S1, S2, Finset.mem_inter, Finset.mem_insert, Finset.mem_compl,
        Set.mem_toFinset, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | hvA, hvnA⟩
        · rfl
        · exact False.elim (hvnA hvA)
      · rintro rfl
        exact ⟨Or.inl rfl, hx⟩
    have hS1_2 : 2 ≤ S1.card := by
      have h1 : A.toFinset.card = Nat.card A := by
        rw [Nat.card_eq_fintype_card, ← Set.toFinset_card]
      have hxnot : x ∉ A.toFinset := by simpa using hx
      rw [Finset.card_insert_of_notMem hxnot]
      omega
    have hS2_2 : 2 ≤ S2.card := by
      have h2 : S2.card = Nat.card (Aᶜ : Set V) := by
        rw [Nat.card_eq_fintype_card, Fintype.card_compl_set]
        have h1 : A.toFinset.card = Fintype.card A := Set.toFinset_card A
        rw [Finset.card_compl, h1]
      omega
    obtain ⟨u, hu, v, hv, huv⟩ := minimal_bad_no_cut_vertex G hm x S1 S2 hcov hint hS1_2 hS2_2
    have huA : u ∈ A := by
      have h1 := Finset.mem_erase.mp hu
      have h2 := Finset.mem_insert.mp h1.2
      exact Set.mem_toFinset.mp (h2.resolve_left h1.1)
    have hvnotA : v ∉ A := by
      have h1 := Finset.mem_erase.mp hv
      exact fun h => (Finset.mem_compl.mp h1.2) (Set.mem_toFinset.mpr h)
    have hvx : v ≠ x := (Finset.mem_erase.mp hv).1
    rcases hcut ⟨u, huA⟩ v hvnotA huv with ⟨_, h⟩ | ⟨_, h⟩
    · exact hvx h
    · exact hvx (h.trans heq.symm)
  have hsm : SideMinimal G A := wfree_side_minimal G A hAc hwfree hmin
  have hnadj : ¬G.Adj a.1 b.1 :=
    wfree_minimal_side_ports_nonadjacent G A a b hab x y hx hy hax hby hda hdb hcut hsm
  have hdegs : ∀ z : A, Nat.card ((Completion G A a b).neighborSet z) = G.degree z.1 :=
    wfree_completion_degrees G A a b hab x y hx hy hax hby hcut hnadj
  have hthree : ∀ S : Set A, S.Nonempty → Sᶜ.Nonempty →
      3 ≤ Nat.card (Boundary (Completion G A a b) S) :=
    minimal_side_completion_three_edge_connected G A a b hab x y hcut hnadj hsm
  let H := Completion G A a b
  let : DecidableRel H.Adj := Classical.decRel _
  have hdegH : ∀ z : A, 3 ≤ H.degree z := by
    intro z
    have h1 := hdegs z
    rw [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree] at h1
    rw [h1]
    exact hwfree z
  have hn : Near H := ⟨⟨a, hdegH a⟩, ⟨a, fun z _ => hdegH z⟩⟩
  have hsmall : Fintype.card A < Fintype.card V := by
    apply Fintype.card_lt_of_injective_not_surjective (fun z : A => z.1) Subtype.val_injective
    intro hs
    obtain ⟨z, hz⟩ := hs x
    exact hx (hz ▸ z.2)
  have hpower : HasPower H := hm.2.2.1 A H hsmall hn
  have hfree : ¬HasPower (G.induce A) := fun hp => hm.2.1 (power_induce G A hp)
  exact ⟨A, a, b, x, y, hA, hAc, hcard, hwfree, hab, hx, hy, hxy, hax, hby, hda, hdb,
    hcut, hsm, hnadj, hdegs, hthree, hpower, hfree⟩

/-! ## Pillar 2: High-Edge Avoidance & `V_3`-Localization of Hitting Edges in `H_A` (`H-T-2` / `H-N-2`) -/

/-- **Class `H` Two-Cut High-Edge Avoidance**: In the completed side `H = Completion G A a b`
of ANY `MinimalBad G` with `SmallCut G 2`, deleting ANY edge `uv` incident to a vertex
`u ∈ A` of degree `≥ 4` STILL preserves `HasPower (H \ edge u v)`! -/
theorem wfree_two_cut_high_edge_avoided {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (A : Set V) (a b : A) (hBout : ∃ z : V, z ∉ A)
    (hwfree : ∀ v : A, 3 ≤ G.degree v.1)
    (hdegs : ∀ z : A, Nat.card ((Completion G A a b).neighborSet z) = G.degree z.1)
    {u v : A} (huv : (Completion G A a b).Adj u v) (hu4 : 4 ≤ G.degree u.1) :
    HasPower ((Completion G A a b) \ SimpleGraph.edge u v) := by
  classical
  let H := Completion G A a b
  let : DecidableRel H.Adj := Classical.decRel _
  have hHdeg : ∀ z : A, H.degree z = G.degree z.1 := by
    intro z
    have h1 := hdegs z
    rw [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree] at h1
    exact h1
  have hA2 : 2 ≤ Fintype.card A := by
    have hne : u ≠ v := H.ne_of_adj huv
    let f : Bool → A := fun t => if t then u else v
    have hf : Function.Injective f := by
      intro p q hpq; cases p <;> cases q <;> simp_all [f]
    have hc := Fintype.card_le_of_injective f hf
    simpa using hc
  have hnear : Near (H \ SimpleGraph.edge u v) := by
    apply near_of_except (H \ SimpleGraph.edge u v) v hA2
    intro z hzv
    have hd := erase_edge_degree H u v huv z
    rw [hHdeg z] at hd
    by_cases hzu : z = u
    · subst hzu; simp at hd; omega
    · simp [hzu, hzv] at hd; rw [hd]; exact hwfree z
  have hsmall : Fintype.card A < Fintype.card V := by
    obtain ⟨z0, hz0⟩ := hBout
    apply Fintype.card_lt_of_injective_not_surjective (fun z : A => z.1) Subtype.val_injective
    intro hs
    obtain ⟨z, hz⟩ := hs z0
    exact hz0 (hz ▸ z.2)
  exact hm.2.2.1 A (H \ SimpleGraph.edge u v) hsmall hnear

/-- **Hitting-Edge Localization Inside `H_A[V_3]`**: Every edge `uv` of `H = Completion G A a b`
whose deletion destroys all `2^k`-cycles MUST have both endpoints of exact degree 3. -/
theorem wfree_two_cut_hitting_edges_in_V3 {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (A : Set V) (a b : A) (hBout : ∃ z : V, z ∉ A)
    (hwfree : ∀ v : A, 3 ≤ G.degree v.1)
    (hdegs : ∀ z : A, Nat.card ((Completion G A a b).neighborSet z) = G.degree z.1)
    {u v : A} (huv : (Completion G A a b).Adj u v)
    (hhit : ¬ HasPower ((Completion G A a b) \ SimpleGraph.edge u v)) :
    G.degree u.1 = 3 ∧ G.degree v.1 = 3 := by
  have hu3 : G.degree u.1 = 3 := by
    have hge := hwfree u
    by_contra hne
    exact hhit (wfree_two_cut_high_edge_avoided G hm A a b hBout hwfree hdegs huv (by omega))
  have hv3 : G.degree v.1 = 3 := by
    have hge := hwfree v
    by_contra hne
    have hsym : (Completion G A a b) \ SimpleGraph.edge v u =
        (Completion G A a b) \ SimpleGraph.edge u v := by
      ext x y
      simp only [SimpleGraph.sdiff_adj, SimpleGraph.edge_adj]
      tauto
    have hpow := wfree_two_cut_high_edge_avoided G hm A a b hBout hwfree hdegs huv.symm (by omega)
    rw [hsym] at hpow
    exact hhit hpow
  exact ⟨hu3, hv3⟩

/-! ## Pillar 3: Multi-Operation Port-Spectrum Forcing & Cross-Side Fermat Disjointness -/

private def liftWalkAvoidEdge {W : Type u} {K : SimpleGraph W} {a b : W}
    {x y : W} (w : (K ⊔ SimpleGraph.edge a b).Walk x y)
    (hno : s(a, b) ∉ w.edges) : K.Walk x y :=
  match w with
  | .nil => .nil
  | .cons (u := u) (v := v) hadj rest =>
    have hK : K.Adj u v := by
      rcases hadj with h | h
      · exact h
      · exfalso
        apply hno
        simp only [Walk.edges_cons, List.mem_cons]
        left
        rcases ((SimpleGraph.edge_adj a b u v).mp h).1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact Sym2.eq_swap
    .cons hK (liftWalkAvoidEdge rest (fun hm => hno (by simp [hm])))

private theorem length_liftWalkAvoidEdge {W : Type u} {K : SimpleGraph W} {a b : W}
    {x y : W} (w : (K ⊔ SimpleGraph.edge a b).Walk x y) (hno : s(a, b) ∉ w.edges) :
    (liftWalkAvoidEdge w hno).length = w.length := by
  induction w with
  | nil => rfl
  | cons hadj rest ih =>
    simp only [liftWalkAvoidEdge, Walk.length_cons]
    rw [ih]

private theorem support_liftWalkAvoidEdge {W : Type u} {K : SimpleGraph W} {a b : W}
    {x y : W} (w : (K ⊔ SimpleGraph.edge a b).Walk x y) (hno : s(a, b) ∉ w.edges) :
    (liftWalkAvoidEdge w hno).support = w.support := by
  induction w with
  | nil => rfl
  | cons hadj rest ih =>
    simp only [liftWalkAvoidEdge, Walk.support_cons]
    rw [ih]

private theorem last_edge_of_mem_edges_end {W : Type u} {H : SimpleGraph W}
    {a b : W} :
    ∀ {z : W} (w : H.Walk z a), w.support.Nodup → s(a, b) ∈ w.edges →
      ∃ (p : H.Walk z b) (hba : H.Adj b a), w = p.append (.cons hba .nil) := by
  intro z w hnd hme
  induction w with
  | nil => simp at hme
  | @cons x y _ hxy rest ih =>
    simp only [Walk.support_cons, List.nodup_cons] at hnd
    rw [Walk.edges_cons, List.mem_cons] at hme
    rcases hme with htop | htail
    · rcases Sym2.eq_iff.mp htop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact False.elim (hnd.1 (Walk.end_mem_support rest))
      · cases rest with
        | nil => exact ⟨.nil, hxy, rfl⟩
        | cons _ rest2 =>
          exfalso
          have hnd2 := hnd.2
          simp only [Walk.support_cons, List.nodup_cons] at hnd2
          exact hnd2.1 (Walk.end_mem_support rest2)
    · obtain ⟨p, hba, rfl⟩ := ih hnd.2 htail
      exact ⟨.cons hxy p, hba, rfl⟩

/-- If adding a single new edge `ab` to a power-free graph `K` creates a `2^k`-cycle,
then `K` contains a simple `a`–`b` path of length `2^k - 1` (`k ≥ 2`). -/
theorem cycle_using_new_edge_gives_path {W : Type u} {K : SimpleGraph W}
    {a b : W} (hab : a ≠ b) (hKfree : ¬ HasPower K)
    (hpow : HasPower (K ⊔ SimpleGraph.edge a b)) :
    ∃ (k : ℕ) (p : K.Walk a b), 2 ≤ k ∧ p.IsPath ∧ p.length + 1 = 2 ^ k := by
  classical
  let H := K ⊔ SimpleGraph.edge a b
  obtain ⟨k, v0, c, hk, hc, hlen⟩ := hpow
  have mem_edge_of_cycle : ∀ {v : W} (w : H.Walk v v),
      w.IsCycle → w.length = 2 ^ k → s(a, b) ∈ w.edges := by
    intro v w hw hwlen
    by_contra hno
    let wK := liftWalkAvoidEdge w hno
    have hlenK : wK.length = 2 ^ k := (length_liftWalkAvoidEdge w hno).trans hwlen
    have hsuppK : wK.support = w.support := support_liftWalkAvoidEdge w hno
    have hpow4 : 4 ≤ 2 ^ k := by
      have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
      simpa using this
    have hnilK : ¬ wK.Nil := by
      intro h; have := Walk.length_eq_zero_iff.mpr h; omega
    have hwK : wK.IsCycle := by
      apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      refine ⟨Walk.IsPath.mk' ?_, by omega⟩
      rw [Walk.support_tail_of_not_nil _ hnilK, hsuppK]
      exact hw.support_nodup
    exact hKfree ⟨k, v, wK, hk, hwK, hlenK⟩
  have hmem_e : s(a, b) ∈ c.edges := mem_edge_of_cycle c hc hlen
  have ha_supp : a ∈ c.support := Walk.fst_mem_support_of_mem_edges c hmem_e
  let d : H.Walk a a := c.rotate a ha_supp
  have hd : d.IsCycle := hc.rotate ha_supp
  have hdlen : d.length = 2 ^ k := (Walk.length_rotate c a ha_supp).trans hlen
  have hd_edge : s(a, b) ∈ d.edges := mem_edge_of_cycle d hd hdlen
  have extract_from_first : ∀ (w : H.Walk a a), w.IsCycle → w.length = 2 ^ k →
      (∃ (hadj : H.Adj a b) (q : H.Walk b a), w = .cons hadj q) →
      ∃ (p : K.Walk a b), p.IsPath ∧ p.length + 1 = 2 ^ k := by
    rintro w hw hwlen ⟨hadj, q, rfl⟩
    have hq_no : s(a, b) ∉ q.edges := by
      have hnd := hw.edges_nodup
      rw [Walk.edges_cons, List.nodup_cons] at hnd
      exact hnd.1
    let qK : K.Walk b a := liftWalkAvoidEdge q hq_no
    have hqK_path : qK.IsPath := by
      apply Walk.IsPath.mk'
      rw [support_liftWalkAvoidEdge]
      simpa [Walk.support_cons] using hw.support_nodup
    refine ⟨qK.reverse, hqK_path.reverse, ?_⟩
    rw [Walk.length_reverse, length_liftWalkAvoidEdge]
    simp only [Walk.length_cons] at hwlen
    omega
  cases hd_eq : d with
  | nil => exact False.elim (hd.ne_nil hd_eq)
  | @cons _ u _ hau q =>
    by_cases hub : u = b
    · subst hub
      obtain ⟨p, hp, hplen⟩ := extract_from_first d hd hdlen ⟨hau, q, hd_eq⟩
      exact ⟨k, p, hk, hp, hplen⟩
    · have hmem_q : s(a, b) ∈ q.edges := by
        rw [hd_eq, Walk.edges_cons, List.mem_cons] at hd_edge
        refine hd_edge.resolve_left ?_
        intro heq
        rcases Sym2.eq_iff.mp heq with ⟨_, h2⟩ | ⟨_, h2⟩
        · exact hub h2.symm
        · exact hab h2.symm
      have hq_nd : q.support.Nodup := by
        have hnd := hd.support_nodup
        rw [hd_eq] at hnd
        simpa [Walk.support_cons] using hnd
      obtain ⟨p0, hba, hq_eq⟩ := last_edge_of_mem_edges_end q hq_nd hmem_q
      have hd_app : d = (Walk.cons hau p0).append (.cons hba .nil) := by
        rw [hd_eq, hq_eq]; rfl
      have hrev_eq : d.reverse = .cons hba.symm (Walk.cons hau p0).reverse := by
        rw [hd_app, Walk.reverse_append]
        rfl
      have hrev_len : d.reverse.length = 2 ^ k := by rw [Walk.length_reverse]; exact hdlen
      obtain ⟨p, hp, hplen⟩ :=
        extract_from_first d.reverse hd.reverse hrev_len ⟨hba.symm, (Walk.cons hau p0).reverse, hrev_eq⟩
      exact ⟨k, p, hk, hp, hplen⟩

/-- On the minimal `w`-free 2-cut side `A`, `G.induce A` contains a simple `a`–`b` path
of Fermat length `2^k - 1` (`k ≥ 2`). -/
theorem wfree_two_cut_fermat_path {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Set V) (a b : A) (hab : a ≠ b)
    (hpow : HasPower (Completion G A a b)) (hfree : ¬HasPower (G.induce A)) :
    ∃ (k : ℕ) (p : (G.induce A).Walk a b), 2 ≤ k ∧ p.IsPath ∧ p.length + 1 = 2 ^ k :=
  cycle_using_new_edge_gives_path hab hfree hpow

/-- On the minimal `w`-free 2-cut side `A`, identifying `a = b` inside `G.induce A` yields a
strictly smaller `Near` graph, forcing a simple `a`–`b` path of dyadic length `2^k` (`k ≥ 2`). -/
theorem wfree_two_cut_ident_dyadic_path {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (A : Set V) (a b : A) (hab : a ≠ b) (x y : V)
    (hx : x ∉ A) (hy : y ∉ A) (hax : G.Adj a.1 x) (hby : G.Adj b.1 y)
    (hda : G.degree a.1 = 3) (hdb : G.degree b.1 = 3)
    (hwfree : ∀ v : A, 3 ≤ G.degree v.1)
    (hcut : ∀ z : A, ∀ t : V, t ∉ A → G.Adj z.1 t →
      (z = a ∧ t = x) ∨ (z = b ∧ t = y))
    (hnadj : ¬ G.Adj a.1 b.1) :
    ∃ (k : ℕ) (p : (G.induce A).Walk a b), 2 ≤ k ∧ p.IsPath ∧ p.length = 2 ^ k := by
  classical
  let K := G.induce A
  let : DecidableRel K.Adj := Classical.decRel _
  have hKfree : ¬ HasPower K := fun hp => hm.2.1 (power_induce G A hp)
  have hKa : K.degree a = 2 := by
    have hd := induce_degree_add_out_local G A a
    have hout_a : ((G.neighborFinset a.1).filter (fun t => t ∉ A)) = {x} := by
      ext t
      simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
      constructor
      · rintro ⟨hat, ht⟩
        rcases hcut a t ht hat with ⟨_, h⟩ | ⟨h, _⟩
        · exact h
        · exact False.elim (hab h)
      · rintro rfl; exact ⟨hax, hx⟩
    rw [hout_a, Finset.card_singleton, hda] at hd
    change K.degree a + 1 = 3 at hd
    omega
  have hKb : K.degree b = 2 := by
    have hd := induce_degree_add_out_local G A b
    have hout_b : ((G.neighborFinset b.1).filter (fun t => t ∉ A)) = {y} := by
      ext t
      simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
      constructor
      · rintro ⟨hbt, ht⟩
        rcases hcut b t ht hbt with ⟨h, _⟩ | ⟨_, h⟩
        · exact False.elim (hab h.symm)
        · exact h
      · rintro rfl; exact ⟨hby, hy⟩
    rw [hout_b, Finset.card_singleton, hdb] at hd
    change K.degree b + 1 = 3 at hd
    omega
  have hKother : ∀ v : A, v ≠ a → v ≠ b → 3 ≤ K.degree v := by
    intro v hva hvb
    have hd := induce_degree_add_out_local G A v
    have hout : ((G.neighborFinset v.1).filter (fun t => t ∉ A)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro t ht hn
      rcases hcut v t hn ((G.mem_neighborFinset v.1 t).mp ht) with ⟨h, _⟩ | ⟨h, _⟩
      · exact hva h
      · exact hvb h
    rw [hout, Finset.card_empty, add_zero] at hd
    change K.degree v = G.degree v.1 at hd
    rw [hd]; exact hwfree v
  let W := {v : A // v ≠ b}
  let H := identGraph K a b
  let : DecidableRel H.Adj := Classical.decRel _
  let z : W := ⟨a, hab⟩
  have hWcard : Fintype.card W < Fintype.card V := by
    have h1 : Fintype.card W + 1 = Fintype.card A := card_delete_one b
    have h2 : Fintype.card A < Fintype.card V := by
      apply Fintype.card_lt_of_injective_not_surjective (fun t : A => t.1) Subtype.val_injective
      intro hs; obtain ⟨t, ht⟩ := hs x; exact hx (ht ▸ t.2)
    omega
  have hv_deg_of_not_common : ∀ v : W, v ≠ z → ¬ (K.Adj a v.1 ∧ K.Adj b v.1) →
      3 ≤ H.degree v := by
    intro v hvz hnc
    have hva : v.1 ≠ a := fun h => hvz (Subtype.ext h)
    let f : K.neighborSet v.1 → H.neighborSet v := fun u =>
      if hub : u.1 = b then
        ⟨z, ⟨hvz, Or.inr (Or.inr ⟨rfl, Eq.mp (congrArg (K.Adj v.1) hub) u.2⟩)⟩⟩
      else
        ⟨⟨u.1, hub⟩, ⟨fun h => (K.ne_of_adj u.2) (congrArg Subtype.val h), Or.inl u.2⟩⟩
    have hf : Function.Injective f := by
      intro u1 u2 heq
      by_cases h1 : u1.1 = b <;> by_cases h2 : u2.1 = b
      · exact Subtype.ext (h1.trans h2.symm)
      · simp only [f, h1, h2, ↓reduceDIte] at heq
        have h2a : u2.1 = a := (congrArg (fun t => t.1.1) heq).symm
        exact False.elim (hnc ⟨(h2a ▸ u2.2).symm, (h1 ▸ u1.2).symm⟩)
      · simp only [f, h1, h2, ↓reduceDIte] at heq
        have h1a : u1.1 = a := congrArg (fun t => t.1.1) heq
        exact False.elim (hnc ⟨(h1a ▸ u1.2).symm, (h2 ▸ u2.2).symm⟩)
      · simp only [f, h1, h2, ↓reduceDIte] at heq
        exact Subtype.ext (congrArg (fun t => t.1.1) heq)
    have hc := Fintype.card_le_of_injective f hf
    rw [SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.card_neighborSet_eq_degree] at hc
    exact (hKother v.1 hva v.2).trans hc
  have hnear : Near H := by
    by_cases hcom : ∃ c : A, K.Adj a c ∧ K.Adj b c
    · obtain ⟨c0, hac0, hbc0⟩ := hcom
      have huniq : ∀ c : A, K.Adj a c ∧ K.Adj b c → c = c0 := by
        rintro c ⟨hac, hbc⟩
        by_contra hne
        exact hKfree (rectangle_power K (K.ne_of_adj hac0) hab (K.ne_of_adj hac)
          (K.ne_of_adj hbc0).symm (Ne.symm hne) (K.ne_of_adj hbc) hac0 hbc0.symm hbc hac.symm)
      have hc0b : c0 ≠ b := (K.ne_of_adj hbc0).symm
      have hv1_ex : ∃ v1 : A, K.Adj b v1 ∧ v1 ≠ c0 := by
        have hcard2 : (K.neighborFinset b).card = 2 := by
          rw [K.card_neighborFinset_eq_degree, hKb]
        obtain ⟨u1, u2, hu12, hN⟩ := Finset.card_eq_two.mp hcard2
        by_cases h1 : u1 = c0
        · refine ⟨u2, (K.mem_neighborFinset b u2).mp (by rw [hN]; simp), ?_⟩
          intro h2; exact hu12 (h1.trans h2.symm)
        · exact ⟨u1, (K.mem_neighborFinset b u1).mp (by rw [hN]; simp), h1⟩
      obtain ⟨v1, hbv1, hv1c0⟩ := hv1_ex
      have hv1_not_a : ¬ K.Adj a v1 := fun hav1 => hv1c0 (huniq v1 ⟨hav1, hbv1⟩)
      have hz_deg : 3 ≤ H.degree z := by
        let f : K.neighborSet a ⊕ Unit → H.neighborSet z :=
          Sum.elim
            (fun u => ⟨⟨u.1, fun h => hnadj (h ▸ u.2)⟩,
              ⟨fun h => (K.ne_of_adj u.2) (congrArg Subtype.val h), Or.inl u.2⟩⟩)
            (fun _ => ⟨⟨v1, (K.ne_of_adj hbv1).symm⟩,
              ⟨fun h => hnadj (by
                have h1 : a = v1 := congrArg Subtype.val h
                rw [h1]; exact hbv1.symm),
               Or.inr (Or.inl ⟨rfl, hbv1⟩)⟩⟩)
        have hf : Function.Injective f := by
          rintro (u | ⟨⟩) (v | ⟨⟩) heq
          · exact congrArg Sum.inl (Subtype.ext (congrArg (fun t => t.1.1) heq))
          · have hval : u.1 = v1 := congrArg (fun t => t.1.1) heq
            exact False.elim (hv1_not_a (hval ▸ u.2))
          · have hval : v1 = v.1 := congrArg (fun t => t.1.1) heq
            exact False.elim (hv1_not_a (hval.symm ▸ v.2))
          · rfl
        have hc := Fintype.card_le_of_injective f hf
        rw [Fintype.card_sum, SimpleGraph.card_neighborSet_eq_degree,
          SimpleGraph.card_neighborSet_eq_degree, Fintype.card_unit, hKa] at hc
        omega
      refine ⟨⟨z, hz_deg⟩, ⟨⟨c0, hc0b⟩, fun v hvc => ?_⟩⟩
      by_cases hvz : v = z
      · rw [hvz]; exact hz_deg
      · exact hv_deg_of_not_common v hvz (fun h => hvc (Subtype.ext (huniq v.1 h)))
    · have hnc : ∀ c : A, ¬ (K.Adj a c ∧ K.Adj b c) := fun c hc => hcom ⟨c, hc⟩
      have hz_deg : 3 ≤ H.degree z := by
        let f : K.neighborSet a ⊕ K.neighborSet b → H.neighborSet z :=
          Sum.elim
            (fun u => ⟨⟨u.1, fun h => hnadj (h ▸ u.2)⟩,
              ⟨fun h => (K.ne_of_adj u.2) (congrArg Subtype.val h), Or.inl u.2⟩⟩)
            (fun u => ⟨⟨u.1, (K.ne_of_adj u.2).symm⟩,
              ⟨fun h => hnadj (by
                have h1 : a = u.1 := congrArg Subtype.val h
                rw [h1]; exact u.2.symm),
               Or.inr (Or.inl ⟨rfl, u.2⟩)⟩⟩)
        have hf : Function.Injective f := by
          rintro (u | u) (v | v) heq
          · exact congrArg Sum.inl (Subtype.ext (congrArg (fun t => t.1.1) heq))
          · have hval : u.1 = v.1 := congrArg (fun t => t.1.1) heq
            exact False.elim (hnc u.1 ⟨u.2, hval ▸ v.2⟩)
          · have hval : u.1 = v.1 := congrArg (fun t => t.1.1) heq
            exact False.elim (hnc u.1 ⟨hval ▸ v.2, u.2⟩)
          · exact congrArg Sum.inr (Subtype.ext (congrArg (fun t => t.1.1) heq))
        have hc := Fintype.card_le_of_injective f hf
        rw [Fintype.card_sum, SimpleGraph.card_neighborSet_eq_degree,
          SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.card_neighborSet_eq_degree,
          hKa, hKb] at hc
        omega
      refine ⟨⟨z, hz_deg⟩, ⟨z, fun v hvz => hv_deg_of_not_common v hvz (hnc v.1)⟩⟩
  obtain ⟨k, v0, c, hk, hc, hlen⟩ := hm.2.2.1 W H hWcard hnear
  obtain ⟨p, hp, hplen, _⟩ := lift_ident_cycle hab hKfree hk c hc hlen
  exact ⟨k, p, hk, hp, hplen⟩

/-- **Cross-Side Port-Path Coupling Obstruction**: Across any matching 2-edge cut
`E(A, Aᶜ) = {ax, by}` in a power-free graph `G`, no simple `a`–`b` path `p` in `G[A]`
and simple `x`–`y` path `q` in `G[Aᶜ]` can satisfy `p.length + q.length + 2 = 2 ^ k` (`k ≥ 2`). -/
theorem two_cut_no_matching_port_sum_pow2 {V : Type u}
    (G : SimpleGraph V) (hfree : ¬ HasPower G)
    (A : Set V) (a b : A) (x y : (Aᶜ : Set V))
    (hax : G.Adj a.1 x.1) (hby : G.Adj b.1 y.1)
    (p : (G.induce A).Walk a b) (hp : p.IsPath)
    (q : (G.induce (Aᶜ : Set V)).Walk y x) (hq : q.IsPath)
    {k : ℕ} (hk : 2 ≤ k) :
    p.length + q.length + 2 ≠ 2 ^ k := by
  intro heq
  let fA : G.induce A →g G := ⟨Subtype.val, fun h => h⟩
  let fAc : G.induce (Aᶜ : Set V) →g G := ⟨Subtype.val, fun h => h⟩
  let pG : G.Walk a.1 b.1 := p.map fA
  let qG : G.Walk y.1 x.1 := q.map fAc
  let p1 : G.Walk a.1 y.1 := pG.append (.cons hby .nil)
  let p2 : G.Walk y.1 a.1 := qG.append (.cons hax.symm .nil)
  let cyc : G.Walk a.1 a.1 := p1.append p2
  have hpG_nd : pG.support.Nodup := by
    rw [Walk.support_map]
    exact (List.nodup_map_iff Subtype.val_injective).mpr hp.support_nodup
  have hqG_nd : qG.support.Nodup := by
    rw [Walk.support_map]
    exact (List.nodup_map_iff Subtype.val_injective).mpr hq.support_nodup
  have hpG_inA : ∀ v ∈ pG.support, v ∈ A := by
    intro v hv
    rw [Walk.support_map, List.mem_map] at hv
    obtain ⟨u, _, rfl⟩ := hv
    exact u.2
  have hqG_notinA : ∀ v ∈ qG.support, v ∉ A := by
    intro v hv
    rw [Walk.support_map, List.mem_map] at hv
    obtain ⟨u, _, rfl⟩ := hv
    exact u.2
  have htail_eq : cyc.support.tail = pG.support.tail ++ qG.support ++ [a.1] := by
    have h1 : cyc.support = p1.support ++ p2.support.tail := Walk.support_append p1 p2
    have h2 : p1.support = pG.support ++ [y.1] := by simp [p1, Walk.support_append]
    have h3 : p2.support = qG.support ++ [a.1] := by simp [p2, Walk.support_append]
    have h6 : p2.support.tail = qG.support.tail ++ [a.1] := by
      rw [h3, ← qG.cons_tail_support]; rfl
    rw [h1, h2, h6]
    conv_lhs => rw [← pG.cons_tail_support]
    simp only [List.cons_append, List.tail_cons, List.append_assoc]
    conv_rhs => rw [← qG.cons_tail_support]
    simp only [List.cons_append, List.nil_append]
  have hpG_tail_nd : pG.support.tail.Nodup := by
    have h4 : pG.support = a.1 :: pG.support.tail := (pG.cons_tail_support).symm
    rw [h4, List.nodup_cons] at hpG_nd
    exact hpG_nd.2
  have ha_not_pG_tail : a.1 ∉ pG.support.tail := by
    have h4 : pG.support = a.1 :: pG.support.tail := (pG.cons_tail_support).symm
    rw [h4, List.nodup_cons] at hpG_nd
    exact hpG_nd.1
  have htail_nd : cyc.support.tail.Nodup := by
    rw [htail_eq]
    apply List.nodup_append.mpr
    refine ⟨List.nodup_append.mpr ⟨hpG_tail_nd, hqG_nd, ?_⟩, List.nodup_singleton a.1, ?_⟩
    · intro u hu v hv hequv
      subst hequv
      exact hqG_notinA u hv (hpG_inA u (List.mem_of_mem_tail hu))
    · intro u hu v hv hequv
      have hva : v = a.1 := List.mem_singleton.mp hv
      subst hequv hva
      rcases List.mem_append.mp hu with h1 | h2
      · exact ha_not_pG_tail h1
      · exact hqG_notinA a.1 h2 a.2
  have hlen : cyc.length = 2 ^ k := by
    simp only [cyc, p1, p2, pG, qG, Walk.length_append, Walk.length_map,
      Walk.length_cons, Walk.length_nil]
    omega
  have hpow4 : 4 ≤ 2 ^ k := by
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
    simpa using this
  have hnil : ¬ cyc.Nil := by
    intro h; have := Walk.length_eq_zero_iff.mpr h; omega
  have hcyc : cyc.IsCycle := by
    apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    refine ⟨Walk.IsPath.mk' ?_, by omega⟩
    rwa [Walk.support_tail_of_not_nil _ hnil]
  exact hfree ⟨k, a.1, cyc, hk, hcyc, hlen⟩

/-- **Cross-Side Fermat Disjointness**: Across any matching 2-edge cut in `MinimalBad G`,
no Fermat length `2^k - 1` (`k ≥ 2`) can occur as a simple port-to-port path on BOTH sides. -/
theorem two_cut_fermat_disjoint {V : Type u}
    (G : SimpleGraph V) (hfree : ¬ HasPower G)
    (A : Set V) (a b : A) (x y : (Aᶜ : Set V))
    (hax : G.Adj a.1 x.1) (hby : G.Adj b.1 y.1)
    {k : ℕ} (hk : 2 ≤ k)
    (p : (G.induce A).Walk a b) (hp : p.IsPath) (hplen : p.length + 1 = 2 ^ k)
    (q : (G.induce (Aᶜ : Set V)).Walk y x) (hq : q.IsPath) (hqlen : q.length + 1 = 2 ^ k) :
    False := by
  have hno := two_cut_no_matching_port_sum_pow2 G hfree A a b x y hax hby p hp q hq
    (k := k + 1) (by omega)
  have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; omega
  omega

/-! ## Pillar 4: Exact 6-Leaf Official DAG Closure Gates (13/26 → 19/26) -/

/-- **Gate 1 (`NoCubicHittingEdge3EC`)**: No 3-edge-connected finite graph `H` with `δ(H) ≥ 3`
admits a cubic hitting edge `ab` (`deg_H(a) = deg_H(b) = 3`, `HasPower H`, `¬HasPower (H \ ab)`). -/
def NoCubicHittingEdge3EC : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (a b : W), a ≠ b → H.Adj a b →
    (∀ z : W, 3 ≤ H.degree z) →
    H.degree a = 3 → H.degree b = 3 →
    (∀ S : Set W, S.Nonempty → Sᶜ.Nonempty → 3 ≤ Nat.card (Boundary H S)) →
    HasPower H → ¬ HasPower (H \ SimpleGraph.edge a b) → False

/-- **Master 6-Leaf Closure Gate 1**: `NoCubicHittingEdge3EC` simultaneously closes
ALL SIX open `*-2` terminal leaves of the official 26-leaf DAG
(`C-T-2`, `C-N-2`, `S-T-2`, `S-N-2`, `H-T-2`, `H-N-2`, moving 13/26 → 19/26). -/
theorem exclude_all_six_low2_of_no_cubic_hitting_edge_3ec
    (hgate : NoCubicHittingEdge3EC.{u}) :
    Exclude.{u} (Leaf.ct .low2) ∧
    Exclude.{u} (Leaf.cn .low2) ∧
    Exclude.{u} (Leaf.st .low2) ∧
    Exclude.{u} (Leaf.sn .low2) ∧
    Exclude.{u} (Leaf.ht .low2) ∧
    Exclude.{u} (Leaf.hn .low2) := by
  have hmaster : ∀ (V : Type u) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
      MinimalBad G → SmallCut G 2 → False := by
    intro V G _ _ hm hcutG
    classical
    obtain ⟨A, a, b, x, y, _, _, _, hwfree, hab, _, _, _, _, _, hda, hdb,
      _, _, hnadj, hdegs, hthree, hpower, hfree⟩ :=
      wfree_minimal_bad_two_cut_normal_form G hm hcutG
    let H := Completion G A a b
    let : DecidableRel H.Adj := Classical.decRel _
    have hHdeg : ∀ z : A, H.degree z = G.degree z.1 := by
      intro z
      have h1 := hdegs z
      rw [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree] at h1
      exact h1
    have hHab : H.Adj a b := Or.inr ((SimpleGraph.edge_adj a b a b).mpr ⟨Or.inl ⟨rfl, rfl⟩, hab⟩)
    have hdiff : H \ SimpleGraph.edge a b = G.induce A := by
      ext u v
      simp only [H, Completion, SimpleGraph.sdiff_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]
      constructor
      · rintro ⟨h1 | h2, hnot⟩
        · exact h1
        · exact False.elim (hnot h2)
      · intro huv
        refine ⟨Or.inl huv, ?_⟩
        rintro ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, _⟩
        · exact hnadj huv
        · exact hnadj huv.symm
    exact hgate A H a b hab hHab
      (fun z => by rw [hHdeg z]; exact hwfree z)
      (by rw [hHdeg a]; exact hda)
      (by rw [hHdeg b]; exact hdb)
      hthree hpower (by rw [hdiff]; exact hfree)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro V G _ _ hm hleaf; exact hmaster V G hm hleaf.2.2.2
  · intro V G _ _ hm hleaf; exact hmaster V G hm hleaf.2.2.2
  · intro V G _ _ hm hleaf; exact hmaster V G hm hleaf.2.2.2
  · intro V G _ _ hm hleaf; exact hmaster V G hm hleaf.2.2.2
  · intro V G _ _ hm hleaf; exact hmaster V G hm hleaf.2.2.2
  · intro V G _ _ hm hleaf; exact hmaster V G hm hleaf.2.2.2

/-- **Gate 2 (`TwoCutPortSync`)**: For every `MinimalBad G` with minimal `w`-free 2-cut side `A`,
the port-to-port path spectra of `G[A]` and `G[Aᶜ]` synchronize on some power of two
`p.length + q.length + 2 = 2 ^ k` (`k ≥ 2`). -/
def TwoCutPortSync : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    MinimalBad G → SmallCut G 2 →
    ∃ (A : Set V) (a b : A) (x y : (Aᶜ : Set V))
      (k : ℕ) (p : (G.induce A).Walk a b) (q : (G.induce (Aᶜ : Set V)).Walk y x),
      G.Adj a.1 x.1 ∧ G.Adj b.1 y.1 ∧ 2 ≤ k ∧
      p.IsPath ∧ q.IsPath ∧ p.length + q.length + 2 = 2 ^ k

/-- **Master 6-Leaf Closure Gate 2**: `TwoCutPortSync` simultaneously closes
ALL SIX open `*-2` terminal leaves of the official 26-leaf DAG. -/
theorem exclude_all_six_low2_of_port_sync
    (hsync : TwoCutPortSync.{u}) :
    Exclude.{u} (Leaf.ct .low2) ∧
    Exclude.{u} (Leaf.cn .low2) ∧
    Exclude.{u} (Leaf.st .low2) ∧
    Exclude.{u} (Leaf.sn .low2) ∧
    Exclude.{u} (Leaf.ht .low2) ∧
    Exclude.{u} (Leaf.hn .low2) := by
  have hmaster : ∀ (V : Type u) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
      MinimalBad G → SmallCut G 2 → False := by
    intro V G _ _ hm hcutG
    classical
    obtain ⟨A, a, b, x, y, k, p, q, hax, hby, hk, hp, hq, heq⟩ := hsync V G hm hcutG
    exact two_cut_no_matching_port_sum_pow2 G hm.2.1 A a b x y hax hby p hp q hq hk heq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro V G _ _ hm hleaf; exact hmaster V G hm hleaf.2.2.2
  · intro V G _ _ hm hleaf; exact hmaster V G hm hleaf.2.2.2
  · intro V G _ _ hm hleaf; exact hmaster V G hm hleaf.2.2.2
  · intro V G _ _ hm hleaf; exact hmaster V G hm hleaf.2.2.2
  · intro V G _ _ hm hleaf; exact hmaster V G hm hleaf.2.2.2
  · intro V G _ _ hm hleaf; exact hmaster V G hm hleaf.2.2.2

#print axioms select_minimal_wfree_two_cut
#print axioms wfree_side_minimal
#print axioms wfree_minimal_side_ports_nonadjacent
#print axioms wfree_completion_degrees
#print axioms wfree_minimal_bad_two_cut_normal_form
#print axioms wfree_two_cut_high_edge_avoided
#print axioms wfree_two_cut_hitting_edges_in_V3
#print axioms cycle_using_new_edge_gives_path
#print axioms wfree_two_cut_fermat_path
#print axioms wfree_two_cut_ident_dyadic_path
#print axioms two_cut_no_matching_port_sum_pow2
#print axioms two_cut_fermat_disjoint
#print axioms exclude_all_six_low2_of_no_cubic_hitting_edge_3ec
#print axioms exclude_all_six_low2_of_port_sync

end E64Wave7Agent5
