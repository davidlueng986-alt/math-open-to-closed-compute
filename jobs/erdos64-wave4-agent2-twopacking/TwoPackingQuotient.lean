import Core

/-!
# Universal 2-Packing Internally-Disjoint Dyadic-Path Theorem (Wave 4 Agent #2)

For ANY `MinimalBad` graph `G` (spanning all 13 remaining open leaves: `C-*`, `S-*`, `H-*`,
both `CUT` and `CORE`) and ANY 2-packing `I : Finset V` with `2 ≤ I.card` (pairwise non-adjacent
and sharing no common neighbor outside `I`), collapsing `I` to a single vertex yields a strictly
smaller `Near` simple graph `quotientGraph G I`. Global minimality forces a `2^k`-cycle in the
quotient, which lifts to an internally-`I`-disjoint simple `2^k`-path between two distinct
vertices of `I`.

Note on Whole-Problem Closure Gate:
This strictly generalizes Wave 1–2's All-Pairs Dyadic Path Theorem (`|I| = 2`) to arbitrary
2-packings across all 13 open leaves, yet independent verification shows that the 14-vertex
`AllPairsObstruction` witness (`witness14.json`) already satisfies all 34 2-packings of size ≥ 3
with 0 failures. Thus single-fiber quotient path-consequences alone do not close Erdős #64.
-/

namespace E64Wave4Agent2
open SimpleGraph Erdos64Closure E64Core
universe u

/-- A 2-packing in `G`: an independent set `I` such that no vertex outside `I`
has two distinct neighbors in `I`. -/
def IsTwoPacking {V : Type u} (G : SimpleGraph V) (I : Finset V) : Prop :=
  (∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) ∧
  (∀ w, w ∉ I → ∀ u ∈ I, ∀ v ∈ I, G.Adj w u → G.Adj w v → u = v)

/-- Vertices of the quotient graph obtained by collapsing `I` to `none`. -/
abbrev QVert {V : Type u} (I : Finset V) := Option { v : V // v ∉ I }

/-- Simple graph obtained by collapsing `I` to `none`. -/
def quotientGraph {V : Type u} (G : SimpleGraph V) (I : Finset V) :
    SimpleGraph (QVert I) where
  Adj a b := match a, b with
    | none, none => False
    | none, some y => ∃ u ∈ I, G.Adj u y.1
    | some x, none => ∃ u ∈ I, G.Adj x.1 u
    | some x, some y => G.Adj x.1 y.1
  symm := by
    rintro (_ | ⟨x, hx⟩) (_ | ⟨y, hy⟩) h
    · exact h
    · rcases h with ⟨u, hu, hadj⟩; exact ⟨u, hu, hadj.symm⟩
    · rcases h with ⟨u, hu, hadj⟩; exact ⟨u, hu, hadj.symm⟩
    · exact h.symm
  loopless := by
    rintro (_ | ⟨x, hx⟩) h
    · exact h
    · exact G.loopless x h

theorem card_qvert_lt {V : Type u} [Fintype V] [DecidableEq V]
    (I : Finset V) (hI : 2 ≤ I.card) :
    Fintype.card (QVert I) < Fintype.card V := by
  classical
  rw [Fintype.card_option]
  have hcompl : Fintype.card { v : V // v ∉ I } + I.card = Fintype.card V := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe]
    exact Nat.sub_add_cancel (Finset.card_le_univ I)
  omega

theorem degree_some_ge {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (I : Finset V) (hpack : IsTwoPacking G I)
    [DecidableRel (quotientGraph G I).Adj]
    (x : { v : V // v ∉ I }) :
    G.degree x.1 ≤ (quotientGraph G I).degree (some x) := by
  classical
  let f : V → QVert I := fun w => if hw : w ∈ I then none else some ⟨w, hw⟩
  have hmaps : ∀ w ∈ G.neighborFinset x.1, f w ∈ (quotientGraph G I).neighborFinset (some x) := by
    intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw ⊢
    by_cases hwi : w ∈ I
    · simp only [f, hwi, ↓reduceDIte]
      exact ⟨w, hwi, hw⟩
    · simp only [f, hwi, ↓reduceDIte]
      exact hw
  have hinj : Set.InjOn f (G.neighborFinset x.1 : Set V) := by
    intro w₁ hw₁ w₂ hw₂ heq
    rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hw₁ hw₂
    by_cases h₁ : w₁ ∈ I <;> by_cases h₂ : w₂ ∈ I
    · exact hpack.2 x.1 x.2 w₁ h₁ w₂ h₂ hw₁ hw₂
    · simp [f, h₁, h₂] at heq
    · simp [f, h₁, h₂] at heq
    · simp [f, h₁, h₂] at heq
      exact heq
  calc G.degree x.1
      = (G.neighborFinset x.1).card := (SimpleGraph.card_neighborFinset_eq_degree G x.1).symm
    _ = ((G.neighborFinset x.1).image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ ((quotientGraph G I).neighborFinset (some x)).card :=
        Finset.card_le_card (Finset.image_subset_iff.mpr hmaps)
    _ = (quotientGraph G I).degree (some x) :=
        SimpleGraph.card_neighborFinset_eq_degree (quotientGraph G I) (some x)

theorem degree_none_ge {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (I : Finset V) (hpack : IsTwoPacking G I)
    [DecidableRel (quotientGraph G I).Adj]
    {u : V} (hu : u ∈ I) :
    G.degree u ≤ (quotientGraph G I).degree none := by
  classical
  have hsub : ∀ y ∈ G.neighborFinset u, y ∉ I := by
    intro y hy hyI
    rw [SimpleGraph.mem_neighborFinset] at hy
    exact hpack.1 u hu y hyI hy
  let f : { y : V // y ∈ G.neighborFinset u } → (quotientGraph G I).neighborFinset none :=
    fun y => ⟨some ⟨y.1, hsub y.1 y.2⟩, by
      rw [SimpleGraph.mem_neighborFinset]
      exact ⟨u, hu, (SimpleGraph.mem_neighborFinset G u y.1).mp y.2⟩⟩
  have hinj : Function.Injective f := by
    intro y₁ y₂ heq
    have h1 : (f y₁).1 = (f y₂).1 := congrArg Subtype.val heq
    simp only [f, Option.some.injEq, Subtype.mk.injEq] at h1
    exact Subtype.ext h1
  have hcard := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_coe, SimpleGraph.card_neighborFinset_eq_degree] at hcard
  exact hcard

theorem near_quotient {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hnear : Near G) (I : Finset V) (hI : 2 ≤ I.card) (hpack : IsTwoPacking G I)
    [DecidableRel (quotientGraph G I).Adj] :
    Near (quotientGraph G I) := by
  classical
  obtain ⟨_, ⟨w, hw⟩⟩ := hnear
  have hex_u : ∃ u ∈ I, u ≠ w := by
    by_contra hall
    push_neg at hall
    have hsub : I ⊆ {w} := fun x hx => Finset.mem_singleton.mpr (hall x hx)
    have hle : I.card ≤ 1 := (Finset.card_le_card hsub).trans (by simp)
    omega
  obtain ⟨u, huI, huw⟩ := hex_u
  have hnone : 3 ≤ (quotientGraph G I).degree none :=
    (hw u huw).trans (degree_none_ge G I hpack huI)
  refine ⟨⟨none, hnone⟩, ?_⟩
  by_cases hwI : w ∈ I
  · refine ⟨none, ?_⟩
    rintro (_ | ⟨x, hx⟩) hne
    · exact absurd rfl hne
    · have hxw : x ≠ w := fun h => hx (h ▸ hwI)
      exact (hw x hxw).trans (degree_some_ge G I hpack ⟨x, hx⟩)
  · refine ⟨some ⟨w, hwI⟩, ?_⟩
    rintro (_ | ⟨x, hx⟩) hne
    · exact hnone
    · have hxw : x ≠ w := by
        intro h
        apply hne
        congr 1
        exact Subtype.ext h
      exact (hw x hxw).trans (degree_some_ge G I hpack ⟨x, hx⟩)

/-- Lift a walk in `quotientGraph G I` whose support avoids `none` back to `G`. -/
def liftWalkAvoidNone {V : Type u} {G : SimpleGraph V} {I : Finset V}
    {a b : { v : V // v ∉ I }} :
    (p : (quotientGraph G I).Walk (some a) (some b)) →
    none ∉ p.support → G.Walk a.1 b.1
  | .nil, _ => .nil
  | .cons (v := none) _ _, h => absurd (by simp) h
  | .cons (v := some c) hadj q, h =>
      .cons hadj (liftWalkAvoidNone q (fun hm => h (by simp [hm])))

theorem length_liftWalkAvoidNone {V : Type u} {G : SimpleGraph V} {I : Finset V}
    {a b : { v : V // v ∉ I }}
    (p : (quotientGraph G I).Walk (some a) (some b)) (h : none ∉ p.support) :
    (liftWalkAvoidNone p h).length = p.length := by
  induction p with
  | nil => rfl
  | @cons x y z hadj q ih =>
    cases y with
    | none => exact absurd (by simp) h
    | some c =>
      simp only [liftWalkAvoidNone, Walk.length_cons]
      rw [ih (fun hm => h (by simp [hm]))]

theorem support_liftWalkAvoidNone {V : Type u} {G : SimpleGraph V} {I : Finset V}
    {a b : { v : V // v ∉ I }}
    (p : (quotientGraph G I).Walk (some a) (some b)) (h : none ∉ p.support) :
    (liftWalkAvoidNone p h).support.map (fun v => if hv : v ∈ I then none else some ⟨v, hv⟩) =
      p.support := by
  classical
  induction p with
  | nil => simp [liftWalkAvoidNone, a.2]
  | @cons x y z hadj q ih =>
    cases y with
    | none => exact absurd (by simp) h
    | some c =>
      simp only [liftWalkAvoidNone, Walk.support_cons, List.map_cons, x.2, ↓reduceDIte]
      congr 1
      exact ih (fun hm => h (by simp [hm]))

theorem mem_support_liftWalkAvoidNone_not_mem {V : Type u} {G : SimpleGraph V} {I : Finset V}
    {a b : { v : V // v ∉ I }}
    (p : (quotientGraph G I).Walk (some a) (some b)) (h : none ∉ p.support)
    {v : V} (hv : v ∈ (liftWalkAvoidNone p h).support) : v ∉ I := by
  induction p with
  | nil =>
    simp only [liftWalkAvoidNone, Walk.support_nil, List.mem_singleton] at hv
    exact hv ▸ a.2
  | @cons x y z hadj q ih =>
    cases y with
    | none => exact absurd (by simp) h
    | some c =>
      simp only [liftWalkAvoidNone, Walk.support_cons, List.mem_cons] at hv
      rcases hv with rfl | hv'
      · exact x.2
      · exact ih (fun hm => h (by simp [hm])) hv'

theorem nodup_liftWalkAvoidNone {V : Type u} {G : SimpleGraph V} {I : Finset V}
    {a b : { v : V // v ∉ I }}
    (p : (quotientGraph G I).Walk (some a) (some b)) (h : none ∉ p.support)
    (hnd : p.support.Nodup) : (liftWalkAvoidNone p h).support.Nodup := by
  classical
  have hmap := support_liftWalkAvoidNone p h
  rw [← hmap] at hnd
  exact List.Nodup.of_map _ hnd

theorem nodup_tail_liftWalkAvoidNone {V : Type u} {G : SimpleGraph V} {I : Finset V}
    {a b : { v : V // v ∉ I }}
    (p : (quotientGraph G I).Walk (some a) (some b)) (h : none ∉ p.support)
    (hnd : p.support.tail.Nodup) : (liftWalkAvoidNone p h).support.tail.Nodup := by
  classical
  have hmap := congrArg List.tail (support_liftWalkAvoidNone p h)
  rw [List.map_tail] at hmap
  rw [← hmap] at hnd
  exact List.Nodup.of_map _ hnd

/-- Split a walk from `some a` to `none` whose support is `Nodup` into a walk
from `some a` to `some b` avoiding `none`, followed by a final edge `some b → none`. -/
theorem split_walk_to_none {V : Type u} {G : SimpleGraph V} {I : Finset V}
    {a : { v : V // v ∉ I }}
    (q : (quotientGraph G I).Walk (some a) none) (hnd : q.support.Nodup) :
    ∃ (b : { v : V // v ∉ I }) (q' : (quotientGraph G I).Walk (some a) (some b))
      (hlast : (quotientGraph G I).Adj (some b) none),
      none ∉ q'.support ∧ q'.support.Nodup ∧
      (∀ v ∈ q'.support, v ∈ q.support) ∧ q'.length + 1 = q.length := by
  generalize hsrc : (some a : QVert I) = s at q hnd
  induction q generalizing a with
  | nil => cases hsrc
  | @cons x y z hadj r ih =>
    subst hsrc
    cases y with
    | none =>
      cases r with
      | nil =>
        exact ⟨a, .nil, hadj, by simp, by simp, fun v hv => by simp at hv; simp [hv], by simp⟩
      | cons hadj' r' =>
        simp only [Walk.support_cons, List.nodup_cons] at hnd
        have hnd2 := hnd.2
        simp only [Walk.support_cons, List.nodup_cons] at hnd2
        exact absurd (Walk.end_mem_support r') hnd2.1
    | some c =>
      simp only [Walk.support_cons, List.nodup_cons] at hnd
      obtain ⟨b, q', hlast, hno, hnd', hsub, hlen⟩ := ih hnd.2 rfl
      refine ⟨b, .cons hadj q', hlast, ?_, ?_, ?_, ?_⟩
      · simp [hno]
      · simp only [Walk.support_cons, List.nodup_cons]
        exact ⟨fun hmem => hnd.1 (hsub _ hmem), hnd'⟩
      · intro v hv
        simp only [Walk.support_cons, List.mem_cons] at hv ⊢
        rcases hv with rfl | hv'
        · exact Or.inl rfl
        · exact Or.inr (hsub v hv')
      · simp only [Walk.length_cons]
        omega

/-- Universal 2-Packing Internally-Disjoint Dyadic-Path Theorem across all 13 open leaves
of `MinimalBad`: for any 2-packing `I` of size at least 2, there exist distinct `x, y ∈ I`
and a simple `x`–`y` path of length `2^k` (`k ≥ 2`) whose internal vertices lie outside `I`. -/
theorem minimal_bad_two_packing_dyadic_path
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hm : MinimalBad G) (I : Finset V) (hI : 2 ≤ I.card) (hpack : IsTwoPacking G I) :
    ∃ (x y : V) (k : ℕ) (p : G.Walk x y),
      x ∈ I ∧ y ∈ I ∧ x ≠ y ∧ 2 ≤ k ∧ p.IsPath ∧ p.length = 2 ^ k ∧
      ∀ v ∈ p.support, v ∈ I → v = x ∨ v = y := by
  classical
  let H := quotientGraph G I
  have hpow : HasPower H :=
    hm.2.2.1 (QVert I) H (card_qvert_lt I hI) (near_quotient G hm.1 I hI hpack)
  obtain ⟨k, v₀, c, hk, hcyc, hlen⟩ := hpow
  by_cases hnone : none ∈ c.support
  · let c' := c.rotate hnone
    have hcyc' : c'.IsCycle := hcyc.rotate hnone
    have hlen' : c'.length = 2 ^ k := by simp [c', hlen]
    have hge3 : 3 ≤ c'.length := hcyc'.three_le_length
    cases hc' : c' with
    | nil =>
      rw [hc'] at hge3
      simp at hge3
    | @cons _ y _ h₁ q =>
      cases y with
      | none =>
        exact absurd h₁ (H.loopless none)
      | some a =>
        have hnd_q : q.support.Nodup := by
          have ht := hcyc'.support_nodup
          rw [hc'] at ht
          simpa [Walk.support_cons] using ht
        obtain ⟨b, q', hlast, hno, hnd', _, hlen_q'⟩ := split_walk_to_none q hnd_q
        obtain ⟨x, hxI, hxadj⟩ := h₁
        obtain ⟨y, hyI, hyadj⟩ := hlast
        let p' : G.Walk a.1 b.1 := liftWalkAvoidNone q' hno
        have hp'_len : p'.length = q'.length := length_liftWalkAvoidNone q' hno
        have hp'_nd : p'.support.Nodup := nodup_liftWalkAvoidNone q' hno hnd'
        have hp'_out : ∀ v ∈ p'.support, v ∉ I :=
          fun v hv => mem_support_liftWalkAvoidNone_not_mem q' hno hv
        let p : G.Walk x y := Walk.cons hxadj (p'.concat hyadj)
        have hp_len : p.length = 2 ^ k := by
          have hcl : q.length + 1 = 2 ^ k := by
            rw [hc', Walk.length_cons] at hlen'
            omega
          simp only [p, Walk.length_cons, Walk.length_concat, hp'_len]
          omega
        have hp_supp : p.support = x :: (p'.support ++ [y]) := by
          simp [p, Walk.support_cons, Walk.support_concat]
        have hxy : x ≠ y := by
          intro hEq
          subst hEq
          have hp_nil : ¬ p.Nil := by
            intro hnil
            have hz := Walk.length_eq_zero_iff.mpr hnil
            have hpow4 : 4 ≤ 2 ^ k := by
              calc 4 = 2 ^ 2 := by decide
                _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
            omega
          have hp_tail_nd : p.support.tail.Nodup := by
            rw [hp_supp, List.tail_cons, List.nodup_append]
            refine ⟨hp'_nd, List.nodup_singleton x, ?_⟩
            intro u hu v hv huv
            simp only [List.mem_singleton] at hv
            subst hv
            exact hp'_out u hu (huv ▸ hxI)
          have hp_cyc : p.IsCycle := by
            apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
            refine ⟨Walk.IsPath.mk' ?_, ?_⟩
            · rwa [Walk.support_tail_of_not_nil _ hp_nil]
            · have hpow4 : 4 ≤ 2 ^ k := by
                calc 4 = 2 ^ 2 := by decide
                  _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
              omega
          exact hm.2.1 ⟨k, x, p, hk, hp_cyc, hp_len⟩
        have hp_nd : p.support.Nodup := by
          rw [hp_supp, List.nodup_cons, List.nodup_append]
          refine ⟨?_, hp'_nd, List.nodup_singleton y, ?_⟩
          · intro hmem
            rw [List.mem_append, List.mem_singleton] at hmem
            rcases hmem with hx' | hEq
            · exact hp'_out x hx' hxI
            · exact hxy hEq
          · intro u hu v hv huv
            simp only [List.mem_singleton] at hv
            subst hv
            exact hp'_out u hu (huv ▸ hyI)
        refine ⟨x, y, k, p, hxI, hyI, hxy, hk, Walk.IsPath.mk' hp_nd, hp_len, ?_⟩
        intro v hv hvI
        rw [hp_supp, List.mem_cons, List.mem_append, List.mem_singleton] at hv
        rcases hv with rfl | (hv' | rfl)
        · exact Or.inl rfl
        · exact absurd hvI (hp'_out v hv')
        · exact Or.inr rfl
  · cases hv₀ : v₀ with
    | none =>
      exact absurd (hv₀ ▸ Walk.start_mem_support c) hnone
    | some a =>
      subst hv₀
      let cl : G.Walk a.1 a.1 := liftWalkAvoidNone c hnone
      have hcl_len : cl.length = 2 ^ k := by
        rw [length_liftWalkAvoidNone, hlen]
      have hcl_ge3 : 3 ≤ cl.length := by
        rw [length_liftWalkAvoidNone]
        exact hcyc.three_le_length
      have hcl_nil : ¬ cl.Nil := by
        intro hnil
        have hz := Walk.length_eq_zero_iff.mpr hnil
        omega
      have hcl_tail_nd : cl.support.tail.Nodup :=
        nodup_tail_liftWalkAvoidNone c hnone hcyc.support_nodup
      have hcl_cyc : cl.IsCycle := by
        apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
        refine ⟨Walk.IsPath.mk' ?_, hcl_ge3⟩
        rwa [Walk.support_tail_of_not_nil _ hcl_nil]
      exact False.elim (hm.2.1 ⟨k, a.1, cl, hk, hcl_cyc, hcl_len⟩)

#print axioms minimal_bad_two_packing_dyadic_path
#print axioms near_quotient
#print axioms card_qvert_lt

end E64Wave4Agent2
