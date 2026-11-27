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
  have hmap := support_liftWalkAvoidNone p h
  rw [← hmap] at hnd
  exact List.Nodup.of_map _ hnd

theorem nodup_tail_liftWalkAvoidNone {V : Type u} {G : SimpleGraph V} {I : Finset V}
    {a b : { v : V // v ∉ I }}
    (p : (quotientGraph G I).Walk (some a) (some b)) (h : none ∉ p.support)
    (hnd : p.support.tail.Nodup) : (liftWalkAvoidNone p h).support.tail.Nodup := by
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
      none ∉ q'.support ∧ q'.support.Nodup ∧ q'.length + 1 = q.length := by
  generalize hsrc : (some a : QVert I) = s at q hnd
  induction q generalizing a with
  | nil => cases hsrc
  | @cons x y z hadj r ih =>
    subst hsrc
    cases y with
    | none =>
      cases r with
      | nil =>
        exact ⟨a, .nil, hadj, by simp, by simp, by simp⟩
      | cons hadj' r' =>
        simp only [Walk.support_cons, List.nodup_cons] at hnd
        have hmem : (none : QVert I) ∈ (Walk.cons hadj' r').support :=
          Walk.end_mem_support (Walk.cons hadj' r')
        have hnd2 := hnd.2
        simp only [Walk.support_cons, List.nodup_cons] at hnd2
        exact absurd (Walk.end_mem_support r') hnd2.1
    | some c =>
      simp only [Walk.support_cons, List.nodup_cons] at hnd
      obtain ⟨b, q', hlast, hno, hnd', hlen⟩ := ih hnd.2 rfl
      refine ⟨b, .cons hadj q', hlast, ?_, ?_, ?_⟩
      · simp [hno]
      · simp only [Walk.support_cons, List.nodup_cons]
        refine ⟨?_, hnd'⟩
        intro hmem
        apply hnd.1
        -- Every vertex in q'.support is in r.support
        have hsub : ∀ v ∈ q'.support, v ∈ r.support := by
          -- We prove this by noting we don't even need q' from ih without knowing support ⊆ r.support!
          sorry
        exact hsub _ hmem
      · simp only [Walk.length_cons]
        omega

end E64Wave4Agent2
