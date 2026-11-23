import Mathlib

/-!
# CAP062: cap-specific sumsets and robust representation bounds

No classification theorem or external finite certificate is assumed here.
The main deletion theorem is the exact combinatorial implication used to
deduce `r(-c) <= number of deleted endpoints` in the cap upper-bound proof.

An `IsCap` set has only diagonal zero-sum triples.  On a vector space over
`ZMod 3`, this is the usual definition of a cap.  The slicing theorem takes
an actual cap in `G × ZMod 3`, rather than assuming its mixed-sum condition.
-/

namespace Capset

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Every zero-sum triple in the finite set is diagonal. -/
def IsCap (S : Finset G) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a + b + c = 0 → a = b ∧ b = c

/-- The three sets contain no mixed zero-sum triple. -/
def MixedAvoid (A B C : Finset G) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, ∀ c ∈ C, a + b + c ≠ 0

/-- Ordered representations of `t` as a sum from `A` and `B`. -/
def representations (A B : Finset G) (t : G) : Finset (G × G) :=
  (A.product B).filter fun p => p.1 + p.2 = t

/-- First endpoints of representations; the second endpoint is forced. -/
def representationFirst (A B : Finset G) (t : G) : Finset G :=
  A.filter fun a => t - a ∈ B

/-- Counting first endpoints counts ordered sum representations exactly. -/
theorem representations_card_eq (A B : Finset G) (t : G) :
    (representations A B t).card = (representationFirst A B t).card := by
  classical
  have hset : representations A B t =
      (representationFirst A B t).image (fun a => (a, t - a)) := by
    ext p
    constructor
    · intro hp
      have hp' : (p.1 ∈ A ∧ p.2 ∈ B) ∧ p.1 + p.2 = t := by
        simpa [representations] using hp
      have hb : p.2 = t - p.1 := by
        calc
          p.2 = (p.1 + p.2) - p.1 := by abel
          _ = t - p.1 := by rw [hp'.2]
      apply Finset.mem_image.mpr
      refine ⟨p.1, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        exact ⟨hp'.1.1, by rw [← hb]; exact hp'.1.2⟩
      · exact Prod.ext rfl hb.symm
    · intro hp
      rcases Finset.mem_image.mp hp with ⟨a, ha, rfl⟩
      have ha' : a ∈ A ∧ t - a ∈ B := by
        simpa [representationFirst] using ha
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ha', ?_⟩
      change a + (t - a) = t
      abel
  rw [hset]
  exact Finset.card_image_of_injective _ (by
    intro x y hxy
    exact congrArg Prod.fst hxy)

/--
If deleting endpoints leaves no mixed zero-sum triple, every original
representation of `-c` is charged to a deleted endpoint.  For a fixed sum,
each first or second endpoint occurs in at most one representation.

No subset assumption is needed: `A \ A₀` already means the endpoints of
`A` that are absent from `A₀`, and likewise for the second set.
-/
theorem representation_card_le_deleted
    (A B A₀ B₀ C : Finset G) (hMixed : MixedAvoid A₀ B₀ C)
    {c : G} (hc : c ∈ C) :
    (representations A B (-c)).card ≤ (A \ A₀).card + (B \ B₀).card := by
  classical
  have hsub : representationFirst A B (-c) ⊆
      (A \ A₀) ∪ (B \ B₀).image (fun b => -c - b) := by
    intro a ha
    have ha' : a ∈ A ∧ -c - a ∈ B := by
      simpa [representationFirst] using ha
    by_cases ha₀ : a ∈ A₀
    · have hb₀ : -c - a ∉ B₀ := by
        intro hb₀
        exact hMixed a ha₀ (-c - a) hb₀ c hc (by abel)
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_image.mpr
      refine ⟨-c - a, Finset.mem_sdiff.mpr ⟨ha'.2, hb₀⟩, ?_⟩
      abel
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨ha'.1, ha₀⟩))
  calc
    (representations A B (-c)).card =
        (representationFirst A B (-c)).card := representations_card_eq A B (-c)
    _ ≤ ((A \ A₀) ∪ (B \ B₀).image (fun b => -c - b)).card :=
      Finset.card_le_card hsub
    _ ≤ (A \ A₀).card + ((B \ B₀).image (fun b => -c - b)).card :=
      Finset.card_union_le _ _
    _ ≤ (A \ A₀).card + (B \ B₀).card :=
      Nat.add_le_add_left Finset.card_image_le _

/-- A slice of an actual cap, with its layer coordinate removed. -/
def slice [Fintype G] (K : Finset (G × ZMod 3)) (t : ZMod 3) : Finset G :=
  Finset.univ.filter fun x => (x, t) ∈ K

/-- Distinct layers of a cap contain no mixed zero-sum triple. -/
theorem cap_slices_mixed [Fintype G]
    {K : Finset (G × ZMod 3)} (hK : IsCap K) :
    MixedAvoid (slice K 0) (slice K 1) (slice K 2) := by
  intro a ha b hb c hc hzero
  have haK : (a, (0 : ZMod 3)) ∈ K := by simpa [slice] using ha
  have hbK : (b, (1 : ZMod 3)) ∈ K := by simpa [slice] using hb
  have hcK : (c, (2 : ZMod 3)) ∈ K := by simpa [slice] using hc
  have hsum : (a, (0 : ZMod 3)) + (b, (1 : ZMod 3)) + (c, (2 : ZMod 3)) = 0 := by
    apply Prod.ext
    · change a + b + c = 0
      exact hzero
    · change (0 : ZMod 3) + 1 + 2 = 0
      decide
  have heq := (hK (a, 0) haK (b, 1) hbK (c, 2) hcK hsum).1
  have h01 : (0 : ZMod 3) = 1 := congrArg Prod.snd heq
  norm_num at h01

/--
The cap-specific robust deletion theorem used in the Fourier upper bound.
`A` and `B` may be any completed or enlarged first and second layers.
-/
theorem cap_slice_representation_bound [Fintype G]
    {K : Finset (G × ZMod 3)} (hK : IsCap K)
    (A B : Finset G) {c : G} (hc : c ∈ slice K 2) :
    (representations A B (-c)).card ≤
      (A \ slice K 0).card + (B \ slice K 1).card := by
  exact representation_card_le_deleted A B (slice K 0) (slice K 1) (slice K 2)
    (cap_slices_mixed hK) hc

/-- Sums of two distinct points of a finite set. -/
def restrictedSumset (S : Finset G) : Finset G :=
  ((S.product S).filter fun p => p.1 ≠ p.2).image fun p => p.1 + p.2

/-- Negative points of a finite set. -/
def negativeSet (S : Finset G) : Finset G := S.image fun x => -x

/-- A cap is disjoint from the negatives of its restricted sumset. -/
theorem negative_disjoint_restrictedSumset {S : Finset G} (hS : IsCap S) :
    Disjoint (negativeSet S) (restrictedSumset S) := by
  classical
  rw [Finset.disjoint_left]
  intro z hzN hzR
  rcases Finset.mem_image.mp hzN with ⟨c, hc, hcz⟩
  rcases Finset.mem_image.mp hzR with ⟨p, hp, hpz⟩
  have hp' : (p.1 ∈ S ∧ p.2 ∈ S) ∧ p.1 ≠ p.2 := by
    simpa using hp
  have hzero : p.1 + p.2 + c = 0 := by
    rw [hpz, ← hcz]
    simp
  exact hp'.2 (hS p.1 hp'.1.1 p.2 hp'.1.2 c hc hzero).1

/-- A quantitative, finite-universe cap-specific restricted-sumset bound. -/
theorem card_add_restrictedSumset_le [Fintype G]
    {S : Finset G} (hS : IsCap S) :
    S.card + (restrictedSumset S).card ≤ Fintype.card G := by
  classical
  have hneg : (negativeSet S).card = S.card := by
    exact Finset.card_image_of_injective S neg_injective
  have hdisj := negative_disjoint_restrictedSumset hS
  have hle := Finset.card_le_card
    (Finset.subset_univ (negativeSet S ∪ restrictedSumset S))
  rw [Finset.card_union_of_disjoint hdisj, hneg, Finset.card_univ] at hle
  exact hle

/-! ## Small kernel-checked non-vacuity and sharpness examples -/

/-- A nonempty cap with two distinct points; verified by Lean's kernel. -/
theorem two_point_cap : IsCap ({0, 1} : Finset (ZMod 3)) := by
  unfold IsCap
  decide

/-- The restricted-sumset cardinality bound is attained. -/
theorem two_point_packing_sharp :
    ({0, 1} : Finset (ZMod 3)).card +
      (restrictedSumset ({0, 1} : Finset (ZMod 3))).card = Fintype.card (ZMod 3) := by
  decide

/-- The deletion estimate has a nonempty example attaining equality. -/
theorem deletion_bound_sharp :
    MixedAvoid ({0} : Finset (ZMod 3)) {0, 1} {1} ∧
    (representations ({0, 1} : Finset (ZMod 3)) {0, 1} (-1)).card = 1 ∧
    (({0, 1} : Finset (ZMod 3)) \ {0}).card +
      (({0, 1} : Finset (ZMod 3)) \ {0, 1}).card = 1 := by
  unfold MixedAvoid
  decide

/-! ## Two-plus-two deletion holes and double-translate intersections -/

/-- Translation of a finite set. -/
def translate (a : G) (S : Finset G) : Finset G := S.image fun b => a + b

theorem mem_translate_iff (a t : G) (S : Finset G) :
    t ∈ translate a S ↔ t - a ∈ S := by
  classical
  constructor
  · intro ht
    rcases Finset.mem_image.mp ht with ⟨b, hb, hbt⟩
    have heq : t - a = b := by
      calc
        t - a = (a + b) - a := by rw [hbt]
        _ = b := by abel
    simpa [heq] using hb
  · intro ht
    exact Finset.mem_image.mpr ⟨t - a, ht, by abel⟩

/-- At most one of a pair can pass a predicate unless both pass. -/
theorem pair_filter_card_le_one (a b : G) (P : G → Prop) [DecidablePred P]
    (h : ¬ (P a ∧ P b)) :
    (({a, b} : Finset G).filter P).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  have hx' : (x = a ∨ x = b) ∧ P x := by simpa using hx
  have hy' : (y = a ∨ y = b) ∧ P y := by simpa using hy
  aesop

/-- Every original representation of a hole uses an active deleted endpoint. -/
theorem representation_card_le_active_deletions
    (A B D₁ D₂ : Finset G) (t : G)
    (hHole : representationFirst (A \ D₁) (B \ D₂) t = ∅) :
    (representations A B t).card ≤
      (representationFirst D₁ B t).card + (representationFirst D₂ A t).card := by
  classical
  have hsub : representationFirst A B t ⊆
      representationFirst D₁ B t ∪
        (representationFirst D₂ A t).image (fun b => t - b) := by
    intro a ha
    have ha' : a ∈ A ∧ t - a ∈ B := by
      simpa [representationFirst] using ha
    by_cases haD : a ∈ D₁
    · apply Finset.mem_union.mpr
      left
      exact Finset.mem_filter.mpr ⟨haD, ha'.2⟩
    · have hbD : t - a ∈ D₂ := by
        by_contra hbD
        have hs : a ∈ representationFirst (A \ D₁) (B \ D₂) t := by
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_sdiff.mpr ⟨ha'.1, haD⟩,
            Finset.mem_sdiff.mpr ⟨ha'.2, hbD⟩⟩
        rw [hHole] at hs
        exact Finset.not_mem_empty a hs
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_image.mpr
      refine ⟨t - a, ?_, by abel⟩
      apply Finset.mem_filter.mpr
      refine ⟨hbD, ?_⟩
      have heq : t - (t - a) = a := by abel
      simpa [heq] using ha'.1
  calc
    (representations A B t).card = (representationFirst A B t).card :=
      representations_card_eq A B t
    _ ≤ (representationFirst D₁ B t ∪
        (representationFirst D₂ A t).image (fun b => t - b)).card :=
      Finset.card_le_card hsub
    _ ≤ (representationFirst D₁ B t).card +
        ((representationFirst D₂ A t).image (fun b => t - b)).card :=
      Finset.card_union_le _ _
    _ ≤ (representationFirst D₁ B t).card + (representationFirst D₂ A t).card :=
      Nat.add_le_add_left Finset.card_image_le _

/--
After deleting two endpoints on each side, a hole with at least three
original representations belongs to one of two double-translate
intersections.  No distinctness or membership hypotheses on the named
deleted endpoints are needed for this covering statement.
-/
theorem three_representation_hole_mem_double_translate
    (A B : Finset G) (a₁ a₂ b₁ b₂ t : G)
    (hHole : representationFirst (A \ {a₁, a₂}) (B \ {b₁, b₂}) t = ∅)
    (hThree : 3 ≤ (representations A B t).card) :
    t ∈ (translate a₁ B ∩ translate a₂ B) ∪
      (translate b₁ A ∩ translate b₂ A) := by
  classical
  by_contra hNot
  have hA : ¬ (t - a₁ ∈ B ∧ t - a₂ ∈ B) := by
    intro hBoth
    apply hNot
    apply Finset.mem_union.mpr
    left
    exact Finset.mem_inter.mpr ⟨(mem_translate_iff a₁ t B).mpr hBoth.1,
      (mem_translate_iff a₂ t B).mpr hBoth.2⟩
  have hB : ¬ (t - b₁ ∈ A ∧ t - b₂ ∈ A) := by
    intro hBoth
    apply hNot
    apply Finset.mem_union.mpr
    right
    exact Finset.mem_inter.mpr ⟨(mem_translate_iff b₁ t A).mpr hBoth.1,
      (mem_translate_iff b₂ t A).mpr hBoth.2⟩
  have hca : (representationFirst ({a₁, a₂} : Finset G) B t).card ≤ 1 :=
    pair_filter_card_le_one a₁ a₂ (fun a => t - a ∈ B) hA
  have hcb : (representationFirst ({b₁, b₂} : Finset G) A t).card ≤ 1 :=
    pair_filter_card_le_one b₁ b₂ (fun b => t - b ∈ A) hB
  have hle := representation_card_le_active_deletions A B {a₁, a₂} {b₁, b₂} t hHole
  omega

/-- Points in a specified finite region with at least three representations. -/
def highRepresentationPoints (A B Z : Finset G) : Finset G :=
  Z.filter fun t => 3 ≤ (representations A B t).card

/-- A finite family of deletion holes is covered by the two intersections. -/
theorem high_representation_holes_subset
    (A B Z : Finset G) (a₁ a₂ b₁ b₂ : G)
    (hHole : ∀ t ∈ Z,
      representationFirst (A \ {a₁, a₂}) (B \ {b₁, b₂}) t = ∅) :
    highRepresentationPoints A B Z ⊆
      (translate a₁ B ∩ translate a₂ B) ∪
        (translate b₁ A ∩ translate b₂ A) := by
  intro t ht
  have ht' : t ∈ Z ∧ 3 ≤ (representations A B t).card := by
    simpa [highRepresentationPoints] using ht
  exact three_representation_hole_mem_double_translate A B a₁ a₂ b₁ b₂ t
    (hHole t ht'.1) ht'.2

/-- The covering theorem yields a concrete cardinality estimate. -/
theorem high_representation_holes_card_le
    (A B Z : Finset G) (a₁ a₂ b₁ b₂ : G)
    (hHole : ∀ t ∈ Z,
      representationFirst (A \ {a₁, a₂}) (B \ {b₁, b₂}) t = ∅) :
    (highRepresentationPoints A B Z).card ≤
      (translate a₁ B ∩ translate a₂ B).card +
        (translate b₁ A ∩ translate b₂ A).card := by
  calc
    (highRepresentationPoints A B Z).card ≤
        ((translate a₁ B ∩ translate a₂ B) ∪
          (translate b₁ A ∩ translate b₂ A)).card :=
      Finset.card_le_card (high_representation_holes_subset A B Z a₁ a₂ b₁ b₂ hHole)
    _ ≤ (translate a₁ B ∩ translate a₂ B).card +
        (translate b₁ A ∩ translate b₂ A).card := Finset.card_union_le _ _

/-- Cap slices satisfy the deletion-hole hypothesis needed by the new cover. -/
theorem cap_slice_deletion_holes [Fintype G]
    {K : Finset (G × ZMod 3)} (hK : IsCap K)
    (A B D₁ D₂ : Finset G)
    (hA : A \ D₁ ⊆ slice K 0) (hB : B \ D₂ ⊆ slice K 1) :
    ∀ t ∈ negativeSet (slice K 2),
      representationFirst (A \ D₁) (B \ D₂) t = ∅ := by
  intro t ht
  rcases Finset.mem_image.mp ht with ⟨c, hc, rfl⟩
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro a ha
  have ha' : a ∈ A \ D₁ ∧ -c - a ∈ B \ D₂ := by
    simpa [representationFirst] using ha
  exact cap_slices_mixed hK a (hA ha'.1) (-c - a) (hB ha'.2) c hc (by abel)

/--
Cap-specific version of the two-plus-two intersection bound.  The right
side counts overlaps of explicit translates, not an assumed hole bound.
-/
theorem cap_two_deletion_high_holes_card_le [Fintype G]
    {K : Finset (G × ZMod 3)} (hK : IsCap K)
    (A B : Finset G) (a₁ a₂ b₁ b₂ : G)
    (hA : A \ {a₁, a₂} ⊆ slice K 0)
    (hB : B \ {b₁, b₂} ⊆ slice K 1) :
    (highRepresentationPoints A B (negativeSet (slice K 2))).card ≤
      (translate a₁ B ∩ translate a₂ B).card +
        (translate b₁ A ∩ translate b₂ A).card := by
  exact high_representation_holes_card_le A B (negativeSet (slice K 2))
    a₁ a₂ b₁ b₂ (cap_slice_deletion_holes hK A B {a₁, a₂} {b₁, b₂} hA hB)

end Capset

#print axioms Capset.representations_card_eq
#print axioms Capset.representation_card_le_deleted
#print axioms Capset.cap_slices_mixed
#print axioms Capset.cap_slice_representation_bound
#print axioms Capset.negative_disjoint_restrictedSumset
#print axioms Capset.card_add_restrictedSumset_le
#print axioms Capset.two_point_cap
#print axioms Capset.two_point_packing_sharp
#print axioms Capset.deletion_bound_sharp

#print axioms Capset.mem_translate_iff
#print axioms Capset.pair_filter_card_le_one
#print axioms Capset.representation_card_le_active_deletions
#print axioms Capset.three_representation_hole_mem_double_translate
#print axioms Capset.high_representation_holes_subset
#print axioms Capset.high_representation_holes_card_le
#print axioms Capset.cap_slice_deletion_holes
#print axioms Capset.cap_two_deletion_high_holes_card_le
