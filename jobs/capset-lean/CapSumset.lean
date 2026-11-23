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
  decide

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
