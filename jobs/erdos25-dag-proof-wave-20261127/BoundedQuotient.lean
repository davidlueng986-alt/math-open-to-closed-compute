import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace Erdos25

open scoped BigOperators

private theorem card_union_le_of_nested {ι β : Type*} [DecidableEq β]
    (I : Finset ι) (before after : ι → Finset β)
    (sameCard : ∀ i ∈ I, (before i).card = (after i).card)
    (nested : ∀ i ∈ I, ∀ j ∈ I, after i ⊆ after j ∨ after j ⊆ after i) :
    (I.biUnion after).card ≤ (I.biUnion before).card := by
  by_cases nonempty : I.Nonempty
  · obtain ⟨j, hj, largest⟩ := I.exists_max_image (fun i => (after i).card) nonempty
    have contained : I.biUnion after ⊆ after j := Finset.biUnion_subset.mpr (by
      intro i hi
      rcases nested i hi j hj with h | h
      · exact h
      · have eq := Finset.eq_of_subset_of_card_le h (largest i hi)
        rw [eq])
    calc
      (I.biUnion after).card ≤ (after j).card := Finset.card_le_card contained
      _ = (before j).card := (sameCard j hj).symm
      _ ≤ (I.biUnion before).card := Finset.card_le_card (Finset.subset_biUnion_of_mem before hj)
  · simp [Finset.not_nonempty_iff_eq_empty.mp nonempty]

private theorem card_rectangles_eq_sum_fibers {ι α β : Type*} [DecidableEq α] [DecidableEq β]
    (I : Finset ι) (rows : ι → Finset α) (cols : ι → Finset β) :
    (I.biUnion fun i => rows i ×ˢ cols i).card =
    ∑ r ∈ I.biUnion rows, ((I.filter fun i => r ∈ rows i).biUnion cols).card := by
  let fiber (r : α) := (I.filter fun i => r ∈ rows i).biUnion cols
  let rectangle (r : α) := {r} ×ˢ fiber r
  have representation : (I.biUnion fun i => rows i ×ˢ cols i) = (I.biUnion rows).biUnion rectangle := by
    ext ⟨r, c⟩
    simp only [rectangle, fiber, Finset.mem_biUnion, Finset.mem_product, Finset.mem_singleton,
      Finset.mem_filter]
    constructor
    · rintro ⟨i, hi, hr, hc⟩
      exact ⟨r, ⟨i, hi, hr⟩, rfl, ⟨i, ⟨hi, hr⟩, hc⟩⟩
    · rintro ⟨r', _, rfl, i, ⟨hi, hr⟩, hc⟩
      exact ⟨i, hi, hr, hc⟩
  have separated : ((I.biUnion rows : Finset α) : Set α).PairwiseDisjoint rectangle := by
    intro r _ r' _ different
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    have atR := Finset.mem_singleton.mp (Finset.mem_product.mp hz).1
    have atR' := Finset.mem_singleton.mp (Finset.mem_product.mp hz').1
    exact different (atR.symm.trans atR')
  rw [representation, Finset.card_biUnion separated]
  simp only [rectangle, fiber, Finset.card_product, Finset.card_singleton, one_mul]

/-- Compress one coordinate by replacing each fiber with a nested fiber of the same size. -/
theorem card_rectangles_le_of_nested {ι α β : Type*} [DecidableEq α] [DecidableEq β]
    (I : Finset ι) (rows : ι → Finset α) (before after : ι → Finset β)
    (sameCard : ∀ i ∈ I, (before i).card = (after i).card)
    (nested : ∀ i ∈ I, ∀ j ∈ I, after i ⊆ after j ∨ after j ⊆ after i) :
    (I.biUnion fun i => rows i ×ˢ after i).card ≤
    (I.biUnion fun i => rows i ×ˢ before i).card := by
  rw [card_rectangles_eq_sum_fibers, card_rectangles_eq_sum_fibers]
  apply Finset.sum_le_sum
  intro r _
  exact card_union_le_of_nested _ before after
    (fun i hi => sameCard i (Finset.mem_filter.mp hi).1)
    (fun i hi j hj => nested i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1)

private theorem sum_image_le {ι α : Type*} [DecidableEq α]
    (I : Finset ι) (f : ι → α) (w : α → ℝ) (nonneg : ∀ x, 0 ≤ w x) :
    (∑ y ∈ I.image f, w y) ≤ ∑ x ∈ I, w (f x) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert x I hx ih =>
    rw [Finset.image_insert, Finset.sum_insert hx]
    by_cases hm : f x ∈ I.image f
    · rw [Finset.insert_eq_of_mem hm]
      exact ih.trans (le_add_of_nonneg_left (nonneg (f x)))
    · rw [Finset.sum_insert hm]
      exact add_le_add_right ih _

/-- Count each activated hit once, then bound its weight using its positive quotient. -/
theorem sum_delayed_hits_le (F : Finset ℕ) (a : ℕ → ℕ) (T : ℕ) (w : ℕ → ℝ)
    (moduliPositive : ∀ n ∈ F, 0 < n) (nonneg : ∀ m, 0 ≤ w m)
    (decreasing : ∀ ⦃k m⦄, 0 < k → k ≤ m → w m ≤ w k)
    (multiplicative : ∀ ⦃n t⦄, 0 < n → 0 < t → w (n * t) = w n * w t) :
    (∑ m ∈ (F ×ˢ Finset.Icc 1 T).image (fun p => a p.1 + p.1 * p.2), w m) ≤
      (∑ n ∈ F, w n) * ∑ t ∈ Finset.Icc 1 T, w t := by
  calc
    _ ≤ ∑ p ∈ F ×ˢ Finset.Icc 1 T, w (a p.1 + p.1 * p.2) := sum_image_le _ _ w nonneg
    _ ≤ ∑ p ∈ F ×ˢ Finset.Icc 1 T, w p.1 * w p.2 := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hn, ht⟩ := Finset.mem_product.mp hp
      have hnPos := moduliPositive p.1 hn
      have htPos := (Finset.mem_Icc.mp ht).1
      rw [← multiplicative hnPos htPos]
      exact decreasing (Nat.mul_pos hnPos htPos) (Nat.le_add_left _ _)
    _ = _ := by
      rw [Finset.sum_product, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n _
      rw [Finset.mul_sum]

end Erdos25

#print axioms Erdos25.card_rectangles_le_of_nested
#print axioms Erdos25.sum_delayed_hits_le

