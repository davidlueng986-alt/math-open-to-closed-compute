import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.LinearCombination

namespace Erdos25

/-- The affine change of variables converts exactly the activated hits to restricted multiples. -/
theorem affine_quotient_iff (n a m d b c : ℤ) (hn : 0 < n) (ha : 0 ≤ a ∧ a < n)
    (hd : 0 < d) (hy : 0 < d * m - b) (profile : d * a = b + c * n) :
    (∃ t : ℤ, 1 ≤ t ∧ m = a + n * t) ↔
    n ≤ m ∧ ∃ q : ℤ, 0 < q ∧ d * m - b = n * q ∧ q ≡ c [ZMOD d] := by
  constructor
  · rintro ⟨t, ht, hit⟩
    have nle : n ≤ n * t := by simpa using mul_le_mul_of_nonneg_left ht hn.le
    have multiple : d * m - b = n * (c + d * t) := by
      linear_combination d * hit + profile
    refine ⟨by omega, c + d * t, ?_, multiple, ?_⟩
    · have positiveProduct : 0 < n * (c + d * t) := multiple ▸ hy
      by_contra! nonpositive
      exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hn.le nonpositive)) positiveProduct
    · exact Int.modEq_iff_dvd.mpr ⟨-t, by rw [mul_neg]; omega⟩
  · rintro ⟨active, q, _, multiple, congruence⟩
    obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.mp congruence.symm
    have canceled : d * (m - a - n * t) = 0 := by
      linear_combination multiple - profile + n * ht
    have hit : m = a + n * t := by
      have zero : m - a - n * t = 0 := (mul_eq_zero.mp canceled).resolve_left hd.ne'
      omega
    refine ⟨t, ?_, hit⟩
    by_contra! before
    have nonpositive : n * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hn.le (by omega)
    omega

/-- In one group of fixed prime part and unit residue, the quotient condition is one congruence. -/
theorem restricted_quotient_iff (g u y d r c : ℕ) (hg : 0 < g) (hu : 0 < u)
    (coprime : d.Coprime u) (residue : u ≡ r [MOD d]) :
    (∃ q : ℕ, 0 < q ∧ y = g * (u * q) ∧ q ≡ c [MOD d]) ↔
    0 < y ∧ g ∣ y ∧ u ∣ y / g ∧ y / g ≡ r * c [MOD d] := by
  constructor
  · rintro ⟨q, hq, hy, hmod⟩
    have quotient : y / g = u * q := by rw [hy, Nat.mul_div_cancel_left _ hg]
    exact ⟨hy.symm ▸ Nat.mul_pos hg (Nat.mul_pos hu hq), ⟨u * q, hy⟩, ⟨q, quotient⟩,
      quotient.symm ▸ residue.mul hmod⟩
  · rintro ⟨hy, hgDiv, ⟨q, hq⟩, hmod⟩
    have multiple : y = g * (u * q) := by rw [← hq, Nat.mul_div_cancel' hgDiv]
    have positive : 0 < q := by
      by_contra! h
      have qzero : q = 0 := Nat.eq_zero_of_le_zero h
      simp [multiple, qzero] at hy
    have congruence : u * q ≡ u * c [MOD d] := by
      rw [hq] at hmod
      exact hmod.trans (residue.mul_right c).symm
    exact ⟨q, positive, multiple, Nat.ModEq.cancel_left_of_coprime coprime congruence⟩

end Erdos25

#print axioms Erdos25.affine_quotient_iff
#print axioms Erdos25.restricted_quotient_iff

