import Mathlib

/-!
ABC Wave 3: the actual square-area descent, with primitive scope sufficient
for the quartic root escape.  No use is made of `not_fermat_42`.

Pinned Lean: 4.36.0; Mathlib: fc4f59e577feb1a4956671bc04ac18aaaf8cd842.
Compilation status is recorded separately; this source does not assert abc.
-/

set_option maxHeartbeats 1600000

namespace ABCWave3Fermat

private theorem coprime_add_right {a b : ℤ} (h : IsCoprime a b) :
    IsCoprime a (a + b) := by
  rcases h with ⟨u, v, h⟩
  refine ⟨u - v, v, ?_⟩
  linear_combination h

private theorem coprime_sub_right {a b : ℤ} (h : IsCoprime a b) :
    IsCoprime a (a - b) := by
  rcases h with ⟨u, v, h⟩
  refine ⟨u + v, -v, ?_⟩
  linear_combination h

private theorem coprime_sum_difference {m n : ℤ} (h : IsCoprime m n)
    (ho : Odd (m + n)) : IsCoprime (m + n) (m - n) := by
  rcases h with ⟨a, b, hab⟩
  rcases ho.isCoprime_two with ⟨u, v, huv⟩
  refine ⟨u + v * (a + b), v * (a - b), ?_⟩
  linear_combination huv + 2 * v * hab

private theorem positive_square_factor {a b s : ℤ}
    (ha : 0 < a) (hcp : IsCoprime a b) (hs : a * b = s ^ 2) :
    ∃ r : ℤ, 0 < r ∧ a = r ^ 2 := by
  obtain ⟨r, hr⟩ := Int.sq_of_gcd_eq_one
    (Int.isCoprime_iff_gcd_eq_one.mp hcp) hs
  have hr' : a = r ^ 2 := by
    rcases hr with h | h
    · exact h
    · nlinarith [sq_nonneg r]
  refine ⟨|r|, ?_, ?_⟩
  · apply abs_pos.mpr
    intro hz
    simp [hz] at hr'
    omega
  · simpa only [sq_abs] using hr'

/-- A positive primitive integer right triangle whose area is an integer square. -/
structure PrimitiveSquareArea (x y z : ℤ) : Prop where
  xpos : 0 < x
  ypos : 0 < y
  zpos : 0 < z
  triangle : PythagoreanTriple x y z
  coprime : Int.gcd x y = 1
  square_area : ∃ s : ℤ, x * y = 2 * s ^ 2

private theorem odd_square_root {u : ℤ} (h : u ^ 2 % 2 = 1) :
    u % 2 = 1 := by
  rcases Int.emod_two_eq_zero_or_one u with hu | hu
  · norm_num [Int.pow_emod, hu] at h
  · exact hu

/-- The complete descending construction, for an odd first leg. -/
theorem primitive_square_area_descent_odd {x y z : ℤ}
    (h : PrimitiveSquareArea x y z) (hxodd : x % 2 = 1) :
    ∃ p q r : ℤ, PrimitiveSquareArea p q r ∧ r < z := by
  obtain ⟨m, n, hx, hy, hz, hmn, hpar, hm0⟩ :=
    h.triangle.coprime_classification' h.coprime hxodd h.zpos
  have hm : 0 < m := by
    by_contra hm
    have : m = 0 := by omega
    rw [this] at hy
    have := h.ypos
    nlinarith
  have hn : 0 < n := by
    have hprod : 0 < m * n := by nlinarith [h.ypos]
    exact (mul_pos_iff_of_pos_left hm).mp hprod
  have hnm : n < m := by
    by_contra hh
    have hprod := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hh))
      (le_of_lt (add_pos hn hm))
    nlinarith [h.xpos]
  have hplus : 0 < m + n := add_pos hm hn
  have hminus : 0 < m - n := sub_pos.mpr hnm
  have hplusmod : (m + n) % 2 = 1 := by
    rcases hpar with ⟨hm2, hn2⟩ | ⟨hm2, hn2⟩ <;>
      norm_num [Int.add_emod, hm2, hn2]
  have hminusmod : (m - n) % 2 = 1 := by
    rcases hpar with ⟨hm2, hn2⟩ | ⟨hm2, hn2⟩ <;>
      norm_num [Int.sub_emod, hm2, hn2]
  have hplusodd : Odd (m + n) := by
    refine ⟨(m + n) / 2, ?_⟩
    omega
  have cmn : IsCoprime m n := Int.isCoprime_iff_gcd_eq_one.mpr hmn
  have cmp : IsCoprime m (m + n) := coprime_add_right cmn
  have cmm : IsCoprime m (m - n) := coprime_sub_right cmn
  have cnp : IsCoprime n (m + n) := by
    simpa only [add_comm] using coprime_add_right cmn.symm
  have cnm : IsCoprime n (m - n) := by
    simpa only [neg_sub] using (coprime_sub_right cmn.symm).neg_right
  have cpm : IsCoprime (m + n) (m - n) := coprime_sum_difference cmn hplusodd
  obtain ⟨s, hs⟩ := h.square_area
  have hproduct : m * n * (m + n) * (m - n) = s ^ 2 := by
    rw [hx, hy] at hs
    nlinarith [hs]
  obtain ⟨r, hr0, hr⟩ := positive_square_factor hm
    (cmn.mul_right (cmp.mul_right cmm))
    (show m * (n * ((m + n) * (m - n))) = s ^ 2 by
      nlinarith [hproduct])
  obtain ⟨t, ht0, ht⟩ := positive_square_factor hn
    (cmn.symm.mul_right (cnp.mul_right cnm))
    (show n * (m * ((m + n) * (m - n))) = s ^ 2 by
      nlinarith [hproduct])
  obtain ⟨u, hu0, hu⟩ := positive_square_factor hplus
    (cmp.symm.mul_right (cnp.symm.mul_right cpm))
    (show (m + n) * (m * (n * (m - n))) = s ^ 2 by
      nlinarith [hproduct])
  obtain ⟨v, hv0, hv⟩ := positive_square_factor hminus
    (cmm.symm.mul_right (cnm.symm.mul_right cpm.symm))
    (show (m - n) * (m * (n * (m + n))) = s ^ 2 by
      nlinarith [hproduct])
  have huodd : u % 2 = 1 := odd_square_root (by rw [← hu]; exact hplusmod)
  have hvodd : v % 2 = 1 := odd_square_root (by rw [← hv]; exact hminusmod)
  have hvu : v < u := by
    by_contra hh
    have hprod := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hh))
      (le_of_lt (add_pos hv0 hu0))
    nlinarith
  let p : ℤ := (u + v) / 2
  let q : ℤ := (u - v) / 2
  have hp : 2 * p = u + v := by dsimp [p]; omega
  have hq : 2 * q = u - v := by dsimp [q]; omega
  have hp0 : 0 < p := by omega
  have hq0 : 0 < q := by omega
  have hpqu : p + q = u := by omega
  have hpqv : p - q = v := by omega
  have hp2 := congrArg (fun k : ℤ => k ^ 2) hp
  have hq2 := congrArg (fun k : ℤ => k ^ 2) hq
  have hu2 := congrArg (fun k : ℤ => k ^ 2) hpqu
  have hv2 := congrArg (fun k : ℤ => k ^ 2) hpqv
  have hright : p ^ 2 + q ^ 2 = r ^ 2 := by nlinarith only [hp2, hq2, hu, hv, hr]
  have harea : 2 * p * q = t ^ 2 := by nlinarith only [hu2, hv2, hu, hv, ht]
  have htmod : t % 2 = 0 := by
    rcases Int.emod_two_eq_zero_or_one t with hh | hh
    · exact hh
    · have hh2 := congrArg (fun k : ℤ => k % 2) harea
      norm_num [Int.mul_emod, Int.pow_emod, hh] at hh2
  have htdiv : t = 2 * (t / 2) := by omega
  have htdiv2 := congrArg (fun k : ℤ => k ^ 2) htdiv
  have hsquare : p * q = 2 * (t / 2) ^ 2 := by nlinarith only [harea, htdiv2]
  have cuv2 : IsCoprime (u ^ 2) (v ^ 2) := by rwa [← hu, ← hv]
  have cuv : IsCoprime u v := (IsCoprime.pow_iff (by decide : 0 < 2)
    (by decide : 0 < 2)).mp cuv2
  have cpq : IsCoprime p q := by
    rcases cuv with ⟨a, b, hab⟩
    rw [← hpqu, ← hpqv] at hab
    refine ⟨a + b, a - b, ?_⟩
    linear_combination hab
  refine ⟨p, q, r, ?_, ?_⟩
  · refine ⟨hp0, hq0, hr0, ?_, Int.isCoprime_iff_gcd_eq_one.mp cpq,
      ⟨t / 2, hsquare⟩⟩
    change p * p + q * q = r * r
    nlinarith [hright]
  · have hn2 : 0 < n ^ 2 := sq_pos_of_pos hn
    have hrr : r ≤ r ^ 2 := Int.le_self_sq r
    have hmm : m ≤ m ^ 2 := Int.le_self_sq m
    nlinarith

/-- Descending construction with either orientation of the two legs. -/
theorem primitive_square_area_descent {x y z : ℤ}
    (h : PrimitiveSquareArea x y z) :
    ∃ p q r : ℤ, PrimitiveSquareArea p q r ∧ r < z := by
  rcases h.triangle.even_odd_of_coprime h.coprime with heo | hoe
  · have hs : PrimitiveSquareArea y x z := by
      refine ⟨h.ypos, h.xpos, h.zpos, h.triangle.symm, ?_, ?_⟩
      · simpa only [Int.gcd_comm] using h.coprime
      · obtain ⟨s, hs⟩ := h.square_area
        exact ⟨s, by nlinarith [hs]⟩
    exact primitive_square_area_descent_odd hs heo.2
  · exact primitive_square_area_descent_odd h hoe.1

/-- Fermat's square-area theorem in primitive positive integer scope. -/
theorem no_primitive_square_area (x y z : ℤ) : ¬ PrimitiveSquareArea x y z := by
  have all_n : ∀ n : ℕ, ∀ x y z : ℤ, z.natAbs = n →
      PrimitiveSquareArea x y z → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x y z hz h
      obtain ⟨p, q, r, hnew, hlt⟩ := primitive_square_area_descent h
      have habs : r.natAbs < z.natAbs := by
        apply Int.ofNat_lt.mp
        rw [← Int.eq_natAbs_of_nonneg (le_of_lt hnew.zpos),
          ← Int.eq_natAbs_of_nonneg (le_of_lt h.zpos)]
        exact hlt
      rw [hz] at habs
      exact ih r.natAbs habs p q r rfl hnew
  exact all_n z.natAbs x y z rfl

/-- The difference-of-fourths theorem needed for ABC's quartic root escape.
It has the minus sign, and it concludes non-squareness, not merely nonzero.
-/
theorem fourth_difference_not_square (b c w : ℤ)
    (hb : 0 < b) (hbc : b < c) (hcp : Int.gcd c b = 1)
    (hcodd : c % 2 = 1) (hbeven : b % 2 = 0) :
    c ^ 4 - b ^ 4 ≠ w ^ 2 := by
  intro heq
  have hc : 0 < c := lt_trans hb hbc
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  have hbc2 : b ^ 2 < c ^ 2 := by
    have hh := mul_pos (sub_pos.mpr hbc) (add_pos hc hb)
    nlinarith
  have hbc4 : b ^ 4 < c ^ 4 := by
    have hh := mul_pos (sub_pos.mpr hbc2) (add_pos hc2 hb2)
    nlinarith
  have hparam : PythagoreanTriple (c ^ 4 - b ^ 4) (2 * c ^ 2 * b ^ 2)
      (c ^ 4 + b ^ 4) ∧ Int.gcd (c ^ 4 - b ^ 4) (2 * c ^ 2 * b ^ 2) = 1 := by
    apply PythagoreanTriple.coprime_classification.mpr
    refine ⟨c ^ 2, b ^ 2, Or.inl ⟨?_, rfl⟩, Or.inl ?_, ?_, Or.inr ⟨?_, ?_⟩⟩
    · ring
    · ring
    · exact Int.isCoprime_iff_gcd_eq_one.mp
        (Int.isCoprime_iff_gcd_eq_one.mpr hcp).pow
    · norm_num [Int.pow_emod, hcodd]
    · norm_num [Int.pow_emod, hbeven]
  apply no_primitive_square_area (c ^ 4 - b ^ 4) (2 * c ^ 2 * b ^ 2)
    (c ^ 4 + b ^ 4)
  refine ⟨sub_pos.mpr hbc4, by positivity, by positivity, hparam.1, hparam.2,
    ⟨b * c * w, ?_⟩⟩
  linear_combination 2 * b ^ 2 * c ^ 2 * heq

#print axioms primitive_square_area_descent_odd
#print axioms primitive_square_area_descent
#print axioms no_primitive_square_area
#print axioms fourth_difference_not_square

end ABCWave3Fermat
