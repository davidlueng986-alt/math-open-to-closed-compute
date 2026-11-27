import Mathlib.Tactic

/-!
Unbounded integer classification of the equality case in the weighted local
cusp formula. The analytic reduction to these explicit conditions is proved
in QUASIHOMOGENEOUS-EQUALITY.md, not postulated as a custom axiom.
-/

namespace JC2.CuspEquality

/-- The corrected polar identity yields a weak lower bound; tangent degree
alone supplies no strict inequality. -/
theorem corrected_polar_bound (K r c mu : ℤ) (hc : 2 ≤ c) (hmu : 0 ≤ mu)
    (hid : (K - r) * (c - 1) = mu) : r ≤ K := by
  by_contra hn
  have hp := mul_nonneg (show 0 ≤ r - K - 1 by omega) (show 0 ≤ c - 1 by omega)
  nlinarith

theorem corrected_polar_equality (K r c mu : ℤ) (hc : 2 ≤ c)
    (hid : (K - r) * (c - 1) = mu) : K = r ↔ mu = 0 := by
  constructor
  · intro h
    subst K
    simpa using hid.symm
  · intro h
    rw [h] at hid
    rcases mul_eq_zero.mp hid with hleft | hright
    · omega
    · omega

theorem classify_equality (a b r e L : ℤ)
    (ha : 2 ≤ a) (hab : a < b) (hr : 1 ≤ r)
    (hL : L = r * (a * b - a - b) + 1)
    (hdegree : e * L = r * (a + b) - 1)
    (hfinite : L ∣ a ∨ L ∣ b) :
    a = 2 ∧ b = 3 ∧ ((r = 1 ∧ e = 2) ∨ (r = 2 ∧ e = 3)) := by
  have hb : 3 ≤ b := by omega
  have ht : 1 ≤ a * b - a - b := by
    have hp := mul_nonneg (show 0 ≤ a - 2 by omega) (show 0 ≤ b - 3 by omega)
    nlinarith
  have hbase : a * b - a - b + 1 ≤ L := by
    have hp := mul_nonneg (show 0 ≤ r - 1 by omega) (show 0 ≤ a * b - a - b by omega)
    nlinarith [hL]
  have hLpos : 0 < L := by omega
  have hupper : L ≤ b := by
    rcases hfinite with hd | hd
    · have hx : L ≤ a := Int.le_of_dvd (by omega) hd
      omega
    · exact Int.le_of_dvd (by omega) hd
  have haeq : a = 2 := by
    by_contra hn
    have ha3 : 3 ≤ a := by omega
    have hb4 : 4 ≤ b := by omega
    have hp := mul_nonneg (show 0 ≤ a - 3 by omega) (show 0 ≤ b - 4 by omega)
    nlinarith
  subst a
  have hLs : L = r * (b - 2) + 1 := by nlinarith [hL]
  rcases hfinite with hd | hd
  · have hu : L ≤ 2 := Int.le_of_dvd (by norm_num) hd
    have hp := mul_nonneg (show 0 ≤ r by omega) (show 0 ≤ b - 3 by omega)
    have hr1 : r = 1 := by nlinarith
    have hb3 : b = 3 := by nlinarith [hLs]
    have he2 : e = 2 := by subst r; subst b; norm_num at hLs; nlinarith
    exact ⟨rfl, hb3, Or.inl ⟨hr1, he2⟩⟩
  · have hr2 : 2 ≤ r := by
      by_contra hn
      have hr1 : r = 1 := by omega
      have hs : b - L = 1 := by nlinarith [hLs]
      have hone : L ∣ 1 := by simpa only [hs] using dvd_sub hd (dvd_refl L)
      have hu : L ≤ 1 := Int.le_of_dvd (by norm_num) hone
      omega
    have hp := mul_nonneg (show 0 ≤ r - 2 by omega) (show 0 ≤ b - 3 by omega)
    have hrb : r = 2 ∧ b = 3 := by constructor <;> nlinarith [hLs]
    have he3 : e = 3 := by rcases hrb with ⟨rfl, rfl⟩; norm_num at hLs; nlinarith
    exact ⟨rfl, hrb.2, Or.inr ⟨hrb.1, he3⟩⟩

theorem normal_index_le_three (a b r e L : ℤ)
    (ha : 2 ≤ a) (hab : a < b) (hr : 1 ≤ r)
    (hL : L = r * (a * b - a - b) + 1)
    (hdegree : e * L = r * (a + b) - 1)
    (hfinite : L ∣ a ∨ L ∣ b) : e ≤ 3 := by
  obtain ⟨_, _, h⟩ := classify_equality a b r e L ha hab hr hL hdegree hfinite
  rcases h with h | h <;> omega

#print axioms classify_equality
#print axioms normal_index_le_three
#print axioms corrected_polar_bound
#print axioms corrected_polar_equality

end JC2.CuspEquality
