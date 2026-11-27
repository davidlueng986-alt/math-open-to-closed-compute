import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Universal derivative-divisor bound for a (12,18,10) Weierstrass pair

This file proves the entire polynomial statement, not merely scalar formulas:
over every characteristic-zero field, if p, q, S have degrees 12, 18, 10,
q^2 = p^3 + alpha*p + beta + S, and alpha is nonzero, then every polynomial
dividing both actual derivatives p' and q' has degree at most four.

The proof uses an exact polynomial norm identity and a unique highest-degree
term. There are no simple-root, monicity, or analytic normal-form hypotheses.
The geometric passage from a Keller boundary profile to these hypotheses is
separate ordinary mathematics.
-/

noncomputable section

namespace JacobianC2.DerivativeGcdBound

open Polynomial

section Identity

variable {A : Type*} [CommRing A]

/-- An exact ring identity, before specializing the entries to polynomials. -/
theorem norm_identity_core (p q s a b dp dq ds : A)
    (h : q ^ 2 = p ^ 3 + a * p + b + s)
    (hd : 2 * q * dq = 3 * p ^ 2 * dp + a * dp + ds) :
    q ^ 2 * (4 * a * (4 * dq ^ 2 - 9 * p * dp ^ 2) +
        3 * (2 * p * dq - 3 * q * dp) ^ 2) =
      12 * a * p ^ 2 * dp * ds +
        3 * (3 * (s + b) * dp - p * ds) ^ 2 +
        4 * a ^ 3 * dp ^ 2 + 8 * a ^ 2 * dp * ds + 4 * a * ds ^ 2 := by
  have hR : q * (2 * p * dq - 3 * q * dp) =
      p * ds - (3 * s + 2 * a * p + 3 * b) * dp := by
    linear_combination p * hd - 3 * dp * h
  have hB : q ^ 2 * (4 * dq ^ 2 - 9 * p * dp ^ 2) =
      (-3 * a * p ^ 2 + a ^ 2 - 9 * b * p - 9 * p * s) * dp ^ 2 +
        (6 * p ^ 2 + 2 * a) * dp * ds + ds ^ 2 := by
    linear_combination
      (2 * q * dq + 3 * p ^ 2 * dp + a * dp + ds) * hd - 9 * p * dp ^ 2 * h
  calc
    _ = 4 * a * (q ^ 2 * (4 * dq ^ 2 - 9 * p * dp ^ 2)) +
        3 * (q * (2 * p * dq - 3 * q * dp)) ^ 2 := by ring
    _ = 4 * a *
        ((-3 * a * p ^ 2 + a ^ 2 - 9 * b * p - 9 * p * s) * dp ^ 2 +
          (6 * p ^ 2 + 2 * a) * dp * ds + ds ^ 2) +
        3 * (p * ds - (3 * s + 2 * a * p + 3 * b) * dp) ^ 2 := by rw [hB, hR]
    _ = _ := by ring

end Identity

variable {K : Type*} [Field K]

def wronskian (p q : K[X]) : K[X] :=
  2 * p * q.derivative - 3 * q * p.derivative

def normPolynomial (p q : K[X]) (a : K) : K[X] :=
  C (4 * a) * (4 * q.derivative ^ 2 - 9 * p * p.derivative ^ 2) +
    C 3 * wronskian p q ^ 2

def leadingTerm (p s : K[X]) (a : K) : K[X] :=
  C (12 * a) * (p ^ 2 * p.derivative * s.derivative)

def lowerTerms (p s : K[X]) (a b : K) : K[X] :=
  C 3 * (C 3 * (s + C b) * p.derivative - p * s.derivative) ^ 2 +
    C (4 * a ^ 3) * p.derivative ^ 2 +
    C (8 * a ^ 2) * (p.derivative * s.derivative) +
    C (4 * a) * s.derivative ^ 2

/-- The certificate is connected to the actual polynomial derivative. -/
theorem polynomial_norm_identity (p q s : K[X]) (a b : K)
    (h : q ^ 2 = p ^ 3 + C a * p + C b + s) :
    q ^ 2 * normPolynomial p q a = leadingTerm p s a + lowerTerms p s a b := by
  have hd := congrArg Polynomial.derivative h
  simp only [derivative_sq, derivative_pow, derivative_add, derivative_C_mul,
    derivative_C, add_zero] at hd
  norm_num only [C_eq_natCast, pow_one] at hd
  change 2 * q * q.derivative =
    3 * p ^ 2 * p.derivative + C a * p.derivative + s.derivative at hd
  have hn := norm_identity_core p q s (C a) (C b)
    p.derivative q.derivative s.derivative h hd
  unfold normPolynomial wronskian leadingTerm lowerTerms
  simp only [C_mul, C_pow]
  change q ^ 2 * (4 * C a * (4 * q.derivative ^ 2 - 9 * p * p.derivative ^ 2) +
      3 * (2 * p * q.derivative - 3 * q * p.derivative) ^ 2) =
    (12 * C a) * (p ^ 2 * p.derivative * s.derivative) +
      (3 * (3 * (s + C b) * p.derivative - p * s.derivative) ^ 2 +
        (4 * C a ^ 3) * p.derivative ^ 2 +
        (8 * C a ^ 2) * (p.derivative * s.derivative) +
        (4 * C a) * s.derivative ^ 2)
  linear_combination hn

section Degree

variable [CharZero K]

private theorem derivative_degree_of_positive {p : K[X]} {n : ℕ}
    (hp : p.natDegree = n) (hn : 0 < n) : p.derivative.natDegree = n - 1 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · simpa only [hp] using natDegree_derivative_le p
  · rw [coeff_derivative]
    apply mul_ne_zero
    · rw [show n - 1 + 1 = n by omega, ← hp, coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt (by omega : 0 < p.natDegree))
    · exact_mod_cast (show n - 1 + 1 ≠ 0 by omega)

/-- The polynomial on the left of the norm identity has exact degree eight. -/
theorem normPolynomial_degree (p q s : K[X]) (a b : K)
    (hp : p.natDegree = 12) (hq : q.natDegree = 18) (hs : s.natDegree = 10)
    (ha : a ≠ 0) (h : q ^ 2 = p ^ 3 + C a * p + C b + s) :
    (normPolynomial p q a).natDegree = 8 ∧ normPolynomial p q a ≠ 0 := by
  have hpd : p.derivative.natDegree = 11 :=
    derivative_degree_of_positive hp (by norm_num)
  have hsd : s.derivative.natDegree = 9 :=
    derivative_degree_of_positive hs (by norm_num)
  have hp0 : p ≠ 0 := ne_zero_of_natDegree_gt (by omega : 0 < p.natDegree)
  have hq0 : q ≠ 0 := ne_zero_of_natDegree_gt (by omega : 0 < q.natDegree)
  have hpd0 : p.derivative ≠ 0 :=
    ne_zero_of_natDegree_gt (by omega : 0 < p.derivative.natDegree)
  have hsd0 : s.derivative ≠ 0 :=
    ne_zero_of_natDegree_gt (by omega : 0 < s.derivative.natDegree)
  have hlead : (leadingTerm p s a).natDegree = 44 := by
    unfold leadingTerm
    rw [natDegree_C_mul (mul_ne_zero (by norm_num) ha),
      natDegree_mul (mul_ne_zero (pow_ne_zero 2 hp0) hpd0) hsd0,
      natDegree_mul (pow_ne_zero 2 hp0) hpd0, natDegree_pow, hp, hpd, hsd]
  have hsb : (s + C b).natDegree ≤ 10 :=
    natDegree_add_le_of_degree_le hs.le (by simp)
  have hinner :
      (C 3 * (s + C b) * p.derivative - p * s.derivative).natDegree ≤ 21 := by
    apply le_trans (natDegree_sub_le _ _) (max_le _ _)
    · exact (natDegree_mul_le_of_le
        ((natDegree_C_mul_le 3 (s + C b)).trans hsb) hpd.le)
    · exact natDegree_mul_le_of_le hp.le hsd.le
  have ht1 :
      (C 3 * (C 3 * (s + C b) * p.derivative - p * s.derivative) ^ 2).natDegree
        ≤ 42 := by
    exact (natDegree_C_mul_le _ _).trans (natDegree_pow_le_of_le 2 hinner)
  have ht2 : (C (4 * a ^ 3) * p.derivative ^ 2).natDegree ≤ 42 := by
    have hb := (natDegree_C_mul_le (4 * a ^ 3) (p.derivative ^ 2)).trans
      (natDegree_pow_le_of_le 2 hpd.le)
    omega
  have ht3 : (C (8 * a ^ 2) * (p.derivative * s.derivative)).natDegree ≤ 42 := by
    have hb := (natDegree_C_mul_le (8 * a ^ 2) (p.derivative * s.derivative)).trans
      (natDegree_mul_le_of_le hpd.le hsd.le)
    omega
  have ht4 : (C (4 * a) * s.derivative ^ 2).natDegree ≤ 42 := by
    have hb := (natDegree_C_mul_le (4 * a) (s.derivative ^ 2)).trans
      (natDegree_pow_le_of_le 2 hsd.le)
    omega
  have hlow : (lowerTerms p s a b).natDegree ≤ 42 := by
    unfold lowerTerms
    exact natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ht1 ht2) ht3) ht4
  have htotal : (q ^ 2 * normPolynomial p q a).natDegree = 44 := by
    rw [polynomial_norm_identity p q s a b h,
      natDegree_add_eq_left_of_natDegree_lt (by omega), hlead]
  have hnorm0 : normPolynomial p q a ≠ 0 := by
    intro hz
    simp only [hz, mul_zero, natDegree_zero] at htotal
    omega
  have htotal' := htotal
  rw [natDegree_mul (pow_ne_zero 2 hq0) hnorm0, natDegree_pow, hq] at htotal'
  exact ⟨by omega, hnorm0⟩

/-- Every common divisor of the actual derivatives has degree at most four.
Repeated roots and all nonmonic input polynomials are included. -/
theorem common_derivative_divisor_degree_le_four (p q s D : K[X]) (a b : K)
    (hp : p.natDegree = 12) (hq : q.natDegree = 18) (hs : s.natDegree = 10)
    (ha : a ≠ 0) (h : q ^ 2 = p ^ 3 + C a * p + C b + s)
    (hDp : D ∣ p.derivative) (hDq : D ∣ q.derivative) : D.natDegree ≤ 4 := by
  obtain ⟨hdeg, hne⟩ := normPolynomial_degree p q s a b hp hq hs ha h
  obtain ⟨v, hv⟩ := hDp
  obtain ⟨w, hw⟩ := hDq
  have hdiv : D ^ 2 ∣ normPolynomial p q a := by
    refine ⟨C (4 * a) * (4 * w ^ 2 - 9 * p * v ^ 2) +
      C 3 * (2 * p * w - 3 * q * v) ^ 2, ?_⟩
    unfold normPolynomial wronskian
    rw [hv, hw]
    ring
  have hbound := natDegree_le_of_dvd hdiv hne
  rw [natDegree_pow, hdeg] at hbound
  omega

end Degree

#print axioms norm_identity_core
#print axioms polynomial_norm_identity
#print axioms normPolynomial_degree
#print axioms common_derivative_divisor_degree_le_four

end JacobianC2.DerivativeGcdBound
