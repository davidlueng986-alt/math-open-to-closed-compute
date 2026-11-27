import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Actual coefficient certificates for the complete (6,9,5) normal form

The polynomial definitions are the actual normal-form pair P and Q8 = 8 Q.
The cubic determinant and fifth numerator below are defined from their
Polynomial.coeff values, not from assumed scalar formulas. Scaling Q by eight
scales each determinant by eight and does not change its vanishing in
characteristic zero.

The file proves the coefficient extraction, reduction certificates, and
nonvanishing statements used by NORMALFORM-695.md. It does not postulate an
analytic change of coordinates or a Puiseux classification as an axiom.
-/

noncomputable section

namespace JacobianC2.CuspJets695

open Polynomial

variable {K : Type*} [Field K]

def R (b c : K) : K[X] :=
  (X + C b) * (X ^ 2 + C b * X + C (2 * c))

def S (b c : K) : K[X] := X ^ 2 + C b * X + C c

def P (b c : K) : K[X] := R b c ^ 2 + S b c

def Q8 (b c : K) : K[X] :=
  8 * R b c ^ 3 + 12 * R b c * S b c + 3 * X

def G (b c : K) : K := 4 * b ^ 2 * c + 8 * c ^ 2 + 1

def F (c : K) : K := 160 * c ^ 4 + 40 * c ^ 2 - 1

def H (b c : K) : K := b ^ 2 + 40 * c ^ 3 + 12 * c

def a2 (b c : K) : K := b ^ 4 + 12 * b ^ 2 * c + 4 * c ^ 2 + 1
def a3 (b c : K) : K := 4 * b ^ 3 + 12 * b * c
def a4 (b c : K) : K := 6 * b ^ 2 + 4 * c
def a5 (b : K) : K := 4 * b

def q2 (b c : K) : K :=
  48 * b ^ 5 * c + 384 * b ^ 3 * c ^ 2 + 12 * b ^ 3 +
    192 * b * c ^ 3 + 72 * b * c
def q3 (b c : K) : K :=
  8 * b ^ 6 + 240 * b ^ 4 * c + 576 * b ^ 2 * c ^ 2 +
    36 * b ^ 2 + 64 * c ^ 3 + 36 * c
def q4 (b c : K) : K :=
  48 * b ^ 5 + 480 * b ^ 3 * c + 384 * b * c ^ 2 + 36 * b
def q5 (b c : K) : K :=
  120 * b ^ 4 + 480 * b ^ 2 * c + 96 * c ^ 2 + 12

/-- Full polynomial equality supplying the actual first-coordinate jets. -/
theorem P_expanded (b c : K) :
    P b c = C (4 * b ^ 2 * c ^ 2 + c) + C (b * G b c) * X +
      C (a2 b c) * X ^ 2 + C (a3 b c) * X ^ 3 +
      C (a4 b c) * X ^ 4 + C (a5 b) * X ^ 5 + X ^ 6 := by
  simp only [P, R, S, G, a2, a3, a4, a5, C_add, C_mul, C_pow, map_one]
  change ((X + C b) * (X ^ 2 + C b * X + 2 * C c)) ^ 2 +
      (X ^ 2 + C b * X + C c) =
    (4 * C b ^ 2 * C c ^ 2 + C c) +
      (C b * (4 * C b ^ 2 * C c + 8 * C c ^ 2 + 1)) * X +
      (C b ^ 4 + 12 * C b ^ 2 * C c + 4 * C c ^ 2 + 1) * X ^ 2 +
      (4 * C b ^ 3 + 12 * C b * C c) * X ^ 3 +
      (6 * C b ^ 2 + 4 * C c) * X ^ 4 + (4 * C b) * X ^ 5 + X ^ 6
  ring

/-- Full polynomial equality supplying the actual second-coordinate jets. -/
theorem Q8_expanded (b c : K) :
    Q8 b c = C (64 * b ^ 3 * c ^ 3 + 24 * b * c ^ 2) +
      C (3 * (8 * b ^ 2 * c + 1) * G b c) * X +
      C (q2 b c) * X ^ 2 + C (q3 b c) * X ^ 3 +
      C (q4 b c) * X ^ 4 + C (q5 b c) * X ^ 5 +
      C (160 * b ^ 3 + 240 * b * c) * X ^ 6 +
      C (120 * b ^ 2 + 48 * c) * X ^ 7 + C (48 * b) * X ^ 8 +
      C 8 * X ^ 9 := by
  simp only [Q8, R, S, G, q2, q3, q4, q5, C_add, C_mul, C_pow, map_one]
  change 8 * ((X + C b) * (X ^ 2 + C b * X + 2 * C c)) ^ 3 +
      12 * ((X + C b) * (X ^ 2 + C b * X + 2 * C c)) *
        (X ^ 2 + C b * X + C c) + 3 * X =
    (64 * C b ^ 3 * C c ^ 3 + 24 * C b * C c ^ 2) +
      (3 * (8 * C b ^ 2 * C c + 1) *
        (4 * C b ^ 2 * C c + 8 * C c ^ 2 + 1)) * X +
      (48 * C b ^ 5 * C c + 384 * C b ^ 3 * C c ^ 2 + 12 * C b ^ 3 +
        192 * C b * C c ^ 3 + 72 * C b * C c) * X ^ 2 +
      (8 * C b ^ 6 + 240 * C b ^ 4 * C c + 576 * C b ^ 2 * C c ^ 2 +
        36 * C b ^ 2 + 64 * C c ^ 3 + 36 * C c) * X ^ 3 +
      (48 * C b ^ 5 + 480 * C b ^ 3 * C c + 384 * C b * C c ^ 2 +
        36 * C b) * X ^ 4 +
      (120 * C b ^ 4 + 480 * C b ^ 2 * C c + 96 * C c ^ 2 + 12) * X ^ 5 +
      (160 * C b ^ 3 + 240 * C b * C c) * X ^ 6 +
      (120 * C b ^ 2 + 48 * C c) * X ^ 7 + (48 * C b) * X ^ 8 + 8 * X ^ 9
  ring

theorem P_coeff_two (b c : K) : (P b c).coeff 2 = a2 b c := by
  rw [P_expanded]
  norm_num only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X_pow, coeff_C, ite_true, ite_false, zero_add, add_zero]

theorem P_coeff_three (b c : K) : (P b c).coeff 3 = a3 b c := by
  rw [P_expanded]
  norm_num only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X_pow, coeff_C, ite_true, ite_false, zero_add, add_zero]

theorem P_coeff_four (b c : K) : (P b c).coeff 4 = a4 b c := by
  rw [P_expanded]
  norm_num only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X_pow, coeff_C, ite_true, ite_false, zero_add, add_zero]

theorem P_coeff_five (b c : K) : (P b c).coeff 5 = a5 b := by
  rw [P_expanded]
  norm_num only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X_pow, coeff_C, ite_true, ite_false, zero_add, add_zero]

theorem Q8_coeff_two (b c : K) : (Q8 b c).coeff 2 = q2 b c := by
  rw [Q8_expanded]
  norm_num only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X_pow, coeff_C, ite_true, ite_false, zero_add, add_zero]

theorem Q8_coeff_three (b c : K) : (Q8 b c).coeff 3 = q3 b c := by
  rw [Q8_expanded]
  norm_num only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X_pow, coeff_C, ite_true, ite_false, zero_add, add_zero]

theorem Q8_coeff_four (b c : K) : (Q8 b c).coeff 4 = q4 b c := by
  rw [Q8_expanded]
  norm_num only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X_pow, coeff_C, ite_true, ite_false, zero_add, add_zero]

theorem Q8_coeff_five (b c : K) : (Q8 b c).coeff 5 = q5 b c := by
  rw [Q8_expanded]
  norm_num only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X_pow, coeff_C, ite_true, ite_false, zero_add, add_zero]

/-- Eight times the ordinary cubic determinant for (P,Q). -/
def cubicDet8 (b c : K) : K :=
  (P b c).coeff 2 * (Q8 b c).coeff 3 -
    (P b c).coeff 3 * (Q8 b c).coeff 2

/-- Eight times the fifth-order numerator after the cubic determinant vanishes. -/
def fifthNumerator8 (b c : K) : K :=
  (P b c).coeff 2 ^ 2 * (Q8 b c).coeff 5 -
    (P b c).coeff 2 * (Q8 b c).coeff 2 * (P b c).coeff 5 -
    2 * (P b c).coeff 2 * (P b c).coeff 3 * (Q8 b c).coeff 4 +
    2 * (P b c).coeff 3 * (Q8 b c).coeff 2 * (P b c).coeff 4

def J3 (b c : K) : K :=
  256 * b ^ 8 * c ^ 4 + b ^ 6 * (4096 * c ^ 5 - 64 * c ^ 3) +
    b ^ 4 * (35840 * c ^ 6 - 1024 * c ^ 4 + 16 * c ^ 2) +
    b ^ 2 * (10240 * c ^ 7 + 1920 * c ^ 5 + 224 * c ^ 3 - 4 * c) +
    4096 * c ^ 8 + 2816 * c ^ 6 + 224 * c ^ 4 - 48 * c ^ 2 + 1

/-- This identity is proved from the actual Polynomial.coeff determinants. -/
theorem cubic_reduction_certificate (b c : K) :
    128 * c ^ 5 * cubicDet8 b c = F c + G b c * J3 b c := by
  rw [cubicDet8, P_coeff_two, P_coeff_three, Q8_coeff_two, Q8_coeff_three]
  unfold a2 a3 q2 q3 F G J3
  ring

theorem exceptional_locus_certificate (b c : K) :
    4 * c * H b c = G b c + F c := by
  unfold H G F
  ring

theorem second_reduction_certificate (b c : K) :
    2 * (P b c).coeff 2 - 3 * (1 - 4 * c ^ 2) =
      2 * (b ^ 2 - 40 * c ^ 3) * H b c + (20 * c ^ 2 + 1) * F c := by
  rw [P_coeff_two]
  unfold a2 H F
  ring

theorem cusp_parameter_nonzero (b c : K) (hG : G b c = 0) : c ≠ 0 := by
  intro hc
  simp [G, hc] at hG

def J5H2 (b c : K) : K :=
  -60096 * c ^ 3
    + -66 * b ^ 10
    + -48 * b ^ 2
    + 27 * b ^ 6
    + 480 * c
    + 2553792 * c ^ 5
    + 73566720 * c ^ 7
    + 707136000 * c ^ 9
    + 3282432000 * c ^ 11
    + 6758400000 * c ^ 15
    + 7495680000 * c ^ 13
    + -168960000 * b ^ 2 * c ^ 12
    + -136704000 * b ^ 2 * c ^ 10
    + -41049600 * b ^ 2 * c ^ 8
    + -5363520 * b ^ 2 * c ^ 6
    + -230112 * b ^ 2 * c ^ 4
    + -105600 * b ^ 6 * c ^ 6
    + -22080 * b ^ 6 * c ^ 4
    + -2904 * b ^ 6 * c ^ 2
    + -492 * b ^ 4 * c
    + -240 * b ^ 8 * c
    + 2640 * b ^ 8 * c ^ 3
    + 5160 * b ^ 2 * c ^ 2
    + 19752 * b ^ 4 * c ^ 3
    + 381120 * b ^ 4 * c ^ 5
    + 2150400 * b ^ 4 * c ^ 7
    + 4224000 * b ^ 4 * c ^ 9

def J5F (c : K) : K :=
  -33630
    + -156672000000 * c ^ 12
    + -135168000000 * c ^ 14
    + -72299520000 * c ^ 10
    + -16741632000 * c ^ 8
    + -1980614400 * c ^ 6
    + -101957760 * c ^ 4
    + -1010040 * c ^ 2

/-- The fifth numerator is reduced using the explicit H,F multipliers.
All denominators from the rational certificate have been cleared. -/
theorem fifth_reduction_certificate (b c : K) :
    20 * fifthNumerator8 b c + 210 * (580 * c ^ 2 + 159) =
      80 * J5H2 b c * H b c + J5F c * F c := by
  rw [fifthNumerator8, P_coeff_two, P_coeff_three, P_coeff_four, P_coeff_five,
    Q8_coeff_two, Q8_coeff_four, Q8_coeff_five]
  unfold a2 a3 a4 a5 q2 q4 q5 J5H2 J5F H F
  ring

def J0 (b c : K) : K :=
  32 * b ^ 4 * c ^ 2 + b ^ 2 * (64 * c ^ 3 + 4 * c) - 8 * c ^ 2 - 1

/-- The actual second-order vector never vanishes on the cusp locus. -/
theorem second_vector_certificate (b c : K) :
    16 * b * c ^ 2 * (Q8 b c).coeff 2 -
      48 * c ^ 2 * (8 * b ^ 2 * c + 1) * (P b c).coeff 2 =
      3 + 3 * G b c * J0 b c := by
  rw [P_coeff_two, Q8_coeff_two]
  unfold a2 q2 G J0
  ring

theorem second_nonvanishing_certificate (c : K) :
    F c + (40 * c ^ 2 + 20) * (1 - 4 * c ^ 2) = 19 := by
  unfold F
  ring

theorem fifth_nonvanishing_certificate (c : K) :
    4205 * F c - (1160 * c ^ 2 - 28) * (580 * c ^ 2 + 159) = 247 := by
  unfold F
  ring

section Nonvanishing

variable [CharZero K]

theorem second_vector_nonzero (b c : K) (hG : G b c = 0) :
    ¬ ((P b c).coeff 2 = 0 ∧ (Q8 b c).coeff 2 = 0) := by
  rintro ⟨hp, hq⟩
  have h := second_vector_certificate b c
  rw [hp, hq, hG] at h
  norm_num at h

theorem cubic_zero_iff (b c : K) (hG : G b c = 0) :
    cubicDet8 b c = 0 ↔ F c = 0 := by
  have hc := cusp_parameter_nonzero b c hG
  have hid : 128 * c ^ 5 * cubicDet8 b c = F c := by
    simpa only [hG, zero_mul, add_zero] using cubic_reduction_certificate b c
  constructor
  · intro h
    simpa only [h, mul_zero] using hid.symm
  · intro h
    have hz := hid.trans h
    exact (mul_eq_zero.mp hz).resolve_left
      (mul_ne_zero (by norm_num) (pow_ne_zero 5 hc))

/-- The ordinary-cusp test uses actual second/third polynomial coefficients. -/
theorem ordinary_cubic_nonzero_iff (b c : K) (hG : G b c = 0) :
    cubicDet8 b c ≠ 0 ↔ F c ≠ 0 :=
  not_congr (cubic_zero_iff b c hG)

theorem exceptional_H_zero (b c : K) (hG : G b c = 0) (hF : F c = 0) :
    H b c = 0 := by
  have hc := cusp_parameter_nonzero b c hG
  have hz : 4 * c * H b c = 0 := by
    simpa only [hG, hF, add_zero] using exceptional_locus_certificate b c
  exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) hc)

/-- The actual coefficient of X² in P survives on the exceptional locus. -/
theorem exceptional_actual_second_nonzero (b c : K)
    (hG : G b c = 0) (hF : F c = 0) : (P b c).coeff 2 ≠ 0 := by
  have hH := exceptional_H_zero b c hG hF
  have hunit : 1 - 4 * c ^ 2 ≠ 0 := by
    intro hzero
    have h := second_nonvanishing_certificate c
    rw [hF, hzero] at h
    norm_num at h
  intro hp
  have h := second_reduction_certificate b c
  rw [hp, hH, hF] at h
  have hz : 3 * (1 - 4 * c ^ 2) = 0 := by
    linear_combination -h
  exact mul_ne_zero (by norm_num) hunit hz

/-- The fifth-order numerator is nonzero on the exceptional
cubic-zero locus. The statement refers to actual polynomial coefficients. -/
theorem exceptional_actual_fifth_nonzero (b c : K)
    (hG : G b c = 0) (hF : F c = 0) : fifthNumerator8 b c ≠ 0 := by
  have hH := exceptional_H_zero b c hG hF
  have hunit : 580 * c ^ 2 + 159 ≠ 0 := by
    intro hzero
    have h := fifth_nonvanishing_certificate c
    rw [hF, hzero] at h
    norm_num at h
  intro hc5
  have h := fifth_reduction_certificate b c
  rw [hc5, hH, hF] at h
  have hz : 210 * (580 * c ^ 2 + 159) = 0 := by
    simpa using h
  exact mul_ne_zero (by norm_num) hunit hz

/-- Complete coefficient-level alternatives used by the ordinary analytic
cusp classification. No analytic normal-form theorem is assumed. -/
theorem actual_cusp_jet_alternatives (b c : K) (hG : G b c = 0) :
    ¬ ((P b c).coeff 2 = 0 ∧ (Q8 b c).coeff 2 = 0) ∧
    (cubicDet8 b c ≠ 0 ↔ F c ≠ 0) ∧
    (F c = 0 → cubicDet8 b c = 0 ∧ (P b c).coeff 2 ≠ 0 ∧
      fifthNumerator8 b c ≠ 0) := by
  refine ⟨second_vector_nonzero b c hG, ordinary_cubic_nonzero_iff b c hG, ?_⟩
  intro hF
  exact ⟨(cubic_zero_iff b c hG).mpr hF,
    exceptional_actual_second_nonzero b c hG hF,
    exceptional_actual_fifth_nonzero b c hG hF⟩

end Nonvanishing

#print axioms P_expanded
#print axioms Q8_expanded
#print axioms cubic_reduction_certificate
#print axioms second_reduction_certificate
#print axioms fifth_reduction_certificate
#print axioms second_vector_certificate
#print axioms ordinary_cubic_nonzero_iff
#print axioms exceptional_actual_second_nonzero
#print axioms exceptional_actual_fifth_nonzero
#print axioms actual_cusp_jet_alternatives

end JacobianC2.CuspJets695

