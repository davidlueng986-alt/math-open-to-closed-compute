import Mathlib

/-!
Algebraic certificate for the complete (6,9,5) normal form.
The ordinary Laurent-normalization and Puiseux arguments are in NORMALFORM-695.md.
This file does not claim the Jacobian conjecture or a terminal profile exclusion.
-/

noncomputable section
namespace JacobianC2.NormalForm695

open Polynomial

def R (b c : ℂ) : ℂ[X] :=
  (X + C b) * (X ^ 2 + C b * X + C (2 * c))

def S (b c : ℂ) : ℂ[X] := X ^ 2 + C b * X + C c

def P (b c : ℂ) : ℂ[X] := R b c ^ 2 + S b c

/-- Eight times the second coordinate, to retain integral polynomial certificates. -/
def Q8 (b c : ℂ) : ℂ[X] :=
  8 * R b c ^ 3 + 12 * R b c * S b c + 3 * X

/-- A Bezout identity in the polynomial ring, so multiplicities are retained. -/
theorem derivative_bezout (b c : ℂ) :
    3 * X = (X + 4 * S b c * R b c) * (Q8 b c).derivative -
      3 * (4 * R b c * (X + 4 * S b c * R b c) + 8 * S b c ^ 2) *
        (P b c).derivative := by
  simp only [P, Q8, R, S, derivative_add, derivative_mul, derivative_pow,
    derivative_X, derivative_C]
  push_cast
  ring

/-- Any polynomial dividing both actual derivatives divides the parameter. -/
theorem common_derivative_divisor_dvd_X (b c : ℂ) (D : ℂ[X])
    (hP : D ∣ (P b c).derivative) (hQ : D ∣ (Q8 b c).derivative) : D ∣ X := by
  have h3 : D ∣ (3 : ℂ[X]) * X := by
    rw [derivative_bezout b c]
    exact dvd_sub (dvd_mul_of_dvd_right hQ _) (dvd_mul_of_dvd_right hP _)
  have h := dvd_mul_of_dvd_right h3 (C (1 / 3 : ℂ))
  have hi : C (1 / 3 : ℂ) * (3 : ℂ[X]) = 1 := by
    norm_num [← map_ofNat C, ← map_mul]
  simpa [← mul_assoc, hi] using h

/-- Every simultaneous zero of the derivatives is the parameter zero. -/
theorem critical_parameter_zero (b c t : ℂ)
    (hP : (P b c).derivative.eval t = 0)
    (hQ : (Q8 b c).derivative.eval t = 0) : t = 0 := by
  have h := congrArg (fun f : ℂ[X] => f.eval t) (derivative_bezout b c)
  have hz : (3 : ℂ) * t = 0 := by simpa [hP, hQ] using h
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

def cuspEquation (b c : ℂ) : ℂ := 4 * b ^ 2 * c + 8 * c ^ 2 + 1

theorem first_derivative_at_zero (b c : ℂ) :
    (P b c).derivative.eval 0 = b * cuspEquation b c := by
  simp [P, R, S, cuspEquation]
  ring

theorem second_derivative_at_zero (b c : ℂ) :
    (Q8 b c).derivative.eval 0 =
      3 * (8 * b ^ 2 * c + 1) * cuspEquation b c := by
  simp [Q8, R, S, cuspEquation]
  ring

/-- Exact critical locus, with no assumptions on the complex parameters. -/
theorem critical_iff (b c t : ℂ) :
    ((P b c).derivative.eval t = 0 ∧ (Q8 b c).derivative.eval t = 0) ↔
      t = 0 ∧ cuspEquation b c = 0 := by
  constructor
  · rintro ⟨hP, hQ⟩
    have ht := critical_parameter_zero b c t hP hQ
    refine ⟨ht, ?_⟩
    subst t
    rw [first_derivative_at_zero] at hP
    rw [second_derivative_at_zero] at hQ
    linear_combination (1 / 3 : ℂ) * hQ - (8 * b * c) * hP
  · rintro ⟨rfl, h⟩
    simp [first_derivative_at_zero, second_derivative_at_zero, h]

/-- The entire Weierstrass relation, with the same coefficients. -/
theorem weierstrass_identity (b c : ℂ) :
    Q8 b c ^ 2 - 64 * P b c ^ 3 =
      8 * S b c ^ 3 - 48 * C (c ^ 2) * R b c ^ 2 -
        72 * C (c ^ 2) * S b c + 9 * X ^ 2 := by
  simp only [P, Q8, R, S]
  push_cast
  ring

-- The quotient of the derivative gcd is handled by `common_derivative_divisor_dvd_X`.
-- The following scalar identities certify the only possible higher cusp.

def F (c : ℂ) : ℂ := 160 * c ^ 4 + 40 * c ^ 2 - 1

theorem exceptional_second_coefficient_nonzero (c : ℂ) (hF : F c = 0) :
    1 - 4 * c ^ 2 ≠ 0 := by
  intro h
  have hid : F c + (40 * c ^ 2 + 20) * (1 - 4 * c ^ 2) = 19 := by
    unfold F
    ring
  rw [hF, h] at hid
  norm_num at hid

theorem exceptional_fifth_coefficient_nonzero (c : ℂ) (hF : F c = 0) :
    580 * c ^ 2 + 159 ≠ 0 := by
  intro h
  have hid : F c - ((8 : ℂ) * c ^ 2 / 29 - 28 / 4205) *
      (580 * c ^ 2 + 159) = 247 / 4205 := by
    unfold F
    ring
  rw [hF, h] at hid
  norm_num at hid

#print axioms derivative_bezout
#print axioms common_derivative_divisor_dvd_X
#print axioms critical_parameter_zero
#print axioms critical_iff
#print axioms weierstrass_identity
#print axioms exceptional_second_coefficient_nonzero
#print axioms exceptional_fifth_coefficient_nonzero

end JacobianC2.NormalForm695
