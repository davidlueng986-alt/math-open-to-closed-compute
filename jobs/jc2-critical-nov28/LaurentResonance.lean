import Mathlib.Tactic

/-!
Exact algebra certificates for the finite germ and the corresponding balanced
Laurent Newton chart.  These are identities over every commutative ring.

The file does not assert a polynomial Keller counterexample.  The Jacobian is
6*v^2 for the scaled second coordinate, and the Laurent chart has a pole.
The written note supplies the standard Groebner-basis argument for local
intersection length 8; this file checks its ideal and S-polynomial identities.
-/

namespace JacobianHeightResonance

variable {K : Type*} [CommRing K]

def p (u v : K) : K := u ^ 4 + u * v
def q8 (u v : K) : K := 8 * u ^ 6 + 12 * u ^ 3 * v + 3 * v ^ 2
def g1 (u v : K) : K := 3 * v ^ 2 - 4 * u ^ 6
def g3 (u : K) : K := u ^ 7

/-- The displayed factors are the two formal partial derivatives of each
coordinate: `p_u*q8_v - p_v*q8_u = 6*v^2`. -/
theorem jacobian_identity (u v : K) :
    (4 * u ^ 3 + v) * (12 * u ^ 3 + 6 * v) -
      u * (48 * u ^ 5 + 36 * u ^ 2 * v) = 6 * v ^ 2 := by
  ring

/-- The target cusp has another pullback component besides `v=0`. -/
theorem cusp_pullback (u v : K) :
    q8 u v ^ 2 - 64 * p u v ^ 3 = v ^ 3 * (8 * u ^ 3 + 9 * v) := by
  simp only [p, q8]
  ring

/-- On the source boundary, the cusp-normalization parameter is `u^2`. -/
theorem boundary_normalization (u : K) :
    p u 0 = (u ^ 2) ^ 2 ∧ q8 u 0 = 8 * (u ^ 2) ^ 3 := by
  simp only [p, q8]
  constructor <;> ring

/-- First Groebner generator belongs to the coordinate ideal. -/
theorem first_generator (u v : K) :
    g1 u v = q8 u v - 12 * u ^ 2 * p u v := by
  simp only [g1, p, q8]
  ring

/-- The final pure-power generator belongs to the same ideal. -/
theorem last_generator (u v : K) :
    g3 u = (3 * v + 9 * u ^ 3) * p u v - u * q8 u v := by
  simp only [g3, p, q8]
  ring

/-- Conversely the scaled second coordinate lies in the generated ideal. -/
theorem recover_second_coordinate (u v : K) :
    q8 u v = g1 u v + 12 * u ^ 2 * p u v := by
  simp only [g1, p, q8]
  ring

/-- Reduction of the S-polynomial for leading terms `3*v^2` and `u*v`. -/
theorem s_polynomial_12 (u v : K) :
    u * g1 u v - 3 * v * p u v = -3 * u ^ 3 * p u v - g3 u := by
  simp only [g1, g3, p]
  ring

/-- Reduction of the S-polynomial for leading terms `3*v^2` and `u^7`. -/
theorem s_polynomial_13 (u v : K) :
    u ^ 7 * g1 u v - 3 * v ^ 2 * g3 u = -4 * u ^ 6 * g3 u := by
  simp only [g1, g3]
  ring

/-- Reduction of the S-polynomial for leading terms `u*v` and `u^7`. -/
theorem s_polynomial_23 (u v : K) :
    u ^ 6 * p u v - v * g3 u = u ^ 3 * g3 u := by
  simp only [g3, p]
  ring

/-- The Jacobian and generic transverse cusp exponents are e-1=2 and e=3;
the normalization index is r=2 and the local length is d=8. -/
theorem numerical_failure_of_strict_residual_bound :
    8 - 3 * 2 = 2 ∧ ¬ (2 + 1 ≤ 8 - 3 * 2) := by
  norm_num

/-- The height-four face ODE has a genuine polynomial solution.  This is the
denominator-cleared identity for A(z)=(1-z)^3 and S(z)=(1-z)(1-4z/5).
The normalized equation has right side 1. -/
theorem height_four_face_ode (z : K) :
    4 * z * (-9 + 8 * z) * (1 - z) +
      ((1 - z) + 9 * z) * (5 - 9 * z + 4 * z ^ 2) =
        5 * (1 - z) := by
  ring

def hp (t z b : K) : K := z ^ 9 + 3 * t ^ 5 * z ^ 5 + b * t ^ 10 * z
def hq (t z b : K) : K :=
  3 * z ^ 12 + 12 * t ^ 5 * z ^ 8 + (6 + 4 * b) * t ^ 10 * z ^ 4 +
    (4 * b - 4) * t ^ 15

/-- A height-four balanced Laurent chart: after clearing the t-poles of
P=t^(-12)*hp and Q=t^(-16)*hq, the only error is the displayed quadratic
relation on b.  Taking 2*b^2-12*b+15=0 gives Jac(P,Q)=b*(4*b-4)*t^(-4).
The two occurrences of partial derivatives are expanded explicitly. -/
theorem balanced_height_four_identity (t z b : K) :
    t * ((15 * t ^ 4 * z ^ 5 + 10 * b * t ^ 9 * z) *
        (36 * z ^ 11 + 96 * t ^ 5 * z ^ 7 + 4 * (6 + 4 * b) * t ^ 10 * z ^ 3) -
      (9 * z ^ 8 + 15 * t ^ 5 * z ^ 4 + b * t ^ 10) *
        (60 * t ^ 4 * z ^ 8 + 10 * (6 + 4 * b) * t ^ 9 * z ^ 4 +
          15 * (4 * b - 4) * t ^ 14)) +
      16 * (9 * z ^ 8 + 15 * t ^ 5 * z ^ 4 + b * t ^ 10) * hq t z b -
      12 * hp t z b *
        (36 * z ^ 11 + 96 * t ^ 5 * z ^ 7 + 4 * (6 + 4 * b) * t ^ 10 * z ^ 3) =
    b * (4 * b - 4) * t ^ 25 -
      4 * t ^ 20 * z ^ 4 * (2 * b ^ 2 - 12 * b + 15) := by
  simp only [hp, hq]
  ring

/-- The complete leading-coefficient necessary equation allows the height-four
profile R=x^12 and C=(x-x^3)/(8a).  This is its denominator-cleared form. -/
theorem height_four_global_leading_equation (x : K) :
    4 * (1 - 3 * x ^ 2) * x ^ 12 -
      12 * x ^ 11 * (x - x ^ 3) = -8 * x ^ 12 := by
  ring

end JacobianHeightResonance

#print axioms JacobianHeightResonance.jacobian_identity
#print axioms JacobianHeightResonance.cusp_pullback
#print axioms JacobianHeightResonance.boundary_normalization
#print axioms JacobianHeightResonance.first_generator
#print axioms JacobianHeightResonance.last_generator
#print axioms JacobianHeightResonance.recover_second_coordinate
#print axioms JacobianHeightResonance.s_polynomial_12
#print axioms JacobianHeightResonance.s_polynomial_13
#print axioms JacobianHeightResonance.s_polynomial_23
#print axioms JacobianHeightResonance.numerical_failure_of_strict_residual_bound
#print axioms JacobianHeightResonance.height_four_face_ode
#print axioms JacobianHeightResonance.balanced_height_four_identity
#print axioms JacobianHeightResonance.height_four_global_leading_equation
