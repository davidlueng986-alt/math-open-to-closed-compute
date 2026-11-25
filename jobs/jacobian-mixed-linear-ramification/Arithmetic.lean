import Mathlib

namespace MixedLinear

-- All variables are formal scalars; hp and kp stand for derivatives.
theorem one_root_resultant {R : Type*} [CommRing R]
    (a b h k hp kp alpha : R) :
    b^2*hp^2*k-b^2*h*hp*kp-a*kp^2 =
    b^2*hp^2*(k+b*alpha*h-a*alpha^2) +
      (kp+b*alpha*hp)*((2*a*b*alpha-b^2*h)*hp-a*(kp+b*alpha*hp)) := by
  ring

theorem two_root_resultant {R : Type*} [CommRing R]
    (a b h k hp kp alpha beta : R) :
    (alpha-beta)^2*(b^2*hp^2*k-b^2*h*hp*kp-a*kp^2) =
    -a*(alpha-beta)^2*(kp+b*alpha*hp)*(kp+b*beta*hp)
      -((kp+b*alpha*hp)-(kp+b*beta*hp))*
        ((k+b*alpha*h-a*alpha^2)*(kp+b*beta*hp)-
          (k+b*beta*h-a*beta^2)*(kp+b*alpha*hp)) := by
  ring

theorem ramification_budget (d D : ℤ) (hd : 11 ≤ d) (hD : 2 ≤ D) :
    d < (d-2)*D-2*(3*D-3) := by
  have h : 0 ≤ (d-8)*(D-2) := mul_nonneg (by omega) (by omega)
  nlinarith

theorem discriminant_square {K : Type*} [Field K] (d w v : K)
    (hd : d ≠ 0) (hm : d-1 ≠ 0) :
    (w*(2-(d+1)*v)/(d-1))^2 -
      4*(d+1)/d^2*(w^2*(1-d*v)/(d-1)) =
    (w*(d*(d+1)*v-2)/(d*(d-1)))^2 := by
  field_simp
  ring

end MixedLinear

namespace Degree135

-- Coefficients at Y^16,Y^13,Y^10,Y^7 after z-1 ~ 3*tau*Y.
-- The coefficient Y^-1 of sqrt of the terminal form equals 1/3
-- of the residue of the v^0 square-root coefficient at z=1.
theorem terminal_residue_scaling {K : Type*} [Field K] [CharZero K]
    (r a b c : K) (hr : r ≠ 0) :
    3*((3^7*c)/(2*(3^8*r))-
      (3^13*a)*(3^10*b)/(4*(3^8*r)^3)+
      (3^13*a)^3/(16*(3^8*r)^5)) =
    c/(2*r)-a*b/(4*r^3)+a^3/(16*r^5) := by
  field_simp

theorem square_correction {K : Type*} [Field K] [CharZero K]
    (r a b : K) (hr : r ≠ 0) :
    3*b^2/(8*r)-3*a^2*b/(16*r^3)+3*a^4/(128*r^5) =
    3*(4*r^2*b-a^2)^2/(128*r^5) := by
  field_simp
  ring

-- In a common square-root branch, A^2=cP*f5,
-- C=cQ*g8/A^3, s=A*sigma, J=-cP*cQ/3.
theorem opposite_cancels {K : Type*} [Field K] [CharZero K]
    (A cP cQ f5 g8 sigma : K)
    (hA : A ≠ 0) (hf : f5 ≠ 0) (h : A^2 = cP*f5) :
    -(-cP*cQ/3)*(cQ*g8/A^3)*(3*(A*sigma)) =
       cQ^2*(g8/f5)*sigma := by
  field_simp
  linear_combination -cQ^2*g8*sigma*h

end Degree135

#print axioms MixedLinear.one_root_resultant
#print axioms MixedLinear.two_root_resultant
#print axioms MixedLinear.ramification_budget
#print axioms MixedLinear.discriminant_square
#print axioms Degree135.terminal_residue_scaling
#print axioms Degree135.square_correction
#print axioms Degree135.opposite_cancels
