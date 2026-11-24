import Mathlib

namespace JacobianMixedSection

-- Exact ring-theoretic core of the divided-difference obstruction.
-- C is the third target coordinate, W is the intermediate parameter,
-- D is 1 - partial_w S_d(W,C L(C)).
theorem derivative_factor_unit {R : Type*} [CommRing R]
    (C W D d i k s j c ci : R)
    (hinv : (1-d)*i = 1)
    (hid : W*W-W = C*k)
    (hd : D = 1-d*W+C*s)
    (hjac : C*c = D*j)
    (hc : c*ci = 1) : D ∣ 1 := by
  have hC : C = D*(j*ci) := calc
    C = C*(c*ci) := by rw [hc, mul_one]
    _ = (C*c)*ci := by ring
    _ = D*(j*ci) := by rw [hjac]; ring
  have hE : D*(1+d*i*W) = 1+C*(s*(1+d*i*W)-d*d*i*k) := by
    rw [hd]
    linear_combination (W*d)*hinv - (d*d*i)*hid
  refine ⟨(1+d*i*W)-(j*ci)*(s*(1+d*i*W)-d*d*i*k), ?_⟩
  calc
    1 = D*(1+d*i*W)-C*(s*(1+d*i*W)-d*d*i*k) := by rw [hE]; ring
    _ = D*((1+d*i*W)-(j*ci)*(s*(1+d*i*W)-d*d*i*k)) := by rw [hC]; ring

-- For a nonzero offset kappa the divided-difference equation is T*M=kappa*X^2,
-- with T=1+X*F. The two factors T and X are comaximal.
theorem offset_forces_unit {R : Type*} [CommRing R]
    (X T F M k ki : R)
    (ht : T = 1+X*F)
    (hm : T*M = k*X^2)
    (hk : k*ki = 1) : T ∣ 1 := by
  have hx : X^2 = T*M*ki := calc
    X^2 = (k*ki)*X^2 := by rw [hk, one_mul]
    _ = (k*X^2)*ki := by ring
    _ = T*M*ki := by rw [hm]
  refine ⟨T-2*X*F+M*ki*F^2, ?_⟩
  calc
    1 = (T-X*F)^2 := by rw [ht]; ring
    _ = T*(T-2*X*F)+X^2*F^2 := by ring
    _ = T*(T-2*X*F)+T*M*ki*F^2 := by rw [← hx]
    _ = T*(T-2*X*F+M*ki*F^2) := by ring

-- If B=b0+X*B1 and C=X*Gamma, the determinant after applying
-- the product rule is divisible by X (the constant b0 has zero derivative).
theorem shared_factor_jacobian {R : Type*} [CommRing R]
    (X b g x1 x2 b1 b2 g1 g2 : R) :
    X ∣ (x1*b+X*b1)*(x2*g+X*g2)-(x2*b+X*b2)*(x1*g+X*g1) := by
  refine ⟨x1*b*g2+b1*x2*g+X*b1*g2-x2*b*g1-b2*x1*g-X*b2*g1, ?_⟩
  ring

#print axioms derivative_factor_unit
#print axioms offset_forces_unit
#print axioms shared_factor_jacobian

end JacobianMixedSection
