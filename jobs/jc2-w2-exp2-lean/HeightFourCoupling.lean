import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Omega

/-!
# Exact algebraic & arithmetic theorems for SECANT-HEIGHT-FOUR-REALIZATION
(OPPOSITE-EDGE.md Eqs. (77)-(83) coupled into the Wave 1 symplectic ODE).

All declarations below are pure ring/integer theorems with zero custom axioms.
-/

namespace JC2.Wave2Exp2.HeightFour

/-- Theorem 1a: Exact V-degree upper bound and unique attainment for p*(t, U). -/
theorem exact_p_v_degree_rigidity (j i k : ℤ)
    (hj : 1 ≤ j)
    (htot : i + k ≤ 4 * (2 * j + 1))
    (hwt : (3 * j + 1) * i - j * k ≤ 2 * j + 1) :
    i ≤ 2 * j + 1 ∧ (i = 2 * j + 1 → k = 3 * (2 * j + 1)) := by
  have h1 : (4 * j + 1) * i ≤ (4 * j + 1) * (2 * j + 1) := by nlinarith
  have hi : i ≤ 2 * j + 1 := by nlinarith
  refine ⟨hi, fun heq => ?_⟩
  subst heq
  nlinarith

/-- Theorem 1b: Exact d = j + 1 rigidity from deg_V a_0 = 2d - 1 = 2j + 1. -/
theorem exact_d_eq_j_succ (d j : ℕ) (h : 2 * d - 1 = 2 * j + 1) (hd : 1 ≤ d) :
    d = j + 1 := by
  omega

/-- Theorem 1c: Exact V-degree upper bound and unique attainment for q*(t, U). -/
theorem exact_q_v_degree_rigidity (j i k : ℤ)
    (hj : 1 ≤ j)
    (htot : i + k ≤ 4 * (3 * j + 1))
    (hwt : (3 * j + 1) * i - j * k ≤ 3 * j + 1) :
    i ≤ 3 * j + 1 ∧ (i = 3 * j + 1 → k = 3 * (3 * j + 1)) := by
  have h1 : (4 * j + 1) * i ≤ (4 * j + 1) * (3 * j + 1) := by nlinarith
  have hi : i ≤ 3 * j + 1 := by nlinarith
  refine ⟨hi, fun heq => ?_⟩
  subst heq
  nlinarith

/-- Theorem 4a: All-d top-down pivot nonvanishing inequality for every d >= 2
and every 1 <= k <= 2d - 2. Since 3k^2 < d*(8d - 2k - 6)^2, the pivot
3k +/- (8d - 2k - 6)*sqrt(3d) never vanishes over C. -/
theorem top_down_pivot_strict_pos (d k : ℤ)
    (hd : 2 ≤ d) (hk1 : 1 ≤ k) (hk2 : k ≤ 2 * d - 2) :
    3 * k ^ 2 < d * (8 * d - 2 * k - 6) ^ 2 := by
  have hlin : 4 * d - 2 ≤ 8 * d - 2 * k - 6 := by linarith
  have hpos : 0 ≤ 4 * d - 2 := by linarith
  have hsq1 : (4 * d - 2) ^ 2 ≤ (8 * d - 2 * k - 6) ^ 2 := by nlinarith
  have hsq2 : k ^ 2 ≤ (2 * d - 2) ^ 2 := by nlinarith
  have hcore : 3 * (2 * d - 2) ^ 2 < d * (4 * d - 2) ^ 2 := by
    have hm : 0 ≤ d - 2 := by linarith
    nlinarith [sq_nonneg (d - 2)]
  nlinarith

/-- Theorem 4b: All-d binomial exclusion core contradiction:
for all d >= 2, no element x of a commutative ring of char 0 (represented over Q)
can satisfy both (8d - 4)*x + 3 = 0 and 16*(4d - 3)*x^2 + 24*x - 3 = 0. -/
theorem binomial_leading_contradiction (d : ℤ) (hd : 2 ≤ d) (x : ℚ)
    (hlin : (8 * (d : ℚ) - 4) * x + 3 = 0)
    (hquad : 16 * (4 * (d : ℚ) - 3) * x ^ 2 + 24 * x - 3 = 0) : False := by
  have hpoly :
      (4 * (d : ℚ) - 2) ^ 2 * (16 * (4 * (d : ℚ) - 3) * x ^ 2 + 24 * x - 3)
      - (4 * (4 * (d : ℚ) - 3) * x + 12 * (d : ℚ)) * ((8 * (d : ℚ) - 4) * x + 3)
      = -12 * (4 * (d : ℚ) ^ 3 - 7 * (d : ℚ) ^ 2 + 7 * (d : ℚ) - 3) := by
    ring
  rw [hquad, hlin] at hpoly
  have hzero : 4 * (d : ℚ) ^ 3 - 7 * (d : ℚ) ^ 2 + 7 * (d : ℚ) - 3 = 0 := by linarith
  have hdq : (2 : ℚ) ≤ (d : ℚ) := by exact_mod_cast hd
  have hpos : 0 < 4 * (d : ℚ) ^ 3 - 7 * (d : ℚ) ^ 2 + 7 * (d : ℚ) - 3 := by
    nlinarith [sq_nonneg ((d : ℚ) - 2)]
  linarith

/-- Theorem 3: Exact cusp-divisor factorization identity along t = 0. -/
theorem cusp_divisor_factorization {R : Type*} [CommRing R]
    (P_eta P_V Q_eta Q_V d_eta d_V : R) :
    P_eta * (Q_eta * d_eta + Q_V * d_V) - Q_eta * (P_eta * d_eta + P_V * d_V) =
      (P_eta * Q_V - P_V * Q_eta) * d_V := by
  ring

/-- Theorem 2: Exact square-completion cancellation 4*Q1^2 - 9*R drops from deg 4d to 2d + 1. -/
theorem square_completion_cancellation {R : Type*} [CommRing R]
    (V a1 dlt alpha : R) :
    4 * (3 * a1 ^ 2 + 3 * dlt * a1 + 2 * V) ^ 2
      - 36 * (a1 ^ 4 + 2 * dlt * a1 ^ 3 + 4 * V * a1 ^ 2 - 8 * alpha * dlt * V ^ 2 * a1 + 16 * alpha * V ^ 3) =
    4 * ((9 * dlt ^ 2 - 24 * V) * a1 ^ 2 + 12 * dlt * V * (1 + 6 * alpha * V) * a1 + 4 * V ^ 2 * (1 - 36 * alpha * V)) := by
  ring

/-- Exact symplectic ODE decoupling identity from [eta^2] and [eta^0]. -/
theorem symplectic_ode_decoupling {R : Type*} [CommRing R]
    (X VX' Z a1 mu0 mu1 mu2 mu3 V : R)
    (heq2 : 2 * VX' - 3 * X + 3 * (a1 ^ 2 - mu3 * a1) / 2 + mu2 * V - 3 * Z = 0)
    (heq0 : 16 * X * Z - (a1 ^ 4 - 2 * mu3 * a1 ^ 3 + 4 * mu2 * V * a1 ^ 2 - 8 * mu1 * V ^ 2 * a1 + 16 * mu0 * V ^ 3) = 0) :
    16 * X * (2 * VX' - 3 * X + 3 * (a1 ^ 2 - mu3 * a1) / 2 + mu2 * V) =
      3 * (a1 ^ 4 - 2 * mu3 * a1 ^ 3 + 4 * mu2 * V * a1 ^ 2 - 8 * mu1 * V ^ 2 * a1 + 16 * mu0 * V ^ 3) := by
  linear_combination 16 * X * heq2 + 3 * heq0

#print axioms exact_p_v_degree_rigidity
#print axioms exact_d_eq_j_succ
#print axioms exact_q_v_degree_rigidity
#print axioms top_down_pivot_strict_pos
#print axioms binomial_leading_contradiction
#print axioms cusp_divisor_factorization
#print axioms square_completion_cancellation
#print axioms symplectic_ode_decoupling

end JC2.Wave2Exp2.HeightFour
