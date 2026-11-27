import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.Tactic

/-!
# Nilpotent chains and the local boundary-degree bound

The theorems below are genuine finite-dimensional linear-algebra and algebra
statements. No analytic map, Puiseux atlas, Jacobian-socle theorem, or Euler
identity is postulated as an axiom.

Application in FOUR-AFFINE-SHEETS.md:
A = C[[u,t]] / (p,q), t^(e-1) is nonzero by the Jacobian-socle theorem,
and A/(t) has dimension r*m. The last theorem then gives d >= e-1+r*m.
The geometric application remains an ordinary proof.
-/

namespace JC2.LocalDefect

open Module

section Linear

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- A nilpotent operator vanishes at the dimension of its vector space. -/
theorem nilpotent_pow_finrank_eq_zero (f : Module.End K V)
    (hf : IsNilpotent f) : f ^ finrank K V = 0 := by
  obtain ⟨n, hn⟩ := hf
  apply LinearMap.ext
  intro x
  have hx : x ∈ LinearMap.ker (f ^ n) := by
    simp only [hn, LinearMap.ker_zero, Submodule.mem_top]
  have hx' := (Module.End.ker_pow_le_ker_pow_finrank f n) hx
  exact LinearMap.mem_ker.mp hx'

/-- Restriction of an endomorphism to its invariant range. -/
private def rangeEnd (f : Module.End K V) : Module.End K f.range :=
  f.rangeRestrict.comp f.range.subtype

private theorem rangeEnd_pow_apply (f : Module.End K V) (n : ℕ)
    (x : f.range) :
    ((rangeEnd f ^ n) x : V) = (f ^ n) (x : V) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply]
    exact congrArg f ih

private theorem rangeEnd_nilpotent (f : Module.End K V)
    (hf : IsNilpotent f) : IsNilpotent (rangeEnd f) := by
  obtain ⟨n, hn⟩ := hf
  refine ⟨n, ?_⟩
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change ((rangeEnd f ^ n) x : V) = 0
  rw [rangeEnd_pow_apply, hn, LinearMap.zero_apply]

/-- One additional application enters the invariant range, whose dimension
bounds the remaining nilpotent chain length. -/
theorem nilpotent_pow_finrank_range_succ_eq_zero (f : Module.End K V)
    (hf : IsNilpotent f) : f ^ (finrank K f.range + 1) = 0 := by
  have hz := nilpotent_pow_finrank_eq_zero (rangeEnd f) (rangeEnd_nilpotent f hf)
  apply LinearMap.ext
  intro x
  have h := congrArg
    (fun g : Module.End K f.range => ((g (f.rangeRestrict x) : f.range) : V)) hz
  rw [rangeEnd_pow_apply] at h
  change (f ^ finrank K f.range) (f x) = 0 at h
  change (f ^ (finrank K f.range + 1)) x = 0
  rw [pow_succ, Module.End.mul_apply]
  exact h

/-- A nonzero power of a nilpotent endomorphism forces a sufficiently
large range, without choosing a Jordan normal form. -/
theorem pow_ne_zero_le_finrank_range (f : Module.End K V)
    (hf : IsNilpotent f) (n : ℕ) (hn : f ^ n ≠ 0) :
    n ≤ finrank K f.range := by
  by_contra h
  have hle : finrank K f.range + 1 ≤ n := by omega
  exact hn (pow_eq_zero_of_le hle (nilpotent_pow_finrank_range_succ_eq_zero f hf))

/-- The nonzero nilpotent chain and the quotient by its range occupy
independent portions of the total vector-space dimension. -/
theorem nilpotent_range_codimension_bound (f : Module.End K V)
    (hf : IsNilpotent f) (n : ℕ) (hn : f ^ n ≠ 0) :
    n + finrank K (V ⧸ f.range) ≤ finrank K V := by
  have hchain := pow_ne_zero_le_finrank_range f hf n hn
  have hdim := f.range.finrank_quotient_add_finrank
  omega

end Linear

section Algebra

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]
  [FiniteDimensional K A]

/-- Algebra form of the dimension bound. Multiplication by t has range tA;
a surviving t^n requires n dimensions there, in addition to A/tA. -/
theorem nilpotent_element_quotient_bound (t : A) (ht : IsNilpotent t)
    (n : ℕ) (hn : t ^ n ≠ 0) :
    n + finrank K (A ⧸ (LinearMap.mulLeft K t).range) ≤ finrank K A := by
  have hnil : IsNilpotent (LinearMap.mulLeft K t) := by
    obtain ⟨j, hj⟩ := ht
    refine ⟨j, ?_⟩
    apply LinearMap.ext
    intro x
    rw [LinearMap.pow_mulLeft]
    change t ^ j * x = 0
    rw [hj, zero_mul]
  have hnonzero : (LinearMap.mulLeft K t) ^ n ≠ 0 := by
    intro h
    have h1 := LinearMap.congr_fun h (1 : A)
    rw [LinearMap.pow_mulLeft] at h1
    exact hn (by simpa using h1)
  exact nilpotent_range_codimension_bound (LinearMap.mulLeft K t) hnil n hnonzero

/-- The numerical form used when a one-dimensional boundary quotient has
length r*m and the Jacobian has normal order e-1. -/
theorem local_degree_bound_from_socle_power (t : A) (ht : IsNilpotent t)
    (e r m : ℕ) (hsocle : t ^ (e - 1) ≠ 0)
    (hboundary : finrank K (A ⧸ (LinearMap.mulLeft K t).range) = r * m) :
    e - 1 + r * m ≤ finrank K A := by
  simpa only [hboundary] using
    nilpotent_element_quotient_bound t ht (e - 1) hsocle

end Algebra

#print axioms nilpotent_pow_finrank_eq_zero
#print axioms nilpotent_pow_finrank_range_succ_eq_zero
#print axioms pow_ne_zero_le_finrank_range
#print axioms nilpotent_range_codimension_bound
#print axioms nilpotent_element_quotient_bound
#print axioms local_degree_bound_from_socle_power


section Arithmetic

/-- The weighted finite-cover degree formula forces strictly more than one
extra sheet per five generic missing sheets. This is an algebraic consequence
over the rationals; the geometric degree formula is an explicit hypothesis. -/
theorem monomial_cusp_surplus_fifth (a b r e d : ℚ)
    (ha : 2 ≤ a) (hb : 3 ≤ b) (hr : 1 ≤ r) (he : 0 < e)
    (hdegree : d * (r * (a + b) - 1) = e * a * b * r ^ 2) :
    e * r < 5 * (d - e * r) := by
  have hrpos : 0 < r := by linarith
  have hab : 0 ≤ 5 * a * b - 6 * (a + b) := by
    have hp : 0 ≤ (a - 2) * (b - 3) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hden : 0 < r * (a + b) - 1 := by nlinarith
  have hinner : 0 < r * (5 * a * b - 6 * (a + b)) + 6 := by
    have hp := mul_nonneg (le_of_lt hrpos) hab
    linarith
  have hpositive :
      0 < e * r * (r * (5 * a * b - 6 * (a + b)) + 6) :=
    mul_pos (mul_pos he hrpos) hinner
  have hid :
      (5 * d - 6 * e * r) * (r * (a + b) - 1) =
        e * r * (r * (5 * a * b - 6 * (a + b)) + 6) := by
    calc
      (5 * d - 6 * e * r) * (r * (a + b) - 1) =
          5 * (d * (r * (a + b) - 1)) -
            6 * e * r * (r * (a + b) - 1) := by ring
      _ = 5 * (e * a * b * r ^ 2) -
            6 * e * r * (r * (a + b) - 1) := by rw [hdegree]
      _ = e * r * (r * (5 * a * b - 6 * (a + b)) + 6) := by ring
  rw [← hid] at hpositive
  have hgap : 0 < 5 * d - 6 * e * r :=
    (mul_pos_iff_of_pos_right hden).mp hpositive
  linarith

/-- Global integer assembly, with all geometric input exposed in hlarge:
a component heavier than half the cover has another component of weight
at least one and a cusp excess C with 5*C>M. -/
theorem affine_sheet_bound_from_ledger (μ M C : ℤ) (hμ : 6 ≤ μ)
    (hlarge : μ < 2 * M → M < 5 * C ∧ M + 1 + C ≤ μ - 1) :
    6 * M ≤ 5 * μ - 11 ∧ μ + 11 ≤ 6 * (μ - M) := by
  by_cases h : 2 * M ≤ μ
  · omega
  · obtain ⟨hstrict, hledger⟩ := hlarge (by omega)
    omega

end Arithmetic

#print axioms monomial_cusp_surplus_fifth
#print axioms affine_sheet_bound_from_ledger

end JC2.LocalDefect

