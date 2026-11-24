import Mathlib

/-!
E076. Sound pruning algebra for unrestricted net searches.
These theorems formalize the matrix and exact-cover implications below.
The full incidence geometry to these hypotheses is proved in the accompanying
mathematical note, not encoded as a Lean OA structure in this file.
-/
open scoped BigOperators
namespace MOLS10.E076

section Matrices
variable {K n m : Type*} [Field K] [Fintype n] [DecidableEq n]

theorem rank_left_of_inverse (A L R : Matrix n n K) (hRL : R * L = 1) :
    (L * A).rank = A.rank := by
  apply le_antisymm (Matrix.rank_mul_le_right _ _)
  calc
    A.rank = (R * (L * A)).rank := by rw [← mul_assoc, hRL, one_mul]
    _ ≤ (L * A).rank := Matrix.rank_mul_le_right _ _

theorem rank_right_of_inverse (A L R : Matrix n n K) (hLR : L * R = 1) :
    (A * L).rank = A.rank := by
  apply le_antisymm (Matrix.rank_mul_le_left _ _)
  calc
    A.rank = ((A * L) * R).rank := by rw [mul_assoc, hLR, mul_one]
    _ ≤ (A * L).rank := Matrix.rank_mul_le_left _ _

theorem rank_nilpotent_shear (A N : Matrix n n K) (hN : N * N = 0) :
    ((1 + N) * A).rank = A.rank := by
  apply rank_left_of_inverse A (1 + N) (1 - N)
  calc
    (1 - N) * (1 + N) = 1 - N * N := by noncomm_ring
    _ = 1 := by rw [hN, sub_zero]

def onesMatrix : Matrix n n K := fun _ _ => 1

/-- A left preimage of the all-one vector with zero coordinate sum
makes every all-one shift preserve rank. -/
theorem rank_all_one_shift (A : Matrix n n K) (y : n → K)
    (hsum : ∑ i, y i = 0) (hy : ∀ j, ∑ i, y i * A i j = 1) (c : K) :
    (A + c • (onesMatrix : Matrix n n K)).rank = A.rank := by
  let N : Matrix n n K := fun _ j => c * y j
  have hN : N * N = 0 := by
    ext i j
    change (∑ k, c * y k * (c * y j)) = 0
    rw [← Finset.sum_mul, ← Finset.mul_sum, hsum, mul_zero, zero_mul]
  have hNA : N * A = c • (onesMatrix : Matrix n n K) := by
    ext i j
    change (∑ k, c * y k * A k j) = c * 1
    calc
      _ = c * (∑ k, y k * A k j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = c * 1 := by rw [hy]
  have heq : (1 + N) * A = A + c • (onesMatrix : Matrix n n K) := by
    rw [add_mul, one_mul, hNA]
  rw [← heq]
  exact rank_nilpotent_shear A N hN

theorem rank_hadamard_transform (A : Matrix n n K) (y : n → K)
    (hsum : ∑ i, y i = 0) (hy : ∀ j, ∑ i, y i * A i j = 1)
    (htwo : (2 : K) ≠ 0) :
    ((onesMatrix : Matrix n n K) - (2 : K) • A).rank = A.rank := by
  have hf : (onesMatrix : Matrix n n K) - (2 : K) • A =
      (-2 : K) • (A + (-(2 : K)⁻¹) • (onesMatrix : Matrix n n K)) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    field_simp
    ring
  rw [hf, Matrix.rank_smul_of_mem_nonZeroDivisors _
    (mem_nonZeroDivisors_of_ne_zero (neg_ne_zero.mpr htwo))]
  exact rank_all_one_shift A y hsum hy _

/-- Includes every Seidel switch, using its diagonal sign matrix D. -/
theorem rank_involutory_conjugate (H D : Matrix n n K) (hD : D * D = 1) :
    (D * H * D).rank = H.rank := by
  calc
    (D * H * D).rank = (H * D).rank := by
      rw [mul_assoc]
      exact rank_left_of_inverse (H * D) D D hD
    _ = H.rank := rank_right_of_inverse H D D hD

theorem partial_rank_bound [Fintype m] (A : Matrix n n K) (e : m → n)
    (r : ℕ) (hr : A.rank ≤ r) : (A.submatrix e e).rank ≤ r :=
  (Matrix.rank_submatrix_le A e e).trans hr

/-- Sound rejection of a partial matrix under a prescribed rank cap. -/
theorem no_completion_over_rank [Fintype m] (P : Matrix m m K)
    (e : m → n) (r : ℕ) (hP : r < P.rank) :
    ¬ ∃ A : Matrix n n K, A.rank ≤ r ∧ A.submatrix e e = P := by
  rintro ⟨A, hA, hAP⟩
  have hb := partial_rank_bound A e r hA
  rw [hAP] at hb
  omega
end Matrices

/-- Finite-field or rational dual certificates rule out every exact cover. -/
theorem no_exact_cover_of_dual
    {K E C : Type*} [CommRing K] [Fintype E] [Fintype C]
    (inc : E → C → K) (w : E → K)
    (htotal : (∑ e, w e) ≠ 0)
    (hzero : ∀ c, ∑ e, w e * inc e c = 0) :
    ¬ ∃ z : C → K, ∀ e, ∑ c, inc e c * z c = 1 := by
  rintro ⟨z, hz⟩
  apply htotal
  calc
    (∑ e, w e) = ∑ e, w e * (∑ c, inc e c * z c) := by
      simp only [hz, mul_one]
    _ = ∑ c, (∑ e, w e * inc e c) * z c := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ = 0 := by simp [hzero]

/-- Incidence degree counts force every binary relation weight divisible by4. -/
theorem binary_relation_weight_four (w q n2 n4 : ℤ)
    (hdeg : 10 * w = 2 * n2 + 4 * n4)
    (hpair : q = n2 + 6 * n4) (hq : (4 : ℤ) ∣ q) :
    (4 : ℤ) ∣ w := by omega

#print axioms rank_left_of_inverse
#print axioms rank_right_of_inverse
#print axioms rank_nilpotent_shear
#print axioms rank_all_one_shift
#print axioms rank_hadamard_transform
#print axioms rank_involutory_conjugate
#print axioms partial_rank_bound
#print axioms no_completion_over_rank
#print axioms no_exact_cover_of_dual
#print axioms binary_relation_weight_four
end MOLS10.E076
