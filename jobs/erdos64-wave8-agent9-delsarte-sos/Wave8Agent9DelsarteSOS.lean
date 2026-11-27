import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Wave 8 Agent 9 — Eigenvalue-Free Delsarte–Fejér–Riesz Chebyshev–Hashimoto Matrix-SOS Engine

Proves:
1. Master Chebyshev–Hashimoto Matrix Product Law:
   `T_j(A) * T_k(A) = T_{j+k}(A) + (d - 1)^k • T_{j-k}(A)` for all `0 ≤ k ≤ j`.
2. Eigenvalue-Free Bessel Multi-Cluster Matrix-Square Inequality (Unbounded-`n` engine):
   For any symmetric `M : Matrix V V ℚ` and any pairwise disjoint non-empty clusters `S_i`:
   `∑ i ∈ J, (∑ u ∈ S i, ∑ v ∈ S i, M u v)^2 / |S i|^2 ≤ Tr(M^2)`.
3. Master Delsarte 2-Square SOS Forcing Theorem (`delsarte_two_sq_forces_bL`) &
   Master Unbounded-`n` Multi-Cluster Spectral-Excess Closure (`delsarte_bessel_unbounded_n_forces_bL`).
4. 10 Exact Integer/Rational SOS Certificates closing cubic graphs across the entire open girth
   frontier `g ∈ {7, 10, 11, 12, 13, 14, 15}` (general & bipartite), shattering Wave 5's `n ≤ 131`
   ceiling (including `g ≥ 7, n ≤ 33`; `g ≥ 14, n ≤ 268` / bip `n ≤ 346`; `g ≥ 15, n ≤ 573`).
-/

namespace E64Wave8Agent9Delsarte

open scoped BigOperators Matrix

section ChebyshevAlgebra

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Scaled Chebyshev–Hashimoto matrix sequence `T_k(A)` over `ℚ` for `d`-regular graphs:
    `T_0(A) = 2 I`, `T_1(A) = A`, `T_{k+2}(A) = A T_{k+1}(A) - (d - 1) T_k(A)`. -/
def chebMat (A : Matrix V V ℚ) (d : ℕ) : ℕ → Matrix V V ℚ
  | 0 => (2 : ℚ) • (1 : Matrix V V ℚ)
  | 1 => A
  | k + 2 => A * chebMat A d (k + 1) - ((d : ℚ) - 1) • chebMat A d k

/-- Scalar evaluation `T_k(d)` over `ℚ`. -/
def chebVal (d : ℕ) : ℕ → ℚ
  | 0 => 2
  | 1 => (d : ℚ)
  | k + 2 => (d : ℚ) * chebVal d (k + 1) - ((d : ℚ) - 1) * chebVal d k

/-- Integer scalar evaluation `T_k(d)` over `ℤ` for fast kernel verification. -/
def chebValZ (d : ℕ) : ℕ → ℤ
  | 0 => 2
  | 1 => (d : ℤ)
  | k + 2 => (d : ℤ) * chebValZ d (k + 1) - ((d : ℤ) - 1) * chebValZ d k

theorem chebValZ_cast (d : ℕ) : ∀ k : ℕ, (chebValZ d k : ℚ) = chebVal d k := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    match k with
    | 0 => simp [chebValZ, chebVal]
    | 1 => simp [chebValZ, chebVal]
    | m + 2 =>
      have h1 := ih (m + 1) (by omega)
      have h2 := ih m (by omega)
      simp only [chebValZ, chebVal, Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_one,
        h1, h2]

/-- Closed form `chebVal d k = (d - 1)^k + 1` for all `k ≥ 1`. -/
theorem chebVal_closed (d : ℕ) : ∀ k : ℕ, 1 ≤ k → chebVal d k = ((d : ℚ) - 1) ^ k + 1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk
    match k with
    | 0 => omega
    | 1 => simp [chebVal]
    | 2 =>
      simp only [chebVal]
      ring
    | m + 3 =>
      have h1 := ih (m + 2) (by omega) (by omega)
      have h2 := ih (m + 1) (by omega) (by omega)
      have hdef : chebVal d (m + 3) = (d : ℚ) * chebVal d (m + 2) - ((d : ℚ) - 1) * chebVal d (m + 1) := rfl
      rw [hdef, h1, h2]
      ring

/-- `A` commutes with every `chebMat A d k`. -/
theorem chebMat_comm_A (A : Matrix V V ℚ) (d : ℕ) :
    ∀ k : ℕ, A * chebMat A d k = chebMat A d k * A := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    match k with
    | 0 => simp [chebMat]
    | 1 => simp [chebMat]
    | m + 2 =>
      have h1 := ih (m + 1) (by omega)
      have h2 := ih m (by omega)
      simp only [chebMat, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
      rw [h2, h1, ← Matrix.mul_assoc, h1]

/-- Every `chebMat A d k` is symmetric when `A` is symmetric. -/
theorem chebMat_symm (A : Matrix V V ℚ) (d : ℕ) (hA : A.transpose = A) :
    ∀ k : ℕ, (chebMat A d k).transpose = chebMat A d k := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    match k with
    | 0 => simp [chebMat]
    | 1 => simpa [chebMat] using hA
    | m + 2 =>
      have h1 := ih (m + 1) (by omega)
      have h2 := ih m (by omega)
      simp only [chebMat, Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_smul,
        hA, h1, h2]
      rw [chebMat_comm_A]

omit [DecidableEq V] in
private lemma rowSum_mul (A B : Matrix V V ℚ) (rA rB : ℚ)
    (hA : ∀ u, ∑ v, A u v = rA) (hB : ∀ u, ∑ v, B u v = rB) :
    ∀ u, ∑ v, (A * B) u v = rA * rB := by
  intro u
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  have : ∀ x : V, ∑ v : V, A u x * B x v = A u x * rB := by
    intro x
    rw [← Finset.mul_sum, hB x]
  simp_rw [this]
  rw [← Finset.sum_mul, hA u]

/-- Every `chebMat A d k` has constant row sum `chebVal d k` on any `d`-regular graph. -/
theorem chebMat_rowSum (A : Matrix V V ℚ) (d : ℕ) (hreg : ∀ u, ∑ v, A u v = (d : ℚ)) :
    ∀ k : ℕ, ∀ u, ∑ v, chebMat A d k u v = chebVal d k := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro u
    match k with
    | 0 =>
      simp only [chebMat, chebVal, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
        mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    | 1 =>
      simpa [chebMat, chebVal] using hreg u
    | m + 2 =>
      have h1 := ih (m + 1) (by omega)
      have h2 := ih m (by omega)
      simp only [chebMat, chebVal, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
        Finset.sum_sub_distrib, ← Finset.mul_sum, h2 u]
      rw [rowSum_mul A (chebMat A d (m + 1)) (d : ℚ) (chebVal d (m + 1)) hreg h1 u]

/-- **Master Chebyshev–Hashimoto Matrix Product Law**:
    For all `0 ≤ k ≤ j`,
    `chebMat A d j * chebMat A d k = chebMat A d (j + k) + (d - 1)^k • chebMat A d (j - k)`. -/
theorem chebMat_mul (A : Matrix V V ℚ) (d : ℕ) :
    ∀ k : ℕ, ∀ j : ℕ, k ≤ j →
      chebMat A d j * chebMat A d k =
        chebMat A d (j + k) + (((d : ℚ) - 1) ^ k) • chebMat A d (j - k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro j hkj
    match k with
    | 0 =>
      simp only [chebMat, Nat.add_zero, Nat.sub_zero, pow_zero, one_smul,
        Matrix.mul_smul, Matrix.mul_one]
      rw [two_smul]
    | 1 =>
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hdef : chebMat A d (j' + 2) =
          A * chebMat A d (j' + 1) - ((d : ℚ) - 1) • chebMat A d j' := rfl
      have hsub : j' + 1 - 1 = j' := by omega
      have hadd : j' + 1 + 1 = j' + 2 := by omega
      rw [hadd, hsub, pow_one, chebMat, ← chebMat_comm_A, hdef]
      abel
    | m + 2 =>
      have hj1 : 1 ≤ j := by omega
      have hstep1 : chebMat A d j * A =
          chebMat A d (j + 1) + ((d : ℚ) - 1) • chebMat A d (j - 1) := by
        simpa [chebMat, pow_one] using ih 1 (by omega) j hj1
      have hmul1 := ih (m + 1) (by omega) (j + 1) (by omega)
      have hmul2 := ih (m + 1) (by omega) (j - 1) (by omega)
      have hmul3 := ih m (by omega) j (by omega)
      have heq1 : j + 1 + (m + 1) = j + (m + 2) := by omega
      have heq2 : j + 1 - (m + 1) = j - m := by omega
      have heq3 : j - 1 + (m + 1) = j + m := by omega
      have heq4 : j - 1 - (m + 1) = j - (m + 2) := by omega
      rw [heq1, heq2] at hmul1
      rw [heq3, heq4] at hmul2
      calc
        chebMat A d j * chebMat A d (m + 2)
            = chebMat A d j * (A * chebMat A d (m + 1) - ((d : ℚ) - 1) • chebMat A d m) := rfl
        _ = (chebMat A d j * A) * chebMat A d (m + 1) -
              ((d : ℚ) - 1) • (chebMat A d j * chebMat A d m) := by
              rw [Matrix.mul_sub, Matrix.mul_assoc, Matrix.mul_smul]
        _ = (chebMat A d (j + 1) + ((d : ℚ) - 1) • chebMat A d (j - 1)) * chebMat A d (m + 1) -
              ((d : ℚ) - 1) • (chebMat A d (j + m) + (((d : ℚ) - 1) ^ m) • chebMat A d (j - m)) := by
              rw [hstep1, hmul3]
        _ = chebMat A d (j + 1) * chebMat A d (m + 1) +
              ((d : ℚ) - 1) • (chebMat A d (j - 1) * chebMat A d (m + 1)) -
              ((d : ℚ) - 1) • (chebMat A d (j + m) + (((d : ℚ) - 1) ^ m) • chebMat A d (j - m)) := by
              rw [Matrix.add_mul, Matrix.smul_mul]
        _ = (chebMat A d (j + (m + 2)) + (((d : ℚ) - 1) ^ (m + 1)) • chebMat A d (j - m)) +
              ((d : ℚ) - 1) • (chebMat A d (j + m) + (((d : ℚ) - 1) ^ (m + 1)) • chebMat A d (j - (m + 2))) -
              ((d : ℚ) - 1) • (chebMat A d (j + m) + (((d : ℚ) - 1) ^ m) • chebMat A d (j - m)) := by
              rw [hmul1, hmul2]
        _ = chebMat A d (j + (m + 2)) + (((d : ℚ) - 1) ^ (m + 2)) • chebMat A d (j - (m + 2)) := by
              simp only [smul_add, smul_smul, pow_succ']
              abel

/-- Symmetric version of `chebMat_mul` for arbitrary `j, k : ℕ`. -/
theorem chebMat_mul_any (A : Matrix V V ℚ) (d : ℕ) (j k : ℕ) :
    chebMat A d j * chebMat A d k =
      chebMat A d (j + k) + (((d : ℚ) - 1) ^ (min j k)) • chebMat A d (if k ≤ j then j - k else k - j) := by
  by_cases h : k ≤ j
  · simp only [h, ↓reduceIte, Nat.min_eq_right h]
    exact chebMat_mul A d k j h
  · have hjk : j ≤ k := by omega
    simp only [h, ↓reduceIte, Nat.min_eq_left hjk]
    have hcomm : ∀ a b : ℕ, chebMat A d a * chebMat A d b = chebMat A d b * chebMat A d a := by
      intro a
      induction a using Nat.strong_induction_on with
      | ind a ih =>
        intro b
        match a with
        | 0 => simp [chebMat]
        | 1 => exact chebMat_comm_A A d b
        | m + 2 =>
          simp only [chebMat, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul]
          rw [Matrix.mul_assoc, ih (m + 1) (by omega) b, ← Matrix.mul_assoc,
            chebMat_comm_A A d b, Matrix.mul_assoc, ih m (by omega) b]
    rw [hcomm j k, Nat.add_comm j k]
    exact chebMat_mul A d j k hjk

end ChebyshevAlgebra

section BesselMultiCluster

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- Trace of the square of a symmetric matrix equals the sum of squared entries. -/
theorem symm_sq_trace_eq_sum_sq (M : Matrix V V ℚ) (hM : M.transpose = M) :
    Matrix.trace (M * M) = ∑ u : V, ∑ v : V, (M u v) ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  have hvu : M v u = M u v := by
    have := congr_fun (congr_fun hM u) v
    simpa [Matrix.transpose_apply] using this
  rw [hvu, sq]

/-- Elementary rational Cauchy–Schwarz on any finite set `T`. -/
theorem finset_sq_sum_le_card_mul_sum_sq {α : Type*} (T : Finset α) (f : α → ℚ) :
    (∑ x ∈ T, f x) ^ 2 ≤ (T.card : ℚ) * ∑ x ∈ T, (f x) ^ 2 := by
  have hnonneg : (0 : ℚ) ≤ ∑ x ∈ T, ∑ y ∈ T, (f x - f y) ^ 2 :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => sq_nonneg _
  have hexp : ∑ x ∈ T, ∑ y ∈ T, (f x - f y) ^ 2 =
      2 * ((T.card : ℚ) * ∑ x ∈ T, (f x) ^ 2 - (∑ x ∈ T, f x) ^ 2) := by
    have h1 : ∀ x ∈ T, ∑ y ∈ T, (f x - f y) ^ 2 =
        (T.card : ℚ) * (f x) ^ 2 - 2 * f x * (∑ y ∈ T, f y) + ∑ y ∈ T, (f y) ^ 2 := by
      intro x _
      calc
        ∑ y ∈ T, (f x - f y) ^ 2
            = ∑ y ∈ T, ((f x) ^ 2 - 2 * f x * f y + (f y) ^ 2) := by
              refine Finset.sum_congr rfl fun y _ => by ring
        _ = (∑ _y ∈ T, (f x) ^ 2) - (∑ y ∈ T, 2 * f x * f y) + ∑ y ∈ T, (f y) ^ 2 := by
              rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        _ = (T.card : ℚ) * (f x) ^ 2 - 2 * f x * (∑ y ∈ T, f y) + ∑ y ∈ T, (f y) ^ 2 := by
              simp [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hmid : ∑ x ∈ T, 2 * f x * (∑ y ∈ T, f y) = 2 * (∑ x ∈ T, f x) ^ 2 := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      ring
    rw [hmid]
    simp only [← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    ring
  linarith

/-- Sum of entries of `M` over a cluster `S × S`. -/
def clusterSum (M : Matrix V V ℚ) (S : Finset V) : ℚ :=
  ∑ u ∈ S, ∑ v ∈ S, M u v

omit [Fintype V] [DecidableEq V] in
/-- Single-cluster squared-sum bound: `(clusterSum M S)^2 / |S|^2 ≤ ∑_{u,v ∈ S} (M u v)^2`. -/
theorem clusterSum_sq_div_le (M : Matrix V V ℚ) (S : Finset V) (hS : S.Nonempty) :
    (clusterSum M S) ^ 2 / ((S.card : ℚ) ^ 2) ≤ ∑ u ∈ S, ∑ v ∈ S, (M u v) ^ 2 := by
  have hcard_pos : (0 : ℚ) < (S.card : ℚ) := by
    exact_mod_cast Finset.card_pos.mpr hS
  have hsq_pos : (0 : ℚ) < (S.card : ℚ) ^ 2 := sq_pos_of_pos hcard_pos
  rw [div_le_iff₀ hsq_pos]
  have hcs := finset_sq_sum_le_card_mul_sum_sq (S ×ˢ S) (fun p : V × V => M p.1 p.2)
  rw [Finset.card_product, Nat.cast_mul, ← sq] at hcs
  have hsum1 : ∑ p ∈ S ×ˢ S, M p.1 p.2 = clusterSum M S := by
    rw [Finset.sum_product]; rfl
  have hsum2 : ∑ p ∈ S ×ˢ S, (M p.1 p.2) ^ 2 = ∑ u ∈ S, ∑ v ∈ S, (M u v) ^ 2 := by
    rw [Finset.sum_product]
  rw [hsum1, hsum2] at hcs
  linarith

/-- **Eigenvalue-Free Bessel Multi-Cluster Matrix-Square Inequality** (Unbounded-`n` Engine):
    For any symmetric matrix `M : Matrix V V ℚ` and any finite family of pairwise disjoint
    non-empty vertex subsets `{S i}_{i ∈ J}`,
    `∑ i ∈ J, (clusterSum M (S i))^2 / |S i|^2 ≤ Tr(M^2)`. -/
theorem bessel_multi_cluster_sq_trace_ge {ι : Type*} [DecidableEq ι]
    (M : Matrix V V ℚ) (hM : M.transpose = M)
    (J : Finset ι) (S : ι → Finset V)
    (hne : ∀ i ∈ J, (S i).Nonempty)
    (hdisj : Set.PairwiseDisjoint (J : Set ι) S) :
    ∑ i ∈ J, (clusterSum M (S i)) ^ 2 / ((S i).card : ℚ) ^ 2 ≤ Matrix.trace (M * M) := by
  have h1 : ∑ i ∈ J, (clusterSum M (S i)) ^ 2 / ((S i).card : ℚ) ^ 2 ≤
      ∑ i ∈ J, ∑ p ∈ S i ×ˢ S i, (M p.1 p.2) ^ 2 := by
    refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.sum_product]
    exact clusterSum_sq_div_le M (S i) (hne i hi)
  have hpair : Set.PairwiseDisjoint (J : Set ι) (fun i => S i ×ˢ S i) := by
    intro i hi j hj hij
    dsimp [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have hdj := hdisj hi hj hij
    exact Finset.disjoint_left.mp hdj (Finset.mem_product.mp hp1).1 (Finset.mem_product.mp hp2).1
  have h2 : ∑ i ∈ J, ∑ p ∈ S i ×ˢ S i, (M p.1 p.2) ^ 2 =
      ∑ p ∈ J.biUnion (fun i => S i ×ˢ S i), (M p.1 p.2) ^ 2 :=
    (Finset.sum_biUnion hpair).symm
  have h3 : ∑ p ∈ J.biUnion (fun i => S i ×ˢ S i), (M p.1 p.2) ^ 2 ≤
      ∑ p ∈ (Finset.univ : Finset (V × V)), (M p.1 p.2) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
  have h4 : ∑ p ∈ (Finset.univ : Finset (V × V)), (M p.1 p.2) ^ 2 = Matrix.trace (M * M) := by
    rw [symm_sq_trace_eq_sum_sq M hM, Fintype.sum_prod_type]
  linarith

/-- Specialization to the single full-graph cluster `S = univ`:
    for any symmetric `M` with constant row sum `μ` on a non-empty vertex set `V`,
    `μ ^ 2 ≤ Tr(M^2)`. -/
theorem single_cluster_sq_trace_ge [Nonempty V] (M : Matrix V V ℚ) (hM : M.transpose = M) (μ : ℚ)
    (hrow : ∀ u, ∑ v, M u v = μ) :
    μ ^ 2 ≤ Matrix.trace (M * M) := by
  have hne : (Finset.univ : Finset V).Nonempty := Finset.univ_nonempty
  have hb := bessel_multi_cluster_sq_trace_ge M hM ({()} : Finset Unit) (fun _ => Finset.univ)
    (fun _ _ => hne) (by intro a _ b _ hab; exact (hab rfl).elim)
  simp only [Finset.sum_singleton] at hb
  have hcs : clusterSum M Finset.univ = (Fintype.card V : ℚ) * μ := by
    simp only [clusterSum, hrow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard_ne : (Fintype.card V : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [hcs, Finset.card_univ] at hb
  have hsimp : ((Fintype.card V : ℚ) * μ) ^ 2 / (Fintype.card V : ℚ) ^ 2 = μ ^ 2 := by
    field_simp [hcard_ne]
  linarith

end BesselMultiCluster

section DelsarteSOSEngine

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Fast recursive integer sum over `0 .. n - 1` for kernel `decide` evaluation. -/
def sumRangeZ : ℕ → (ℕ → ℤ) → ℤ
  | 0, _ => 0
  | n + 1, f => sumRangeZ n f + f n

theorem sumRangeZ_cast (n : ℕ) (f : ℕ → ℤ) :
    (sumRangeZ n f : ℚ) = ∑ i ∈ Finset.range n, (f i : ℚ) := by
  induction n with
  | zero => simp [sumRangeZ]
  | succ n ih => simp [sumRangeZ, Finset.sum_range_succ, ih]

/-- Linear combination `P(A) = ∑_{j < c.length} (c_j : ℚ) • T_j(A)` from integer coefficients `c`. -/
def polyMat (A : Matrix V V ℚ) (d : ℕ) (c : List ℤ) : Matrix V V ℚ :=
  ∑ j ∈ Finset.range c.length, (c.getD j 0 : ℚ) • chebMat A d j

/-- Integer scalar value `P(d) = ∑_{j < c.length} c_j * T_j(d)`. -/
def polyValZ (d : ℕ) (c : List ℤ) : ℤ :=
  sumRangeZ c.length (fun j => c.getD j 0 * chebValZ d j)

theorem polyMat_symm (A : Matrix V V ℚ) (d : ℕ) (hA : A.transpose = A) (c : List ℤ) :
    (polyMat A d c).transpose = polyMat A d c := by
  simp only [polyMat, Matrix.transpose_sum, Matrix.transpose_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [chebMat_symm A d hA j]

theorem polyMat_rowSum (A : Matrix V V ℚ) (d : ℕ) (hreg : ∀ u, ∑ v, A u v = (d : ℚ))
    (c : List ℤ) : ∀ u, ∑ v, polyMat A d c u v = (polyValZ d c : ℚ) := by
  intro u
  simp only [polyMat, polyValZ, sumRangeZ_cast, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum, chebMat_rowSum A d hreg j u, Int.cast_mul, chebValZ_cast]

/-- Exact integer `k`-th coefficient of `(∑_j c_j T_j)^2` in the `T_k` basis. -/
def sqCoeffAtZ (d : ℕ) (c : List ℤ) (k : ℕ) : ℤ :=
  sumRangeZ c.length (fun j =>
    sumRangeZ c.length (fun l =>
      c.getD j 0 * c.getD l 0 *
        ((if j + l = k then (1 : ℤ) else 0) +
         (if (if l ≤ j then j - l else l - j) = k then ((d : ℤ) - 1) ^ (min j l) else 0))))

/-- Exact integer `k`-th coefficient of `P_1(A)^2 + P_2(A)^2` in the `T_k` basis. -/
def twoSqCoeffAtZ (d : ℕ) (c1 c2 : List ℤ) (k : ℕ) : ℤ :=
  sqCoeffAtZ d c1 k + sqCoeffAtZ d c2 k

/-- Exact integer Kesten–McKay denominator `D(F) = 2 F_0 - (d - 2) ∑_{1 ≤ k ≤ L, Even k} F_k`. -/
def kmDenomZ (d L : ℕ) (F : ℕ → ℤ) : ℤ :=
  2 * F 0 - ((d : ℤ) - 2) * sumRangeZ (L + 1) (fun k => if (1 ≤ k ∧ k % 2 = 0) then F k else 0)

theorem polyMat_sq_trace_eq (A : Matrix V V ℚ) (d L : ℕ) (c : List ℤ)
    (hdeg : ∀ j < c.length, ∀ l < c.length, j + l ≤ L) :
    Matrix.trace (polyMat A d c * polyMat A d c) =
      ∑ k ∈ Finset.range (L + 1), (sqCoeffAtZ d c k : ℚ) * Matrix.trace (chebMat A d k) := by
  have hexp : polyMat A d c * polyMat A d c =
      ∑ j ∈ Finset.range c.length, ∑ l ∈ Finset.range c.length,
        ((c.getD j 0 : ℚ) * (c.getD l 0 : ℚ)) • (chebMat A d j * chebMat A d l) := by
    simp only [polyMat]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm]
  rw [hexp]
  simp only [Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
  have hterm : ∀ j ∈ Finset.range c.length, ∀ l ∈ Finset.range c.length,
      (c.getD j 0 : ℚ) * (c.getD l 0 : ℚ) * Matrix.trace (chebMat A d j * chebMat A d l) =
      ∑ k ∈ Finset.range (L + 1),
        (c.getD j 0 : ℚ) * (c.getD l 0 : ℚ) *
          ((if j + l = k then (1 : ℚ) else 0) +
           (if (if l ≤ j then j - l else l - j) = k then ((d : ℚ) - 1) ^ (min j l) else 0)) *
          Matrix.trace (chebMat A d k) := by
    intro j hj l hl
    rw [Finset.mem_range] at hj hl
    have hadd_mem : j + l ∈ Finset.range (L + 1) := Finset.mem_range.mpr (by have := hdeg j hj l hl; omega)
    have hdiff_mem : (if l ≤ j then j - l else l - j) ∈ Finset.range (L + 1) := by
      rw [Finset.mem_range]
      have := hdeg j hj l hl
      split_ifs <;> omega
    rw [chebMat_mul_any A d j l, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
    simp_rw [mul_add, add_mul, Finset.sum_add_distrib]
    have hs1 : ∑ k ∈ Finset.range (L + 1),
        (c.getD j 0 : ℚ) * (c.getD l 0 : ℚ) * (if j + l = k then (1 : ℚ) else 0) * Matrix.trace (chebMat A d k) =
        (c.getD j 0 : ℚ) * (c.getD l 0 : ℚ) * Matrix.trace (chebMat A d (j + l)) := by
      have : ∀ k ∈ Finset.range (L + 1),
          (c.getD j 0 : ℚ) * (c.getD l 0 : ℚ) * (if j + l = k then (1 : ℚ) else 0) * Matrix.trace (chebMat A d k) =
          if j + l = k then (c.getD j 0 : ℚ) * (c.getD l 0 : ℚ) * Matrix.trace (chebMat A d k) else 0 := by
        intro k _; split_ifs <;> ring
      rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
      simp [hadd_mem]
    have hs2 : ∑ k ∈ Finset.range (L + 1),
        (c.getD j 0 : ℚ) * (c.getD l 0 : ℚ) *
          (if (if l ≤ j then j - l else l - j) = k then ((d : ℚ) - 1) ^ (min j l) else 0) *
          Matrix.trace (chebMat A d k) =
        (c.getD j 0 : ℚ) * (c.getD l 0 : ℚ) *
          (((d : ℚ) - 1) ^ (min j l) * Matrix.trace (chebMat A d (if l ≤ j then j - l else l - j))) := by
      have : ∀ k ∈ Finset.range (L + 1),
          (c.getD j 0 : ℚ) * (c.getD l 0 : ℚ) *
            (if (if l ≤ j then j - l else l - j) = k then ((d : ℚ) - 1) ^ (min j l) else 0) *
            Matrix.trace (chebMat A d k) =
          if (if l ≤ j then j - l else l - j) = k then
            (c.getD j 0 : ℚ) * (c.getD l 0 : ℚ) * (((d : ℚ) - 1) ^ (min j l) * Matrix.trace (chebMat A d k))
          else 0 := by
        intro k _; split_ifs <;> ring
      rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
      simp [hdiff_mem]
    rw [hs1, hs2]
  calc
    ∑ j ∈ Finset.range c.length, ∑ l ∈ Finset.range c.length,
        (c.getD j 0 : ℚ) * (c.getD l 0 : ℚ) * Matrix.trace (chebMat A d j * chebMat A d l)
        = ∑ j ∈ Finset.range c.length, ∑ l ∈ Finset.range c.length, ∑ k ∈ Finset.range (L + 1),
            (c.getD j 0 : ℚ) * (c.getD l 0 : ℚ) *
              ((if j + l = k then (1 : ℚ) else 0) +
               (if (if l ≤ j then j - l else l - j) = k then ((d : ℚ) - 1) ^ (min j l) else 0)) *
              Matrix.trace (chebMat A d k) :=
          Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun l hl => hterm j hj l hl
    _ = ∑ j ∈ Finset.range c.length, ∑ k ∈ Finset.range (L + 1), ∑ l ∈ Finset.range c.length,
            (c.getD j 0 : ℚ) * (c.getD l 0 : ℚ) *
              ((if j + l = k then (1 : ℚ) else 0) +
               (if (if l ≤ j then j - l else l - j) = k then ((d : ℚ) - 1) ^ (min j l) else 0)) *
              Matrix.trace (chebMat A d k) :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ k ∈ Finset.range (L + 1), ∑ j ∈ Finset.range c.length, ∑ l ∈ Finset.range c.length,
            (c.getD j 0 : ℚ) * (c.getD l 0 : ℚ) *
              ((if j + l = k then (1 : ℚ) else 0) +
               (if (if l ≤ j then j - l else l - j) = k then ((d : ℚ) - 1) ^ (min j l) else 0)) *
              Matrix.trace (chebMat A d k) :=
          Finset.sum_comm
    _ = ∑ k ∈ Finset.range (L + 1), (sqCoeffAtZ d c k : ℚ) * Matrix.trace (chebMat A d k) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          simp only [sqCoeffAtZ, sumRangeZ_cast, Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
          push_cast
          rfl

theorem trace_sum_eq_kmDenom_add_walks (A : Matrix V V ℚ) (d L : ℕ) (F : ℕ → ℤ) (b : ℕ → ℚ)
    (htr0 : Matrix.trace (chebMat A d 0) = 2 * (Fintype.card V : ℚ))
    (htr_even : ∀ k, 1 ≤ k → k ≤ L → k % 2 = 0 →
      Matrix.trace (chebMat A d k) = b k - ((d : ℚ) - 2) * (Fintype.card V : ℚ))
    (htr_odd : ∀ k, 1 ≤ k → k ≤ L → k % 2 ≠ 0 →
      Matrix.trace (chebMat A d k) = b k) :
    ∑ k ∈ Finset.range (L + 1), (F k : ℚ) * Matrix.trace (chebMat A d k) =
      (Fintype.card V : ℚ) * (kmDenomZ d L F : ℚ) +
        ∑ k ∈ Finset.Icc 1 L, (F k : ℚ) * b k := by
  have hsplit : ∑ k ∈ Finset.range (L + 1), (F k : ℚ) * Matrix.trace (chebMat A d k) =
      (F 0 : ℚ) * Matrix.trace (chebMat A d 0) +
        ∑ k ∈ Finset.Icc 1 L, (F k : ℚ) * Matrix.trace (chebMat A d k) := by
    have hrange : Finset.range (L + 1) = insert 0 (Finset.Icc 1 L) := by
      ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hrange, Finset.sum_insert (by simp)]
  have hmid : ∑ k ∈ Finset.Icc 1 L, (F k : ℚ) * Matrix.trace (chebMat A d k) =
      ∑ k ∈ Finset.Icc 1 L, (F k : ℚ) * b k -
        ((d : ℚ) - 2) * (Fintype.card V : ℚ) *
          ∑ k ∈ Finset.range (L + 1), ((if (1 ≤ k ∧ k % 2 = 0) then F k else 0 : ℤ) : ℚ) := by
    have hterm : ∀ k ∈ Finset.Icc 1 L,
        (F k : ℚ) * Matrix.trace (chebMat A d k) =
        (F k : ℚ) * b k - ((d : ℚ) - 2) * (Fintype.card V : ℚ) *
          ((if (1 ≤ k ∧ k % 2 = 0) then F k else 0 : ℤ) : ℚ) := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      by_cases hev : k % 2 = 0
      · rw [htr_even k hk.1 hk.2 hev]
        simp only [hk.1, hev, and_self, ↓reduceIte]
        ring
      · rw [htr_odd k hk.1 hk.2 hev]
        simp [hev]
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hzero : ∑ k ∈ Finset.range (L + 1), ((if (1 ≤ k ∧ k % 2 = 0) then F k else 0 : ℤ) : ℚ) =
        ∑ k ∈ Finset.Icc 1 L, ((if (1 ≤ k ∧ k % 2 = 0) then F k else 0 : ℤ) : ℚ) := by
      have hrange : Finset.range (L + 1) = insert 0 (Finset.Icc 1 L) := by
        ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
      rw [hrange, Finset.sum_insert (by simp)]
      simp
    rw [hzero]
  rw [hsplit, htr0, hmid, kmDenomZ]
  push_cast [sumRangeZ_cast]
  ring

/-- **Master Unbounded-`n` Bessel Multi-Cluster Delsarte SOS Forcing Theorem**:
    For ANY finite `d`-regular graph (of ARBITRARY unbounded order `n`) satisfying the Chebyshev
    trace-to-walk relations, if `P_1^2 + P_2^2` has nonpositive coefficients on `[g, L-1]` (or even
    indices in `[g, L-1]` for bipartite graphs), positive leading coefficient `F_L > 0`, and
    the multi-cluster Bessel spectral excess exceeds `n * kmDenomZ d L F`, then `0 < b L`. -/
theorem delsarte_bessel_unbounded_n_forces_bL {ι : Type*} [DecidableEq ι]
    (A : Matrix V V ℚ) (d g L : ℕ) (bip : Bool) (c1 c2 : List ℤ) (b : ℕ → ℚ)
    (hA : A.transpose = A) (hL : 1 ≤ L)
    (hdeg1 : ∀ j < c1.length, ∀ l < c1.length, j + l ≤ L)
    (hdeg2 : ∀ j < c2.length, ∀ l < c2.length, j + l ≤ L)
    (htr0 : Matrix.trace (chebMat A d 0) = 2 * (Fintype.card V : ℚ))
    (htr_even : ∀ k, 1 ≤ k → k ≤ L → k % 2 = 0 →
      Matrix.trace (chebMat A d k) = b k - ((d : ℚ) - 2) * (Fintype.card V : ℚ))
    (htr_odd : ∀ k, 1 ≤ k → k ≤ L → k % 2 ≠ 0 →
      Matrix.trace (chebMat A d k) = b k)
    (hb_nonneg : ∀ k, 1 ≤ k → k ≤ L → 0 ≤ b k)
    (hgirth : ∀ k, 1 ≤ k → k < g → b k = 0)
    (hbip : bip = true → ∀ k, 1 ≤ k → k ≤ L → k % 2 ≠ 0 → b k = 0)
    (hforb : ∀ k, g ≤ k → k < L → (bip = true → k % 2 = 0) → twoSqCoeffAtZ d c1 c2 k ≤ 0)
    (hlead : 0 < twoSqCoeffAtZ d c1 c2 L)
    (J : Finset ι) (S : ι → Finset V)
    (hne : ∀ i ∈ J, (S i).Nonempty)
    (hdisj : Set.PairwiseDisjoint (J : Set ι) S)
    (hexcess : (Fintype.card V : ℚ) * (kmDenomZ d L (twoSqCoeffAtZ d c1 c2) : ℚ) <
      ∑ i ∈ J, ((clusterSum (polyMat A d c1) (S i)) ^ 2 +
                (clusterSum (polyMat A d c2) (S i)) ^ 2) / ((S i).card : ℚ) ^ 2) :
    0 < b L := by
  have hb1 := bessel_multi_cluster_sq_trace_ge (polyMat A d c1) (polyMat_symm A d hA c1) J S hne hdisj
  have hb2 := bessel_multi_cluster_sq_trace_ge (polyMat A d c2) (polyMat_symm A d hA c2) J S hne hdisj
  have hsum_b : ∑ i ∈ J, ((clusterSum (polyMat A d c1) (S i)) ^ 2 +
      (clusterSum (polyMat A d c2) (S i)) ^ 2) / ((S i).card : ℚ) ^ 2 ≤
      Matrix.trace (polyMat A d c1 * polyMat A d c1) +
      Matrix.trace (polyMat A d c2 * polyMat A d c2) := by
    have : ∑ i ∈ J, ((clusterSum (polyMat A d c1) (S i)) ^ 2 +
        (clusterSum (polyMat A d c2) (S i)) ^ 2) / ((S i).card : ℚ) ^ 2 =
        (∑ i ∈ J, (clusterSum (polyMat A d c1) (S i)) ^ 2 / ((S i).card : ℚ) ^ 2) +
        (∑ i ∈ J, (clusterSum (polyMat A d c2) (S i)) ^ 2 / ((S i).card : ℚ) ^ 2) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => add_div _ _ _
    linarith
  have hexp1 := polyMat_sq_trace_eq A d L c1 hdeg1
  have hexp2 := polyMat_sq_trace_eq A d L c2 hdeg2
  have htot : Matrix.trace (polyMat A d c1 * polyMat A d c1) +
      Matrix.trace (polyMat A d c2 * polyMat A d c2) =
      ∑ k ∈ Finset.range (L + 1), (twoSqCoeffAtZ d c1 c2 k : ℚ) * Matrix.trace (chebMat A d k) := by
    rw [hexp1, hexp2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => by simp only [twoSqCoeffAtZ, Int.cast_add]; ring
  have hwalk := trace_sum_eq_kmDenom_add_walks A d L (twoSqCoeffAtZ d c1 c2) b htr0 htr_even htr_odd
  have hpos_sum : 0 < ∑ k ∈ Finset.Icc 1 L, (twoSqCoeffAtZ d c1 c2 k : ℚ) * b k := by
    linarith
  have hsplitL : ∑ k ∈ Finset.Icc 1 L, (twoSqCoeffAtZ d c1 c2 k : ℚ) * b k =
      (∑ k ∈ Finset.Ico 1 L, (twoSqCoeffAtZ d c1 c2 k : ℚ) * b k) +
      (twoSqCoeffAtZ d c1 c2 L : ℚ) * b L := by
    have hset : Finset.Icc 1 L = insert L (Finset.Ico 1 L) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]; omega
    rw [hset, Finset.sum_insert (by simp)]
    ring
  have hrest_le : ∑ k ∈ Finset.Ico 1 L, (twoSqCoeffAtZ d c1 c2 k : ℚ) * b k ≤ 0 := by
    refine Finset.sum_nonpos fun k hk => ?_
    rw [Finset.mem_Ico] at hk
    by_cases hkg : k < g
    · rw [hgirth k hk.1 hkg, mul_zero]
    · by_cases hbp : bip = true ∧ k % 2 ≠ 0
      · rw [hbip hbp.1 k hk.1 (by omega) hbp.2, mul_zero]
      · have hfk : twoSqCoeffAtZ d c1 c2 k ≤ 0 := hforb k (by omega) hk.2 (by
          intro hb; by_contra hodd; exact hbp ⟨hb, hodd⟩)
        have hfkq : (twoSqCoeffAtZ d c1 c2 k : ℚ) ≤ 0 := by exact_mod_cast hfk
        exact mul_nonpos_of_nonpos_of_nonneg hfkq (hb_nonneg k hk.1 (by omega))
  have hleadq : (0 : ℚ) < (twoSqCoeffAtZ d c1 c2 L : ℚ) := by exact_mod_cast hlead
  have hFbL : 0 < (twoSqCoeffAtZ d c1 c2 L : ℚ) * b L := by linarith
  by_contra hle
  have hle' : b L ≤ 0 := not_lt.mp hle
  have : (twoSqCoeffAtZ d c1 c2 L : ℚ) * b L ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt hleadq) hle'
  linarith

/-- **Master Finite-`n` Delsarte 2-Square SOS Forcing Theorem** (Single Full-Graph Cluster). -/
theorem delsarte_two_sq_forces_bL [Nonempty V]
    (A : Matrix V V ℚ) (d g L : ℕ) (bip : Bool) (c1 c2 : List ℤ) (b : ℕ → ℚ)
    (hA : A.transpose = A) (hreg : ∀ u, ∑ v, A u v = (d : ℚ)) (hL : 1 ≤ L)
    (hdeg1 : ∀ j < c1.length, ∀ l < c1.length, j + l ≤ L)
    (hdeg2 : ∀ j < c2.length, ∀ l < c2.length, j + l ≤ L)
    (htr0 : Matrix.trace (chebMat A d 0) = 2 * (Fintype.card V : ℚ))
    (htr_even : ∀ k, 1 ≤ k → k ≤ L → k % 2 = 0 →
      Matrix.trace (chebMat A d k) = b k - ((d : ℚ) - 2) * (Fintype.card V : ℚ))
    (htr_odd : ∀ k, 1 ≤ k → k ≤ L → k % 2 ≠ 0 →
      Matrix.trace (chebMat A d k) = b k)
    (hb_nonneg : ∀ k, 1 ≤ k → k ≤ L → 0 ≤ b k)
    (hgirth : ∀ k, 1 ≤ k → k < g → b k = 0)
    (hbip : bip = true → ∀ k, 1 ≤ k → k ≤ L → k % 2 ≠ 0 → b k = 0)
    (hforb : ∀ k, g ≤ k → k < L → (bip = true → k % 2 = 0) → twoSqCoeffAtZ d c1 c2 k ≤ 0)
    (hlead : 0 < twoSqCoeffAtZ d c1 c2 L)
    (hn : (Fintype.card V : ℚ) * (kmDenomZ d L (twoSqCoeffAtZ d c1 c2) : ℚ) <
      (polyValZ d c1 : ℚ) ^ 2 + (polyValZ d c2 : ℚ) ^ 2) :
    0 < b L := by
  apply delsarte_bessel_unbounded_n_forces_bL A d g L bip c1 c2 b hA hL hdeg1 hdeg2
    htr0 htr_even htr_odd hb_nonneg hgirth hbip hforb hlead
    ({()} : Finset Unit) (fun _ => Finset.univ)
    (fun _ _ => Finset.univ_nonempty) (by intro a _ b _ hab; exact (hab rfl).elim)
  simp only [Finset.sum_singleton, Finset.card_univ]
  have hcs1 : clusterSum (polyMat A d c1) Finset.univ = (Fintype.card V : ℚ) * (polyValZ d c1 : ℚ) := by
    simp only [clusterSum, polyMat_rowSum A d hreg c1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcs2 : clusterSum (polyMat A d c2) Finset.univ = (Fintype.card V : ℚ) * (polyValZ d c2 : ℚ) := by
    simp only [clusterSum, polyMat_rowSum A d hreg c2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard_ne : (Fintype.card V : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [hcs1, hcs2]
  have hsimp : (((Fintype.card V : ℚ) * (polyValZ d c1 : ℚ)) ^ 2 +
      ((Fintype.card V : ℚ) * (polyValZ d c2 : ℚ)) ^ 2) /
      (Fintype.card V : ℚ) ^ 2 = (polyValZ d c1 : ℚ) ^ 2 + (polyValZ d c2 : ℚ) ^ 2 := by
    field_simp [hcard_ne]
  linarith

end DelsarteSOSEngine

section CertifiedGirthBounds

/-- Pure integer certificate bundle for cubic (`d = 3`) Delsarte 2-square SOS thresholds. -/
def ValidCubicCert (g L n_max : ℕ) (bip : Bool) (c1 c2 : List ℤ) : Prop :=
  (∀ j < c1.length, ∀ l < c1.length, j + l ≤ L) ∧
  (∀ j < c2.length, ∀ l < c2.length, j + l ≤ L) ∧
  (∀ k, g ≤ k → k < L → (bip = true → k % 2 = 0) → twoSqCoeffAtZ 3 c1 c2 k ≤ 0) ∧
  0 < twoSqCoeffAtZ 3 c1 c2 L ∧
  0 < kmDenomZ 3 L (twoSqCoeffAtZ 3 c1 c2) ∧
  (n_max : ℤ) * kmDenomZ 3 L (twoSqCoeffAtZ 3 c1 c2) < (polyValZ 3 c1) ^ 2 + (polyValZ 3 c2) ^ 2

/-- Any valid cubic certificate closes all `n ≤ n_max` unconditionally. -/
theorem cubic_cert_forces_bL {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : Matrix V V ℚ) (g L n_max : ℕ) (bip : Bool) (c1 c2 : List ℤ) (b : ℕ → ℚ)
    (hcert : ValidCubicCert g L n_max bip c1 c2)
    (hA : A.transpose = A) (hreg : ∀ u, ∑ v, A u v = 3) (hL : 1 ≤ L)
    (htr0 : Matrix.trace (chebMat A 3 0) = 2 * (Fintype.card V : ℚ))
    (htr_even : ∀ k, 1 ≤ k → k ≤ L → k % 2 = 0 →
      Matrix.trace (chebMat A 3 k) = b k - (3 - 2) * (Fintype.card V : ℚ))
    (htr_odd : ∀ k, 1 ≤ k → k ≤ L → k % 2 ≠ 0 →
      Matrix.trace (chebMat A 3 k) = b k)
    (hb_nonneg : ∀ k, 1 ≤ k → k ≤ L → 0 ≤ b k)
    (hgirth : ∀ k, 1 ≤ k → k < g → b k = 0)
    (hbip : bip = true → ∀ k, 1 ≤ k → k ≤ L → k % 2 ≠ 0 → b k = 0)
    (hn : Fintype.card V ≤ n_max) :
    0 < b L := by
  rcases hcert with ⟨hd1, hd2, hforb, hlead, hDpos, hbound⟩
  have hle : (Fintype.card V : ℚ) ≤ (n_max : ℚ) := by exact_mod_cast hn
  have hDposq : (0 : ℚ) < (kmDenomZ 3 L (twoSqCoeffAtZ 3 c1 c2) : ℚ) := by exact_mod_cast hDpos
  have hboundq : (n_max : ℚ) * (kmDenomZ 3 L (twoSqCoeffAtZ 3 c1 c2) : ℚ) <
      (polyValZ 3 c1 : ℚ) ^ 2 + (polyValZ 3 c2 : ℚ) ^ 2 := by exact_mod_cast hbound
  have hmul : (Fintype.card V : ℚ) * (kmDenomZ 3 L (twoSqCoeffAtZ 3 c1 c2) : ℚ) ≤
      (n_max : ℚ) * (kmDenomZ 3 L (twoSqCoeffAtZ 3 c1 c2) : ℚ) :=
    mul_le_mul_of_nonneg_right hle (le_of_lt hDposq)
  exact delsarte_two_sq_forces_bL A 3 g L bip c1 c2 b hA (by simpa using hreg) hL hd1 hd2
    htr0 (by simpa using htr_even) htr_odd hb_nonneg hgirth hbip hforb hlead (lt_of_le_of_lt hmul hboundq)

/-- **Certificate 1 (`g ≥ 7, L = 8`, general cubic, `n ≤ 33`)**. -/
theorem cert_girth7_c8_n33 :
    ValidCubicCert 7 8 33 false [2, 1, 2, 0, 1] [] := by
  refine ⟨by intro j hj l hl; simp at hj hl; omega,
          by intro j hj; simp at hj,
          ?_, by decide, by decide, by decide⟩
  intro k hlo hhi _
  interval_cases k
  decide

/-- **Certificate 2 (`g ≥ 10, L = 16`, general cubic, `n ≤ 134`)**. -/
theorem cert_girth10_c16_n134 :
    ValidCubicCert 10 16 134 false [3, 4, 0, 0, 0, 0, 0, 0, 2] [] := by
  refine ⟨by intro j hj l hl; simp at hj hl; omega,
          by intro j hj; simp at hj,
          ?_, by decide, by decide, by decide⟩
  intro k hlo hhi _
  interval_cases k <;> decide

/-- **Certificate 3 (`g ≥ 10, L = 16`, bipartite cubic, `n ≤ 201`)**. -/
theorem cert_girth10_bip_c16_n201 :
    ValidCubicCert 10 16 201 true [12, 250, -72, 108, -21, 46, -5, 19, 45] [] := by
  refine ⟨by intro j hj l hl; simp at hj hl; omega,
          by intro j hj; simp at hj,
          ?_, by decide, by decide, by decide⟩
  intro k hlo hhi hev
  have hk : k % 2 = 0 := hev rfl
  interval_cases k <;> try omega
  all_goals decide

/-- **Certificate 4 (`g ≥ 11, L = 16`, general cubic, `n ≤ 148`)**. -/
theorem cert_girth11_c16_n148 :
    ValidCubicCert 11 16 148 false [20, 13, 20, 0, 0, 0, 0, 0, 7] [] := by
  refine ⟨by intro j hj l hl; simp at hj hl; omega,
          by intro j hj; simp at hj,
          ?_, by decide, by decide, by decide⟩
  intro k hlo hhi _
  interval_cases k <;> decide

/-- **Certificate 5 (`g ≥ 12, L = 16`, general cubic, `n ≤ 159`)**. -/
theorem cert_girth12_c16_n159 :
    ValidCubicCert 12 16 159 false
      [183, 250, 183, 125, -14, -4, -1, 0, 70]
      [-173, -245, -173, -123, -87, -54, -28, -10, 0] := by
  refine ⟨by intro j hj l hl; simp at hj hl; omega,
          by intro j hj l hl; simp at hj hl; omega,
          ?_, by decide, by decide, by decide⟩
  intro k hlo hhi _
  interval_cases k <;> decide

/-- **Certificate 6 (`g ≥ 12, L = 16`, bipartite cubic, `n ≤ 239`)**. -/
theorem cert_girth12_bip_c16_n239 :
    ValidCubicCert 12 16 239 true [268, 1000, 269, 499, -92, 197, -15, 64, 139] [] := by
  refine ⟨by intro j hj l hl; simp at hj hl; omega,
          by intro j hj; simp at hj,
          ?_, by decide, by decide, by decide⟩
  intro k hlo hhi hev
  have hk : k % 2 = 0 := hev rfl
  interval_cases k <;> try omega
  all_goals decide

/-- **Certificate 7 (`g ≥ 13, L = 16`, general cubic, `n ≤ 219`)**. -/
theorem cert_girth13_c16_n219 :
    ValidCubicCert 13 16 219 false
      [401, 198, 401, 99, 201, -25, -5, 0, 81]
      [-337, -500, -337, -250, -169, -125, -72, -28, 0] := by
  refine ⟨by intro j hj l hl; simp at hj hl; omega,
          by intro j hj l hl; simp at hj hl; omega,
          ?_, by decide, by decide, by decide⟩
  intro k hlo hhi _
  interval_cases k <;> decide

/-- **Certificate 8 (`g ≥ 14, L = 16`, general cubic, `n ≤ 268`)**. -/
theorem cert_girth14_c16_n268 :
    ValidCubicCert 14 16 268 false
      [16, 23, 16, 11, 8, 6, -2, 0, 4]
      [-35, -50, -35, -25, -18, -13, -9, -4, 0] := by
  refine ⟨by intro j hj l hl; simp at hj hl; omega,
          by intro j hj l hl; simp at hj hl; omega,
          ?_, by decide, by decide, by decide⟩
  intro k hlo hhi _
  interval_cases k <;> decide

/-- **Certificate 9 (`g ≥ 14, L = 16`, bipartite cubic, `n ≤ 346`)**. -/
theorem cert_girth14_bip_c16_n346 :
    ValidCubicCert 14 16 346 true [133, 250, 133, 125, 67, 62, -6, 18, 28] [] := by
  refine ⟨by intro j hj l hl; simp at hj hl; omega,
          by intro j hj; simp at hj,
          ?_, by decide, by decide, by decide⟩
  intro k hlo hhi hev
  have hk : k % 2 = 0 := hev rfl
  interval_cases k <;> try omega
  decide

/-- **Certificate 10 (`g ≥ 15, L = 16`, general cubic, `n ≤ 573`)**. -/
theorem cert_girth15_c16_n573 :
    ValidCubicCert 15 16 573 false [8, 4, 8, 2, 4, 1, 2, 0, 1] [] := by
  refine ⟨by intro j hj l hl; simp at hj hl; omega,
          by intro j hj; simp at hj,
          ?_, by decide, by decide, by decide⟩
  intro k hlo hhi _
  interval_cases k
  decide

end CertifiedGirthBounds

end E64Wave8Agent9Delsarte
