import Shadow
import NonBacktrackingGirth
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Wave 5 Agent #6: Unconditional Eigenvalue-Free Chebyshev-Squaring Girth-Doubling Closure

Eliminates the Ramanujan / spectral-gap hypothesis from Wave 4 Agent #1's girth-doubling
theorem completely via an elementary eigenvalue-free matrix-squaring identity over `ℚ`
and a one-step tail-stripping combinatorial bijection:

1. `chebMat_double`: `T_{2L}(A) = T_L(A)^2 - 2 (d - 1)^L I` over `ℚ`.
2. `chebMat_sq_trace_ge` and `chebMat_sq_trace_sharp`: For any `d`-regular graph `G`,
   `Tr(T_L(A)^2) ≥ ((d - 1)^L + 1)^2` and the sharpened Cauchy-Schwarz bound
   `n * Tr(T_L(A)^2) ≥ n * ((d - 1)^L + 1)^2 + (Tr(T_L(A)) - ((d - 1)^L + 1))^2`.
3. `taillessCount_eq_chebMat_trace`: Exact combinatorial identity
   `taillessCount G (2 * L) = Tr(T_{2L}(A)) + (d - 2) * n` via one-step tail stripping.
4. `unconditional_chebyshev_girth_doubling_hasPower` and `..._sharp`:
   Every finite `d`-regular simple graph (`d ≥ 3`) of girth `g > 2^k` and order
   up to the quadratic Moore bound unconditionally satisfies `Erdos64Closure.HasPower G`.
5. Concrete corollaries (`cubic_girth9_le_131_hasPower`, `cubic_girth17_le_32771_hasPower`,
   `cubic_girth33_le_2147483651_hasPower`, `four_reg_girth5_le_46_hasPower`).
6. `erdos64_closed_of_tailless_gt_nonSimple`: Whole-problem closure gate for Erdős #64.
-/

namespace E64Wave5Agent6
open SimpleGraph Erdos64Closure E64NonBacktrackingGirth Matrix

section ChebyshevAlgebra

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Rational adjacency matrix of a finite simple graph. -/
def adjMat (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℚ :=
  Matrix.of fun u v => if G.Adj u v then 1 else 0

omit [Fintype V] [DecidableEq V] in
theorem adjMat_symm (G : SimpleGraph V) [DecidableRel G.Adj] :
    (adjMat G)ᵀ = adjMat G := by
  ext u v
  simp only [transpose_apply, adjMat, of_apply]
  by_cases h : G.Adj v u
  · simp [h, h.symm]
  · have h' : ¬ G.Adj u v := fun huv => h huv.symm
    simp [h, h']

omit [DecidableEq V] in
theorem adjMat_mulVec_one (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : ∀ v : V, G.degree v = d) :
    (adjMat G).mulVec (fun _ => 1) = (d : ℚ) • (fun _ => 1) := by
  ext u
  simp only [mulVec, dotProduct, adjMat, of_apply, Pi.smul_apply, smul_eq_mul, mul_one]
  have hsum : (∑ v : V, (if G.Adj u v then (1 : ℚ) else 0)) =
      ((Finset.univ.filter (fun v => G.Adj u v)).card : ℚ) := by
    rw [Finset.sum_boole]
  rw [hsum]
  have hcard : (Finset.univ.filter (fun v => G.Adj u v)).card = G.degree u := by
    rw [← G.card_neighborFinset_eq_degree]
    congr 1
    ext v
    simp [SimpleGraph.mem_neighborFinset]
  rw [hcard, hreg u]

/-- Scaled Chebyshev-Hashimoto polynomial matrices `T_k(A)` over `ℚ`. -/
def chebMat (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : ℕ → Matrix V V ℚ
  | 0 => (2 : ℚ) • (1 : Matrix V V ℚ)
  | 1 => adjMat G
  | k + 2 => adjMat G * chebMat G d (k + 1) - ((d - 1 : ℕ) : ℚ) • chebMat G d k

theorem chebMat_comm_adj (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) :
    ∀ k : ℕ, adjMat G * chebMat G d k = chebMat G d k * adjMat G
  | 0 => by simp [chebMat]
  | 1 => rfl
  | k + 2 => by
      simp only [chebMat, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
      rw [chebMat_comm_adj G d k]
      congr 1
      rw [chebMat_comm_adj G d (k + 1), ← Matrix.mul_assoc, chebMat_comm_adj G d (k + 1)]

theorem chebMat_symm (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) :
    ∀ k : ℕ, (chebMat G d k)ᵀ = chebMat G d k
  | 0 => by simp [chebMat]
  | 1 => adjMat_symm G
  | k + 2 => by
      simp only [chebMat, transpose_sub, transpose_mul, transpose_smul]
      rw [chebMat_symm G d (k + 1), chebMat_symm G d k, adjMat_symm G,
          ← chebMat_comm_adj G d (k + 1)]

theorem chebMat_mulVec_one (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hd : 1 ≤ d) (hreg : ∀ v : V, G.degree v = d) :
    ∀ k : ℕ, (chebMat G d k).mulVec (fun _ => 1) =
      (((d - 1 : ℕ) : ℚ) ^ k + 1) • (fun _ => 1)
  | 0 => by
      ext u
      simp only [chebMat, smul_mulVec, one_mulVec, pow_zero, Pi.smul_apply, smul_eq_mul, mul_one]
      norm_num
  | 1 => by
      have hdq : ((d - 1 : ℕ) : ℚ) + 1 = (d : ℚ) := by
        exact_mod_cast Nat.sub_add_cancel hd
      simpa [chebMat, hdq] using adjMat_mulVec_one G hreg
  | k + 2 => by
      have ih1 := chebMat_mulVec_one G hd hreg (k + 1)
      have ih0 := chebMat_mulVec_one G hd hreg k
      have hA := adjMat_mulVec_one G hreg
      have hdq : ((d - 1 : ℕ) : ℚ) + 1 = (d : ℚ) := by
        exact_mod_cast Nat.sub_add_cancel hd
      ext u
      simp only [chebMat, sub_mulVec, ← mulVec_mulVec, smul_mulVec, ih1, ih0,
        mulVec_smul, hA, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one]
      rw [← hdq]
      ring

theorem chebMat_add_sub (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) :
    ∀ (k L : ℕ), k ≤ L →
      chebMat G d (L + k) + (((d - 1 : ℕ) : ℚ) ^ k) • chebMat G d (L - k) =
        chebMat G d k * chebMat G d L
  | 0, L, _ => by
      simp only [Nat.add_zero, Nat.sub_zero, pow_zero, one_smul, chebMat, smul_mul, one_mul]
      rw [two_smul]
  | 1, L, hL => by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hL
      have hsub : m + 1 - 1 = m := by omega
      rw [hsub]
      change chebMat G d (m + 2) + (((d - 1 : ℕ) : ℚ) ^ 1) • chebMat G d m =
        adjMat G * chebMat G d (m + 1)
      simp only [chebMat, pow_one, sub_add_cancel]
  | k + 2, L, hL => by
      have hk1 : k + 1 ≤ L := by omega
      have hk0 : k ≤ L := by omega
      have ih1 := chebMat_add_sub G d (k + 1) L hk1
      have ih0 := chebMat_add_sub G d k L hk0
      have hLm : L - k = (L - (k + 2)) + 2 := by omega
      have hLm1 : L - (k + 1) = (L - (k + 2)) + 1 := by omega
      have hrec_hi : adjMat G * chebMat G d (L + (k + 1)) =
          chebMat G d (L + (k + 2)) + ((d - 1 : ℕ) : ℚ) • chebMat G d (L + k) := by
        have h1 : L + (k + 2) = (L + k) + 2 := by omega
        have h2 : L + (k + 1) = (L + k) + 1 := by omega
        rw [h1, h2]
        simp only [chebMat, sub_add_cancel]
      have hrec_lo : adjMat G * chebMat G d (L - (k + 1)) =
          chebMat G d (L - k) + ((d - 1 : ℕ) : ℚ) • chebMat G d (L - (k + 2)) := by
        rw [hLm, hLm1]
        simp only [chebMat, sub_add_cancel]
      have hlin :
          chebMat G d (L + (k + 2)) + (((d - 1 : ℕ) : ℚ) ^ (k + 2)) • chebMat G d (L - (k + 2)) =
            (chebMat G d (L + (k + 2)) + ((d - 1 : ℕ) : ℚ) • chebMat G d (L + k)) +
              (((d - 1 : ℕ) : ℚ) ^ (k + 1)) •
                (chebMat G d (L - k) + ((d - 1 : ℕ) : ℚ) • chebMat G d (L - (k + 2))) -
              ((d - 1 : ℕ) : ℚ) •
                (chebMat G d (L + k) + (((d - 1 : ℕ) : ℚ) ^ k) • chebMat G d (L - k)) := by
        ext u v
        simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
        ring
      calc
        chebMat G d (L + (k + 2)) + (((d - 1 : ℕ) : ℚ) ^ (k + 2)) • chebMat G d (L - (k + 2))
            = (chebMat G d (L + (k + 2)) + ((d - 1 : ℕ) : ℚ) • chebMat G d (L + k)) +
                (((d - 1 : ℕ) : ℚ) ^ (k + 1)) •
                  (chebMat G d (L - k) + ((d - 1 : ℕ) : ℚ) • chebMat G d (L - (k + 2))) -
                ((d - 1 : ℕ) : ℚ) •
                  (chebMat G d (L + k) + (((d - 1 : ℕ) : ℚ) ^ k) • chebMat G d (L - k)) := hlin
        _ = adjMat G * chebMat G d (L + (k + 1)) +
              (((d - 1 : ℕ) : ℚ) ^ (k + 1)) • (adjMat G * chebMat G d (L - (k + 1))) -
              ((d - 1 : ℕ) : ℚ) • (chebMat G d k * chebMat G d L) := by
              rw [hrec_hi, hrec_lo, ih0]
        _ = adjMat G * (chebMat G d (L + (k + 1)) +
              (((d - 1 : ℕ) : ℚ) ^ (k + 1)) • chebMat G d (L - (k + 1))) -
              ((d - 1 : ℕ) : ℚ) • (chebMat G d k * chebMat G d L) := by
              rw [mul_add, mul_smul_comm]
        _ = adjMat G * (chebMat G d (k + 1) * chebMat G d L) -
              ((d - 1 : ℕ) : ℚ) • (chebMat G d k * chebMat G d L) := by
              rw [ih1]
        _ = chebMat G d (k + 2) * chebMat G d L := by
              simp only [chebMat, sub_mul, smul_mul, Matrix.mul_assoc]

/-- Exact doubling identity: `T_{2L}(A) = T_L(A)^2 - 2 (d - 1)^L I`. -/
theorem chebMat_double (G : SimpleGraph V) [DecidableRel G.Adj] (d L : ℕ) :
    chebMat G d (2 * L) =
      chebMat G d L * chebMat G d L - (2 * ((d - 1 : ℕ) : ℚ) ^ L) • (1 : Matrix V V ℚ) := by
  have h := chebMat_add_sub G d L L le_rfl
  rw [Nat.sub_self, show L + L = 2 * L by omega] at h
  simp only [chebMat, smul_smul] at h
  have hmul : (((d - 1 : ℕ) : ℚ) ^ L * 2) = 2 * ((d - 1 : ℕ) : ℚ) ^ L := mul_comm _ _
  rw [hmul] at h
  exact eq_sub_of_add_eq h

/-- All-ones rational matrix on `V`. -/
def onesMat (V : Type*) : Matrix V V ℚ :=
  Matrix.of fun _ _ => 1

omit [DecidableEq V] in
/-- Elementary eigenvalue-free matrix-squaring trace decomposition for any symmetric matrix
with constant row sum `μ`. -/
theorem symm_const_rowSum_sq_trace (M : Matrix V V ℚ) (μ : ℚ)
    (hsym : Mᵀ = M) (hrow : M.mulVec (fun _ => 1) = μ • (fun _ => 1))
    (hn : 0 < Fintype.card V) :
    Matrix.trace (M * M) =
      (∑ u : V, ∑ v : V,
        ((M - (μ / (Fintype.card V : ℚ)) • onesMat V) u v) ^ 2) + μ ^ 2 ∧
    Matrix.trace (M - (μ / (Fintype.card V : ℚ)) • onesMat V) =
      Matrix.trace M - μ := by
  set n : ℚ := (Fintype.card V : ℚ)
  set J : Matrix V V ℚ := onesMat V
  set R : Matrix V V ℚ := M - (μ / n) • J
  have hn0 : n ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hMJ : M * J = μ • J := by
    ext u v
    have hu := congrFun hrow u
    simpa [Matrix.mul_apply, mulVec, dotProduct, J, onesMat] using hu
  have hJM : J * M = μ • J := by
    have h1 := congrArg Matrix.transpose hMJ
    rw [transpose_mul, hsym, transpose_smul] at h1
    have hJt : Jᵀ = J := by ext u v; rfl
    simpa [hJt] using h1
  have hJJ : J * J = n • J := by
    ext u v
    simp [Matrix.mul_apply, J, onesMat, n]
  have hRJ : R * J = 0 := by
    dsimp only [R]
    rw [sub_mul, smul_mul, hMJ, hJJ, smul_smul, div_mul_cancel₀ _ hn0, sub_self]
  have hJR : J * R = 0 := by
    dsimp only [R]
    rw [mul_sub, mul_smul_comm, hJM, hJJ, smul_smul, div_mul_cancel₀ _ hn0, sub_self]
  have hRt : Rᵀ = R := by
    dsimp only [R]
    rw [transpose_sub, hsym, transpose_smul]
    have hJt : Jᵀ = J := by ext u v; rfl
    rw [hJt]
  have hMeq : M = R + (μ / n) • J := by
    dsimp only [R]; rw [sub_add_cancel]
  have hMM : M * M = R * R + (μ ^ 2 / n) • J := by
    calc
      M * M = (R + (μ / n) • J) * (R + (μ / n) • J) := by rw [← hMeq]
      _ = R * R + (μ / n) • (R * J) + (μ / n) • (J * R) +
            ((μ / n) * (μ / n)) • (J * J) := by
          rw [add_mul, mul_add, mul_add, mul_smul_comm, smul_mul, smul_mul, mul_smul_comm,
              smul_smul]
          abel
      _ = R * R + (μ ^ 2 / n) • J := by
          rw [hRJ, hJR, smul_zero, add_zero, add_zero, hJJ, smul_smul]
          congr 1
          field_simp [hn0]
  have htrJ : Matrix.trace J = n := by
    simp [Matrix.trace, J, onesMat, n]
  have htrRR : Matrix.trace (R * R) = ∑ u : V, ∑ v : V, (R u v) ^ 2 := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    have hvu : R v u = R u v := by
      have := congrFun (congrFun hRt u) v
      simpa [transpose_apply] using this
    rw [hvu, sq]
  constructor
  · rw [hMM, trace_add, trace_smul, htrJ, smul_eq_mul, htrRR, div_mul_cancel₀ _ hn0]
  · dsimp only [R]
    rw [trace_sub, trace_smul, htrJ, smul_eq_mul, div_mul_cancel₀ _ hn0]

/-- Unconditional eigenvalue-free trace lower bound for `T_L(A)^2`. -/
theorem chebMat_sq_trace_ge (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hd : 1 ≤ d) (hreg : ∀ v : V, G.degree v = d) (hn : 0 < Fintype.card V) (L : ℕ) :
    (((d - 1 : ℕ) : ℚ) ^ L + 1) ^ 2 ≤ Matrix.trace (chebMat G d L * chebMat G d L) := by
  have hdecomp := symm_const_rowSum_sq_trace (chebMat G d L) (((d - 1 : ℕ) : ℚ) ^ L + 1)
    (chebMat_symm G d L) (chebMat_mulVec_one G hd hreg L) hn
  rw [hdecomp.1]
  exact le_add_of_nonneg_left
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- Sharpened Cauchy-Schwarz trace lower bound for `T_L(A)^2`. -/
theorem chebMat_sq_trace_sharp (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hd : 1 ≤ d) (hreg : ∀ v : V, G.degree v = d) (hn : 0 < Fintype.card V) (L : ℕ) :
    (Fintype.card V : ℚ) * (((d - 1 : ℕ) : ℚ) ^ L + 1) ^ 2 +
      (Matrix.trace (chebMat G d L) - (((d - 1 : ℕ) : ℚ) ^ L + 1)) ^ 2 ≤
    (Fintype.card V : ℚ) * Matrix.trace (chebMat G d L * chebMat G d L) := by
  set n : ℚ := (Fintype.card V : ℚ)
  set μ : ℚ := ((d - 1 : ℕ) : ℚ) ^ L + 1
  set R : Matrix V V ℚ := chebMat G d L - (μ / n) • onesMat V
  have hn_pos : (0 : ℚ) < n := Nat.cast_pos.mpr hn
  have hdecomp := symm_const_rowSum_sq_trace (chebMat G d L) μ
    (chebMat_symm G d L) (chebMat_mulVec_one G hd hreg L) hn
  have h1 : Matrix.trace (chebMat G d L * chebMat G d L) =
      (∑ u : V, ∑ v : V, (R u v) ^ 2) + μ ^ 2 := hdecomp.1
  have h2 : Matrix.trace R = Matrix.trace (chebMat G d L) - μ := hdecomp.2
  have hdiag : (∑ u : V, (R u u) ^ 2) ≤ ∑ u : V, ∑ v : V, (R u v) ^ 2 := by
    refine Finset.sum_le_sum fun u _ => ?_
    exact Finset.single_le_sum (fun v _ => sq_nonneg (R u v)) (Finset.mem_univ u)
  have hcs : (∑ u : V, R u u) ^ 2 ≤ ((Finset.univ : Finset V).card : ℚ) * ∑ u : V, (R u u) ^ 2 :=
    sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset V)) (f := fun u => R u u)
  have htrR : (∑ u : V, R u u) = Matrix.trace (chebMat G d L) - μ := by
    simpa [Matrix.trace, Matrix.diag_apply] using h2
  rw [htrR, Finset.card_univ] at hcs
  have hmul : n * (∑ u : V, (R u u) ^ 2) ≤ n * (∑ u : V, ∑ v : V, (R u v) ^ 2) :=
    mul_le_mul_of_nonneg_left hdiag hn_pos.le
  rw [h1, mul_add]
  linarith

end ChebyshevAlgebra

section CombinatorialBridge

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Decidability of `IsNonBacktracking` for walks on graphs with decidable vertex equality. -/
def isNonBacktrackingBool {G : SimpleGraph V} : ∀ {u v : V}, G.Walk u v → Bool
  | _, _, .nil => true
  | _, _, .cons _ .nil => true
  | _, _, .cons (u := a) _ (.cons (v := c) h₂ rest) =>
      decide (a ≠ c) && isNonBacktrackingBool (.cons h₂ rest)

omit [Fintype V] in
theorem isNonBacktrackingBool_eq_true_iff {G : SimpleGraph V} :
    ∀ {u v : V} (p : G.Walk u v), isNonBacktrackingBool p = true ↔ IsNonBacktracking p
  | _, _, .nil => by simp [isNonBacktrackingBool, IsNonBacktracking]
  | _, _, .cons _ .nil => by simp [isNonBacktrackingBool, IsNonBacktracking]
  | _, _, .cons _ (.cons h₂ rest) => by
      simp only [isNonBacktrackingBool, IsNonBacktracking, Bool.and_eq_true, decide_eq_true_eq]
      exact and_congr_right fun _ => isNonBacktrackingBool_eq_true_iff (.cons h₂ rest)

instance instDecidableIsNonBacktracking {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    Decidable (IsNonBacktracking p) :=
  decidable_of_iff (isNonBacktrackingBool p = true) (isNonBacktrackingBool_eq_true_iff p)

instance instDecidableIsCyclicallyNonBacktracking {G : SimpleGraph V} {v : V} (p : G.Walk v v) :
    Decidable (IsCyclicallyNonBacktracking p) :=
  instDecidableIsNonBacktracking (p.append p)

/-- Finset of all non-backtracking walks of length `k` from `u` to `v`. -/
def nbWalks (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (u v : V) :
    Finset (G.Walk u v) :=
  (G.finsetWalkLength k u v).filter IsNonBacktracking

/-- Rational matrix of non-backtracking walk counts of length `k`. -/
def nbMat (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : Matrix V V ℚ :=
  Matrix.of fun u v => ((nbWalks G k u v).card : ℚ)

/-- Total number of non-backtracking closed walks of length `k`. -/
def nbClosedCount (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : ℕ :=
  ∑ v : V, (nbWalks G k v v).card

/-- Total number of cyclically non-backtracking (tailless) closed walks of length `k`
(the exact combinatorial quantity equal to the Hashimoto trace `Tr(B^k)`). -/
def taillessCount (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : ℕ :=
  ∑ v : V, ((nbWalks G k v v).filter IsCyclicallyNonBacktracking).card

/-- Total number of non-simple cyclically non-backtracking closed walks of length `k`. -/
noncomputable def nonSimpleTaillessCount (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : ℕ := by
  classical
  exact ∑ v : V,
    ((nbWalks G k v v).filter fun p => IsCyclicallyNonBacktracking p ∧ ¬ p.IsCycle).card

theorem nbMat_trace_eq_nbClosedCount (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    Matrix.trace (nbMat G k) = (nbClosedCount G k : ℚ) := by
  simp [Matrix.trace, Matrix.diag_apply, nbMat, nbClosedCount]

theorem nbMat_zero (G : SimpleGraph V) [DecidableRel G.Adj] :
    nbMat G 0 = (1 : Matrix V V ℚ) := by
  ext u v
  simp only [nbMat, of_apply, Matrix.one_apply]
  by_cases huv : u = v
  · subst huv
    have hcard : (nbWalks G 0 u u).card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨.nil, ?_⟩
      ext p
      cases p with
      | nil => simp [nbWalks, mem_finsetWalkLength_iff, IsNonBacktracking]
      | cons _ _ => simp [nbWalks, mem_finsetWalkLength_iff]
    simp [hcard]
  · have hcard : (nbWalks G 0 u v).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro p hp
      simp only [nbWalks, Finset.mem_filter, mem_finsetWalkLength_iff] at hp
      cases p with
      | nil => exact huv rfl
      | cons _ _ => simp at hp
    simp [huv, hcard]

theorem nbMat_one (G : SimpleGraph V) [DecidableRel G.Adj] :
    nbMat G 1 = adjMat G := by
  ext u v
  simp only [nbMat, adjMat, of_apply]
  by_cases huv : G.Adj u v
  · have hcard : (nbWalks G 1 u v).card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨.cons huv .nil, ?_⟩
      ext p
      cases p with
      | nil => simp [nbWalks, mem_finsetWalkLength_iff]
      | cons h rest =>
          cases rest with
          | nil => simp [nbWalks, mem_finsetWalkLength_iff, IsNonBacktracking]
          | cons _ _ =>
              simp only [nbWalks, Finset.mem_filter, mem_finsetWalkLength_iff, Walk.length_cons,
                Finset.mem_singleton, Walk.cons.injEq]
              constructor
              · intro h1; omega
              · rintro ⟨rfl, h2⟩; cases h2
    simp [huv, hcard]
  · have hcard : (nbWalks G 1 u v).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro p hp
      simp only [nbWalks, Finset.mem_filter, mem_finsetWalkLength_iff] at hp
      cases p with
      | nil => simp at hp
      | cons h rest =>
          cases rest with
          | nil => exact huv h
          | cons _ _ => simp at hp
    simp [huv, hcard]

theorem nbWalks_two_card (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) :
    (nbWalks G 2 u v).card =
      if u = v then 0 else (Finset.univ.filter fun w => G.Adj u w ∧ G.Adj w v).card := by
  by_cases huv : u = v
  · subst huv
    simp only [↓reduceIte, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro p hmem
    simp only [nbWalks, Finset.mem_filter, mem_finsetWalkLength_iff] at hmem
    cases p with
    | nil => simp at hmem
    | cons _ rest =>
        cases rest with
        | nil => simp at hmem
        | cons _ rest₂ =>
            cases rest₂ with
            | nil => exact hmem.2.1 rfl
            | cons _ _ => simp at hmem
  · simp only [huv, ↓reduceIte]
    refine Finset.card_bij
      (fun p _ => p.snd)
      (fun p hp => ?_)
      (fun p₁ hp₁ p₂ hp₂ heq => ?_)
      (fun w hw => ?_)
    · simp only [nbWalks, Finset.mem_filter, mem_finsetWalkLength_iff] at hp
      cases p with
      | nil => simp at hp
      | cons h₁ rest =>
          cases rest with
          | nil => simp at hp
          | cons h₂ rest₂ =>
              cases rest₂ with
              | nil => simp [h₁, h₂]
              | cons _ _ => simp at hp
    · simp only [nbWalks, Finset.mem_filter, mem_finsetWalkLength_iff] at hp₁ hp₂
      cases p₁ with
      | nil => simp at hp₁
      | cons h₁ rest₁ =>
          cases rest₁ with
          | nil => simp at hp₁
          | cons h₂ rest₁' =>
              cases rest₁' with
              | cons _ _ => simp at hp₁
              | nil =>
                  cases p₂ with
                  | nil => simp at hp₂
                  | cons h₃ rest₂ =>
                      cases rest₂ with
                      | nil => simp at hp₂
                      | cons h₄ rest₂' =>
                          cases rest₂' with
                          | cons _ _ => simp at hp₂
                          | nil =>
                              simp only [Walk.snd_cons] at heq
                              subst heq
                              rfl
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      refine ⟨.cons hw.1 (.cons hw.2 .nil), ?_, rfl⟩
      simp [nbWalks, mem_finsetWalkLength_iff, IsNonBacktracking, huv]

theorem nbMat_two (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : ∀ v : V, G.degree v = d) :
    nbMat G 2 = adjMat G * adjMat G - (d : ℚ) • (1 : Matrix V V ℚ) := by
  ext u v
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  simp only [nbMat, adjMat, of_apply, nbWalks_two_card]
  have hmul : (∑ w : V, (if G.Adj u w then (1 : ℚ) else 0) * (if G.Adj w v then 1 else 0)) =
      ((Finset.univ.filter fun w => G.Adj u w ∧ G.Adj w v).card : ℚ) := by
    have h1 : (∑ w : V, (if G.Adj u w then (1 : ℚ) else 0) * (if G.Adj w v then 1 else 0)) =
        ∑ w : V, if G.Adj u w ∧ G.Adj w v then (1 : ℚ) else 0 := by
      refine Finset.sum_congr rfl fun w _ => ?_
      by_cases ha : G.Adj u w <;> by_cases hb : G.Adj w v <;> simp [ha, hb]
    rw [h1, Finset.sum_boole]
  rw [hmul]
  by_cases huv : u = v
  · subst huv
    have hcard : (Finset.univ.filter fun w => G.Adj u w ∧ G.Adj w u).card = d := by
      rw [← hreg u, ← G.card_neighborFinset_eq_degree]
      congr 1
      ext w
      simp [SimpleGraph.mem_neighborFinset, G.adj_comm]
    simp [hcard]
  · simp [huv]

/-- Combinatorial recurrence for non-backtracking walk counts of length `k + 2` (`k ≥ 1`). -/
theorem nbWalks_rec_card (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : ∀ v : V, G.degree v = d) (k : ℕ) (hk : 1 ≤ k) (u v : V) :
    (∑ w ∈ G.neighborFinset u, (nbWalks G (k + 1) w v).card) =
      (nbWalks G (k + 2) u v).card + (d - 1) * (nbWalks G k u v).card := by
  let S := (G.neighborFinset u).sigma fun w => nbWalks G (k + 1) w v
  have hS : S.card = ∑ w ∈ G.neighborFinset u, (nbWalks G (k + 1) w v).card :=
    Finset.card_sigma _ _
  rw [← hS]
  let good := S.filter fun x => x.2.snd ≠ u
  let bad := S.filter fun x => x.2.snd = u
  have hpart : S.card = good.card + bad.card := by
    have := Finset.card_filter_add_card_filter_not (s := S) (p := fun x => x.2.snd ≠ u)
    simpa [good, bad] using this.symm
  rw [hpart]
  congr 1
  · refine Finset.card_bij
      (fun x hx => Walk.cons ((G.mem_neighborFinset u x.1).mp (Finset.mem_sigma.mp (Finset.mem_filter.mp hx).1).1) x.2)
      (fun x hx => ?_)
      (fun x₁ hx₁ x₂ hx₂ heq => ?_)
      (fun p hp => ?_)
    · rcases x with ⟨w, q⟩
      simp only [good, S, Finset.mem_filter, Finset.mem_sigma, nbWalks, mem_finsetWalkLength_iff] at hx ⊢
      refine ⟨by simp [hx.1.2.1], ?_⟩
      cases q with
      | nil => simp at hx
      | cons h₂ rest =>
          simp only [IsNonBacktracking, Walk.snd_cons] at hx ⊢
          exact ⟨Ne.symm hx.2, hx.1.2.2⟩
    · rcases x₁ with ⟨w₁, q₁⟩
      rcases x₂ with ⟨w₂, q₂⟩
      cases heq
      rfl
    · simp only [nbWalks, Finset.mem_filter, mem_finsetWalkLength_iff] at hp
      cases p with
      | nil => simp at hp
      | cons h₁ rest =>
          cases rest with
          | nil => simp at hp
          | cons h₂ rest₂ =>
              refine ⟨⟨_, Walk.cons h₂ rest₂⟩, ?_, rfl⟩
              simp only [good, S, Finset.mem_filter, Finset.mem_sigma, G.mem_neighborFinset,
                nbWalks, mem_finsetWalkLength_iff, Walk.snd_cons]
              exact ⟨⟨h₁, ⟨by simpa using hp.1, hp.2.2⟩⟩, Ne.symm hp.2.1⟩
  · let T := (nbWalks G k u v).sigma fun p => (G.neighborFinset u).erase p.snd
    have hT : T.card = (d - 1) * (nbWalks G k u v).card := by
      rw [Finset.card_sigma]
      have hconst : ∀ p ∈ nbWalks G k u v, ((G.neighborFinset u).erase p.snd).card = d - 1 := by
        intro p hp
        simp only [nbWalks, Finset.mem_filter, mem_finsetWalkLength_iff] at hp
        cases p with
        | nil => simp at hp; omega
        | cons h₁ rest =>
            simp only [Walk.snd_cons]
            rw [Finset.card_erase_of_mem ((G.mem_neighborFinset u _).mpr h₁),
                G.card_neighborFinset_eq_degree, hreg u]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, mul_comm]
    rw [← hT]
    symm
    refine Finset.card_bij
      (fun y hy => ⟨y.2, Walk.cons ((G.mem_neighborFinset u y.2).mp (Finset.mem_erase.mp (Finset.mem_sigma.mp hy).2).2).symm y.1⟩)
      (fun y hy => ?_)
      (fun y₁ hy₁ y₂ hy₂ heq => ?_)
      (fun x hx => ?_)
    · rcases y with ⟨p, w⟩
      simp only [T, Finset.mem_sigma, nbWalks, Finset.mem_filter, mem_finsetWalkLength_iff,
        Finset.mem_erase, G.mem_neighborFinset] at hy
      simp only [bad, S, Finset.mem_filter, Finset.mem_sigma, G.mem_neighborFinset,
        nbWalks, mem_finsetWalkLength_iff, Walk.snd_cons]
      refine ⟨⟨hy.2.2, ⟨by simp [hy.1.1], ?_⟩⟩, trivial⟩
      cases p with
      | nil => simp at hy; omega
      | cons h₃ rest₃ =>
          simp only [IsNonBacktracking, Walk.snd_cons] at hy ⊢
          exact ⟨hy.2.1, hy.1.2⟩
    · rcases y₁ with ⟨p₁, w₁⟩
      rcases y₂ with ⟨p₂, w₂⟩
      simp only [Sigma.mk.inj_iff] at heq
      rcases heq with ⟨rfl, hwalk⟩
      have hwalk' := eq_of_heq hwalk
      cases hwalk'
      rfl
    · rcases x with ⟨w, q⟩
      simp only [bad, S, Finset.mem_filter, Finset.mem_sigma, G.mem_neighborFinset,
        nbWalks, mem_finsetWalkLength_iff] at hx
      cases q with
      | nil => simp at hx
      | cons h₂ rest =>
          simp only [Walk.snd_cons] at hx
          rcases hx with ⟨⟨huw, ⟨hqlen, hqnb⟩⟩, hzu⟩
          subst hzu
          cases rest with
          | nil => simp at hqlen; omega
          | cons h₃ rest₃ =>
              refine ⟨⟨Walk.cons h₃ rest₃, w⟩, ?_, rfl⟩
              simp only [T, Finset.mem_sigma, nbWalks, Finset.mem_filter, mem_finsetWalkLength_iff,
                Finset.mem_erase, G.mem_neighborFinset, Walk.snd_cons]
              exact ⟨⟨by simpa using hqlen, hqnb.2⟩, ⟨hqnb.1, huw⟩⟩

/-- Matrix recurrence `P_{k+2} = A * P_{k+1} - (d - 1) P_k` for `k ≥ 1`. -/
theorem nbMat_rec (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : ∀ v : V, G.degree v = d) (k : ℕ) (hk : 1 ≤ k) :
    nbMat G (k + 2) = adjMat G * nbMat G (k + 1) - ((d - 1 : ℕ) : ℚ) • nbMat G k := by
  ext u v
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [nbMat, adjMat, of_apply]
  have hsum : (∑ w : V, (if G.Adj u w then (1 : ℚ) else 0) * ((nbWalks G (k + 1) w v).card : ℚ)) =
      ((∑ w ∈ G.neighborFinset u, (nbWalks G (k + 1) w v).card : ℕ) : ℚ) := by
    rw [Nat.cast_sum]
    have h1 : (∑ w : V, (if G.Adj u w then (1 : ℚ) else 0) * ((nbWalks G (k + 1) w v).card : ℚ)) =
        ∑ w : V, if G.Adj u w then ((nbWalks G (k + 1) w v).card : ℚ) else 0 := by
      refine Finset.sum_congr rfl fun w _ => ?_
      by_cases h : G.Adj u w <;> simp [h]
    rw [h1, ← Finset.sum_filter]
    congr 1
    ext w
    simp [SimpleGraph.mem_neighborFinset]
  rw [hsum, nbWalks_rec_card G hreg k hk u v]
  push_cast
  ring

/-- Exact algebraic relation `T_k(A) = P_k - (d - 2) ∑_{j=1}^{k/2} P_{k - 2j}` for `k ≥ 1`. -/
theorem chebMat_eq_nbMat_sub (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hd : 2 ≤ d) (hreg : ∀ v : V, G.degree v = d) :
    ∀ k : ℕ, 1 ≤ k →
      chebMat G d k = nbMat G k -
        ((d - 2 : ℕ) : ℚ) • ∑ j ∈ Finset.Icc 1 (k / 2), nbMat G (k - 2 * j) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
      intro hk
      match k with
      | 0 => omega
      | 1 =>
          simp [chebMat, nbMat_one]
      | 2 =>
          have h1 : (2 : ℕ) / 2 = 1 := rfl
          rw [h1, Finset.Icc_self, Finset.sum_singleton]
          simp only [Nat.sub_self, nbMat_zero, nbMat_two G hreg, chebMat]
          have hdq : ((d - 2 : ℕ) : ℚ) + (d : ℚ) = 2 * ((d - 1 : ℕ) : ℚ) := by
            have : (d - 2) + d = 2 * (d - 1) := by omega
            exact_mod_cast this
          ext u v
          rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.sub_apply, Matrix.smul_apply,
              Matrix.smul_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply]
          simp only [smul_eq_mul]
          by_cases huv : u = v
          · subst huv; simp; linarith
          · simp [huv]
      | m + 3 =>
          have ih2 := ih (m + 2) (by omega) (by omega)
          have ih1 := ih (m + 1) (by omega) (by omega)
          rw [chebMat, ih2, ih1, nbMat_rec G hreg (m + 1) (by omega)]
          have hgoal :
              adjMat G * (∑ j ∈ Finset.Icc 1 ((m + 2) / 2), nbMat G (m + 2 - 2 * j)) -
                ((d - 1 : ℕ) : ℚ) • (∑ j ∈ Finset.Icc 1 ((m + 1) / 2), nbMat G (m + 1 - 2 * j)) =
              ∑ j ∈ Finset.Icc 1 ((m + 3) / 2), nbMat G (m + 3 - 2 * j) := by
            rw [Finset.mul_sum, Finset.smul_sum]
            have hcases : (m + 2) / 2 = (m + 1) / 2 ∨ (m + 2) / 2 = (m + 1) / 2 + 1 := by omega
            rcases hcases with heq | hstep
            · have hm3 : (m + 3) / 2 = (m + 1) / 2 + 1 := by omega
              have hlast : m + 3 - 2 * ((m + 1) / 2 + 1) = 0 := by omega
              have hmid : m + 2 - 2 * ((m + 1) / 2) = 1 := by omega
              rw [heq, hm3, Finset.sum_Icc_succ_top (by omega : 1 ≤ (m + 1) / 2 + 1), hlast,
                  ← Finset.sum_sub_distrib]
              have hsplit_top :
                  (adjMat G * nbMat G (m + 2 - 2 * ((m + 1) / 2)) -
                    ((d - 1 : ℕ) : ℚ) • nbMat G (m + 1 - 2 * ((m + 1) / 2))) =
                  nbMat G (m + 3 - 2 * ((m + 1) / 2)) + nbMat G 0 := by
                have h0 : m + 1 - 2 * ((m + 1) / 2) = 0 := by omega
                have h2 : m + 3 - 2 * ((m + 1) / 2) = 2 := by omega
                rw [hmid, h0, h2, nbMat_one, nbMat_zero, nbMat_two G hreg]
                have hdq : ((d - 1 : ℕ) : ℚ) + 1 = (d : ℚ) := by
                  exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ d)
                ext u v
                rw [Matrix.sub_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
                    Matrix.smul_apply, Matrix.one_apply]
                simp only [smul_eq_mul]
                by_cases huv : u = v
                · subst huv; simp; linarith
                · simp [huv]
              have hbody :
                  ∑ j ∈ Finset.Icc 1 ((m + 1) / 2 - 1),
                    (adjMat G * nbMat G (m + 2 - 2 * j) -
                      ((d - 1 : ℕ) : ℚ) • nbMat G (m + 1 - 2 * j)) =
                  ∑ j ∈ Finset.Icc 1 ((m + 1) / 2 - 1), nbMat G (m + 3 - 2 * j) := by
                refine Finset.sum_congr rfl fun j hj => ?_
                simp only [Finset.mem_Icc] at hj
                have hk1 : 1 ≤ m + 1 - 2 * j := by omega
                have h1 : m + 2 - 2 * j = (m + 1 - 2 * j) + 1 := by omega
                have h2 : m + 3 - 2 * j = (m + 1 - 2 * j) + 2 := by omega
                rw [h1, h2, nbMat_rec G hreg (m + 1 - 2 * j) hk1]
              have hIcc : Finset.Icc 1 ((m + 1) / 2) =
                  insert ((m + 1) / 2) (Finset.Icc 1 ((m + 1) / 2 - 1)) := by
                ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
              have hnotmem : (m + 1) / 2 ∉ Finset.Icc 1 ((m + 1) / 2 - 1) := by
                simp only [Finset.mem_Icc]; omega
              rw [hIcc, Finset.sum_insert hnotmem, Finset.sum_insert hnotmem, hbody, hsplit_top]
              abel
            · have hm3 : (m + 3) / 2 = (m + 1) / 2 + 1 := by omega
              have hlast2 : m + 2 - 2 * ((m + 1) / 2 + 1) = 0 := by omega
              have hlast3 : m + 3 - 2 * ((m + 1) / 2 + 1) = 1 := by omega
              rw [hstep, hm3,
                  Finset.sum_Icc_succ_top (by omega : 1 ≤ (m + 1) / 2 + 1),
                  Finset.sum_Icc_succ_top (by omega : 1 ≤ (m + 1) / 2 + 1),
                  hlast2, hlast3, nbMat_zero, nbMat_one, Matrix.mul_one,
                  add_sub_right_comm, ← Finset.sum_sub_distrib]
              congr 1
              refine Finset.sum_congr rfl fun j hj => ?_
              simp only [Finset.mem_Icc] at hj
              have hk1 : 1 ≤ m + 1 - 2 * j := by omega
              have h1 : m + 2 - 2 * j = (m + 1 - 2 * j) + 1 := by omega
              have h2 : m + 3 - 2 * j = (m + 1 - 2 * j) + 2 := by omega
              rw [h1, h2, nbMat_rec G hreg (m + 1 - 2 * j) hk1]
          rw [mul_sub, mul_smul_comm, smul_sub, sub_sub_sub_comm,
              smul_comm ((d - 1 : ℕ) : ℚ) ((d - 2 : ℕ) : ℚ), ← smul_sub, hgoal]

omit [Fintype V] [DecidableEq V] in
private theorem reverse_snd_cons_cons {G : SimpleGraph V} {x y z w : V}
    (h₁ : G.Adj x y) (h₂ : G.Adj y z) (rest : G.Walk z w) :
    (Walk.cons h₁ (Walk.cons h₂ rest)).reverse.snd = (Walk.cons h₂ rest).reverse.snd := by
  rw [Walk.reverse_cons]
  cases hrv : (Walk.cons h₂ rest).reverse with
  | nil =>
      have hlen := congrArg Walk.length hrv
      simp only [Walk.length_reverse, Walk.length_cons, Walk.length_nil] at hlen
      omega
  | cons _ _ => simp [Walk.cons_append]

omit [Fintype V] [DecidableEq V] in
private theorem isNonBacktracking_append_cons_iff {G : SimpleGraph V} :
    ∀ {x y z w : V} (q : G.Walk x y) (h₁ : G.Adj y z) (r : G.Walk z w),
      IsNonBacktracking q → IsNonBacktracking (Walk.cons h₁ r) → 1 ≤ q.length →
      (IsNonBacktracking (q.append (Walk.cons h₁ r)) ↔ z ≠ q.reverse.snd) := by
  intro x y z w q
  induction q with
  | nil => intro _ _ _ _ hqlen; simp at hqlen
  | cons hyz qrest ih =>
      intro h₁ r hq hr _
      cases qrest with
      | nil =>
          simp only [Walk.cons_append, Walk.nil_append, IsNonBacktracking, Walk.reverse_cons,
            Walk.reverse_nil, Walk.nil_append, Walk.snd_cons]
          exact ⟨fun h => Ne.symm h.1, fun h => ⟨Ne.symm h, hr⟩⟩
      | cons hzw qrest₂ =>
          simp only [Walk.cons_append, IsNonBacktracking] at hq ⊢
          have ih' := ih h₁ r hq.2 hr (by simp)
          rw [reverse_snd_cons_cons hyz hzw qrest₂]
          exact ⟨fun h => ih'.mp h.2, fun h => ⟨hq.1, ih'.mpr h⟩⟩

omit [Fintype V] [DecidableEq V] in
private theorem isCyclicallyNonBacktracking_iff_snd_ne_rev_snd {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hnb : IsNonBacktracking p) (hlen : 1 ≤ p.length) :
    IsCyclicallyNonBacktracking p ↔ p.snd ≠ p.reverse.snd := by
  cases p with
  | nil => simp at hlen
  | cons h₁ rest =>
      simpa [IsCyclicallyNonBacktracking, Walk.snd_cons] using
        isNonBacktracking_append_cons_iff (Walk.cons h₁ rest) h₁ rest hnb hnb hlen

omit [Fintype V] [DecidableEq V] in
private theorem isNonBacktracking_append_single {G : SimpleGraph V} :
    ∀ {a b c : V} (p : G.Walk a b) (h : G.Adj b c),
      IsNonBacktracking p → 1 ≤ p.length → c ≠ p.reverse.snd →
      IsNonBacktracking (p.append (Walk.cons h Walk.nil)) := by
  intro a b c p
  induction p with
  | nil => intro _ _ hplen _; simp at hplen
  | cons hp₁ prest ih =>
      intro h hp _ hne
      cases prest with
      | nil =>
          simp only [Walk.cons_append, Walk.nil_append, IsNonBacktracking, Walk.reverse_cons,
            Walk.reverse_nil, Walk.nil_append, Walk.snd_cons] at hne ⊢
          exact ⟨Ne.symm hne, trivial⟩
      | cons hp₂ prest₂ =>
          simp only [Walk.cons_append, IsNonBacktracking] at hp ⊢
          rw [reverse_snd_cons_cons hp₁ hp₂ prest₂] at hne
          exact ⟨hp.1, ih h hp.2 (by simp) hne⟩

omit [Fintype V] [DecidableEq V] in
private theorem isNonBacktracking_reverse {G : SimpleGraph V} :
    ∀ {u v : V} {p : G.Walk u v}, IsNonBacktracking p → IsNonBacktracking p.reverse
  | _, _, .nil, _ => trivial
  | _, _, .cons _ .nil, _ => trivial
  | _, _, .cons h₁ (.cons h₂ rest), hnb => by
      have hrest : IsNonBacktracking (Walk.cons h₂ rest).reverse :=
        isNonBacktracking_reverse hnb.2
      rw [Walk.reverse_cons]
      refine isNonBacktracking_append_single (Walk.cons h₂ rest).reverse h₁.symm hrest
        (by simp) ?_
      rw [Walk.reverse_reverse, Walk.snd_cons]
      exact hnb.1

/-- One-step tail-stripping recurrence:
`nbClosedCount G (k + 2) + taillessCount G k = taillessCount G (k + 2) + (d - 1) * nbClosedCount G k`
for all `k ≥ 1` in a `d`-regular graph (`d ≥ 2`). -/
theorem one_step_tail_strip (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hd : 2 ≤ d) (hreg : ∀ v : V, G.degree v = d) (k : ℕ) (hk : 1 ≤ k) :
    nbClosedCount G (k + 2) + taillessCount G k =
      taillessCount G (k + 2) + (d - 1) * nbClosedCount G k := by
  let All (m : ℕ) := (Finset.univ : Finset V).sigma fun v => nbWalks G m v v
  let Tailless (m : ℕ) := (All m).filter fun x => IsCyclicallyNonBacktracking x.2
  let Tailed (m : ℕ) := (All m).filter fun x => ¬ IsCyclicallyNonBacktracking x.2
  have hAll_card : ∀ m, (All m).card = nbClosedCount G m := fun m => Finset.card_sigma _ _
  have hTL_card : ∀ m, (Tailless m).card = taillessCount G m := by
    intro m
    simp only [Tailless, All, taillessCount, Finset.filter_sigma, Finset.card_sigma]
  have hpart : ∀ m, (All m).card = (Tailless m).card + (Tailed m).card := fun m => by
    simpa [Tailless, Tailed] using
      (Finset.card_filter_add_card_filter_not (s := All m)
        (p := fun x => IsCyclicallyNonBacktracking x.2)).symm
  let Fibers := (All k).sigma fun x =>
    ((G.neighborFinset x.1).erase x.2.snd).erase x.2.reverse.snd
  have hFibers_card : Fibers.card + (Tailless k).card = (d - 1) * (All k).card := by
    rw [Finset.card_sigma]
    have hsplit : (∑ x ∈ All k, (((G.neighborFinset x.1).erase x.2.snd).erase x.2.reverse.snd).card) +
        (Tailless k).card = ∑ x ∈ All k, (d - 1) := by
      have htl_sum : (Tailless k).card =
          ∑ x ∈ All k, if IsCyclicallyNonBacktracking x.2 then 1 else 0 := by
        simp [Tailless, Finset.sum_boole]
      rw [htl_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x hx => ?_
      rcases x with ⟨w, q⟩
      simp only [All, Finset.mem_sigma, Finset.mem_univ, true_and, nbWalks, Finset.mem_filter,
        mem_finsetWalkLength_iff] at hx
      have hqlen : q.length = k := hx.1
      have hqnb : IsNonBacktracking q := hx.2
      have hqpos : 1 ≤ q.length := by omega
      have hsnd_mem : q.snd ∈ G.neighborFinset w := by
        cases q with
        | nil => simp at hqpos
        | cons h₁ _ =>
            simp only [Walk.snd_cons]
            exact (G.mem_neighborFinset w _).mpr h₁
      have hrev_mem : q.reverse.snd ∈ G.neighborFinset w := by
        cases hrv : q.reverse with
        | nil =>
            have h0 := congrArg Walk.length hrv
            simp only [Walk.length_reverse, Walk.length_nil] at h0
            omega
        | cons h₁ _ =>
            simp only [Walk.snd_cons]
            exact (G.mem_neighborFinset w _).mpr h₁
      have hiff := isCyclicallyNonBacktracking_iff_snd_ne_rev_snd q hqnb hqpos
      by_cases hcyc : IsCyclicallyNonBacktracking q
      · have hne : q.snd ≠ q.reverse.snd := hiff.mp hcyc
        have hmem2 : q.reverse.snd ∈ (G.neighborFinset w).erase q.snd :=
          Finset.mem_erase.mpr ⟨Ne.symm hne, hrev_mem⟩
        rw [Finset.card_erase_of_mem hmem2, Finset.card_erase_of_mem hsnd_mem,
            G.card_neighborFinset_eq_degree, hreg w]
        simp only [hcyc, ↓reduceIte]
        omega
      · have heq : q.snd = q.reverse.snd := by
          by_contra hne
          exact hcyc (hiff.mpr hne)
        rw [← heq, Finset.erase_idem, Finset.card_erase_of_mem hsnd_mem,
            G.card_neighborFinset_eq_degree, hreg w]
        simp only [hcyc, ↓reduceIte]
        omega
    rw [hsplit, Finset.sum_const, smul_eq_mul, mul_comm]
  let fwd : (y : (_ : (v : V) × G.Walk v v) × V) → y ∈ Fibers → (v : V) × G.Walk v v :=
    fun y hy =>
      let huw : G.Adj y.2 y.1.1 :=
        ((G.mem_neighborFinset y.1.1 y.2).mp (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_sigma.mp hy).2).2).2).symm
      ⟨y.2, (Walk.cons huw y.1.2).append (Walk.cons huw.symm Walk.nil)⟩
  have hbij : Fibers.card = (Tailed (k + 2)).card := by
    refine Finset.card_bij fwd (fun y hy => ?_) (fun y₁ hy₁ y₂ hy₂ heq => ?_) (fun z hz => ?_)
    · rcases y with ⟨⟨w, q⟩, u⟩
      have hy' := hy
      simp only [Fibers, All, Finset.mem_sigma, Finset.mem_univ, true_and, nbWalks,
        Finset.mem_filter, mem_finsetWalkLength_iff, Finset.mem_erase, G.mem_neighborFinset] at hy'
      have huw : G.Adj u w := hy'.2.2.2.symm
      have hqlen : q.length = k := hy'.1.1
      have hnb_q : IsNonBacktracking q := hy'.1.2
      have hnb_wq : IsNonBacktracking (Walk.cons huw q) := by
        cases q with
        | nil => simp at hqlen; omega
        | cons h₁ rest =>
            simp only [IsNonBacktracking, Walk.snd_cons] at hy' ⊢
            exact ⟨hy'.2.2.1, hnb_q⟩
      have hnb_all : IsNonBacktracking ((Walk.cons huw q).append (Walk.cons huw.symm Walk.nil)) := by
        refine isNonBacktracking_append_single (Walk.cons huw q) huw.symm hnb_wq (by simp) ?_
        have hrev : (Walk.cons huw q).reverse.snd = q.reverse.snd := by
          simp only [Walk.reverse_cons]
          cases hrv : q.reverse with
          | nil =>
              have h0 := congrArg Walk.length hrv
              simp only [Walk.length_reverse, Walk.length_nil] at h0; omega
          | cons _ _ => simp [Walk.cons_append]
        rw [hrev]
        exact hy'.2.1
      have hnotcyc : ¬ IsCyclicallyNonBacktracking ((Walk.cons huw q).append (Walk.cons huw.symm Walk.nil)) := by
        rw [isCyclicallyNonBacktracking_iff_snd_ne_rev_snd _ hnb_all (by simp)]
        have hsnd : ((Walk.cons huw q).append (Walk.cons huw.symm Walk.nil)).snd = w := by
          simp [Walk.cons_append]
        have hrevsnd : ((Walk.cons huw q).append (Walk.cons huw.symm Walk.nil)).reverse.snd = w := by
          simp [Walk.reverse_append, Walk.reverse_cons, Walk.cons_append]
        rw [hsnd, hrevsnd]
        exact not_not.mpr rfl
      simp only [fwd, Tailed, All, Finset.mem_filter, Finset.mem_sigma, Finset.mem_univ, true_and,
        nbWalks, mem_finsetWalkLength_iff]
      exact ⟨⟨by simp [hqlen], hnb_all⟩, hnotcyc⟩
    · rcases y₁ with ⟨⟨w₁, q₁⟩, u₁⟩
      rcases y₂ with ⟨⟨w₂, q₂⟩, u₂⟩
      simp only [fwd, Sigma.mk.inj_iff] at heq
      rcases heq with ⟨rfl, hwalk⟩
      have hwalk' := eq_of_heq hwalk
      have hsnd := congrArg Walk.snd hwalk'
      simp only [Walk.cons_append, Walk.snd_cons] at hsnd
      subst hsnd
      simp only [Walk.cons_append, Walk.cons.injEq, heq_eq_eq, true_and] at hwalk'
      have hrev := congrArg Walk.reverse hwalk'
      simp only [Walk.reverse_append, Walk.reverse_cons, Walk.reverse_nil, Walk.nil_append,
        Walk.cons_append, Walk.cons.injEq, heq_eq_eq, true_and] at hrev
      have hqeq : q₁ = q₂ := by
        have := congrArg Walk.reverse hrev
        simpa using this
      subst hqeq
      rfl
    · rcases z with ⟨u, p⟩
      simp only [Tailed, All, Finset.mem_filter, Finset.mem_sigma, Finset.mem_univ, true_and,
        nbWalks, mem_finsetWalkLength_iff] at hz
      have hplen : p.length = k + 2 := hz.1.1
      have hnb_p : IsNonBacktracking p := hz.1.2
      have hnotcyc := hz.2
      rw [isCyclicallyNonBacktracking_iff_snd_ne_rev_snd p hnb_p (by omega)] at hnotcyc
      have hsnd_eq : p.snd = p.reverse.snd := by
        by_contra hne; exact hnotcyc hne
      cases p with
      | nil => simp at hplen
      | cons huw rest =>
          have hrev_len : rest.reverse.length = k + 1 := by
            simp only [Walk.length_reverse]
            simp only [Walk.length_cons] at hplen
            omega
          cases hrv : rest.reverse with
          | nil =>
              rw [hrv] at hrev_len; simp at hrev_len
          | cons huw' qrev =>
              have hww' : (Walk.cons huw' qrev).snd = (Walk.cons huw rest).snd := by
                have h1 : (Walk.cons huw rest).reverse.snd = (Walk.cons huw' qrev).snd := by
                  rw [Walk.reverse_cons, hrv]; simp [Walk.cons_append]
                rw [← h1]
                exact hsnd_eq.symm
              simp only [Walk.snd_cons] at hww'
              subst hww'
              let q : G.Walk _ _ := qrev.reverse
              have hrest_eq : rest = q.append (Walk.cons huw'.symm Walk.nil) := by
                have := congrArg Walk.reverse hrv
                simpa [q, Walk.reverse_cons] using this
              have hqlen : q.length = k := by
                have h0 : (Walk.cons huw' qrev).length = k + 1 := hrv ▸ hrev_len
                simp only [Walk.length_cons] at h0
                change qrev.reverse.length = k
                rw [Walk.length_reverse]
                omega
              have hnb_q : IsNonBacktracking q := by
                have hnb_rest : IsNonBacktracking rest :=
                  isNonBacktracking_of_append_right (p := Walk.cons huw Walk.nil) (q := rest) hnb_p
                exact isNonBacktracking_of_append_left (hrest_eq ▸ hnb_rest)
              have hne_snd : u ≠ q.snd := by
                have hp' : Walk.cons huw rest =
                    Walk.cons huw (q.append (Walk.cons huw'.symm Walk.nil)) := by rw [hrest_eq]
                cases hq_eq : q with
                | nil =>
                    rw [hq_eq] at hqlen; simp at hqlen; omega
                | cons h₁ q' =>
                    rw [hp', hq_eq, Walk.cons_append] at hnb_p
                    simpa [Walk.snd_cons] using hnb_p.1
              have hne_rev : u ≠ q.reverse.snd := by
                have hnb_rev := isNonBacktracking_reverse hnb_p
                rw [Walk.reverse_cons, hrv] at hnb_rev
                have hnb_r2 : IsNonBacktracking (Walk.cons huw' qrev) :=
                  isNonBacktracking_of_append_left hnb_rev
                cases qrev with
                | nil =>
                    change Walk.nil.reverse.length = k at hqlen
                    simp at hqlen; omega
                | cons h₁ qrev' =>
                    simp only [IsNonBacktracking] at hnb_r2
                    simpa [q, Walk.reverse_reverse, Walk.snd_cons] using hnb_r2.1
              refine ⟨⟨⟨_, q⟩, u⟩, ?_, ?_⟩
              · simp only [Fibers, All, Finset.mem_sigma, Finset.mem_univ, true_and, nbWalks,
                  Finset.mem_filter, mem_finsetWalkLength_iff, Finset.mem_erase,
                  G.mem_neighborFinset]
                exact ⟨⟨hqlen, hnb_q⟩, hne_rev, hne_snd, huw.symm⟩
              · simp only [fwd, Sigma.mk.inj_iff, heq_eq_eq, true_and]
                rw [hrest_eq]
                rfl
  have h1 := hpart (k + 2)
  rw [hAll_card, hTL_card, ← hbij] at h1
  rw [hAll_card, hTL_card] at hFibers_card
  omega

/-- Exact combinatorial identity: for every `d`-regular graph (`d ≥ 2`) and `L ≥ 1`,
`taillessCount G (2 * L) = Tr(T_{2L}(A)) + (d - 2) * n`. -/
theorem taillessCount_eq_chebMat_trace (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hd : 2 ≤ d) (hreg : ∀ v : V, G.degree v = d) :
    ∀ L : ℕ, 1 ≤ L →
      (taillessCount G (2 * L) : ℚ) =
        Matrix.trace (chebMat G d (2 * L)) + ((d - 2 : ℕ) : ℚ) * (Fintype.card V : ℚ) := by
  intro L hL
  have hcheb := chebMat_eq_nbMat_sub G hd hreg (2 * L) (by omega)
  have htr : Matrix.trace (chebMat G d (2 * L)) =
      (nbClosedCount G (2 * L) : ℚ) -
        ((d - 2 : ℕ) : ℚ) * ∑ j ∈ Finset.Icc 1 L, (nbClosedCount G (2 * L - 2 * j) : ℚ) := by
    rw [hcheb, trace_sub, trace_smul, nbMat_trace_eq_nbClosedCount,
        show (2 * L) / 2 = L by omega, trace_sum, smul_eq_mul]
    congr 2
    refine Finset.sum_congr rfl fun j _ => nbMat_trace_eq_nbClosedCount G (2 * L - 2 * j)
  have hsum_split :
      (∑ j ∈ Finset.Icc 1 L, (nbClosedCount G (2 * L - 2 * j) : ℚ)) =
        (∑ j ∈ Finset.Icc 1 (L - 1), (nbClosedCount G (2 * L - 2 * j) : ℚ)) +
          (Fintype.card V : ℚ) := by
    have hL' : L = (L - 1) + 1 := by omega
    conv_lhs => rw [hL', Finset.sum_Icc_succ_top (by omega : 1 ≤ (L - 1) + 1)]
    have h0 : 2 * L - 2 * L = 0 := Nat.sub_self _
    have hc0 : (nbClosedCount G 0 : ℚ) = (Fintype.card V : ℚ) := by
      have := nbMat_trace_eq_nbClosedCount G 0
      rw [nbMat_zero] at this
      simpa [Matrix.trace] using this.symm
    rw [← hL', h0, hc0]
  rw [htr, hsum_split]
  have htelesc : ∀ m : ℕ, 1 ≤ m →
      (taillessCount G (2 * m) : ℚ) +
        ((d - 2 : ℕ) : ℚ) * (∑ j ∈ Finset.Icc 1 (m - 1), (nbClosedCount G (2 * m - 2 * j) : ℚ)) =
      (nbClosedCount G (2 * m) : ℚ) := by
    intro m hm
    induction m with
    | zero => omega
    | succ m ih =>
        cases m with
        | zero =>
            have hc2 : nbClosedCount G 2 = 0 := by
              simp [nbClosedCount, nbWalks_two_card]
            have ht2 : taillessCount G 2 = 0 := by
              simp only [taillessCount]
              refine Finset.sum_eq_zero fun v _ => ?_
              have hle := Finset.card_filter_le (nbWalks G 2 v v) IsCyclicallyNonBacktracking
              have h0 : (nbWalks G 2 v v).card = 0 := by simp [nbWalks_two_card]
              omega
            simp [hc2, ht2]
        | succ r =>
            have ihr := ih (by omega)
            have hstrip := one_step_tail_strip G hd hreg (2 * (r + 1)) (by omega)
            rw [show 2 * (r + 1) + 2 = 2 * (r + 2) by omega] at hstrip
            have hstrip_q : (nbClosedCount G (2 * (r + 2)) : ℚ) + (taillessCount G (2 * (r + 1)) : ℚ) =
                (taillessCount G (2 * (r + 2)) : ℚ) +
                  ((d - 1 : ℕ) : ℚ) * (nbClosedCount G (2 * (r + 1)) : ℚ) := by
              have hcast := congrArg (Nat.cast (R := ℚ)) hstrip
              push_cast at hcast
              exact hcast
            have hdq : ((d - 1 : ℕ) : ℚ) = ((d - 2 : ℕ) : ℚ) + 1 := by
              have : d - 1 = (d - 2) + 1 := by omega
              exact_mod_cast this
            have hsum_shift :
                (∑ j ∈ Finset.Icc 1 (r + 1), (nbClosedCount G (2 * (r + 2) - 2 * j) : ℚ)) =
                  (nbClosedCount G (2 * (r + 1)) : ℚ) +
                    ∑ j ∈ Finset.Icc 1 r, (nbClosedCount G (2 * (r + 1) - 2 * j) : ℚ) := by
              rw [show Finset.Icc 1 (r + 1) = insert 1 (Finset.Icc 2 (r + 1)) by
                    ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega]
              have h1not : 1 ∉ Finset.Icc 2 (r + 1) := by simp
              rw [Finset.sum_insert h1not]
              congr 1
              refine Finset.sum_bij (fun j _ => j - 1) ?_ ?_ ?_ ?_
              · intro j hj; simp only [Finset.mem_Icc] at hj ⊢; omega
              · intro j₁ hj₁ j₂ hj₂ h; simp only [Finset.mem_Icc] at hj₁ hj₂; omega
              · intro b hb; refine ⟨b + 1, ?_, by omega⟩; simp only [Finset.mem_Icc] at hb ⊢; omega
              · intro j hj
                simp only [Finset.mem_Icc] at hj
                rw [show 2 * (r + 2) - 2 * j = 2 * (r + 1) - 2 * (j - 1) by omega]
            have hsub_r : r + 2 - 1 = r + 1 := by omega
            have hsub_r1 : r + 1 - 1 = r := by omega
            rw [hsub_r, hsum_shift]
            rw [hsub_r1] at ihr
            rw [hdq] at hstrip_q
            linarith
  have ht := htelesc L hL
  linarith

/-- Unconditional eigenvalue-free lower bound on `taillessCount G (2 * L)`. -/
theorem taillessCount_double_ge (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hd : 2 ≤ d) (hreg : ∀ v : V, G.degree v = d) (hn : 0 < Fintype.card V)
    {L : ℕ} (hL : 1 ≤ L) :
    (((d - 1 : ℕ) : ℚ) ^ L + 1) ^ 2 -
      (2 * ((d - 1 : ℕ) : ℚ) ^ L - ((d - 2 : ℕ) : ℚ)) * (Fintype.card V : ℚ) ≤
    (taillessCount G (2 * L) : ℚ) := by
  rw [taillessCount_eq_chebMat_trace G hd hreg L hL, chebMat_double G d L,
      trace_sub, trace_smul]
  simp only [Matrix.trace_one, smul_eq_mul]
  have hsq := chebMat_sq_trace_ge G (by omega) hreg hn L
  linarith

/-- Sharpened Cauchy-Schwarz lower bound on `taillessCount G (2 * L)` when `taillessCount G L = 0`
(for even `L ≥ 2`). -/
theorem taillessCount_double_sharp (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hd : 2 ≤ d) (hreg : ∀ v : V, G.degree v = d) (hn : 0 < Fintype.card V)
    {m : ℕ} (hm : 1 ≤ m) (hzero : taillessCount G (2 * m) = 0) :
    (Fintype.card V : ℚ) * (((d - 1 : ℕ) : ℚ) ^ (2 * m) + 1) ^ 2 +
      (((d - 2 : ℕ) : ℚ) * (Fintype.card V : ℚ) + (((d - 1 : ℕ) : ℚ) ^ (2 * m) + 1)) ^ 2 -
      (2 * ((d - 1 : ℕ) : ℚ) ^ (2 * m) - ((d - 2 : ℕ) : ℚ)) * (Fintype.card V : ℚ) ^ 2 ≤
    (Fintype.card V : ℚ) * (taillessCount G (2 * (2 * m)) : ℚ) := by
  set L := 2 * m
  set n : ℚ := (Fintype.card V : ℚ)
  set M : ℚ := ((d - 1 : ℕ) : ℚ) ^ L + 1
  have hL : 1 ≤ L := by omega
  have htrL : Matrix.trace (chebMat G d L) = -(((d - 2 : ℕ) : ℚ) * n) := by
    have h := taillessCount_eq_chebMat_trace G hd hreg m hm
    rw [hzero, Nat.cast_zero] at h
    linarith
  have hsharp := chebMat_sq_trace_sharp G (by omega) hreg hn L
  rw [htrL] at hsharp
  have hsq_eq : (-(((d - 2 : ℕ) : ℚ) * n) - M) ^ 2 = (((d - 2 : ℕ) : ℚ) * n + M) ^ 2 := by ring
  rw [show -(((d - 2 : ℕ) : ℚ) * n) - (((d - 1 : ℕ) : ℚ) ^ L + 1) =
        -(((d - 2 : ℕ) : ℚ) * n) - M from rfl, hsq_eq] at hsharp
  rw [taillessCount_eq_chebMat_trace G hd hreg L hL, chebMat_double G d L,
      trace_sub, trace_smul]
  simp only [Matrix.trace_one, smul_eq_mul]
  have hmul : n * (Matrix.trace (chebMat G d L * chebMat G d L) -
      2 * ((d - 1 : ℕ) : ℚ) ^ L * n + ((d - 2 : ℕ) : ℚ) * n) =
    n * Matrix.trace (chebMat G d L * chebMat G d L) -
      (2 * ((d - 1 : ℕ) : ℚ) ^ L - ((d - 2 : ℕ) : ℚ)) * n ^ 2 := by ring
  rw [hmul]
  linarith

/-- Extract a concrete cyclically non-backtracking closed walk of length `m` from `taillessCount G m > 0`. -/
theorem exists_tailless_of_pos (G : SimpleGraph V) [DecidableRel G.Adj] {m : ℕ}
    (hpos : 0 < taillessCount G m) :
    ∃ (v : V) (p : G.Walk v v), IsCyclicallyNonBacktracking p ∧ p.length = m := by
  unfold taillessCount at hpos
  obtain ⟨v, _, hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero (Nat.ne_of_gt hpos)
  obtain ⟨p, hmem⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hv)
  simp only [nbWalks, Finset.mem_filter, mem_finsetWalkLength_iff] at hmem
  exact ⟨v, p, hmem.2, hmem.1.1⟩

/-- **Main Theorem 1 (Unconditional Eigenvalue-Free Chebyshev-Squaring Girth-Doubling Closure)**:
For EVERY finite `d`-regular simple graph (`d ≥ 3`) of girth `g > 2^k` (`k ≥ 1`) and order `n`
satisfying `n * (2 * (d - 1)^(2^k) - (d - 2)) < ((d - 1)^(2^k) + 1)^2`,
`G` unconditionally contains a simple `2^(k+1)`-cycle (`Erdos64Closure.HasPower G`).
Zero Ramanujan / spectral-gap hypothesis is required. -/
theorem unconditional_chebyshev_girth_doubling_hasPower (G : SimpleGraph V) [DecidableRel G.Adj]
    {d k : ℕ} (hd : 3 ≤ d) (hreg : ∀ v : V, G.degree v = d) (hn : 0 < Fintype.card V)
    (hk : 1 ≤ k) (hg : GirthAtLeast G (2 ^ k + 1))
    (hord : Fintype.card V * (2 * (d - 1) ^ (2 ^ k) - (d - 2)) <
      ((d - 1) ^ (2 ^ k) + 1) ^ 2) :
    HasPower G := by
  have hL : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hlb := taillessCount_double_ge G (by omega) hreg hn hL
  have hsub_le : d - 2 ≤ 2 * (d - 1) ^ (2 ^ k) := by
    have hpow2 : d - 1 ≤ (d - 1) ^ (2 ^ k) := by
      calc d - 1 = (d - 1) ^ 1 := (pow_one _).symm
        _ ≤ (d - 1) ^ (2 ^ k) := Nat.pow_le_pow_right (by omega) hL
    omega
  have hord_q : (2 * ((d - 1 : ℕ) : ℚ) ^ (2 ^ k) - ((d - 2 : ℕ) : ℚ)) * (Fintype.card V : ℚ) <
      (((d - 1 : ℕ) : ℚ) ^ (2 ^ k) + 1) ^ 2 := by
    have hq : ((Fintype.card V * (2 * (d - 1) ^ (2 ^ k) - (d - 2)) : ℕ) : ℚ) <
        ((((d - 1) ^ (2 ^ k) + 1) ^ 2 : ℕ) : ℚ) := by exact_mod_cast hord
    rw [Nat.cast_mul, Nat.cast_sub hsub_le] at hq
    push_cast at hq
    linarith
  have hpos_q : (0 : ℚ) < (taillessCount G (2 * 2 ^ k) : ℚ) := by linarith
  have hpos : 0 < taillessCount G (2 * 2 ^ k) := by exact_mod_cast hpos_q
  obtain ⟨v, p, hcyc, hlen⟩ := exists_tailless_of_pos G hpos
  have hpow_eq : 2 * 2 ^ k = 2 ^ (k + 1) := by ring
  rw [hpow_eq] at hlen
  exact hasPower_of_cyclicallyNonBacktracking_lt_two_girth hg (by omega : 2 ≤ k + 1)
    (by omega : 2 ^ (k + 1) < 2 * (2 ^ k + 1)) p hcyc hlen

/-- **Main Theorem 2 (Sharpened Cauchy-Schwarz Unconditional Closure)**:
When `k ≥ 2`, if `G` has no `2^k`-cycle then `taillessCount G (2^k) = 0`, sharpening the
unconditional order threshold via Cauchy-Schwarz on the traceless residual matrix. -/
theorem unconditional_chebyshev_girth_doubling_sharp (G : SimpleGraph V) [DecidableRel G.Adj]
    {d k : ℕ} (hd : 3 ≤ d) (hreg : ∀ v : V, G.degree v = d) (hn : 0 < Fintype.card V)
    (hk : 2 ≤ k) (hg : GirthAtLeast G (2 ^ k + 1))
    (hord : Fintype.card V * Fintype.card V * (2 * (d - 1) ^ (2 ^ k) - (d - 2)) <
      Fintype.card V * ((d - 1) ^ (2 ^ k) + 1) ^ 2 +
        ((d - 2) * Fintype.card V + (d - 1) ^ (2 ^ k) + 1) ^ 2) :
    HasPower G := by
  by_contra hnp
  have hm_eq : 2 ^ k = 2 * 2 ^ (k - 1) := by
    have hk1 : k = (k - 1) + 1 := by omega
    conv_lhs => rw [hk1, pow_succ]
    ring
  have hm_ge : 1 ≤ 2 ^ (k - 1) := Nat.one_le_two_pow
  have hzero : taillessCount G (2 * 2 ^ (k - 1)) = 0 := by
    by_contra hne
    obtain ⟨v, p, hcyc, hlen⟩ := exists_tailless_of_pos G (Nat.pos_of_ne_zero hne)
    rw [← hm_eq] at hlen
    exact no_cyclicallyNonBacktracking_in_girth_window_of_not_hasPower hg hnp hk
      (by omega : 2 ^ k < 2 * (2 ^ k + 1)) p hcyc hlen
  have hsharp := taillessCount_double_sharp G (by omega) hreg hn hm_ge hzero
  rw [← hm_eq] at hsharp
  have hsub_le : d - 2 ≤ 2 * (d - 1) ^ (2 ^ k) := by
    have hpow2 : d - 1 ≤ (d - 1) ^ (2 ^ k) := by
      calc d - 1 = (d - 1) ^ 1 := (pow_one _).symm
        _ ≤ (d - 1) ^ (2 ^ k) := Nat.pow_le_pow_right (by omega) Nat.one_le_two_pow
    omega
  have hord_q :
      (2 * ((d - 1 : ℕ) : ℚ) ^ (2 ^ k) - ((d - 2 : ℕ) : ℚ)) * (Fintype.card V : ℚ) ^ 2 <
        (Fintype.card V : ℚ) * (((d - 1 : ℕ) : ℚ) ^ (2 ^ k) + 1) ^ 2 +
          (((d - 2 : ℕ) : ℚ) * (Fintype.card V : ℚ) + (((d - 1 : ℕ) : ℚ) ^ (2 ^ k) + 1)) ^ 2 := by
    have hq : ((Fintype.card V * Fintype.card V * (2 * (d - 1) ^ (2 ^ k) - (d - 2)) : ℕ) : ℚ) <
        ((Fintype.card V * ((d - 1) ^ (2 ^ k) + 1) ^ 2 +
          ((d - 2) * Fintype.card V + (d - 1) ^ (2 ^ k) + 1) ^ 2 : ℕ) : ℚ) := by
      exact_mod_cast hord
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hsub_le] at hq
    push_cast at hq
    linarith
  have hpos_q : (0 : ℚ) < (Fintype.card V : ℚ) * (taillessCount G (2 * 2 ^ k) : ℚ) := by
    linarith
  have hpos_t : (0 : ℚ) < (taillessCount G (2 * 2 ^ k) : ℚ) :=
    pos_of_mul_pos_right hpos_q (Nat.cast_nonneg _)
  have hpos : 0 < taillessCount G (2 * 2 ^ k) := by exact_mod_cast hpos_t
  obtain ⟨v, p, hcyc, hlen⟩ := exists_tailless_of_pos G hpos
  have hpow_eq : 2 * 2 ^ k = 2 ^ (k + 1) := by ring
  rw [hpow_eq] at hlen
  exact hnp (hasPower_of_cyclicallyNonBacktracking_lt_two_girth hg (by omega : 2 ≤ k + 1)
    (by omega : 2 ^ (k + 1) < 2 * (2 ^ k + 1)) p hcyc hlen)

/-- Unconditional cubic girth ≥ 9 closure up to `n ≤ 131` (2.85x Moore bound, zero spectral hypothesis). -/
theorem cubic_girth9_le_131_hasPower (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : ∀ v : V, G.degree v = 3) (hn : 0 < Fintype.card V) (hle : Fintype.card V ≤ 131)
    (hg : GirthAtLeast G 9) : HasPower G := by
  refine unconditional_chebyshev_girth_doubling_sharp G (d := 3) (k := 3) (by decide)
    hreg hn (by decide) (by simpa using hg) ?_
  have h1 : (2 : ℕ) ^ 3 = 8 := by decide
  have h2 : (3 - 1 : ℕ) ^ 8 = 256 := by decide
  rw [h1, h2]
  nlinarith

/-- Unconditional cubic girth ≥ 17 closure up to `n ≤ 32771` (42.78x Moore bound, zero spectral hypothesis). -/
theorem cubic_girth17_le_32771_hasPower (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : ∀ v : V, G.degree v = 3) (hn : 0 < Fintype.card V) (hle : Fintype.card V ≤ 32771)
    (hg : GirthAtLeast G 17) : HasPower G := by
  refine unconditional_chebyshev_girth_doubling_sharp G (d := 3) (k := 4) (by decide)
    hreg hn (by decide) (by simpa using hg) ?_
  have h1 : (2 : ℕ) ^ 4 = 16 := by decide
  have h2 : (3 - 1 : ℕ) ^ 16 = 65536 := by decide
  rw [h1, h2]
  nlinarith

/-- Unconditional cubic girth ≥ 33 closure up to `n ≤ 2147483651` (10,922x Moore bound, zero spectral hypothesis). -/
theorem cubic_girth33_le_2147483651_hasPower (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : ∀ v : V, G.degree v = 3) (hn : 0 < Fintype.card V) (hle : Fintype.card V ≤ 2147483651)
    (hg : GirthAtLeast G 33) : HasPower G := by
  refine unconditional_chebyshev_girth_doubling_sharp G (d := 3) (k := 5) (by decide)
    hreg hn (by decide) (by simpa using hg) ?_
  have h1 : (2 : ℕ) ^ 5 = 32 := by decide
  have h2 : (3 - 1 : ℕ) ^ 32 = 4294967296 := by decide
  rw [h1, h2]
  nlinarith

/-- Unconditional 4-regular girth ≥ 5 closure up to `n ≤ 46` (2.71x Moore bound, zero spectral hypothesis). -/
theorem four_reg_girth5_le_46_hasPower (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : ∀ v : V, G.degree v = 4) (hn : 0 < Fintype.card V) (hle : Fintype.card V ≤ 46)
    (hg : GirthAtLeast G 5) : HasPower G := by
  refine unconditional_chebyshev_girth_doubling_sharp G (d := 4) (k := 2) (by decide)
    hreg hn (by decide) (by simpa using hg) ?_
  have h1 : (2 : ℕ) ^ 2 = 4 := by decide
  have h2 : (4 - 1 : ℕ) ^ 4 = 81 := by decide
  rw [h1, h2]
  nlinarith

/-- **Whole-Problem Closure Gate**: If every finite simple graph with `δ(G) ≥ 3` admits
some `k ≥ 2` where the total cyclically non-backtracking walk count `taillessCount G (2^k)`
strictly exceeds the non-simple count `nonSimpleTaillessCount G (2^k)`, then the entire
Erdős–Gyárfás Conjecture holds. -/
theorem erdos64_closed_of_tailless_gt_nonSimple
    (H : ∀ {W : Type} [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj],
      (∀ v : W, 3 ≤ G.degree v) →
      ∃ k : ℕ, 2 ≤ k ∧ nonSimpleTaillessCount G (2 ^ k) < taillessCount G (2 ^ k)) :
    ∀ {W : Type} [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj],
      (∀ v : W, 3 ≤ G.degree v) → HasPower G := by
  intro W _ _ G _ hdeg
  classical
  obtain ⟨k, hk, hlt⟩ := H G hdeg
  unfold nonSimpleTaillessCount taillessCount at hlt
  have hex : ∃ v : W,
      ((nbWalks G (2 ^ k) v v).filter fun p => IsCyclicallyNonBacktracking p ∧ ¬ p.IsCycle).card <
      ((nbWalks G (2 ^ k) v v).filter IsCyclicallyNonBacktracking).card := by
    by_contra hall
    push Not at hall
    have hle := Finset.sum_le_sum fun v (_ : v ∈ Finset.univ) => hall v
    omega
  obtain ⟨v, hv⟩ := hex
  have hsub : ¬ (((nbWalks G (2 ^ k) v v).filter IsCyclicallyNonBacktracking) ⊆
      ((nbWalks G (2 ^ k) v v).filter fun p => IsCyclicallyNonBacktracking p ∧ ¬ p.IsCycle)) := by
    intro hss
    have := Finset.card_le_card hss
    omega
  rw [Finset.not_subset] at hsub
  obtain ⟨p, hmem, hnotmem⟩ := hsub
  simp only [nbWalks, Finset.mem_filter, mem_finsetWalkLength_iff, not_and, not_not] at hmem hnotmem
  exact ⟨k, v, p, hk, hnotmem hmem.1 hmem.2, hmem.1.1⟩

end CombinatorialBridge

#print axioms chebMat_double
#print axioms chebMat_sq_trace_ge
#print axioms chebMat_sq_trace_sharp
#print axioms nbMat_rec
#print axioms chebMat_eq_nbMat_sub
#print axioms taillessCount_eq_chebMat_trace
#print axioms taillessCount_double_ge
#print axioms taillessCount_double_sharp
#print axioms unconditional_chebyshev_girth_doubling_hasPower
#print axioms unconditional_chebyshev_girth_doubling_sharp
#print axioms cubic_girth9_le_131_hasPower
#print axioms cubic_girth17_le_32771_hasPower
#print axioms cubic_girth33_le_2147483651_hasPower
#print axioms four_reg_girth5_le_46_hasPower
#print axioms erdos64_closed_of_tailless_gt_nonSimple

end E64Wave5Agent6
