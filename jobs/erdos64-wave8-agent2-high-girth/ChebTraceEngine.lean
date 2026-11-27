import Shadow
import NonBacktrackingGirth
import Wave5Agent5GirthTripling
import Wave5Agent6ChebyshevGirth
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Wave 8 Agent #2 — Pillar 1: Exact Pure-2-Square Chebyshev Trace Positivity Engine

Extends Wave 5 Agent #6's eigenvalue-free Chebyshev-Hashimoto trace framework over `ℚ`:
1. `taillessCount_eq_chebMat_trace_odd` & `taillessCount_eq_chebMat_trace_all`:
   Exact combinatorial identity for ALL `k ≥ 1` (both even and odd):
   `taillessCount G k = Tr(T_k(A)) + (if k % 2 = 0 then (d - 2) * n else 0)`.
2. `chebMat_mul_cubic`: Exact product identity for cubic (`d = 3`) Chebyshev matrices:
   `T_j(A) * T_k(A) = T_{j+k}(A) + 2^{min j k} * T_{|j-k|}(A)`.
3. `chebComb`, `chebMul3`, `chebAdd`, `chebComb_mul_cubic`:
   Exact `List ℤ`-indexed Chebyshev linear combinations and multiplication algebra.
4. `two_square_cheb_trace_lb`:
   For ANY `p q : List ℤ`, `S = p*p + q*q` satisfies
   `(eval3 p)^2 + (eval3 q)^2 ≤ Tr(chebComb G 3 S)` unconditionally over `ℚ` (zero eigenvalues!).
5. `cert_trace_surplus_of_two_square`:
   Kernel-computable certificate checker `checkCert g L N p q alpha = true` unconditionally
   implies `∑ k ∈ Finset.range L, lookupAlpha alpha k * taillessCount G k < taillessCount G L`
   for every power-free cubic graph of girth `≥ g` and order `0 < |V| ≤ N`.
-/

namespace E64Wave8Agent2
open SimpleGraph Erdos64Closure E64NonBacktrackingGirth E64Wave5Agent5 E64Wave5Agent6 Matrix

section OddAndAllTrace

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exact odd-length combinatorial trace identity: for every `d`-regular graph (`d ≥ 2`),
`taillessCount G (2 * m + 1) = Tr(T_{2m+1}(A))`. -/
theorem taillessCount_eq_chebMat_trace_odd (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hd : 2 ≤ d) (hreg : ∀ v : V, G.degree v = d) :
    ∀ m : ℕ, (taillessCount G (2 * m + 1) : ℚ) = Matrix.trace (chebMat G d (2 * m + 1)) := by
  intro m
  have hcheb := chebMat_eq_nbMat_sub G hd hreg (2 * m + 1) (by omega)
  have htr : Matrix.trace (chebMat G d (2 * m + 1)) =
      (nbClosedCount G (2 * m + 1) : ℚ) -
        ((d - 2 : ℕ) : ℚ) * ∑ j ∈ Finset.Icc 1 m, (nbClosedCount G (2 * m + 1 - 2 * j) : ℚ) := by
    rw [hcheb, trace_sub, trace_smul, nbMat_trace_eq_nbClosedCount,
        show (2 * m + 1) / 2 = m by omega, map_sum, smul_eq_mul]
    congr 2
    refine Finset.sum_congr rfl fun j _ => nbMat_trace_eq_nbClosedCount G (2 * m + 1 - 2 * j)
  rw [htr]
  have htelesc : ∀ r : ℕ,
      (taillessCount G (2 * r + 1) : ℚ) +
        ((d - 2 : ℕ) : ℚ) * (∑ j ∈ Finset.Icc 1 r, (nbClosedCount G (2 * r + 1 - 2 * j) : ℚ)) =
      (nbClosedCount G (2 * r + 1) : ℚ) := by
    intro r
    induction r with
    | zero =>
        have hc1 : nbClosedCount G 1 = 0 := by
          unfold nbClosedCount
          refine Finset.sum_eq_zero fun v _ => ?_
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          rintro ⟨p, hp⟩ _
          cases p with
          | nil => simp at hp
          | cons h rest =>
              cases rest with
              | nil => exact G.loopless v h
              | cons _ _ => simp at hp
        have ht1 : taillessCount G 1 = 0 := by
          unfold taillessCount
          refine Finset.sum_eq_zero fun v _ => ?_
          have hle := Finset.card_filter_le (nbWalks G 1 v v)
            (fun p => IsCyclicallyNonBacktracking p.1)
          have h0 : (nbWalks G 1 v v).card = 0 := by
            have hsum : nbClosedCount G 1 = 0 := hc1
            unfold nbClosedCount at hsum
            exact Finset.sum_eq_zero_iff.mp hsum v (Finset.mem_univ v)
          omega
        simp [hc1, ht1]
    | succ r ih =>
        have hstrip := one_step_tail_strip G hd hreg (2 * r + 1) (by omega)
        have hstrip_q : (nbClosedCount G (2 * (r + 1) + 1) : ℚ) + (taillessCount G (2 * r + 1) : ℚ) =
            (taillessCount G (2 * (r + 1) + 1) : ℚ) +
              ((d - 1 : ℕ) : ℚ) * (nbClosedCount G (2 * r + 1) : ℚ) := by
          have h1 : 2 * (r + 1) + 1 = (2 * r + 1) + 2 := by omega
          rw [h1]
          exact_mod_cast hstrip
        have hdq : ((d - 1 : ℕ) : ℚ) = ((d - 2 : ℕ) : ℚ) + 1 := by
          have : d - 1 = (d - 2) + 1 := by omega
          exact_mod_cast this
        have hsum_shift :
            (∑ j ∈ Finset.Icc 1 (r + 1), (nbClosedCount G (2 * (r + 1) + 1 - 2 * j) : ℚ)) =
              (nbClosedCount G (2 * r + 1) : ℚ) +
                ∑ j ∈ Finset.Icc 1 r, (nbClosedCount G (2 * r + 1 - 2 * j) : ℚ) := by
          rw [show Finset.Icc 1 (r + 1) = insert 1 (Finset.Icc 2 (r + 1)) by
                ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega]
          have h1not : 1 ∉ Finset.Icc 2 (r + 1) := by simp
          rw [Finset.sum_insert h1not]
          congr 1
          · congr 2; omega
          · refine Finset.sum_bij (fun j _ => j - 1) ?_ ?_ ?_ ?_
            · intro j hj; simp only [Finset.mem_Icc] at hj ⊢; omega
            · intro j₁ hj₁ j₂ hj₂ h; simp only [Finset.mem_Icc] at hj₁ hj₂; omega
            · intro b hb; refine ⟨b + 1, ?_, by omega⟩; simp only [Finset.mem_Icc] at hb ⊢; omega
            · intro j hj; simp only [Finset.mem_Icc] at hj; congr 2; omega
        rw [hsum_shift]
        rw [hdq] at hstrip_q
        linarith
  have ht := htelesc m
  linarith

/-- Unified combinatorial trace identity for ALL `k ≥ 1` in any `d`-regular graph (`d ≥ 2`). -/
theorem taillessCount_eq_chebMat_trace_all (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hd : 2 ≤ d) (hreg : ∀ v : V, G.degree v = d) {k : ℕ} (hk : 1 ≤ k) :
    (taillessCount G k : ℚ) =
      Matrix.trace (chebMat G d k) +
        if k % 2 = 0 then ((d - 2 : ℕ) : ℚ) * (Fintype.card V : ℚ) else 0 := by
  by_cases hev : k % 2 = 0
  · have hkm : k = 2 * (k / 2) := by omega
    have hpos : 1 ≤ k / 2 := by omega
    rw [if_pos hev]
    conv_lhs => rw [hkm]
    conv_rhs => rw [hkm]
    exact taillessCount_eq_chebMat_trace G hd hreg (k / 2) hpos
  · have hkm : k = 2 * (k / 2) + 1 := by omega
    rw [if_neg hev, add_zero]
    conv_lhs => rw [hkm]
    conv_rhs => rw [hkm]
    exact taillessCount_eq_chebMat_trace_odd G hd hreg (k / 2)

/-- Zero tailless walks of length `1 ≤ k < g` when girth is at least `g`. -/
theorem taillessCount_eq_zero_of_lt_girth (G : SimpleGraph V) [DecidableRel G.Adj]
    {g k : ℕ} (hg : GirthAtLeast G g) (hk1 : 1 ≤ k) (hkg : k < g) :
    taillessCount G k = 0 := by
  by_contra hne
  obtain ⟨v, p, hcyc, hlen⟩ := exists_tailless_of_pos G (Nat.pos_of_ne_zero hne)
  have hge := girth_le_length_of_nonBacktracking_closed hg k p hlen (by omega)
    (isNonBacktracking_of_append_left hcyc)
  omega

/-- Zero tailless walks of length `2^m < 2 * g` (`m ≥ 2`) in any power-free graph. -/
theorem taillessCount_pow2_eq_zero (G : SimpleGraph V) [DecidableRel G.Adj]
    {g m : ℕ} (hg : GirthAtLeast G g) (hnp : ¬ HasPower G) (hm : 2 ≤ m) (hlt : 2 ^ m < 2 * g) :
    taillessCount G (2 ^ m) = 0 := by
  by_contra hne
  obtain ⟨v, p, hcyc, hlen⟩ := exists_tailless_of_pos G (Nat.pos_of_ne_zero hne)
  exact no_cyclicallyNonBacktracking_in_girth_window_of_not_hasPower hg hnp hm hlt p hcyc hlen

end OddAndAllTrace

section ChebyshevListAlgebra

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Symmetric product identity for cubic (`d = 3`) Chebyshev matrices:
`T_j(A) * T_k(A) = T_{j+k}(A) + 2^{min j k} • T_{max j k - min j k}(A)`. -/
theorem chebMat_mul_cubic (G : SimpleGraph V) [DecidableRel G.Adj] (j k : ℕ) :
    chebMat G 3 j * chebMat G 3 k =
      chebMat G 3 (j + k) + ((2 ^ min j k : ℕ) : ℚ) • chebMat G 3 (max j k - min j k) := by
  by_cases hjk : j ≤ k
  · have h := chebMat_add_sub G 3 j k hjk
    have hmin : min j k = j := Nat.min_eq_left hjk
    have hmax : max j k = k := Nat.max_eq_right hjk
    rw [hmin, hmax, Nat.add_comm j k]
    have h2 : (((3 - 1 : ℕ) : ℚ) ^ j) = ((2 ^ j : ℕ) : ℚ) := by norm_num
    rw [h2] at h
    exact h.symm
  · have hkj : k ≤ j := by omega
    have h := congrArg Matrix.transpose (chebMat_add_sub G 3 k j hkj)
    rw [transpose_add, transpose_smul, transpose_mul,
        chebMat_symm, chebMat_symm, chebMat_symm, chebMat_symm] at h
    have hmin : min j k = k := Nat.min_eq_right hkj
    have hmax : max j k = j := Nat.max_eq_left hkj
    rw [hmin, hmax]
    have h2 : (((3 - 1 : ℕ) : ℚ) ^ k) = ((2 ^ k : ℕ) : ℚ) := by norm_num
    rw [h2] at h
    exact h.symm

/-- Pure integer Chebyshev evaluation at `λ₁ = 3`: `∑_{k} p[k] * (2^k + 1)`. -/
def chebEval3 (p : List ℤ) : ℤ :=
  ((List.range p.length).map fun k => p.getD k 0 * ((2 : ℤ) ^ k + 1)).sum

/-- Pure integer Chebyshev addition. -/
def chebAdd (p q : List ℤ) : List ℤ :=
  (List.range (max p.length q.length)).map fun k => p.getD k 0 + q.getD k 0

/-- Pure integer cubic Chebyshev multiplication: coefficient of `T_m` in `p * q`. -/
def chebMul3Coeff (p q : List ℤ) (m : ℕ) : ℤ :=
  ((List.range p.length).map fun j =>
    ((List.range q.length).map fun k =>
      (if j + k = m then p.getD j 0 * q.getD k 0 else 0) +
      (if max j k - min j k = m then p.getD j 0 * q.getD k 0 * ((2 : ℤ) ^ min j k) else 0)).sum).sum

/-- Pure integer cubic Chebyshev product list of length `p.length + q.length`. -/
def chebMul3 (p q : List ℤ) : List ℤ :=
  (List.range (p.length + q.length)).map (chebMul3Coeff p q)

/-- Helper connecting `List.sum` over `List.range n` to `Finset.sum` over `Finset.range n`. -/
theorem list_sum_range_eq_finset_sum {α : Type*} [AddCommMonoid α] (n : ℕ) (f : ℕ → α) :
    ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
          Finset.sum_range_succ, ih]

/-- Matrix linear combination of Chebyshev matrices `∑ k, p[k] • T_k(A)`. -/
def chebComb (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (p : List ℤ) : Matrix V V ℚ :=
  ∑ k ∈ Finset.range p.length, ((p.getD k 0 : ℤ) : ℚ) • chebMat G d k

theorem chebComb_symm (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (p : List ℤ) :
    (chebComb G d p)ᵀ = chebComb G d p := by
  unfold chebComb
  rw [Matrix.transpose_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [transpose_smul, chebMat_symm]

theorem chebComb_mulVec_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : ∀ v : V, G.degree v = 3) (p : List ℤ) :
    (chebComb G 3 p).mulVec (fun _ => 1) = ((chebEval3 p : ℤ) : ℚ) • (fun _ => 1) := by
  unfold chebComb chebEval3
  rw [list_sum_range_eq_finset_sum]
  ext u
  simp only [Matrix.sum_mulVec, Finset.sum_apply, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul,
    chebMat_mulVec_one G (by decide) hreg, mul_one]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  norm_num

theorem chebComb_add (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (p q : List ℤ) :
    chebComb G d p + chebComb G d q = chebComb G d (chebAdd p q) := by
  unfold chebComb chebAdd
  have hlen : ((List.range (max p.length q.length)).map fun k => p.getD k 0 + q.getD k 0).length =
      max p.length q.length := by simp
  rw [hlen]
  have hp_ext : (∑ k ∈ Finset.range p.length, ((p.getD k 0 : ℤ) : ℚ) • chebMat G d k) =
      ∑ k ∈ Finset.range (max p.length q.length), ((p.getD k 0 : ℤ) : ℚ) • chebMat G d k := by
    refine Finset.sum_subset (Finset.range_mono (le_max_left _ _)) fun k _ hk => ?_
    simp only [Finset.mem_range, not_lt] at hk
    have h0 : p.getD k 0 = 0 := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]
    simp [h0]
  have hq_ext : (∑ k ∈ Finset.range q.length, ((q.getD k 0 : ℤ) : ℚ) • chebMat G d k) =
      ∑ k ∈ Finset.range (max p.length q.length), ((q.getD k 0 : ℤ) : ℚ) • chebMat G d k := by
    refine Finset.sum_subset (Finset.range_mono (le_max_right _ _)) fun k _ hk => ?_
    simp only [Finset.mem_range, not_lt] at hk
    have h0 : q.getD k 0 = 0 := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]
    simp [h0]
  rw [hp_ext, hq_ext, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hget : ((List.range (max p.length q.length)).map fun k => p.getD k 0 + q.getD k 0).getD k 0 =
      p.getD k 0 + q.getD k 0 := by
    simp only [Finset.mem_range] at hk
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
    simp
  rw [hget, Int.cast_add, add_smul]

theorem chebComb_mul_cubic (G : SimpleGraph V) [DecidableRel G.Adj] (p q : List ℤ) :
    chebComb G 3 p * chebComb G 3 q = chebComb G 3 (chebMul3 p q) := by
  unfold chebComb chebMul3
  have hlen : ((List.range (p.length + q.length)).map (chebMul3Coeff p q)).length =
      p.length + q.length := by simp
  rw [hlen]
  rw [Finset.sum_mul]
  have h_lhs : (∑ j ∈ Finset.range p.length,
      (((p.getD j 0 : ℤ) : ℚ) • chebMat G 3 j) *
        (∑ k ∈ Finset.range q.length, ((q.getD k 0 : ℤ) : ℚ) • chebMat G 3 k)) =
      ∑ j ∈ Finset.range p.length, ∑ k ∈ Finset.range q.length,
        (((p.getD j 0 * q.getD k 0 : ℤ) : ℚ) • chebMat G 3 (j + k) +
         ((p.getD j 0 * q.getD k 0 * ((2 : ℤ) ^ min j k) : ℤ) : ℚ) •
           chebMat G 3 (max j k - min j k)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, chebMat_mul_cubic, smul_add, smul_smul]
    push_cast
    ring_nf
  rw [h_lhs]
  have h_rhs : (∑ m ∈ Finset.range (p.length + q.length),
      ((((List.range (p.length + q.length)).map (chebMul3Coeff p q)).getD m 0 : ℤ) : ℚ) •
        chebMat G 3 m) =
      ∑ m ∈ Finset.range (p.length + q.length),
        ∑ j ∈ Finset.range p.length, ∑ k ∈ Finset.range q.length,
          ((if j + k = m then ((p.getD j 0 * q.getD k 0 : ℤ) : ℚ) • chebMat G 3 m else 0) +
           (if max j k - min j k = m then
              ((p.getD j 0 * q.getD k 0 * ((2 : ℤ) ^ min j k) : ℤ) : ℚ) • chebMat G 3 m
            else 0)) := by
    refine Finset.sum_congr rfl fun m hm => ?_
    simp only [Finset.mem_range] at hm
    have hget : ((List.range (p.length + q.length)).map (chebMul3Coeff p q)).getD m 0 =
        chebMul3Coeff p q m := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hm]
      simp
    rw [hget]
    unfold chebMul3Coeff
    rw [list_sum_range_eq_finset_sum]
    have hinner : (∑ j ∈ Finset.range p.length,
        ((List.range q.length).map fun k =>
          (if j + k = m then p.getD j 0 * q.getD k 0 else 0) +
          (if max j k - min j k = m then
             p.getD j 0 * q.getD k 0 * ((2 : ℤ) ^ min j k)
           else 0)).sum) =
        ∑ j ∈ Finset.range p.length, ∑ k ∈ Finset.range q.length,
          ((if j + k = m then p.getD j 0 * q.getD k 0 else 0) +
           (if max j k - min j k = m then
              p.getD j 0 * q.getD k 0 * ((2 : ℤ) ^ min j k)
            else 0)) := by
      refine Finset.sum_congr rfl fun j _ => list_sum_range_eq_finset_sum q.length _
    rw [hinner, Int.cast_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Int.cast_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Int.cast_add, add_smul]
    congr 1
    · split_ifs <;> simp
    · split_ifs <;> simp
  rw [h_rhs, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_range] at hj hk
  rw [Finset.sum_add_distrib]
  have h1 : j + k ∈ Finset.range (p.length + q.length) := by
    simp only [Finset.mem_range]; omega
  have h2 : max j k - min j k ∈ Finset.range (p.length + q.length) := by
    simp only [Finset.mem_range]; omega
  rw [Finset.sum_ite_eq (Finset.range (p.length + q.length)) (j + k), if_pos h1]
  rw [Finset.sum_ite_eq (Finset.range (p.length + q.length)) (max j k - min j k), if_pos h2]

/-- **Pure 2-Square Unconditional Trace Lower Bound (Zero Eigenvalues!)**:
For EVERY cubic graph `G` on `n > 0` vertices and ANY `p q : List ℤ`,
`(chebEval3 p)^2 + (chebEval3 q)^2 ≤ Tr(chebComb G 3 (p*p + q*q))`. -/
theorem two_square_cheb_trace_lb (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : ∀ v : V, G.degree v = 3) (hn : 0 < Fintype.card V) (p q : List ℤ) :
    (((chebEval3 p) ^ 2 + (chebEval3 q) ^ 2 : ℤ) : ℚ) ≤
      Matrix.trace (chebComb G 3 (chebAdd (chebMul3 p p) (chebMul3 q q))) := by
  rw [← chebComb_add, ← chebComb_mul_cubic, ← chebComb_mul_cubic, trace_add]
  have hp := symm_const_rowSum_sq_trace (chebComb G 3 p) ((chebEval3 p : ℤ) : ℚ)
    (chebComb_symm G 3 p) (chebComb_mulVec_one G hreg p) hn
  have hq := symm_const_rowSum_sq_trace (chebComb G 3 q) ((chebEval3 q : ℤ) : ℚ)
    (chebComb_symm G 3 q) (chebComb_mulVec_one G hreg q) hn
  have hnn_p : 0 ≤ ∑ u : V, ∑ v : V,
      ((chebComb G 3 p - (((chebEval3 p : ℤ) : ℚ) / (Fintype.card V : ℚ)) •
        Matrix.of (fun _ _ => (1 : ℚ))) u v) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hnn_q : 0 ≤ ∑ u : V, ∑ v : V,
      ((chebComb G 3 q - (((chebEval3 q : ℤ) : ℚ) / (Fintype.card V : ℚ)) •
        Matrix.of (fun _ _ => (1 : ℚ))) u v) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [hp.1, hq.1]
  push_cast
  linarith

/-! ## Pure `ℤ` Kernel-Computable Certificate Checker -/

/-- Decidable check whether `k` is a power of 2 ≥ 4 (for `k ≤ 64`). -/
def isPow2Small (k : ℕ) : Bool :=
  k == 4 || k == 8 || k == 16 || k == 32 || k == 64

theorem isPow2Small_spec {k : ℕ} (h : isPow2Small k = true) :
    ∃ m : ℕ, 2 ≤ m ∧ k = 2 ^ m := by
  unfold isPow2Small at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (((rfl | rfl) | rfl) | rfl) | rfl
  · exact ⟨2, by decide, by decide⟩
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨4, by decide, by decide⟩
  · exact ⟨5, by decide, by decide⟩
  · exact ⟨6, by decide, by decide⟩

/-- Lookup `α_k` in an association list `alpha : List (ℕ × ℕ)`. -/
def lookupAlpha (alpha : List (ℕ × ℕ)) (k : ℕ) : ℕ :=
  (alpha.filter fun kv => kv.1 == k).map Prod.snd |>.sum

private theorem lookupAlpha_zero_of_all_pos (alpha : List (ℕ × ℕ))
    (h : ∀ kv ∈ alpha, 1 ≤ kv.1) : lookupAlpha alpha 0 = 0 := by
  unfold lookupAlpha
  have hf : (alpha.filter fun kv => kv.1 == 0) = [] := by
    rw [List.filter_eq_nil_iff]
    intro kv hkv
    have := h kv hkv
    simp only [beq_iff_eq]
    omega
  rw [hf]
  rfl

/-- Pure integer certificate check for girth `g`, target length `L`, order bound `N`,
2-square Chebyshev factors `p, q : List ℤ`, and non-simple walk coefficients `alpha`. -/
def checkCert (g L N : ℕ) (p q : List ℤ) (alpha : List (ℕ × ℕ)) : Bool :=
  let S := chebAdd (chebMul3 p p) (chebMul3 q q)
  let lead := S.getD L 0
  let s3 := (chebEval3 p) ^ 2 + (chebEval3 q) ^ 2
  let evenSum := ((List.range S.length).map fun k =>
    if 1 ≤ k ∧ k % 2 = 0 then S.getD k 0 else 0).sum
  let negSlope := 2 * S.getD 0 0 - evenSum
  decide (1 ≤ L) &&
  decide (0 < lead) &&
  decide (L < S.length) &&
  ((List.range S.length).all fun k =>
    if L < k then decide (S.getD k 0 = 0) else true) &&
  ((List.range L).all fun k =>
    if k = 0 then true
    else if k < g then true
    else if isPow2Small k && decide (k < 2 * g) then true
    else decide (S.getD k 0 ≤ -((lookupAlpha alpha k : ℤ) * lead))) &&
  (alpha.all fun kv =>
    decide (1 ≤ kv.1) && decide (kv.1 < L)) &&
  (if decide (negSlope ≤ 0) then decide (0 < s3) else decide (negSlope * (N : ℤ) < s3))

/-- **Master Pure-2-Square Certificate Theorem**:
Whenever `checkCert g L N p q alpha = true`, EVERY power-free cubic graph `G` of girth `≥ g`
and order `0 < |V| ≤ N` satisfies
`∑ k ∈ Finset.range L, lookupAlpha alpha k * taillessCount G k < taillessCount G L`. -/
theorem cert_trace_surplus_of_two_square (G : SimpleGraph V) [DecidableRel G.Adj]
    {g L N : ℕ} {p q : List ℤ} {alpha : List (ℕ × ℕ)}
    (hreg : ∀ v : V, G.degree v = 3) (hn : 0 < Fintype.card V) (hle : Fintype.card V ≤ N)
    (hg : GirthAtLeast G g) (hnp : ¬ HasPower G)
    (hcert : checkCert g L N p q alpha = true) :
    (∑ k ∈ Finset.range L, lookupAlpha alpha k * taillessCount G k) < taillessCount G L := by
  set S := chebAdd (chebMul3 p p) (chebMul3 q q) with hS_def
  set lead := S.getD L 0 with hlead_def
  set s3 := (chebEval3 p) ^ 2 + (chebEval3 q) ^ 2 with hs3_def
  set evenSum := ((List.range S.length).map fun k =>
    if 1 ≤ k ∧ k % 2 = 0 then S.getD k 0 else 0).sum with heven_def
  set negSlope := 2 * S.getD 0 0 - evenSum with hns_def
  unfold checkCert at hcert
  rw [← hS_def, ← hlead_def, ← hs3_def, ← heven_def, ← hns_def] at hcert
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hcert
  rcases hcert with ⟨⟨⟨⟨⟨⟨hL1, hlead_pos⟩, hLlt⟩, hhi_zero⟩, hmid_le⟩, halpha_ok⟩, hord_check⟩
  have hlb := two_square_cheb_trace_lb G hreg hn p q
  rw [← hS_def, ← hs3_def] at hlb
  have htr_S : Matrix.trace (chebComb G 3 S) =
      ((negSlope : ℤ) : ℚ) * (Fintype.card V : ℚ) +
        ∑ k ∈ Finset.range S.length,
          if 1 ≤ k then ((S.getD k 0 : ℤ) : ℚ) * (taillessCount G k : ℚ) else 0 := by
    unfold chebComb
    rw [map_sum]
    have hsplit : (∑ k ∈ Finset.range S.length, Matrix.trace (((S.getD k 0 : ℤ) : ℚ) • chebMat G 3 k)) =
        ∑ k ∈ Finset.range S.length,
          ((if k = 0 then 2 * ((S.getD 0 0 : ℤ) : ℚ) * (Fintype.card V : ℚ) else 0) -
           (if 1 ≤ k ∧ k % 2 = 0 then ((S.getD k 0 : ℤ) : ℚ) * (Fintype.card V : ℚ) else 0) +
           (if 1 ≤ k then ((S.getD k 0 : ℤ) : ℚ) * (taillessCount G k : ℚ) else 0)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [trace_smul, smul_eq_mul]
      cases k with
      | zero =>
          simp [chebMat, trace_smul, Matrix.trace_one]
          ring
      | succ k' =>
          have htk := taillessCount_eq_chebMat_trace_all G (d := 3) (by decide) hreg (k := k' + 1) (by omega)
          have h32 : ((3 - 2 : ℕ) : ℚ) = 1 := by norm_num
          rw [h32, one_mul] at htk
          by_cases hev : (k' + 1) % 2 = 0
          · rw [if_pos hev] at htk
            simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.one_le_iff_ne_zero, hev, and_self]
            have : Matrix.trace (chebMat G 3 (k' + 1)) = (taillessCount G (k' + 1) : ℚ) - (Fintype.card V : ℚ) := by linarith
            rw [this]; ring
          · rw [if_neg hev, add_zero] at htk
            simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.one_le_iff_ne_zero, hev, and_false, sub_zero, zero_add]
            rw [← htk]
    rw [hsplit, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    congr 1
    have h0mem : 0 ∈ Finset.range S.length := by simp only [Finset.mem_range]; omega
    rw [Finset.sum_ite_eq' (Finset.range S.length) 0, if_pos h0mem]
    rw [hns_def, heven_def, list_sum_range_eq_finset_sum]
    push_cast
    rw [sub_mul, Finset.sum_mul]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs <;> simp
  have hsum_le : (∑ k ∈ Finset.range S.length,
        if 1 ≤ k then ((S.getD k 0 : ℤ) : ℚ) * (taillessCount G k : ℚ) else 0) ≤
      ((lead : ℤ) : ℚ) * (taillessCount G L : ℚ) -
        ((lead : ℤ) : ℚ) * (∑ k ∈ Finset.range L, (lookupAlpha alpha k : ℚ) * (taillessCount G k : ℚ)) := by
    have hsplit_L : (∑ k ∈ Finset.range S.length,
          if 1 ≤ k then ((S.getD k 0 : ℤ) : ℚ) * (taillessCount G k : ℚ) else 0) =
        (∑ k ∈ Finset.range L,
          if 1 ≤ k then ((S.getD k 0 : ℤ) : ℚ) * (taillessCount G k : ℚ) else 0) +
        ((lead : ℤ) : ℚ) * (taillessCount G L : ℚ) := by
      have hsub : Finset.range (L + 1) ⊆ Finset.range S.length := Finset.range_mono (by omega)
      have hhi : (∑ k ∈ Finset.range S.length,
            if 1 ≤ k then ((S.getD k 0 : ℤ) : ℚ) * (taillessCount G k : ℚ) else 0) =
          ∑ k ∈ Finset.range (L + 1),
            if 1 ≤ k then ((S.getD k 0 : ℤ) : ℚ) * (taillessCount G k : ℚ) else 0 := by
        refine (Finset.sum_subset hsub ?_).symm
        intro k hk hk'
        simp only [Finset.mem_range] at hk hk'
        have hgt : L < k := by omega
        have hkz := hhi_zero k hk
        simp only [hgt, ↓reduceIte, decide_eq_true_eq] at hkz
        simp [hkz]
      rw [hhi, Finset.sum_range_succ, if_pos hL1, hlead_def]
    rw [hsplit_L]
    have hlt_le : (∑ k ∈ Finset.range L,
          if 1 ≤ k then ((S.getD k 0 : ℤ) : ℚ) * (taillessCount G k : ℚ) else 0) ≤
        -((lead : ℤ) : ℚ) * (∑ k ∈ Finset.range L, (lookupAlpha alpha k : ℚ) * (taillessCount G k : ℚ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k hk => ?_
      simp only [Finset.mem_range] at hk
      by_cases hk0 : k = 0
      · subst hk0
        have ha0 : lookupAlpha alpha 0 = 0 :=
          lookupAlpha_zero_of_all_pos alpha fun kv hkv => (halpha_ok kv hkv).1
        simp [ha0]
      · simp only [show 1 ≤ k by omega, ↓reduceIte]
        by_cases hkg : k < g
        · have h0 := taillessCount_eq_zero_of_lt_girth G hg (by omega) hkg
          simp [h0]
        · by_cases hp2 : isPow2Small k = true ∧ k < 2 * g
          · obtain ⟨m, hm, rfl⟩ := isPow2Small_spec hp2.1
            have h0 := taillessCount_pow2_eq_zero G hg hnp hm hp2.2
            simp [h0]
          · have hck := hmid_le k hk
            have hnotp2 : (isPow2Small k && decide (k < 2 * g)) = false := by
              cases h1 : isPow2Small k <;> simp [h1] at hp2 ⊢
              exact Nat.le_of_not_lt hp2
            simp only [hk0, ↓reduceIte, hkg, hnotp2, Bool.false_eq_true, decide_eq_true_eq] at hck
            have hck_q : ((S.getD k 0 : ℤ) : ℚ) ≤ -(((lookupAlpha alpha k : ℕ) : ℚ) * ((lead : ℤ) : ℚ)) := by
              exact_mod_cast hck
            have hnn : (0 : ℚ) ≤ (taillessCount G k : ℚ) := Nat.cast_nonneg _
            have hmul := mul_le_mul_of_nonneg_right hck_q hnn
            linarith
    linarith
  have hord_q : ((negSlope : ℤ) : ℚ) * (Fintype.card V : ℚ) < ((s3 : ℤ) : ℚ) := by
    by_cases hns_le : negSlope ≤ 0
    · simp only [hns_le, decide_true, ↓reduceIte, decide_eq_true_eq] at hord_check
      have h1 : ((negSlope : ℤ) : ℚ) ≤ 0 := by exact_mod_cast hns_le
      have h2 : (0 : ℚ) < ((s3 : ℤ) : ℚ) := by exact_mod_cast hord_check
      have h3 : ((negSlope : ℤ) : ℚ) * (Fintype.card V : ℚ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg h1 (Nat.cast_nonneg _)
      linarith
    · simp only [hns_le, decide_false, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at hord_check
      have hns_pos : (0 : ℚ) < ((negSlope : ℤ) : ℚ) := by exact_mod_cast (show 0 < negSlope by omega)
      have hle_q : (Fintype.card V : ℚ) ≤ (N : ℚ) := by exact_mod_cast hle
      have hlt_q : ((negSlope : ℤ) : ℚ) * (N : ℚ) < ((s3 : ℤ) : ℚ) := by exact_mod_cast hord_check
      nlinarith
  have hlead_q : (0 : ℚ) < ((lead : ℤ) : ℚ) := by exact_mod_cast hlead_pos
  have hdiff_pos : (0 : ℚ) < ((lead : ℤ) : ℚ) *
      ((taillessCount G L : ℚ) - ∑ k ∈ Finset.range L, (lookupAlpha alpha k : ℚ) * (taillessCount G k : ℚ)) := by
    linarith
  have hlt_q : (∑ k ∈ Finset.range L, (lookupAlpha alpha k : ℚ) * (taillessCount G k : ℚ)) <
      (taillessCount G L : ℚ) := by
    have := pos_of_mul_pos_right hdiff_pos hlead_q.le
    linarith
  exact_mod_cast hlt_q

end ChebyshevListAlgebra

end E64Wave8Agent2
