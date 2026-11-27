import Mathlib

/-!
Erdős #25: machine-check the exact activation, weighted finite-block
inequality and one-block closure reduction. The weights may be the normalized
harmonic weights 1/(n H_X). Finite-rulePrefix convergence and finite Haar footprint
monotonicity are explicit hypotheses (established in the ordinary paper);
the uniform conditioned bound is still an UNPROVED hypothesis. This does
not assert Erdős #25.
-/
namespace Erdos25Block
open scoped BigOperators

def rulePrefix (D : ℕ → Prop) (Y : ℕ) : ℕ → Prop :=
  fun q => D q ∧ q ≤ Y

def block (D : ℕ → Prop) (Y X : ℕ) : ℕ → Prop :=
  fun q => D q ∧ Y < q ∧ q ≤ X

def active (D : ℕ → Prop) (a : ℕ → ℕ) (n : ℕ) : Prop :=
  ∃ q, D q ∧ 0 < q ∧ q ≤ n ∧ n % q = a q

def full (D : ℕ → Prop) (a : ℕ → ℕ) (n : ℕ) : Prop :=
  ∃ q, D q ∧ 0 < q ∧ n % q = a q

def conditioned (D : ℕ → Prop) (a : ℕ → ℕ) (P Y X n : ℕ) : Prop :=
  active (block D Y X) a n ∧ ¬ full (rulePrefix D P) a n

/-- All old rules are active at a new hit. The new witness cannot
come from the old rulePrefix. No change of residue or activation threshold. -/
theorem late_hit_in_block
    (D : ℕ → Prop) (a : ℕ → ℕ) (P Y X n : ℕ)
    (hPY : P ≤ Y) (hnX : n ≤ X)
    (hit : active D a n) (notOld : ¬ active (rulePrefix D Y) a n) :
    conditioned D a P Y X n := by
  obtain ⟨q, hq, hqpos, hqn, ha⟩ := hit
  have hYq : Y < q := by
    by_contra! hqY
    exact notOld ⟨q, ⟨hq, hqY⟩, hqpos, hqn, ha⟩
  refine ⟨⟨q, ⟨hq, hYq, hqn.trans hnX⟩, hqpos, hqn, ha⟩, ?_⟩
  intro hold
  obtain ⟨r, ⟨hr, hrP⟩, hrpos, hra⟩ := hold
  have hrY : r ≤ Y := hrP.trans hPY
  exact notOld ⟨r, ⟨hr, hrY⟩, hrpos, by omega, hra⟩

noncomputable def mass (w : ℕ → ℕ → ℝ) (X : ℕ) (A : ℕ → Prop) : ℝ := by
  classical
  exact ∑ n ∈ Finset.Icc 1 X, if A n then w X n else 0

/-- Exact inequality for arbitrary nonnegative weights on [1,X].
In particular it applies to normalized harmonic weights. -/
theorem weighted_block_inequality
    (D : ℕ → Prop) (a : ℕ → ℕ) (w : ℕ → ℕ → ℝ)
    (hw : ∀ X n, 0 ≤ w X n) (P Y X : ℕ) (hPY : P ≤ Y) :
    mass w X (active D a) ≤ mass w X (active (rulePrefix D Y) a) +
      mass w X (conditioned D a P Y X) := by
  classical
  unfold mass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro n hn
  have hnX : n ≤ X := (Finset.mem_Icc.mp hn).2
  by_cases hD : active D a n
  · by_cases hOld : active (rulePrefix D Y) a n
    · by_cases hC : conditioned D a P Y X n
      · simp only [if_pos hD, if_pos hOld, if_pos hC]
        linarith [hw X n]
      · simp [hD, hOld, hC]
    · have hC := late_hit_in_block D a P Y X n hPY hnX hD hOld
      simp [hD, hOld, hC]
  · by_cases hOld : active (rulePrefix D Y) a n <;>
      by_cases hC : conditioned D a P Y X n <;>
      simp [hD, hOld, hC, hw X n, add_nonneg (hw X n) (hw X n)]

/-- Extract a single bad block above ANY prescribed old cutoff.
Only the two actual analytic premises (arbitrarily late peaks and convergence
of each fixed rulePrefix) are assumed. This avoids a recursion across blocks. -/
theorem one_block_from_gap
    (D : ℕ → Prop) (a : ℕ → ℕ) (w : ℕ → ℕ → ℝ)
    (hw : ∀ X n, 0 ≤ w X n) (β Δ η : ℝ) (hη : 0 < η)
    (peaks : ∀ N : ℕ, ∃ X : ℕ, N ≤ X ∧ β + Δ ≤ mass w X (active D a))
    (prefixUpper : ∀ Y : ℕ, ∀ e : ℝ, 0 < e →
      ∃ N : ℕ, ∀ X : ℕ, N ≤ X → mass w X (active (rulePrefix D Y) a) ≤ β + e)
    (P Y : ℕ) (hPY : P ≤ Y) :
    ∃ X : ℕ, Y < X ∧ Δ - η ≤ mass w X (conditioned D a P Y X) := by
  obtain ⟨N, hN⟩ := prefixUpper Y η hη
  obtain ⟨X, hX, peak⟩ := peaks (max N (Y+1))
  have hNX : N ≤ X := (le_max_left N (Y+1)).trans hX
  have hYX : Y < X := by
    have hh := (le_max_right N (Y+1)).trans hX
    omega
  have hold := hN X hNX
  have hsplit := weighted_block_inequality D a w hw P Y X hPY
  exact ⟨X, hYX, by linarith⟩

/-- Pure arithmetic form of the Haar increment bound. A monotone footprint
on subsets of the rules is enough. Every block is a subfamily of D. -/
theorem increment_bound
    (D : ℕ → Prop) (footprint : (ℕ → Prop) → ℝ)
    (mono : ∀ U V : ℕ → Prop, (∀ q, U q → V q) → footprint U ≤ footprint V)
    (P Y X : ℕ) :
    footprint (fun q => rulePrefix D P q ∨ block D Y X q) - footprint (rulePrefix D P)
      ≤ footprint D - footprint (rulePrefix D P) := by
  have h := mono (fun q => rulePrefix D P q ∨ block D Y X q) D (by
    intro q hq
    rcases hq with hp | hb
    · exact hp.1
    · exact hb.1)
  linarith

/-- The single-block closure gate, in epsilon-delta form.
The only NEW analytic premise is gate. Its epsilon must be uniform in the
old rulePrefix, but its separation threshold Q may depend on that rulePrefix.
This theorem rules out any positive gap under that premise. -/
theorem uniform_gate_excludes_gap
    (D : ℕ → Prop) (a : ℕ → ℕ) (w : ℕ → ℕ → ℝ)
    (hw : ∀ X n, 0 ≤ w X n)
    (footprint : (ℕ → Prop) → ℝ)
    (mono : ∀ U V : ℕ → Prop, (∀ q, U q → V q) → footprint U ≤ footprint V)
    (β Δ : ℝ) (hβ : footprint D = β) (hΔ : 0 < Δ)
    (peaks : ∀ N : ℕ, ∃ X : ℕ, N ≤ X ∧ β + Δ ≤ mass w X (active D a))
    (prefixUpper : ∀ Y : ℕ, ∀ e : ℝ, 0 < e →
      ∃ N : ℕ, ∀ X : ℕ, N ≤ X → mass w X (active (rulePrefix D Y) a) ≤ β + e)
    (approx : ∀ d : ℝ, 0 < d → ∃ P : ℕ, β - footprint (rulePrefix D P) ≤ d)
    (gate : ∀ e : ℝ, 0 < e → ∃ d : ℝ, 0 < d ∧
      ∀ P : ℕ, ∃ Q : ℕ, ∀ Y X : ℕ, Q ≤ Y → P ≤ Y → Y < X →
      footprint (fun q => rulePrefix D P q ∨ block D Y X q) - footprint (rulePrefix D P) ≤ d →
      mass w X (conditioned D a P Y X) ≤ e) :
    False := by
  obtain ⟨d, hd, hgate⟩ := gate (Δ / 3) (by linarith)
  obtain ⟨P, hP⟩ := approx d hd
  obtain ⟨Q, hQ⟩ := hgate P
  let Y := max P Q
  have hPY : P ≤ Y := le_max_left P Q
  have hQY : Q ≤ Y := le_max_right P Q
  obtain ⟨X, hYX, hmass⟩ := one_block_from_gap D a w hw β Δ (Δ / 3)
    (by linarith) peaks prefixUpper P Y hPY
  have hinc := increment_bound D footprint mono P Y X
  have hsmall : footprint (fun q => rulePrefix D P q ∨ block D Y X q) -
      footprint (rulePrefix D P) ≤ d := by linarith
  have hbound := hQ Y X hQY hPY hYX hsmall
  linarith

/-- A finite weighted injective endpoint transport bound, with explicit
dilation constant and no assumption that a transport actually exists. -/
theorem injective_transport
    (V : Finset ℕ) (m : ℕ → ℕ) (C : ℝ)
    (hV : ∀ n ∈ V, 0 < n)
    (hm : ∀ n ∈ V, 0 < m n)
    (hd : ∀ n ∈ V, (m n : ℝ) ≤ C * (n : ℝ))
    (hinj : ∀ n ∈ V, ∀ r ∈ V, m n = m r → n = r) :
    (∑ n ∈ V, (1 : ℝ) / (n : ℝ)) ≤ C * ∑ r ∈ V.image m, (1 : ℝ) / (r : ℝ) := by
  calc
    (∑ n ∈ V, (1 : ℝ) / (n : ℝ)) ≤ ∑ n ∈ V, C * ((1 : ℝ) / (m n : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast hV n hn
      have hmpos : 0 < (m n : ℝ) := by exact_mod_cast hm n hn
      rw [mul_one_div]
      exact (div_le_div_iff₀ hnpos hmpos).mpr (by simpa [mul_comm] using hd n hn)
    _ = C * ∑ r ∈ V.image m, (1 : ℝ) / (r : ℝ) := by
      rw [← Finset.mul_sum]
      congr 1
      exact (Finset.sum_image (f := fun r : ℕ => (1 : ℝ) / (r : ℝ)) hinj).symm

#print axioms late_hit_in_block
#print axioms weighted_block_inequality
#print axioms one_block_from_gap
#print axioms increment_bound
#print axioms uniform_gate_excludes_gap
#print axioms injective_transport
end Erdos25Block
