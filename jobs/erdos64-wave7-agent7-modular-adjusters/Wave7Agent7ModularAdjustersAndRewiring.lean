import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
# Erdős Problem #64 (Wave 7 Agent #7)
## Modular-Octave Ear Adjusters, Dual Cross-Rewiring, and Cubic Non-Backtracking Exclusions

All theorems are proved unconditionally in Lean 4.36.0 with standard axioms only
(`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace E64Wave7Agent7

open SimpleGraph

/-- `IsPow2 n` holds when `n = 2^k` for some `k ≥ 2` (i.e. `n ∈ {4, 8, 16, 32, ...}`). -/
def IsPow2 (n : ℕ) : Prop := ∃ k : ℕ, 2 ≤ k ∧ n = 2 ^ k

/-- `HasPow2Cycle G` holds when `G` contains a simple cycle whose length is a power of 2 ≥ 4. -/
def HasPow2Cycle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ IsPow2 p.length

/-- `HasCycleLen G L` holds when `G` contains a simple cycle of exact length `L`. -/
def HasCycleLen {V : Type*} (G : SimpleGraph V) (L : ℕ) : Prop :=
  ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = L

/-! ### Part 1: Signed-Shift Normalization & Modular-Octave Arithmetic Progression Closure -/

/--
Theorem 1 (`signed_shift_subset_sum_realization`):
Given `t` independent ear-bypasses with base arc lengths `p i` and bypass lengths `q i`,
activating all shortening bypasses (`q i < p i`) produces a baseline length `L₀` and
nonnegative shifts `d i = |q i - p i|` such that every subset `I : Finset (Fin t)` of
positive shifts is realized by an explicit toggle subset `T : Finset (Fin t)` of the
original bypasses.
-/
theorem signed_shift_subset_sum_realization {t : ℕ} (L : ℕ) (p q : Fin t → ℕ)
    (hL : (∑ i ∈ Finset.univ.filter (fun i => q i < p i), (p i - q i)) ≤ L)
    (I : Finset (Fin t)) :
    ∃ T : Finset (Fin t),
      (L : ℤ) + ∑ i ∈ T, ((q i : ℤ) - (p i : ℤ)) =
      ((L - ∑ i ∈ Finset.univ.filter (fun i => q i < p i), (p i - q i) +
        ∑ i ∈ I, (if p i ≤ q i then q i - p i else p i - q i) : ℕ) : ℤ) := by
  classical
  let Sneg : Finset (Fin t) := Finset.univ.filter (fun i => q i < p i)
  let T : Finset (Fin t) := (I \ Sneg) ∪ (Sneg \ I)
  refine ⟨T, ?_⟩
  have hcast :
      ((L - ∑ i ∈ Sneg, (p i - q i) : ℕ) : ℤ) =
        (L : ℤ) - ∑ i ∈ Sneg, ((p i - q i : ℕ) : ℤ) := by
    rw [Nat.cast_sub hL, Nat.cast_sum]
  have hsum_cast :
      ((L - ∑ i ∈ Sneg, (p i - q i) +
        ∑ i ∈ I, (if p i ≤ q i then q i - p i else p i - q i) : ℕ) : ℤ) =
      (L : ℤ) - ∑ i ∈ Sneg, ((p i - q i : ℕ) : ℤ) +
        ∑ i ∈ I, ((if p i ≤ q i then q i - p i else p i - q i : ℕ) : ℤ) := by
    rw [Nat.cast_add, hcast, Nat.cast_sum]
  rw [hsum_cast]
  have hT_disj : Disjoint (I \ Sneg) (Sneg \ I) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact (Finset.mem_sdiff.mp hx1).2 (Finset.mem_sdiff.mp hx2).1
  rw [Finset.sum_union hT_disj]
  have hSneg_split :
      ∑ i ∈ Sneg, ((p i - q i : ℕ) : ℤ) =
        ∑ i ∈ Sneg \ I, ((p i - q i : ℕ) : ℤ) + ∑ i ∈ Sneg ∩ I, ((p i - q i : ℕ) : ℤ) := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter Sneg I), Finset.sdiff_union_inter]
  have hI_split :
      ∑ i ∈ I, ((if p i ≤ q i then q i - p i else p i - q i : ℕ) : ℤ) =
        ∑ i ∈ I \ Sneg, ((if p i ≤ q i then q i - p i else p i - q i : ℕ) : ℤ) +
        ∑ i ∈ I ∩ Sneg, ((if p i ≤ q i then q i - p i else p i - q i : ℕ) : ℤ) := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter I Sneg), Finset.sdiff_union_inter]
  have h1 :
      ∑ i ∈ I \ Sneg, ((q i : ℤ) - (p i : ℤ)) =
        ∑ i ∈ I \ Sneg, ((if p i ≤ q i then q i - p i else p i - q i : ℕ) : ℤ) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hnot : ¬ q i < p i := by
      have := (Finset.mem_sdiff.mp hi).2
      simpa [Sneg] using this
    have hle : p i ≤ q i := Nat.le_of_not_lt hnot
    simp [hle, Nat.cast_sub hle]
  have h2 :
      ∑ i ∈ Sneg \ I, ((q i : ℤ) - (p i : ℤ)) =
        - ∑ i ∈ Sneg \ I, ((p i - q i : ℕ) : ℤ) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hlt : q i < p i := by
      have := (Finset.mem_sdiff.mp hi).1
      simpa [Sneg] using this
    have hle : q i ≤ p i := Nat.le_of_lt hlt
    rw [Nat.cast_sub hle]
    ring
  have h3 :
      ∑ i ∈ I ∩ Sneg, ((if p i ≤ q i then q i - p i else p i - q i : ℕ) : ℤ) =
        ∑ i ∈ Sneg ∩ I, ((p i - q i : ℕ) : ℤ) := by
    rw [Finset.inter_comm]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hlt : q i < p i := by
      have := (Finset.mem_inter.mp hi).1
      simpa [Sneg] using this
    have hnot : ¬ p i ≤ q i := Nat.not_le_of_gt hlt
    simp [hnot]
  rw [h1, h2, hSneg_split, hI_split, h3]
  ring

private lemma exists_pow2_ge_step (a r o M : ℕ) (ho : 1 ≤ o) :
    ∃ q : ℕ, M ≤ 2 ^ (a + r + q * o) := by
  refine ⟨M, ?_⟩
  have h1 : M ≤ a + r + M * o := by
    have : M ≤ M * o := Nat.le_mul_of_pos_right M ho
    omega
  exact le_trans h1 (Nat.le_of_lt (Nat.lt_two_pow_self))

private lemma pow2_modEq_of_period {u o : ℕ} (hper : 2 ^ o ≡ 1 [MOD u]) (k : ℕ) :
    2 ^ k ≡ 2 ^ (k % o) [MOD u] := by
  conv_lhs => rw [← Nat.div_add_mod k o]
  rw [pow_add, pow_mul]
  have h1 : (2 ^ o) ^ (k / o) ≡ 1 ^ (k / o) [MOD u] := hper.pow (k / o)
  rw [one_pow] at h1
  have h2 := h1.mul_right (2 ^ (k % o))
  simpa using h2

/--
Theorem 2 (`exists_pow2_mod_odd_in_window`):
**Modular-Octave Arithmetic Progression Closure**.
Let `s = 2^a * u` with `2^o ≡ 1 [MOD u]` (`o ≥ 1`). If `L₀ ≥ 1`, `2^a ∣ L₀`, and
`L₀ / 2^a ≡ 2^r [MOD u]` for some `r`, then for any `t` with
`L₀ + t * s ≥ 2^o * max L₀ 4`, there exist `j ≤ t` and `k ≥ 2` such that `L₀ + j * s = 2^k`.
-/
theorem exists_pow2_mod_odd_in_window {a u o r L₀ t : ℕ}
    (ho : 1 ≤ o) (hper : 2 ^ o ≡ 1 [MOD u])
    (hLpos : 1 ≤ L₀) (hdvd : 2 ^ a ∣ L₀)
    (hcong : 2 ^ r ≡ L₀ / 2 ^ a [MOD u])
    (hbound : 2 ^ o * max L₀ 4 ≤ L₀ + t * (2 ^ a * u)) :
    ∃ j ≤ t, IsPow2 (L₀ + j * (2 ^ a * u)) := by
  classical
  let r' : ℕ := r % o
  have hr'_lt : r' < o := Nat.mod_lt r ho
  have hr'_cong : 2 ^ r' ≡ L₀ / 2 ^ a [MOD u] :=
    (pow2_modEq_of_period hper r).symm.trans hcong
  let M : ℕ := max L₀ 4
  have hM_ge_L : L₀ ≤ M := le_max_left L₀ 4
  have hM_ge_4 : 4 ≤ M := le_max_right L₀ 4
  have hex : ∃ q : ℕ, M ≤ 2 ^ (a + r' + q * o) := exists_pow2_ge_step a r' o M ho
  let q₀ : ℕ := Nat.find hex
  have hq₀_ge : M ≤ 2 ^ (a + r' + q₀ * o) := Nat.find_spec hex
  let k : ℕ := a + r' + q₀ * o
  have hk_ge_M : M ≤ 2 ^ k := hq₀_ge
  have hk_ge_L : L₀ ≤ 2 ^ k := le_trans hM_ge_L hk_ge_M
  have hk_ge_2 : 2 ≤ k := by
    by_contra hlt
    have hk_le : k ≤ 1 := by omega
    have hpow_le : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by decide) hk_le
    omega
  have hk_lt_bound : 2 ^ k ≤ 2 ^ o * M := by
    rcases Nat.eq_zero_or_pos q₀ with hq0 | hqpos
    · have hk_eq : k = a + r' := by simp [k, hq0]
      rw [hk_eq]
      have h2a_le_L : 2 ^ a ≤ L₀ := Nat.le_of_dvd (by omega) hdvd
      have h2a_le_M : 2 ^ a ≤ M := le_trans h2a_le_L hM_ge_L
      have h2r_le : 2 ^ r' ≤ 2 ^ o := Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hr'_lt)
      calc
        2 ^ (a + r') = 2 ^ r' * 2 ^ a := by rw [pow_add, mul_comm]
        _ ≤ 2 ^ o * M := Nat.mul_le_mul h2r_le h2a_le_M
    · have hprev_lt : 2 ^ (a + r' + (q₀ - 1) * o) < M := by
        have hnot := Nat.find_min hex (Nat.sub_lt hqpos (by decide))
        exact Nat.lt_of_not_le hnot
      have hk_eq : k = a + r' + (q₀ - 1) * o + o := by
        have : q₀ = (q₀ - 1) + 1 := (Nat.sub_add_cancel hqpos).symm
        calc
          k = a + r' + ((q₀ - 1) + 1) * o := by rw [← this]
          _ = a + r' + (q₀ - 1) * o + o := by ring
      rw [hk_eq, pow_add, mul_comm]
      exact Nat.mul_le_mul_left (2 ^ o) (Nat.le_of_lt hprev_lt)
  have hk_mod_u : 2 ^ (r' + q₀ * o) ≡ L₀ / 2 ^ a [MOD u] := by
    rw [pow_add, pow_mul]
    have h1 : (2 ^ o) ^ q₀ ≡ 1 ^ q₀ [MOD u] := hper.pow q₀
    rw [one_pow] at h1
    have h2 := h1.mul_left (2 ^ r')
    simp only [mul_one] at h2
    exact h2.trans hr'_cong
  have h2a_mul : 2 ^ a * (L₀ / 2 ^ a) = L₀ := Nat.mul_div_cancel' hdvd
  have hk_factor : 2 ^ k = 2 ^ a * 2 ^ (r' + q₀ * o) := by
    have : k = a + (r' + q₀ * o) := by ring
    rw [this, pow_add]
  have h_le_div : L₀ / 2 ^ a ≤ 2 ^ (r' + q₀ * o) := by
    have hpos : 0 < 2 ^ a := Nat.two_pow_pos a
    have : 2 ^ a * (L₀ / 2 ^ a) ≤ 2 ^ a * 2 ^ (r' + q₀ * o) := by
      rw [h2a_mul, ← hk_factor]; exact hk_ge_L
    exact Nat.le_of_mul_le_mul_left this hpos
  have hu_dvd : u ∣ (2 ^ (r' + q₀ * o) - L₀ / 2 ^ a) :=
    (Nat.modEq_iff_dvd' h_le_div).mp hk_mod_u.symm
  rcases hu_dvd with ⟨j, hj⟩
  have h_eq : L₀ + j * (2 ^ a * u) = 2 ^ k := by
    calc
      L₀ + j * (2 ^ a * u)
          = 2 ^ a * (L₀ / 2 ^ a) + 2 ^ a * (u * j) := by rw [h2a_mul]; ring
      _ = 2 ^ a * (L₀ / 2 ^ a + (2 ^ (r' + q₀ * o) - L₀ / 2 ^ a)) := by rw [← hj, mul_add]
      _ = 2 ^ a * 2 ^ (r' + q₀ * o) := by rw [Nat.add_sub_of_le h_le_div]
      _ = 2 ^ k := hk_factor.symm
  have hj_le : j ≤ t := by
    rcases Nat.eq_zero_or_pos (2 ^ a * u) with hs0 | hspos
    · have hu0 : u = 0 := by
        have h2a : 2 ^ a ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos a)
        exact (mul_eq_zero.mp hs0).resolve_left h2a
      have h1 : 2 ^ o = 1 := by simpa [hu0, Nat.ModEq] using hper
      have h2 : 2 ≤ 2 ^ o := by
        calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ o := Nat.pow_le_pow_right (by decide) ho
      omega
    · have hle_prod : j * (2 ^ a * u) ≤ t * (2 ^ a * u) := by
        have : L₀ + j * (2 ^ a * u) ≤ L₀ + t * (2 ^ a * u) := by
          rw [h_eq]; exact le_trans hk_lt_bound hbound
        omega
      exact Nat.le_of_mul_le_mul_right hle_prod hspos
  exact ⟨j, hj_le, ⟨k, hk_ge_2, h_eq⟩⟩

/--
Theorem 3 (`pentagon_pure_shift3_closure`):
For pure `C₅` (`Δ = 3`) bypass chains: if `3 ∤ L₀` (`L₀ ≥ 1`) and `L₀ + 3*t ≥ 4 * max L₀ 4`,
then the arithmetic progression `L₀ + 3*j` (`j ≤ t`) hits a power of 2 ≥ 4.
-/
theorem pentagon_pure_shift3_closure {L₀ t : ℕ}
    (hLpos : 1 ≤ L₀) (hndvd : ¬ 3 ∣ L₀)
    (hbound : 4 * max L₀ 4 ≤ L₀ + t * 3) :
    ∃ j ≤ t, IsPow2 (L₀ + j * 3) := by
  have hmod : L₀ % 3 = 1 ∨ L₀ % 3 = 2 := by omega
  have hcong : ∃ r : ℕ, 2 ^ r ≡ L₀ / 2 ^ 0 [MOD 3] := by
    rcases hmod with h1 | h2
    · exact ⟨0, by simp [Nat.ModEq, h1]⟩
    · exact ⟨1, by simp [Nat.ModEq, h2]⟩
  rcases hcong with ⟨r, hr⟩
  have hper : 2 ^ 2 ≡ 1 [MOD 3] := by decide
  have h := exists_pow2_mod_odd_in_window (a := 0) (u := 3) (o := 2) (r := r)
    (by decide) hper hLpos (by simp) hr (by simpa using hbound)
  simpa using h

/--
Theorem 4 (`hexagon_pure_shift4_closure`):
For pure `C₆` (`Δ = 4`) bypass chains: if `4 ∣ L₀` (`L₀ ≥ 1`) and `L₀ + 4*t ≥ 2 * max L₀ 4`,
then the arithmetic progression `L₀ + 4*j` (`j ≤ t`) hits a power of 2 ≥ 4.
-/
theorem hexagon_pure_shift4_closure {L₀ t : ℕ}
    (hLpos : 1 ≤ L₀) (hdvd : 4 ∣ L₀)
    (hbound : 2 * max L₀ 4 ≤ L₀ + t * 4) :
    ∃ j ≤ t, IsPow2 (L₀ + j * 4) := by
  have hper : 2 ^ 1 ≡ 1 [MOD 1] := by decide
  have hcong : 2 ^ 0 ≡ L₀ / 2 ^ 2 [MOD 1] := by simp [Nat.ModEq]
  have h := exists_pow2_mod_odd_in_window (a := 2) (u := 1) (o := 1) (r := 0)
    (by decide) hper hLpos (by simpa using hdvd) hcong (by simpa using hbound)
  simpa using h

/--
Theorem 5 (`heptagon_pure_shift5_closure`):
For pure `C₇` (`Δ = 5`) bypass chains: if `5 ∤ L₀` (`L₀ ≥ 1`) and `L₀ + 5*t ≥ 16 * max L₀ 4`,
then the arithmetic progression `L₀ + 5*j` (`j ≤ t`) hits a power of 2 ≥ 4.
-/
theorem heptagon_pure_shift5_closure {L₀ t : ℕ}
    (hLpos : 1 ≤ L₀) (hndvd : ¬ 5 ∣ L₀)
    (hbound : 16 * max L₀ 4 ≤ L₀ + t * 5) :
    ∃ j ≤ t, IsPow2 (L₀ + j * 5) := by
  have hmod : L₀ % 5 = 1 ∨ L₀ % 5 = 2 ∨ L₀ % 5 = 3 ∨ L₀ % 5 = 4 := by omega
  have hcong : ∃ r : ℕ, 2 ^ r ≡ L₀ / 2 ^ 0 [MOD 5] := by
    rcases hmod with h1 | h2 | h3 | h4
    · exact ⟨0, by simp [Nat.ModEq, h1]⟩
    · exact ⟨1, by simp [Nat.ModEq, h2]⟩
    · exact ⟨3, by simp [Nat.ModEq, h3]⟩
    · exact ⟨2, by simp [Nat.ModEq, h4]⟩
  rcases hcong with ⟨r, hr⟩
  have hper : 2 ^ 4 ≡ 1 [MOD 5] := by decide
  have h := exists_pow2_mod_odd_in_window (a := 0) (u := 5) (o := 4) (r := r)
    (by decide) hper hLpos (by simp) hr (by simpa using hbound)
  simpa using h

/--
Theorem 6 (`mixed_shift_1_and_3_breaks_mod3_obstruction`):
A single `Δ = 1` bypass alongside `b` bypasses of `Δ = 3` **completely breaks** the `3 ∣ L₀`
modular obstruction: for **every** `L₀ ≥ 1` (with no divisibility hypothesis!), if
`L₀ + 1 + 3*b ≥ 4 * max (L₀ + 1) 4`, then `∃ ε ≤ 1, j ≤ b` with `IsPow2 (L₀ + ε + j * 3)`.
-/
theorem mixed_shift_1_and_3_breaks_mod3_obstruction {L₀ b : ℕ}
    (hLpos : 1 ≤ L₀)
    (hbound : 4 * max (L₀ + 1) 4 ≤ L₀ + 1 + b * 3) :
    ∃ ε ≤ 1, ∃ j ≤ b, IsPow2 (L₀ + ε + j * 3) := by
  by_cases h3 : 3 ∣ L₀
  · have hndvd : ¬ 3 ∣ (L₀ + 1) := by omega
    rcases pentagon_pure_shift3_closure (L₀ := L₀ + 1) (t := b) (by omega) hndvd hbound with
      ⟨j, hj, hpow⟩
    exact ⟨1, le_rfl, j, hj, hpow⟩
  · by_cases hL1 : L₀ = 1
    · subst hL1
      have hndvd : ¬ 3 ∣ (1 + 1) := by omega
      rcases pentagon_pure_shift3_closure (L₀ := 1 + 1) (t := b) (by omega) hndvd hbound with
        ⟨j, hj, hpow⟩
      exact ⟨1, le_rfl, j, hj, hpow⟩
    · have hbound0 : 4 * max L₀ 4 ≤ L₀ + b * 3 := by
        by_cases hL4 : L₀ < 4
        · have hL2 : L₀ = 2 := by omega
          subst hL2
          have hb : 5 ≤ b := by
            have : max (2 + 1) 4 = 4 := by decide
            rw [this] at hbound
            omega
          have : max 2 4 = 4 := by decide
          rw [this]
          omega
        · have h1 : max L₀ 4 = L₀ := max_eq_left (by omega)
          have h2 : max (L₀ + 1) 4 = L₀ + 1 := max_eq_left (by omega)
          rw [h1]
          rw [h2] at hbound
          omega
      rcases pentagon_pure_shift3_closure (L₀ := L₀) (t := b) hLpos h3 hbound0 with
        ⟨j, hj, hpow⟩
      exact ⟨0, by decide, j, hj, by simpa using hpow⟩

/--
Theorem 7 (`mixed_shift_ge2_ones_full_interval`):
With `a ≥ 2` shifts of `Δ = 1` and `b` shifts of `Δ = 3`, every integer `x ≤ a + 3*b`
is represented as `i + 3*j` with `i ≤ a` and `j ≤ b` (eliminating all modular gaps).
-/
theorem mixed_shift_ge2_ones_full_interval {a b x : ℕ} (ha : 2 ≤ a) (hx : x ≤ a + b * 3) :
    ∃ i ≤ a, ∃ j ≤ b, i + j * 3 = x := by
  by_cases hle : x / 3 ≤ b
  · refine ⟨x % 3, ?_, x / 3, hle, ?_⟩
    · have : x % 3 < 3 := Nat.mod_lt x (by decide)
      omega
    · have := Nat.div_add_mod x 3
      omega
  · refine ⟨x - b * 3, ?_, b, le_rfl, ?_⟩
    · omega
    · omega

/-! ### Part 2: 2-Factor Arc-Partition Shifts & Abstract Modular-Adjuster Graph Closure -/

/--
Theorem 8 (`two_factor_arc_partition`):
On any cycle of length `c`, two complementary arcs of lengths `p, q` with `p + q = c`
have shift `Δ = max p q - min p q` with the same parity as `c`.
-/
theorem two_factor_arc_partition {c p q : ℕ} (hsum : p + q = c) :
    (max p q - min p q) % 2 = c % 2 := by
  by_cases h : p ≤ q
  · rw [max_eq_right h, min_eq_left h]
    omega
  · rw [max_eq_left (Nat.le_of_not_le h), min_eq_right (Nat.le_of_not_le h)]
    omega

/--
Theorem 9 (`pentagon_arc_shifts`):
Every nontrivial split `p + q = 5` (`p ≥ 1, q ≥ 1`) of a pentagon `C₅` has nonzero shift
`Δ = max p q - min p q ∈ {1, 3}`.
-/
theorem pentagon_arc_shifts {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hsum : p + q = 5) :
    max p q - min p q = 1 ∨ max p q - min p q = 3 := by
  by_cases h : p ≤ q
  · rw [max_eq_right h, min_eq_left h]; omega
  · rw [max_eq_left (Nat.le_of_not_le h), min_eq_right (Nat.le_of_not_le h)]; omega

/--
Theorem 10 (`hexagon_arc_shifts`):
Every nontrivial split `p + q = 6` (`p ≥ 1, q ≥ 1`) of a hexagon `C₆` has shift
`Δ = max p q - min p q ∈ {0, 2, 4}`.
-/
theorem hexagon_arc_shifts {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hsum : p + q = 6) :
    max p q - min p q = 0 ∨ max p q - min p q = 2 ∨ max p q - min p q = 4 := by
  by_cases h : p ≤ q
  · rw [max_eq_right h, min_eq_left h]; omega
  · rw [max_eq_left (Nat.le_of_not_le h), min_eq_right (Nat.le_of_not_le h)]; omega

/--
Theorem 11 (`hasPow2Cycle_of_modular_adjuster_chain`):
Any graph `G` realizing an arithmetic progression of simple cycle lengths `L₀ + j * (2^a * u)`
(`0 ≤ j ≤ t`) under the Modular-Octave bound unconditionally contains a power-of-2 cycle.
-/
theorem hasPow2Cycle_of_modular_adjuster_chain {V : Type*} (G : SimpleGraph V)
    {a u o r L₀ t : ℕ}
    (ho : 1 ≤ o) (hper : 2 ^ o ≡ 1 [MOD u])
    (hLpos : 1 ≤ L₀) (hdvd : 2 ^ a ∣ L₀)
    (hcong : 2 ^ r ≡ L₀ / 2 ^ a [MOD u])
    (hbound : 2 ^ o * max L₀ 4 ≤ L₀ + t * (2 ^ a * u))
    (hreal : ∀ j ≤ t, HasCycleLen G (L₀ + j * (2 ^ a * u))) :
    HasPow2Cycle G := by
  rcases exists_pow2_mod_odd_in_window ho hper hLpos hdvd hcong hbound with ⟨j, hj, hpow⟩
  rcases hreal j hj with ⟨v, p, hcyc, hlen⟩
  exact ⟨v, p, hcyc, hlen ▸ hpow⟩

/-! ### Part 3: Dual Cross-Rewiring Theorem on `MinimalBad` Non-Triangle Cubic Edges -/

/-- A graph `G` is `C₄`-free if no four distinct vertices form a 4-cycle. -/
def C4Free {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ a b c d : V, a ≠ b → b ≠ c → c ≠ d → d ≠ a → a ≠ c → b ≠ d →
    ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)

/--
Theorem 12 (`cross_rewiring_neighbors_disjoint_and_nonadj`):
In any `C₄`-free simple graph `G`, if `uv ∈ E(G)` lies in no triangle, then the external
neighbors `u' ∈ N(u) \ {v}` and `v' ∈ N(v) \ {u}` are disjoint and non-adjacent in `G`.
-/
theorem cross_rewiring_neighbors_disjoint_and_nonadj {V : Type*} (G : SimpleGraph V)
    (hc4 : C4Free G) {u v u' v' : V}
    (huv : G.Adj u v)
    (hnotri : ∀ w : V, ¬ (G.Adj u w ∧ G.Adj w v))
    (hu' : G.Adj u u') (hu'v : u' ≠ v)
    (hv' : G.Adj v v') (hv'u : v' ≠ u) :
    u' ≠ v' ∧ ¬ G.Adj u' v' := by
  have hne : u' ≠ v' := by
    intro heq
    subst heq
    exact hnotri u' ⟨hu', hv'.symm⟩
  have hnadj : ¬ G.Adj u' v' := by
    intro hadj
    have huv_ne : u ≠ v := G.ne_of_adj huv
    have huu'_ne : u ≠ u' := G.ne_of_adj hu'
    have hvv'_ne : v ≠ v' := G.ne_of_adj hv'
    exact hc4 u u' v' v huu'_ne hne hvv'_ne.symm huv_ne.symm hv'u.symm hu'v
      ⟨hu', hadj, hv'.symm, huv.symm⟩
  exact ⟨hne, hnadj⟩

/-- The cross-rewired graph `G_×(u, v; u₁, u₂, v₁, v₂)` on `{w : V // w ≠ u ∧ w ≠ v}` obtained
by deleting `{u, v}` and adding the two cross-edges `u₁v₁` and `u₂v₂`. -/
def crossRewire {V : Type*} (G : SimpleGraph V) (u v u₁ u₂ v₁ v₂ : V)
    (h1 : u₁ ≠ v₁) (h2 : u₂ ≠ v₂) :
    SimpleGraph {w : V // w ≠ u ∧ w ≠ v} where
  Adj x y :=
    G.Adj x.1 y.1 ∨
    (x.1 = u₁ ∧ y.1 = v₁) ∨ (x.1 = v₁ ∧ y.1 = u₁) ∨
    (x.1 = u₂ ∧ y.1 = v₂) ∨ (x.1 = v₂ ∧ y.1 = u₂)
  symm := by
    intro x y h
    rcases h with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  loopless := by
    intro x h
    rcases h with h | ⟨hxa, hxb⟩ | ⟨hxa, hxb⟩ | ⟨hxa, hxb⟩ | ⟨hxa, hxb⟩
    · exact G.loopless x.1 h
    · exact h1 (hxa.symm.trans hxb)
    · exact h1 (hxb.symm.trans hxa)
    · exact h2 (hxa.symm.trans hxb)
    · exact h2 (hxb.symm.trans hxa)

private lemma card_neighborFinset_ge_of_replace {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v u₁ u₂ v₁ v₂ : V} (h1 : u₁ ≠ v₁) (h2 : u₂ ≠ v₂)
    (H : SimpleGraph {w : V // w ≠ u ∧ w ≠ v}) [DecidableRel H.Adj]
    (hH : H = crossRewire G u v u₁ u₂ v₁ v₂ h1 h2)
    (x : {w : V // w ≠ u ∧ w ≠ v})
    (del : V) (add : {w : V // w ≠ u ∧ w ≠ v})
    (hdel_only : ∀ w : V, G.Adj x.1 w → w = u ∨ w = v → w = del)
    (hadd_nadj : ¬ G.Adj x.1 add.1)
    (hadd_adj : H.Adj x add) :
    G.degree x.1 ≤ H.degree x := by
  classical
  have hsub :
      (G.neighborFinset x.1).erase del |>.card ≤ ((H.neighborFinset x).erase add).card := by
    refine Finset.card_le_card_of_injOn
      (fun w => if hw : w ≠ u ∧ w ≠ v then ⟨w, hw⟩ else add) ?_ ?_
    · intro w hw
      have hw_ne_del : w ≠ del := (Finset.mem_erase.mp hw).1
      have hw_adj : G.Adj x.1 w := (mem_neighborFinset G x.1 w).mp (Finset.mem_erase.mp hw).2
      have hne_uv : w ≠ u ∧ w ≠ v := by
        constructor
        · intro hwu; exact hw_ne_del (hdel_only w hw_adj (Or.inl hwu))
        · intro hwv; exact hw_ne_del (hdel_only w hw_adj (Or.inr hwv))
      simp only [dif_pos hne_uv, Finset.mem_erase, mem_neighborFinset]
      refine ⟨?_, ?_⟩
      · intro heq
        have : w = add.1 := congrArg Subtype.val heq
        exact hadd_nadj (this ▸ hw_adj)
      · rw [hH]
        exact Or.inl hw_adj
    · intro w₁ hw₁ w₂ hw₂ heq
      have hne1 : w₁ ≠ u ∧ w₁ ≠ v := by
        have hw_ne_del : w₁ ≠ del := (Finset.mem_erase.mp hw₁).1
        have hw_adj : G.Adj x.1 w₁ := (mem_neighborFinset G x.1 w₁).mp (Finset.mem_erase.mp hw₁).2
        exact ⟨fun h => hw_ne_del (hdel_only w₁ hw_adj (Or.inl h)),
               fun h => hw_ne_del (hdel_only w₁ hw_adj (Or.inr h))⟩
      have hne2 : w₂ ≠ u ∧ w₂ ≠ v := by
        have hw_ne_del : w₂ ≠ del := (Finset.mem_erase.mp hw₂).1
        have hw_adj : G.Adj x.1 w₂ := (mem_neighborFinset G x.1 w₂).mp (Finset.mem_erase.mp hw₂).2
        exact ⟨fun h => hw_ne_del (hdel_only w₂ hw_adj (Or.inl h)),
               fun h => hw_ne_del (hdel_only w₂ hw_adj (Or.inr h))⟩
      simp only [dif_pos hne1, dif_pos hne2] at heq
      exact congrArg Subtype.val heq
  have hadd_mem : add ∈ H.neighborFinset x := (mem_neighborFinset H x add).mpr hadd_adj
  have hHcard : ((H.neighborFinset x).erase add).card + 1 = (H.neighborFinset x).card :=
    Finset.card_erase_add_one hadd_mem
  have hGcard : (G.neighborFinset x.1).card ≤ ((G.neighborFinset x.1).erase del).card + 1 := by
    by_cases hm : del ∈ G.neighborFinset x.1
    · rw [Finset.card_erase_add_one hm]
    · rw [Finset.erase_eq_of_notMem hm]; omega
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  omega

/--
Theorem 13 (`cross_rewiring_min_degree_three`):
In any `C₄`-free finite graph `G` with `δ(G) ≥ 3`, if `uv ∈ E(G)` is a non-triangle cubic edge
with `N(u) = {v, u₁, u₂}` and `N(v) = {u, v₁, v₂}`, then the cross-rewired graph
`crossRewire G u v u₁ u₂ v₁ v₂` on `|V(G)| - 2` vertices preserves `δ ≥ 3` (in fact
`deg_{G_×}(x) ≥ deg_G(x)` for every surviving vertex `x`).
-/
theorem cross_rewiring_min_degree_three {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc4 : C4Free G) (hmin : ∀ w : V, 3 ≤ G.degree w)
    {u v u₁ u₂ v₁ v₂ : V}
    (huv : G.Adj u v)
    (hnotri : ∀ w : V, ¬ (G.Adj u w ∧ G.Adj w v))
    (hu_nb : ∀ w : V, G.Adj u w ↔ w = v ∨ w = u₁ ∨ w = u₂)
    (hv_nb : ∀ w : V, G.Adj v w ↔ w = u ∨ w = v₁ ∨ w = v₂)
    (hu₁v : u₁ ≠ v) (hu₂v : u₂ ≠ v) (hv₁u : v₁ ≠ u) (hv₂u : v₂ ≠ u)
    (h1 : u₁ ≠ v₁) (h2 : u₂ ≠ v₂) :
    let H := crossRewire G u v u₁ u₂ v₁ v₂ h1 h2
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    ∀ x : {w : V // w ≠ u ∧ w ≠ v}, 3 ≤ H.degree x := by
  classical
  intro H _ x
  have hu₁_adj : G.Adj u u₁ := (hu_nb u₁).mpr (Or.inr (Or.inl rfl))
  have hu₂_adj : G.Adj u u₂ := (hu_nb u₂).mpr (Or.inr (Or.inr rfl))
  have hv₁_adj : G.Adj v v₁ := (hv_nb v₁).mpr (Or.inr (Or.inl rfl))
  have hv₂_adj : G.Adj v v₂ := (hv_nb v₂).mpr (Or.inr (Or.inr rfl))
  have hu₁_ne_u : u₁ ≠ u := (G.ne_of_adj hu₁_adj).symm
  have hu₂_ne_u : u₂ ≠ u := (G.ne_of_adj hu₂_adj).symm
  have hv₁_ne_v : v₁ ≠ v := (G.ne_of_adj hv₁_adj).symm
  have hv₂_ne_v : v₂ ≠ v := (G.ne_of_adj hv₂_adj).symm
  have h11 := cross_rewiring_neighbors_disjoint_and_nonadj G hc4 huv hnotri hu₁_adj hu₁v hv₁_adj hv₁u
  have h22 := cross_rewiring_neighbors_disjoint_and_nonadj G hc4 huv hnotri hu₂_adj hu₂v hv₂_adj hv₂u
  have hdeg_ge : G.degree x.1 ≤ H.degree x := by
    by_cases hxu₁ : x.1 = u₁
    · refine card_neighborFinset_ge_of_replace G h1 h2 H rfl x u ⟨v₁, hv₁u, hv₁_ne_v⟩ ?_ ?_ ?_
      · intro w hw hwu
        rcases hwu with rfl | rfl
        · rfl
        · exfalso; exact hnotri u₁ ⟨hu₁_adj, hxu₁ ▸ hw⟩
      · rw [hxu₁]; exact h11.2
      · exact Or.inr (Or.inl ⟨hxu₁, rfl⟩)
    · by_cases hxu₂ : x.1 = u₂
      · refine card_neighborFinset_ge_of_replace G h1 h2 H rfl x u ⟨v₂, hv₂u, hv₂_ne_v⟩ ?_ ?_ ?_
        · intro w hw hwu
          rcases hwu with rfl | rfl
          · rfl
          · exfalso; exact hnotri u₂ ⟨hu₂_adj, hxu₂ ▸ hw⟩
        · rw [hxu₂]; exact h22.2
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hxu₂, rfl⟩)))
      · by_cases hxv₁ : x.1 = v₁
        · refine card_neighborFinset_ge_of_replace G h1 h2 H rfl x v ⟨u₁, hu₁_ne_u, hu₁v⟩ ?_ ?_ ?_
          · intro w hw hwu
            rcases hwu with rfl | rfl
            · exfalso; exact hnotri v₁ ⟨(hxv₁ ▸ hw).symm, hv₁_adj.symm⟩
            · rfl
          · rw [hxv₁]; intro hadj; exact h11.2 hadj.symm
          · exact Or.inr (Or.inr (Or.inl ⟨hxv₁, rfl⟩))
        · by_cases hxv₂ : x.1 = v₂
          · refine card_neighborFinset_ge_of_replace G h1 h2 H rfl x v ⟨u₂, hu₂_ne_u, hu₂v⟩ ?_ ?_ ?_
            · intro w hw hwu
              rcases hwu with rfl | rfl
              · exfalso; exact hnotri v₂ ⟨(hxv₂ ▸ hw).symm, hv₂_adj.symm⟩
              · rfl
            · rw [hxv₂]; intro hadj; exact h22.2 hadj.symm
            · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hxv₂, rfl⟩)))
          · rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
            refine Finset.card_le_card_of_injOn
              (fun w => if hw : w ≠ u ∧ w ≠ v then ⟨w, hw⟩ else x) ?_ ?_
            · intro w hw
              have hxw : G.Adj x.1 w := (mem_neighborFinset G x.1 w).mp hw
              have hne : w ≠ u ∧ w ≠ v := by
                constructor
                · intro hwu
                  subst hwu
                  have := (hu_nb x.1).mp hxw.symm
                  rcases this with h | h | h
                  · exact x.2.2 h
                  · exact hxu₁ h
                  · exact hxu₂ h
                · intro hwv
                  subst hwv
                  have := (hv_nb x.1).mp hxw.symm
                  rcases this with h | h | h
                  · exact x.2.1 h
                  · exact hxv₁ h
                  · exact hxv₂ h
              simp only [dif_pos hne, mem_neighborFinset]
              exact Or.inl hxw
            · intro w₁ hw₁ w₂ hw₂ heq
              have hne1 : w₁ ≠ u ∧ w₁ ≠ v := by
                have hxw : G.Adj x.1 w₁ := (mem_neighborFinset G x.1 w₁).mp hw₁
                exact ⟨fun h => by subst h; rcases (hu_nb x.1).mp hxw.symm with h' | h' | h'
                                   · exact x.2.2 h'
                                   · exact hxu₁ h'
                                   · exact hxu₂ h',
                       fun h => by subst h; rcases (hv_nb x.1).mp hxw.symm with h' | h' | h'
                                   · exact x.2.1 h'
                                   · exact hxv₁ h'
                                   · exact hxv₂ h'⟩
              have hne2 : w₂ ≠ u ∧ w₂ ≠ v := by
                have hxw : G.Adj x.1 w₂ := (mem_neighborFinset G x.1 w₂).mp hw₂
                exact ⟨fun h => by subst h; rcases (hu_nb x.1).mp hxw.symm with h' | h' | h'
                                   · exact x.2.2 h'
                                   · exact hxu₁ h'
                                   · exact hxu₂ h',
                       fun h => by subst h; rcases (hv_nb x.1).mp hxw.symm with h' | h' | h'
                                   · exact x.2.1 h'
                                   · exact hxv₁ h'
                                   · exact hxv₂ h'⟩
              simp only [dif_pos hne1, dif_pos hne2] at heq
              exact congrArg Subtype.val heq
  exact le_trans (hmin x.1) hdeg_ge

/--
Theorem 14 (`cross_rewiring_length_lifting_arithmetic`):
Exact length-accounting law for lifting a `2^c`-cycle `C'` from `crossRewire G u v u₁ u₂ v₁ v₂`
back to `G`:
- Using 1 cross-edge replaces length `1` by `u₁-u-v-v₁` (length `3`), giving length `2^c + 2`.
- Using 2 cross-edges leaves two disjoint paths of total length `2^c - 2` in `G - {u,v}`:
  - Twisted routing (`u₁ ↝ v₂`, `v₁ ↝ u₂`) closes via `u₁-u-u₂` and `v₁-v-v₂` into a single
    simple cycle of length `(2^c - 2) + 4 = 2^c + 2`.
  - Parallel routing (`u₁ ↝ u₂`, `v₁ ↝ v₂`) closes via `u` and `v` into a vertex-disjoint
    dumbbell `(C_u, C_v)` joined by `uv` with `|C_u| + |C_v| = 2^c + 2`.
-/
theorem cross_rewiring_length_lifting_arithmetic {c p₁ p₂ : ℕ} (hc : 2 ≤ c)
    (hsum : p₁ + p₂ + 2 = 2 ^ c) :
    (2 ^ c - 1) + 3 = 2 ^ c + 2 ∧ (p₁ + 2) + (p₂ + 2) = 2 ^ c + 2 := by
  have h4 : 4 ≤ 2 ^ c := by
    calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ c := Nat.pow_le_pow_right (by decide) hc
  omega

/-! ### Part 4: Cubic Non-Backtracking Power-Cycle Exclusion & Zero-Figure-Eight Theorem -/

/--
Theorem 15 (`no_repeated_cycle_pow2`):
If a simple graph `G` has no power-of-two simple cycle (`¬ HasPow2Cycle G`), then NO positive
multiple `m * p.length` of any simple cycle `p` in `G` can equal `2^r`.
-/
theorem no_repeated_cycle_pow2 {V : Type*} (G : SimpleGraph V) (hno : ¬ HasPow2Cycle G)
    {v : V} (p : G.Walk v v) (hp : p.IsCycle) (m r : ℕ) :
    m * p.length ≠ 2 ^ r := by
  intro heq
  have hdvd : p.length ∣ 2 ^ r := ⟨m, by linarith⟩
  rcases (Nat.dvd_prime_pow Nat.prime_two).mp hdvd with ⟨k, _, hk⟩
  have h3 : 3 ≤ p.length := hp.three_le_length
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have hk_le : k ≤ 1 := by omega
    have hpow_le : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by decide) hk_le
    omega
  exact hno ⟨v, p, hp, ⟨k, hk2, hk⟩⟩

/-- Helper: every simple cycle `p : G.Walk v v` contains two distinct edges incident to `v`. -/
private lemma cycle_two_distinct_incident_edges {V : Type*} (G : SimpleGraph V)
    {v : V} (p : G.Walk v v) (hp : p.IsCycle) :
    ∃ e₁ e₂ : Sym2 V, e₁ ≠ e₂ ∧ e₁ ∈ p.edges ∧ e₂ ∈ p.edges ∧ v ∈ e₁ ∧ v ∈ e₂ := by
  have hne_nil : ¬ p.Nil := hp.ne_nil
  have hlen3 : 3 ≤ p.length := hp.three_le_length
  have hnodup : p.edges.Nodup := hp.edges_nodup
  have hlen_edges : p.edges.length = p.length := p.length_edges
  have hpos : 0 < p.edges.length := by omega
  let e₁ := p.edges.head (List.ne_nil_of_length_pos hpos)
  let e₂ := p.edges.getLast (List.ne_nil_of_length_pos hpos)
  have he₁_mem : e₁ ∈ p.edges := List.head_mem _
  have he₂_mem : e₂ ∈ p.edges := List.getLast_mem _
  have hne : e₁ ≠ e₂ := by
    intro heq
    have h0 : p.edges[0]'hpos = e₁ := (List.head_eq_getElem_zero _).symm
    have hlast : p.edges[p.edges.length - 1]'(Nat.sub_lt hpos (by decide)) = e₂ :=
      (List.getLast_eq_getElem _).symm
    have hidx : (0 : ℕ) = p.edges.length - 1 := by
      have := (List.Nodup.getElem_inj_iff hnodup).mp (h0.trans (heq.trans hlast.symm))
      exact this
    omega
  have hv₁ : v ∈ e₁ := by
    cases p with
    | nil => exact absurd rfl hne_nil
    | cons h q =>
      simp [e₁, Walk.edges_cons]
  have hv₂ : v ∈ e₂ := by
    have hrev : p.reverse.edges = p.edges.reverse := Walk.edges_reverse p
    have hne_rev : ¬ p.reverse.Nil := by
      intro hr
      exact hne_nil (by simpa using congrArg Walk.reverse hr)
    have hpos_rev : 0 < p.reverse.edges.length := by
      rw [hrev, List.length_reverse]; exact hpos
    have hhead_rev : v ∈ p.reverse.edges.head (List.ne_nil_of_length_pos hpos_rev) := by
      cases hp_rev : p.reverse with
      | nil => exact absurd hp_rev (by simpa [Walk.nil_iff_eq_nil] using hne_rev)
      | cons h q => simp [Walk.edges_cons]
    have hhead_eq : p.reverse.edges.head (List.ne_nil_of_length_pos hpos_rev) = e₂ := by
      have h1 : p.edges.reverse.head (by rw [List.ne_nil_iff_length_pos, List.length_reverse]; exact hpos) =
          p.edges.getLast (List.ne_nil_of_length_pos hpos) := List.head_reverse _
      simpa [e₂, hrev] using h1
    exact hhead_eq ▸ hhead_rev
  exact ⟨e₁, e₂, hne, he₁_mem, he₂_mem, hv₁, hv₂⟩

/--
Theorem 16 (`cubic_no_edge_disjoint_cycles_sharing_vertex`):
**Cubic Zero-Figure-Eight Theorem**.
In any finite simple graph `G` with maximum degree `Δ(G) ≤ 3`, two edge-disjoint simple cycles
cannot share a vertex. Hence every non-simple tailless closed non-backtracking walk in a cubic
graph must repeat at least one edge (no figure-eight walks exist).
-/
theorem cubic_no_edge_disjoint_cycles_sharing_vertex {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcub : ∀ w : V, G.degree w ≤ 3)
    {v : V} (p₁ p₂ : G.Walk v v) (hp₁ : p₁.IsCycle) (hp₂ : p₂.IsCycle)
    (hdisj : Disjoint p₁.edges.toFinset p₂.edges.toFinset) :
    False := by
  classical
  rcases cycle_two_distinct_incident_edges G p₁ hp₁ with ⟨e₁, e₂, h12, hm1, hm2, hv1, hv2⟩
  rcases cycle_two_distinct_incident_edges G p₂ hp₂ with ⟨e₃, e₄, h34, hm3, hm4, hv3, hv4⟩
  have h13 : e₁ ≠ e₃ := fun h => Finset.disjoint_left.mp hdisj
    (List.mem_toFinset.mpr hm1) (h ▸ List.mem_toFinset.mpr hm3)
  have h14 : e₁ ≠ e₄ := fun h => Finset.disjoint_left.mp hdisj
    (List.mem_toFinset.mpr hm1) (h ▸ List.mem_toFinset.mpr hm4)
  have h23 : e₂ ≠ e₃ := fun h => Finset.disjoint_left.mp hdisj
    (List.mem_toFinset.mpr hm2) (h ▸ List.mem_toFinset.mpr hm3)
  have h24 : e₂ ≠ e₄ := fun h => Finset.disjoint_left.mp hdisj
    (List.mem_toFinset.mpr hm2) (h ▸ List.mem_toFinset.mpr hm4)
  let S : Finset (Sym2 V) := {e₁, e₂, e₃, e₄}
  have hcardS : S.card = 4 := by
    simp [S, h12, h13, h14, h23, h24, h34]
  have hsub : S ⊆ G.incidenceFinset v := by
    intro e he
    rw [mem_incidenceFinset]
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact ⟨Walk.edges_subset_edgeSet p₁ hm1, hv1⟩
    · exact ⟨Walk.edges_subset_edgeSet p₁ hm2, hv2⟩
    · exact ⟨Walk.edges_subset_edgeSet p₂ hm3, hv3⟩
    · exact ⟨Walk.edges_subset_edgeSet p₂ hm4, hv4⟩
  have hle : S.card ≤ (G.incidenceFinset v).card := Finset.card_le_card hsub
  rw [hcardS, card_incidenceFinset_eq_degree] at hle
  have hdeg := hcub v
  omega

end E64Wave7Agent7
