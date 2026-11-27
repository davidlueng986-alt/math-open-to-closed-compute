import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic

namespace E64Wave7Agent9

/-- A natural number `m` is a power of two at least `4` (`2^k` with `k ≥ 2`). -/
def IsPow2Ge4 (m : ℕ) : Prop :=
  ∃ k : ℕ, 2 ≤ k ∧ m = 2 ^ k

/-! ### Part 1: Dyadic-Octave Interval & Signed Adjuster Normalization -/

/-- Every integer interval `[a, b]` with `a ≥ 2`, `b ≥ 4`, and `b ≥ 2a - 1`
    unconditionally contains a power of two `2^k` (`k ≥ 2`). -/
theorem pow2_in_interval_of_double_sub_one (a b : ℕ)
    (ha : 2 ≤ a) (hb : 4 ≤ b) (hgap : 2 * a - 1 ≤ b) :
    ∃ m : ℕ, a ≤ m ∧ m ≤ b ∧ IsPow2Ge4 m := by
  have h_exists : ∃ k : ℕ, a ≤ 2 ^ k := ⟨a, Nat.le_of_lt (Nat.lt_two_pow_self)⟩
  classical
  let k := Nat.find h_exists
  have hk_ge : a ≤ 2 ^ k := Nat.find_spec h_exists
  by_cases hk2 : 2 ≤ k
  · refine ⟨2 ^ k, hk_ge, ?_, ⟨k, hk2, rfl⟩⟩
    have hprev : ¬ (a ≤ 2 ^ (k - 1)) := Nat.find_min h_exists (by omega)
    have hlt : 2 ^ (k - 1) < a := Nat.lt_of_not_ge hprev
    have hpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
      have : k = (k - 1) + 1 := by omega
      conv_lhs => rw [this, Nat.pow_succ]
      ring
    omega
  · have hk_le1 : k ≤ 1 := by omega
    have ha_le2 : a ≤ 2 := by
      have : 2 ^ k ≤ 2 := by
        interval_cases k <;> norm_num
      omega
    exact ⟨4, by omega, hb, ⟨2, le_rfl, by norm_num⟩⟩

/-- Even-interval dyadic hitting: `[2a, 2b]` with `a ≥ 2` and `b ≥ 2a - 1`
    unconditionally contains a power of two `2^k` (`k ≥ 2`). -/
theorem pow2_even_in_interval_of_double_sub_two (a b : ℕ)
    (ha : 2 ≤ a) (hgap : 2 * a - 1 ≤ b) :
    ∃ m : ℕ, 2 * a ≤ m ∧ m ≤ 2 * b ∧ Even m ∧ IsPow2Ge4 m := by
  have hb4 : 4 ≤ 2 * b := by omega
  have hgap2 : 2 * (2 * a) - 1 ≤ 2 * b := by omega
  rcases pow2_in_interval_of_double_sub_one (2 * a) (2 * b) (by omega) hb4 hgap2 with
    ⟨m, hlo, hhi, ⟨k, hk2, rfl⟩⟩
  refine ⟨2 ^ k, hlo, hhi, ?_, ⟨k, hk2, rfl⟩⟩
  have : 2 ^ k = 2 * 2 ^ (k - 1) := by
    have hk1 : k = (k - 1) + 1 := by omega
    conv_lhs => rw [hk1, Nat.pow_succ]
    ring
  exact ⟨2 ^ (k - 1), by omega⟩

/-- Sum of positive parts of a signed shift list. -/
def posSum : List ℤ → ℕ
  | [] => 0
  | d :: ds => (if 0 ≤ d then d.natAbs else 0) + posSum ds

/-- Sum of magnitudes of negative parts (shortcuts) of a signed shift list. -/
def negSum : List ℤ → ℕ
  | [] => 0
  | d :: ds => (if d < 0 then d.natAbs else 0) + negSum ds

/-- Sum of all absolute magnitudes of a signed shift list. -/
def absSum : List ℤ → ℕ
  | [] => 0
  | d :: ds => d.natAbs + absSum ds

/-- `absSum = posSum + negSum`. -/
theorem absSum_eq_posSum_add_negSum (ds : List ℤ) :
    absSum ds = posSum ds + negSum ds := by
  induction ds with
  | nil => simp [absSum, posSum, negSum]
  | cons d tl ih =>
    simp only [absSum, posSum, negSum]
    by_cases h : 0 ≤ d
    · have hnot : ¬ (d < 0) := by omega
      simp [h, hnot]
      omega
    · have hlt : d < 0 := by omega
      simp [h, hlt]
      omega

/-- Signed subset-sum evaluation against a boolean selector `sel`. -/
def signedSelSum : List ℤ → List Bool → ℤ
  | [], _ => 0
  | _, [] => 0
  | d :: ds, b :: bs => (if b then d else 0) + signedSelSum ds bs

/-- Unsigned subset-sum evaluation against a boolean selector `sel`. -/
def absSelSum : List ℤ → List Bool → ℕ
  | [], _ => 0
  | _, [] => 0
  | d :: ds, b :: bs => (if b then d.natAbs else 0) + absSelSum ds bs

/-- Toggle selector on negative shifts (`d < 0`) to convert signed subset sums
    into nonnegative subset sums shifted by `-negSum ds`. -/
def toggleNegSel : List ℤ → List Bool → List Bool
  | [], _ => []
  | _, [] => []
  | d :: ds, b :: bs => (if d < 0 then !b else b) :: toggleNegSel ds bs

private lemma toggleNegSel_length (ds : List ℤ) (sel : List Bool)
    (hlen : sel.length = ds.length) :
    (toggleNegSel ds sel).length = ds.length := by
  induction ds generalizing sel with
  | nil => cases sel <;> simp [toggleNegSel] at *
  | cons d tl ih =>
    cases sel with
    | nil => simp at hlen
    | cons b bs =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      simp [toggleNegSel, ih bs hlen]

/-- Exact Signed Adjuster Normalization Bijection:
    For any base length `L` and boolean selector `sel` of length `ds.length`,
    `(L - negSum ds) + absSelSum ds sel = L + signedSelSum ds (toggleNegSel ds sel)`. -/
theorem signed_adjuster_normalization (L : ℤ) (ds : List ℤ) (sel : List Bool)
    (hlen : sel.length = ds.length) :
    (L - (negSum ds : ℤ)) + (absSelSum ds sel : ℤ) =
      L + signedSelSum ds (toggleNegSel ds sel) := by
  induction ds generalizing sel with
  | nil =>
    cases sel with
    | nil => simp [negSum, absSelSum, signedSelSum, toggleNegSel]
    | cons _ _ => simp at hlen
  | cons d tl ih =>
    cases sel with
    | nil => simp at hlen
    | cons b bs =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      specialize ih bs hlen
      simp only [negSum, absSelSum, signedSelSum, toggleNegSel, Nat.cast_add]
      by_cases hlt : d < 0
      · have hd : (d.natAbs : ℤ) = -d := by omega
        cases b <;> simp [hlt, hd] at * <;> omega
      · have hd : (d.natAbs : ℤ) = d := by omega
        cases b <;> simp [hlt, hd] at * <;> omega

/-- Double-Weight Shortcut Dyadic Threshold:
    If `L_min = L - negSum ds ≥ 2`, `L_max = L + posSum ds ≥ 4`, and
    `posSum ds + 2 * negSum ds ≥ L - 1`, then `[L - negSum ds, L + posSum ds]`
    unconditionally contains a power of two `2^k` (`k ≥ 2`). -/
theorem signed_double_shortcut_threshold (L : ℕ) (ds : List ℤ)
    (hmin : negSum ds + 2 ≤ L) (hmax : 4 ≤ L + posSum ds)
    (hshortcut : L - 1 ≤ posSum ds + 2 * negSum ds) :
    ∃ m : ℕ, L - negSum ds ≤ m ∧ m ≤ L + posSum ds ∧ IsPow2Ge4 m := by
  apply pow2_in_interval_of_double_sub_one (L - negSum ds) (L + posSum ds)
  · omega
  · exact hmax
  · omega

/-! ### Part 2: Brown Completeness, Parity-Flip Even-Brown, & Modular Dyadic Hitting -/

/-- A list of positive weights `ws` is Brown-complete if every element is at most
    `1 + sum` of the remaining suffix (inductive form). -/
def IsBrownComplete : List ℕ → Prop
  | [] => True
  | w :: ws => w ≤ ws.sum + 1 ∧ IsBrownComplete ws

/-- Predicate that `t` is a subset sum of `ws`. -/
def IsSubsetSum (ws : List ℕ) (t : ℕ) : Prop :=
  ∃ sel : List Bool, sel.length = ws.length ∧
    t = (ws.zip sel).foldr (fun p acc => (if p.2 then p.1 else 0) + acc) 0

private lemma foldr_zip_cons (w : ℕ) (ws : List ℕ) (b : Bool) (bs : List Bool) :
    ((w :: ws).zip (b :: bs)).foldr (fun p acc => (if p.2 then p.1 else 0) + acc) 0 =
      (if b then w else 0) + (ws.zip bs).foldr (fun p acc => (if p.2 then p.1 else 0) + acc) 0 := by
  rfl

/-- Brown's Completeness Theorem: every `t ≤ ws.sum` is realized as a subset sum of `ws`. -/
theorem brown_subset_sum_complete (ws : List ℕ) (hB : IsBrownComplete ws) :
    ∀ t : ℕ, t ≤ ws.sum → IsSubsetSum ws t := by
  induction ws with
  | nil =>
    intro t ht
    simp only [List.sum_nil, Nat.le_zero] at ht
    subst ht
    exact ⟨[], rfl, rfl⟩
  | cons w tl ih =>
    rcases hB with ⟨hw, hBtl⟩
    intro t ht
    simp only [List.sum_cons] at ht
    by_cases hle : t ≤ tl.sum
    · rcases ih hBtl t hle with ⟨bs, hlen, hsum⟩
      refine ⟨false :: bs, by simp [hlen], ?_⟩
      rw [foldr_zip_cons]
      simpa using hsum
    · have hsub : t - w ≤ tl.sum := by omega
      have hge : w ≤ t := by omega
      rcases ih hBtl (t - w) hsub with ⟨bs, hlen, hsum⟩
      refine ⟨true :: bs, by simp [hlen], ?_⟩
      rw [foldr_zip_cons]
      simp only [↓reduceIte]
      omega

private lemma absSelSum_eq_foldr_map (ds : List ℤ) (sel : List Bool) :
    absSelSum ds sel =
      ((ds.map Int.natAbs).zip sel).foldr (fun p acc => (if p.2 then p.1 else 0) + acc) 0 := by
  induction ds generalizing sel with
  | nil => simp [absSelSum]
  | cons d tl ih =>
    cases sel with
    | nil => simp [absSelSum]
    | cons b bs =>
      simp only [absSelSum, List.map_cons, foldr_zip_cons]
      rw [ih bs]

private lemma sum_map_natAbs_eq_absSum (ds : List ℤ) :
    (ds.map Int.natAbs).sum = absSum ds := by
  induction ds with
  | nil => simp [absSum]
  | cons d tl ih => simp [absSum, ih]

/-- Signed Adjuster Brown Dyadic Hitting Theorem:
    If `ds.map Int.natAbs` is Brown-complete and `posSum ds + 2 * negSum ds ≥ L - 1`
    (with `L ≥ negSum ds + 2`, `L + posSum ds ≥ 4`), then there exists a boolean selector
    `sel` realizing a power of two `2^k` (`k ≥ 2`) as `L + signedSelSum ds sel`. -/
theorem signed_adjuster_brown_pow2 (L : ℕ) (ds : List ℤ)
    (hB : IsBrownComplete (ds.map Int.natAbs))
    (hmin : negSum ds + 2 ≤ L) (hmax : 4 ≤ L + posSum ds)
    (hshortcut : L - 1 ≤ posSum ds + 2 * negSum ds) :
    ∃ sel : List Bool, sel.length = ds.length ∧
      ∃ m : ℕ, IsPow2Ge4 m ∧ (L : ℤ) + signedSelSum ds sel = (m : ℤ) := by
  rcases signed_double_shortcut_threshold L ds hmin hmax hshortcut with ⟨m, hlo, hhi, hpow⟩
  have hsum_eq : (ds.map Int.natAbs).sum = posSum ds + negSum ds := by
    rw [sum_map_natAbs_eq_absSum, absSum_eq_posSum_add_negSum]
  have ht_le : m - (L - negSum ds) ≤ (ds.map Int.natAbs).sum := by omega
  rcases brown_subset_sum_complete (ds.map Int.natAbs) hB (m - (L - negSum ds)) ht_le with
    ⟨sel0, hlen0, hfold⟩
  have hlen_ds : sel0.length = ds.length := by simpa using hlen0
  have habs : absSelSum ds sel0 = m - (L - negSum ds) := by
    rw [absSelSum_eq_foldr_map, ← hfold]
  have hnorm := signed_adjuster_normalization (L : ℤ) ds sel0 hlen_ds
  refine ⟨toggleNegSel ds sel0, toggleNegSel_length ds sel0 hlen_ds, m, hpow, ?_⟩
  omega

/-- Parity-Flip + Even-Brown Completeness Theorem (Zero Unit-Step Adjusters!):
    Given ONE odd weight `w0` and a Brown-complete list `hs` representing even weights `2 * h`,
    if `L_min ≥ 3` and `2 * hs.sum ≥ L_min + w0 - 2`, then regardless of whether `L_min` is
    even or odd, there is a choice of `use_w0 : Bool` and `t ≤ hs.sum` such that
    `L_min + (if use_w0 then w0 else 0) + 2 * t` is a power of two `2^k` (`k ≥ 2`). -/
theorem parity_flip_even_brown_pow2 (L_min w0 : ℕ) (hs : List ℕ)
    (hB : IsBrownComplete hs) (hodd : Odd w0)
    (hL : 3 ≤ L_min) (hspan : L_min + w0 - 2 ≤ 2 * hs.sum) :
    ∃ (use_w0 : Bool) (t : ℕ), IsSubsetSum hs t ∧
      IsPow2Ge4 (L_min + (if use_w0 then w0 else 0) + 2 * t) := by
  by_cases hpar : Even L_min
  · rcases hpar with ⟨a, ha⟩
    have ha2 : 2 ≤ a := by omega
    have hgap : 2 * a - 1 ≤ a + hs.sum := by omega
    rcases pow2_even_in_interval_of_double_sub_two a (a + hs.sum) ha2 hgap with
      ⟨m, hlo, hhi, ⟨c, hc⟩, hpow⟩
    have ht_le : c - a ≤ hs.sum := by omega
    refine ⟨false, c - a, brown_subset_sum_complete hs hB (c - a) ht_le, ?_⟩
    have heq : L_min + (if false then w0 else 0) + 2 * (c - a) = m := by
      simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
      omega
    rw [heq]
    exact hpow
  · have hLodd : Odd L_min := Nat.not_even_iff_odd.mp hpar
    rcases hLodd with ⟨a1, ha1⟩
    rcases hodd with ⟨a2, ha2⟩
    let a := a1 + a2 + 1
    have hLw : L_min + w0 = 2 * a := by omega
    have ha2_ge : 2 ≤ a := by omega
    have hgap : 2 * a - 1 ≤ a + hs.sum := by omega
    rcases pow2_even_in_interval_of_double_sub_two a (a + hs.sum) ha2_ge hgap with
      ⟨m, hlo, hhi, ⟨c, hc⟩, hpow⟩
    have ht_le : c - a ≤ hs.sum := by omega
    refine ⟨true, c - a, brown_subset_sum_complete hs hB (c - a) ht_le, ?_⟩
    have heq : L_min + (if true then w0 else 0) + 2 * (c - a) = m := by
      simp only [↓reduceIte]
      omega
    rw [heq]
    exact hpow

/-- Clean Modular Dyadic AP Hitting Theorem with canonical representative `2 ≤ j ≤ e + 1`. -/
theorem modular_dyadic_ap_hit_canon (m e j L_min r : ℕ)
    (hm : 1 ≤ m) (he : 1 ≤ e) (hj_lo : 2 ≤ j) (hj_hi : j ≤ e + 1) (hL : 4 ≤ L_min)
    (hord : 2 ^ e % m = 1 % m) (hres : L_min % m = 2 ^ j % m)
    (hbound : 2 ^ e * (L_min - 1) ≤ L_min + m * r) :
    ∃ t : ℕ, t ≤ r ∧ IsPow2Ge4 (L_min + m * t) := by
  have hex : ∃ q : ℕ, L_min ≤ 2 ^ (j + q * e) := by
    refine ⟨L_min, ?_⟩
    have h1 : L_min ≤ j + L_min * e := by
      have : L_min ≤ L_min * e := Nat.le_mul_of_pos_right L_min (by omega)
      omega
    exact le_trans h1 (Nat.le_of_lt Nat.lt_two_pow_self)
  classical
  let q := Nat.find hex
  have hq_ge : L_min ≤ 2 ^ (j + q * e) := Nat.find_spec hex
  have hmod_step : ∀ n : ℕ, 2 ^ (j + n * e) % m = 2 ^ j % m := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hadd : j + (n + 1) * e = (j + n * e) + e := by ring
      rw [hadd, Nat.pow_add, Nat.mul_mod, ih, hord, ← Nat.mul_mod, mul_one]
  have hq_mod : 2 ^ (j + q * e) % m = L_min % m := by
    rw [hmod_step q, hres]
  have hdiv : m ∣ (2 ^ (j + q * e) - L_min) := by
    exact (Nat.modEq_iff_dvd' hq_ge).mp hq_mod.symm
  have hq_upper : 2 ^ (j + q * e) ≤ 2 ^ e * (L_min - 1) := by
    by_cases hq0 : q = 0
    · rw [hq0]
      simp only [zero_mul, add_zero]
      have h1 : 2 ^ j ≤ 2 ^ (e + 1) := Nat.pow_le_pow_right (by norm_num) hj_hi
      have h2 : 2 ^ (e + 1) = 2 ^ e * 2 := by rw [Nat.pow_succ]
      have h3 : 2 ^ e * 2 ≤ 2 ^ e * (L_min - 1) := Nat.mul_le_mul_left (2 ^ e) (by omega)
      omega
    · have hprev : ¬ (L_min ≤ 2 ^ (j + (q - 1) * e)) :=
        Nat.find_min hex (by omega)
      have hlt : 2 ^ (j + (q - 1) * e) ≤ L_min - 1 := by omega
      have hpow : 2 ^ (j + q * e) = 2 ^ e * 2 ^ (j + (q - 1) * e) := by
        have hidx : j + q * e = e + (j + (q - 1) * e) := by
          have : q = (q - 1) + 1 := by omega
          calc j + q * e = j + ((q - 1) + 1) * e := by rw [← this]
            _ = e + (j + (q - 1) * e) := by ring
        rw [hidx, Nat.pow_add]
      rw [hpow]
      exact Nat.mul_le_mul_left (2 ^ e) hlt
  rcases hdiv with ⟨t, ht⟩
  have hsum : L_min + m * t = 2 ^ (j + q * e) := by omega
  refine ⟨t, ?_, ⟨j + q * e, by omega, hsum⟩⟩
  have : m * t ≤ m * r := by omega
  exact Nat.le_of_mul_le_mul_left this (by omega)

/-- Mod-3 Dyadic AP Hitting (e.g. pure `C_5`-chord adjusters of shift `3`):
    If `L_min ≥ 4`, `3 ∤ L_min`, and `r ≥ L_min - 1`, then `{L_min + 3t | t ≤ r}`
    unconditionally contains a power of two `2^k` (`k ≥ 2`). -/
theorem mod3_dyadic_ap_hit (L_min r : ℕ)
    (hL : 4 ≤ L_min) (hndiv : L_min % 3 ≠ 0) (hr : L_min - 1 ≤ r) :
    ∃ t : ℕ, t ≤ r ∧ IsPow2Ge4 (L_min + 3 * t) := by
  have hcases : L_min % 3 = 1 ∨ L_min % 3 = 2 := by omega
  rcases hcases with h1 | h2
  · exact modular_dyadic_ap_hit_canon 3 2 2 L_min r (by omega) (by omega)
      (by omega) (by omega) hL (by norm_num) (by omega) (by omega)
  · exact modular_dyadic_ap_hit_canon 3 2 3 L_min r (by omega) (by omega)
      (by omega) (by omega) hL (by norm_num) (by omega) (by omega)

/-- Mod-5 Dyadic AP Hitting (e.g. pure `C_7`-chord adjusters of shift `5`):
    If `L_min ≥ 4`, `5 ∤ L_min`, and `r ≥ 3 * L_min - 3`, then `{L_min + 5t | t ≤ r}`
    unconditionally contains a power of two `2^k` (`k ≥ 2`). -/
theorem mod5_dyadic_ap_hit (L_min r : ℕ)
    (hL : 4 ≤ L_min) (hndiv : L_min % 5 ≠ 0) (hr : 3 * L_min - 3 ≤ r) :
    ∃ t : ℕ, t ≤ r ∧ IsPow2Ge4 (L_min + 5 * t) := by
  have hcases : L_min % 5 = 1 ∨ L_min % 5 = 2 ∨ L_min % 5 = 3 ∨ L_min % 5 = 4 := by omega
  rcases hcases with h1 | h2 | h3 | h4
  · exact modular_dyadic_ap_hit_canon 5 4 4 L_min r (by omega) (by omega)
      (by omega) (by omega) hL (by norm_num) (by omega) (by omega)
  · exact modular_dyadic_ap_hit_canon 5 4 5 L_min r (by omega) (by omega)
      (by omega) (by omega) hL (by norm_num) (by omega) (by omega)
  · exact modular_dyadic_ap_hit_canon 5 4 3 L_min r (by omega) (by omega)
      (by omega) (by omega) hL (by norm_num) (by omega) (by omega)
  · exact modular_dyadic_ap_hit_canon 5 4 2 L_min r (by omega) (by omega)
      (by omega) (by omega) hL (by norm_num) (by omega) (by omega)

/-! ### Part 3: Cubic Cycle-Intersection & Same-Scale / Cross-Scale Overlap Rigidity -/

/-- Cubic Pigeonhole Lemma: In any graph with `deg(v) ≤ 3`, two 2-element neighbor
    sets `S1, S2 ⊆ N(v)` (representing two cycles passing through `v`) must share
    at least one neighbor (hence at least one incident edge). -/
theorem cubic_shared_vertex_forces_shared_edge {V : Type*} [DecidableEq V]
    (Nv S1 S2 : Finset V)
    (hdeg : Nv.card ≤ 3) (hS1 : S1 ⊆ Nv) (hS2 : S2 ⊆ Nv)
    (hc1 : S1.card = 2) (hc2 : S2.card = 2) :
    (S1 ∩ S2).Nonempty := by
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  have hdisj : Disjoint S1 S2 := Finset.disjoint_iff_inter_eq_empty.mpr hempty
  have hunion_sub : S1 ∪ S2 ⊆ Nv := Finset.union_subset hS1 hS2
  have hunion_card : (S1 ∪ S2).card = 4 := by
    rw [Finset.card_union_of_disjoint hdisj, hc1, hc2]
  have hle : (S1 ∪ S2).card ≤ Nv.card := Finset.card_le_card hunion_sub
  omega

/-- Same-Scale `(2^k + 1)`-Cycle Single-Edge Exclusion:
    Two `(2^k + 1)`-cycles (`k ≥ 2`) sharing a single edge (`p = 1`) have
    symmetric-difference length `2^(k+1)`. -/
theorem same_scale_pow2_plus_one_no_single_edge (k : ℕ) (hk : 2 ≤ k) :
    IsPow2Ge4 ((2 ^ k + 1) + (2 ^ k + 1) - 2 * 1) := by
  refine ⟨k + 1, by omega, ?_⟩
  rw [Nat.pow_succ]
  omega

/-- Complete Same-Scale `(2^k + 1)`-Cycle Forbidden Single-Path Overlap Spectrum:
    For any `2 ≤ r ≤ k`, a single-path overlap of length `p = 2^k + 1 - 2^(r-1)`
    yields symmetric-difference length `2^r`. -/
theorem same_scale_pow2_plus_one_forbidden_path (k r : ℕ) (hr : 2 ≤ r) (hrk : r ≤ k) :
    let p := 2 ^ k + 1 - 2 ^ (r - 1)
    IsPow2Ge4 ((2 ^ k + 1) + (2 ^ k + 1) - 2 * p) := by
  intro p
  have hle : 2 ^ (r - 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2r : 2 ^ r = 2 * 2 ^ (r - 1) := by
    have : r = (r - 1) + 1 := by omega
    conv_lhs => rw [this, Nat.pow_succ]
    ring
  refine ⟨r, hr, ?_⟩
  dsimp [p]
  omega

/-- Same-Scale `(2^k + 2)`-Cycle Single-`P_3` Exclusion:
    Two `(2^k + 2)`-cycles (`k ≥ 2`) sharing a single 2-edge path (`p = 2`) have
    symmetric-difference length `2^(k+1)`. -/
theorem same_scale_pow2_plus_two_no_single_p3 (k : ℕ) (hk : 2 ≤ k) :
    IsPow2Ge4 ((2 ^ k + 2) + (2 ^ k + 2) - 2 * 2) := by
  refine ⟨k + 1, by omega, ?_⟩
  rw [Nat.pow_succ]
  omega

/-- Cross-Scale `(2^a + 1)`–`(2^b + 1)` Single-Path Exclusion (`2 ≤ a < b`):
    Sharing a single path of length `p = 2^(a-1) + 1` yields symmetric-difference length `2^b`. -/
theorem cross_scale_pow2_plus_one_forbidden_path (a b : ℕ) (ha : 2 ≤ a) (hab : a < b) :
    let p := 2 ^ (a - 1) + 1
    IsPow2Ge4 ((2 ^ a + 1) + (2 ^ b + 1) - 2 * p) := by
  intro p
  have h2a : 2 ^ a = 2 * 2 ^ (a - 1) := by
    have : a = (a - 1) + 1 := by omega
    conv_lhs => rw [this, Nat.pow_succ]
    ring
  have h2b : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  refine ⟨b, by omega, ?_⟩
  dsimp [p]
  omega

/-- Specialization (`a = 2`): No `(2^b + 1)`-cycle (`b ≥ 3`) can intersect a pentagon `C_5`
    in a single 3-edge path (`p = 3`), as the symmetric difference has length `2^b`. -/
theorem pentagon_no_p4_overlap_with_pow2_plus_one (b : ℕ) (hb : 3 ≤ b) :
    IsPow2Ge4 (5 + (2 ^ b + 1) - 2 * 3) := by
  have h2b : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  exact ⟨b, by omega, by omega⟩

/-- Pentagon Single-Path Overlap Rigidity:
    In any `{C_4, C_8}`-free graph, if two distinct `C_5`s intersect in a single path of
    length `p ∈ {1, 2, 3}`, then `p = 2` (since `p = 1` gives `C_8` and `p = 3` gives `C_4`). -/
theorem pentagon_overlap_only_p3 (p : ℕ) (hlo : 1 ≤ p) (hhi : p ≤ 3)
    (hno4 : ¬ IsPow2Ge4 (5 + 5 - 2 * p)) : p = 2 := by
  interval_cases p
  · exfalso; exact hno4 ⟨3, by omega, by norm_num⟩
  · rfl
  · exfalso; exact hno4 ⟨2, by omega, by norm_num⟩

/-- Exact Pentagon Density Bound from Cluster Isolation:
    If the pentagons of an `n`-vertex girth-≥5 `C_8`-free cubic graph decompose into
    `c1` vertex-disjoint isolated `C_5`s (5 vertices each) and `c2` vertex-disjoint
    isolated `Θ(2,3,3)` pairs (7 vertices, 2 pentagons each), then
    `7 * (c1 + 2 * c2) ≤ 2 * n`, i.e. `#C_5 ≤ ⌊2n / 7⌋`. -/
theorem pentagon_density_bound_of_cluster_isolation (n c1 c2 : ℕ)
    (hverts : 5 * c1 + 7 * c2 ≤ n) :
    7 * (c1 + 2 * c2) ≤ 2 * n := by
  omega

end E64Wave7Agent9
