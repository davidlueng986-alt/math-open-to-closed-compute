import Core

/-!
# Wave 4 Agent #3 — Whole-Problem Closure Theorems for Erdős #64

This module proves two genuinely new all-order global structural and closure theorems
for Erdős Problem #64 (Erdős–Gyárfás Conjecture), with zero `sorry`, zero `native_decide`,
and standard axioms only (`propext`, `Classical.choice`, `Quot.sound`):

1. **Exact Covering-Degree Classification & Non-Galois 4-Sheeted Covering Safe Descent**:
   - `partition_has_pow2_iff_one_two_four`: For every positive integer `d`, every positive
     integer partition of `d` contains a power of 2 if and only if `d ∈ {1, 2, 4}`.
   - `covering_lift_power_cycle_of_degree_two_or_four`: For ANY `d`-sheeted graph covering
     map `p : G → H` with `d ∈ {1, 2, 4}` (requiring NO automorphism of `G` — valid for
     non-Galois `S_4`-monodromy coverings with `Aut(G) = 1`), `HasPower H → HasPower G`.
   - `minimal_bad_no_two_or_four_cover`: Unconditionally across all 13 remaining leaves
     (`C`, `S`, `H`), no `MinimalBad` graph admits a 2- or 4-sheeted covering onto a
     strictly smaller `Near` graph.
   - `erdos64_of_global_two_or_four_cover`: Whole-problem closure gate — if every power-free
     `Near` graph admits a 2- or 4-sheeted covering quotient (or safe step), then full
     Erdős #64 is CLOSED.

2. **All-13-Leaves Global 2-Independent-Set Contraction Theorem**:
   - `minimal_bad_two_indep_avoiding_dyadic_path`: For EVERY `MinimalBad` graph `G`
     (all 13 remaining leaves `C`, `S`, `H` simultaneously) and EVERY 2-independent set
     `I` (`|I| ≥ 2`, pairwise distance ≥ 3), there exist distinct `u, v ∈ I` and a simple
     `u`–`v` path of length `2^k` (`k ≥ 2`) whose internal vertices are disjoint from `I`.
-/

namespace E64Wave4Agent3
open SimpleGraph Erdos64Closure E64Core
universe u

/-! ## Part 1: Exact Covering-Degree Classification (`d ∈ {1, 2, 4}`) -/

def IsPow2 (x : ℕ) : Prop := ∃ m : ℕ, x = 2 ^ m

private lemma not_isPow2_three : ¬ IsPow2 3 := by
  rintro ⟨m, hm⟩
  match m with
  | 0 => simp at hm
  | 1 => simp at hm
  | m + 2 =>
    have h4 : 4 ≤ 2 ^ (m + 2) := by
      have h1 : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by decide)
      calc 4 = 2 ^ 2 * 1 := by decide
        _ ≤ 2 ^ 2 * 2 ^ m := Nat.mul_le_mul_left 4 h1
        _ = 2 ^ (m + 2) := by rw [← pow_add, Nat.add_comm]
    omega

private lemma not_isPow2_five : ¬ IsPow2 5 := by
  rintro ⟨m, hm⟩
  match m with
  | 0 | 1 | 2 => simp at hm
  | m + 3 =>
    have h8 : 8 ≤ 2 ^ (m + 3) := by
      have h1 : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by decide)
      calc 8 = 2 ^ 3 * 1 := by decide
        _ ≤ 2 ^ 3 * 2 ^ m := Nat.mul_le_mul_left 8 h1
        _ = 2 ^ (m + 3) := by rw [← pow_add, Nat.add_comm]
    omega

private lemma not_isPow2_seven : ¬ IsPow2 7 := by
  rintro ⟨m, hm⟩
  match m with
  | 0 | 1 | 2 => simp at hm
  | m + 3 =>
    have h8 : 8 ≤ 2 ^ (m + 3) := by
      have h1 : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by decide)
      calc 8 = 2 ^ 3 * 1 := by decide
        _ ≤ 2 ^ 3 * 2 ^ m := Nat.mul_le_mul_left 8 h1
        _ = 2 ^ (m + 3) := by rw [← pow_add, Nat.add_comm]
    omega

private lemma exists_nonpow2_partition (d : ℕ) (hd : 1 ≤ d)
    (hne : d ≠ 1 ∧ d ≠ 2 ∧ d ≠ 4) :
    ∃ L : List ℕ, (∀ x ∈ L, 1 ≤ x) ∧ L.sum = d ∧ ∀ x ∈ L, ¬ IsPow2 x := by
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    by_cases h3 : d = 3
    · subst h3
      exact ⟨[3], by simp, by simp, by simp [not_isPow2_three]⟩
    by_cases h5 : d = 5
    · subst h5
      exact ⟨[5], by simp, by simp, by simp [not_isPow2_five]⟩
    by_cases h6 : d = 6
    · subst h6
      exact ⟨[3, 3], by simp, by simp, by simp [not_isPow2_three]⟩
    by_cases h7 : d = 7
    · subst h7
      exact ⟨[7], by simp, by simp, by simp [not_isPow2_seven]⟩
    have h8 : 8 ≤ d := by omega
    obtain ⟨L, hpos, hsum, hnp⟩ := ih (d - 3) (by omega) (by omega) ⟨by omega, by omega, by omega⟩
    refine ⟨3 :: L, ?_, ?_, ?_⟩
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · omega
      · exact hpos x hx
    · simp only [List.sum_cons, hsum]
      omega
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact not_isPow2_three
      · exact hnp x hx

/-- Exact number-theoretic classification of covering degrees with universal power-of-two
orbit lifting: every positive integer partition of `d` contains a power of 2 if and only if
`d ∈ {1, 2, 4}`. -/
theorem partition_has_pow2_iff_one_two_four (d : ℕ) (hd : 1 ≤ d) :
    (∀ L : List ℕ, (∀ x ∈ L, 1 ≤ x) → L.sum = d → ∃ x ∈ L, IsPow2 x) ↔
      d = 1 ∨ d = 2 ∨ d = 4 := by
  constructor
  · intro hall
    by_contra hne
    have hne' : d ≠ 1 ∧ d ≠ 2 ∧ d ≠ 4 := ⟨fun h => hne (Or.inl h),
      fun h => hne (Or.inr (Or.inl h)), fun h => hne (Or.inr (Or.inr h))⟩
    obtain ⟨L, hpos, hsum, hnp⟩ := exists_nonpow2_partition d hd hne'
    obtain ⟨x, hxL, hx2⟩ := hall L hpos hsum
    exact hnp x hxL hx2
  · intro hd_cases L hpos hsum
    by_contra hno
    have hge3 : ∀ x ∈ L, x = 3 ∨ 5 ≤ x := by
      intro x hx
      have hx1 : 1 ≤ x := hpos x hx
      have h1 : x ≠ 1 := fun h => hno ⟨x, hx, 0, by simpa using h⟩
      have h2 : x ≠ 2 := fun h => hno ⟨x, hx, 1, by simpa using h⟩
      have h4 : x ≠ 4 := fun h => hno ⟨x, hx, 2, by simpa using h⟩
      omega
    match L with
    | [] => simp at hsum; omega
    | [a] =>
      simp only [List.sum_cons, List.sum_nil, add_zero] at hsum
      have ha := hge3 a (by simp)
      omega
    | a :: b :: rest =>
      simp only [List.sum_cons] at hsum
      have ha := hge3 a (by simp)
      have hb := hge3 b (by simp)
      omega

/-! ## Part 2: Non-Galois `d`-Sheeted Covering Safe Descent (`d ∈ {1, 2, 4}`) -/

/-- A `d`-sheeted graph covering map `G → H` (locally bijective graph homomorphism with
constant fiber size `d`). Requires NO automorphism of `G` (includes non-Galois covers). -/
structure GraphCover {V W : Type u} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (d : ℕ) where
  toFun : V → W
  map_adj : ∀ {u v : V}, G.Adj u v → H.Adj (toFun u) (toFun v)
  unique_lift : ∀ (u : V) {w : W}, H.Adj (toFun u) w → ∃! v : V, G.Adj u v ∧ toFun v = w
  fiber_card : ∀ w : W, Nat.card {u : V // toFun u = w} = d

namespace GraphCover

variable {V W : Type u} [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W} {d : ℕ}

noncomputable def liftStep (cov : GraphCover G H d) (u : V) {w : W}
    (h : H.Adj (cov.toFun u) w) : V :=
  (cov.unique_lift u h).choose

lemma liftStep_adj (cov : GraphCover G H d) (u : V) {w : W} (h : H.Adj (cov.toFun u) w) :
    G.Adj u (cov.liftStep u h) :=
  (cov.unique_lift u h).choose_spec.1.1

lemma liftStep_proj (cov : GraphCover G H d) (u : V) {w : W} (h : H.Adj (cov.toFun u) w) :
    cov.toFun (cov.liftStep u h) = w :=
  (cov.unique_lift u h).choose_spec.1.2

lemma liftStep_unique (cov : GraphCover G H d) (u : V) {w : W} (h : H.Adj (cov.toFun u) w)
    {v : V} (hadj : G.Adj u v) (hproj : cov.toFun v = w) :
    v = cov.liftStep u h :=
  (cov.unique_lift u h).choose_spec.2 v ⟨hadj, hproj⟩

/-- Unique lifting of any walk in `H` starting from a fiber point `u` above `a`. -/
noncomputable def liftWalk (cov : GraphCover G H d) :
    ∀ {a b : W}, H.Walk a b → (u : V) → cov.toFun u = a →
      Σ' (v : V), G.Walk u v ×' (cov.toFun v = b)
  | _, _, .nil, u, hu => ⟨u, .nil, hu⟩
  | _, _, .cons (v := c) h q, u, hu =>
    let h' : H.Adj (cov.toFun u) c := hu.symm ▸ h
    let u1 := cov.liftStep u h'
    let hu1 : cov.toFun u1 = c := cov.liftStep_proj u h'
    let res := cov.liftWalk q u1 hu1
    ⟨res.1, .cons (cov.liftStep_adj u h') res.2.1, res.2.2⟩

lemma liftWalk_length (cov : GraphCover G H d) {a b : W} (p : H.Walk a b)
    (u : V) (hu : cov.toFun u = a) :
    (cov.liftWalk p u hu).2.1.length = p.length := by
  induction p generalizing u with
  | nil => rfl
  | cons h q ih =>
    simp only [liftWalk, Walk.length_cons]
    rw [ih]

lemma liftWalk_support_map (cov : GraphCover G H d) {a b : W} (p : H.Walk a b)
    (u : V) (hu : cov.toFun u = a) :
    (cov.liftWalk p u hu).2.1.support.map cov.toFun = p.support := by
  induction p generalizing u with
  | nil => simp [liftWalk, hu]
  | cons h q ih =>
    simp only [liftWalk, Walk.support_cons, List.map_cons, hu]
    congr 1
    exact ih _ _

lemma liftWalk_append (cov : GraphCover G H d) {a b c : W}
    (p : H.Walk a b) (q : H.Walk b c) (u : V) (hu : cov.toFun u = a) :
    (cov.liftWalk (p.append q) u hu).1 =
      (cov.liftWalk q (cov.liftWalk p u hu).1 (cov.liftWalk p u hu).2.2).1 := by
  induction p generalizing u with
  | nil => rfl
  | cons h p' ih =>
    simp only [Walk.cons_append, liftWalk]
    exact ih q _ _

lemma liftWalk_reverse_endpoint (cov : GraphCover G H d) {a b : W} (p : H.Walk a b)
    (u : V) (hu : cov.toFun u = a) :
    (cov.liftWalk p.reverse (cov.liftWalk p u hu).1 (cov.liftWalk p u hu).2.2).1 = u := by
  induction p generalizing u with
  | nil => rfl
  | cons h q ih =>
    let u1 := cov.liftStep u (hu.symm ▸ h)
    have hu1 : cov.toFun u1 = _ := cov.liftStep_proj u (hu.symm ▸ h)
    have hq := ih u1 hu1
    have hrev : (Walk.cons h q).reverse = q.reverse.append (Walk.cons h.symm Walk.nil) :=
      Walk.reverse_cons h q
    change (cov.liftWalk (Walk.cons h q).reverse
      (cov.liftWalk q u1 hu1).1 (cov.liftWalk q u1 hu1).2.2).1 = u
    rw [hrev, cov.liftWalk_append]
    simp only [liftWalk]
    symm
    apply cov.liftStep_unique
    · rw [hq]
      exact (cov.liftStep_adj u (hu.symm ▸ h)).symm
    · exact hu

/-- Monodromy permutation on the fiber over `w₀` induced by lifting a closed walk `c`. -/
noncomputable def monodromy (cov : GraphCover G H d) {w₀ : W} (c : H.Walk w₀ w₀) :
    Equiv.Perm {u : V // cov.toFun u = w₀} where
  toFun u := ⟨(cov.liftWalk c u.1 u.2).1, (cov.liftWalk c u.1 u.2).2.2⟩
  invFun u := ⟨(cov.liftWalk c.reverse u.1 u.2).1, (cov.liftWalk c.reverse u.1 u.2).2.2⟩
  left_inv u := by
    apply Subtype.ext
    exact cov.liftWalk_reverse_endpoint c u.1 u.2
  right_inv u := by
    apply Subtype.ext
    have h := cov.liftWalk_reverse_endpoint c.reverse u.1 u.2
    simpa only [Walk.reverse_reverse] using h

/-- Iterated lift of a closed walk `c` repeated `r` times from a fiber point `u`. -/
noncomputable def liftRepeat (cov : GraphCover G H d) {w₀ : W} (c : H.Walk w₀ w₀) :
    ∀ (r : ℕ) (u : {x : V // cov.toFun x = w₀}),
      G.Walk u.1 (((cov.monodromy c) ^ r) u).1
  | 0, _ => .nil
  | r + 1, u =>
    let step := cov.liftWalk c u.1 u.2
    let u1 : {x : V // cov.toFun x = w₀} := ⟨step.1, step.2.2⟩
    have hpow : (((cov.monodromy c) ^ r) u1).1 = (((cov.monodromy c) ^ (r + 1)) u).1 := by
      rw [pow_succ, Equiv.Perm.mul_apply]
      rfl
    step.2.1.append ((cov.liftRepeat c r u1).copy rfl hpow)

lemma liftRepeat_length (cov : GraphCover G H d) {w₀ : W} (c : H.Walk w₀ w₀)
    (r : ℕ) (u : {x : V // cov.toFun x = w₀}) :
    (cov.liftRepeat c r u).length = r * c.length := by
  induction r generalizing u with
  | zero =>
    simp only [liftRepeat, zero_mul]
    rfl
  | succ r ih =>
    simp only [liftRepeat, Walk.length_append, Walk.length_copy]
    rw [cov.liftWalk_length c u.1 u.2, ih]
    ring

lemma liftWalk_support_tail_nodup_of_cycle (cov : GraphCover G H d) {w₀ : W}
    (c : H.Walk w₀ w₀) (hc : c.IsCycle) (u : {x : V // cov.toFun x = w₀}) :
    (cov.liftWalk c u.1 u.2).2.1.support.tail.Nodup := by
  have hm : ((cov.liftWalk c u.1 u.2).2.1.support.tail).map cov.toFun = c.support.tail := by
    have h := congrArg List.tail (cov.liftWalk_support_map c u.1 u.2)
    simpa [List.map_tail] using h
  have hnd : (((cov.liftWalk c u.1 u.2).2.1.support.tail).map cov.toFun).Nodup := by
    rw [hm]; exact hc.support_nodup
  exact List.Nodup.of_map cov.toFun hnd

lemma liftWalk_support_tail_mem_proj (cov : GraphCover G H d) {w₀ : W}
    (c : H.Walk w₀ w₀) (hc : c.IsCycle) (u v : {x : V // cov.toFun x = w₀})
    (x : V)
    (hx1 : x ∈ (cov.liftWalk c u.1 u.2).2.1.support.tail)
    (hx2 : x ∈ (cov.liftWalk c v.1 v.2).2.1.support.tail) :
    u = v := by
  classical
  let q1 := (cov.liftWalk c u.1 u.2).2.1
  let q2 := (cov.liftWalk c v.1 v.2).2.1
  have hmap1 : q1.support.map cov.toFun = c.support := cov.liftWalk_support_map c u.1 u.2
  have hmap2 : q2.support.map cov.toFun = c.support := cov.liftWalk_support_map c v.1 v.2
  have htail1 : q1.support.tail.map cov.toFun = c.support.tail := by
    have h := congrArg List.tail hmap1; simpa [List.map_tail] using h
  have htail2 : q2.support.tail.map cov.toFun = c.support.tail := by
    have h := congrArg List.tail hmap2; simpa [List.map_tail] using h
  obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.mp hx1
  obtain ⟨j, hj, hxj⟩ := List.mem_iff_getElem.mp hx2
  have hlen1 : q1.support.tail.length = c.support.tail.length := by
    rw [← htail1, List.length_map]
  have hlen2 : q2.support.tail.length = c.support.tail.length := by
    rw [← htail2, List.length_map]
  have hi_c : i < c.support.tail.length := hlen1 ▸ hi
  have hj_c : j < c.support.tail.length := hlen2 ▸ hj
  have hci : c.support.tail[i]'hi_c = cov.toFun x := by
    have hget : (q1.support.tail.map cov.toFun)[i]'(by rw [List.length_map]; exact hi) =
        c.support.tail[i]'hi_c := by
      simp only [htail1]
    rw [← hget, List.getElem_map, hxi]
  have hcj : c.support.tail[j]'hj_c = cov.toFun x := by
    have hget : (q2.support.tail.map cov.toFun)[j]'(by rw [List.length_map]; exact hj) =
        c.support.tail[j]'hj_c := by
      simp only [htail2]
    rw [← hget, List.getElem_map, hxj]
  have hij : i = j := by
    have hnd := List.nodup_iff_injective_getElem.mp hc.support_nodup
    have heq : (⟨i, hi_c⟩ : Fin c.support.tail.length) = ⟨j, hj_c⟩ :=
      hnd (hci.trans hcj.symm)
    exact congrArg Fin.val heq
  have hback : ∀ {a b : W} (p : H.Walk a b) (u1 u2 : V) (hu1 : cov.toFun u1 = a) (hu2 : cov.toFun u2 = a)
      (k : ℕ) (hk : k ≤ p.length),
      (cov.liftWalk p u1 hu1).2.1.getVert k = (cov.liftWalk p u2 hu2).2.1.getVert k → u1 = u2 := by
    intro a b p
    induction p with
    | nil =>
      intro u1 u2 hu1 hu2 k hk heq
      have hk0 : k = 0 := by simp at hk; omega
      subst hk0
      simpa [liftWalk] using heq
    | cons h p' ih =>
      intro u1 u2 hu1 hu2 k hk heq
      cases k with
      | zero => simpa [liftWalk] using heq
      | succ k' =>
        simp only [liftWalk, Walk.getVert_cons_succ] at heq
        have hstep : cov.liftStep u1 (hu1.symm ▸ h) = cov.liftStep u2 (hu2.symm ▸ h) :=
          ih _ _ _ _ k' (by simp at hk; omega) heq
        let s := cov.liftStep u1 (hu1.symm ▸ h)
        have hs_proj : cov.toFun s = _ := cov.liftStep_proj u1 (hu1.symm ▸ h)
        have hadj2 : G.Adj s u2 := by
          have hs_eq : s = cov.liftStep u2 (hu2.symm ▸ h) := hstep
          rw [hs_eq]
          exact (cov.liftStep_adj u2 (hu2.symm ▸ h)).symm
        have hback1 : u1 = cov.liftStep s (hs_proj.symm ▸ h.symm) :=
          cov.liftStep_unique s (hs_proj.symm ▸ h.symm) (cov.liftStep_adj u1 (hu1.symm ▸ h)).symm hu1
        have hback2 : u2 = cov.liftStep s (hs_proj.symm ▸ h.symm) :=
          cov.liftStep_unique s (hs_proj.symm ▸ h.symm) hadj2 hu2
        exact hback1.trans hback2.symm
  apply Subtype.ext
  have hk : i + 1 ≤ c.length := by
    have hcl : c.support.tail.length = c.length := by
      rw [List.length_tail, Walk.length_support]; omega
    omega
  apply hback c u.1 v.1 u.2 v.2 (i + 1) hk
  have hg1 : q1.getVert (i + 1) = x := by
    rw [Walk.getVert_eq_support_getElem _ (by rw [cov.liftWalk_length]; exact hk)]
    rw [← List.getElem_tail (h := hi)]
    exact hxi
  have hi2 : i < q2.support.tail.length := by rw [hlen2, ← hlen1]; exact hi
  have hg2 : q2.getVert (i + 1) = x := by
    rw [Walk.getVert_eq_support_getElem _ (by rw [cov.liftWalk_length]; exact hk)]
    rw [← List.getElem_tail (h := hi2)]
    simpa [hij] using hxj
  exact hg1.trans hg2.symm

lemma liftRepeat_support_tail_nodup (cov : GraphCover G H d) {w₀ : W}
    (c : H.Walk w₀ w₀) (hc : c.IsCycle)
    (r : ℕ) (u : {x : V // cov.toFun x = w₀})
    (hinj : ∀ i j : ℕ, i < r → j < r → ((cov.monodromy c) ^ i) u = ((cov.monodromy c) ^ j) u → i = j) :
    (cov.liftRepeat c r u).support.tail.Nodup ∧
      ∀ x ∈ (cov.liftRepeat c r u).support.tail,
        ∃ i < r, x ∈ (cov.liftWalk c (((cov.monodromy c) ^ i) u).1 (((cov.monodromy c) ^ i) u).2).2.1.support.tail := by
  induction r generalizing u with
  | zero =>
    change ([] : List V).Nodup ∧
      ∀ x ∈ ([] : List V), ∃ i < 0, x ∈ (cov.liftWalk c (((cov.monodromy c) ^ i) u).1 (((cov.monodromy c) ^ i) u).2).2.1.support.tail
    exact ⟨List.nodup_nil, fun _ h => nomatch h⟩
  | succ r ih =>
    let step := cov.liftWalk c u.1 u.2
    let u1 : {x : V // cov.toFun x = w₀} := ⟨step.1, step.2.2⟩
    have hu1_eq : (cov.monodromy c) u = u1 := rfl
    have hpow_step : ∀ i : ℕ, ((cov.monodromy c) ^ (i + 1)) u = ((cov.monodromy c) ^ i) u1 := by
      intro i
      rw [pow_succ, Equiv.Perm.mul_apply, hu1_eq]
    have hinj1 : ∀ i j : ℕ, i < r → j < r → ((cov.monodromy c) ^ i) u1 = ((cov.monodromy c) ^ j) u1 → i = j := by
      intro i j hi hj heq
      have h1 : ((cov.monodromy c) ^ (i + 1)) u = ((cov.monodromy c) ^ (j + 1)) u := by
        rw [hpow_step i, hpow_step j, heq]
      have := hinj (i + 1) (j + 1) (by omega) (by omega) h1
      omega
    obtain ⟨hnd_rest, hmem_rest⟩ := ih u1 hinj1
    have hsupp_tail : (cov.liftRepeat c (r + 1) u).support.tail =
        step.2.1.support.tail ++ (cov.liftRepeat c r u1).support.tail := by
      simp only [liftRepeat, Walk.support_append, Walk.support_copy]
      cases hs : step.2.1.support with
      | nil => exact absurd hs (Walk.support_ne_nil _)
      | cons hd tl =>
        simp only [List.tail_cons, List.cons_append]
        rfl
    rw [hsupp_tail]
    have hnd_step : step.2.1.support.tail.Nodup := cov.liftWalk_support_tail_nodup_of_cycle c hc u
    have hdisj : step.2.1.support.tail.Disjoint (cov.liftRepeat c r u1).support.tail := by
      intro x hx1 hx2
      obtain ⟨i, hi, hxi⟩ := hmem_rest x hx2
      have hu_eq : u = ((cov.monodromy c) ^ i) u1 :=
        cov.liftWalk_support_tail_mem_proj c hc u (((cov.monodromy c) ^ i) u1) x hx1 hxi
      have h0 : ((cov.monodromy c) ^ 0) u = ((cov.monodromy c) ^ (i + 1)) u := by
        rw [pow_zero, Equiv.Perm.one_apply, hpow_step i, hu_eq]
      have := hinj 0 (i + 1) (by omega) (by omega) h0
      omega
    refine ⟨List.nodup_append'.mpr ⟨hnd_step, hnd_rest, hdisj⟩, ?_⟩
    have hmem_congr : ∀ {a b : {y : V // cov.toFun y = w₀}} {x : V}, a = b →
        x ∈ (cov.liftWalk c a.1 a.2).2.1.support.tail →
        x ∈ (cov.liftWalk c b.1 b.2).2.1.support.tail := by
      rintro a _ x rfl h; exact h
    intro x hx
    rcases List.mem_append.mp hx with hx1 | hx2
    · exact ⟨0, by omega, hmem_congr (by rw [pow_zero, Equiv.Perm.one_apply]) hx1⟩
    · obtain ⟨i, hi, hxi⟩ := hmem_rest x hx2
      exact ⟨i + 1, by omega, hmem_congr (hpow_step i).symm hxi⟩

/-- On any finite type of cardinality `d ∈ {1, 2, 4}`, every permutation has an element
whose minimal positive return time is a power of 2 (`1`, `2`, or `4`). -/
private lemma exists_pow2_orbit_of_card_one_two_four {α : Type*} [Fintype α] [DecidableEq α]
    (e : Equiv.Perm α) (hd : Fintype.card α = 1 ∨ Fintype.card α = 2 ∨ Fintype.card α = 4) :
    ∃ (a : α) (r m : ℕ), 1 ≤ r ∧ r = 2 ^ m ∧ (e ^ r) a = a ∧
      ∀ i j : ℕ, i < r → j < r → (e ^ i) a = (e ^ j) a → i = j := by
  classical
  have hne : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨a⟩ := hne
  have hex : ∃ k : ℕ, 0 < k ∧ (e ^ k) a = a := by
    refine ⟨Fintype.card (Equiv.Perm α), Fintype.card_pos, ?_⟩
    rw [pow_card_eq_one, Equiv.Perm.one_apply]
  let r := Nat.find hex
  have hr_spec : 0 < r ∧ (e ^ r) a = a := Nat.find_spec hex
  have hr_min : ∀ k, 0 < k → (e ^ k) a = a → r ≤ k := fun k hk hper => Nat.find_min' hex ⟨hk, hper⟩
  have hinj_a : ∀ i j : ℕ, i < r → j < r → (e ^ i) a = (e ^ j) a → i = j := by
    intro i j hi hj hij
    by_contra hne_ij
    wlog hlt : i < j
    · exact this e hd a hex hr_spec hr_min j i hj hi hij.symm (Ne.symm hne_ij) (by omega)
    have hper : (e ^ (j - i)) a = a := by
      have h1 : (e ^ i) ((e ^ (j - i)) a) = (e ^ i) a := by
        rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hlt)]
        exact hij.symm
      exact (e ^ i).injective h1
    have hmin := hr_min (j - i) (by omega) hper
    omega
  have hle : r ≤ Fintype.card α := by
    let f : Fin r → α := fun i => (e ^ (i : ℕ)) a
    have hf : Function.Injective f := fun i j hij => Fin.ext (hinj_a i j i.2 j.2 hij)
    simpa using Fintype.card_le_of_injective f hf
  by_cases h1 : r = 1
  · exact ⟨a, r, 0, by omega, by simpa using h1, hr_spec.2, hinj_a⟩
  by_cases h2 : r = 2
  · exact ⟨a, r, 1, by omega, by simpa using h2, hr_spec.2, hinj_a⟩
  by_cases h4 : r = 4
  · exact ⟨a, r, 2, by omega, by simpa using h4, hr_spec.2, hinj_a⟩
  have hr3 : r = 3 := by omega
  have hc4 : Fintype.card α = 4 := by omega
  have h01 : a ≠ e a := by
    intro h
    have := hr_min 1 (by decide) (by simpa using h.symm)
    omega
  have h02 : a ≠ e (e a) := by
    intro h
    have := hr_min 2 (by decide) (by simpa [pow_two, Equiv.Perm.mul_apply] using h.symm)
    omega
  have h12 : e a ≠ e (e a) := fun h => h01 (e.injective h)
  have h3 : e (e (e a)) = a := by
    have hp : (e ^ 3) a = a := hr3 ▸ hr_spec.2
    simpa [pow_succ, pow_zero, Equiv.Perm.mul_apply] using hp
  let orb : Finset α := {a, e a, e (e a)}
  have horb_exact : orb.card = 3 := by
    simp [orb, h01, h02, h12]
  have hex_b : ∃ b : α, b ∉ orb := by
    by_contra hall
    have hsub : (Finset.univ : Finset α) ⊆ orb := fun x _ => by
      by_contra hx; exact hall ⟨x, hx⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, hc4, horb_exact] at this
    omega
  obtain ⟨b, hb⟩ := hex_b
  have heb_not : e b ∉ orb := by
    intro hmem
    simp only [orb, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h
    · have : b = e (e a) := e.injective (h.trans h3.symm)
      exact hb (by simp [orb, this])
    · have : b = a := e.injective h
      exact hb (by simp [orb, this])
    · have : b = e a := e.injective h
      exact hb (by simp [orb, this])
  have heb : e b = b := by
    have huniv : insert b orb = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_insert_of_notMem hb, horb_exact, hc4]
    have hmem : e b ∈ insert b orb := by rw [huniv]; exact Finset.mem_univ _
    simp only [Finset.mem_insert] at hmem
    exact hmem.resolve_right heb_not
  refine ⟨b, 1, 0, by decide, by decide, by simpa using heb, ?_⟩
  intro i j hi hj _
  omega

/-- **Non-Galois 2- and 4-Sheeted Covering Power-Cycle Lift Theorem**:
For ANY `d`-sheeted graph covering `G → H` with `d ∈ {1, 2, 4}` (requiring no
automorphisms of `G`), every power-of-two cycle in `H` lifts to a power-of-two cycle in `G`. -/
theorem covering_lift_power_cycle_of_degree_two_or_four
    (cov : GraphCover G H d) (hd : d = 1 ∨ d = 2 ∨ d = 4) :
    HasPower H → HasPower G := by
  classical
  rintro ⟨k, w₀, c, hk, hc, hlen⟩
  let e := cov.monodromy c
  have hcard : Fintype.card {u : V // cov.toFun u = w₀} = 1 ∨
      Fintype.card {u : V // cov.toFun u = w₀} = 2 ∨
      Fintype.card {u : V // cov.toFun u = w₀} = 4 := by
    have hc' := cov.fiber_card w₀
    rw [Nat.card_eq_fintype_card] at hc'
    rw [hc']
    exact hd
  obtain ⟨u, r, m, hr_pos, hr_pow, hper, hinj⟩ :=
    exists_pow2_orbit_of_card_one_two_four e hcard
  let w_raw := cov.liftRepeat c r u
  have hend : (((cov.monodromy c) ^ r) u).1 = u.1 := congrArg Subtype.val hper
  let w : G.Walk u.1 u.1 := w_raw.copy rfl hend
  have hw_len : w.length = 2 ^ (k + m) := by
    simp only [w, Walk.length_copy, w_raw]
    rw [cov.liftRepeat_length c r u, hlen, hr_pow, pow_add, Nat.mul_comm]
  have hw_tail_nodup : w.support.tail.Nodup := by
    simp only [w, Walk.support_copy, w_raw]
    exact (cov.liftRepeat_support_tail_nodup c hc r u hinj).1
  have hw_len3 : 3 ≤ w.length := by
    rw [hw_len]
    have h4 : 4 ≤ 2 ^ (k + m) := by
      have h1 : 1 ≤ 2 ^ (k + m - 2) := Nat.one_le_pow _ 2 (by decide)
      calc 4 = 2 ^ 2 * 1 := by decide
        _ ≤ 2 ^ 2 * 2 ^ (k + m - 2) := Nat.mul_le_mul_left 4 h1
        _ = 2 ^ (2 + (k + m - 2)) := (pow_add 2 2 _).symm
        _ = 2 ^ (k + m) := by congr 1; omega
    omega
  have hw_nnil : ¬ w.Nil := by
    intro h
    have := Walk.length_eq_zero_iff.mpr h
    omega
  refine ⟨k + m, u.1, w, by omega, ?_, hw_len⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  refine ⟨Walk.IsPath.mk' ?_, hw_len3⟩
  rwa [Walk.support_tail_of_not_nil _ hw_nnil]

lemma card_eq_mul_fiber (cov : GraphCover G H d) :
    Fintype.card V = d * Fintype.card W := by
  classical
  have hsum : Fintype.card V = ∑ w : W, Fintype.card {u : V // cov.toFun u = w} := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr
      { toFun := fun u => ⟨cov.toFun u, ⟨u, rfl⟩⟩
        invFun := fun p => p.2.1
        left_inv := fun _ => rfl
        right_inv := fun ⟨_, ⟨_, rfl⟩⟩ => rfl }
  rw [hsum]
  have hf : ∀ w : W, Fintype.card {u : V // cov.toFun u = w} = d := by
    intro w
    have := cov.fiber_card w
    rwa [Nat.card_eq_fintype_card] at this
  simp only [hf, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm]

end GraphCover

/-- Unconditional across all 13 remaining leaves (`C`, `S`, `H`): no `MinimalBad` graph
admits a 2-sheeted or 4-sheeted (even non-Galois) covering map onto a `Near` graph. -/
theorem minimal_bad_no_two_or_four_cover {V W : Type u} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hm : MinimalBad G) (d : ℕ) (hd : d = 2 ∨ d = 4)
    (cov : GraphCover G H d) (hnH : Near H) : False := by
  have hcardV : Fintype.card V = d * Fintype.card W := cov.card_eq_mul_fiber
  have hWpos : 0 < Fintype.card W := by
    obtain ⟨w, _⟩ := hnH.1
    exact Fintype.card_pos_iff.mpr ⟨w⟩
  have hlt : Fintype.card W < Fintype.card V := by
    rw [hcardV]
    rcases hd with rfl | rfl <;> omega
  have hpowH : HasPower H := hm.2.2.1 W H hlt hnH
  exact hm.2.1 (cov.covering_lift_power_cycle_of_degree_two_or_four (Or.inr hd) hpowH)

/-- **Whole-Problem Closure Gate**: If every power-free `Near` graph admits a 2- or 4-sheeted
covering quotient (or any `SafeStep`), then the FULL Erdős #64 conjecture is CLOSED. -/
theorem erdos64_of_global_two_or_four_cover
    (hcov : ∀ (V : Type u) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
      Near G → ¬ HasPower G →
      (∃ (W : Type u) (H : SimpleGraph W) (_ : Fintype W) (_ : DecidableRel H.Adj)
        (d : ℕ), (d = 2 ∨ d = 4) ∧ Nonempty (GraphCover G H d) ∧ Near H) ∨ SafeStep G) :
    ∀ (V : Type u) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
      G.minDegree ≥ 3 → ∃ (k : ℕ) (v : V) (c : G.Walk v v),
        k ≥ 2 ∧ c.IsCycle ∧ c.length = 2 ^ k := by
  apply erdos64_of_global_descent
  intro V G instV instG hnear hnot
  rcases hcov V G hnear hnot with ⟨W, H, fw, dh, d, hd, ⟨cov⟩, hnH⟩ | hsafe
  · let _ : Fintype W := fw
    let _ : DecidableRel H.Adj := dh
    have hcardV : Fintype.card V = d * Fintype.card W := cov.card_eq_mul_fiber
    have hWpos : 0 < Fintype.card W := by
      obtain ⟨w, _⟩ := hnH.1
      exact Fintype.card_pos_iff.mpr ⟨w⟩
    have hlt : Fintype.card W < Fintype.card V := by
      rw [hcardV]; rcases hd with rfl | rfl <;> omega
    exact ⟨W, H, fw, dh, hlt, hnH,
      cov.covering_lift_power_cycle_of_degree_two_or_four (Or.inr hd)⟩
  · exact hsafe

/-! ## Part 3: All-13-Leaves Global 2-Independent-Set Contraction Theorem -/

/-- A 2-independent set in `G`: pairwise nonadjacent and sharing no common neighbor
(equivalently, pairwise graph distance at least 3). -/
def IsTwoIndep {V : Type u} (G : SimpleGraph V) (I : Finset V) : Prop :=
  ∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬ G.Adj u v ∧ ∀ z : V, ¬ (G.Adj u z ∧ G.Adj v z)

/-- Quotient graph `G / I` obtained by contracting a 2-independent set `I` into `none`. -/
def contractTwoIndep {V : Type u} (G : SimpleGraph V) (I : Finset V) :
    SimpleGraph (Option {x : V // x ∉ I}) where
  Adj a b :=
    match a, b with
    | none, none => False
    | none, some y => ∃ u ∈ I, G.Adj u y.1
    | some x, none => ∃ u ∈ I, G.Adj x.1 u
    | some x, some y => G.Adj x.1 y.1
  symm := ⟨by
    intro a b h
    cases a <;> cases b <;> simp_all only
    · obtain ⟨u, hu, hadj⟩ := h; exact ⟨u, hu, hadj.symm⟩
    · obtain ⟨u, hu, hadj⟩ := h; exact ⟨u, hu, hadj.symm⟩
    · exact h.symm⟩
  loopless := ⟨by
    intro a
    cases a with
    | none => simp
    | some x => exact G.loopless.irrefl x.1⟩

private lemma lift_walk_no_none {V : Type u} [DecidableEq V] (G : SimpleGraph V) (I : Finset V)
    {a b : Option {x : V // x ∉ I}} (p : (contractTwoIndep G I).Walk a b)
    (hno : none ∉ p.support) :
    ∀ (x y : {z : V // z ∉ I}), a = some x → b = some y →
      ∃ q : G.Walk x.1 y.1,
        q.length = p.length ∧
        q.support.map (fun z => if h : z ∉ I then some ⟨z, h⟩ else none) = p.support ∧
        ∀ z ∈ q.support, z ∉ I := by
  induction p with
  | nil =>
    intro x y hx hy
    have hxy : x = y := Option.some.inj (hx.symm.trans hy)
    subst hxy
    refine ⟨.nil, rfl, ?_, ?_⟩
    · simp [hx, x.2]
    · simp [x.2]
  | @cons a b c' hadj q ih =>
    intro x y hx hy
    subst hx
    cases b with
    | none =>
      exfalso
      exact hno (by simp [Walk.support_cons])
    | some b' =>
      have hno_q : none ∉ q.support := fun h => hno (by simp [Walk.support_cons, h])
      obtain ⟨q', hql, hqs, hqi⟩ := ih hno_q b' y rfl hy
      have hadjG : G.Adj x.1 b'.1 := hadj
      refine ⟨Walk.cons hadjG q', ?_, ?_, ?_⟩
      · simp [hql]
      · simp only [Walk.support_cons, List.map_cons]
        rw [hqs]
        simp [x.2]
      · intro z hz
        simp only [Walk.support_cons, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact x.2
        · exact hqi z hz

/-- **All-13-Leaves Global 2-Independent-Set Contraction Theorem**:
In EVERY `MinimalBad` graph `G` (cubic `C`, `S`, or `H` — all 13 remaining leaves),
for EVERY 2-independent set `I` with `|I| ≥ 2`, there exist distinct `u, v ∈ I` and
a simple `u`–`v` path of length `2^k` (`k ≥ 2`) whose internal vertices are disjoint from `I`. -/
theorem minimal_bad_two_indep_avoiding_dyadic_path
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hm : MinimalBad G) (I : Finset V) (hI2 : 2 ≤ I.card) (hI : IsTwoIndep G I) :
    ∃ (u v : V) (k : ℕ) (p : G.Walk u v),
      u ∈ I ∧ v ∈ I ∧ u ≠ v ∧ 2 ≤ k ∧ p.IsPath ∧ p.length = 2 ^ k ∧
      ∀ z ∈ p.support.tail.dropLast, z ∉ I := by
  classical
  let W := Option {x : V // x ∉ I}
  let H := contractTwoIndep G I
  let _ : DecidableRel H.Adj := Classical.decRel _
  have hcardW : Fintype.card W < Fintype.card V := by
    have hcomp : Fintype.card {x : V // x ∉ I} + I.card = Fintype.card V := by
      rw [Fintype.card_subtype_compl]
      have : Fintype.card {x : V // x ∈ I} = I.card := Fintype.card_coe I
      rw [this]
      exact Nat.sub_add_cancel (Finset.card_le_univ I)
    simp only [W, Fintype.card_option]
    omega
  have hdeg_some : ∀ x : {z : V // z ∉ I}, H.degree (some x) = G.degree x.1 := by
    intro x
    rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
    have huniq : ∀ u₁ ∈ I, ∀ u₂ ∈ I, G.Adj x.1 u₁ → G.Adj x.1 u₂ → u₁ = u₂ := by
      intro u₁ hu₁ u₂ hu₂ h1 h2
      by_contra hne
      exact (hI u₁ hu₁ u₂ hu₂ hne).2 x.1 ⟨h1.symm, h2.symm⟩
    refine (Fintype.card_congr
      { toFun := fun p =>
          if h : p.1 ∈ I then ⟨none, ⟨p.1, h, p.2⟩⟩
          else ⟨some ⟨p.1, h⟩, p.2⟩
        invFun := fun q =>
          match q with
          | ⟨none, hq⟩ => ⟨hq.choose, hq.choose_spec.2⟩
          | ⟨some y, hq⟩ => ⟨y.1, hq⟩
        left_inv := by
          intro ⟨y, hy⟩
          by_cases h : y ∈ I
          · simp only [h, ↓reduceDIte]
            apply Subtype.ext
            exact huniq _ (Exists.choose_spec (⟨y, h, hy⟩ : ∃ u ∈ I, G.Adj x.1 u)).1 y h
              (Exists.choose_spec (⟨y, h, hy⟩ : ∃ u ∈ I, G.Adj x.1 u)).2 hy
          · simp [h]
        right_inv := by
          rintro ⟨q, hq⟩
          cases q with
          | none =>
            have hc : hq.choose ∈ I := hq.choose_spec.1
            simp [hc]
          | some y =>
            simp [y.2] }).symm
  have hdeg_none : 3 ≤ H.degree none := by
    obtain ⟨w, hw⟩ := hm.1.2
    have hex_u : ∃ u ∈ I, u ≠ w := by
      by_contra hall
      have hsub : I ⊆ {w} := fun u hu => Finset.mem_singleton.mpr (by
        by_contra huw; exact hall ⟨u, hu, huw⟩)
      have := Finset.card_le_card hsub
      simp at this; omega
    obtain ⟨u, huI, huw⟩ := hex_u
    have hdu : 3 ≤ G.degree u := hw u huw
    have hsub : ∀ y ∈ G.neighborSet u, y ∉ I := by
      intro y hy hyI
      exact (hI u huI y hyI (G.ne_of_adj hy)).1 hy
    let f : G.neighborSet u → H.neighborSet none :=
      fun p => ⟨some ⟨p.1, hsub p.1 p.2⟩, ⟨u, huI, p.2⟩⟩
    have hf : Function.Injective f := by
      intro p q hpq
      have : p.1 = q.1 := by
        have := congrArg (fun r : H.neighborSet none => r.1) hpq
        simp only [f, Option.some.injEq, Subtype.mk.injEq] at this
        exact this
      exact Subtype.ext this
    have hcard := Fintype.card_le_of_injective f hf
    rw [SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.card_neighborSet_eq_degree] at hcard
    omega
  have hnearH : Near H := by
    refine ⟨⟨none, hdeg_none⟩, ?_⟩
    obtain ⟨w, hw⟩ := hm.1.2
    by_cases hwI : w ∈ I
    · refine ⟨none, fun v hv => ?_⟩
      cases v with
      | none => exact absurd rfl hv
      | some x =>
        rw [hdeg_some x]
        exact hw x.1 (fun h => x.2 (h ▸ hwI))
    · refine ⟨some ⟨w, hwI⟩, fun v hv => ?_⟩
      cases v with
      | none => exact hdeg_none
      | some x =>
        rw [hdeg_some x]
        exact hw x.1 (fun h => hv (congrArg some (Subtype.ext h)))
  obtain ⟨k, v₀, c, hk, hc, hlen⟩ := hm.2.2.1 W H hcardW hnearH
  have hnone_mem : none ∈ c.support := by
    by_contra hnot
    cases hv₀ : v₀ with
    | none => exact hnot (hv₀ ▸ Walk.start_mem_support c)
    | some x₀ =>
      obtain ⟨q, hqlen, hqsupp, _⟩ := lift_walk_no_none G I c hnot x₀ x₀ hv₀ hv₀
      have hq_tail : q.support.tail.Nodup := by
        have hm' := congrArg List.tail hqsupp
        rw [← List.map_tail] at hm'
        exact List.Nodup.of_map _ (hm'.symm ▸ hc.support_nodup)
      have hq_len3 : 3 ≤ q.length := by rw [hqlen]; exact hc.three_le_length
      have hq_nnil : ¬ q.Nil := by
        intro h; have := Walk.length_eq_zero_iff.mpr h; omega
      apply hm.2.1
      refine ⟨k, x₀.1, q, hk, ?_, hqlen.trans hlen⟩
      apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      refine ⟨Walk.IsPath.mk' ?_, hq_len3⟩
      rwa [Walk.support_tail_of_not_nil _ hq_nnil]
  let c' := c.rotate none hnone_mem
  have hc' : c'.IsCycle := hc.rotate hnone_mem
  have hc'_len : c'.length = 2 ^ k := by rw [Walk.length_rotate]; exact hlen
  cases hc'_eq : c' with
  | nil =>
    exact absurd hc'_eq hc'.ne_nil
  | @cons _ b _ h1 rest =>
    cases b with
    | none => exact False.elim h1
    | some x₁ =>
      cases hrev : rest.reverse with
      | @cons _ b2 _ h2 mid_rev =>
        cases b2 with
        | none => exact False.elim h2
        | some xₘ =>
          let mid := mid_rev.reverse
          have hrest_eq : rest = mid.append (Walk.cons h2.symm Walk.nil) := by
            have := congrArg Walk.reverse hrev
            simpa [mid, Walk.reverse_cons] using this
          have hnd_tail : (mid.support ++ [none]).Nodup := by
            have hnd : c'.support.tail.Nodup := hc'.support_nodup
            rw [hc'_eq] at hnd
            simp only [Walk.support_cons, List.tail_cons, hrest_eq, Walk.support_append,
              Walk.support_nil] at hnd
            exact hnd
          have hmid_no_none : none ∉ mid.support := by
            intro hmem
            rw [List.nodup_append] at hnd_tail
            exact hnd_tail.2.2 none hmem none (by simp) rfl
          obtain ⟨qmid, hqmid_len, hqmid_supp, hqmid_notI⟩ :=
            lift_walk_no_none G I mid hmid_no_none x₁ xₘ rfl rfl
          obtain ⟨u, huI, hux1⟩ := h1
          obtain ⟨v, hvI, hvxm⟩ := h2
          let full : G.Walk u v := Walk.cons hux1 (qmid.concat hvxm.symm)
          have hfull_len : full.length = 2 ^ k := by
            have hcl : c'.length = 2 ^ k := hc'_len
            rw [hc'_eq, hrest_eq] at hcl
            rw [Walk.length_cons, Walk.length_append, Walk.length_cons, Walk.length_nil] at hcl
            rw [show full.length = (qmid.concat hvxm.symm).length + 1 from rfl,
              Walk.length_concat, hqmid_len]
            omega
          have hqmid_nodup : qmid.support.Nodup := by
            rw [List.nodup_append] at hnd_tail
            exact List.Nodup.of_map _ (hqmid_supp.symm ▸ hnd_tail.1)
          have huv : u ≠ v := by
            intro heq
            subst heq
            have hcyc_tail : full.support.tail.Nodup := by
              simp only [full, Walk.support_cons, List.tail_cons, Walk.support_concat]
              rw [List.nodup_append]
              refine ⟨hqmid_nodup, List.nodup_singleton u, ?_⟩
              intro a ha b hb hab
              simp only [List.mem_singleton] at hb
              subst hb; subst hab
              exact hqmid_notI a ha huI
            have hlen3 : 3 ≤ full.length := by
              rw [hfull_len]
              have h4 : 4 ≤ 2 ^ k := by
                have h1p : 1 ≤ 2 ^ (k - 2) := Nat.one_le_pow _ 2 (by decide)
                calc 4 = 2 ^ 2 * 1 := by decide
                  _ ≤ 2 ^ 2 * 2 ^ (k - 2) := Nat.mul_le_mul_left 4 h1p
                  _ = 2 ^ (2 + (k - 2)) := (pow_add 2 2 _).symm
                  _ = 2 ^ k := by congr 1; omega
              omega
            have hnnil : ¬ full.Nil := by
              intro h; have := Walk.length_eq_zero_iff.mpr h; omega
            apply hm.2.1
            refine ⟨k, u, full, hk, ?_, hfull_len⟩
            apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
            refine ⟨Walk.IsPath.mk' ?_, hlen3⟩
            rwa [Walk.support_tail_of_not_nil _ hnnil]
          have hfull_path : full.IsPath := by
            apply Walk.IsPath.mk'
            simp only [full, Walk.support_cons, Walk.support_concat, List.nodup_cons]
            refine ⟨?_, ?_⟩
            · intro hmem
              rw [List.mem_append, List.mem_singleton] at hmem
              rcases hmem with hmem | hEq
              · exact hqmid_notI u hmem huI
              · exact huv hEq
            · rw [List.nodup_append]
              refine ⟨hqmid_nodup, List.nodup_singleton v, ?_⟩
              intro a ha b hb hab
              simp only [List.mem_singleton] at hb
              subst hb; subst hab
              exact hqmid_notI a ha hvI
          refine ⟨u, v, k, full, huI, hvI, huv, hk, hfull_path, hfull_len, ?_⟩
          intro z hz
          have hdl : full.support.tail.dropLast = qmid.support := by
            simp only [full, Walk.support_cons, List.tail_cons, Walk.support_concat, List.dropLast_concat]
          rw [hdl] at hz
          exact hqmid_notI z hz

#print axioms partition_has_pow2_iff_one_two_four
#print axioms GraphCover.covering_lift_power_cycle_of_degree_two_or_four
#print axioms minimal_bad_no_two_or_four_cover
#print axioms erdos64_of_global_two_or_four_cover
#print axioms minimal_bad_two_indep_avoiding_dyadic_path

end E64Wave4Agent3
