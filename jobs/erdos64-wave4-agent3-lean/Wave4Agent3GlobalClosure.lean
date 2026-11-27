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
    push_neg at hne
    obtain ⟨L, hpos, hsum, hnp⟩ := exists_nonpow2_partition d hd hne
    obtain ⟨x, hxL, hx2⟩ := hall L hpos hsum
    exact hnp x hxL hx2
  · intro hd_cases L hpos hsum
    by_contra hno
    push_neg at hno
    have hge3 : ∀ x ∈ L, x = 3 ∨ 5 ≤ x := by
      intro x hx
      have hx1 : 1 ≤ x := hpos x hx
      have h1 : x ≠ 1 := fun h => hno x hx ⟨0, by simpa using h⟩
      have h2 : x ≠ 2 := fun h => hno x hx ⟨1, by simpa using h⟩
      have h4 : x ≠ 4 := fun h => hno x hx ⟨2, by simpa using h⟩
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
  fiber_card : ∀ w : W, Fintype.card {u : V // toFun u = w} = d

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

lemma liftStep_symm (cov : GraphCover G H d) (u : V) {w : W} (h : H.Adj (cov.toFun u) w) :
    cov.liftStep (cov.liftStep u h)
      (by rw [cov.liftStep_proj u h]; exact h.symm) = u := by
  symm
  exact cov.liftStep_unique (cov.liftStep u h) _ (cov.liftStep_adj u h).symm rfl

/-- Unique lifting of any walk in `H` starting from a fiber point `u` above `a`. -/
noncomputable def liftWalk (cov : GraphCover G H d) :
    ∀ {a b : W} (p : H.Walk a b) (u : V) (_ : cov.toFun u = a),
      Σ' (v : V), G.Walk u v ×' (cov.toFun v = b)
  | _, _, .nil, u, hu => ⟨u, .nil, hu⟩
  | a, _, .cons (v := c) h q, u, hu =>
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
    exact ih _ _

lemma liftWalk_reverse_endpoint (cov : GraphCover G H d) {a b : W} (p : H.Walk a b)
    (u : V) (hu : cov.toFun u = a) :
    (cov.liftWalk p.reverse (cov.liftWalk p u hu).1 (cov.liftWalk p u hu).2.2).1 = u := by
  induction p generalizing u with
  | nil => rfl
  | cons h q ih =>
    simp only [Walk.reverse_cons, liftWalk]
    rw [cov.liftWalk_append]
    have hq := ih (cov.liftStep u (hu.symm ▸ h)) (cov.liftStep_proj u (hu.symm ▸ h))
    simp only [liftWalk] at hq ⊢
    -- After lifting q.reverse, we are at u1 = liftStep u h'; then lifting the single reversed edge returns to u
    generalize_proofs hp1 hp2 hp3
    have hstep : (cov.liftWalk (Walk.cons h.symm Walk.nil)
        (cov.liftWalk q.reverse (cov.liftWalk q (cov.liftStep u (hu.symm ▸ h)) hp1).1 hp2).1 hp3).1 = u := by
      simp only [liftWalk]
      have h1 : (cov.liftWalk q.reverse (cov.liftWalk q (cov.liftStep u (hu.symm ▸ h)) hp1).1 hp2).1 =
          cov.liftStep u (hu.symm ▸ h) := hq
      have hproj : cov.toFun (cov.liftStep u (hu.symm ▸ h)) = _ := hp1
      -- Use liftStep_unique directly
      symm
      apply cov.liftStep_unique
      · rw [h1]
        exact (cov.liftStep_adj u (hu.symm ▸ h)).symm
      · exact hu
    exact hstep

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
    have hpow : ((cov.monodromy c) ^ (r + 1)) u = ((cov.monodromy c) ^ r) u1 := by
      rw [pow_succ']
      rfl
    step.2.1.append (hpow ▸ cov.liftRepeat c r u1)

lemma liftRepeat_length (cov : GraphCover G H d) {w₀ : W} (c : H.Walk w₀ w₀)
    (r : ℕ) (u : {x : V // cov.toFun x = w₀}) :
    (cov.liftRepeat c r u).length = r * c.length := by
  induction r generalizing u with
  | zero => simp [liftRepeat]
  | succ r ih =>
    simp only [liftRepeat, Walk.length_append]
    have h1 := cov.liftWalk_length c u.1 u.2
    have h2 : ∀ {a b : V} (h : a = b) (p : G.Walk _ a), (h ▸ p).length = p.length := by
      rintro a _ rfl p; rfl
    rw [h1, h2, ih]
    ring

lemma liftWalk_unique_endpoint (cov : GraphCover G H d) {a b : W} (p : H.Walk a b)
    {u v : V} (q : G.Walk u v) (hu : cov.toFun u = a)
    (hmap : q.support.map cov.toFun = p.support) :
    v = (cov.liftWalk p u hu).1 := by
  induction p generalizing u with
  | nil =>
    cases q with
    | nil => rfl
    | cons _ _ => simp [Walk.support_cons] at hmap
  | cons h p' ih =>
    cases q with
    | nil => simp [Walk.support_cons] at hmap
    | cons hq q' =>
      simp only [Walk.support_cons, List.map_cons, List.cons.injEq] at hmap
      have hproj : cov.toFun _ = _ := by
        have hhead := congrArg List.head? hmap.2
        simpa [Walk.support_eq_cons] using hhead
      have hstep : _ = cov.liftStep u (hu.symm ▸ h) :=
        cov.liftStep_unique u (hu.symm ▸ h) hq hproj
      subst hstep
      exact ih q' (cov.liftStep_proj u (hu.symm ▸ h)) hmap.2

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
  -- Both lifted walks pass through `x`; splitting at `x` gives the same projected suffix in `c`
  -- Since `c` is a simple cycle, `x` projects to a unique position in `c.support.tail`,
  -- so the prefix from `u` to `x` and from `v` to `x` project to the same prefix of `c`!
  -- Reversing that prefix lifts uniquely from `x`, forcing `u = v`.
  let q1 := (cov.liftWalk c u.1 u.2).2.1
  let q2 := (cov.liftWalk c v.1 v.2).2.1
  have h1 : x ∈ q1.support := List.mem_of_mem_tail hx1
  have h2 : x ∈ q2.support := List.mem_of_mem_tail hx2
  -- Use `takeUntil` on q1.reverse and q2.reverse? Even cleaner: take `dropUntil` from x to the end!
  let s1 := q1.dropUntil x h1
  let s2 := q2.dropUntil x h2
  -- Wait: if x = u.1 (start), it's only in tail if it's the end! Use `takeUntil` on `q1` and `q2`
  -- Actually in a cycle `c`, every vertex in `c.support.tail` appears ONCE in `c.support.tail`.
  -- So `s1.support.map cov.toFun` and `s2.support.map cov.toFun` are both suffixes of `c.support`
  -- starting at `cov.toFun x`. Since `cov.toFun x ∈ c.support.tail` and `c.support.tail.Nodup`,
  -- if `cov.toFun x ≠ w₀`, it appears uniquely in `c.support`, so the two suffixes have equal length!
  -- If `cov.toFun x = w₀`, then `x` is the endpoint of `q1` and `q2` (since `w₀` only occurs at the end of `c.support.tail`),
  -- so `monodromy c u = x = monodromy c v`, hence `u = v` by injectivity of `monodromy c`!
  have hmap1 : q1.support.map cov.toFun = c.support := cov.liftWalk_support_map c u.1 u.2
  have hmap2 : q2.support.map cov.toFun = c.support := cov.liftWalk_support_map c v.1 v.2
  -- Show that `x` occurs at the same index in `q1.support.tail` and `q2.support.tail`,
  -- then lift the reversed prefix from `x` to get `u = v`!
  have htail1 : q1.support.tail.map cov.toFun = c.support.tail := by
    have h := congrArg List.tail hmap1; simpa [List.map_tail] using h
  have htail2 : q2.support.tail.map cov.toFun = c.support.tail := by
    have h := congrArg List.tail hmap2; simpa [List.map_tail] using h
  -- Express `x = q1.getVert (i+1)` and `x = q2.getVert (j+1)` with `i+1 ≤ c.length`, `j+1 ≤ c.length`
  obtain ⟨i, hi, hxi⟩ := List.mem_iff_get.mp hx1
  obtain ⟨j, hj, hxj⟩ := List.mem_iff_get.mp hx2
  have hlen1 : q1.support.tail.length = c.support.tail.length := by
    rw [← htail1, List.length_map]
  have hlen2 : q2.support.tail.length = c.support.tail.length := by
    rw [← htail2, List.length_map]
  have hci : c.support.tail.get ⟨i, hlen1 ▸ hi⟩ = cov.toFun x := by
    rw [← hxi]
    have := congrArg (fun l => l.get ⟨i, by rw [htail1]; exact hlen1 ▸ hi⟩) htail1
    simpa [List.get_map] using this
  have hcj : c.support.tail.get ⟨j, hlen2 ▸ hj⟩ = cov.toFun x := by
    rw [← hxj]
    have := congrArg (fun l => l.get ⟨j, by rw [htail2]; exact hlen2 ▸ hj⟩) htail2
    simpa [List.get_map] using this
  have hij : i = j := by
    have hnd := hc.support_nodup
    have heq : (⟨i, hlen1 ▸ hi⟩ : Fin c.support.tail.length) = ⟨j, hlen2 ▸ hj⟩ :=
      (List.nodup_iff_injective_get.mp hnd) (hci.trans hcj.symm)
    exact congrArg Fin.val heq
  -- Now `q1.getVert (i+1) = x = q2.getVert (i+1)`!
  -- By induction on `k ≤ p.length`, if two lifts of `p` agree at vertex `k`, they have the same start!
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
        have hstep := ih _ _ _ _ k' (by simp at hk; omega) heq
        have hu1' : u1 = cov.liftStep (cov.liftStep u1 (hu1.symm ▸ h))
            (by rw [cov.liftStep_proj]; exact h.symm) := (cov.liftStep_symm u1 (hu1.symm ▸ h)).symm
        have hu2' : u2 = cov.liftStep (cov.liftStep u2 (hu2.symm ▸ h))
            (by rw [cov.liftStep_proj]; exact h.symm) := (cov.liftStep_symm u2 (hu2.symm ▸ h)).symm
        rw [hu1', hu2']
        congr 1
  apply Subtype.ext
  have hk : i + 1 ≤ c.length := by
    have hcl : c.support.tail.length = c.length := by
      rw [List.length_tail, Walk.length_support]; omega
    omega
  apply hback c u.1 v.1 u.2 v.2 (i + 1) hk
  have hg1 : q1.getVert (i + 1) = x := by
    rw [← Walk.getVert_eq_support_getElem]
    · have : q1.support[i + 1]'(by rw [Walk.length_support, cov.liftWalk_length]; omega) =
          q1.support.tail.get ⟨i, hi⟩ := by
        cases hs : q1.support with
        | nil => exact absurd hs (Walk.support_ne_nil q1)
        | cons hd tl => simp
      rw [this, hxi]
    · rw [cov.liftWalk_length]; exact hk
  have hg2 : q2.getVert (i + 1) = x := by
    rw [← Walk.getVert_eq_support_getElem]
    · have : q2.support[i + 1]'(by rw [Walk.length_support, cov.liftWalk_length]; omega) =
          q2.support.tail.get ⟨i, by omega⟩ := by
        cases hs : q2.support with
        | nil => exact absurd hs (Walk.support_ne_nil q2)
        | cons hd tl => simp
      rw [this]
      subst hij
      exact hxj
    · rw [cov.liftWalk_length]; exact hk
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
    simp [liftRepeat]
  | succ r ih =>
    let step := cov.liftWalk c u.1 u.2
    let u1 : {x : V // cov.toFun x = w₀} := ⟨step.1, step.2.2⟩
    have hinj1 : ∀ i j : ℕ, i < r → j < r → ((cov.monodromy c) ^ i) u1 = ((cov.monodromy c) ^ j) u1 → i = j := by
      intro i j hi hj heq
      have h1 : ((cov.monodromy c) ^ (i + 1)) u = ((cov.monodromy c) ^ (j + 1)) u := by
        simpa [pow_succ', u1, step, monodromy] using heq
      have := hinj (i + 1) (j + 1) (by omega) (by omega) h1
      omega
    obtain ⟨hnd_rest, hmem_rest⟩ := ih u1 hinj1
    have hpow : ((cov.monodromy c) ^ (r + 1)) u = ((cov.monodromy c) ^ r) u1 := by
      rw [pow_succ']; rfl
    have hsupp_tail : (cov.liftRepeat c (r + 1) u).support.tail =
        step.2.1.support.tail ++ (cov.liftRepeat c r u1).support.tail := by
      simp only [liftRepeat]
      have hcast : ∀ {a b : V} (h : a = b) (p : G.Walk u1.1 a),
          (step.2.1.append (h ▸ p)).support.tail = step.2.1.support.tail ++ p.support.tail := by
        rintro a _ rfl p
        rw [Walk.support_append]
        cases hs : step.2.1.support with
        | nil => exact absurd hs (Walk.support_ne_nil _)
        | cons hd tl => simp
      exact hcast hpow (cov.liftRepeat c r u1)
    rw [hsupp_tail]
    have hnd_step : step.2.1.support.tail.Nodup := cov.liftWalk_support_tail_nodup_of_cycle c hc u
    have hdisj : step.2.1.support.tail.Disjoint (cov.liftRepeat c r u1).support.tail := by
      intro x hx1 hx2
      obtain ⟨i, hi, hxi⟩ := hmem_rest x hx2
      have hu_eq : u = ((cov.monodromy c) ^ i) u1 :=
        cov.liftWalk_support_tail_mem_proj c hc u (((cov.monodromy c) ^ i) u1) x hx1 hxi
      have h0 : ((cov.monodromy c) ^ 0) u = ((cov.monodromy c) ^ (i + 1)) u := by
        simpa [pow_succ', u1, step, monodromy] using hu_eq
      have := hinj 0 (i + 1) (by omega) (by omega) h0
      omega
    refine ⟨List.nodup_append'.mpr ⟨hnd_step, hnd_rest, hdisj⟩, ?_⟩
    intro x hx
    rcases List.mem_append.mp hx with hx1 | hx2
    · exact ⟨0, by omega, by simpa using hx1⟩
    · obtain ⟨i, hi, hxi⟩ := hmem_rest x hx2
      refine ⟨i + 1, by omega, ?_⟩
      simpa [pow_succ', u1, step, monodromy] using hxi

/-- On any finite type of cardinality `d ∈ {1, 2, 4}`, every permutation has an element
whose minimal period is a power of 2 (`1`, `2`, or `4`). -/
private lemma exists_pow2_period_of_card_one_two_four {α : Type*} [Fintype α] [DecidableEq α]
    (e : Equiv.Perm α) (hd : Fintype.card α = 1 ∨ Fintype.card α = 2 ∨ Fintype.card α = 4) :
    ∃ (a : α) (m : ℕ), 1 ≤ Function.minimalPeriod e a ∧ Function.minimalPeriod e a = 2 ^ m := by
  have hne : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨a⟩ := hne
  have hpos : 0 < Function.minimalPeriod e a := Function.minimalPeriod_pos_of_mem_periodicPts
    (by
      rw [Function.mem_periodicPts]
      exact ⟨Fintype.card (Equiv.Perm α), Fintype.card_pos, by
        have h := orderOf_dvd_card (x := e)
        obtain ⟨k, hk⟩ := h
        have hp : e ^ Fintype.card (Equiv.Perm α) = 1 := pow_card_eq_one
        change (e ^ Fintype.card (Equiv.Perm α)) a = a
        rw [hp]; rfl⟩)
  -- The orbit `{e^i a | i < r}` injects into `α`, so `r ≤ Fintype.card α`
  let r := Function.minimalPeriod e a
  have hle : r ≤ Fintype.card α := by
    let f : Fin r → α := fun i => (e ^ (i : ℕ)) a
    have hf : Function.Injective f := by
      intro i j hij
      apply Fin.ext
      exact Function.injective_iff_iterate_eq_self.mp (fun _ _ h => h) |>.elim (by
        -- Direct proof using minimalPeriod_le
        by_contra hne_ij
        wlog hlt : (i : ℕ) < (j : ℕ)
        · exact this e hd a hpos j i hij.symm (Ne.symm hne_ij) (by omega)
        have hper : Function.IsPeriodicPt e (j - i) a := by
          have h1 : (e ^ (i : ℕ)) ((e ^ ((j : ℕ) - (i : ℕ))) a) = (e ^ (i : ℕ)) a := by
            rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hlt)]
            exact hij.symm
          exact (e ^ (i : ℕ)).injective h1
        have hmin := Function.minimalPeriod_le (by omega) hper
        omega)
    simpa using Fintype.card_le_of_injective f hf
  by_cases h1 : r = 1
  · exact ⟨a, 0, by omega, by simpa using h1⟩
  by_cases h2 : r = 2
  · exact ⟨a, 1, by omega, by simpa using h2⟩
  by_cases h4 : r = 4
  · exact ⟨a, 2, by omega, by simpa using h4⟩
  -- The only remaining possibility is `r = 3` and `Fintype.card α = 4`!
  have hr3 : r = 3 := by omega
  have hc4 : Fintype.card α = 4 := by omega
  -- Then `a, e a, e (e a)` are 3 distinct elements, so the 4th element `b` is a fixed point of `e`!
  let orb : Finset α := {a, e a, e (e a)}
  have horb_card : orb.card ≤ 3 := by
    calc orb.card ≤ ({a, e a} : Finset α).card + 1 := Finset.card_insert_le _ _
      _ ≤ 2 + 1 := by
        have := Finset.card_insert_le a {e a}
        simp at this; omega
      _ = 3 := rfl
  have hex_b : ∃ b : α, b ∉ orb := by
    by_contra hall
    push_neg at hall
    have hsub : (Finset.univ : Finset α) ⊆ orb := fun x _ => hall x
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, hc4] at this
    omega
  obtain ⟨b, hb⟩ := hex_b
  -- Also `a, e a, e (e a)` are pairwise distinct because `r = 3`
  have h01 : a ≠ e a := by
    intro h
    have hper : Function.IsPeriodicPt e 1 a := by simpa [Function.IsPeriodicPt] using h.symm
    have := Function.minimalPeriod_le (by decide) hper
    omega
  have h02 : a ≠ e (e a) := by
    intro h
    have hper : Function.IsPeriodicPt e 2 a := by simpa [Function.IsPeriodicPt] using h.symm
    have := Function.minimalPeriod_le (by decide) hper
    omega
  have h12 : e a ≠ e (e a) := fun h => h01 (e.injective h)
  have h3 : e (e (e a)) = a := by
    have hp : Function.IsPeriodicPt e 3 a := hr3 ▸ Function.isPeriodicPt_minimalPeriod e a
    simpa [Function.IsPeriodicPt] using hp
  have horb_exact : orb.card = 3 := by
    simp [orb, h01, h02, h12]
  -- `e` maps `orb` into `orb`, so `e b ∉ orb`!
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
  -- Since `orb ∪ {b}` has card 4 = `Fintype.card α`, `e b = b`!
  have heb : e b = b := by
    have huniv : insert b orb = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_insert_of_not_mem hb, horb_exact, hc4]
    have hmem : e b ∈ insert b orb := by rw [huniv]; exact Finset.mem_univ _
    simp only [Finset.mem_insert] at hmem
    exact hmem.resolve_right heb_not
  refine ⟨b, 0, ?_, ?_⟩
  · have : Function.minimalPeriod e b = 1 :=
      Function.minimalPeriod_eq_one_iff_isFixedPt.mpr heb
    omega
  · simpa using Function.minimalPeriod_eq_one_iff_isFixedPt.mpr heb

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
    rw [cov.fiber_card w₀]; exact hd
  obtain ⟨u, m, hr_pos, hr_pow⟩ := exists_pow2_period_of_card_one_two_four e hcard
  let r := Function.minimalPeriod e u
  have hper : (e ^ r) u = u := Function.isPeriodicPt_minimalPeriod e u
  have hinj : ∀ i j : ℕ, i < r → j < r → (e ^ i) u = (e ^ j) u → i = j := by
    intro i j hi hj hij
    by_contra hne_ij
    wlog hlt : i < j
    · exact this cov hd k w₀ c hk hc hlen e hcard u m hr_pos hr_pow hper j i hj hi hij.symm (Ne.symm hne_ij) (by omega)
    have hp : Function.IsPeriodicPt e (j - i) u := by
      have h1 : (e ^ i) ((e ^ (j - i)) u) = (e ^ i) u := by
        rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hlt)]
        exact hij.symm
      exact (e ^ i).injective h1
    have hmin := Function.minimalPeriod_le (by omega) hp
    omega
  let w_raw := cov.liftRepeat c r u
  have hend : ((e ^ r) u).1 = u.1 := congrArg Subtype.val hper
  let w : G.Walk u.1 u.1 := hend ▸ w_raw
  have hw_len : w.length = 2 ^ (k + m) := by
    have hcast : ∀ {a b : V} (h : a = b) (p : G.Walk u.1 a), (h ▸ p).length = p.length := by
      rintro a _ rfl p; rfl
    rw [hcast hend w_raw, cov.liftRepeat_length c r u, hlen, hr_pow, pow_add, Nat.mul_comm]
  have hw_tail_nodup : w.support.tail.Nodup := by
    have hcast : ∀ {a b : V} (h : a = b) (p : G.Walk u.1 a), (h ▸ p).support.tail = p.support.tail := by
      rintro a _ rfl p; rfl
    rw [hcast hend w_raw]
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

end GraphCover

/-- Unconditional across all 13 remaining leaves (`C`, `S`, `H`): no `MinimalBad` graph
admits a 2-sheeted or 4-sheeted (even non-Galois) covering map onto a `Near` graph. -/
theorem minimal_bad_no_two_or_four_cover {V W : Type u} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hm : MinimalBad G) (d : ℕ) (hd : d = 2 ∨ d = 4)
    (cov : GraphCover G H d) (hnH : Near H) : False := by
  have hcardV : Fintype.card V = d * Fintype.card W := by
    have hsum : Fintype.card V = ∑ w : W, Fintype.card {u : V // cov.toFun u = w} := by
      rw [← Fintype.card_sigma]
      exact Fintype.card_congr
        { toFun := fun u => ⟨cov.toFun u, ⟨u, rfl⟩⟩
          invFun := fun p => p.2.1
          left_inv := fun _ => rfl
          right_inv := fun ⟨_, ⟨_, rfl⟩⟩ => rfl }
    rw [hsum]
    simp only [cov.fiber_card, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm]
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
    have hcardV : Fintype.card V = d * Fintype.card W := by
      have hsum : Fintype.card V = ∑ w : W, Fintype.card {u : V // cov.toFun u = w} := by
        rw [← Fintype.card_sigma]
        exact Fintype.card_congr
          { toFun := fun u => ⟨cov.toFun u, ⟨u, rfl⟩⟩
            invFun := fun p => p.2.1
            left_inv := fun _ => rfl
            right_inv := fun ⟨_, ⟨_, rfl⟩⟩ => rfl }
      rw [hsum]
      simp only [cov.fiber_card, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm]
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
  symm := by
    intro a b h
    cases a <;> cases b <;> simp_all only
    · obtain ⟨u, hu, hadj⟩ := h; exact ⟨u, hu, hadj.symm⟩
    · obtain ⟨u, hu, hadj⟩ := h; exact ⟨u, hu, hadj.symm⟩
    · exact h.symm
  loopless := by
    intro a
    cases a with
    | none => simp
    | some x => exact G.loopless x.1

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
  -- Step 1: `Fintype.card W < Fintype.card V`
  have hcardW : Fintype.card W < Fintype.card V := by
    have hcomp : Fintype.card {x : V // x ∉ I} + I.card = Fintype.card V := by
      rw [Fintype.card_subtype_compl]
      have : Fintype.card {x : V // x ∈ I} = I.card := Fintype.card_coe I
      rw [this]
      exact Nat.sub_add_cancel (Finset.card_le_univ I)
    simp only [W, Fintype.card_option]
    omega
  -- Step 2: `H.degree (some x) = G.degree x.1` for every `x ∉ I`
  have hdeg_some : ∀ x : {z : V // z ∉ I}, H.degree (some x) = G.degree x.1 := by
    intro x
    rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
    -- Bijection between `G.neighborSet x.1` and `H.neighborSet (some x)`
    have huniq : ∀ u₁ ∈ I, ∀ u₂ ∈ I, G.Adj x.1 u₁ → G.Adj x.1 u₂ → u₁ = u₂ := by
      intro u₁ hu₁ u₂ hu₂ h1 h2
      by_contra hne
      exact (hI u₁ hu₁ u₂ hu₂ hne).2 x.1 ⟨h1.symm, h2.symm⟩
    refine Fintype.card_congr
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
          · simp only [dif_pos h]
            apply Subtype.ext
            exact huniq _ (Exists.choose_spec (⟨y, h, hy⟩ : ∃ u ∈ I, G.Adj x.1 u)).1 y h
              (Exists.choose_spec (⟨y, h, hy⟩ : ∃ u ∈ I, G.Adj x.1 u)).2 hy
          · simp [dif_neg h]
        right_inv := by
          rintro ⟨q, hq⟩
          cases q with
          | none =>
            simp only [dif_pos (Exists.choose_spec hq).1]
          | some y =>
            simp only [dif_neg y.2] }
    |>.symm
  -- Step 3: `3 ≤ H.degree none`
  have hdeg_none : 3 ≤ H.degree none := by
    obtain ⟨w, hw⟩ := hm.1.2
    -- Since `2 ≤ I.card`, there exists `u ∈ I` with `u ≠ w`, hence `3 ≤ G.degree u`
    have hex_u : ∃ u ∈ I, u ≠ w := by
      by_contra hall
      push_neg at hall
      have hsub : I ⊆ {w} := fun u hu => Finset.mem_singleton.mpr (hall u hu)
      have := Finset.card_le_card hsub
      simp at this; omega
    obtain ⟨u, huI, huw⟩ := hex_u
    have hdu : 3 ≤ G.degree u := hw u huw
    -- Every neighbor `y` of `u` lies outside `I` (since `I` is independent)
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
  -- Step 4: `Near H`
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
  -- Step 5: `HasPower H` yields a `2^k`-cycle in `H`
  obtain ⟨k, v₀, c, hk, hc, hlen⟩ := hm.2.2.1 W H hcardW hnearH
  -- Step 6: `none` MUST lie on `c.support` (otherwise `c` lifts to a `2^k`-cycle in `G`)
  have hnone_mem : none ∈ c.support := by
    by_contra hnot
    -- Map `c` into `G` since every vertex on `c` is `some x`
    have liftNoNone : ∀ {a b : W} (p : H.Walk a b), none ∉ p.support →
        ∀ (ha : a.isSome) (hb : b.isSome),
          ∃ q : G.Walk (a.get ha).1 (b.get hb).1,
            q.length = p.length ∧
            q.support.map (fun z => if h : z ∉ I then some ⟨z, h⟩ else none) = p.support := by
      intro a b p
      induction p with
      | nil =>
        intro _ ha hb
        refine ⟨.nil, rfl, ?_⟩
        cases a with
        | none => simp at ha
        | some x => simp [x.2]
      | @cons a b c' hadj q ih =>
        intro hno ha hc'
        have hb : b.isSome := by
          cases b with
          | none => exfalso; exact hno (by simp [Walk.support_cons])
          | some _ => rfl
        have hno_q : none ∉ q.support := fun h => hno (by simp [Walk.support_cons, h])
        obtain ⟨q', hqlen, hqsupp⟩ := ih hno_q hb hc'
        cases a with
        | none => simp at ha
        | some x =>
          cases b with
          | none => simp at hb
          | some y =>
            refine ⟨.cons hadj q', by simp [hqlen], ?_⟩
            simp only [Walk.support_cons, List.map_cons, dif_pos x.2]
            congr 1
    have hv₀ : v₀.isSome := by
      cases v₀ with
      | none => exfalso; exact hnot (Walk.start_mem_support c)
      | some _ => rfl
    obtain ⟨q, hqlen, hqsupp⟩ := liftNoNone c hnot hv₀ hv₀
    have hq_tail : q.support.tail.Nodup := by
      have hm := congrArg List.tail hqsupp
      rw [← List.map_tail] at hm
      exact List.Nodup.of_map _ (hm.symm ▸ hc.support_nodup)
    have hq_len3 : 3 ≤ q.length := by rw [hqlen]; exact hc.three_le_length
    have hq_nnil : ¬ q.Nil := by
      intro h; have := Walk.length_eq_zero_iff.mpr h; omega
    apply hm.2.1
    refine ⟨k, (v₀.get hv₀).1, q, hk, ?_, hqlen.trans hlen⟩
    apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    refine ⟨Walk.IsPath.mk' ?_, hq_len3⟩
    rwa [Walk.support_tail_of_not_nil _ hq_nnil]
  -- Step 7: Rotate `c` to start and end at `none`
  let c' := c.rotate hnone_mem
  have hc' : c'.IsCycle := hc.rotate hnone_mem
  have hc'_len : c'.length = 2 ^ k := by rw [Walk.length_rotate]; exact hlen
  -- Decompose `c'` as `none → some x₁ —(mid)— some xₘ → none`
  cases c' with
  | nil => exact absurd rfl hc'.ne_nil
  | @cons _ b _ h1 rest =>
    cases b with
    | none => exact False.elim h1
    | some x₁ =>
      -- `rest : H.Walk (some x₁) none` has length `2^k - 1 ≥ 3`, and its last edge is `some xₘ → none`
      have hrest_nnil : ¬ rest.Nil := by
        intro h; cases h
      -- Lift `rest.reverse` starting from `none`: its first edge is `none → some xₘ`
      cases hrev : rest.reverse with
      | nil =>
        have : rest = .nil := by simpa using congrArg Walk.reverse hrev
        exact hrest_nnil (by rw [this]; exact Walk.Nil.nil)
      | @cons _ b2 _ h2 mid_rev =>
        cases b2 with
        | none => exact False.elim h2
        | some xₘ =>
          let mid := mid_rev.reverse
          -- `c'` = `cons h1 (mid.concat h2.symm)`!
          have hrest_eq : rest = mid.concat h2.symm := by
            have := congrArg Walk.reverse hrev
            simpa [mid, Walk.reverse_cons] using this
          -- `none ∉ mid.support` because `c'.support.tail = rest.support` is `Nodup` and ends at `none`
          have hmid_no_none : none ∉ mid.support := by
            intro hmem
            have hnd : (Walk.cons h1 rest).support.tail.Nodup := hc'.support_nodup
            simp only [Walk.support_cons, List.tail_cons, hrest_eq, Walk.support_concat] at hnd
            rw [List.nodup_concat] at hnd
            exact hnd.1 hmem
          -- Lift `mid` directly into `G`!
          have liftMid : ∀ {a b : W} (p : H.Walk a b), none ∉ p.support →
              ∀ (ha : a.isSome) (hb : b.isSome),
                ∃ q : G.Walk (a.get ha).1 (b.get hb).1,
                  q.length = p.length ∧
                  q.support.map (fun z => if h : z ∉ I then some ⟨z, h⟩ else none) = p.support ∧
                  ∀ z ∈ q.support, z ∉ I := by
            intro a b p
            induction p with
            | nil =>
              intro _ ha hb
              cases a with
              | none => simp at ha
              | some x => exact ⟨.nil, rfl, by simp [x.2], by simp [x.2]⟩
            | @cons a b c'' hadj q ih =>
              intro hno ha hc''
              have hb : b.isSome := by
                cases b with
                | none => exfalso; exact hno (by simp [Walk.support_cons])
                | some _ => rfl
              obtain ⟨q', hql, hqs, hqi⟩ := ih (fun h => hno (by simp [Walk.support_cons, h])) hb hc''
              cases a with
              | none => simp at ha
              | some x =>
                cases b with
                | none => simp at hb
                | some y =>
                  refine ⟨.cons hadj q', by simp [hql], ?_, ?_⟩
                  · simp only [Walk.support_cons, List.map_cons, dif_pos x.2]; congr 1
                  · intro z hz
                    simp only [Walk.support_cons, List.mem_cons] at hz
                    rcases hz with rfl | hz
                    · exact x.2
                    · exact hqi z hz
          obtain ⟨qmid, hqmid_len, hqmid_supp, hqmid_notI⟩ := liftMid mid hmid_no_none rfl rfl
          obtain ⟨u, huI, hux1⟩ := h1
          obtain ⟨v, hvI, hvxm⟩ := h2
          let full : G.Walk u v := Walk.cons hux1 (qmid.concat hvxm.symm)
          have hfull_len : full.length = 2 ^ k := by
            have hcl : (Walk.cons h1 rest).length = 2 ^ k := hc'_len
            simp only [Walk.length_cons, hrest_eq, Walk.length_concat] at hcl
            simp only [full, Walk.length_cons, Walk.length_concat, hqmid_len]
            exact hcl
          have hqmid_nodup : qmid.support.Nodup := by
            have hnd : (Walk.cons h1 rest).support.tail.Nodup := hc'.support_nodup
            simp only [Walk.support_cons, List.tail_cons, hrest_eq, Walk.support_concat] at hnd
            rw [List.nodup_concat] at hnd
            exact List.Nodup.of_map _ (hqmid_supp.symm ▸ hnd.2)
          -- Show `u ≠ v` (otherwise `full` is a `2^k`-cycle in `G`, contradicting `¬ HasPower G`)
          have huv : u ≠ v := by
            intro heq
            subst heq
            have hcyc_tail : full.support.tail.Nodup := by
              simp only [full, Walk.support_cons, List.tail_cons, Walk.support_concat, List.nodup_concat]
              exact ⟨fun h => hqmid_notI u h huI, hqmid_nodup⟩
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
          -- `full` is a simple path whose internal vertices are `qmid.support`, all disjoint from `I`!
          have hfull_path : full.IsPath := by
            apply Walk.IsPath.mk'
            simp only [full, Walk.support_cons, Walk.support_concat, List.nodup_cons, List.nodup_concat]
            refine ⟨?_, fun h => hqmid_notI v h hvI, hqmid_nodup⟩
            intro hmem
            rw [List.mem_concat] at hmem
            rcases hmem with hmem | hEq
            · exact hqmid_notI u hmem huI
            · exact huv hEq
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
