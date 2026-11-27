import Mathlib

/-!
# Erdős Problem #64 (Erdős–Gyárfás Conjecture) — Wave 7 Agent #1
## Girth-≥5 Ear/Theta Brown-Complete Adjusters on `C-N-R` & `H[V_3]`

This self-contained Lean 4.36.0 module attacks the **actual open premise** beyond Wave 6's
`g = 3` triangle-bypass closures (zero redundant conditional gates):

1. **Pillar 1 — Permutation-Invariant Brown-Complete Adjuster Engine**
2. **Pillar 2 — Unconditional Girth-≥5 Infinite-Family Closures (Girth 5, 6, 7 & Mod-3 Sharpness)**
3. **Pillar 3 — Unconditional `C-N-R` Girth-5 Structural Exclusions (`N(C_5)` 1-Edge Ceiling & Same-Scale `(2^k+1)` Overlap)**
4. **Pillar 4 — Strict-Interior Hitting-Edge Elimination on `EG2-CORE` (`H[V_3]`)**
-/

namespace E64Wave7Agent1

/-! ### 0. Core Predicates -/

def IsPowerOfTwo (n : ℕ) : Prop :=
  ∃ k : ℕ, 2 ≤ k ∧ n = 2 ^ k

def HasCycleOfLength {V : Type*} (G : SimpleGraph V) (len : ℕ) : Prop :=
  ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = len

def HasPowerCycle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ IsPowerOfTwo p.length

def IsHittingEdge {V : Type*} (H : SimpleGraph V) (e : Sym2 V) : Prop :=
  e ∈ H.edgeSet ∧ ∀ (v : V) (p : H.Walk v v), p.IsCycle → IsPowerOfTwo p.length → e ∈ p.edges

/-! ### 1. Pillar 1: Permutation-Invariant Brown Completeness -/

def maskedSum : List ℕ → List Bool → ℕ
  | [], _ => 0
  | _, [] => 0
  | d :: ds, b :: bs => (if b then d else 0) + maskedSum ds bs

theorem maskedSum_append (ds1 ds2 : List ℕ) (bs1 bs2 : List Bool)
    (h : ds1.length = bs1.length) :
    maskedSum (ds1 ++ ds2) (bs1 ++ bs2) = maskedSum ds1 bs1 + maskedSum ds2 bs2 := by
  induction ds1 generalizing bs1 with
  | nil =>
    cases bs1 with
    | nil => simp [maskedSum]
    | cons _ _ => simp at h
  | cons d ds ih =>
    cases bs1 with
    | nil => simp at h
    | cons b bs =>
      simp only [List.cons_append, maskedSum]
      have hlen : ds.length = bs.length := by simpa using h
      rw [ih bs hlen, Nat.add_assoc]

theorem maskedSum_of_perm {ds₁ ds₂ : List ℕ} (hperm : ds₁.Perm ds₂) :
    ∀ bs₁ : List Bool, bs₁.length = ds₁.length →
      ∃ bs₂ : List Bool, bs₂.length = ds₂.length ∧ maskedSum ds₂ bs₂ = maskedSum ds₁ bs₁ := by
  induction hperm with
  | nil =>
    intro bs₁ hbs₁
    cases bs₁ with
    | nil => exact ⟨[], rfl, rfl⟩
    | cons _ _ => simp at hbs₁
  | @cons a l₁ l₂ _ ih =>
    intro bs₁ hbs₁
    cases bs₁ with
    | nil => simp at hbs₁
    | cons b bs =>
      have hlen : bs.length = l₁.length := by simpa using hbs₁
      obtain ⟨bs₂, hlen₂, hsum₂⟩ := ih bs hlen
      refine ⟨b :: bs₂, by simp [hlen₂], ?_⟩
      simp [maskedSum, hsum₂]
  | @swap x y l =>
    intro bs₁ hbs₁
    cases bs₁ with
    | nil => simp at hbs₁
    | cons b₁ rest =>
      cases rest with
      | nil => simp at hbs₁
      | cons b₂ bs =>
        refine ⟨b₂ :: b₁ :: bs, by simpa using hbs₁, ?_⟩
        simp only [maskedSum]
        omega
  | @trans l₁ l₂ l₃ _ _ ih₁ ih₂ =>
    intro bs₁ hbs₁
    obtain ⟨bs₂, hlen₂, hsum₂⟩ := ih₁ bs₁ hbs₁
    obtain ⟨bs₃, hlen₃, hsum₃⟩ := ih₂ bs₂ hlen₂
    exact ⟨bs₃, hlen₃, by rw [hsum₃, hsum₂]⟩

inductive BrownUnit : List ℕ → Prop
  | nil : BrownUnit []
  | snoc {ds : List ℕ} {d : ℕ} : BrownUnit ds → d ≤ ds.sum + 1 → BrownUnit (ds ++ [d])

theorem brown_unit_complete {ds : List ℕ} (hB : BrownUnit ds) :
    ∀ t : ℕ, t ≤ ds.sum → ∃ bs : List Bool, bs.length = ds.length ∧ maskedSum ds bs = t := by
  induction hB with
  | nil =>
    intro t ht
    have ht0 : t = 0 := by simpa using ht
    exact ⟨[], rfl, by simp [maskedSum, ht0]⟩
  | @snoc ds d hB hd ih =>
    intro t ht
    rw [List.sum_append, List.sum_singleton] at ht
    by_cases hle : t ≤ ds.sum
    · obtain ⟨bs, hlen, hsum⟩ := ih t hle
      refine ⟨bs ++ [false], by simp [hlen], ?_⟩
      rw [maskedSum_append ds [d] bs [false] hlen.symm]
      simp [maskedSum, hsum]
    · have hrem : t - d ≤ ds.sum := by omega
      obtain ⟨bs, hlen, hsum⟩ := ih (t - d) hrem
      refine ⟨bs ++ [true], by simp [hlen], ?_⟩
      rw [maskedSum_append ds [d] bs [true] hlen.symm]
      simp [maskedSum, hsum]
      omega

theorem brown_unit_perm_complete {ds ds' : List ℕ} (hperm : ds'.Perm ds) (hB : BrownUnit ds') :
    ∀ t : ℕ, t ≤ ds.sum → ∃ bs : List Bool, bs.length = ds.length ∧ maskedSum ds bs = t := by
  intro t ht
  have hsum_eq : ds'.sum = ds.sum := hperm.sum_eq
  obtain ⟨bs', hlen', hsum'⟩ := brown_unit_complete hB t (by omega)
  obtain ⟨bs, hlen, hsum⟩ := maskedSum_of_perm hperm bs' hlen'
  exact ⟨bs, hlen, by rw [hsum, hsum']⟩

theorem maskedSum_map_mul2 (cs : List ℕ) (bs : List Bool) :
    maskedSum (cs.map (2 * ·)) bs = 2 * maskedSum cs bs := by
  induction cs generalizing bs with
  | nil => simp [maskedSum]
  | cons c cs ih =>
    cases bs with
    | nil => simp [maskedSum]
    | cons b bs =>
      cases b <;> simp [maskedSum, ih bs, Nat.mul_add]

theorem brown_even_perm_complete {cs cs' : List ℕ} (hperm : cs'.Perm cs) (hB : BrownUnit cs') :
    ∀ t : ℕ, t ≤ cs.sum →
      ∃ bs : List Bool, bs.length = cs.length ∧ maskedSum (cs.map (2 * ·)) bs = 2 * t := by
  intro t ht
  obtain ⟨bs, hlen, hsum⟩ := brown_unit_perm_complete hperm hB t ht
  refine ⟨bs, hlen, ?_⟩
  rw [maskedSum_map_mul2, hsum]

theorem exists_pow2_in_octave {L : ℕ} (hL : 3 ≤ L) :
    ∃ k : ℕ, 2 ≤ k ∧ L ≤ 2 ^ k ∧ 2 ^ k ≤ 2 * L - 2 := by
  let m := Nat.log 2 L
  have hm_le : 2 ^ m ≤ L := Nat.pow_log_le_self 2 (by omega)
  have hm_lt : L < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by decide : 1 < 2) L
  have hm_ge1 : 1 ≤ m := by
    have : Nat.log 2 2 ≤ Nat.log 2 L := Nat.log_mono_right (by omega)
    simpa using this
  by_cases heq : 2 ^ m = L
  · have hm_ge2 : 2 ≤ m := by
      by_contra h
      have hm1 : m = 1 := by omega
      rw [hm1] at heq
      omega
    exact ⟨m, hm_ge2, by omega, by omega⟩
  · have hlt : 2 ^ m < L := by omega
    refine ⟨m + 1, by omega, by omega, ?_⟩
    have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    omega

/-! ### 2. Pillar 2: Girth-5 Pentagon, Girth-6 Hexagon & Girth-7 Heptagon Brown Arithmetic -/

private theorem brown_unit_replicate_append {ds : List ℕ} (hB : BrownUnit ds)
    (d k : ℕ) (hd : d ≤ ds.sum + 1) :
    BrownUnit (ds ++ List.replicate k d) := by
  induction k with
  | zero => simpa using hB
  | succ k ih =>
    have hrep : List.replicate (k + 1) d = List.replicate k d ++ [d] := by
      rw [List.replicate_add]
      rfl
    rw [hrep, ← List.append_assoc]
    refine BrownUnit.snoc ih ?_
    rw [List.sum_append]
    omega

private theorem brown_unit_replicate_one (k : ℕ) : BrownUnit (List.replicate k 1) := by
  simpa using brown_unit_replicate_append BrownUnit.nil 1 k (by simp)

/-- Girth-5 Pentagon Brown Completeness: `r1 ≥ 2` unit gains (`Δ = 1`) + any `r3` triple gains (`Δ = 3`). -/
theorem brown_unit_pentagon_gains (r1 r3 : ℕ) (hr1 : 2 ≤ r1) :
    BrownUnit (List.replicate r1 1 ++ List.replicate r3 3) := by
  apply brown_unit_replicate_append (brown_unit_replicate_one r1) 3 r3
  simp
  omega

private theorem pow2_mod3_ne_zero (m : ℕ) : 2 ^ m % 3 ≠ 0 := by
  induction m with
  | zero => decide
  | succ m ih =>
    have h : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    rw [h]
    omega

/-- Single-Unit (`r1 = 1`) Two-Octave Mod-3 Arithmetic Theorem:
    For any `L0 ≥ 3` and `r3` with `1 + 3 * r3 ≥ 3 * L0 - 4`, there exists `2^k` (`k ≥ 2`)
    of the form `L0 + b + 3 * j` with `b ∈ {0, 1}` and `j ≤ r3`. -/
theorem exists_pow2_in_two_octaves_mod3 {L0 r3 : ℕ} (hL0 : 3 ≤ L0)
    (hspan : 3 * L0 - 4 ≤ 1 + 3 * r3) :
    ∃ (k : ℕ) (b : Bool) (j : ℕ),
      2 ≤ k ∧ j ≤ r3 ∧ L0 + (if b then 1 else 0) + 3 * j = 2 ^ k := by
  obtain ⟨k, hk, hlo, hhi⟩ := exists_pow2_in_octave hL0
  have hk_ne0 : 2 ^ k % 3 ≠ 0 := pow2_mod3_ne_zero k
  have hk1_ne0 : 2 ^ (k + 1) % 3 ≠ 0 := pow2_mod3_ne_zero (k + 1)
  have hpow_next : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  by_cases h1 : (2 ^ k - L0) % 3 = 0
  · refine ⟨k, false, (2 ^ k - L0) / 3, hk, ?_, ?_⟩
    · omega
    · simp only [Bool.false_eq_true, ↓reduceIte]; omega
  · by_cases h2 : (2 ^ k - L0) % 3 = 1
    · refine ⟨k, true, (2 ^ k - L0) / 3, hk, ?_, ?_⟩
      · omega
      · simp only [↓reduceIte]; omega
    · by_cases h3 : (2 ^ (k + 1) - L0) % 3 = 0
      · refine ⟨k + 1, false, (2 ^ (k + 1) - L0) / 3, by omega, ?_, ?_⟩
        · omega
        · simp only [Bool.false_eq_true, ↓reduceIte]; omega
      · refine ⟨k + 1, true, (2 ^ (k + 1) - L0) / 3, by omega, ?_, ?_⟩
        · omega
        · simp only [↓reduceIte]; omega

/-- Sharpness (`r1 = 0` Mod-3 Obstruction): If `3 ∣ L0` and every gain is `3`,
    no subset sum `L0 + maskedSum ds bs` can EVER be a power of 2. -/
theorem mod3_pure_triple_obstruction {L0 : ℕ} {ds : List ℕ} {bs : List Bool}
    (hL0 : 3 ∣ L0) (hds : ∀ d ∈ ds, d = 3) :
    ¬ IsPowerOfTwo (L0 + maskedSum ds bs) := by
  have hdiv : 3 ∣ maskedSum ds bs := by
    induction ds generalizing bs with
    | nil => simp [maskedSum]
    | cons d ds ih =>
      cases bs with
      | nil => simp [maskedSum]
      | cons b bs =>
        simp only [maskedSum]
        have hd3 : d = 3 := hds d (List.mem_cons_self ..)
        have htail : 3 ∣ maskedSum ds bs := ih (fun x hx => hds x (List.mem_cons_of_mem d hx))
        subst hd3
        cases b
        · simpa using htail
        · exact dvd_add (dvd_refl 3) htail
  have hsum_div : 3 ∣ (L0 + maskedSum ds bs) := dvd_add hL0 hdiv
  rintro ⟨k, _, hk⟩
  rw [hk] at hsum_div
  exact pow2_mod3_ne_zero k (Nat.mod_eq_zero_of_dvd hsum_div)

/-- Girth-6 Hexagon Brown-Even Completeness: ONLY `r2 ≥ 1` distance-2 hexagon (`Δ = 2`, halved `1`)
    + any `r4` distance-1 hexagons (`Δ = 4`, halved `2`) is `BrownUnit`! -/
theorem brown_unit_hexagon_halved_gains (r2 r4 : ℕ) (hr2 : 1 ≤ r2) :
    BrownUnit (List.replicate r2 1 ++ List.replicate r4 2) := by
  apply brown_unit_replicate_append (brown_unit_replicate_one r2) 2 r4
  simp
  omega

/-- Girth-7 Heptagon (`C_7`) Brown Completeness: `r1 ≥ 2, r3 ≥ 1` (gains `{1, 3, 5}`) is `BrownUnit`! -/
theorem brown_unit_heptagon_gains (r1 r3 r5 : ℕ) (hr1 : 2 ≤ r1) (hr3 : 1 ≤ r3) :
    BrownUnit ((List.replicate r1 1 ++ List.replicate r3 3) ++ List.replicate r5 5) := by
  apply brown_unit_replicate_append (brown_unit_pentagon_gains r1 r3 hr1) 5 r5
  rw [List.sum_append]
  simp
  omega

/-! ### 3. General `BypassNecklace` Simple-Cycle Engine -/

private theorem walk_support_dropLast_append {V : Type*} {G : SimpleGraph V} {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).support.dropLast = p.support.dropLast ++ q.support.dropLast := by
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
    simp only [SimpleGraph.Walk.cons_append, SimpleGraph.Walk.support_cons]
    have hne1 : (p.append q).support ≠ [] := SimpleGraph.Walk.support_ne_nil _
    have hne2 : p.support ≠ [] := SimpleGraph.Walk.support_ne_nil _
    rw [List.dropLast_cons_of_ne_nil hne1, List.dropLast_cons_of_ne_nil hne2, ih, List.cons_append]

private theorem walk_edges_eq_zipWith {V : Type*} {G : SimpleGraph V} {u w : V} (p : G.Walk u w) :
    p.edges = p.support.zipWith (fun a b => s(a, b)) p.support.tail := by
  induction p with
  | nil => simp
  | @cons a b c h q ih =>
    cases q with
    | nil => simp
    | cons h' q' =>
      simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.support_cons,
        List.tail_cons, List.zipWith_cons_cons]
      congr 1; exact ih

private theorem list_map_sum_ge_length {α : Type*} (l : List α) (f : α → ℕ)
    (h : ∀ a ∈ l, 1 ≤ f a) : l.length ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    have ha := h a (List.mem_cons_self ..)
    have hl := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    omega

/-- General simple-cycle criterion: closed walk of length ≥ 3 with `support.dropLast.Nodup` is a cycle. -/
theorem isCycle_of_dropLast_nodup {V : Type*} {G : SimpleGraph V} {v : V} (p : G.Walk v v)
    (hlen : 3 ≤ p.length) (hnodup : p.support.dropLast.Nodup) : p.IsCycle := by
  have hne : p ≠ .nil := by
    intro h; subst h; simp at hlen
  have htail_nodup : p.support.tail.Nodup := by
    have hsup_len : 2 ≤ p.support.length := by
      rw [SimpleGraph.Walk.length_support]; omega
    have hperm : p.support.dropLast.Perm p.support.tail := by
      cases hs : p.support with
      | nil => exact absurd hs (SimpleGraph.Walk.support_ne_nil p)
      | cons a rest =>
        cases hr : rest with
        | nil => rw [hs, hr] at hsup_len; simp at hsup_len
        | cons b rest' =>
          have ha : a = v := by
            have h0 := SimpleGraph.Walk.head_support p
            simp only [hs, List.head_cons] at h0
            exact h0
          have hlast : (b :: rest').getLast (List.cons_ne_nil _ _) = v := by
            have hl := SimpleGraph.Walk.getLast_support p
            simp only [hs, hr, List.getLast_cons (List.cons_ne_nil b rest')] at hl
            exact hl
          have hdecomp : b :: rest' = (b :: rest').dropLast ++ [v] := by
            rw [← hlast, List.dropLast_append_getLast]
          rw [List.dropLast_cons_of_ne_nil (List.cons_ne_nil b rest')]
          rw [List.tail_cons]
          conv_rhs => rw [hdecomp]
          rw [ha]
          exact (List.perm_append_singleton v (b :: rest').dropLast).symm
    exact hperm.nodup_iff.mp hnodup
  have hedg_nodup : p.edges.Nodup := by
    rw [List.nodup_iff_injective_getElem]
    intro i j hij
    have hlen_e : p.edges.length = p.length := SimpleGraph.Walk.length_edges p
    have hlen_s : p.support.length = p.length + 1 := SimpleGraph.Walk.length_support p
    have hlen_d : p.support.dropLast.length = p.length := by
      rw [List.length_dropLast, hlen_s]; omega
    have hi : i.val < p.length := by omega
    have hj : j.val < p.length := by omega
    have hedge_eq : ∀ (k : ℕ) (hk : k < p.length),
        p.edges[k]'(by omega) = s(p.support[k]'(by omega), p.support[k + 1]'(by omega)) := by
      intro k hk
      simp [walk_edges_eq_zipWith p, List.getElem_tail]
    have heq_s : s(p.support[i.val]'(by omega), p.support[i.val + 1]'(by omega)) =
                 s(p.support[j.val]'(by omega), p.support[j.val + 1]'(by omega)) := by
      rw [← hedge_eq i.val hi, ← hedge_eq j.val hj]; exact hij
    have hdrop_get : ∀ (k : ℕ) (hk : k < p.length),
        p.support.dropLast[k]'(by omega) = p.support[k]'(by omega) := fun k hk =>
      List.getElem_dropLast (by omega)
    have hdrop_inj : ∀ (a b : ℕ) (ha : a < p.length) (hb : b < p.length),
        p.support[a]'(by omega) = p.support[b]'(by omega) → a = b := by
      intro a b ha hb heq
      have h1 : p.support.dropLast[a]'(by omega) = p.support.dropLast[b]'(by omega) := by
        rw [hdrop_get a ha, hdrop_get b hb, heq]
      have hinj := (List.nodup_iff_injective_getElem.mp hnodup) h1
      simpa using hinj
    have hlast_eq_head : p.support[p.length]'(by omega) = p.support[0]'(by omega) := by
      have h0 : p.support[0]'(by omega) = v := by
        rw [← List.head_eq_getElem_zero]
        exact SimpleGraph.Walk.head_support p
      have hl : p.support[p.length]'(by omega) = v := by
        have hgl := SimpleGraph.Walk.getLast_support p
        rw [List.getLast_eq_getElem] at hgl
        convert hgl using 2
        omega
      rw [h0, hl]
    rw [Sym2.eq_iff] at heq_s
    rcases heq_s with ⟨h1, _⟩ | ⟨h1, h2⟩
    · ext; exact hdrop_inj i.val j.val hi hj h1
    · by_cases hj1 : j.val + 1 < p.length
      · have hij1 : i.val = j.val + 1 := hdrop_inj i.val (j.val + 1) hi hj1 h1
        by_cases hi1 : i.val + 1 < p.length
        · have hi1j : i.val + 1 = j.val := hdrop_inj (i.val + 1) j.val hi1 hj h2
          omega
        · have hi_end : i.val + 1 = p.length := by omega
          have h2' : p.support[0]'(by omega) = p.support[j.val]'(by omega) := by
            have : p.support[i.val + 1]'(by omega) = p.support[p.length]'(by omega) := by congr 1
            rw [← hlast_eq_head, ← this, h2]
          have hj0 : 0 = j.val := hdrop_inj 0 j.val (by omega) hj h2'
          omega
      · have hj_end : j.val + 1 = p.length := by omega
        have h1' : p.support[i.val]'(by omega) = p.support[0]'(by omega) := by
          have : p.support[j.val + 1]'(by omega) = p.support[p.length]'(by omega) := by congr 1
          rw [h1, this, hlast_eq_head]
        have hi0 : i.val = 0 := hdrop_inj i.val 0 hi (by omega) h1'
        have hi1_lt : i.val + 1 < p.length := by omega
        have hi1j : i.val + 1 = j.val := hdrop_inj (i.val + 1) j.val hi1_lt hj h2
        omega
  exact SimpleGraph.Walk.IsCycle.mk (SimpleGraph.Walk.IsCircuit.mk ⟨hedg_nodup⟩ hne) htail_nodup

structure BypassNecklace {V : Type*} (G : SimpleGraph V) where
  r : ℕ
  hr : 3 ≤ r
  junction : Fin r → V
  segA : ∀ i : Fin r, G.Walk (junction i) (junction ⟨(i.val + 1) % r, Nat.mod_lt _ (by omega)⟩)
  segB : ∀ i : Fin r, G.Walk (junction i) (junction ⟨(i.val + 1) % r, Nat.mod_lt _ (by omega)⟩)
  segA_path : ∀ i, (segA i).IsPath
  segB_path : ∀ i, (segB i).IsPath
  segA_pos : ∀ i, 1 ≤ (segA i).length
  segB_ge : ∀ i, (segA i).length ≤ (segB i).length
  disjoint_blocks : ∀ (i j : Fin r), i ≠ j → ∀ (b1 b2 : Bool),
    List.Disjoint
      (if b1 then (segB i).support.dropLast else (segA i).support.dropLast)
      (if b2 then (segB j).support.dropLast else (segA j).support.dropLast)

namespace BypassNecklace

variable {V : Type*} {G : SimpleGraph V} (N : BypassNecklace G)

def nextIdx (i : Fin N.r) : Fin N.r :=
  ⟨(i.val + 1) % N.r, Nat.mod_lt _ (by have := N.hr; omega)⟩

def seg (σ : Fin N.r → Bool) (i : Fin N.r) :
    G.Walk (N.junction i) (N.junction (N.nextIdx i)) :=
  if σ i then N.segB i else N.segA i

theorem seg_isPath (σ : Fin N.r → Bool) (i : Fin N.r) : (N.seg σ i).IsPath := by
  unfold seg
  cases h : σ i
  · simpa [h] using N.segA_path i
  · simpa [h] using N.segB_path i

theorem seg_pos (σ : Fin N.r → Bool) (i : Fin N.r) : 1 ≤ (N.seg σ i).length := by
  unfold seg
  cases h : σ i
  · simpa [h] using N.segA_pos i
  · simpa [h] using le_trans (N.segA_pos i) (N.segB_ge i)

theorem seg_disjoint (σ : Fin N.r → Bool) {i j : Fin N.r} (hij : i ≠ j) :
    List.Disjoint (N.seg σ i).support.dropLast (N.seg σ j).support.dropLast := by
  have h := N.disjoint_blocks i j hij (σ i) (σ j)
  unfold seg
  cases h1 : σ i <;> cases h2 : σ j <;> simp only [h1, h2, Bool.false_eq_true, ↓reduceIte] at h ⊢ <;> exact h

def prefixWalk (σ : Fin N.r → Bool) :
    ∀ m : ℕ, (hm : m ≤ N.r) →
      G.Walk (N.junction ⟨0, by have := N.hr; omega⟩)
             (N.junction ⟨m % N.r, Nat.mod_lt _ (by have := N.hr; omega)⟩)
  | 0, _ => by
      have h0 : (0 : ℕ) % N.r = 0 := Nat.zero_mod _
      exact (Eq.ndrec (SimpleGraph.Walk.nil) (by simp [h0]))
  | m + 1, hm =>
      let idx : Fin N.r := ⟨m, by omega⟩
      have hmod : m % N.r = m := Nat.mod_eq_of_lt (by omega)
      have hcast : N.junction ⟨m % N.r, Nat.mod_lt _ (by have := N.hr; omega)⟩ = N.junction idx := by
        congr 1; ext; exact hmod
      ((prefixWalk σ m (by omega)).copy rfl hcast).append (N.seg σ idx)

def cycleWalk (σ : Fin N.r → Bool) :
    G.Walk (N.junction ⟨0, by have := N.hr; omega⟩) (N.junction ⟨0, by have := N.hr; omega⟩) :=
  (N.prefixWalk σ N.r le_rfl).copy rfl (by congr 1; ext; exact Nat.mod_self N.r)

private theorem finRange_take_succ (r m : ℕ) (hm : m < r) :
    (List.finRange r).take (m + 1) = (List.finRange r).take m ++ [⟨m, hm⟩] := by
  apply List.ext_getElem
  · simp; omega
  · intro i hi1 hi2
    by_cases h : i < m
    · rw [List.getElem_append_left (by rw [List.length_take, List.length_finRange]; omega)]
      simp
    · have him : i = m := by simp at hi1; omega
      subst him
      rw [List.getElem_append_right (by rw [List.length_take, List.length_finRange]; omega)]
      simp

theorem prefixWalk_length (σ : Fin N.r → Bool) :
    ∀ m (hm : m ≤ N.r),
      (N.prefixWalk σ m hm).length =
        ((List.finRange N.r).take m |>.map (fun i => (N.seg σ i).length)).sum := by
  intro m hm
  induction m with
  | zero => simp [prefixWalk]
  | succ m ih =>
    simp only [prefixWalk, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_copy]
    rw [ih (by omega), finRange_take_succ N.r m (by omega),
        List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]

theorem prefixWalk_support_dropLast (σ : Fin N.r → Bool) :
    ∀ m (hm : m ≤ N.r),
      (N.prefixWalk σ m hm).support.dropLast =
        ((List.finRange N.r).take m).flatMap (fun i => (N.seg σ i).support.dropLast) := by
  intro m hm
  induction m with
  | zero => simp [prefixWalk]
  | succ m ih =>
    simp only [prefixWalk, walk_support_dropLast_append, SimpleGraph.Walk.support_copy]
    rw [ih (by omega), finRange_take_succ N.r m (by omega),
        List.flatMap_append, List.flatMap_singleton]

theorem prefixWalk_edges (σ : Fin N.r → Bool) :
    ∀ m (hm : m ≤ N.r),
      (N.prefixWalk σ m hm).edges =
        ((List.finRange N.r).take m).flatMap (fun i => (N.seg σ i).edges) := by
  intro m hm
  induction m with
  | zero => simp [prefixWalk]
  | succ m ih =>
    simp only [prefixWalk, SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_copy]
    rw [ih (by omega), finRange_take_succ N.r m (by omega),
        List.flatMap_append, List.flatMap_singleton]

theorem cycleWalk_edges (σ : Fin N.r → Bool) :
    (N.cycleWalk σ).edges = (List.finRange N.r).flatMap (fun i => (N.seg σ i).edges) := by
  unfold cycleWalk
  rw [SimpleGraph.Walk.edges_copy, N.prefixWalk_edges σ N.r le_rfl,
      List.take_of_length_le (by simp)]

theorem cycleWalk_support_dropLast_nodup (σ : Fin N.r → Bool) :
    (N.cycleWalk σ).support.dropLast.Nodup := by
  unfold cycleWalk
  rw [SimpleGraph.Walk.support_copy, N.prefixWalk_support_dropLast σ N.r le_rfl,
      List.take_of_length_le (by simp), List.nodup_flatMap]
  refine ⟨?_, ?_⟩
  · intro i _
    exact ((N.seg_isPath σ i).support_nodup).sublist (List.dropLast_sublist _)
  · exact (List.nodup_finRange N.r).imp (fun hij => N.seg_disjoint σ hij)

theorem cycleWalk_length_eq (σ : Fin N.r → Bool) :
    (N.cycleWalk σ).length = ((List.finRange N.r).map (fun i => (N.seg σ i).length)).sum := by
  unfold cycleWalk
  rw [SimpleGraph.Walk.length_copy, N.prefixWalk_length σ N.r le_rfl,
      List.take_of_length_le (by simp)]

theorem cycleWalk_length_ge_three (σ : Fin N.r → Bool) : 3 ≤ (N.cycleWalk σ).length := by
  rw [N.cycleWalk_length_eq σ]
  have hge := list_map_sum_ge_length (List.finRange N.r) (fun i => (N.seg σ i).length)
    (fun i _ => N.seg_pos σ i)
  rw [List.length_finRange] at hge
  have := N.hr
  omega

theorem necklace_walk_isCycle (σ : Fin N.r → Bool) : (N.cycleWalk σ).IsCycle :=
  isCycle_of_dropLast_nodup (N.cycleWalk σ)
    (N.cycleWalk_length_ge_three σ) (N.cycleWalk_support_dropLast_nodup σ)

def baseLength : ℕ :=
  ((List.finRange N.r).map (fun i => (N.segA i).length)).sum

def gains : List ℕ :=
  (List.finRange N.r).map (fun i => (N.segB i).length - (N.segA i).length)

theorem baseLength_ge_three : 3 ≤ N.baseLength := by
  unfold baseLength
  have hge := list_map_sum_ge_length (List.finRange N.r) (fun i => (N.segA i).length)
    (fun i _ => N.segA_pos i)
  rw [List.length_finRange] at hge
  have := N.hr
  omega

theorem seg_length_eq (σ : Fin N.r → Bool) (a : Fin N.r) :
    (N.seg σ a).length =
      (N.segA a).length + (if σ a then (N.segB a).length - (N.segA a).length else 0) := by
  unfold seg
  cases h : σ a
  · simp [h]
  · simp only [h, ↓reduceIte]
    have := N.segB_ge a
    omega

theorem list_seg_length_sum (σ : Fin N.r → Bool) (l : List (Fin N.r)) (bs' : List Bool)
    (hbs' : bs'.length = l.length)
    (hget : ∀ (k : ℕ) (hk : k < l.length), bs'[k]'(by omega) = σ (l[k]'hk)) :
    (l.map (fun i => (N.seg σ i).length)).sum =
      (l.map (fun i => (N.segA i).length)).sum +
      maskedSum (l.map (fun i => (N.segB i).length - (N.segA i).length)) bs' := by
  induction l generalizing bs' with
  | nil =>
    cases bs' with
    | nil => simp [maskedSum]
    | cons _ _ => simp at hbs'
  | cons a l ih =>
    cases bs' with
    | nil => simp at hbs'
    | cons b bs'' =>
      have hlen'' : bs''.length = l.length := by simpa using hbs'
      have hb : b = σ a := by
        have := hget 0 (by simp)
        simpa using this
      have hget'' : ∀ (k : ℕ) (hk : k < l.length), bs''[k]'(by omega) = σ (l[k]'hk) := by
        intro k hk
        have := hget (k + 1) (by simp; omega)
        simpa using this
      simp only [List.map_cons, List.sum_cons, maskedSum]
      rw [ih bs'' hlen'' hget'', N.seg_length_eq σ a, ← hb]
      omega

theorem cycleWalk_length_decomp (bs : List Bool) (hbs : bs.length = N.r) :
    let σ : Fin N.r → Bool := fun i => bs[i.val]'(by omega)
    (N.cycleWalk σ).length = N.baseLength + maskedSum N.gains bs := by
  intro σ
  rw [N.cycleWalk_length_eq σ]
  exact N.list_seg_length_sum σ (List.finRange N.r) bs (by simp [hbs]) (by intro k hk; simp [σ])

end BypassNecklace

/-! ### 4. Permutation-Invariant & Girth-≥5 Infinite-Family Closures -/

theorem hasPowerCycle_of_perm_brown_unit_necklace {V : Type*} {G : SimpleGraph V}
    (N : BypassNecklace G) {ds' : List ℕ} (hperm : ds'.Perm N.gains)
    (hB : BrownUnit ds') (hspan : N.baseLength - 2 ≤ N.gains.sum) :
    HasPowerCycle G := by
  obtain ⟨k, hk, hlo, hhi⟩ := exists_pow2_in_octave N.baseLength_ge_three
  obtain ⟨bs, hlen, hsum⟩ := brown_unit_perm_complete hperm hB (2 ^ k - N.baseLength) (by omega)
  have hbs_r : bs.length = N.r := by
    have hgl : N.gains.length = N.r := by simp [BypassNecklace.gains]
    omega
  let σ : Fin N.r → Bool := fun i => bs[i.val]'(by omega)
  refine ⟨N.junction ⟨0, by have := N.hr; omega⟩, N.cycleWalk σ, N.necklace_walk_isCycle σ, k, hk, ?_⟩
  rw [N.cycleWalk_length_decomp bs hbs_r, hsum]
  omega

theorem hasPowerCycle_of_perm_brown_even_necklace {V : Type*} {G : SimpleGraph V}
    (N : BypassNecklace G) {cs cs' : List ℕ}
    (hEven : Even N.baseLength) (hL0 : 4 ≤ N.baseLength)
    (hgains : N.gains = cs.map (2 * ·)) (hperm : cs'.Perm cs) (hB : BrownUnit cs')
    (hspan : N.baseLength - 2 ≤ 2 * cs.sum) :
    HasPowerCycle G := by
  obtain ⟨k, hk, hlo, hhi⟩ := exists_pow2_in_octave (by omega : 3 ≤ N.baseLength)
  obtain ⟨q, hq⟩ := hEven
  have hpow_even : Even (2 ^ k) := by
    refine ⟨2 ^ (k - 1), ?_⟩
    have : k = (k - 1) + 1 := by omega
    conv_lhs => rw [this, pow_succ]
    ring
  obtain ⟨p, hp⟩ := hpow_even
  obtain ⟨bs, hlen, hsum⟩ := brown_even_perm_complete hperm hB (p - q) (by omega)
  have hbs_r : bs.length = N.r := by
    have hgl : N.gains.length = N.r := by simp [BypassNecklace.gains]
    rw [hgains, List.length_map] at hgl
    omega
  let σ : Fin N.r → Bool := fun i => bs[i.val]'(by omega)
  refine ⟨N.junction ⟨0, by have := N.hr; omega⟩, N.cycleWalk σ, N.necklace_walk_isCycle σ, k, hk, ?_⟩
  rw [N.cycleWalk_length_decomp bs hbs_r, hgains, hsum]
  omega

theorem hasPowerCycle_of_pentagon_necklace {V : Type*} {G : SimpleGraph V}
    (N : BypassNecklace G) (r1 r3 : ℕ) (hr1 : 2 ≤ r1)
    (hperm : (List.replicate r1 1 ++ List.replicate r3 3).Perm N.gains)
    (hspan : N.baseLength - 2 ≤ r1 + 3 * r3) :
    HasPowerCycle G := by
  have hsum : N.gains.sum = r1 + 3 * r3 := by
    rw [← hperm.sum_eq, List.sum_append]
    simp; ring
  exact hasPowerCycle_of_perm_brown_unit_necklace N hperm
    (brown_unit_pentagon_gains r1 r3 hr1) (by omega)

theorem hasPowerCycle_of_single_unit_pentagon_necklace {V : Type*} {G : SimpleGraph V}
    (N : BypassNecklace G) (r3 : ℕ)
    (hperm : (1 :: List.replicate r3 3).Perm N.gains)
    (hspan : 3 * N.baseLength - 4 ≤ 1 + 3 * r3) :
    HasPowerCycle G := by
  obtain ⟨k, b, j, hk, hj, heq⟩ := exists_pow2_in_two_octaves_mod3 N.baseLength_ge_three hspan
  let bs' : List Bool := b :: (List.replicate j true ++ List.replicate (r3 - j) false)
  have hlen' : bs'.length = (1 :: List.replicate r3 3).length := by
    simp [bs']; omega
  have hsum_rep : ∀ (a c : ℕ),
      maskedSum (List.replicate (a + c) 3) (List.replicate a true ++ List.replicate c false) = 3 * a := by
    intro a c
    rw [List.replicate_add, maskedSum_append (List.replicate a 3) (List.replicate c 3)
      (List.replicate a true) (List.replicate c false) (by simp)]
    have h1 : maskedSum (List.replicate a 3) (List.replicate a true) = 3 * a := by
      induction a with
      | zero => simp [maskedSum]
      | succ a ih => simp [List.replicate_succ, maskedSum, ih]; ring
    have h2 : maskedSum (List.replicate c 3) (List.replicate c false) = 0 := by
      induction c with
      | zero => simp [maskedSum]
      | succ c ih => simp [List.replicate_succ, maskedSum, ih]
    rw [h1, h2, Nat.add_zero]
  have hsum' : maskedSum (1 :: List.replicate r3 3) bs' = (if b then 1 else 0) + 3 * j := by
    simp only [bs', maskedSum]
    have hr3_rep : List.replicate r3 3 = List.replicate (j + (r3 - j)) 3 := by
      congr 1; omega
    rw [hr3_rep, hsum_rep j (r3 - j)]
  obtain ⟨bs, hlen, hsum⟩ := maskedSum_of_perm hperm bs' hlen'
  have hbs_r : bs.length = N.r := by
    have hgl : N.gains.length = N.r := by simp [BypassNecklace.gains]
    omega
  let σ : Fin N.r → Bool := fun i => bs[i.val]'(by omega)
  refine ⟨N.junction ⟨0, by have := N.hr; omega⟩, N.cycleWalk σ, N.necklace_walk_isCycle σ, k, hk, ?_⟩
  rw [N.cycleWalk_length_decomp bs hbs_r, hsum, hsum']
  omega

theorem hasPowerCycle_of_hexagon_necklace {V : Type*} {G : SimpleGraph V}
    (N : BypassNecklace G) (r2 r4 : ℕ) (hr2 : 1 ≤ r2)
    (hEven : Even N.baseLength) (hL0 : 4 ≤ N.baseLength)
    (hperm : (List.replicate r2 2 ++ List.replicate r4 4).Perm N.gains)
    (hspan : N.baseLength - 2 ≤ 2 * r2 + 4 * r4) :
    HasPowerCycle G := by
  let cs : List ℕ := N.gains.map (· / 2)
  have hgains_even : ∀ d ∈ N.gains, d % 2 = 0 := by
    intro d hd
    have hd' := hperm.symm.subset hd
    rw [List.mem_append] at hd'
    rcases hd' with h | h
    · rw [List.mem_replicate] at h; omega
    · rw [List.mem_replicate] at h; omega
  have hgains : N.gains = cs.map (2 * ·) := by
    unfold cs
    rw [List.map_map]
    conv_lhs => rw [← List.map_id N.gains]
    apply List.map_congr_left
    intro d hd
    have hmod := hgains_even d hd
    simp; omega
  have hperm_cs : (List.replicate r2 1 ++ List.replicate r4 2).Perm cs := by
    have hmap := hperm.map (· / 2)
    simpa [cs, List.map_append, List.map_replicate] using hmap
  have hsum_cs : cs.sum = r2 + 2 * r4 := by
    rw [← hperm_cs.sum_eq, List.sum_append]
    simp; ring
  exact hasPowerCycle_of_perm_brown_even_necklace N hEven hL0 hgains hperm_cs
    (brown_unit_hexagon_halved_gains r2 r4 hr2) (by omega)

theorem hasPowerCycle_of_heptagon_necklace {V : Type*} {G : SimpleGraph V}
    (N : BypassNecklace G) (r1 r3 r5 : ℕ) (hr1 : 2 ≤ r1) (hr3 : 1 ≤ r3)
    (hperm : ((List.replicate r1 1 ++ List.replicate r3 3) ++ List.replicate r5 5).Perm N.gains)
    (hspan : N.baseLength - 2 ≤ r1 + 3 * r3 + 5 * r5) :
    HasPowerCycle G := by
  have hsum : N.gains.sum = r1 + 3 * r3 + 5 * r5 := by
    rw [← hperm.sum_eq, List.sum_append, List.sum_append]
    simp; ring
  exact hasPowerCycle_of_perm_brown_unit_necklace N hperm
    (brown_unit_heptagon_gains r1 r3 r5 hr1 hr3) (by omega)

/-! ### 5. Pillar 3: Unconditional `C-N-R` Girth-5 Structural Exclusions -/

private theorem walk3_isCycle {V : Type*} {G : SimpleGraph V} {a b c : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a)
    (h1 : a ≠ b) (h2 : a ≠ c) (h3 : b ≠ c) :
    HasCycleOfLength G 3 := by
  let p : G.Walk a a := .cons hab (.cons hbc (.cons hca .nil))
  refine ⟨a, p, isCycle_of_dropLast_nodup p (by simp [p]) ?_, rfl⟩
  simp [p, h1, h2, h3]

private theorem walk4_isCycle {V : Type*} {G : SimpleGraph V} {a b c d : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (h1 : a ≠ b) (h2 : a ≠ c) (h3 : a ≠ d) (h4 : b ≠ c) (h5 : b ≠ d) (h6 : c ≠ d) :
    HasCycleOfLength G 4 := by
  let p : G.Walk a a := .cons hab (.cons hbc (.cons hcd (.cons hda .nil)))
  refine ⟨a, p, isCycle_of_dropLast_nodup p (by simp [p]) ?_, rfl⟩
  simp [p, h1, h2, h3, h4, h5, h6]

private theorem walk8_isCycle {V : Type*} {G : SimpleGraph V}
    {x0 x1 x2 x3 x4 x5 x6 x7 : V}
    (e0 : G.Adj x0 x1) (e1 : G.Adj x1 x2) (e2 : G.Adj x2 x3) (e3 : G.Adj x3 x4)
    (e4 : G.Adj x4 x5) (e5 : G.Adj x5 x6) (e6 : G.Adj x6 x7) (e7 : G.Adj x7 x0)
    (hnodup : ([x0, x1, x2, x3, x4, x5, x6, x7] : List V).Nodup) :
    HasCycleOfLength G 8 := by
  let p : G.Walk x0 x0 :=
    .cons e0 (.cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 .nil)))))))
  refine ⟨x0, p, isCycle_of_dropLast_nodup p (by simp [p]) ?_, rfl⟩
  simpa [p] using hnodup

theorem c5_external_neighbors_distinct {V : Type*} {G : SimpleGraph V}
    (hno3 : ¬ HasCycleOfLength G 3) (hno4 : ¬ HasCycleOfLength G 4)
    (v w : Fin 5 → V) (hv_inj : Function.Injective v)
    (hcyc : ∀ i : Fin 5, G.Adj (v i) (v (i + 1)))
    (hext : ∀ i : Fin 5, G.Adj (v i) (w i))
    (hdisj : ∀ i j : Fin 5, w i ≠ v j) :
    Function.Injective w := by
  intro i j hij
  by_contra hne
  have hcase : j = i + 1 ∨ i = j + 1 ∨ j = i + 2 ∨ i = j + 2 := by
    fin_cases i <;> fin_cases j <;> simp_all
  rcases hcase with rfl | rfl | rfl | rfl
  · exact hno3 (walk3_isCycle (hcyc i) (hext (i + 1)) (hij ▸ (hext i).symm)
      (fun h => hne (hv_inj h)) (fun h => hdisj (i + 1) i h.symm)
      (fun h => hdisj (i + 1) (i + 1) h.symm))
  · exact hno3 (walk3_isCycle (hcyc j) (hext (j + 1)) (hij.symm ▸ (hext j).symm)
      (fun h => hne (hv_inj h).symm) (fun h => hdisj (j + 1) j h.symm)
      (fun h => hdisj (j + 1) (j + 1) h.symm))
  · have hi2 : i + 1 + 1 = i + 2 := by fin_cases i <;> decide
    have hc12 : G.Adj (v (i + 1)) (v (i + 2)) := by rw [← hi2]; exact hcyc (i + 1)
    have hne01 : i ≠ i + 1 := by fin_cases i <;> decide
    have hne12 : i + 1 ≠ i + 2 := by fin_cases i <;> decide
    exact hno4 (walk4_isCycle (hcyc i) hc12 (hext (i + 2)) (hij ▸ (hext i).symm)
      (fun h => hne01 (hv_inj h)) (fun h => hne (hv_inj h))
      (fun h => hdisj (i + 2) i h.symm) (fun h => hne12 (hv_inj h))
      (fun h => hdisj (i + 2) (i + 1) h.symm) (fun h => hdisj (i + 2) (i + 2) h.symm))
  · have hj2 : j + 1 + 1 = j + 2 := by fin_cases j <;> decide
    have hc12 : G.Adj (v (j + 1)) (v (j + 2)) := by rw [← hj2]; exact hcyc (j + 1)
    have hne01 : j ≠ j + 1 := by fin_cases j <;> decide
    have hne12 : j + 1 ≠ j + 2 := by fin_cases j <;> decide
    exact hno4 (walk4_isCycle (hcyc j) hc12 (hext (j + 2)) (hij.symm ▸ (hext j).symm)
      (fun h => hne01 (hv_inj h)) (fun h => hne (hv_inj h).symm)
      (fun h => hdisj (j + 2) j h.symm) (fun h => hne12 (hv_inj h))
      (fun h => hdisj (j + 2) (j + 1) h.symm) (fun h => hdisj (j + 2) (j + 2) h.symm))

theorem c5_external_no_adjacent_edge {V : Type*} {G : SimpleGraph V}
    (hno4 : ¬ HasCycleOfLength G 4)
    (v w : Fin 5 → V) (hv_inj : Function.Injective v)
    (hcyc : ∀ i : Fin 5, G.Adj (v i) (v (i + 1)))
    (hext : ∀ i : Fin 5, G.Adj (v i) (w i))
    (hdisj : ∀ i j : Fin 5, w i ≠ v j) (i : Fin 5) :
    ¬ G.Adj (w i) (w (i + 1)) := by
  intro hadj
  have hne_v : v i ≠ v (i + 1) := fun h => by
    have := hv_inj h; fin_cases i <;> simp at this
  have hne_w : w i ≠ w (i + 1) := G.ne_of_adj hadj
  exact hno4 (walk4_isCycle (hext i) hadj (hext (i + 1)).symm (hcyc i).symm
    (fun h => hdisj i i h.symm) (fun h => hdisj (i + 1) i h.symm) hne_v
    hne_w (hdisj i (i + 1)) (hdisj (i + 1) (i + 1)))

private theorem c5_ext_two_shared_c8 {V : Type*} {G : SimpleGraph V}
    (v w : Fin 5 → V) (hv_inj : Function.Injective v) (hw_inj : Function.Injective w)
    (hcyc : ∀ k : Fin 5, G.Adj (v k) (v (k + 1)))
    (hext : ∀ k : Fin 5, G.Adj (v k) (w k))
    (hdisj : ∀ a b : Fin 5, w a ≠ v b)
    (i : Fin 5) (h1 : G.Adj (w i) (w (i + 2))) (h2 : G.Adj (w (i + 2)) (w (i + 4))) :
    HasCycleOfLength G 8 := by
  have he43 : G.Adj (v (i + 4)) (v (i + 3)) := by
    have : i + 3 + 1 = i + 4 := by fin_cases i <;> decide
    rw [← this]; exact (hcyc (i + 3)).symm
  have he32 : G.Adj (v (i + 3)) (v (i + 2)) := by
    have : i + 2 + 1 = i + 3 := by fin_cases i <;> decide
    rw [← this]; exact (hcyc (i + 2)).symm
  have he21 : G.Adj (v (i + 2)) (v (i + 1)) := by
    have : i + 1 + 1 = i + 2 := by fin_cases i <;> decide
    rw [← this]; exact (hcyc (i + 1)).symm
  refine walk8_isCycle (hext i) h1 h2 (hext (i + 4)).symm he43 he32 he21 (hcyc i).symm ?_
  have hv_ne : ∀ a b : Fin 5, a ≠ b → v a ≠ v b := fun a b h heq => h (hv_inj heq)
  have hw_ne : ∀ a b : Fin 5, a ≠ b → w a ≠ w b := fun a b h heq => h (hw_inj heq)
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true,
    List.nodup_nil, and_true]
  refine ⟨⟨(hdisj i i).symm, (hdisj (i+2) i).symm, (hdisj (i+4) i).symm,
      hv_ne _ _ (by fin_cases i <;> decide), hv_ne _ _ (by fin_cases i <;> decide),
      hv_ne _ _ (by fin_cases i <;> decide), hv_ne _ _ (by fin_cases i <;> decide)⟩,
    ⟨hw_ne _ _ (by fin_cases i <;> decide), hw_ne _ _ (by fin_cases i <;> decide),
      hdisj _ _, hdisj _ _, hdisj _ _, hdisj _ _⟩,
    ⟨hw_ne _ _ (by fin_cases i <;> decide), hdisj _ _, hdisj _ _, hdisj _ _, hdisj _ _⟩,
    ⟨hdisj _ _, hdisj _ _, hdisj _ _, hdisj _ _⟩,
    ⟨hv_ne _ _ (by fin_cases i <;> decide), hv_ne _ _ (by fin_cases i <;> decide),
      hv_ne _ _ (by fin_cases i <;> decide)⟩,
    ⟨hv_ne _ _ (by fin_cases i <;> decide), hv_ne _ _ (by fin_cases i <;> decide)⟩,
    hv_ne _ _ (by fin_cases i <;> decide)⟩

private theorem c5_ext_two_disjoint_c8 {V : Type*} {G : SimpleGraph V}
    (v w : Fin 5 → V) (hv_inj : Function.Injective v) (hw_inj : Function.Injective w)
    (hcyc : ∀ k : Fin 5, G.Adj (v k) (v (k + 1)))
    (hext : ∀ k : Fin 5, G.Adj (v k) (w k))
    (hdisj : ∀ a b : Fin 5, w a ≠ v b)
    (i : Fin 5) (h1 : G.Adj (w i) (w (i + 2))) (h2 : G.Adj (w (i + 1)) (w (i + 3))) :
    HasCycleOfLength G 8 := by
  have he23 : G.Adj (v (i + 2)) (v (i + 3)) := by
    have : i + 2 + 1 = i + 3 := by fin_cases i <;> decide
    rw [← this]; exact hcyc (i + 2)
  refine walk8_isCycle (hext i) h1 (hext (i + 2)).symm he23 (hext (i + 3)) h2.symm
    (hext (i + 1)).symm (hcyc i).symm ?_
  have hv_ne : ∀ a b : Fin 5, a ≠ b → v a ≠ v b := fun a b h heq => h (hv_inj heq)
  have hw_ne : ∀ a b : Fin 5, a ≠ b → w a ≠ w b := fun a b h heq => h (hw_inj heq)
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true,
    List.nodup_nil, and_true]
  refine ⟨⟨(hdisj i i).symm, (hdisj (i+2) i).symm, hv_ne _ _ (by fin_cases i <;> decide),
      hv_ne _ _ (by fin_cases i <;> decide), (hdisj (i+3) i).symm, (hdisj (i+1) i).symm,
      hv_ne _ _ (by fin_cases i <;> decide)⟩,
    ⟨hw_ne _ _ (by fin_cases i <;> decide), hdisj _ _, hdisj _ _,
      hw_ne _ _ (by fin_cases i <;> decide), hw_ne _ _ (by fin_cases i <;> decide), hdisj _ _⟩,
    ⟨hdisj _ _, hdisj _ _, hw_ne _ _ (by fin_cases i <;> decide),
      hw_ne _ _ (by fin_cases i <;> decide), hdisj _ _⟩,
    ⟨hv_ne _ _ (by fin_cases i <;> decide), (hdisj (i+3) (i+2)).symm, (hdisj (i+1) (i+2)).symm,
      hv_ne _ _ (by fin_cases i <;> decide)⟩,
    ⟨(hdisj (i+3) (i+3)).symm, (hdisj (i+1) (i+3)).symm, hv_ne _ _ (by fin_cases i <;> decide)⟩,
    ⟨hw_ne _ _ (by fin_cases i <;> decide), hdisj _ _⟩,
    hdisj _ _⟩

theorem c5_external_at_most_one_edge {V : Type*} {G : SimpleGraph V}
    (hno3 : ¬ HasCycleOfLength G 3) (hno4 : ¬ HasCycleOfLength G 4) (hno8 : ¬ HasCycleOfLength G 8)
    (v w : Fin 5 → V) (hv_inj : Function.Injective v)
    (hcyc : ∀ k : Fin 5, G.Adj (v k) (v (k + 1)))
    (hext : ∀ k : Fin 5, G.Adj (v k) (w k))
    (hdisj : ∀ a b : Fin 5, w a ≠ v b)
    {i j : Fin 5} (hi : G.Adj (w i) (w (i + 2))) (hj : G.Adj (w j) (w (j + 2))) :
    i = j := by
  have hw_inj := c5_external_neighbors_distinct hno3 hno4 v w hv_inj hcyc hext hdisj
  by_contra hne
  have hrel : j = i + 1 ∨ j = i + 2 ∨ i = j + 2 ∨ i = j + 1 := by
    fin_cases i <;> fin_cases j <;> simp_all
  rcases hrel with rfl | rfl | rfl | rfl
  · have h : i + 1 + 2 = i + 3 := by fin_cases i <;> decide
    exact hno8 (c5_ext_two_disjoint_c8 v w hv_inj hw_inj hcyc hext hdisj i hi (by rw [← h]; exact hj))
  · have h : i + 2 + 2 = i + 4 := by fin_cases i <;> decide
    exact hno8 (c5_ext_two_shared_c8 v w hv_inj hw_inj hcyc hext hdisj i hi (by rw [← h]; exact hj))
  · have h : j + 2 + 2 = j + 4 := by fin_cases j <;> decide
    exact hno8 (c5_ext_two_shared_c8 v w hv_inj hw_inj hcyc hext hdisj j hj (by rw [← h]; exact hi))
  · have h : j + 1 + 2 = j + 3 := by fin_cases j <;> decide
    exact hno8 (c5_ext_two_disjoint_c8 v w hv_inj hw_inj hcyc hext hdisj j hj (by rw [← h]; exact hi))

theorem same_scale_dyadic_plus_one_no_single_edge_overlap {V : Type*} {G : SimpleGraph V}
    {u v : V} {k : ℕ} (hk : 2 ≤ k)
    (p q : G.Walk u v) (hp : p.IsPath) (hq : q.IsPath)
    (hlen_p : p.length = 2 ^ k) (hlen_q : q.length = 2 ^ k)
    (hdisj : List.Disjoint p.support.dropLast q.reverse.support.dropLast) :
    HasPowerCycle G := by
  let w : G.Walk u u := p.append q.reverse
  have hlen_w : w.length = 2 ^ (k + 1) := by
    simp only [w, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse, hlen_p, hlen_q]
    ring
  have hlen3 : 3 ≤ w.length := by
    rw [hlen_w]
    have h4 : 4 ≤ 2 ^ k := by
      have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
      simpa using this
    have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    omega
  have hnodup : w.support.dropLast.Nodup := by
    rw [show w.support.dropLast = p.support.dropLast ++ q.reverse.support.dropLast from
      walk_support_dropLast_append p q.reverse]
    rw [List.nodup_append]
    exact ⟨hp.support_nodup.sublist (List.dropLast_sublist _),
      hq.reverse.support_nodup.sublist (List.dropLast_sublist _),
      fun a ha b hb heq => hdisj ha (heq ▸ hb)⟩
  exact ⟨u, w, isCycle_of_dropLast_nodup w hlen3 hnodup, k + 1, by omega, hlen_w⟩

/-! ### 6. Pillar 4: Strict-Interior Hitting-Edge Elimination on `EG2-CORE` (`H[V_3]`) -/

def gainsWithout {V : Type*} {G : SimpleGraph V} (N : BypassNecklace G) (i0 : Fin N.r) : List ℕ :=
  ((List.finRange N.r).erase i0).map (fun i => (N.segB i).length - (N.segA i).length)

theorem strict_interior_avoids_seg_edges {V : Type*} {G : SimpleGraph V}
    (N : BypassNecklace G) (i0 : Fin N.r) {ds' : List ℕ}
    (hperm : ds'.Perm (gainsWithout N i0)) (hB : BrownUnit ds')
    (m : ℕ) (hm : 2 ≤ m)
    (hlo : N.baseLength + ((N.segB i0).length - (N.segA i0).length) ≤ 2 ^ m)
    (hhi : 2 ^ m ≤ N.baseLength + (gainsWithout N i0).sum) :
    (∃ σ : Fin N.r → Bool, σ i0 = false ∧ (N.cycleWalk σ).IsCycle ∧ (N.cycleWalk σ).length = 2 ^ m) ∧
    (∃ σ : Fin N.r → Bool, σ i0 = true ∧ (N.cycleWalk σ).IsCycle ∧ (N.cycleWalk σ).length = 2 ^ m) := by
  let Δ0 := (N.segB i0).length - (N.segA i0).length
  let idxList := (List.finRange N.r).erase i0
  have hlen_gw : (gainsWithout N i0).length = idxList.length := by
    simp [gainsWithout, idxList]
  have build : ∀ (b0 : Bool) (t : ℕ), t ≤ (gainsWithout N i0).sum →
      ∃ σ : Fin N.r → Bool, σ i0 = b0 ∧ (N.cycleWalk σ).IsCycle ∧
        (N.cycleWalk σ).length = N.baseLength + (if b0 then Δ0 else 0) + t := by
    intro b0 t ht
    obtain ⟨bs_rem, hlen_rem, hsum_rem⟩ := brown_unit_perm_complete hperm hB t ht
    have hnodup_idx : idxList.Nodup := (List.nodup_finRange N.r).erase i0
    have hnotmem_i0 : i0 ∉ idxList := (List.nodup_finRange N.r).not_mem_erase
    classical
    let σ : Fin N.r → Bool := fun j =>
      if h : j = i0 then b0
      else
        let pos := idxList.idxOf j
        if hpos : pos < bs_rem.length then bs_rem[pos]'hpos else false
    have hσ_i0 : σ i0 = b0 := by simp [σ]
    have hlen_bs_idx : bs_rem.length = idxList.length := by omega
    have hσ_idx : ∀ (k : ℕ) (hk : k < idxList.length),
        bs_rem[k]'(by omega) = σ (idxList[k]'hk) := by
      intro k hk
      have hne : idxList[k]'hk ≠ i0 := by
        intro heq; exact hnotmem_i0 (heq ▸ List.getElem_mem hk)
      have hidx : idxList.idxOf (idxList[k]'hk) = k :=
        List.Nodup.idxOf_getElem hnodup_idx k hk
      have hk_bs : k < bs_rem.length := by omega
      simp [σ, hne, hidx, hk_bs]
    have hperm_fin : (i0 :: idxList).Perm (List.finRange N.r) :=
      (List.perm_cons_erase (List.mem_finRange i0)).symm
    have hlen_eq : (N.cycleWalk σ).length =
        ((i0 :: idxList).map (fun j => (N.seg σ j).length)).sum := by
      rw [N.cycleWalk_length_eq σ]
      exact (hperm_fin.map (fun j => (N.seg σ j).length)).sum_eq.symm
    have hbase_eq : N.baseLength =
        ((i0 :: idxList).map (fun j => (N.segA j).length)).sum := by
      unfold BypassNecklace.baseLength
      exact (hperm_fin.map (fun j => (N.segA j).length)).sum_eq.symm
    have hseg0 : (N.seg σ i0).length = (N.segA i0).length + (if b0 then Δ0 else 0) := by
      rw [N.seg_length_eq σ i0, hσ_i0]
    have hrem_calc := N.list_seg_length_sum σ idxList bs_rem hlen_bs_idx hσ_idx
    refine ⟨σ, hσ_i0, N.necklace_walk_isCycle σ, ?_⟩
    rw [hlen_eq, hbase_eq]
    simp only [List.map_cons, List.sum_cons]
    rw [hseg0, hrem_calc]
    change (N.segA i0).length + (if b0 then Δ0 else 0) +
      ((idxList.map (fun j => (N.segA j).length)).sum + maskedSum (gainsWithout N i0) bs_rem) =
      (N.segA i0).length + (idxList.map (fun j => (N.segA j).length)).sum +
        (if b0 then Δ0 else 0) + t
    rw [hsum_rem]
    omega
  constructor
  · obtain ⟨σ, hσ, hcyc, hlen⟩ := build false (2 ^ m - N.baseLength) (by omega)
    exact ⟨σ, hσ, hcyc, by simp only [Bool.false_eq_true, ↓reduceIte] at hlen; omega⟩
  · obtain ⟨σ, hσ, hcyc, hlen⟩ := build true (2 ^ m - N.baseLength - Δ0) (by omega)
    exact ⟨σ, hσ, hcyc, by simp only [↓reduceIte] at hlen; omega⟩

theorem no_hitting_edge_on_strict_interior_adjuster {V : Type*} {H : SimpleGraph V}
    (N : BypassNecklace H) (i0 : Fin N.r) {ds' : List ℕ}
    (hperm : ds'.Perm (gainsWithout N i0)) (hB : BrownUnit ds')
    (m : ℕ) (hm : 2 ≤ m)
    (hlo : N.baseLength + ((N.segB i0).length - (N.segA i0).length) ≤ 2 ^ m)
    (hhi : 2 ^ m ≤ N.baseLength + (gainsWithout N i0).sum)
    {e : Sym2 V}
    (hnotB : e ∉ (N.segB i0).edges)
    (hnotOther : ∀ j : Fin N.r, j ≠ i0 → e ∉ (N.segA j).edges ∧ e ∉ (N.segB j).edges) :
    ¬ IsHittingEdge H e := by
  intro hhit
  obtain ⟨_, σ, hσ, hcyc, hlen⟩ := strict_interior_avoids_seg_edges N i0 hperm hB m hm hlo hhi
  have hmem : e ∈ (N.cycleWalk σ).edges := hhit.2 _ (N.cycleWalk σ) hcyc ⟨m, hm, hlen⟩
  rw [N.cycleWalk_edges σ, List.mem_flatMap] at hmem
  obtain ⟨j, _, hj⟩ := hmem
  by_cases hji : j = i0
  · subst hji
    simp only [BypassNecklace.seg, hσ, ↓reduceIte] at hj
    exact hnotB hj
  · have ho := hnotOther j hji
    cases hσj : σ j
    · simp only [BypassNecklace.seg, hσj, Bool.false_eq_true, ↓reduceIte] at hj
      exact ho.1 hj
    · simp only [BypassNecklace.seg, hσj, ↓reduceIte] at hj
      exact ho.2 hj

end E64Wave7Agent1
