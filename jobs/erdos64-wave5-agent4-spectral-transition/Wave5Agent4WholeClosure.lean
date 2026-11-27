import NonBacktrackingGirth
import Wave4Agent6GlobalClosure

/-!
# Erdős Problem #64 — Wave 5 Agent #4 Dual-Pillar Whole-Problem Closure (Lean 4.36.0)

All theorems are all-order (no bound on `|V|`), zero-`sorry`, zero-`native_decide`,
and depend only on standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Pillar 1: Second-Window Non-Backtracking Spectral Closure (`2g ≤ L < 3g`)
Extends Wave 4 Agent #1 (`E64NonBacktrackingGirth`) past the `L < 2g` barrier:
1. `nonBacktracking_lt_girth_add_two_isCyclicallyNonBacktracking`:
   No non-backtracking lollipop of length `< g + 2` exists in a graph of girth `≥ g`.
2. `nonBacktracking_lt_girth_add_two_isCycle`:
   Every nonempty non-backtracking closed walk of length `< g + 2` (`g ≥ 3`) is a simple cycle.
3. `no_nonBacktracking_closed_pow2_lt_girth_add_two`:
   In a power-free graph of girth `≥ g ≥ 3`, `A^(2^k)_{v,v} = 0` identically whenever `2^k < g + 2`.
4. `tailless_pow2_lt_three_girth_not_square`:
   In a power-free graph of girth `≥ g`, no tailless closed walk of length `2^(k+1) < 3g` is a square.
5. `nonSimple_tailless_exists_split_ge_girth`:
   Every non-simple tailless closed walk of length `L` splits at a repeated vertex into two
   nonempty non-backtracking closed walks of lengths `r, L - r ≥ g`.
6. `nonSimple_tailless_mersenne_girth_split_lengths`:
   At Mersenne girth `g = 2^k - 1` (`k ≥ 3`) in a power-free graph, every non-simple tailless
   closed walk of length `2^(k+1) = 2g + 2` splits strictly into `(g, g + 2)` or `(g + 2, g)`.
7. `hasPower_of_second_window_no_split` & `erdos64_of_two_window_nonBacktracking`:
   Whole-problem conditional closure gate directly targeting `Erdos64Closure.HasPower`.

## Pillar 2: Exact Switching-Count Lift for 4-Regular Perfect-Matching Transition Systems
Upgrades Wave 4 Agent #6 (`E64Wave4Agent6.MContract`) with exact cycle lifting back to `G`:
8. `no_pow2_cycle_in_twoFactor`: The 2-factor `G \ m` contains no `2^k`-cycle.
9. `mcontract_general_switching_lift`: Every simple cycle of length `L ≥ 3` in `MContract G m`
   with `S` switching vertices lifts to a simple cycle in `G` of length **exactly** `L + S`.
10. `mcontract_cycle_length_plus_switches_not_pow2`: In any power-free `G`, `L + S ≠ 2^r` (`r ≥ 2`).
11. `mcontract_pow2_cycle_strictly_mixed`: Every `2^k`-cycle in `MContract G m` satisfies
    `1 ≤ S ≤ 2^k - 1` (neither 0-switching nor all-switching).
-/

namespace E64Wave5Agent4
open SimpleGraph Erdos64Closure E64NonBacktrackingGirth E64Wave4Agent6
open scoped Sym2

/-! ## Pillar 1: Second-Window Non-Backtracking Theory (`2g ≤ L < 3g`) -/

private theorem walk_eq_append_last {V : Type*} {G : SimpleGraph V} :
    ∀ {u v : V} (p : G.Walk u v), 1 ≤ p.length →
      ∃ (w : V) (r : G.Walk u w) (h : G.Adj w v), p = r.append (.cons h .nil)
  | _, _, .nil, hlen => by simp at hlen
  | _, _, .cons h .nil, _ => ⟨_, .nil, h, rfl⟩
  | _, _, .cons h₁ (.cons h₂ rest), _ => by
      obtain ⟨w, r, hlast, heq⟩ := walk_eq_append_last (.cons h₂ rest) (by simp)
      exact ⟨w, .cons h₁ r, hlast, by rw [Walk.cons_append, ← heq]⟩

private theorem isNonBacktracking_append_of_adj {V : Type*} {G : SimpleGraph V} :
    ∀ {u v w x : V} {p : G.Walk u v} {q : G.Walk v x}
      (hnbp : IsNonBacktracking p) (hnbq : IsNonBacktracking q)
      (hlast : ∃ (r : G.Walk u w) (h₁ : G.Adj w v), p = r.append (.cons h₁ .nil))
      (hfirst : ∃ (y : V) (h₂ : G.Adj v y) (s : G.Walk y x), q = .cons h₂ s ∧ w ≠ y),
      IsNonBacktracking (p.append q)
  | _, _, _, _, .nil, _, _, _, ⟨r, _, hnil⟩, _ => by
      have hlen := congrArg Walk.length hnil
      simp at hlen
  | _, _, _, _, .cons h₁ .nil, q, _, hnbq, ⟨r, h₁', heq⟩, ⟨y, h₂, s, hq, hwy⟩ => by
      have hr0 : r.length = 0 := by
        have hlen := congrArg Walk.length heq
        simp at hlen
        omega
      cases r with
      | nil =>
          simp only [Walk.nil_append] at heq
          cases heq
          subst hq
          exact ⟨hwy, hnbq⟩
      | cons _ _ => simp at hr0
  | _, _, _, _, .cons h₁ (.cons h₂ rest), q, hnbp, hnbq, ⟨r, hlast, heq⟩, hfirst => by
      cases r with
      | nil =>
          have hlen := congrArg Walk.length heq
          simp at hlen
      | cons h₁' r' =>
          simp only [Walk.cons_append] at heq
          cases heq
          simp only [Walk.cons_append, IsNonBacktracking]
          exact ⟨hnbp.1, isNonBacktracking_append_of_adj hnbp.2 hnbq ⟨r', hlast, rfl⟩ hfirst⟩

/-- In any graph of girth `≥ g`, every nonempty non-backtracking closed walk of length
`< g + 2` is automatically cyclically non-backtracking (tailless): no lollipops exist
below `g + 2`. -/
theorem nonBacktracking_lt_girth_add_two_isCyclicallyNonBacktracking {V : Type*} {G : SimpleGraph V}
    {g : ℕ} (hg : GirthAtLeast G g) {v : V} (p : G.Walk v v)
    (hnb : IsNonBacktracking p) (hpos : 1 ≤ p.length) (hlt : p.length < g + 2) :
    IsCyclicallyNonBacktracking p := by
  cases p with
  | nil => simp at hpos
  | cons (v := u) h₁ rest =>
      cases rest with
      | nil => exact False.elim (G.loopless v h₁)
      | cons h₂ rest₂ =>
          obtain ⟨w, r, hlast, heq⟩ := walk_eq_append_last (.cons h₂ rest₂) (by simp)
          have hpuw : u ≠ w := by
            intro huw
            subst huw
            cases r with
            | nil =>
                simp only [Walk.nil_append] at heq
                cases heq
                exact hnb.1 rfl
            | cons hr₁ hr₂ =>
                have hr_nb : IsNonBacktracking (.cons hr₁ hr₂) := by
                  have hnb_rest : IsNonBacktracking (.cons h₂ rest₂) := hnb.2
                  rw [heq] at hnb_rest
                  exact isNonBacktracking_of_append_left hnb_rest
                have hr_ge : g ≤ (Walk.cons hr₁ hr₂).length :=
                  girth_le_length_of_nonBacktracking_closed hg _ (.cons hr₁ hr₂) rfl (by simp) hr_nb
                have hlen : (Walk.cons h₁ (.cons h₂ rest₂)).length = (Walk.cons hr₁ hr₂).length + 2 := by
                  simp only [Walk.length_cons]
                  rw [heq, Walk.length_append]
                  simp
                  omega
                omega
          refine isNonBacktracking_append_of_adj hnb hnb ?_ ?_
          · exact ⟨.cons h₁ r, hlast, by rw [Walk.cons_append, ← heq]⟩
          · exact ⟨u, h₁, .cons h₂ rest₂, rfl, hpuw.symm⟩

/-- Every nonempty non-backtracking closed walk (even without assuming taillessness)
of length `< g + 2` in a graph of girth `≥ g ≥ 3` is a simple cycle. -/
theorem nonBacktracking_lt_girth_add_two_isCycle {V : Type*} {G : SimpleGraph V}
    {g : ℕ} (hg : GirthAtLeast G g) (hg3 : 3 ≤ g) {v : V} (p : G.Walk v v)
    (hnb : IsNonBacktracking p) (hpos : 1 ≤ p.length) (hlt : p.length < g + 2) :
    p.IsCycle := by
  have hcyc := nonBacktracking_lt_girth_add_two_isCyclicallyNonBacktracking hg p hnb hpos hlt
  exact tailless_nonBacktracking_lt_two_girth_isCycle hg p hcyc hpos (by omega)

/-- Exact zero-diagonal lemma: in a power-free graph of girth `≥ g ≥ 3`, if `2^k < g + 2`
(`k ≥ 2`), then there are ZERO non-backtracking closed walks (even with tails) of length `2^k`
at any vertex (`A^(2^k)_{v,v} = 0` identically). -/
theorem no_nonBacktracking_closed_pow2_lt_girth_add_two {V : Type*} {G : SimpleGraph V}
    {g k : ℕ} (hg : GirthAtLeast G g) (hg3 : 3 ≤ g) (hnp : ¬ HasPower G)
    (hk : 2 ≤ k) (hlt : 2 ^ k < g + 2) {v : V} (p : G.Walk v v)
    (hnb : IsNonBacktracking p) : p.length ≠ 2 ^ k := by
  intro hlen
  have hpos : 1 ≤ p.length := by rw [hlen]; exact Nat.one_le_two_pow
  have hcyc := nonBacktracking_lt_girth_add_two_isCycle hg hg3 p hnb hpos (by omega)
  exact hnp ⟨k, v, p, hk, hcyc, hlen⟩

/-- Power-Free Primitivity Theorem: in a power-free graph of girth `≥ g`, no cyclically
non-backtracking closed walk of length `2^(k+1) < 3g` (`k ≥ 2`) can be a square `q.append q`. -/
theorem tailless_pow2_lt_three_girth_not_square {V : Type*} {G : SimpleGraph V}
    {g k : ℕ} (hg : GirthAtLeast G g) (hnp : ¬ HasPower G)
    (hk : 2 ≤ k) (hlt : 2 ^ (k + 1) < 3 * g) {v : V} (p q : G.Walk v v)
    (hcyc : IsCyclicallyNonBacktracking p) (hlen : p.length = 2 ^ (k + 1)) :
    p ≠ q.append q := by
  intro hpq
  have hqlen : q.length = 2 ^ k := by
    have h1 : p.length = q.length + q.length := by rw [hpq, Walk.length_append]
    have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    omega
  have hqcyc : IsCyclicallyNonBacktracking q := by
    have hnbp : IsNonBacktracking p := isNonBacktracking_of_append_left hcyc
    rwa [hpq] at hnbp
  have hqlt : 2 ^ k < 2 * g := by
    have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    omega
  exact hnp (hasPower_of_cyclicallyNonBacktracking_lt_two_girth hg hk hqlt q hqcyc hqlen)

private theorem mem_support_of_mem_edges' {V : Type*} {G : SimpleGraph V} :
    ∀ {u v : V} {w : G.Walk u v} {a b : V},
      s(a, b) ∈ w.edges → a ∈ w.support ∧ b ∈ w.support
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons _ rest, a, b, h => by
      simp only [Walk.edges_cons, List.mem_cons] at h
      rcases h with heq | hmem
      · rw [Sym2.eq_iff] at heq
        rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨Walk.start_mem_support _, List.mem_cons_of_mem _ (Walk.start_mem_support rest)⟩
        · exact ⟨List.mem_cons_of_mem _ (Walk.start_mem_support rest), Walk.start_mem_support _⟩
      · obtain ⟨ha, hb⟩ := mem_support_of_mem_edges' hmem
        exact ⟨List.mem_cons_of_mem _ ha, List.mem_cons_of_mem _ hb⟩

private theorem closed_nodup_support_eq_nil' {V : Type*} {G : SimpleGraph V}
    {v : V} (w : G.Walk v v) (hnd : w.support.Nodup) : w = .nil := by
  cases w with
  | nil => rfl
  | cons _ rest =>
      simp only [Walk.support_cons, List.nodup_cons] at hnd
      exact absurd (Walk.end_mem_support rest) hnd.1

private theorem isCycle_of_nb_nodup_tail' {V : Type*} {G : SimpleGraph V}
    {v : V} (p : G.Walk v v) (hnb : IsNonBacktracking p) (hlen : 1 ≤ p.length)
    (hnd : p.support.tail.Nodup) : p.IsCycle := by
  cases p with
  | nil => simp at hlen
  | cons h rest =>
      have hrest_nd : rest.support.Nodup := by simpa [Walk.support_cons] using hnd
      have hrest_path : rest.IsPath := Walk.IsPath.mk' hrest_nd
      have hnotmem : s(v, _) ∉ rest.edges := by
        intro hmem
        cases rest with
        | nil => simp at hmem
        | cons h₂ rest₂ =>
            simp only [Walk.edges_cons, List.mem_cons] at hmem
            simp only [Walk.support_cons, List.nodup_cons] at hrest_nd
            rcases hmem with heq | hmem₂
            · rw [Sym2.eq_iff] at heq
              rcases heq with ⟨hvc, _⟩ | ⟨rfl, _⟩
              · exact G.ne_of_adj h hvc
              · have hnil := closed_nodup_support_eq_nil' rest₂ hrest_nd.2
                subst hnil
                exact hnb.1 rfl
            · obtain ⟨_, hc⟩ := mem_support_of_mem_edges' hmem₂
              exact hrest_nd.1 hc
      refine ⟨⟨?_⟩, by simp, hnd⟩
      simp only [Walk.edges_cons, List.nodup_cons]
      exact ⟨hnotmem, hrest_path.isTrail.edges_nodup⟩

private theorem exists_append_of_mem_support' {V : Type*} {G : SimpleGraph V} :
    ∀ {u v : V} (w : G.Walk u v) {x : V},
      x ∈ w.support → ∃ (w₁ : G.Walk u x) (w₂ : G.Walk x v), w = w₁.append w₂
  | _, _, .nil, _, hx => by
      simp only [Walk.support_nil, List.mem_singleton] at hx
      subst hx
      exact ⟨.nil, .nil, rfl⟩
  | _, _, .cons h rest, x, hx => by
      simp only [Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hmem
      · exact ⟨.nil, .cons h rest, rfl⟩
      · obtain ⟨w₁, w₂, heq⟩ := exists_append_of_mem_support' rest hmem
        exact ⟨.cons h w₁, w₂, by rw [Walk.cons_append, ← heq]⟩

private theorem exists_append_of_mem_support_tail' {V : Type*} {G : SimpleGraph V} :
    ∀ {u v : V} (w : G.Walk u v) {x : V},
      x ∈ w.support.tail →
      ∃ (w₁ : G.Walk u x) (w₂ : G.Walk x v), w = w₁.append w₂ ∧ 1 ≤ w₁.length
  | _, _, .nil, _, hx => by simp at hx
  | _, _, .cons h rest, x, hx => by
      simp only [Walk.support_cons, List.tail_cons] at hx
      obtain ⟨w₁, w₂, heq⟩ := exists_append_of_mem_support' rest hx
      exact ⟨.cons h w₁, w₂, by rw [Walk.cons_append, ← heq], by simp⟩

private theorem exists_split_of_not_nodup_tail' {V : Type*} {G : SimpleGraph V} :
    ∀ {u v : V} (w : G.Walk u v), ¬ w.support.tail.Nodup →
      ∃ (x : V) (w₁ : G.Walk u x) (w₂ : G.Walk x x) (w₃ : G.Walk x v),
        w = w₁.append (w₂.append w₃) ∧ 1 ≤ w₁.length ∧ 1 ≤ w₂.length
  | _, _, .nil, hnd => by simp at hnd
  | _, _, .cons (v := c) h rest, hnd => by
      have hnd' : ¬ rest.support.Nodup := by simpa [Walk.support_cons] using hnd
      cases rest with
      | nil => simp at hnd'
      | cons h₂ rest₂ =>
          simp only [Walk.support_cons, List.nodup_cons, not_and_or, not_not] at hnd'
          rcases hnd' with hmem | hnd₂
          · have hmem' : c ∈ (Walk.cons h₂ rest₂).support.tail := by
              simpa [Walk.support_cons] using hmem
            obtain ⟨w₂, w₃, heq, hw₂⟩ := exists_append_of_mem_support_tail' (.cons h₂ rest₂) hmem'
            exact ⟨c, .cons h .nil, w₂, w₃, by simp [heq], by simp, hw₂⟩
          · have hnd₂' : ¬ (Walk.cons h₂ rest₂).support.tail.Nodup := by
              simpa [Walk.support_cons] using hnd₂
            obtain ⟨x, w₁, w₂, w₃, heq, hw₁, hw₂⟩ :=
              exists_split_of_not_nodup_tail' (.cons h₂ rest₂) hnd₂'
            exact ⟨x, .cons h w₁, w₂, w₃, by simp [heq], by simp; omega, hw₂⟩

/-- **Second-Window Repeated-Vertex Split Theorem**:
Every nonempty cyclically non-backtracking closed walk `p` that is NOT a simple cycle
splits at a repeated vertex `x` into two nonempty non-backtracking closed walks `q₁, q₂`
at `x`, each of length `≥ g`, with `q₁.length + q₂.length = p.length`. -/
theorem nonSimple_tailless_exists_split_ge_girth {V : Type*} {G : SimpleGraph V}
    {g : ℕ} (hg : GirthAtLeast G g) {v : V} (p : G.Walk v v)
    (hcyc : IsCyclicallyNonBacktracking p) (hpos : 1 ≤ p.length) (hns : ¬ p.IsCycle) :
    ∃ (x : V) (q₁ q₂ : G.Walk x x),
      IsNonBacktracking q₁ ∧ IsNonBacktracking q₂ ∧
      g ≤ q₁.length ∧ g ≤ q₂.length ∧ q₁.length + q₂.length = p.length := by
  have hnb : IsNonBacktracking p := isNonBacktracking_of_append_left hcyc
  have hnd : ¬ p.support.tail.Nodup := fun hnd => hns (isCycle_of_nb_nodup_tail' p hnb hpos hnd)
  obtain ⟨x, p₁, p₂, p₃, heq, hp₁, hp₂⟩ := exists_split_of_not_nodup_tail' p hnd
  have hnb₂ : IsNonBacktracking p₂ :=
    isNonBacktracking_of_append_left (isNonBacktracking_of_append_right (heq ▸ hnb))
  have hpp : p.append p = p₁.append (p₂.append ((p₃.append p₁).append (p₂.append p₃))) := by
    conv_lhs => rw [heq]
    simp only [Walk.append_assoc]
  have hnb₃₁ : IsNonBacktracking (p₃.append p₁) :=
    isNonBacktracking_of_append_left
      (isNonBacktracking_of_append_right
        (isNonBacktracking_of_append_right (hpp ▸ hcyc)))
  have hg₂ : g ≤ p₂.length :=
    girth_le_length_of_nonBacktracking_closed hg p₂.length p₂ rfl hp₂ hnb₂
  have hpos₃₁ : 1 ≤ (p₃.append p₁).length := by rw [Walk.length_append]; omega
  have hg₃₁ : g ≤ (p₃.append p₁).length :=
    girth_le_length_of_nonBacktracking_closed hg _ (p₃.append p₁) rfl hpos₃₁ hnb₃₁
  have hsum : p₂.length + (p₃.append p₁).length = p.length := by
    rw [heq, Walk.length_append, Walk.length_append, Walk.length_append]
    omega
  exact ⟨x, p₂, p₃.append p₁, hnb₂, hnb₃₁, hg₂, hg₃₁, hsum⟩

/-- **Exact Mersenne-Girth Split Exclusion**:
In any power-free graph of Mersenne girth `g = 2^k - 1` (`k ≥ 3`), every non-simple
cyclically non-backtracking closed walk of length `2^(k+1) = 2g + 2` splits strictly into
lengths `(g, g + 2)` or `(g + 2, g)` — the midpoint split `(2^k, 2^k)` is forbidden. -/
theorem nonSimple_tailless_mersenne_girth_split_lengths {V : Type*} {G : SimpleGraph V}
    {k : ℕ} (hk : 3 ≤ k) (hg : GirthAtLeast G (2 ^ k - 1)) (hnp : ¬ HasPower G)
    {v : V} (p : G.Walk v v) (hcyc : IsCyclicallyNonBacktracking p)
    (hlen : p.length = 2 ^ (k + 1)) (hns : ¬ p.IsCycle) :
    ∃ (x : V) (q₁ q₂ : G.Walk x x),
      IsNonBacktracking q₁ ∧ IsNonBacktracking q₂ ∧
      ((q₁.length = 2 ^ k - 1 ∧ q₂.length = 2 ^ k + 1) ∨
       (q₁.length = 2 ^ k + 1 ∧ q₂.length = 2 ^ k - 1)) := by
  have hpos : 1 ≤ p.length := by rw [hlen]; exact Nat.one_le_two_pow
  obtain ⟨x, q₁, q₂, hnb₁, hnb₂, hg₁, hg₂, hsum⟩ :=
    nonSimple_tailless_exists_split_ge_girth hg p hcyc hpos hns
  have hpow8 : 8 ≤ 2 ^ k := by
    have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
    omega
  have hg3 : 3 ≤ 2 ^ k - 1 := by omega
  have h2k : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  have hneq : q₁.length ≠ 2 ^ k :=
    no_nonBacktracking_closed_pow2_lt_girth_add_two hg hg3 hnp (by omega) (by omega) q₁ hnb₁
  refine ⟨x, q₁, q₂, hnb₁, hnb₂, ?_⟩
  omega

/-- If a cyclically non-backtracking closed walk of length `2^k` (`k ≥ 2`) admits NO
valid non-simple split into two non-backtracking closed walks of lengths `≥ g` summing
to `2^k`, then `HasPower G` holds. -/
theorem hasPower_of_second_window_no_split {V : Type*} {G : SimpleGraph V}
    {g k : ℕ} (hg : GirthAtLeast G g) (hk : 2 ≤ k) {v : V} (p : G.Walk v v)
    (hcyc : IsCyclicallyNonBacktracking p) (hlen : p.length = 2 ^ k)
    (hnosplit : ¬ ∃ (x : V) (q₁ q₂ : G.Walk x x),
      IsNonBacktracking q₁ ∧ IsNonBacktracking q₂ ∧
      g ≤ q₁.length ∧ g ≤ q₂.length ∧ q₁.length + q₂.length = 2 ^ k) :
    HasPower G := by
  by_cases hc : p.IsCycle
  · exact ⟨k, v, p, hk, hc, hlen⟩
  · exfalso
    have hpos : 1 ≤ p.length := by rw [hlen]; exact Nat.one_le_two_pow
    obtain ⟨x, q₁, q₂, hnb₁, hnb₂, hg₁, hg₂, hsum⟩ :=
      nonSimple_tailless_exists_split_ge_girth hg p hcyc hpos hc
    exact hnosplit ⟨x, q₁, q₂, hnb₁, hnb₂, hg₁, hg₂, by omega⟩

/-- **Whole-Problem Closure Gate #1 (Two-Window Non-Backtracking Spectral Closure)**:
If every finite simple graph with `δ(G) ≥ 3` has either a Window-1 (`2^k < 2g`) tailless
closed walk OR a Window-2 tailless closed walk of length `2^k` without a valid `(q₁, q₂)`
non-simple split (e.g., certified by `Tr(B^(2^k)) > NonSimple(2^k)`), then the entire
Erdős–Gyárfás Conjecture (`HasPower G`) is CLOSED. -/
theorem erdos64_of_two_window_nonBacktracking
    (H : ∀ {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (∀ v : V, 3 ≤ G.degree v) →
      ∃ (g k : ℕ) (v : V) (p : G.Walk v v),
        GirthAtLeast G g ∧ 2 ≤ k ∧ IsCyclicallyNonBacktracking p ∧ p.length = 2 ^ k ∧
        (2 ^ k < 2 * g ∨
         ¬ ∃ (x : V) (q₁ q₂ : G.Walk x x),
             IsNonBacktracking q₁ ∧ IsNonBacktracking q₂ ∧
             g ≤ q₁.length ∧ g ≤ q₂.length ∧ q₁.length + q₂.length = 2 ^ k)) :
    ∀ {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (∀ v : V, 3 ≤ G.degree v) → HasPower G := by
  intro V _ G _ hdeg
  obtain ⟨g, k, v, p, hg, hk, hcyc, hlen, hcase⟩ := H G hdeg
  rcases hcase with hw1 | hw2
  · exact hasPower_of_cyclicallyNonBacktracking_lt_two_girth hg hk hw1 p hcyc hlen
  · exact hasPower_of_second_window_no_split hg hk p hcyc hlen hw2

/-! ## Pillar 2: Exact Switching-Count Lift for 4-Regular Perfect-Matching Transition Systems -/

/-- The 2-factor spanning subgraph `G \ m` obtained by deleting a perfect matching `m`. -/
def twoFactorSubgraph {V : Type*} (G : SimpleGraph V) (m : V → V)
    (hm_inv : ∀ v, m (m v) = v) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ v ≠ m u
  symm u v h := ⟨h.1.symm, fun heq => h.2 (by rw [heq, hm_inv])⟩
  loopless v h := G.loopless v h.1

/-- In any power-free graph `G` with perfect matching `m`, the 2-factor `G \ m` contains
no `2^k`-cycle (`0`-switching exclusion). -/
theorem no_pow2_cycle_in_twoFactor {V : Type*} (G : SimpleGraph V) (m : V → V)
    (hm_inv : ∀ v, m (m v) = v) (hnp : ¬ HasPower G) :
    ¬ HasPower (twoFactorSubgraph G m hm_inv) :=
  fun hp => hnp (power_mono (fun _ _ h => h.1) hp)

/-- Adjacent vertex chain predicate on a list. -/
def AdjChain {V : Type*} (G : SimpleGraph V) : List V → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => G.Adj a b ∧ AdjChain G (b :: rest)

private def walkOfAdjChain {V : Type*} {G : SimpleGraph V} :
    ∀ (u : V) (rest : List V) (v : V),
      AdjChain G ((u :: rest) ++ [v]) → G.Walk u v
  | _, [], _, h => .cons h.1 .nil
  | _, b :: rest, v, h => .cons h.1 (walkOfAdjChain b rest v h.2)

private theorem walkOfAdjChain_length {V : Type*} {G : SimpleGraph V} :
    ∀ (u : V) (rest : List V) (v : V) (h : AdjChain G ((u :: rest) ++ [v])),
      (walkOfAdjChain u rest v h).length = rest.length + 1
  | _, [], _, _ => rfl
  | _, b :: rest, v, h => by
      simp only [walkOfAdjChain, Walk.length_cons, List.length_cons]
      rw [walkOfAdjChain_length b rest v h.2]

private theorem walkOfAdjChain_support {V : Type*} {G : SimpleGraph V} :
    ∀ (u : V) (rest : List V) (v : V) (h : AdjChain G ((u :: rest) ++ [v])),
      (walkOfAdjChain u rest v h).support = (u :: rest) ++ [v]
  | _, [], _, _ => rfl
  | _, b :: rest, v, h => by
      simp only [walkOfAdjChain, Walk.support_cons, List.cons_append]
      rw [walkOfAdjChain_support b rest v h.2]
      rfl

private theorem isNonBacktracking_of_nodup_support {V : Type*} {G : SimpleGraph V} :
    ∀ {u v : V} (w : G.Walk u v), w.support.Nodup → IsNonBacktracking w
  | _, _, .nil, _ => trivial
  | _, _, .cons _ .nil, _ => trivial
  | _, _, .cons (u := a) _ (.cons (v := c) h₂ rest), hnd => by
      simp only [Walk.support_cons, List.nodup_cons, List.mem_cons] at hnd
      refine ⟨fun hac => hnd.1 (Or.inr (hac ▸ Walk.start_mem_support rest)), ?_⟩
      exact isNonBacktracking_of_nodup_support (.cons h₂ rest) hnd.2

private theorem cycle_of_adjChain {V : Type*} {G : SimpleGraph V}
    (u : V) (rest : List V) (hnd : (u :: rest).Nodup) (hlen : 2 ≤ rest.length)
    (hchain : AdjChain G ((u :: rest) ++ [u])) :
    ∃ (c : G.Walk u u), c.IsCycle ∧ c.length = rest.length + 1 := by
  let w := walkOfAdjChain u rest u hchain
  have hwlen : w.length = rest.length + 1 := walkOfAdjChain_length u rest u hchain
  have hwsupp : w.support = u :: (rest ++ [u]) := walkOfAdjChain_support u rest u hchain
  have hnd_tail : w.support.tail.Nodup := by
    rw [hwsupp, List.tail_cons]
    simp only [List.nodup_cons] at hnd
    rw [List.nodup_append]
    exact ⟨hnd.2, List.nodup_singleton u, fun x hx y hy hxy =>
      hnd.1 (by simp only [List.mem_singleton] at hy; rwa [hy, ← hxy] at hx)⟩
  have hnb : IsNonBacktracking w := by
    cases rest with
    | nil => simp at hlen
    | cons b rest' =>
        cases rest' with
        | nil => simp at hlen
        | cons c rest'' =>
            have hw_eq : w = .cons hchain.1 (.cons hchain.2.1 (walkOfAdjChain c rest'' u hchain.2.2)) := rfl
            rw [hw_eq]
            have hrest_nd : (Walk.cons hchain.2.1 (walkOfAdjChain c rest'' u hchain.2.2)).support.Nodup := by
              have : w.support.tail = (Walk.cons hchain.2.1 (walkOfAdjChain c rest'' u hchain.2.2)).support := by
                rw [hw_eq]; rfl
              rwa [← this]
            have huc : u ≠ c := by
              simp only [List.nodup_cons, List.mem_cons] at hnd
              intro h
              exact hnd.1 (Or.inr (Or.inl h.symm))
            exact ⟨huc, isNonBacktracking_of_nodup_support _ hrest_nd⟩
  exact ⟨w, isCycle_of_nb_nodup_tail' w hnb (by omega) hnd_tail, hwlen⟩

private theorem adjChain_append {V : Type*} {G : SimpleGraph V} :
    ∀ (l₁ : List V) (x : V) (l₂ : List V),
      AdjChain G (l₁ ++ [x]) → AdjChain G (x :: l₂) → AdjChain G (l₁ ++ x :: l₂)
  | [], _, _, _, h₂ => h₂
  | [a], x, l₂, h₁, h₂ => ⟨h₁.1, h₂⟩
  | a :: b :: rest, x, l₂, h₁, h₂ =>
      ⟨h₁.1, adjChain_append (b :: rest) x l₂ h₁.2 h₂⟩

private theorem adj_of_same_matchSetoid_ne {V : Type*} {G : SimpleGraph V}
    {m : V → V} (hm_adj : ∀ v, G.Adj v (m v)) (hm_inv : ∀ v, m (m v) = v)
    {x y : V} (hq : Quotient.mk (matchSetoid m hm_inv) x = Quotient.mk (matchSetoid m hm_inv) y)
    (hne : x ≠ y) : G.Adj x y := by
  rcases Quotient.exact hq with rfl | rfl
  · exact False.elim (hne rfl)
  · exact hm_adj x

/-- **Exact Switching-Count Lift Theorem** for 4-regular perfect-matching contractions:
Every simple cycle of length `L ≥ 3` in `MContract G m` (given by `L` distinct quotient
vertices `q : Fin L → Q` and lifted non-matching edges `G.Adj (a i) (b i)` connecting
`q i` to `q (i + 1)`) lifts to a **simple cycle** in `G` of length **EXACTLY `L + S`**,
where `S` is the exact number of switching vertices `i` where `b (i - 1) ≠ a i`. -/
theorem mcontract_general_switching_lift {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (m : V → V)
    (hm_adj : ∀ v, G.Adj v (m v)) (hm_inv : ∀ v, m (m v) = v)
    (L : ℕ) (hL : 3 ≤ L)
    (q : Fin L → Quotient (matchSetoid m hm_inv)) (hq_inj : Function.Injective q)
    (a b : Fin L → V)
    (ha : ∀ i : Fin L, Quotient.mk (matchSetoid m hm_inv) (a i) = q i)
    (hb : ∀ i : Fin L, Quotient.mk (matchSetoid m hm_inv) (b i) =
      q ⟨(i.1 + 1) % L, Nat.mod_lt _ (by omega)⟩)
    (hab : ∀ i : Fin L, G.Adj (a i) (b i)) :
    let prev : Fin L → Fin L := fun i => ⟨(i.1 + L - 1) % L, Nat.mod_lt _ (by omega)⟩
    let S : ℕ := ((Finset.univ : Finset (Fin L)).filter (fun i => b (prev i) ≠ a i)).card
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = L + S := by
  classical
  let s := matchSetoid m hm_inv
  let prev : Fin L → Fin L := fun i => ⟨(i.1 + L - 1) % L, Nat.mod_lt _ (by omega)⟩
  let next : Fin L → Fin L := fun i => ⟨(i.1 + 1) % L, Nat.mod_lt _ (by omega)⟩
  have hprev_next : ∀ i : Fin L, prev (next i) = i := by
    intro i
    apply Fin.ext
    change ((i.1 + 1) % L + L - 1) % L = i.1
    by_cases h : i.1 + 1 < L
    · rw [Nat.mod_eq_of_lt h]
      have : i.1 + 1 + L - 1 = i.1 + L := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt i.2]
    · have hi : i.1 + 1 = L := by omega
      rw [hi, Nat.mod_self, zero_add, Nat.mod_eq_of_lt (by omega)]
      omega
  have hnext_prev : ∀ i : Fin L, next (prev i) = i := by
    intro i
    apply Fin.ext
    change ((i.1 + L - 1) % L + 1) % L = i.1
    by_cases h0 : i.1 = 0
    · rw [h0, zero_add, Nat.mod_eq_of_lt (by omega)]
      have : L - 1 + 1 = L := by omega
      rw [this, Nat.mod_self]
    · have : i.1 + L - 1 = (i.1 - 1) + L := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have : i.1 - 1 + 1 = i.1 := by omega
      rw [this, Nat.mod_eq_of_lt i.2]
  have hb_prev_q : ∀ i : Fin L, Quotient.mk s (b (prev i)) = q i := by
    intro i
    have h1 := hb (prev i)
    have h2 : (⟨((prev i).1 + 1) % L, Nat.mod_lt _ (by omega)⟩ : Fin L) = i := hnext_prev i
    rw [h2] at h1
    exact h1
  let block : Fin L → List V := fun i =>
    if b (prev i) = a i then [a i] else [b (prev i), a i]
  have hblock_head : ∀ i : Fin L, ∃ t : List V, block i = b (prev i) :: t := by
    intro i
    by_cases h : b (prev i) = a i
    · refine ⟨[], ?_⟩; simp [block, h]
    · refine ⟨[a i], ?_⟩; simp [block, h]
  have hblock_mem_q : ∀ (i : Fin L) (x : V), x ∈ block i → Quotient.mk s x = q i := by
    intro i x hx
    by_cases h : b (prev i) = a i
    · simp only [block, if_pos h, List.mem_singleton] at hx
      subst hx; exact ha i
    · simp only [block, if_neg h, List.mem_cons, List.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hb_prev_q i
      · exact ha i
  have hblock_nodup : ∀ i : Fin L, (block i).Nodup := by
    intro i
    by_cases h : b (prev i) = a i
    · simp [block, h]
    · simp [block, h]
  have hblock_chain : ∀ i : Fin L, AdjChain G (block i ++ [b i]) := by
    intro i
    by_cases h : b (prev i) = a i
    · simp only [block, if_pos h, List.singleton_append, AdjChain]
      exact ⟨hab i, trivial⟩
    · simp only [block, if_neg h, List.cons_append, List.singleton_append, AdjChain]
      refine ⟨adj_of_same_matchSetoid_ne hm_adj hm_inv ((hb_prev_q i).trans (ha i).symm) h, hab i, trivial⟩
  have hblock_len : ∀ i : Fin L, (block i).length = 1 + if b (prev i) ≠ a i then 1 else 0 := by
    intro i
    by_cases h : b (prev i) = a i
    · simp [block, h]
    · simp [block, h]
  let idx0 : Fin L := ⟨0, by omega⟩
  -- Build the concatenated vertex list across `i = 0, 1, ..., L - 1`
  let l : List V := (List.finRange L).flatMap block
  have hl_len : l.length = L + ((Finset.univ : Finset (Fin L)).filter (fun i => b (prev i) ≠ a i)).card := by
    have h1 : l.length = ((List.finRange L).map (fun i => (block i).length)).sum := by
      simp [l, List.length_flatMap]
    rw [h1]
    have h2 : (List.finRange L).map (fun i => (block i).length) =
        (List.finRange L).map (fun i => 1 + if b (prev i) ≠ a i then 1 else 0) :=
      List.map_congr_left (fun i _ => hblock_len i)
    rw [h2]
    have hsum_eq : ((List.finRange L).map (fun i => 1 + if b (prev i) ≠ a i then 1 else 0)).sum =
        ∑ i : Fin L, (1 + if b (prev i) ≠ a i then 1 else 0) := by
      rw [← Finset.sum_toList]
      congr 1
      have hperm : (Finset.univ : Finset (Fin L)).toList.Perm (List.finRange L) := by
        refine (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) (List.nodup_finRange L)).mpr ?_
        intro x
        simp
      exact hperm.symm.map _ |>.sum_eq
    rw [hsum_eq, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one, Finset.sum_boole]
    simp
  have hl_nodup : l.Nodup := by
    rw [List.nodup_flatMap]
    refine ⟨fun i _ => hblock_nodup i, ?_⟩
    exact (List.nodup_finRange L).imp_of_mem (fun {i j} _ _ hij x hxi hxj =>
      hij (hq_inj ((hblock_mem_q i x hxi).symm.trans (hblock_mem_q j x hxj))))
  -- Prove `AdjChain G (l ++ [b (prev idx0)])` by induction on prefixes `0 .. k`
  have hprefix_chain : ∀ k (hk : k ≤ L) (hkpos : 1 ≤ k),
      AdjChain G (((List.finRange L).take k).flatMap block ++ [b ⟨k - 1, by omega⟩]) := by
    intro k
    induction k with
    | zero => intro _ hkpos; omega
    | succ k ih =>
        intro hk _
        by_cases hk0 : k = 0
        · subst hk0
          have htake : (List.finRange L).take 1 = [idx0] := by
            apply List.ext_getElem
            · simp [List.length_take]; omega
            · intro n hn1 hn2
              have hn0 : n = 0 := by simp at hn2; omega
              subst hn0
              simp [idx0]
          rw [htake, List.flatMap_cons, List.flatMap_nil, List.append_nil]
          exact hblock_chain idx0
        · have hkpos : 1 ≤ k := by omega
          let ik : Fin L := ⟨k, by omega⟩
          let ik_prev : Fin L := ⟨k - 1, by omega⟩
          have htake : (List.finRange L).take (k + 1) = (List.finRange L).take k ++ [ik] := by
            apply List.ext_getElem
            · simp [List.length_take]; omega
            · intro n hn1 hn2
              simp only [List.getElem_take, List.getElem_finRange]
              by_cases hnk : n < k
              · rw [List.getElem_append_left (by simp [List.length_take]; omega)]
                simp [List.getElem_take]
              · have hneq : n = k := by simp [List.length_take] at hn1; omega
                subst hneq
                rw [List.getElem_append_right (by simp [List.length_take]; omega)]
                simp [List.length_take, Nat.min_eq_left (by omega : k ≤ L), ik]
          rw [htake, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
            List.append_assoc]
          have hprev_eq : prev ik = ik_prev := by
            apply Fin.ext
            change (k + L - 1) % L = k - 1
            have : k + L - 1 = (k - 1) + L := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          obtain ⟨t, ht⟩ := hblock_head ik
          rw [hprev_eq] at ht
          have h1 := ih (by omega) hkpos
          have h2 := hblock_chain ik
          rw [ht] at h2 ⊢
          exact adjChain_append _ (b ik_prev) (t ++ [b ik]) h1 h2
  have hfull_chain : AdjChain G (l ++ [b (prev idx0)]) := by
    have h1 := hprefix_chain L le_rfl (by omega)
    have htakeL : (List.finRange L).take L = List.finRange L := by
      rw [List.take_of_length_le (by simp)]
    have hlast_eq : (⟨L - 1, by omega⟩ : Fin L) = prev idx0 := by
      apply Fin.ext
      change L - 1 = (0 + L - 1) % L
      rw [zero_add, Nat.mod_eq_of_lt (by omega)]
    rw [htakeL, hlast_eq] at h1
    exact h1
  -- Extract head `b (prev idx0)` of `l`
  have hl_cons : ∃ rest : List V, l = b (prev idx0) :: rest := by
    have hfr : List.finRange L = idx0 :: (List.finRange L).tail := by
      cases h : List.finRange L with
      | nil =>
          have := congrArg List.length h
          simp at this; omega
      | cons hd tl =>
          have hhd : hd = idx0 := by
            have := congrArg (fun xs => xs[0]?) h
            simp [idx0, Nat.zero_lt_of_lt (by omega : 0 < L)] at this
            exact this.symm
          rw [hhd]; rfl
    obtain ⟨t, ht⟩ := hblock_head idx0
    refine ⟨t ++ (List.finRange L).tail.flatMap block, ?_⟩
    simp only [l]
    rw [hfr, List.flatMap_cons, ht, List.cons_append]
  obtain ⟨rest, hrest⟩ := hl_cons
  rw [hrest] at hl_len hl_nodup hfull_chain
  have hrest_ge : 2 ≤ rest.length := by
    simp only [List.length_cons] at hl_len
    omega
  obtain ⟨c, hcyc, hclen⟩ := cycle_of_adjChain (b (prev idx0)) rest hl_nodup hrest_ge hfull_chain
  refine ⟨b (prev idx0), c, hcyc, ?_⟩
  simp only [List.length_cons] at hl_len
  omega

/-- In any power-free graph `G` with perfect matching `m`, EVERY simple cycle of length
`L ≥ 3` in `MContract G m` with `S` switching vertices satisfies `L + S ≠ 2^r` for all `r ≥ 2`. -/
theorem mcontract_cycle_length_plus_switches_not_pow2 {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (hnp : ¬ HasPower G) (m : V → V)
    (hm_adj : ∀ v, G.Adj v (m v)) (hm_inv : ∀ v, m (m v) = v)
    (L : ℕ) (hL : 3 ≤ L)
    (q : Fin L → Quotient (matchSetoid m hm_inv)) (hq_inj : Function.Injective q)
    (a b : Fin L → V)
    (ha : ∀ i : Fin L, Quotient.mk (matchSetoid m hm_inv) (a i) = q i)
    (hb : ∀ i : Fin L, Quotient.mk (matchSetoid m hm_inv) (b i) =
      q ⟨(i.1 + 1) % L, Nat.mod_lt _ (by omega)⟩)
    (hab : ∀ i : Fin L, G.Adj (a i) (b i)) :
    let prev : Fin L → Fin L := fun i => ⟨(i.1 + L - 1) % L, Nat.mod_lt _ (by omega)⟩
    let S : ℕ := ((Finset.univ : Finset (Fin L)).filter (fun i => b (prev i) ≠ a i)).card
    ∀ r : ℕ, 2 ≤ r → L + S ≠ 2 ^ r := by
  intro prev S r hr heq
  obtain ⟨v, c, hcyc, hlen⟩ :=
    mcontract_general_switching_lift G m hm_adj hm_inv L hL q hq_inj a b ha hb hab
  exact hnp ⟨r, v, c, hr, hcyc, hlen.trans heq⟩

/-- **Strictly-Mixed Power-Cycle Obstruction**:
In any power-free graph `G` with perfect matching `m`, every `2^k`-cycle (`k ≥ 2`) in
`MContract G m` has switching count `1 ≤ S ≤ 2^k - 1` (neither 0-switching nor all-switching). -/
theorem mcontract_pow2_cycle_strictly_mixed {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (hnp : ¬ HasPower G) (m : V → V)
    (hm_adj : ∀ v, G.Adj v (m v)) (hm_inv : ∀ v, m (m v) = v)
    (k : ℕ) (hk : 2 ≤ k)
    (q : Fin (2 ^ k) → Quotient (matchSetoid m hm_inv)) (hq_inj : Function.Injective q)
    (a b : Fin (2 ^ k) → V)
    (ha : ∀ i : Fin (2 ^ k), Quotient.mk (matchSetoid m hm_inv) (a i) = q i)
    (hb : ∀ i : Fin (2 ^ k), Quotient.mk (matchSetoid m hm_inv) (b i) =
      q ⟨(i.1 + 1) % (2 ^ k), Nat.mod_lt _ (Nat.pos_of_ne_zero (by positivity))⟩)
    (hab : ∀ i : Fin (2 ^ k), G.Adj (a i) (b i)) :
    let prev : Fin (2 ^ k) → Fin (2 ^ k) :=
      fun i => ⟨(i.1 + 2 ^ k - 1) % (2 ^ k), Nat.mod_lt _ (Nat.pos_of_ne_zero (by positivity))⟩
    let S : ℕ := ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun i => b (prev i) ≠ a i)).card
    1 ≤ S ∧ S ≤ 2 ^ k - 1 := by
  have h4 : 4 ≤ 2 ^ k := by
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
    omega
  have hnot := mcontract_cycle_length_plus_switches_not_pow2 G hnp m hm_adj hm_inv
    (2 ^ k) (by omega) q hq_inj a b ha hb hab
  dsimp only at hnot ⊢
  have hle : ((Finset.univ : Finset (Fin (2 ^ k))).filter
      (fun i => b ⟨(i.1 + 2 ^ k - 1) % 2 ^ k, Nat.mod_lt _ (Nat.pos_of_ne_zero (by positivity))⟩ ≠ a i)).card ≤ 2 ^ k := by
    calc _ ≤ (Finset.univ : Finset (Fin (2 ^ k))).card := Finset.card_filter_le _ _
      _ = 2 ^ k := by simp
  have hne0 := hnot k hk
  have hne_all := hnot (k + 1) (by omega)
  have h2k : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
  omega

#print axioms nonBacktracking_lt_girth_add_two_isCyclicallyNonBacktracking
#print axioms nonBacktracking_lt_girth_add_two_isCycle
#print axioms no_nonBacktracking_closed_pow2_lt_girth_add_two
#print axioms tailless_pow2_lt_three_girth_not_square
#print axioms nonSimple_tailless_exists_split_ge_girth
#print axioms nonSimple_tailless_mersenne_girth_split_lengths
#print axioms hasPower_of_second_window_no_split
#print axioms erdos64_of_two_window_nonBacktracking
#print axioms no_pow2_cycle_in_twoFactor
#print axioms mcontract_general_switching_lift
#print axioms mcontract_cycle_length_plus_switches_not_pow2
#print axioms mcontract_pow2_cycle_strictly_mixed

end E64Wave5Agent4
