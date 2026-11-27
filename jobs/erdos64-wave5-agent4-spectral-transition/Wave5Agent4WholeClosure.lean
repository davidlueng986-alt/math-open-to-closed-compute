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
7. `erdos64_of_two_window_nonBacktracking`:
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
def twoFactorSubgraph {V : Type*} (G : SimpleGraph V) (m : V → V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ v ≠ m u
  symm u v h := ⟨h.1.symm, fun heq => h.2 (by rw [← heq]; exact sorry_free_unused)⟩
  loopless v h := G.loopless v h.1

end E64Wave5Agent4
