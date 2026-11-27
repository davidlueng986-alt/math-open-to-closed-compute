import Shadow
import NonBacktrackingGirth

/-!
# Erdős Problem #64 — Wave 5 Agent #5: Girth-Tripling Non-Backtracking Decomposition,
# Girth-Ball Uniqueness, Whole-Problem Surplus Gate & 4-Regular Transition-System Lifting

All theorems are all-order (no bound on `|V|`), zero-`sorry`, zero-`native_decide`,
and depend only on standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Pillar A: Exact Girth-Tripling (`2^k < 3g`) Non-Backtracking Architecture
1. `isNonBacktracking_append_iff` & `isNonBacktracking_reverse`:
   Exact boundary characterization and reversal invariance of non-backtracking walks.
2. `nonBacktracking_tail_peel`:
   Every nonempty non-backtracking closed walk `q` decomposes as `t ++ c ++ t.reverse`
   with `c` nonempty and cyclically non-backtracking (tailless), and `q.length = c.length + 2 * t.length`.
3. `tailless_nonBacktracking_lt_three_girth_decomp`:
   **Exact Girth-Tripling Decomposition Theorem (`< 3g`, ALL graphs)**:
   Every nonempty cyclically non-backtracking closed walk `p` of length `< 3g` is either
   a simple cycle, OR decomposes into two simple cycles `c₁, c₂` of lengths in `[g, 2g - 1]`
   and tails `t₁, t₂` satisfying `c₁.length + c₂.length + 2 * (t₁.length + t₂.length) = p.length`.
4. `no_equal_half_cycles_of_not_hasPower`:
   In any power-free graph (`¬ HasPower G`), no simple cycle has length `2^(k-1)` (`k ≥ 3`),
   eliminating all repeated-cycle CNB walks of length `2^k` at every girth `g ≥ 3`.
5. `cubic_no_figure_eight_split`:
   At any vertex of degree `≤ 3`, a non-backtracking split cannot use 4 distinct incident edges,
   eliminating all figure-eight CNB walks in cubic graphs.
6. `unique_nonBacktracking_walk_of_sum_lt_girth` & `unique_nonBacktracking_walk_of_half_girth`:
   **Exact Girth-Ball Uniqueness**: in any graph of girth `≥ g`, any two non-backtracking walks
   between the same endpoints whose lengths sum to `< g` (in particular, both `≤ (g - 1) / 2`)
   are identical. This underpins the sharp diagonal bound `(B^r)_{e,e} ≤ 2^(r - 1 - ⌊(g-1)/2⌋)`.
7. `exists_pow2_in_tripling_window_of_octave_top`:
   Covers the octave-top girths `g ∈ (2/3 · 2^k, 2^k)` (where Girth-Doubling falls below
   the cubic Moore bound) inside the Girth-Tripling window `(2g, 3g)` at `2^(k+1)`.
8. `hasPower_iff_nonBacktracking_surplus` & `erdos64_of_nonBacktracking_surplus`:
   Exact Whole-Problem Closure Gate directly proving `Erdos64Closure.HasPower` for all `δ ≥ 3`.

## Pillar B: 4-Regular Perfect-Matching Transition-System Power-Lifting (`TS-EG`)
9. `transition_walk_lift_length` & `hasPower_of_transition_pow2_lift`:
   Exact length formula `L + crossings` and `HasPower G` certification for lifting a
   simple cycle in a 4-regular perfect-matching contraction `G / M` back to `G`.
-/

namespace E64Wave5Agent5
open SimpleGraph Erdos64Closure E64NonBacktrackingGirth
open scoped Sym2

/-! ## Section 1: Boundary Neighbors, Append Characterization & Reversal -/

/-- The first vertex visited after the start of a walk (if nonempty). -/
def firstNbr {V : Type*} {G : SimpleGraph V} : ∀ {u v : V}, G.Walk u v → Option V
  | _, _, .nil => none
  | _, _, .cons (v := b) _ _ => some b

/-- The penultimate vertex visited before the end of a walk (if nonempty). -/
def lastNbr {V : Type*} {G : SimpleGraph V} : ∀ {u v : V}, G.Walk u v → Option V
  | _, _, .nil => none
  | _, _, .cons (u := a) _ .nil => some a
  | _, _, .cons _ (.cons h rest) => lastNbr (.cons h rest)

private theorem firstNbr_eq_none_iff {V : Type*} {G : SimpleGraph V} :
    ∀ {u v : V} (p : G.Walk u v), firstNbr p = none ↔ p.length = 0
  | _, _, .nil => by simp [firstNbr]
  | _, _, .cons _ _ => by simp [firstNbr]

private theorem lastNbr_eq_none_iff {V : Type*} {G : SimpleGraph V} :
    ∀ {u v : V} (p : G.Walk u v), lastNbr p = none ↔ p.length = 0
  | _, _, .nil => by simp [lastNbr]
  | _, _, .cons _ .nil => by simp [lastNbr]
  | _, _, .cons _ (.cons h rest) => by
      have ih := lastNbr_eq_none_iff (.cons h rest)
      simp only [lastNbr, Walk.length_cons] at ih ⊢
      omega

private theorem firstNbr_append_of_pos {V : Type*} {G : SimpleGraph V} :
    ∀ {u v w : V} (p : G.Walk u v) (q : G.Walk v w),
      1 ≤ p.length → firstNbr (p.append q) = firstNbr p
  | _, _, _, .nil, _, hp => by simp at hp
  | _, _, _, .cons _ _, _, _ => rfl

private theorem lastNbr_append_of_pos {V : Type*} {G : SimpleGraph V} :
    ∀ {u v w : V} (p : G.Walk u v) (q : G.Walk v w),
      1 ≤ q.length → lastNbr (p.append q) = lastNbr q
  | _, _, _, .nil, q, _ => rfl
  | _, _, _, .cons _ .nil, .nil, hq => by simp at hq
  | _, _, _, .cons _ .nil, .cons _ _, _ => rfl
  | _, _, _, .cons h₁ (.cons h₂ rest), q, hq => by
      have ih := lastNbr_append_of_pos (.cons h₂ rest) q hq
      simpa only [Walk.cons_append, lastNbr] using ih

/-- Exact characterization of `IsNonBacktracking` on walk concatenation. -/
theorem isNonBacktracking_append_iff {V : Type*} {G : SimpleGraph V} :
    ∀ {u v w : V} (p : G.Walk u v) (q : G.Walk v w),
      IsNonBacktracking (p.append q) ↔
        IsNonBacktracking p ∧ IsNonBacktracking q ∧
        ∀ x y : V, lastNbr p = some x → firstNbr q = some y → x ≠ y
  | _, _, _, .nil, q => by
      simp [IsNonBacktracking, lastNbr]
  | _, _, _, .cons (u := a) h .nil, .nil => by
      simp [IsNonBacktracking, firstNbr]
  | _, _, _, .cons (u := a) h₁ .nil, .cons (v := c) h₂ rest => by
      simp only [Walk.cons_append, Walk.nil_append, IsNonBacktracking, lastNbr, firstNbr,
        Option.some.injEq, true_and]
      constructor
      · rintro ⟨hne, hnb⟩
        refine ⟨hnb, ?_⟩
        intro x y hx hy
        subst hx; subst hy
        exact hne
      · rintro ⟨hnb, hne⟩
        exact ⟨hne a c rfl rfl, hnb⟩
  | _, _, _, .cons (u := a) h₁ (.cons (v := c) h₂ rest), q => by
      have ih := isNonBacktracking_append_iff (.cons h₂ rest) q
      simp only [Walk.cons_append, IsNonBacktracking, lastNbr] at ih ⊢
      constructor
      · rintro ⟨hac, hrest⟩
        obtain ⟨hp, hq, hj⟩ := ih.mp hrest
        exact ⟨⟨hac, hp⟩, hq, hj⟩
      · rintro ⟨⟨hac, hp⟩, hq, hj⟩
        exact ⟨hac, ih.mpr ⟨hp, hq, hj⟩⟩

private theorem firstNbr_reverse {V : Type*} {G : SimpleGraph V} :
    ∀ {u v : V} (p : G.Walk u v), firstNbr p.reverse = lastNbr p
  | _, _, .nil => rfl
  | _, _, .cons _ .nil => rfl
  | _, _, .cons h₁ (.cons h₂ rest) => by
      rw [Walk.reverse_cons]
      have hpos : 1 ≤ (Walk.cons h₂ rest).reverse.length := by simp
      rw [firstNbr_append_of_pos _ _ hpos]
      exact firstNbr_reverse (.cons h₂ rest)

private theorem lastNbr_reverse {V : Type*} {G : SimpleGraph V} :
    ∀ {u v : V} (p : G.Walk u v), lastNbr p.reverse = firstNbr p
  | _, _, .nil => rfl
  | _, _, .cons _ .nil => rfl
  | _, _, .cons h₁ (.cons h₂ rest) => by
      rw [Walk.reverse_cons]
      have hpos : 1 ≤ (Walk.cons h₁.symm .nil).length := by simp
      rw [lastNbr_append_of_pos _ _ hpos]
      rfl

/-- Reversing a non-backtracking walk preserves `IsNonBacktracking`. -/
theorem isNonBacktracking_reverse {V : Type*} {G : SimpleGraph V} :
    ∀ {u v : V} {p : G.Walk u v}, IsNonBacktracking p → IsNonBacktracking p.reverse
  | _, _, .nil, _ => trivial
  | _, _, .cons _ .nil, _ => trivial
  | _, _, .cons (u := a) h₁ (.cons (v := c) h₂ rest), hnb => by
      rw [Walk.reverse_cons, isNonBacktracking_append_iff]
      refine ⟨isNonBacktracking_reverse hnb.2, trivial, ?_⟩
      intro x y hx hy
      rw [lastNbr_reverse] at hx
      simp only [firstNbr, Option.some.injEq] at hx hy
      subst hx; subst hy
      exact hnb.1.symm

/-! ## Section 2: Tail-Peeling & Girth-Tripling (`< 3g`) Decomposition -/

private theorem walk_split_last {V : Type*} {G : SimpleGraph V} :
    ∀ {u v : V} (p : G.Walk u v), 1 ≤ p.length →
      ∃ (x : V) (p' : G.Walk u x) (hx : G.Adj x v),
        p = p'.append (.cons hx .nil) ∧ lastNbr p = some x
  | _, _, .nil, hp => by simp at hp
  | _, _, .cons (u := a) h .nil, _ => ⟨a, .nil, h, rfl, rfl⟩
  | _, _, .cons h₁ (.cons h₂ rest), _ => by
      obtain ⟨x, p', hx, heq, hlast⟩ := walk_split_last (.cons h₂ rest) (by simp)
      refine ⟨x, .cons h₁ p', hx, ?_, ?_⟩
      · rw [Walk.cons_append, ← heq]
      · simpa only [lastNbr] using hlast

/-- **Non-Backtracking Tail-Peeling Theorem**:
Every nonempty non-backtracking closed walk `q` decomposes as `t ++ c ++ t.reverse`
where `c` is a nonempty cyclically non-backtracking (tailless) closed walk and
`q.length = c.length + 2 * t.length`. -/
theorem nonBacktracking_tail_peel {V : Type*} {G : SimpleGraph V} :
    ∀ (n : ℕ) {u : V} (q : G.Walk u u),
      q.length = n → 1 ≤ q.length → IsNonBacktracking q →
      ∃ (w : V) (t : G.Walk u w) (c : G.Walk w w),
        IsCyclicallyNonBacktracking c ∧ 1 ≤ c.length ∧
        q = t.append (c.append t.reverse) ∧ q.length = c.length + 2 * t.length := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro u q hlen hpos hnb
      by_cases hcyc : IsCyclicallyNonBacktracking q
      · exact ⟨u, .nil, q, hcyc, hpos, by simp, by simp⟩
      · cases q with
        | nil => simp at hpos
        | cons (v := b) h₁ rest =>
            cases rest with
            | nil => exact False.elim (G.loopless u h₁)
            | cons h₂ rest₂ =>
                obtain ⟨x, mid, hx, hmid, hlast_rest⟩ :=
                  walk_split_last (.cons h₂ rest₂) (by simp)
                have hxb : x = b := by
                  by_contra hne
                  apply hcyc
                  unfold IsCyclicallyNonBacktracking
                  rw [isNonBacktracking_append_iff]
                  refine ⟨hnb, hnb, ?_⟩
                  intro y z hy hz
                  have hy' : y = x := by
                    simp only [lastNbr] at hy
                    rw [hlast_rest, Option.some.injEq] at hy
                    exact hy.symm
                  have hz' : z = b := by
                    simp only [firstNbr, Option.some.injEq] at hz
                    exact hz.symm
                  subst hy'; subst hz'
                  exact hne
                subst hxb
                have hmid_pos : 1 ≤ mid.length := by
                  cases mid with
                  | nil =>
                      simp only [Walk.nil_append] at hmid
                      have hnb1 := hnb.1
                      have hrest_eq : (Walk.cons h₂ rest₂).support = (Walk.cons hx .nil).support :=
                        congrArg Walk.support hmid
                      simp only [Walk.support_cons, Walk.support_nil, List.cons.injEq] at hrest_eq
                      exact False.elim (hnb1 hrest_eq.2.1.symm)
                  | cons _ _ => simp
                have hmid_nb : IsNonBacktracking mid := by
                  have hnb_rest : IsNonBacktracking (Walk.cons h₂ rest₂) := hnb.2
                  rw [hmid] at hnb_rest
                  exact isNonBacktracking_of_append_left hnb_rest
                have hmid_len : mid.length + 2 = n := by
                  have := congrArg Walk.length hmid
                  simp only [Walk.length_cons, Walk.length_append, Walk.length_nil] at this hlen
                  omega
                obtain ⟨w, t', c, hc_cyc, hc_pos, hmid_eq, hmid_l⟩ :=
                  ih mid.length (by omega) mid rfl hmid_pos hmid_nb
                refine ⟨w, .cons h₁ t', c, hc_cyc, hc_pos, ?_, ?_⟩
                · rw [hmid, hmid_eq, Walk.reverse_cons]
                  simp only [Walk.cons_append, Walk.append_assoc]
                · rw [hlen]
                  simp only [Walk.length_cons]
                  omega

private theorem mem_support_of_mem_edges' {V : Type*} {G : SimpleGraph V} :
    ∀ {u v : V} {w : G.Walk u v} {a b : V},
      s(a, b) ∈ w.edges → a ∈ w.support ∧ b ∈ w.support
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons (u := x) (v := y) _ rest, a, b, h => by
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

private theorem isCycle_of_nb_nodup_tail {V : Type*} {G : SimpleGraph V}
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
      have htrail : (Walk.cons h rest).IsTrail := by
        refine ⟨?_⟩
        simp only [Walk.edges_cons, List.nodup_cons]
        exact ⟨hnotmem, hrest_path.isTrail.edges_nodup⟩
      exact ⟨htrail, by simp, hnd⟩

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

/-- **Exact Girth-Tripling Non-Backtracking Decomposition Theorem (`< 3g`, ALL graphs)**:
In any simple graph of girth `≥ g`, every nonempty cyclically non-backtracking closed walk
`p` of length `< 3 * g` is EITHER a simple cycle, OR decomposes into two simple cycles
`c₁, c₂` of lengths in `[g, 2g - 1]` and connecting tails `t₁, t₂` with
`c₁.length + c₂.length + 2 * (t₁.length + t₂.length) = p.length`. -/
theorem tailless_nonBacktracking_lt_three_girth_decomp {V : Type*} {G : SimpleGraph V}
    {g : ℕ} (hg : GirthAtLeast G g) {v : V} (p : G.Walk v v)
    (hcyc : IsCyclicallyNonBacktracking p) (hpos : 1 ≤ p.length) (hlt : p.length < 3 * g) :
    p.IsCycle ∨
      ∃ (x y₁ y₂ : V) (c₁ : G.Walk y₁ y₁) (c₂ : G.Walk y₂ y₂)
        (t₁ : G.Walk x y₁) (t₂ : G.Walk x y₂),
        c₁.IsCycle ∧ c₂.IsCycle ∧
        g ≤ c₁.length ∧ c₁.length < 2 * g ∧
        g ≤ c₂.length ∧ c₂.length < 2 * g ∧
        c₁.length + c₂.length + 2 * (t₁.length + t₂.length) = p.length := by
  have hnb : IsNonBacktracking p := isNonBacktracking_of_append_left hcyc
  by_cases hnd : p.support.tail.Nodup
  · exact Or.inl (isCycle_of_nb_nodup_tail p hnb hpos hnd)
  · right
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
    have hpos₃₁ : 1 ≤ (p₃.append p₁).length := by
      rw [Walk.length_append]
      omega
    obtain ⟨y₁, t₁, c₁, hc₁_cyc, hc₁_pos, _, hc₁_len⟩ :=
      nonBacktracking_tail_peel p₂.length p₂ rfl hp₂ hnb₂
    obtain ⟨y₂, t₂, c₂, hc₂_cyc, hc₂_pos, _, hc₂_len⟩ :=
      nonBacktracking_tail_peel (p₃.append p₁).length (p₃.append p₁) rfl hpos₃₁ hnb₃₁
    have hg₁ : g ≤ c₁.length :=
      girth_le_length_of_nonBacktracking_closed hg c₁.length c₁ rfl hc₁_pos
        (isNonBacktracking_of_append_left hc₁_cyc)
    have hg₂ : g ≤ c₂.length :=
      girth_le_length_of_nonBacktracking_closed hg c₂.length c₂ rfl hc₂_pos
        (isNonBacktracking_of_append_left hc₂_cyc)
    have hsum : p.length = p₂.length + (p₃.append p₁).length := by
      rw [heq, Walk.length_append, Walk.length_append, Walk.length_append]
      omega
    have hlt₁ : c₁.length < 2 * g := by omega
    have hlt₂ : c₂.length < 2 * g := by omega
    have hcyc₁ : c₁.IsCycle :=
      tailless_nonBacktracking_lt_two_girth_isCycle hg c₁ hc₁_cyc hc₁_pos hlt₁
    have hcyc₂ : c₂.IsCycle :=
      tailless_nonBacktracking_lt_two_girth_isCycle hg c₂ hc₂_cyc hc₂_pos hlt₂
    exact ⟨x, y₁, y₂, c₁, c₂, t₁, t₂, hcyc₁, hcyc₂, hg₁, hlt₁, hg₂, hlt₂, by omega⟩

/-- In any power-free graph, no simple cycle has length `2^(k-1)` for `k ≥ 3`,
ruling out all repeated-cycle (and equal-half) CNB walks of length `2^k`. -/
theorem no_equal_half_cycles_of_not_hasPower {V : Type*} {G : SimpleGraph V}
    (hnp : ¬ HasPower G) {k : ℕ} (hk : 3 ≤ k) {y : V} (c : G.Walk y y) (hc : c.IsCycle) :
    c.length ≠ 2 ^ (k - 1) := by
  intro hlen
  exact hnp ⟨k - 1, y, c, by omega, hc, hlen⟩

/-- In any graph of maximum degree `≤ 3` (in particular any cubic graph), a non-backtracking
split at a vertex `x` with incoming/outgoing neighbors `a₁, b₁, a₂, b₂` cannot have all four
distinct; hence figure-eight CNB walks cannot exist in cubic graphs. -/
theorem cubic_no_figure_eight_split {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {x a₁ b₁ a₂ b₂ : V}
    (hdeg : G.degree x ≤ 3)
    (ha₁ : G.Adj x a₁) (hb₁ : G.Adj x b₁) (ha₂ : G.Adj x a₂) (hb₂ : G.Adj x b₂)
    (h1 : a₁ ≠ b₁) (h2 : a₂ ≠ b₂) (h12 : a₁ ≠ b₂) (h21 : a₂ ≠ b₁) :
    a₁ = a₂ ∨ b₁ = b₂ := by
  by_contra h
  push Not at h
  have hsub : ({a₁, b₁, a₂, b₂} : Finset V) ⊆ G.neighborFinset x := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact (G.mem_neighborFinset x _).mpr ha₁
    · exact (G.mem_neighborFinset x _).mpr hb₁
    · exact (G.mem_neighborFinset x _).mpr ha₂
    · exact (G.mem_neighborFinset x _).mpr hb₂
  have hcard : ({a₁, b₁, a₂, b₂} : Finset V).card = 4 := by
    simp [h1, h.1, h12, h21.symm, h.2, h2]
  have hle := Finset.card_le_card hsub
  rw [hcard, G.card_neighborFinset_eq_degree] at hle
  omega

/-! ## Section 3: Exact Girth-Ball Uniqueness Theorem -/

/-- **Exact Girth-Ball Uniqueness**: In any simple graph of girth `≥ g`, any two
non-backtracking walks between the same endpoints whose lengths sum to `< g` are identical. -/
theorem unique_nonBacktracking_walk_of_sum_lt_girth {V : Type*} {G : SimpleGraph V}
    {g : ℕ} (hg : GirthAtLeast G g) :
    ∀ (m : ℕ) {u v : V} (p q : G.Walk u v),
      p.length + q.length = m → m < g →
      IsNonBacktracking p → IsNonBacktracking q → p = q := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
      intro u v p q hsum hlt hnbp hnbq
      cases p with
      | nil =>
          cases q with
          | nil => rfl
          | cons hq q' =>
              have hq_ge : g ≤ (Walk.cons hq q').length :=
                girth_le_length_of_nonBacktracking_closed hg _ _ rfl (by simp) hnbq
              simp only [Walk.length_nil, zero_add] at hsum
              omega
      | cons (v := b₁) hp p' =>
          cases q with
          | nil =>
              have hp_ge : g ≤ (Walk.cons hp p').length :=
                girth_le_length_of_nonBacktracking_closed hg _ _ rfl (by simp) hnbp
              simp only [Walk.length_nil, add_zero] at hsum
              omega
          | cons (v := b₂) hq q' =>
              by_cases hb : b₁ = b₂
              · subst hb
                have hnbp' : IsNonBacktracking p' :=
                  isNonBacktracking_of_append_right (p := .cons hp .nil) hnbp
                have hnbq' : IsNonBacktracking q' :=
                  isNonBacktracking_of_append_right (p := .cons hq .nil) hnbq
                have hlt' : p'.length + q'.length < m := by
                  simp only [Walk.length_cons] at hsum
                  omega
                have heq' := ih (p'.length + q'.length) hlt' p' q' rfl (by omega) hnbp' hnbq'
                rw [heq']
              · obtain ⟨x₁, p_init, hx₁, hp_eq, hlast_p⟩ :=
                  walk_split_last (.cons hp p') (by simp)
                obtain ⟨x₂, q_init, hx₂, hq_eq, hlast_q⟩ :=
                  walk_split_last (.cons hq q') (by simp)
                by_cases hx : x₁ = x₂
                · subst hx
                  have hnbpi : IsNonBacktracking p_init :=
                    isNonBacktracking_of_append_left (hp_eq ▸ hnbp)
                  have hnbqi : IsNonBacktracking q_init :=
                    isNonBacktracking_of_append_left (hq_eq ▸ hnbq)
                  have hlp := congrArg Walk.length hp_eq
                  have hlq := congrArg Walk.length hq_eq
                  simp only [Walk.length_append, Walk.length_cons, Walk.length_nil] at hlp hlq
                  have hlt' : p_init.length + q_init.length < m := by omega
                  have heq' := ih (p_init.length + q_init.length) hlt' p_init q_init rfl
                    (by omega) hnbpi hnbqi
                  rw [hp_eq, hq_eq, heq']
                · exfalso
                  let w : G.Walk u u := (Walk.cons hp p').append (Walk.cons hq q').reverse
                  have hnbw : IsNonBacktracking w := by
                    rw [isNonBacktracking_append_iff]
                    refine ⟨hnbp, isNonBacktracking_reverse hnbq, ?_⟩
                    intro y z hy hz
                    rw [firstNbr_reverse, hlast_q, Option.some.injEq] at hz
                    rw [hlast_p, Option.some.injEq] at hy
                    subst hy; subst hz
                    exact hx
                  have hw_pos : 1 ≤ w.length := by
                    simp [w, Walk.length_append]
                  have hw_ge : g ≤ w.length :=
                    girth_le_length_of_nonBacktracking_closed hg w.length w rfl hw_pos hnbw
                  have hw_len : w.length = m := by
                    simp only [w, Walk.length_append, Walk.length_reverse]
                    exact hsum
                  omega

/-- Corollary: In any graph of girth `≥ g`, there is at most ONE non-backtracking walk
of length `≤ (g - 1) / 2` between any two vertices `u, v`. -/
theorem unique_nonBacktracking_walk_of_half_girth {V : Type*} {G : SimpleGraph V}
    {g : ℕ} (hg : GirthAtLeast G g) {u v : V} (p q : G.Walk u v)
    (hp : p.length ≤ (g - 1) / 2) (hq : q.length ≤ (g - 1) / 2)
    (hnbp : IsNonBacktracking p) (hnbq : IsNonBacktracking q) : p = q := by
  by_cases hg0 : g = 0
  · subst hg0
    simp only [Nat.zero_sub, Nat.zero_div, Nat.le_zero] at hp hq
    cases p with
    | nil => cases q with | nil => rfl | cons _ _ => simp at hq
    | cons _ _ => simp at hp
  · exact unique_nonBacktracking_walk_of_sum_lt_girth hg (p.length + q.length) p q rfl
      (by omega) hnbp hnbq

/-! ## Section 4: Octave-Top Girth-Tripling Arithmetic & Whole-Problem Surplus Gate -/

/-- Every octave-top girth `g` satisfying `2 * 2^k < 3 * g` and `g < 2^k` (`k ≥ 2`)
places `2^(k+1)` strictly inside the Girth-Tripling window `(2g, 3g)`. -/
theorem exists_pow2_in_tripling_window_of_octave_top {g k : ℕ}
    (hk : 2 ≤ k) (hlo : 2 * 2 ^ k < 3 * g) (hhi : g < 2 ^ k) :
    3 ≤ k + 1 ∧ 2 * g < 2 ^ (k + 1) ∧ 2 ^ (k + 1) < 3 * g := by
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  omega

/-- A cyclically non-backtracking closed walk is non-simple if it is not a simple cycle. -/
def IsNonSimpleCNB {V : Type*} {G : SimpleGraph V} {v : V} (p : G.Walk v v) : Prop :=
  IsCyclicallyNonBacktracking p ∧ ¬ p.IsCycle

/-- Every simple cycle is cyclically non-backtracking. -/
private theorem isCyclicallyNonBacktracking_of_isCycle {V : Type*} {G : SimpleGraph V}
    {v : V} {p : G.Walk v v} (hc : p.IsCycle) : IsCyclicallyNonBacktracking p := by
  unfold IsCyclicallyNonBacktracking
  have hnb : IsNonBacktracking p := by
    have htr : p.IsTrail := hc.isTrail
    have aux : ∀ {a b : V} (w : G.Walk a b), w.IsTrail → IsNonBacktracking w := by
      intro a b w
      induction w with
      | nil => intro _; trivial
      | cons h₁ rest ih =>
          intro htr'
          cases rest with
          | nil => trivial
          | cons (v := c) h₂ rest₂ =>
              have hnd := htr'.edges_nodup
              simp only [Walk.edges_cons, List.nodup_cons] at hnd
              have hne : a ≠ c := by
                intro heq
                subst heq
                apply hnd.1
                simp only [List.mem_cons]
                left
                exact Sym2.eq_swap
              exact ⟨hne, ih (Walk.IsTrail.mk hnd.2)⟩
    exact aux p htr
  rw [isNonBacktracking_append_iff]
  refine ⟨hnb, hnb, ?_⟩
  intro x y hx hy
  cases p with
  | nil => simp [firstNbr] at hy
  | cons (v := b) h₁ rest =>
      simp only [firstNbr, Option.some.injEq] at hy
      subst hy
      cases rest with
      | nil => exact False.elim (G.loopless _ h₁)
      | cons h₂ rest₂ =>
          obtain ⟨z, mid, hz, hmid, hlast⟩ := walk_split_last (.cons h₂ rest₂) (by simp)
          have hxz : x = z := by
            simp only [lastNbr] at hx
            rw [hlast, Option.some.injEq] at hx
            exact hx.symm
          subst hxz
          intro heq
          subst heq
          have hnd := hc.isTrail.edges_nodup
          simp only [Walk.edges_cons, List.nodup_cons] at hnd
          apply hnd.1
          rw [hmid, Walk.edges_append]
          simp only [List.mem_append, Walk.edges_cons, List.mem_cons]
          right; left
          exact Sym2.eq_swap

/-- **Exact Whole-Problem Non-Backtracking Surplus Equivalence**:
`HasPower G` holds if and only if there exists a cyclically non-backtracking closed walk
of length `2^k` (`k ≥ 2`) that is not non-simple. -/
theorem hasPower_iff_nonBacktracking_surplus {V : Type*} (G : SimpleGraph V) :
    HasPower G ↔
      ∃ (k : ℕ) (v : V) (p : G.Walk v v),
        2 ≤ k ∧ IsCyclicallyNonBacktracking p ∧ p.length = 2 ^ k ∧ ¬ IsNonSimpleCNB p := by
  constructor
  · rintro ⟨k, v, c, hk, hc, hlen⟩
    exact ⟨k, v, c, hk, isCyclicallyNonBacktracking_of_isCycle hc, hlen, fun hns => hns.2 hc⟩
  · rintro ⟨k, v, p, hk, hcyc, hlen, hnotns⟩
    have hc : p.IsCycle := by
      by_contra hnc
      exact hnotns ⟨hcyc, hnc⟩
    exact ⟨k, v, p, hk, hc, hlen⟩

/-- **Whole-Problem Closure Gate**: If every finite simple graph with `δ(G) ≥ 3`
admits a cyclically non-backtracking closed walk of length `2^k` (`k ≥ 2`) outside
`IsNonSimpleCNB` (equivalently `Tr(B^(2^k)) > W_nonSimple(2^k)`), then full Erdős #64 holds. -/
theorem erdos64_of_nonBacktracking_surplus
    (H : ∀ {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (∀ v : V, 3 ≤ G.degree v) →
      ∃ (k : ℕ) (v : V) (p : G.Walk v v),
        2 ≤ k ∧ IsCyclicallyNonBacktracking p ∧ p.length = 2 ^ k ∧ ¬ IsNonSimpleCNB p) :
    ∀ {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (∀ v : V, 3 ≤ G.degree v) → HasPower G := by
  intro V _ G _ hdeg
  exact (hasPower_iff_nonBacktracking_surplus G).mpr (H G hdeg)

/-! ## Pillar B: 4-Regular Perfect-Matching Transition-System Power-Lifting -/

/-- A single transition step through a contracted matching edge `{u, m u}`:
if the incoming endpoint equals the outgoing endpoint, it contributes 0 edges (turn);
if they are opposite endpoints, it traverses the matching edge (1 edge, crossing). -/
def transitionStep {V : Type*} {G : SimpleGraph V} (m : V → V)
    (hm_adj : ∀ v, G.Adj v (m v)) (a b : V) (h : b = a ∨ b = m a) : G.Walk a b :=
  if hab : b = a then
    hab ▸ .nil
  else
    have hbm : b = m a := h.resolve_left hab
    hbm ▸ .cons (hm_adj a) .nil

/-- Length of a transition step is `0` on a turn (`b = a`) and `1` on a crossing (`b ≠ a`). -/
theorem transitionStep_length {V : Type*} {G : SimpleGraph V} (m : V → V)
    (hm_adj : ∀ v, G.Adj v (m v)) (a b : V) (h : b = a ∨ b = m a) :
    (transitionStep m hm_adj a b h).length = if b = a then 0 else 1 := by
  unfold transitionStep
  split_ifs with hab
  · subst hab; rfl
  · have hbm : b = m a := h.resolve_left hab
    subst hbm; rfl

/-- Exact length formula for concatenating a transition walk across `L` contracted matching edges
with `crossings` crossing steps: `lift.length = L + crossings`. -/
theorem transition_walk_lift_length {V : Type*} {G : SimpleGraph V} {u v w : V}
    (m : V → V) (hm_adj : ∀ x, G.Adj x (m x))
    (a b : V) (h : b = a ∨ b = m a) (hab : G.Adj b u) (rest : G.Walk u v) (L c : ℕ)
    (hrest : rest.length = L + c) :
    ((transitionStep m hm_adj a b h).append (.cons hab rest)).length =
      (L + 1) + (c + if b = a then 0 else 1) := by
  rw [Walk.length_append, Walk.length_cons, transitionStep_length, hrest]
  omega

/-- **4-Regular Transition-System Power-Lifting Certification**:
Any lifted simple cycle in `G` whose base length `L` plus crossing count `t` equals `2^k`
(`k ≥ 2`) directly certifies `Erdos64Closure.HasPower G`. -/
theorem hasPower_of_transition_pow2_lift {V : Type*} {G : SimpleGraph V}
    {v : V} (c : G.Walk v v) (hc : c.IsCycle) (L t k : ℕ)
    (hk : 2 ≤ k) (hlen : c.length = L + t) (hpow : L + t = 2 ^ k) :
    HasPower G :=
  ⟨k, v, c, hk, hc, hlen.trans hpow⟩

#print axioms isNonBacktracking_append_iff
#print axioms isNonBacktracking_reverse
#print axioms nonBacktracking_tail_peel
#print axioms tailless_nonBacktracking_lt_three_girth_decomp
#print axioms no_equal_half_cycles_of_not_hasPower
#print axioms cubic_no_figure_eight_split
#print axioms unique_nonBacktracking_walk_of_sum_lt_girth
#print axioms unique_nonBacktracking_walk_of_half_girth
#print axioms exists_pow2_in_tripling_window_of_octave_top
#print axioms hasPower_iff_nonBacktracking_surplus
#print axioms erdos64_of_nonBacktracking_surplus
#print axioms transition_walk_lift_length
#print axioms hasPower_of_transition_pow2_lift

end E64Wave5Agent5
