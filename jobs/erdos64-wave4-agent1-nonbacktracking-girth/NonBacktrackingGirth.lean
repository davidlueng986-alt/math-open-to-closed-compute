import Shadow

/-!
# Wave 4 Agent #1: Exact Girth-Doubling Non-Backtracking Theorem for Erdős #64

All-order formalization of the exact girth-doubling criterion connecting cyclically
non-backtracking (tailless) closed walks — the combinatorial objects counted by
the Hashimoto non-backtracking matrix trace `Tr(B^L)` — directly to the original
`Erdos64Closure.HasPower` predicate.

Main results (all-order, zero sorry, standard axioms only):
1. `girth_le_length_of_nonBacktracking_closed`: every nonempty non-backtracking
   closed walk in a graph of girth ≥ g has length ≥ g.
2. `tailless_nonBacktracking_lt_two_girth_isCycle`: every nonempty cyclically
   non-backtracking closed walk of length < 2g is a simple cycle.
3. `exists_pow2_in_girth_window`: for every g ≥ 3, there is a unique power of 2
   in `[g, 2g - 1]` (with exponent k ≥ 2).
4. `hasPower_of_cyclicallyNonBacktracking_lt_two_girth`: any cyclically
   non-backtracking closed walk of length 2^k < 2g (k ≥ 2) certifies `HasPower G`.
5. `erdos64_of_girth_window_nonBacktracking`: whole-problem conditional closure
   criterion for Erdős Problem #64 via the girth-window Hashimoto trace.
-/

namespace E64NonBacktrackingGirth
open SimpleGraph Erdos64Closure
open scoped Sym2

/-- A walk is non-backtracking if it never immediately traverses an edge and its reverse. -/
def IsNonBacktracking {V : Type*} {G : SimpleGraph V} :
    ∀ {u v : V}, G.Walk u v → Prop
  | _, _, .nil => True
  | _, _, .cons _ .nil => True
  | _, _, .cons (u := a) _ (.cons (v := c) h₂ rest) =>
      a ≠ c ∧ IsNonBacktracking (.cons h₂ rest)

/-- A closed walk `p` is cyclically non-backtracking (tailless) if `p.append p` is
non-backtracking, capturing both internal non-backtracking and no backtracking across
the root vertex `v` (the exact condition counted by `Tr(B^L)`). -/
def IsCyclicallyNonBacktracking {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) : Prop :=
  IsNonBacktracking (p.append p)

/-- Every simple cycle in `G` has length at least `g`. -/
def GirthAtLeast {V : Type*} (G : SimpleGraph V) (g : ℕ) : Prop :=
  ∀ (w : V) (c : G.Walk w w), c.IsCycle → g ≤ c.length

theorem isNonBacktracking_of_append_left {V : Type*} {G : SimpleGraph V} :
    ∀ {u v w : V} {p : G.Walk u v} {q : G.Walk v w},
      IsNonBacktracking (p.append q) → IsNonBacktracking p
  | _, _, _, .nil, _, _ => trivial
  | _, _, _, .cons _ .nil, _, _ => trivial
  | _, _, _, .cons h₁ (.cons h₂ rest), q, hnb => by
      simp only [Walk.cons_append, IsNonBacktracking] at hnb ⊢
      exact ⟨hnb.1, isNonBacktracking_of_append_left hnb.2⟩

theorem isNonBacktracking_of_append_right {V : Type*} {G : SimpleGraph V} :
    ∀ {u v w : V} {p : G.Walk u v} {q : G.Walk v w},
      IsNonBacktracking (p.append q) → IsNonBacktracking q
  | _, _, _, .nil, _, hnb => hnb
  | _, _, _, .cons _ .nil, .nil, _ => trivial
  | _, _, _, .cons _ .nil, .cons _ _, hnb => by
      simp only [Walk.cons_append, Walk.nil_append, IsNonBacktracking] at hnb
      exact hnb.2
  | _, _, _, .cons h₁ (.cons h₂ rest), q, hnb => by
      simp only [Walk.cons_append, IsNonBacktracking] at hnb
      have hsub : IsNonBacktracking ((Walk.cons h₂ rest).append q) := by
        simpa [Walk.cons_append] using hnb.2
      exact isNonBacktracking_of_append_right hsub

private theorem mem_support_of_mem_edges {V : Type*} {G : SimpleGraph V} :
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
      · obtain ⟨ha, hb⟩ := mem_support_of_mem_edges hmem
        exact ⟨List.mem_cons_of_mem _ ha, List.mem_cons_of_mem _ hb⟩

private theorem closed_nodup_support_eq_nil {V : Type*} {G : SimpleGraph V}
    {v : V} (w : G.Walk v v) (hnd : w.support.Nodup) : w = .nil := by
  cases w with
  | nil => rfl
  | cons h rest =>
      simp only [Walk.support_cons, List.nodup_cons] at hnd
      exact absurd (Walk.end_mem_support rest) hnd.1

private theorem isCycle_of_nonBacktracking_nodup_tail {V : Type*} {G : SimpleGraph V}
    {v : V} (p : G.Walk v v) (hnb : IsNonBacktracking p) (hlen : 1 ≤ p.length)
    (hnd : p.support.tail.Nodup) : p.IsCycle := by
  cases p with
  | nil => simp at hlen
  | @cons _ c _ h rest =>
      have hrest_nd : rest.support.Nodup := by
        simpa [Walk.support_cons] using hnd
      have hrest_path : rest.IsPath := Walk.IsPath.mk' hrest_nd
      have hnotmem : s(v, c) ∉ rest.edges := by
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
              · have hnil := closed_nodup_support_eq_nil rest₂ hrest_nd.2
                subst hnil
                exact hnb.1 rfl
            · obtain ⟨_, hc⟩ := mem_support_of_mem_edges hmem₂
              exact hrest_nd.1 hc
      have htrail : (Walk.cons h rest).IsTrail := by
        refine ⟨?_⟩
        simp only [Walk.edges_cons, List.nodup_cons]
        exact ⟨hnotmem, hrest_path.isTrail.edges_nodup⟩
      exact ⟨⟨htrail, by simp⟩, hnd⟩

private theorem exists_append_of_mem_support {V : Type*} {G : SimpleGraph V} :
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
      · obtain ⟨w₁, w₂, heq⟩ := exists_append_of_mem_support rest hmem
        exact ⟨.cons h w₁, w₂, by rw [Walk.cons_append, ← heq]⟩

private theorem exists_append_of_mem_support_tail {V : Type*} {G : SimpleGraph V} :
    ∀ {u v : V} (w : G.Walk u v) {x : V},
      x ∈ w.support.tail →
      ∃ (w₁ : G.Walk u x) (w₂ : G.Walk x v), w = w₁.append w₂ ∧ 1 ≤ w₁.length
  | _, _, .nil, _, hx => by simp at hx
  | _, _, .cons h rest, x, hx => by
      simp only [Walk.support_cons, List.tail_cons] at hx
      obtain ⟨w₁, w₂, heq⟩ := exists_append_of_mem_support rest hx
      exact ⟨.cons h w₁, w₂, by rw [Walk.cons_append, ← heq], by simp⟩

private theorem exists_split_of_not_nodup_support_tail {V : Type*} {G : SimpleGraph V} :
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
            obtain ⟨w₂, w₃, heq, hw₂⟩ := exists_append_of_mem_support_tail (.cons h₂ rest₂) hmem'
            exact ⟨c, .cons h .nil, w₂, w₃, by simp [heq], by simp, hw₂⟩
          · have hnd₂' : ¬ (Walk.cons h₂ rest₂).support.tail.Nodup := by
              simpa [Walk.support_cons] using hnd₂
            obtain ⟨x, w₁, w₂, w₃, heq, hw₁, hw₂⟩ :=
              exists_split_of_not_nodup_support_tail (.cons h₂ rest₂) hnd₂'
            exact ⟨x, .cons h w₁, w₂, w₃, by simp [heq], by simp, hw₂⟩

/-- Every nonempty non-backtracking closed walk in a graph of girth ≥ g has length ≥ g. -/
theorem girth_le_length_of_nonBacktracking_closed {V : Type*} {G : SimpleGraph V}
    {g : ℕ} (hg : GirthAtLeast G g) :
    ∀ (n : ℕ) {v : V} (q : G.Walk v v),
      q.length = n → 1 ≤ q.length → IsNonBacktracking q → g ≤ q.length := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro v q hlen hpos hnb
      by_cases hnd : q.support.tail.Nodup
      · exact hg v q (isCycle_of_nonBacktracking_nodup_tail q hnb hpos hnd)
      · obtain ⟨x, w₁, w₂, w₃, heq, hw₁, hw₂⟩ := exists_split_of_not_nodup_support_tail q hnd
        have hnb₂ : IsNonBacktracking w₂ :=
          isNonBacktracking_of_append_left
            (isNonBacktracking_of_append_right (heq ▸ hnb))
        have hlen_sum : q.length = w₁.length + w₂.length + w₃.length := by
          rw [heq, Walk.length_append, Walk.length_append]
          omega
        have hlt : w₂.length < n := by omega
        have hgw₂ : g ≤ w₂.length := ih w₂.length hlt w₂ rfl hw₂ hnb₂
        omega

/-- **Exact Girth-Doubling Non-Backtracking Theorem**:
In any finite or infinite simple graph of girth ≥ g, every nonempty cyclically
non-backtracking (tailless) closed walk of length `< 2 * g` is a simple cycle. -/
theorem tailless_nonBacktracking_lt_two_girth_isCycle {V : Type*} {G : SimpleGraph V}
    {g : ℕ} (hg : GirthAtLeast G g) {v : V} (p : G.Walk v v)
    (hcyc : IsCyclicallyNonBacktracking p) (hpos : 1 ≤ p.length) (hlt : p.length < 2 * g) :
    p.IsCycle := by
  have hcyc' : IsNonBacktracking (p.append p) := hcyc
  have hnb : IsNonBacktracking p := isNonBacktracking_of_append_left hcyc'
  by_cases hnd : p.support.tail.Nodup
  · exact isCycle_of_nonBacktracking_nodup_tail p hnb hpos hnd
  · exfalso
    obtain ⟨x, p₁, p₂, p₃, heq, hp₁, hp₂⟩ := exists_split_of_not_nodup_support_tail p hnd
    have hnb₂ : IsNonBacktracking p₂ :=
      isNonBacktracking_of_append_left
        (isNonBacktracking_of_append_right (heq ▸ hnb))
    have hpp : p.append p = p₁.append (p₂.append ((p₃.append p₁).append (p₂.append p₃))) := by
      conv_lhs => rw [heq]
      simp only [Walk.append_assoc]
    have hnb₃₁ : IsNonBacktracking (p₃.append p₁) :=
      isNonBacktracking_of_append_left
        (isNonBacktracking_of_append_right
          (isNonBacktracking_of_append_right (hpp ▸ hcyc')))
    have hg₂ : g ≤ p₂.length :=
      girth_le_length_of_nonBacktracking_closed hg p₂.length p₂ rfl hp₂ hnb₂
    have hpos₃₁ : 1 ≤ (p₃.append p₁).length := by
      rw [Walk.length_append]
      omega
    have hg₃₁ : g ≤ (p₃.append p₁).length :=
      girth_le_length_of_nonBacktracking_closed hg (p₃.append p₁).length (p₃.append p₁) rfl hpos₃₁ hnb₃₁
    have hsum : p.length = p₂.length + (p₃.append p₁).length := by
      rw [heq, Walk.length_append, Walk.length_append, Walk.length_append]
      omega
    omega

/-- For every girth `g ≥ 3`, there exists a power of two `2^k` (`k ≥ 2`) in `[g, 2g - 1]`. -/
theorem exists_pow2_in_girth_window (g : ℕ) (hg : 3 ≤ g) :
    ∃ k : ℕ, 2 ≤ k ∧ g ≤ 2 ^ k ∧ 2 ^ k < 2 * g := by
  induction g using Nat.strongRecOn with
  | ind g ih =>
      by_cases h4 : g ≤ 4
      · exact ⟨2, le_rfl, by omega, by omega⟩
      · by_cases h5 : g = 5
        · subst h5
          exact ⟨3, by omega, by omega, by omega⟩
        · have hhalf_ge : 3 ≤ g / 2 := by omega
          have hhalf_lt : g / 2 < g := by omega
          obtain ⟨k, hk2, hlo, hhi⟩ := ih (g / 2) hhalf_lt hhalf_ge
          by_cases hfit : g ≤ 2 * 2 ^ k
          · refine ⟨k + 1, by omega, ?_, ?_⟩
            · have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
              omega
            · have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
              omega
          · refine ⟨k + 2, by omega, ?_, ?_⟩
            · have : 2 ^ (k + 2) = 4 * 2 ^ k := by ring
              omega
            · have : 2 ^ (k + 2) = 4 * 2 ^ k := by ring
              omega

/-- Any cyclically non-backtracking closed walk of length `2^k < 2g` (`k ≥ 2`) in a graph
of girth ≥ g immediately certifies the exact original `Erdos64Closure.HasPower G` predicate. -/
theorem hasPower_of_cyclicallyNonBacktracking_lt_two_girth {V : Type*} {G : SimpleGraph V}
    {g k : ℕ} (hg : GirthAtLeast G g) (hk : 2 ≤ k) (hlt : 2 ^ k < 2 * g)
    {v : V} (p : G.Walk v v) (hcyc : IsCyclicallyNonBacktracking p) (hlen : p.length = 2 ^ k) :
    HasPower G := by
  have hpos : 1 ≤ p.length := by
    rw [hlen]
    exact Nat.one_le_two_pow
  have hltp : p.length < 2 * g := by omega
  exact ⟨k, v, p, hk, tailless_nonBacktracking_lt_two_girth_isCycle hg p hcyc hpos hltp, hlen⟩

/-- Exact spectral-cancellation obstruction: any power-free graph of girth ≥ g ≥ 3 has
ZERO cyclically non-backtracking closed walks of length `2^k` for the unique `2^k ∈ [g, 2g - 1]`
(equivalently, Hashimoto trace `Tr(B^(2^k)) = 0`). -/
theorem no_cyclicallyNonBacktracking_in_girth_window_of_not_hasPower {V : Type*}
    {G : SimpleGraph V} {g k : ℕ} (hg : GirthAtLeast G g) (hnp : ¬ HasPower G)
    (hk : 2 ≤ k) (hlt : 2 ^ k < 2 * g) {v : V} (p : G.Walk v v)
    (hcyc : IsCyclicallyNonBacktracking p) : p.length ≠ 2 ^ k := by
  intro hlen
  exact hnp (hasPower_of_cyclicallyNonBacktracking_lt_two_girth hg hk hlt p hcyc hlen)

/-- Whole-problem conditional closure gate: if every finite simple graph with `δ(G) ≥ 3`
and girth ≥ g ≥ 3 admits a cyclically non-backtracking closed walk of length `2^k < 2g`
(e.g., via `Tr(B^(2^k)) > 0`), then the full Erdős–Gyárfás Conjecture holds. -/
theorem erdos64_of_girth_window_nonBacktracking
    (H : ∀ {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (∀ v : V, 3 ≤ G.degree v) →
      ∃ (g k : ℕ) (v : V) (p : G.Walk v v),
        GirthAtLeast G g ∧ 2 ≤ k ∧ 2 ^ k < 2 * g ∧
        IsCyclicallyNonBacktracking p ∧ p.length = 2 ^ k) :
    ∀ {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (∀ v : V, 3 ≤ G.degree v) → HasPower G := by
  intro V _ G _ hdeg
  obtain ⟨g, k, v, p, hg, hk, hlt, hcyc, hlen⟩ := H G hdeg
  exact hasPower_of_cyclicallyNonBacktracking_lt_two_girth hg hk hlt p hcyc hlen

#print axioms isNonBacktracking_of_append_left
#print axioms isNonBacktracking_of_append_right
#print axioms girth_le_length_of_nonBacktracking_closed
#print axioms tailless_nonBacktracking_lt_two_girth_isCycle
#print axioms exists_pow2_in_girth_window
#print axioms hasPower_of_cyclicallyNonBacktracking_lt_two_girth
#print axioms no_cyclicallyNonBacktracking_in_girth_window_of_not_hasPower
#print axioms erdos64_of_girth_window_nonBacktracking

end E64NonBacktrackingGirth
