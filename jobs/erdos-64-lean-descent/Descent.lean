import Mathlib

/-!
Erdos 64: kernel-checkable descent infrastructure.
The open global forcing assertion is deliberately NOT assumed.
Use the same SimpleGraph.Walk, IsCycle and length as Formal Conjectures.
-/

namespace Erdos64Descent
open SimpleGraph
open scoped Sym2

def PowerFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ (k : ℕ) (v : V) (c : G.Walk v v),
    2 ≤ k → c.IsCycle → c.length ≠ 2 ^ k

theorem two_pow_gt_one {k : ℕ} (hk : 1 ≤ k) : 1 < 2 ^ k := by
  cases k with
  | zero => omega
  | succ k =>
    rw [pow_succ]
    have h : 0 < (2 : ℕ) ^ k := pow_pos (by decide) _
    omega

/-- Two internally disjoint paths whose lengths sum to a power of two
    give an actual simple cycle in the original graph. -/
theorem power_cycle_of_disjoint_paths {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (q : G.Walk v u)
    (hp : p.IsPath) (hq : q.IsPath)
    (hd : p.support.tail.Disjoint q.support.tail)
    {k : ℕ} (hk : 2 ≤ k) (hlen : p.length + q.length = 2 ^ k) :
    ∃ c : G.Walk u u, c.IsCycle ∧ c.length = 2 ^ k := by
  have hk' : 1 ≤ k := by omega
  have hpow : 2 < (2 : ℕ) ^ k := by
    cases k with
    | zero => omega
    | succ j =>
      rw [pow_succ]
      have hj : 1 ≤ j := by omega
      have h := two_pow_gt_one hj
      omega
  have hlong : 1 < p.length ∨ 1 < q.length := by omega
  exact ⟨p.append q, hp.isCycle_append hq hd hlong, by simpa using hlen⟩

/-- The exact terminal contradiction needed by the root-path argument. -/
theorem dyadic_collision {V : Type*} {G : SimpleGraph V}
    {u v : V} (p q : G.Walk u v)
    (hp : p.IsPath) (hq : q.IsPath)
    (hd : p.support.tail.Disjoint q.reverse.support.tail)
    {k : ℕ} (hk : 2 ≤ k)
    (h₁ : p.length = 2 ^ k) (h₂ : q.length = 2 ^ k) :
    ∃ c : G.Walk u u, c.IsCycle ∧ c.length = 2 ^ (k + 1) := by
  apply power_cycle_of_disjoint_paths p q.reverse hp hq.reverse hd (by omega)
  simp only [SimpleGraph.Walk.length_reverse, h₁, h₂, pow_succ]
  omega

theorem forbidden_dyadic_collision {V : Type*} {G : SimpleGraph V}
    (hG : PowerFree G) {u v : V} (p q : G.Walk u v)
    (hp : p.IsPath) (hq : q.IsPath) {k : ℕ} (hk : 2 ≤ k)
    (h₁ : p.length = 2 ^ k) (h₂ : q.length = 2 ^ k) :
    ¬ p.support.tail.Disjoint q.reverse.support.tail := by
  intro hd
  obtain ⟨c, hc, hlen⟩ := dyadic_collision p q hp hq hd hk h₁ h₂
  exact hG (k+1) u c (by omega) hc hlen

/-- Exact walk parity when every edge except a designated exceptional
    undirected edge flips a two-coloring.  Counts occurrences of that edge,
    so the lemma works for arbitrary walks, not just paths. -/
theorem walk_parity_one_exception {V : Type*} [DecidableEq V]
    {H : SimpleGraph V} (color : V → Fin 2) (e : Sym2 V)
    (hc : ∀ a b, H.Adj a b → (color a = color b ↔ s(a,b) = e))
    {u v : V} (p : H.Walk u v) :
    (p.length + p.edges.count e + (color u).val + (color v).val) % 2 = 0 := by
  induction p with
  | nil =>
    simp only [Walk.length_nil, Walk.edges_nil, List.count_nil, Nat.zero_add]
    omega
  | @cons a b c hab p ih =>
    have ha := (color a).isLt
    have hb := (color b).isLt
    by_cases he : s(a,b) = e
    · have hcol := congrArg Fin.val ((hc a b hab).mpr he)
      simp only [Walk.length_cons, Walk.edges_cons, List.count_cons]
      simp [he]
      omega
    · have hcol : (color a).val ≠ (color b).val := by
        intro h
        exact he ((hc a b hab).mp (Fin.ext h))
      simp only [Walk.length_cons, Walk.edges_cons, List.count_cons]
      simp [he, Ne.symm he]
      omega

/-- A same-color exception cannot occur in an even simple cycle:
    a simple cycle uses each edge at most once. -/
theorem even_cycle_avoids_exception {V : Type*} [DecidableEq V]
    {H : SimpleGraph V} (color : V → Fin 2) (e : Sym2 V)
    (hc : ∀ a b, H.Adj a b → (color a = color b ↔ s(a,b) = e))
    {v : V} (c : H.Walk v v) (hcyc : c.IsCycle)
    (heven : c.length % 2 = 0) :
    e ∉ c.edges := by
  intro hm
  have hcount := List.count_eq_one_of_mem hcyc.isTrail.edges_nodup hm
  have hpar := walk_parity_one_exception color e hc c
  omega

/-- All even simple cycles in a graph obtained by a single same-side
    edge addition transfer to the original graph, with exact length. -/
theorem even_cycle_transfer {V : Type*} [DecidableEq V]
    {G H : SimpleGraph V} (color : V → Fin 2) (e : Sym2 V)
    (hc : ∀ a b, H.Adj a b → (color a = color b ↔ s(a,b) = e))
    (hold : ∀ f, f ∈ H.edgeSet → f ≠ e → f ∈ G.edgeSet)
    {v : V} (c : H.Walk v v) (hcyc : c.IsCycle)
    (heven : c.length % 2 = 0) :
    ∃ d : G.Walk v v, d.IsCycle ∧ d.length = c.length := by
  have havoid := even_cycle_avoids_exception color e hc c hcyc heven
  have htransfer : ∀ f, f ∈ c.edges → f ∈ G.edgeSet := by
    intro f hf
    exact hold f (c.edges_subset_edgeSet hf) (fun h => havoid (h ▸ hf))
  exact ⟨c.transfer G htransfer, hcyc.transfer htransfer, by simp⟩

/-- The actual power-free invariant for the one-edge parity repair. -/
theorem power_free_after_parity_repair {V : Type*} [DecidableEq V]
    {G H : SimpleGraph V} (color : V → Fin 2) (e : Sym2 V)
    (hc : ∀ a b, H.Adj a b → (color a = color b ↔ s(a,b) = e))
    (hold : ∀ f, f ∈ H.edgeSet → f ≠ e → f ∈ G.edgeSet)
    (hG : PowerFree G) : PowerFree H := by
  intro k v c hk hcyc hlen
  have heven : c.length % 2 = 0 := by
    rw [hlen]
    cases k with
    | zero => omega
    | succ k => rw [pow_succ]; omega
  obtain ⟨d, hd, hl⟩ := even_cycle_transfer color e hc hold c hcyc heven
  exact hG k v d hk hd (hl.trans hlen)

#print axioms power_cycle_of_disjoint_paths
#print axioms dyadic_collision
#print axioms forbidden_dyadic_collision
#print axioms walk_parity_one_exception
#print axioms even_cycle_avoids_exception
#print axioms even_cycle_transfer
#print axioms power_free_after_parity_repair

end Erdos64Descent
