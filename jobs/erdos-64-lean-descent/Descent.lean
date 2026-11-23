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
      simp [he]
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

/-- The concrete simple-graph operation used in parity repair. No new
    power cycle can be created by adding one same-color edge to a
    bipartite power-free graph. -/
theorem same_color_edge_safe {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} (color : V → Fin 2)
    (hc : ∀ u v, G.Adj u v → color u ≠ color v)
    (a b : V) (hab : a ≠ b) (hcolor : color a = color b)
    (hG : PowerFree G) :
    PowerFree (G ⊔ SimpleGraph.edge a b) := by
  apply power_free_after_parity_repair color s(a,b) _ _ hG
  · intro u v huv
    constructor
    · intro hsame
      rcases (SimpleGraph.sup_adj G (SimpleGraph.edge a b) u v).mp huv with h | h
      · exact False.elim ((hc u v h) hsame)
      · exact ((SimpleGraph.adj_edge a b).mp h).1.symm
    · intro he
      rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hcolor
      · exact hcolor.symm
  · intro f hf hne
    rw [SimpleGraph.edgeSet_sup] at hf
    rcases hf with hg | he
    · exact hg
    · rw [SimpleGraph.edgeSet_edge_of_ne hab] at he
      exact False.elim (hne (Set.mem_singleton_iff.mp he))

/-- Adding a new edge increases the degree at its first endpoint by one. -/
theorem degree_add_new_edge_left {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V)
    (hab : a ≠ b) (hn : ¬ G.Adj a b) :
    (G ⊔ SimpleGraph.edge a b).degree a = G.degree a + 1 := by
  have hset : (G ⊔ SimpleGraph.edge a b).neighborFinset a =
      insert b (G.neighborFinset a) := by
    ext x
    simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.sup_adj,
      Finset.mem_insert, SimpleGraph.edge_adj]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · rcases h.1 with ⟨_, rfl⟩ | ⟨h', _⟩
        · exact Or.inl rfl
        · exact False.elim (hab h')
    · rintro (rfl | h)
      · exact Or.inr ⟨Or.inl ⟨by trivial, by trivial⟩, hab⟩
      · exact Or.inl h
  have hb : b ∉ G.neighborFinset a := by
    exact fun h => hn ((G.mem_neighborFinset a b).mp h)
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hset,
    Finset.card_insert_of_notMem hb, SimpleGraph.card_neighborFinset_eq_degree]

/-- The degree at the second endpoint also increases by one.  Prove
    directly to avoid dependent rewriting of decidable graph instances. -/
theorem degree_add_new_edge_right {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V)
    (hab : a ≠ b) (hn : ¬ G.Adj a b) :
    (G ⊔ SimpleGraph.edge a b).degree b = G.degree b + 1 := by
  have hset : (G ⊔ SimpleGraph.edge a b).neighborFinset b =
      insert a (G.neighborFinset b) := by
    ext x
    simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.sup_adj,
      Finset.mem_insert, SimpleGraph.edge_adj]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · rcases h.1 with ⟨h', _⟩ | ⟨_, rfl⟩
        · exact False.elim (hab h'.symm)
        · exact Or.inl rfl
    · rintro (rfl | h)
      · exact Or.inr ⟨Or.inr ⟨by trivial, by trivial⟩, hab.symm⟩
      · exact Or.inl h
  have ha : a ∉ G.neighborFinset b := by
    exact fun h => hn (((G.mem_neighborFinset b a).mp h).symm)
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hset,
    Finset.card_insert_of_notMem ha, SimpleGraph.card_neighborFinset_eq_degree]

/-- One complete degree-and-cycle safe repair. Two degree-two vertices
    in one bipartition side are repaired while leaving at most the
    designated third defect. The global unavoidability of such a
    subgraph is not assumed. -/
theorem repair_two_same_color_ports {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (color : V → Fin 2)
    (hc : ∀ u v, G.Adj u v → color u ≠ color v)
    (a b w : V) (hab : a ≠ b) (hcolor : color a = color b)
    (ha : G.degree a = 2) (hb : G.degree b = 2)
    (hrest : ∀ x, x ≠ a → x ≠ b → x ≠ w → 3 ≤ G.degree x)
    (hG : PowerFree G) :
    PowerFree (G ⊔ SimpleGraph.edge a b) ∧
    ∀ x, x ≠ w → 3 ≤ (G ⊔ SimpleGraph.edge a b).degree x := by
  have hn : ¬ G.Adj a b := fun h => hc a b h hcolor
  have hda := degree_add_new_edge_left G a b hab hn
  have hdb := degree_add_new_edge_right G a b hab hn
  refine ⟨same_color_edge_safe color hc a b hab hcolor hG, ?_⟩
  intro x hx
  by_cases hxa : x = a
  · subst x
    omega
  by_cases hxb : x = b
  · subst x
    omega
  exact (hrest x hxa hxb hx).trans
    (G.degree_le_of_le (v := x) (H := G ⊔ SimpleGraph.edge a b) le_sup_left)

#print axioms power_cycle_of_disjoint_paths
#print axioms dyadic_collision
#print axioms forbidden_dyadic_collision
#print axioms walk_parity_one_exception
#print axioms even_cycle_avoids_exception
#print axioms even_cycle_transfer
#print axioms power_free_after_parity_repair
#print axioms same_color_edge_safe
#print axioms degree_add_new_edge_left
#print axioms degree_add_new_edge_right
#print axioms repair_two_same_color_ports

end Erdos64Descent
