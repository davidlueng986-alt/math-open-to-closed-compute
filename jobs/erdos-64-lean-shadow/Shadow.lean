import Mathlib

/-!
Exact midpoint expansion of simple graph walks. This verifies the mathematical
lifting operation used by the parity-shadow proof attack. The absence of a
collision is an explicit hypothesis, not an assumed global forcing theorem.
-/
namespace Erdos64Shadow
open SimpleGraph
open scoped Sym2

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
variable (f : W → V) (mid : Sym2 W → V)
variable (ha : ∀ {a b : W}, H.Adj a b → G.Adj (f a) (mid s(a,b)))
variable (hb : ∀ {a b : W}, H.Adj a b → G.Adj (mid s(a,b)) (f b))

/-- Replace each edge by the designated length-two path in the original graph. -/
def expand {a b : W} (p : H.Walk a b) : G.Walk (f a) (f b) :=
  match p with
  | .nil => .nil
  | .cons h q => .cons (ha h) (.cons (hb h) (expand q))

theorem length_expand {a b : W} (p : H.Walk a b) :
    (expand f mid ha hb p).length = 2 * p.length := by
  induction p with
  | nil => simp [expand]
  | cons h q ih =>
    simp only [expand, Walk.length_cons, ih]
    omega

/-- The expanded tail support is the multiset of old branch vertices and
    selected midpoints. This identity exposes every possible collision. -/
theorem tail_support_expand_perm {a b : W} (p : H.Walk a b) :
    (expand f mid ha hb p).support.tail.Perm
      (p.support.tail.map f ++ p.edges.map mid) := by
  induction p with
  | nil => simp [expand]
  | @cons a b c h q ih =>
    simp only [expand, Walk.support_cons, List.tail_cons, Walk.edges_cons, List.map_cons]
    have hq : q.support = b :: q.support.tail := (q.cons_tail_support).symm
    have he : (expand f mid ha hb q).support =
        f b :: (expand f mid ha hb q).support.tail :=
      ((expand f mid ha hb q).cons_tail_support).symm
    conv_lhs => rw [he]
    conv_rhs => rw [hq, List.map_cons]
    exact ((ih.cons (f b)).cons (mid s(a,b))).trans
      (List.perm_middle (l₁ := f b :: q.support.tail.map f) (l₂ := q.edges.map mid)).symm

/-- Any simple cycle in a shadow with distinct midpoint images and
    no branch-midpoint overlap lifts to a genuine simple cycle. -/
theorem cycle_expand {a : W} (c : H.Walk a a) (hc : c.IsCycle)
    (hf : Function.Injective f)
    (hm : (c.edges.map mid).Nodup)
    (hd : (c.support.tail.map f).Disjoint (c.edges.map mid)) :
    (expand f mid ha hb c).IsCycle := by
  have hbranches : (c.support.tail.map f).Nodup :=
    (List.nodup_map_iff hf).mpr hc.support_nodup
  have hall : (c.support.tail.map f ++ c.edges.map mid).Nodup :=
    List.nodup_append'.mpr ⟨hbranches, hm, hd⟩
  have htail : (expand f mid ha hb c).support.tail.Nodup :=
    (tail_support_expand_perm f mid ha hb c).nodup_iff.mpr hall
  have hlen : 3 ≤ (expand f mid ha hb c).length := by
    rw [length_expand]
    have := hc.three_le_length
    omega
  have hnil : ¬ (expand f mid ha hb c).Nil := by
    intro h
    have hz := Walk.length_eq_zero_iff.mpr h
    omega
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  refine ⟨Walk.IsPath.mk' ?_, hlen⟩
  rwa [Walk.support_tail_of_not_nil _ hnil]

include ha hb in
/-- Exact original power-cycle witness, with the exponent increased by one. -/
theorem power_cycle_expand {a : W} (c : H.Walk a a) (hc : c.IsCycle)
    (hf : Function.Injective f)
    (hm : (c.edges.map mid).Nodup)
    (hd : (c.support.tail.map f).Disjoint (c.edges.map mid))
    {k : ℕ} (hk : 2 ≤ k) (hlen : c.length = 2^k) :
    ∃ (j : ℕ) (v : V) (d : G.Walk v v),
      2 ≤ j ∧ d.IsCycle ∧ d.length = 2^j := by
  refine ⟨k+1, f a, expand f mid ha hb c, by omega,
    cycle_expand f mid ha hb c hc hf hm hd, ?_⟩
  rw [length_expand, hlen, pow_succ]
  omega

#print axioms length_expand
#print axioms tail_support_expand_perm
#print axioms cycle_expand
#print axioms power_cycle_expand

end Erdos64Shadow

/-! Well-founded closure contract: this connects a genuinely global safe
    descent theorem to the exact original Erdős #64 conclusion. The global
    descent is an explicit, as-yet-unproved premise, not an axiom or a sorry. -/
namespace Erdos64Closure
open SimpleGraph
open scoped Sym2
universe u

def HasPower {V : Type u} (G : SimpleGraph V) : Prop :=
  ∃ (k : ℕ) (v : V) (c : G.Walk v v),
    2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k

def Near {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] : Prop :=
  (∃ v, 3 ≤ G.degree v) ∧
    (∃ w, ∀ v, v ≠ w → 3 ≤ G.degree v)

/-- A safe smaller near graph, with the actual original-cycle implication. -/
def SafeStep {V : Type u} (G : SimpleGraph V) [Fintype V] : Prop :=
  ∃ (W : Type u) (H : SimpleGraph W) (fw : Fintype W)
    (dh : DecidableRel H.Adj),
    @Fintype.card W fw < Fintype.card V ∧
    @Near W H fw dh ∧ (HasPower H → HasPower G)

/-- A genuinely disjoint midpoint shadow is sufficient for a safe step.
    This packages the previously verified lifting result into the descent
    interface used by the final induction. -/
theorem safe_step_of_uniform_shadow {V W : Type u}
    (G : SimpleGraph V) (H : SimpleGraph W)
    [Fintype V] [Fintype W] [DecidableRel H.Adj]
    (hsize : Fintype.card W < Fintype.card V) (hnear : Near H)
    (f : W → V) (mid : Sym2 W → V)
    (ha : ∀ {a b : W}, H.Adj a b → G.Adj (f a) (mid s(a,b)))
    (hb : ∀ {a b : W}, H.Adj a b → G.Adj (mid s(a,b)) (f b))
    (hf : Function.Injective f)
    (hn : ∀ {a : W} (c : H.Walk a a), c.IsCycle →
      (c.edges.map mid).Nodup)
    (hd : ∀ {a : W} (c : H.Walk a a), c.IsCycle →
      (c.support.tail.map f).Disjoint (c.edges.map mid)) :
    SafeStep G := by
  refine ⟨W, H, inferInstance, inferInstance, hsize, hnear, ?_⟩
  rintro ⟨k,a,c,hk,hc,hl⟩
  exact Erdos64Shadow.power_cycle_expand f mid ha hb c hc hf
    (hn c hc) (hd c hc) hk hl

/-- Complete induction over the order of arbitrary finite near graphs.
    The only unproved global obligation is the supplied safe-step premise. -/
theorem near_of_global_descent
    (hstep : ∀ (V : Type u) (G : SimpleGraph V)
      [Fintype V] [DecidableRel G.Adj],
      Near G → ¬ HasPower G → SafeStep G) :
    ∀ (V : Type u) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
      Near G → HasPower G := by
  classical
  have go : ∀ n : ℕ, ∀ (V : Type u) (G : SimpleGraph V)
      [Fintype V] [DecidableRel G.Adj],
      Fintype.card V = n → Near G → HasPower G := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V G instV instG hn hnear
      by_contra hnot
      obtain ⟨W,H,fw,dh,hsize,hnH,htransfer⟩ :=
        hstep V G hnear hnot
      letI : Fintype W := fw
      letI : DecidableRel H.Adj := dh
      have hlt : Fintype.card W < n := by
        rw [← hn]
        exact hsize
      exact hnot (htransfer (ih (Fintype.card W) hlt W H rfl hnH))
  intro V G instV instG hnear
  exact go (Fintype.card V) V G rfl hnear

/-- The conclusion exactly matches the original Formal Conjectures statement.
    This is a conditional closure contract, not a proof of hstep. -/
theorem erdos64_of_global_descent
    (hstep : ∀ (V : Type u) (G : SimpleGraph V)
      [Fintype V] [DecidableRel G.Adj],
      Near G → ¬ HasPower G → SafeStep G) :
    ∀ (V : Type u) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
      G.minDegree ≥ 3 → ∃ (k : ℕ) (v : V) (c : G.Walk v v),
        k ≥ 2 ∧ c.IsCycle ∧ c.length = 2 ^ k := by
  intro V G instV instG hmin
  rcases isEmpty_or_nonempty V with hempty | hnonempty
  · letI : IsEmpty V := hempty
    have hz : G.minDegree = 0 := SimpleGraph.minDegree_of_subsingleton
    omega
  · obtain ⟨w⟩ := hnonempty
    have hall : ∀ v, 3 ≤ G.degree v :=
      fun v => hmin.trans (G.minDegree_le_degree v)
    exact near_of_global_descent hstep V G
      ⟨⟨w, hall w⟩, ⟨w, fun v _ => hall v⟩⟩

#print axioms safe_step_of_uniform_shadow
#print axioms near_of_global_descent
#print axioms erdos64_of_global_descent
end Erdos64Closure
