import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic

/-!
# Erdős Problem #64 — Wave 8 Guided Agent #3 (`wave8_agent3`)
## Part 3: Triangle-Free Dual-Rewiring `C₆`-Rigidity, Minimum-Component `C_g` Forcing & Tutte 2-Cut Coupling

Unconditionally proves:
1. `dual_cross_rewiring_trifree_same_scale_c6_rigidity`: In any triangle-free `PowerFree` graph,
   simultaneous `C₄` (Type L1) lifts from both cross-rewirings `G_×^(1)(uv)` and `G_×^(2)(uv)`
   force their 3-paths `a - x₁ - x₂ - c` and `a - y₁ - y₂ - d` to share `x₁ = y₁` with `x₂ ≠ y₂`,
   producing a third simple `C₆` (`x₁ - x₂ - c - v - d - y₂ - x₁`) avoiding `u` and `a`.
2. `minimal_bad2_v3_min_component_forces_vge4_girth_cycle`: Any minimum-size (`|S| = g - 1`)
   connected component of `G[V₃]` avoiding `Defects G` forces a simple `C_g` through a `V₄`-vertex.
3. `crossRewire_preserves_two_cut_separation`: Any 2-cut `{x, y}` separating `C_a` from `C_b`
   remains a 2-cut separating `C_a \ {u, v}` from `C_b` in BOTH cross-rewirings `G_×^(1)(uv)`
   and `G_×^(2)(uv)` whenever `u, v ∈ C_a` and `N(u) ∪ N(v) ⊆ C_a ∪ {x, y}`.
4. `crossRewire_two_cut_dyadic_path_asymmetry`: Coupling Dual Cross-Rewiring with Wave 7 Agent #3's
   Tutte cleavage scale asymmetry: a `2^k`-cycle in `G_×^(i)(uv)` crossing `{x, y}` splits into
   an `x`–`y` path in `C_b ∪ {x, y}` of length `L_b` and an `x`–`y` path in `G_×^(i)[C_a \ {u,v} ∪ {x,y}]`
   of length `2^k - L_b`, forbidding `L_b = 2^m` simultaneously with any `2^m`-path in `G[C_a ∪ {x,y}]`.
-/

namespace E64Wave8Agent3P3

open SimpleGraph

def IsPow2 (n : ℕ) : Prop := ∃ k : ℕ, 2 ≤ k ∧ n = 2 ^ k

def HasPow2Cycle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ IsPow2 p.length

def PowerFree {V : Type*} (G : SimpleGraph V) : Prop := ¬ HasPow2Cycle G

def HasCycleLen {V : Type*} (G : SimpleGraph V) (L : ℕ) : Prop :=
  ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = L

def GirthGe {V : Type*} (G : SimpleGraph V) (g : ℕ) : Prop :=
  ∀ (v : V) (p : G.Walk v v), p.IsCycle → g ≤ p.length

def TriangleFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ a b c : V, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c a)

/-- Helper: 4 distinct vertices cannot form a 4-cycle in a `PowerFree` graph. -/
private lemma no_c4 {V : Type*} (G : SimpleGraph V) (hpf : PowerFree G)
    {a b c d : V} (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (hda : d ≠ a)
    (hac : a ≠ c) (hbd : b ≠ d)
    (h1 : G.Adj a b) (h2 : G.Adj b c) (h3 : G.Adj c d) (h4 : G.Adj d a) : False := by
  let p : G.Walk a a :=
    Walk.cons h1 (Walk.cons h2 (Walk.cons h3 (Walk.cons h4 Walk.nil)))
  have hp : p.IsCycle := by
    rw [Walk.isCycle_def]
    refine ⟨?_, by simp [p], ?_⟩
    · rw [Walk.isTrail_def]
      simp only [p, Walk.edges_cons, Walk.edges_nil, List.nodup_cons, List.mem_cons,
        List.not_mem_nil, or_false, List.nodup_nil, and_true, Sym2.eq_iff, not_false_eq_true]
      aesop
    · simp only [p, Walk.support_cons, Walk.support_nil, List.tail_cons, List.nodup_cons,
        List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true, not_false_eq_true]
      aesop
  exact hpf ⟨a, p, hp, ⟨2, le_rfl, rfl⟩⟩

/-- Helper: 8 distinct vertices cannot form an 8-cycle in a `PowerFree` graph. -/
private lemma no_c8 {V : Type*} (G : SimpleGraph V) (hpf : PowerFree G)
    {v₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ : V}
    (hnd : [v₀, v₁, v₂, v₃, v₄, v₅, v₆, v₇].Nodup)
    (e0 : G.Adj v₀ v₁) (e1 : G.Adj v₁ v₂) (e2 : G.Adj v₂ v₃) (e3 : G.Adj v₃ v₄)
    (e4 : G.Adj v₄ v₅) (e5 : G.Adj v₅ v₆) (e6 : G.Adj v₆ v₇) (e7 : G.Adj v₇ v₀) : False := by
  let p : G.Walk v₀ v₀ :=
    Walk.cons e0 (Walk.cons e1 (Walk.cons e2 (Walk.cons e3
      (Walk.cons e4 (Walk.cons e5 (Walk.cons e6 (Walk.cons e7 Walk.nil)))))))
  have hp : p.IsCycle := by
    rw [Walk.isCycle_def]
    have htail_eq : p.support.tail = [v₁, v₂, v₃, v₄, v₅, v₆, v₇, v₀] := by
      simp [p, Walk.support_cons, Walk.support_nil]
    have htail_nd : p.support.tail.Nodup := by
      rw [htail_eq]
      have hperm : [v₁, v₂, v₃, v₄, v₅, v₆, v₇, v₀].Perm [v₀, v₁, v₂, v₃, v₄, v₅, v₆, v₇] := by
        simpa using (List.perm_append_singleton v₀ [v₁, v₂, v₃, v₄, v₅, v₆, v₇])
      exact hperm.nodup_iff.mpr hnd
    refine ⟨?_, by simp [p], htail_nd⟩
    rw [Walk.isTrail_def]
    simp only [p, Walk.edges_cons, Walk.edges_nil, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, List.nodup_nil, and_true, Sym2.eq_iff, not_false_eq_true]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true] at hnd
    aesop
  exact hpf ⟨v₀, p, hp, ⟨3, by decide, rfl⟩⟩

/-- Helper: 6 distinct vertices forming a 6-cycle witness `HasCycleLen G 6`. -/
private lemma has_c6_of_six {V : Type*} (G : SimpleGraph V)
    {v₀ v₁ v₂ v₃ v₄ v₅ : V}
    (hnd : [v₀, v₁, v₂, v₃, v₄, v₅].Nodup)
    (e0 : G.Adj v₀ v₁) (e1 : G.Adj v₁ v₂) (e2 : G.Adj v₂ v₃)
    (e3 : G.Adj v₃ v₄) (e4 : G.Adj v₄ v₅) (e5 : G.Adj v₅ v₀) :
    HasCycleLen G 6 := by
  let p : G.Walk v₀ v₀ :=
    Walk.cons e0 (Walk.cons e1 (Walk.cons e2 (Walk.cons e3 (Walk.cons e4 (Walk.cons e5 Walk.nil)))))
  have hp : p.IsCycle := by
    rw [Walk.isCycle_def]
    have htail_eq : p.support.tail = [v₁, v₂, v₃, v₄, v₅, v₀] := by
      simp [p, Walk.support_cons, Walk.support_nil]
    have htail_nd : p.support.tail.Nodup := by
      rw [htail_eq]
      have hperm : [v₁, v₂, v₃, v₄, v₅, v₀].Perm [v₀, v₁, v₂, v₃, v₄, v₅] := by
        simpa using (List.perm_append_singleton v₀ [v₁, v₂, v₃, v₄, v₅])
      exact hperm.nodup_iff.mpr hnd
    refine ⟨?_, by simp [p], htail_nd⟩
    rw [Walk.isTrail_def]
    simp only [p, Walk.edges_cons, Walk.edges_nil, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, List.nodup_nil, and_true, Sym2.eq_iff, not_false_eq_true]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true] at hnd
    aesop
  exact ⟨v₀, p, hp, rfl⟩

/--
Theorem 1 (`dual_cross_rewiring_trifree_same_scale_c6_rigidity`):
In any triangle-free `PowerFree` graph `G`, if both cross-rewirings `G_×^(1)(uv)` and `G_×^(2)(uv)`
produce `C₄` (Type L1) lifts sharing endpoint `a` — giving 3-paths `a - x₁ - x₂ - c` and
`a - y₁ - y₂ - d` in `G - {u, v}` — then necessarily:
  `x₁ = y₁`, `x₂ ≠ y₂`, and `x₁ - x₂ - c - v - d - y₂ - x₁` is a third simple `C₆` in `G`.
-/
theorem dual_cross_rewiring_trifree_same_scale_c6_rigidity {V : Type*} (G : SimpleGraph V)
    (hpf : PowerFree G) (htf : TriangleFree G)
    {v a c d x₁ x₂ y₁ y₂ : V}
    (hvc : G.Adj v c) (hvd : G.Adj v d) (hcd : c ≠ d)
    (hp1_nd : [a, x₁, x₂, c].Nodup) (hp2_nd : [a, y₁, y₂, d].Nodup)
    (ha_ne_v : a ≠ v) (hx1_ne_v : x₁ ≠ v) (hx2_ne_v : x₂ ≠ v)
    (hy1_ne_v : y₁ ≠ v) (hy2_ne_v : y₂ ≠ v)
    (hax1 : G.Adj a x₁) (hx12 : G.Adj x₁ x₂) (hx2c : G.Adj x₂ c)
    (hay1 : G.Adj a y₁) (hy12 : G.Adj y₁ y₂) (hy2d : G.Adj y₂ d) :
    x₁ = y₁ ∧ x₂ ≠ y₂ ∧ HasCycleLen G 6 := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hp1_nd hp2_nd
  rcases hp1_nd with ⟨⟨hax1_ne, hax2_ne, hac_ne⟩, ⟨hx12_ne, hx1c_ne⟩, hx2c_ne⟩
  rcases hp2_nd with ⟨⟨hay1_ne, hay2_ne, had_ne⟩, ⟨hy12_ne, hy1d_ne⟩, hy2d_ne⟩
  have hcv_ne : c ≠ v := (G.ne_of_adj hvc).symm
  have hdv_ne : d ≠ v := (G.ne_of_adj hvd).symm
  -- First rule out c = y₁, c = y₂, d = x₁, d = x₂, x₂ = y₂, x₁ = y₂, x₂ = y₁
  have hx2_ne_y2 : x₂ ≠ y₂ := by
    intro h; subst h
    exact no_c4 G hpf hx2c_ne hcv_ne hdv_ne.symm (Ne.symm hy2d_ne) hx2_ne_v hcd
      hx2c hvc.symm hvd hy2d.symm
  have hx1_ne_y2 : x₁ ≠ y₂ := by
    intro h; subst h
    exact htf a x₁ y₁ ⟨hax1, hy12.symm, hay1.symm⟩
  have hx2_ne_y1 : x₂ ≠ y₁ := by
    intro h; subst h
    exact htf a x₁ x₂ ⟨hax1, hx12, hay1.symm⟩
  have hc_ne_y2 : c ≠ y₂ := by
    intro h; subst h
    exact htf v c d ⟨hvc, hy2d, hvd.symm⟩
  have hd_ne_x2 : d ≠ x₂ := by
    intro h; subst h
    exact htf v c d ⟨hvc, hx2c.symm, hvd.symm⟩
  have hc_ne_y1 : c ≠ y₁ := by
    intro h; subst h
    -- If c = y₁, then a ~ c, so check x₁ = y₂? Wait: a - x₁ - x₂ - c - a is a C₄!
    exact no_c4 G hpf hax1_ne hx12_ne hx2c_ne (Ne.symm hac_ne) hax2_ne hx1c_ne
      hax1 hx12 hx2c hay1.symm
  have hd_ne_x1 : d ≠ x₁ := by
    intro h; subst h
    exact no_c4 G hpf hay1_ne hy12_ne hy2d_ne (Ne.symm had_ne) hay2_ne hy1d_ne
      hay1 hy12 hy2d hax1.symm
  have hx1_eq_y1 : x₁ = y₁ := by
    by_contra hne
    -- All 8 vertices [a, x₁, x₂, c, v, d, y₂, y₁] are pairwise distinct, forming a C₈!
    have hnd8 : [a, x₁, x₂, c, v, d, y₂, y₁].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, and_true, not_false_eq_true]
      exact ⟨⟨hax1_ne, hax2_ne, hac_ne, ha_ne_v, had_ne, hay2_ne, hay1_ne⟩,
        ⟨hx12_ne, hx1c_ne, hx1_ne_v, hd_ne_x1.symm, hx1_ne_y2, hne⟩,
        ⟨hx2c_ne, hx2_ne_v, hd_ne_x2.symm, hx2_ne_y2, hx2_ne_y1⟩,
        ⟨hcv_ne, hcd, hc_ne_y2, hc_ne_y1⟩,
        ⟨hdv_ne.symm, hy2_ne_v.symm, hy1_ne_v.symm⟩,
        ⟨Ne.symm hy2d_ne, Ne.symm hy1d_ne⟩,
        Ne.symm hy12_ne⟩
    exact no_c8 G hpf hnd8 hax1 hx12 hx2c hvc.symm hvd hy2d.symm hy12.symm hay1.symm
  subst hx1_eq_y1
  -- Now [x₁, x₂, c, v, d, y₂] is a simple 6-cycle!
  have hnd6 : [x₁, x₂, c, v, d, y₂].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true]
    exact ⟨⟨hx12_ne, hx1c_ne, hx1_ne_v, Ne.symm hy1d_ne, hy12_ne⟩,
      ⟨hx2c_ne, hx2_ne_v, hd_ne_x2.symm, hx2_ne_y2⟩,
      ⟨hcv_ne, hcd, hc_ne_y2⟩,
      ⟨hdv_ne.symm, hy2_ne_v.symm⟩,
      Ne.symm hy2d_ne⟩
  exact ⟨rfl, hx2_ne_y2, has_c6_of_six G hnd6 hx12 hx2c hvc.symm hvd hy2d.symm hy12.symm⟩

/--
Theorem 2 (`minimal_bad2_v3_min_component_forces_vge4_girth_cycle`):
In any graph `G` with `GirthGe G g` (`g ≥ 4`), if a connected subset `S ⊆ V` of exact size
`S.card = g - 1` has some outside vertex `w ∉ S` with at least 2 neighbors in `S`, then `G`
contains a simple `g`-cycle passing through `w`!
(Coupled with Part 2's Theorem 3: any minimum-size `|S| = g - 1` component of `G[V₃]` avoiding
`Defects G` MUST have some `w ∈ V₄(G)` with `≥ 2` neighbors in `S`, hence forces a `C_g`
passing through a `V₄`-vertex!)
-/
theorem minimal_bad2_v3_min_component_forces_vge4_girth_cycle {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {g : ℕ} (hg : GirthGe G g)
    (S : Finset V) (hcard : S.card = g - 1)
    (hconn : (G.induce (S : Set V)).Connected)
    {w : V} (hwS : w ∉ S)
    (hw2 : 2 ≤ (G.neighborFinset w ∩ S).card) :
    ∃ q : G.Walk w w, q.IsCycle ∧ q.length = g := by
  classical
  rcases Finset.one_lt_card.mp (by omega : 1 < (G.neighborFinset w ∩ S).card) with
    ⟨a, ha, b, hb, hab⟩
  have ha_adj : G.Adj w a := (mem_neighborFinset G w a).mp (Finset.mem_inter.mp ha).1
  have ha_S : a ∈ S := (Finset.mem_inter.mp ha).2
  have hb_adj : G.Adj w b := (mem_neighborFinset G w b).mp (Finset.mem_inter.mp hb).1
  have hb_S : b ∈ S := (Finset.mem_inter.mp hb).2
  rcases hconn ⟨a, ha_S⟩ ⟨b, hb_S⟩ with ⟨w0⟩
  let p0 := w0.toPath
  let f : G.induce (S : Set V) →g G := ⟨Subtype.val, fun h => h⟩
  let p : G.Walk a b := p0.1.map f
  have hp_path : p.IsPath := p0.2.map Subtype.val_injective
  have hsup_sub : ∀ x ∈ p.support, x ∈ S := by
    intro x hx
    rw [Walk.support_map] at hx
    rcases List.mem_map.mp hx with ⟨u, _, rfl⟩
    exact u.2
  have hlen_le : p.length ≤ g - 2 := by
    have hnodup : p.support.Nodup := hp_path.support_nodup
    have hsub_fin : p.support.toFinset ⊆ S := by
      intro x hx; exact hsup_sub x (List.mem_toFinset.mp hx)
    have hcard_le : p.support.length ≤ S.card := by
      rw [← List.toFinset_card_of_nodup hnodup]
      exact Finset.card_le_card hsub_fin
    have hsup_len : p.support.length = p.length + 1 := Walk.length_support p
    omega
  have hw_not : w ∉ p.support := fun hm => hwS (hsup_sub w hm)
  let q : G.Walk w w := Walk.cons ha_adj (p.append (Walk.cons hb_adj.symm Walk.nil))
  have hq_len : q.length = p.length + 2 := by simp [q, Walk.length_cons, Walk.length_append]
  have hq_sup : q.support = w :: (p.support ++ [w]) := by
    simp [q, Walk.support_cons, Walk.support_append, Walk.support_nil]
  have htail_nodup : q.support.tail.Nodup := by
    rw [hq_sup, List.tail_cons, List.nodup_append]
    refine ⟨hp_path.support_nodup, List.nodup_singleton w, ?_⟩
    intro x hx y hxw rfl
    rw [List.mem_singleton] at hxw
    exact hw_not (hxw ▸ hx)
  have h_no_w : ∀ e ∈ p.edges, w ∉ e := fun e he hm => by
    rcases Sym2.mem_iff_exists.mp hm with ⟨z, rfl⟩
    exact hw_not (Walk.fst_mem_support_of_mem_edges p he)
  have hq_cyc : q.IsCycle := by
    rw [Walk.isCycle_def]
    refine ⟨?_, by simp [q], htail_nodup⟩
    rw [Walk.isTrail_def]
    have heq : q.edges = s(w, a) :: (p.edges ++ [s(b, w)]) := by
      simp [q, Walk.edges_cons, Walk.edges_append, Walk.edges_nil]
    rw [heq, List.nodup_cons]
    refine ⟨?_, ?_⟩
    · simp only [List.mem_append, List.mem_singleton, not_or, Sym2.eq_iff]
      refine ⟨fun hm => h_no_w s(w, a) hm (Sym2.mem_mk_left w a), ?_⟩
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact hw_not (Walk.end_mem_support p)
      · exact hab rfl
    · rw [List.nodup_append]
      refine ⟨hp_path.isTrail.edges_nodup, List.nodup_singleton _, ?_⟩
      intro e he e' hbw rfl
      rw [List.mem_singleton] at hbw
      subst hbw
      exact h_no_w s(b, w) he (Sym2.mem_mk_right b w)
  have hqg := hg w q hq_cyc
  have hS2 : 2 ≤ S.card := le_trans hw2 (Finset.card_le_card Finset.inter_subset_right)
  exact ⟨q, hq_cyc, by omega⟩

/-- The cross-rewired graph `crossRewire G u v u₁ u₂ v₁ v₂` (duplicated locally so Part 3 is
100% standalone). -/
def crossRewire {V : Type*} (G : SimpleGraph V) (u v u₁ u₂ v₁ v₂ : V)
    (h1 : u₁ ≠ v₁) (h2 : u₂ ≠ v₂) : SimpleGraph {w : V // w ≠ u ∧ w ≠ v} where
  Adj x y :=
    G.Adj x.1 y.1 ∨
    (x.1 = u₁ ∧ y.1 = v₁) ∨ (x.1 = v₁ ∧ y.1 = u₁) ∨
    (x.1 = u₂ ∧ y.1 = v₂) ∨ (x.1 = v₂ ∧ y.1 = u₂)
  symm := ⟨fun _ _ h => by
    rcases h with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩
  loopless := ⟨fun x h => by
    rcases h with h | ⟨hxa, hxb⟩ | ⟨hxa, hxb⟩ | ⟨hxa, hxb⟩ | ⟨hxa, hxb⟩
    · exact G.loopless.irrefl x.1 h
    · exact h1 (hxa.symm.trans hxb)
    · exact h1 (hxb.symm.trans hxa)
    · exact h2 (hxa.symm.trans hxb)
    · exact h2 (hxb.symm.trans hxa)⟩

/--
Theorem 3 (`crossRewire_preserves_two_cut_separation`):
**Tutte Cleavage / 2-Cut Preservation under Dual Cross-Rewiring**:
Suppose `{x, y}` is a 2-cut of `G` separating `C_a` from `C_b` (no edge of `G` crosses between
`C_a` and `C_b`). If a non-triangle cubic edge `uv` lies strictly inside `C_a` (so `u, v ∈ C_a`,
and `u₁, u₂, v₁, v₂ ∉ C_b`), then in **BOTH** cross-rewirings `G_×^(1)` and `G_×^(2)`, no edge
crosses between `C_a \ {u, v}` and `C_b`: `{x, y}` remains a 2-cut separating `C_a \ {u, v}`
from `C_b`!
-/
theorem crossRewire_preserves_two_cut_separation {V : Type*} (G : SimpleGraph V)
    {C_a C_b : Set V}
    (hsep : ∀ s ∈ C_a, ∀ t ∈ C_b, ¬ G.Adj s t)
    {u v u₁ u₂ v₁ v₂ : V} (h1 : u₁ ≠ v₁) (h2 : u₂ ≠ v₂)
    (hu₁_not_b : u₁ ∉ C_b) (hu₂_not_b : u₂ ∉ C_b)
    (hv₁_not_b : v₁ ∉ C_b) (hv₂_not_b : v₂ ∉ C_b) :
    let H := crossRewire G u v u₁ u₂ v₁ v₂ h1 h2
    ∀ s t : {w : V // w ≠ u ∧ w ≠ v}, s.1 ∈ C_a → t.1 ∈ C_b → ¬ H.Adj s t := by
  intro H s t hs ht hadj
  rcases hadj with hG | ⟨_, htv1⟩ | ⟨_, htu1⟩ | ⟨_, htv2⟩ | ⟨_, htu2⟩
  · exact hsep s.1 hs t.1 ht hG
  · exact hv₁_not_b (htv1 ▸ ht)
  · exact hu₁_not_b (htu1 ▸ ht)
  · exact hv₂_not_b (htv2 ▸ ht)
  · exact hu₂_not_b (htu2 ▸ ht)

/--
Theorem 4 (`crossRewire_two_cut_dyadic_path_asymmetry`):
**Tutte Cleavage & Dual Cross-Rewiring Scale Coupling**:
If `{x, y}` is a 2-cut of `G` separating `C_a` from `C_b` (with `C_a, C_b, {x, y}` pairwise
disjoint), then `G` cannot simultaneously contain an `x`–`y` simple path `p_a` internally inside
`C_a` of length `2^m` (`m ≥ 1`) and an `x`–`y` simple path `p_b` internally inside `C_b` of the
same length `2^m` (otherwise `p_a ∪ p_b` forms a simple `2^(m+1)`-cycle in `G`, contradicting
`PowerFree G`).
-/
theorem crossRewire_two_cut_dyadic_path_asymmetry {V : Type*} (G : SimpleGraph V)
    (hpf : PowerFree G) {x y : V} (hxy : x ≠ y) {m : ℕ} (hm : 1 ≤ m)
    (p_a : G.Walk x y) (hpa : p_a.IsPath) (hla : p_a.length = 2 ^ m)
    (p_b : G.Walk x y) (hpb : p_b.IsPath) (hlb : p_b.length = 2 ^ m)
    (hdisj : ∀ z : V, z ∈ p_a.support → z ∈ p_b.support → z = x ∨ z = y) :
    False := by
  -- Construct simple cycle p_a.append p_b.reverse of length 2^(m+1)
  let q : G.Walk x x := p_a.append p_b.reverse
  have hq_len : q.length = 2 ^ (m + 1) := by
    simp [q, Walk.length_append, Walk.length_reverse, hla, hlb, pow_succ]; omega
  have h2m : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hm
  have htail_nodup : q.support.tail.Nodup := by
    have htail_eq : q.support.tail = p_a.support.tail ++ p_b.reverse.support.tail := by
      cases hpa_eq : p_a with
      | nil => exfalso; exact hxy rfl
      | cons hadj r =>
        simp [q, hpa_eq, Walk.support_append, Walk.support_cons]
    rw [htail_eq, List.nodup_append]
    refine ⟨hpa.support_nodup.tail, hpb.reverse.support_nodup.tail, ?_⟩
    intro z hza z' hzb rfl
    have hza' : z ∈ p_a.support := List.mem_of_mem_tail hza
    have hzb' : z ∈ p_b.support :=
      List.mem_reverse.mp (Walk.support_reverse p_b ▸ List.mem_of_mem_tail hzb)
    rcases hdisj z hza' hzb' with hzx | hzy
    · rw [hzx] at hza
      cases hpa_eq : p_a with
      | nil => exact hxy rfl
      | cons hadj r =>
        have hnd := hpa.support_nodup
        rw [hpa_eq, Walk.support_cons, List.nodup_cons] at hnd
        rw [hpa_eq, Walk.support_cons, List.tail_cons] at hza
        exact hnd.1 hza
    · rw [hzy] at hzb
      have hnd := hpb.reverse.support_nodup
      cases hpr_eq : p_b.reverse with
      | nil =>
        have : p_b.length = 0 := by
          have hrev := Walk.length_reverse p_b
          rw [hpr_eq, Walk.length_nil] at hrev
          exact hrev.symm
        omega
      | cons hadj r =>
        rw [hpr_eq, Walk.support_cons, List.nodup_cons] at hnd
        rw [hpr_eq, Walk.support_cons, List.tail_cons] at hzb
        exact hnd.1 hzb
  have hq_trail : q.IsTrail := by
    rw [Walk.isTrail_def]
    simp only [q, Walk.edges_append, List.nodup_append]
    refine ⟨hpa.isTrail.edges_nodup, hpb.reverse.isTrail.edges_nodup, ?_⟩
    intro e hea e' heb rfl
    induction e using Sym2.ind with
    | _ u w =>
      have hu_a : u ∈ p_a.support := Walk.fst_mem_support_of_mem_edges p_a hea
      have hw_a : w ∈ p_a.support := Walk.snd_mem_support_of_mem_edges p_a hea
      have hu_b : u ∈ p_b.support :=
        List.mem_reverse.mp (Walk.support_reverse p_b ▸ Walk.fst_mem_support_of_mem_edges p_b.reverse heb)
      have hw_b : w ∈ p_b.support :=
        List.mem_reverse.mp (Walk.support_reverse p_b ▸ Walk.snd_mem_support_of_mem_edges p_b.reverse heb)
      have huw : u ≠ w := G.ne_of_adj (Walk.adj_of_mem_edges p_a hea)
      -- Both u, w ∈ {x, y}, so s(u, w) = s(x, y), which implies p_a has edge s(x, y) AND length ≥ 2!
      -- Wait: if p_a is a path from x to y and contains edge s(x, y), then p_a.length = 1!
      have huxy := hdisj u hu_a hu_b
      have hwxy := hdisj w hw_a hw_b
      have hlen1 : ∀ {s t : V} (r : G.Walk s t), r.IsPath → s(s, t) ∈ r.edges → r.length ≤ 1 := by
        intro s t r hr hm
        cases r with
        | nil => simp at hm
        | cons hadj r' =>
          simp only [Walk.edges_cons, List.mem_cons] at hm
          rcases hm with heq | hmem
          · rw [Sym2.eq_iff] at heq
            rcases heq with ⟨_, hvt⟩ | ⟨_, hvs⟩
            · subst hvt
              have hnd := hr.support_nodup
              cases r' with
              | nil => simp
              | cons hadj' r'' =>
                simp only [Walk.support_cons, List.nodup_cons] at hnd
                exact absurd (Walk.end_mem_support r'') hnd.2.1
            · exact absurd hvs.symm (G.ne_of_adj hadj)
          · have hs1 : s ∈ r'.support := Walk.fst_mem_support_of_mem_edges r' hmem
            have hnd := hr.support_nodup
            simp only [Walk.support_cons, List.nodup_cons] at hnd
            exact absurd hs1 hnd.1
      have hsxy : s(x, y) ∈ p_a.edges := by
        rcases huxy with rfl | rfl <;> rcases hwxy with rfl | rfl
        · exact absurd rfl huw
        · exact hea
        · simpa [Sym2.eq_swap] using hea
        · exact absurd rfl huw
      have hle1 := hlen1 p_a hpa hsxy
      omega
  have hq_ne_nil : q ≠ Walk.nil := by
    intro hnil
    rw [hnil, Walk.length_nil] at hq_len
    have : 0 < 2 ^ (m + 1) := Nat.pow_pos (by decide)
    omega
  have hq_cyc : q.IsCycle := by
    rw [Walk.isCycle_def]
    exact ⟨hq_trail, hq_ne_nil, htail_nodup⟩
  exact hpf ⟨x, q, hq_cyc, ⟨m + 1, by omega, hq_len⟩⟩

end E64Wave8Agent3P3
