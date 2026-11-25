import Core
import Leaves
import PairedShadow
import Identification

/-!
Erdos 64 (Wave 3, Agent #4):
1. Two-Cut Cross-Side Dyadic Coupling Theorem (covers all 6 `*-2` leaves:
   C-T-2, C-N-2, S-T-2, S-N-2, H-T-2, H-N-2).
2. C5 Single-Edge Disjointness Theorem (no two 5-cycles in a C8-free / MinimalBad
   graph can share exactly one edge and no other vertices).
-/

namespace E64TwoCutC5
open SimpleGraph Erdos64Closure E64Core E64Leaves Erdos64Paired E64Identification
universe u

variable {V : Type u}

/-- Helper: any walk in `G` from `x ∈ A` to `y ∉ A` crosses the cut `(A, Aᶜ)` at some first edge
    `u - v` with `u ∈ A`, `v ∉ A`, such that the prefix stays inside `A`. -/
lemma walk_first_cut_edge {G : SimpleGraph V} (A : Set V) [DecidablePred (· ∈ A)]
    {x y : V} (hx : x ∈ A) (hy : y ∉ A) (p : G.Walk x y) :
    ∃ (u v : V) (huv : G.Adj u v) (p₁ : G.Walk x u) (p₂ : G.Walk v y),
      u ∈ A ∧ v ∉ A ∧
      p = p₁.append (.cons huv p₂) ∧
      (∀ z ∈ p₁.support, z ∈ A) := by
  induction p with
  | nil => exact False.elim (hy hx)
  | @cons a b c hab q ih =>
    by_cases hb : b ∈ A
    · obtain ⟨u, v, huv, p₁, p₂, huA, hvA, hq, hstay⟩ := ih hb hy
      refine ⟨u, v, huv, .cons hab p₁, p₂, huA, hvA, ?_, ?_⟩
      · rw [hq]; rfl
      · intro z hz
        simp only [Walk.support_cons, List.mem_cons] at hz
        rcases hz with rfl | hz'
        · exact hx
        · exact hstay z hz'
    · exact ⟨a, b, hab, .nil, q, hx, hb, rfl, fun z hz => by simp at hz; subst hz; exact hx⟩

/-- Helper: if a path `p : G.Walk x y` crosses a 2-edge cut `{a₁b₁, a₂b₂}` from `A` to `Aᶜ`
    at `a₁b₁`, and `a₂` is NOT used after crossing, wait: if `p` ever re-entered `A` after crossing
    `a₁b₁`, it would have to cross back into `A` via `a₂b₂` and then could NEVER leave `A` again
    to reach `y ∉ A` without reusing a port! Hence `p` stays strictly outside `A` after crossing! -/
lemma path_single_crossing_two_cut {G : SimpleGraph V} (A : Set V) [DecidablePred (· ∈ A)]
    {a₁ a₂ b₁ b₂ : V}
    (hcut : ∀ u v, u ∈ A → v ∉ A → G.Adj u v → (u = a₁ ∧ v = b₁) ∨ (u = a₂ ∧ v = b₂))
    {x y : V} (hx : x ∈ A) (hy : y ∉ A) (p : G.Walk x y) (hp : p.IsPath) :
    ∃ (k_idx : Bool) (pA : G.Walk x (if k_idx then a₁ else a₂))
      (pB : G.Walk (if k_idx then b₁ else b₂) y),
      pA.IsPath ∧ pB.IsPath ∧
      (∀ z ∈ pA.support, z ∈ A) ∧
      (∀ z ∈ pB.support, z ∉ A) ∧
      pA.length + pB.length + 1 = p.length := by
  obtain ⟨u, v, huv, p₁, p₂, huA, hvA, hpeq, hstay1⟩ := walk_first_cut_edge A hx hy p
  have hp_nodup : p.support.Nodup := hp.support_nodup
  rw [hpeq, Walk.support_append, Walk.support_cons, List.tail_cons] at hp_nodup
  have hp₁_nodup : p₁.support.Nodup := (List.nodup_append'.mp hp_nodup).1
  have hp₂_nodup : p₂.support.Nodup := (List.nodup_append'.mp hp_nodup).2.1
  have hdisj : p₁.support.Disjoint p₂.support := (List.nodup_append'.mp hp_nodup).2.2
  have hu_in_p₁ : u ∈ p₁.support := Walk.end_mem_support p₁
  have hv_in_p₂ : v ∈ p₂.support := Walk.start_mem_support p₂
  have hstay2 : ∀ z ∈ p₂.support, z ∉ A := by
    -- Suppose p₂ enters A at some vertex z ∈ A. Then p₂ must cross from Aᶜ to A at some edge
    -- (v', u') with v' ∉ A, u' ∈ A, and then LATER cross back from A to Aᶜ to reach y ∉ A!
    -- Both crossings must use edges in {a₁b₁, a₂b₂}, so one of them reuses u (contradicting hdisj)
    -- or reuses the same edge (contradicting hp₂_nodup)!
    intro z hz hzA
    -- Split p₂ at z into q₁ : v -> z and q₂ : z -> y
    let q₁ := p₂.takeUntil z hz
    let q₂ := p₂.dropUntil z hz
    have hq_eq : p₂ = q₁.append q₂ := (Walk.take_spec p₂ hz).symm
    -- q₁ goes from v ∉ A to z ∈ A, so q₁.reverse goes from z ∈ A to v ∉ A
    obtain ⟨u', v', huv', r₁, r₂, hu'A, hv'A, hq1r, _⟩ := walk_first_cut_edge A hzA hvA q₁.reverse
    -- q₂ goes from z ∈ A to y ∉ A
    obtain ⟨u'', v'', huv'', s₁, s₂, hu''A, hv''A, hq2, _⟩ := walk_first_cut_edge A hzA hy q₂
    have hu'_in_q₁ : u' ∈ q₁.support := by
      have : u' ∈ q₁.reverse.support := by
        rw [hq1r, Walk.support_append]; exact List.mem_append_left _ (Walk.end_mem_support r₁)
      rwa [Walk.support_reverse, List.mem_reverse] at this
    have hu''_in_q₂ : u'' ∈ q₂.support := by
      rw [hq2, Walk.support_append]; exact List.mem_append_left _ (Walk.end_mem_support s₁)
    have hv''_in_q₂ : v'' ∈ q₂.support := by
      rw [hq2, Walk.support_append, Walk.support_cons, List.tail_cons]
      exact List.mem_append_right _ (Walk.start_mem_support s₂)
    have hv'_in_q₁ : v' ∈ q₁.support := by
      have : v' ∈ q₁.reverse.support := by
        rw [hq1r, Walk.support_append, Walk.support_cons, List.tail_cons]
        exact List.mem_append_right _ (Walk.start_mem_support r₂)
      rwa [Walk.support_reverse, List.mem_reverse] at this
    -- Notice v' ∉ A and v'' ∉ A, and q₁.support ++ q₂.support.tail = p₂.support is Nodup!
    have hq12_nodup : (q₁.support ++ q₂.support.tail).Nodup := by
      rwa [hq_eq, Walk.support_append] at hp₂_nodup
    have hv''_in_q₂t : v'' ∈ q₂.support.tail := by
      have hne_z : v'' ≠ z := fun h => hv''A (h ▸ hzA)
      have hqs : q₂.support = z :: q₂.support.tail := (q₂.cons_tail_support).symm
      rw [hqs, List.mem_cons] at hv''_in_q₂
      exact hv''_in_q₂.resolve_left hne_z
    have hv'_ne_v'' : v' ≠ v'' := fun h =>
      (List.nodup_append'.mp hq12_nodup).2.2 hv'_in_q₁ (h ▸ hv''_in_q₂t)
    have hu'_in_p₂ : u' ∈ p₂.support := by
      rw [hq_eq, Walk.support_append]; exact List.mem_append_left _ hu'_in_q₁
    have hu''_in_p₂ : u'' ∈ p₂.support := by
      rw [hq_eq, Walk.support_append]
      by_cases hzu'' : u'' = z
      · subst hzu''; exact List.mem_append_left _ (Walk.end_mem_support q₁)
      · have hqs : q₂.support = z :: q₂.support.tail := (q₂.cons_tail_support).symm
        rw [hqs, List.mem_cons] at hu''_in_q₂
        exact List.mem_append_right _ (hu''_in_q₂.resolve_left hzu'')
    have hu_ne_u' : u ≠ u' := fun h => hdisj hu_in_p₁ (h ▸ hu'_in_p₂)
    have hu_ne_u'' : u ≠ u'' := fun h => hdisj hu_in_p₁ (h ▸ hu''_in_p₂)
    rcases hcut u v huA hvA huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases hcut u' v' hu'A hv'A huv' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hu_ne_u' rfl
      · rcases hcut u'' v'' hu''A hv''A huv'' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hu_ne_u'' rfl
        · exact hv'_ne_v'' rfl
    · rcases hcut u' v' hu'A hv'A huv' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases hcut u'' v'' hu''A hv''A huv'' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hv'_ne_v'' rfl
        · exact hu_ne_u'' rfl
      · exact hu_ne_u' rfl
  have hlen_eq : p₁.length + p₂.length + 1 = p.length := by
    rw [hpeq, Walk.length_append, Walk.length_cons]; omega
  rcases hcut u v huA hvA huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨true, p₁, p₂, Walk.IsPath.mk' hp₁_nodup, Walk.IsPath.mk' hp₂_nodup, hstay1, hstay2, hlen_eq⟩
  · exact ⟨false, p₁, p₂, Walk.IsPath.mk' hp₁_nodup, Walk.IsPath.mk' hp₂_nodup, hstay1, hstay2, hlen_eq⟩

/-- NEW (Wave 3, Agent #4): 2-Cut Cross-Side Dyadic Coupling Theorem.
    In ANY `MinimalBad(G)` with a matching 2-edge cut `E(A, Aᶜ) = {a₁b₁, a₂b₂}`
    (covering all 6 `*-2` open leaves: C-T-2, C-N-2, S-T-2, S-N-2, H-T-2, H-N-2),
    for EVERY interior vertex `x ∈ A \ {a₁, a₂}` and EVERY interior vertex `y ∈ Aᶜ \ {b₁, b₂}`,
    there exists `k ≥ 2` and internal simple paths `pA` (from `x` to `aᵢ` in `A`) and `pB`
    (from `bᵢ` to `y` in `Aᶜ`) with `pA.length + pB.length + 1 = 2^k`. -/
theorem two_cut_cross_side_dyadic_coupling [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (A : Set V) [DecidablePred (· ∈ A)]
    {a₁ a₂ b₁ b₂ : V}
    (hcut : ∀ u v, u ∈ A → v ∉ A → G.Adj u v → (u = a₁ ∧ v = b₁) ∨ (u = a₂ ∧ v = b₂))
    {x y : V} (hx : x ∈ A) (hxa₁ : x ≠ a₁) (hxa₂ : x ≠ a₂)
    (hy : y ∉ A) (hyb₁ : y ≠ b₁) (hyb₂ : y ≠ b₂) :
    ∃ (k : ℕ) (idx : Bool) (pA : G.Walk x (if idx then a₁ else a₂))
      (pB : G.Walk (if idx then b₁ else b₂) y),
      2 ≤ k ∧ pA.IsPath ∧ pB.IsPath ∧
      (∀ z ∈ pA.support, z ∈ A) ∧ (∀ z ∈ pB.support, z ∉ A) ∧
      pA.length + pB.length + 1 = 2 ^ k := by
  have hxy : x ≠ y := fun h => hy (h ▸ hx)
  have hnadj : ¬ G.Adj x y := by
    intro h
    rcases hcut x y hx hy h with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact hxa₁ rfl
    · exact hxa₂ rfl
  have hnocom : ∀ z, ¬ (G.Adj x z ∧ G.Adj y z) := by
    rintro z ⟨hxz, hyz⟩
    by_cases hz : z ∈ A
    · rcases hcut z y hz hy hyz.symm with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact hyb₁ rfl
      · exact hyb₂ rfl
    · rcases hcut x z hx hz hxz with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact hxa₁ rfl
      · exact hxa₂ rfl
  obtain ⟨k, p, hk, hp, hplen⟩ := dyadic_path_of_dist_ge_three G hm hxy hnadj hnocom
  obtain ⟨idx, pA, pB, hpA, hpB, hstA, hstB, hlen⟩ :=
    path_single_crossing_two_cut A hcut hx hy p hp
  exact ⟨k, idx, pA, pB, hk, hpA, hpB, hstA, hstB, hlen.trans hplen⟩

/-- NEW (Wave 3, Agent #4): C5 Single-Edge Disjointness Theorem.
    In ANY power-free (hence any `MinimalBad`) graph, two 5-cycles cannot intersect
    in exactly one shared edge `{u, v}` (their symmetric difference is a simple `C8`). -/
theorem no_two_c5_share_single_edge {G : SimpleGraph V} (hfree : ¬ HasPower G)
    {u v a₁ a₂ a₃ b₁ b₂ b₃ : V}
    (hdist : [u, v, a₁, a₂, a₃, b₁, b₂, b₃].Nodup)
    (h1 : G.Adj u a₁) (h2 : G.Adj a₁ a₂) (h3 : G.Adj a₂ a₃) (h4 : G.Adj a₃ v)
    (h5 : G.Adj v b₁) (h6 : G.Adj b₁ b₂) (h7 : G.Adj b₂ b₃) (h8 : G.Adj b₃ u) :
    False := by
  let c : G.Walk u u :=
    .cons h1 (.cons h2 (.cons h3 (.cons h4 (.cons h5 (.cons h6 (.cons h7 (.cons h8 .nil)))))))
  have hlen : c.length = 2 ^ 3 := rfl
  have htail : c.support.tail = [a₁, a₂, a₃, v, b₁, b₂, b₃, u] := rfl
  have hnod : c.support.tail.Nodup := by
    rw [htail]
    -- Permutation of [u, v, a1, a2, a3, b1, b2, b3]
    have hperm : [u, v, a₁, a₂, a₃, b₁, b₂, b₃].Perm [a₁, a₂, a₃, v, b₁, b₂, b₃, u] := by
      have p1 : [u, v, a₁, a₂, a₃, b₁, b₂, b₃].Perm ([v, a₁, a₂, a₃, b₁, b₂, b₃] ++ [u]) := by
        simpa using (List.perm_append_singleton u [v, a₁, a₂, a₃, b₁, b₂, b₃]).symm
      have p2 : [v, a₁, a₂, a₃, b₁, b₂, b₃].Perm [a₁, a₂, a₃, v, b₁, b₂, b₃] := by
        calc [v, a₁, a₂, a₃, b₁, b₂, b₃]
            ~ [a₁, v, a₂, a₃, b₁, b₂, b₃] := List.Perm.swap _ _ _
          _ ~ [a₁, a₂, v, a₃, b₁, b₂, b₃] := List.Perm.cons _ (List.Perm.swap _ _ _)
          _ ~ [a₁, a₂, a₃, v, b₁, b₂, b₃] := List.Perm.cons _ (List.Perm.cons _ (List.Perm.swap _ _ _))
      exact p1.trans (by simpa using p2.append_right [u])
    exact (List.Perm.nodup_iff hperm).mp hdist
  have hcyc : c.IsCycle := by
    apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    refine ⟨Walk.IsPath.mk' hnod, by decide⟩
  exact hfree ⟨3, u, c, by decide, hcyc, hlen⟩

#print axioms two_cut_cross_side_dyadic_coupling
#print axioms no_two_c5_share_single_edge

end E64TwoCutC5
