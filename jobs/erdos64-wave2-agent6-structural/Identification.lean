import Core
import Leaves
import PairedShadow

/-!
Erdos 64 (Wave 2, Agent #6): Unified Vertex-Identification & Edge-Contraction Engine.
Proves (unconditionally, all finite orders, standard axioms only):
1. Universal Dyadic Path Theorem (dist >= 3) & 6-line unified bipartite exclusion.
2. Extended Distance-2 Dyadic Path Theorem (cubic, high-degree hub, or defect endpoint).
3. Cubic All-Non-Edge Dyadic Path Theorem (every non-adjacent pair has a 2^k-path).
4. Universal Fermat-Edge Cycle Theorem (every non-triangle edge, and every edge in cubic
   MinimalBad, lies on a simple (2^k + 1)-cycle, k >= 2).
5. Bridgelessness (every edge of MinimalBad lies on a simple cycle).
-/

namespace E64Identification
open SimpleGraph Erdos64Closure E64Core E64Leaves Erdos64Paired
universe u

variable {V : Type u}

/-- Identify y into x in G (deleting y and redirecting y's incident edges to x).
    When ¬G.Adj x y, this is vertex identification G/(x=y);
    when G.Adj x y, this is simple edge contraction G/xy. -/
def identify (G : SimpleGraph V) (x y : V) : SimpleGraph {v : V // v ≠ y} where
  Adj u v := u ≠ v ∧
    (G.Adj u.1 v.1 ∨ (u.1 = x ∧ G.Adj y v.1) ∨ (v.1 = x ∧ G.Adj u.1 y))
  symm := ⟨by
    rintro u v ⟨hne, h | ⟨hux, hyv⟩ | ⟨hvx, huy⟩⟩
    · exact ⟨hne.symm, Or.inl h.symm⟩
    · exact ⟨hne.symm, Or.inr (Or.inr ⟨hux, hyv.symm⟩)⟩
    · exact ⟨hne.symm, Or.inr (Or.inl ⟨hvx, huy.symm⟩)⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

/-- Lift a walk in `identify G x y` that avoids the merged vertex `x` back to `G`. -/
def liftAvoid {G : SimpleGraph V} {x y : V}
    {a b : {v : V // v ≠ y}} (p : (identify G x y).Walk a b)
    (havoid : ∀ v ∈ p.support, v.1 ≠ x) : G.Walk a.1 b.1 :=
  match p with
  | .nil => .nil
  | @Walk.cons _ _ u v w huv q =>
    have hu : u.1 ≠ x := havoid u (by simp)
    have hv : v.1 ≠ x := havoid v (by simp)
    have hedge : G.Adj u.1 v.1 := by
      rcases huv.2 with h | ⟨hux, _⟩ | ⟨hvx, _⟩
      · exact h
      · exact False.elim (hu hux)
      · exact False.elim (hv hvx)
    .cons hedge (liftAvoid q (fun z hz => havoid z (by simp [hz])))

theorem length_liftAvoid {G : SimpleGraph V} {x y : V}
    {a b : {v : V // v ≠ y}} (p : (identify G x y).Walk a b)
    (havoid : ∀ v ∈ p.support, v.1 ≠ x) :
    (liftAvoid p havoid).length = p.length := by
  induction p with
  | nil => rfl
  | cons huv q ih => simp [liftAvoid, ih]

theorem support_liftAvoid {G : SimpleGraph V} {x y : V}
    {a b : {v : V // v ≠ y}} (p : (identify G x y).Walk a b)
    (havoid : ∀ v ∈ p.support, v.1 ≠ x) :
    (liftAvoid p havoid).support = p.support.map Subtype.val := by
  induction p with
  | nil => rfl
  | cons huv q ih => simp [liftAvoid, ih]

theorem isPath_liftAvoid {G : SimpleGraph V} {x y : V}
    {a b : {v : V // v ≠ y}} (p : (identify G x y).Walk a b)
    (hp : p.IsPath) (havoid : ∀ v ∈ p.support, v.1 ≠ x) :
    (liftAvoid p havoid).IsPath := by
  apply Walk.IsPath.mk'
  rw [support_liftAvoid]
  exact (List.nodup_map_iff Subtype.val_injective).mpr hp.support_nodup

/-- Helper: close a path `midG : G.Walk a b` (avoiding `u`) with edges `u-a` and `b-u`
    to obtain a simple cycle of length `midG.length + 2`. -/
theorem cycle_of_path_and_apex {G : SimpleGraph V} {u a b : V}
    (midG : G.Walk a b) (hmid : midG.IsPath) (hpos : 1 ≤ midG.length)
    (hu : u ∉ midG.support) (hua : G.Adj u a) (hbu : G.Adj b u) :
    ∃ c : G.Walk u u, c.IsCycle ∧ c.length = midG.length + 2 := by
  let c : G.Walk u u := .cons hua (midG.append (.cons hbu .nil))
  have hlen : c.length = midG.length + 2 := by
    simp [c, Walk.length_append]
  have hsupp : c.support = u :: (midG.support ++ [u]) := by
    simp [c, Walk.support_cons, Walk.support_append]
  have htail : c.support.tail = midG.support ++ [u] := by
    rw [hsupp, List.tail_cons]
  have hnodup : c.support.tail.Nodup := by
    rw [htail]
    exact List.nodup_append'.mpr ⟨hmid.support_nodup, List.nodup_singleton u,
      fun z hz1 hz2 => hu ((List.mem_singleton.mp hz2) ▸ hz1)⟩
  have hnil : ¬ c.Nil := by
    intro h
    have := Walk.length_eq_zero_iff.mpr h
    omega
  have hc : c.IsCycle := by
    apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    refine ⟨Walk.IsPath.mk' ?_, by omega⟩
    rwa [Walk.support_tail_of_not_nil _ hnil]
  exact ⟨c, hc, hlen⟩

/-- Helper: extend a path `midG : G.Walk a b` (avoiding `x` and `y`, with `x ≠ y`)
    by `x-a` and `b-y` to get a simple `x`-`y` path of length `midG.length + 2`. -/
theorem path_of_mid_and_ends {G : SimpleGraph V} {x y a b : V}
    (hxy : x ≠ y) (midG : G.Walk a b) (hmid : midG.IsPath)
    (hx : x ∉ midG.support) (hy : y ∉ midG.support)
    (hxa : G.Adj x a) (hby : G.Adj b y) :
    ∃ p : G.Walk x y, p.IsPath ∧ p.length = midG.length + 2 := by
  let p : G.Walk x y := .cons hxa (midG.append (.cons hby .nil))
  have hlen : p.length = midG.length + 2 := by
    simp [p, Walk.length_append]
  have hsupp : p.support = x :: (midG.support ++ [y]) := by
    simp [p, Walk.support_cons, Walk.support_append]
  have hp : p.IsPath := by
    apply Walk.IsPath.mk'
    rw [hsupp, List.nodup_cons]
    refine ⟨?_, List.nodup_append'.mpr ⟨hmid.support_nodup, List.nodup_singleton y,
      fun z hz1 hz2 => hy ((List.mem_singleton.mp hz2) ▸ hz1)⟩⟩
    intro hm
    rcases List.mem_append.mp hm with hm1 | hm2
    · exact hx hm1
    · exact hxy (List.mem_singleton.mp hm2)
  exact ⟨p, hp, hlen⟩

/-- Universal Identification Lifting Lemma:
    If `G` is power-free and `identify G x y` has a power-of-2 cycle, then `G` contains
    a simple `x`-`y` path of length `2^k` for some `k ≥ 2`. -/
theorem dyadic_path_of_identify {G : SimpleGraph V} {x y : V} (hxy : x ≠ y)
    (hfree : ¬ HasPower G) (hpow : HasPower (identify G x y)) :
    ∃ (k : ℕ) (p : G.Walk x y), 2 ≤ k ∧ p.IsPath ∧ p.length = 2 ^ k := by
  classical
  obtain ⟨k, v₀, c, hk, hc, hlen⟩ := hpow
  let X : {v : V // v ≠ y} := ⟨x, hxy⟩
  by_cases hmem : X ∈ c.support
  · let c' := c.rotate X hmem
    have hc' : c'.IsCycle := SimpleGraph.Walk.IsCycle.rotate hmem hc
    have hlen' : c'.length = 2 ^ k := by rw [Walk.length_rotate, hlen]
    have hge4 : 4 ≤ c'.length := by
      rw [hlen']
      have h1 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide : 0 < 2) hk
      omega
    cases hce : c' with
    | nil =>
      rw [hce] at hge4
      simp at hge4
    | @cons _ a _ h₁ q =>
      have hqlen : q.length + 1 = 2 ^ k := by
        have := congrArg Walk.length hce
        simp only [Walk.length_cons] at this
        omega
      have hqpath : q.IsPath := by
        apply Walk.IsPath.mk'
        have hsn := hc'.support_nodup
        rw [hce, Walk.support_cons, List.tail_cons] at hsn
        exact hsn
      have hqrpath : q.reverse.IsPath := hqpath.reverse
      have hqrlen : q.reverse.length = q.length := Walk.length_reverse q
      cases hqre : q.reverse with
      | nil =>
        rw [hqre] at hqrlen
        simp at hqrlen
        omega
      | @cons _ b _ h₂ r =>
        let mid : (identify G x y).Walk a b := r.reverse
        have hmidlen : mid.length + 2 = 2 ^ k := by
          have := congrArg Walk.length hqre
          simp only [Walk.length_cons, hqrlen] at this
          have hml : mid.length = r.length := Walk.length_reverse r
          omega
        have hmidpath : mid.IsPath := by
          have hrp : r.IsPath := by
            apply Walk.IsPath.mk'
            have hsn := hqrpath.support_nodup
            rw [hqre, Walk.support_cons, List.nodup_cons] at hsn
            exact hsn.2
          exact hrp.reverse
        have hXnotr : X ∉ r.support := by
          have hsn := hqrpath.support_nodup
          rw [hqre, Walk.support_cons, List.nodup_cons] at hsn
          exact hsn.1
        have hXnotmid : ∀ v ∈ mid.support, v.1 ≠ x := by
          intro v hv hvx
          have hvX : v = X := Subtype.ext hvx
          rw [hvX] at hv
          have hr : X ∈ r.support := by
            have hs : mid.support = r.support.reverse := Walk.support_reverse r
            rw [hs, List.mem_reverse] at hv
            exact hv
          exact hXnotr hr
        let midG := liftAvoid mid hXnotmid
        have hmidGpath : midG.IsPath := isPath_liftAvoid mid hmidpath hXnotmid
        have hmidGlen : midG.length = mid.length := length_liftAvoid mid hXnotmid
        have hxnot : x ∉ midG.support := by
          rw [support_liftAvoid]
          intro hm
          obtain ⟨v, hv, hvx⟩ := List.mem_map.mp hm
          exact hXnotmid v hv hvx
        have hynot : y ∉ midG.support := by
          rw [support_liftAvoid]
          intro hm
          obtain ⟨v, _, hvy⟩ := List.mem_map.mp hm
          exact v.2 hvy
        have h1G : G.Adj x a.1 ∨ G.Adj y a.1 := by
          rcases h₁.2 with h | ⟨_, hy⟩ | ⟨hax, _⟩
          · exact Or.inl h
          · exact Or.inr hy
          · exact False.elim (h₁.1 (Subtype.ext hax.symm))
        have h2G : G.Adj b.1 x ∨ G.Adj b.1 y := by
          rcases h₂.2 with h | ⟨_, hy⟩ | ⟨hbx, _⟩
          · exact Or.inl h.symm
          · exact Or.inr hy.symm
          · exact False.elim (h₂.1 (Subtype.ext hbx.symm))
        rcases h1G with hxa | hya <;> rcases h2G with hbx | hby
        · obtain ⟨d, hd, hdl⟩ := cycle_of_path_and_apex midG hmidGpath (by omega) hxnot hxa hbx
          exact False.elim (hfree ⟨k, x, d, hk, hd, by omega⟩)
        · obtain ⟨p, hp, hpl⟩ := path_of_mid_and_ends hxy midG hmidGpath hxnot hynot hxa hby
          exact ⟨k, p, hk, hp, by omega⟩
        · obtain ⟨p, hp, hpl⟩ := path_of_mid_and_ends hxy midG.reverse hmidGpath.reverse
            (by rw [Walk.support_reverse, List.mem_reverse]; exact hxnot)
            (by rw [Walk.support_reverse, List.mem_reverse]; exact hynot)
            hbx.symm hya.symm
          exact ⟨k, p, hk, hp, by simp only [Walk.length_reverse] at hpl; omega⟩
        · obtain ⟨d, hd, hdl⟩ := cycle_of_path_and_apex midG hmidGpath (by omega) hynot hya hby
          exact False.elim (hfree ⟨k, y, d, hk, hd, by omega⟩)
  · have havoid : ∀ v ∈ c.support, v.1 ≠ x := by
      intro v hv hvx
      have hvX : v = X := Subtype.ext hvx; exact hmem (hvX ▸ hv)
    let d := liftAvoid c havoid
    have hdlen : d.length = 2 ^ k := by rw [length_liftAvoid, hlen]
    have hdtail : d.support.tail.Nodup := by
      have hs : d.support = c.support.map Subtype.val := support_liftAvoid c havoid
      rw [hs, ← List.map_tail]
      exact (List.nodup_map_iff Subtype.val_injective).mpr hc.support_nodup
    have hdnil : ¬ d.Nil := by
      intro h
      have := Walk.length_eq_zero_iff.mpr h
      have h1 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide : 0 < 2) hk
      omega
    have hdc : d.IsCycle := by
      apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      refine ⟨Walk.IsPath.mk' ?_, ?_⟩
      · rwa [Walk.support_tail_of_not_nil _ hdnil]
      · rw [hdlen]
        have h1 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide : 0 < 2) hk
        omega
    exact False.elim (hfree ⟨k, v₀.1, d, hk, hdc, hdlen⟩)

/-- In any power-free graph, two distinct vertices have at most one common neighbor. -/
theorem unique_common_neighbor {G : SimpleGraph V} (hfree : ¬ HasPower G)
    {x y u v : V} (hxy : x ≠ y)
    (hxu : G.Adj x u) (hyu : G.Adj y u) (hxv : G.Adj x v) (hyv : G.Adj y v) :
    u = v := by
  by_contra huv
  exact hfree (rectangle_power G (G.ne_of_adj hxu) hxy (G.ne_of_adj hxv)
    (G.ne_of_adj hyu).symm huv (G.ne_of_adj hyv) hxu hyu.symm hyv hxv.symm)

/-- Cardinality of `{v : V // v ≠ y}` is strictly less than `Fintype.card V`. -/
theorem card_sub_lt [Fintype V] [DecidableEq V] (y : V) :
    Fintype.card {v : V // v ≠ y} < Fintype.card V := by
  classical
  have h : Fintype.card {v : V // v ≠ y} + 1 = Fintype.card V := by
    rw [Fintype.card_subtype,
      show (Finset.univ.filter (fun v : V => v ≠ y)) = Finset.univ.erase y by ext z; simp]
    exact Finset.card_erase_add_one (Finset.mem_univ y)
  omega

/-- Exact neighbor-set formula for `v ≠ X` in `identify G x y` when `v` is not a common neighbor
    of `x` and `y`: its degree is unchanged. -/
theorem identify_degree_other_of_not_common [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {x y : V} (hxy : x ≠ y)
    [DecidableRel (identify G x y).Adj]
    (v : {z : V // z ≠ y}) (hvx : v.1 ≠ x)
    (hnc : ¬ (G.Adj x v.1 ∧ G.Adj y v.1)) :
    (identify G x y).degree v = G.degree v.1 := by
  classical
  let H := identify G x y
  let X : {z : V // z ≠ y} := ⟨x, hxy⟩
  let f : H.neighborSet v → G.neighborSet v.1 := fun u =>
    if hu : u.1.1 = x then
      if h : G.Adj v.1 x then ⟨x, h⟩ else ⟨y, by
        rcases u.2.2 with h1 | ⟨hvx', _⟩ | ⟨_, hvy⟩
        · exact False.elim (h (hu ▸ h1))
        · exact False.elim (hvx hvx')
        · exact hvy⟩
    else ⟨u.1.1, by
      rcases u.2.2 with h1 | ⟨hvx', _⟩ | ⟨hux, _⟩
      · exact h1
      · exact False.elim (hvx hvx')
      · exact False.elim (hu hux)⟩
  let g : G.neighborSet v.1 → H.neighborSet v := fun u =>
    if hu : u.1 = y then
      ⟨X, ⟨fun h => hvx (congrArg Subtype.val h), Or.inr (Or.inr ⟨rfl, hu ▸ u.2⟩)⟩⟩
    else
      ⟨⟨u.1, hu⟩, ⟨fun h => (G.ne_of_adj u.2) (congrArg Subtype.val h), Or.inl u.2⟩⟩
  have e : H.neighborSet v ≃ G.neighborSet v.1 :=
    { toFun := f
      invFun := g
      left_inv := by
        intro u
        apply Subtype.ext
        by_cases hux : u.1.1 = x
        · by_cases hvxa : G.Adj v.1 x
          · simp only [f, g, dif_pos hux, dif_pos hvxa, dif_neg hxy]
            exact Subtype.ext hux.symm
          · simp only [f, g, dif_pos hux, dif_neg hvxa, dif_pos rfl]
            exact Subtype.ext hux.symm
        · have huy : u.1.1 ≠ y := u.1.2
          simp only [f, g, dif_neg hux, dif_neg huy]
      right_inv := by
        intro u
        apply Subtype.ext
        by_cases huy : u.1 = y
        · have hnvx : ¬ G.Adj v.1 x := fun h => hnc ⟨h.symm, (huy ▸ u.2).symm⟩
          simp only [f, g, dif_pos huy, dif_pos rfl, dif_neg hnvx, huy]
        · by_cases hux : u.1 = x
          · have hvxa : G.Adj v.1 x := hux ▸ u.2
            simp only [f, g, dif_neg huy, dif_pos hux, dif_pos hvxa, hux]
          · simp only [f, g, dif_neg huy, dif_neg hux] }
  have hc := Fintype.card_congr e
  rwa [SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.card_neighborSet_eq_degree] at hc

/-- Exact degree formula for a common neighbor `u` of `x` and `y` in `identify G x y`:
    its degree drops by 1. -/
theorem identify_degree_common [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {x y : V} (hxy : x ≠ y)
    [DecidableRel (identify G x y).Adj]
    (u : {z : V // z ≠ y}) (hux : G.Adj x u.1) (huy : G.Adj y u.1) :
    (identify G x y).degree u + 1 = G.degree u.1 := by
  classical
  let H := identify G x y
  have hunx : u.1 ≠ x := (G.ne_of_adj hux).symm
  let e : H.neighborSet u ≃ {z : V // G.Adj u.1 z ∧ z ≠ y} :=
    { toFun := fun v => ⟨v.1.1, by
        rcases v.2.2 with h1 | ⟨hux', _⟩ | ⟨hvx, _⟩
        · exact ⟨h1, v.1.2⟩
        · exact False.elim (hunx hux')
        · exact ⟨hvx.symm ▸ hux.symm, v.1.2⟩⟩
      invFun := fun z => ⟨⟨z.1, z.2.2⟩, ⟨fun h => (G.ne_of_adj z.2.1) (congrArg Subtype.val h),
        Or.inl z.2.1⟩⟩
      left_inv := by intro v; rfl
      right_inv := by intro z; rfl }
  have hc := Fintype.card_congr e
  rw [SimpleGraph.card_neighborSet_eq_degree, Fintype.card_subtype] at hc
  have hs : (Finset.univ.filter (fun z : V => G.Adj u.1 z ∧ z ≠ y)) =
      (G.neighborFinset u.1).erase y := by
    ext z; simp [and_comm]
  rw [hs] at hc
  change H.degree u + 1 = G.degree u.1
  rw [hc, ← G.card_neighborFinset_eq_degree]
  exact Finset.card_erase_add_one ((G.mem_neighborFinset u.1 y).mpr huy.symm)

/-- Exact degree formula for the merged vertex `X = ⟨x, hxy⟩` in `identify G x y`. -/
theorem identify_degree_merged_ge [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {x y : V} (hxy : x ≠ y)
    [DecidableRel (identify G x y).Adj] :
    (identify G x y).degree ⟨x, hxy⟩ =
      ((G.neighborFinset x ∪ G.neighborFinset y).erase x |>.erase y).card := by
  classical
  let H := identify G x y
  let X : {z : V // z ≠ y} := ⟨x, hxy⟩
  change H.degree X = _
  rw [← H.card_neighborFinset_eq_degree]
  let f : H.neighborFinset X → ((G.neighborFinset x ∪ G.neighborFinset y).erase x |>.erase y) :=
    fun v => ⟨v.1.1, by
      have hv := (H.mem_neighborFinset X v.1).mp v.2
      simp only [Finset.mem_erase, Finset.mem_union, SimpleGraph.mem_neighborFinset]
      refine ⟨v.1.2, fun h => hv.1 (Subtype.ext h.symm), ?_⟩
      rcases hv.2 with h1 | ⟨_, hy⟩ | ⟨hvx, _⟩
      · exact Or.inl h1
      · exact Or.inr hy
      · exact False.elim (hv.1 (Subtype.ext hvx.symm))⟩
  let g : ((G.neighborFinset x ∪ G.neighborFinset y).erase x |>.erase y) → H.neighborFinset X :=
    fun z => ⟨⟨z.1, (Finset.mem_erase.mp z.2).1⟩, by
      have hz := z.2
      simp only [Finset.mem_erase, Finset.mem_union, SimpleGraph.mem_neighborFinset] at hz
      apply (H.mem_neighborFinset X _).mpr
      refine ⟨fun h => hz.2.1 (congrArg Subtype.val h).symm, ?_⟩
      rcases hz.2.2 with hx | hy
      · exact Or.inl hx
      · exact Or.inr (Or.inl ⟨rfl, hy⟩)⟩
  have e : H.neighborFinset X ≃
      ((G.neighborFinset x ∪ G.neighborFinset y).erase x |>.erase y) :=
    { toFun := f, invFun := g, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  simpa using Fintype.card_congr e

/-- Wave 1 Universal Dyadic Path Theorem (dist >= 3):
    In any MinimalBad graph, every pair of non-adjacent vertices with no common neighbor
    is connected by a simple path of length `2^k` (`k ≥ 2`). -/
theorem dyadic_path_of_dist_ge_three [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {x y : V} (hxy : x ≠ y) (hnadj : ¬ G.Adj x y)
    (hnocom : ∀ u, ¬ (G.Adj x u ∧ G.Adj y u)) :
    ∃ (k : ℕ) (p : G.Walk x y), 2 ≤ k ∧ p.IsPath ∧ p.length = 2 ^ k := by
  classical
  let H := identify G x y
  let _ : DecidableRel H.Adj := fun a b => Classical.dec _
  let X : {z : V // z ≠ y} := ⟨x, hxy⟩
  have hXdeg : H.degree X = G.degree x + G.degree y := by
    rw [identify_degree_merged_ge G hxy]
    have hdisj : Disjoint (G.neighborFinset x) (G.neighborFinset y) := by
      rw [Finset.disjoint_left]
      intro u hux huy
      exact hnocom u ⟨(G.mem_neighborFinset x u).mp hux, (G.mem_neighborFinset y u).mp huy⟩
    have hxnot : x ∉ G.neighborFinset x ∪ G.neighborFinset y := by
      simp only [Finset.mem_union, SimpleGraph.mem_neighborFinset, not_or]
      exact ⟨G.loopless.irrefl x, fun h => hnadj h.symm⟩
    have hynot : y ∉ (G.neighborFinset x ∪ G.neighborFinset y).erase x := by
      simp only [Finset.mem_erase, Finset.mem_union, SimpleGraph.mem_neighborFinset, not_and, not_or]
      intro _
      exact ⟨hnadj, G.loopless.irrefl y⟩
    rw [Finset.erase_eq_of_notMem hynot, Finset.erase_eq_of_notMem hxnot,
      Finset.card_union_of_disjoint hdisj,
      G.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree]
  have hXge : 3 ≤ H.degree X := by
    have hx2 := no_small_defect G hm x
    have hy2 := no_small_defect G hm y
    omega
  obtain ⟨_, w, hw⟩ := hm.1
  have hnear : Near H := by
    refine ⟨⟨X, hXge⟩, ?_⟩
    by_cases hwy : w = y
    · refine ⟨X, fun v hv => ?_⟩
      have hvx : v.1 ≠ x := fun h => hv (Subtype.ext h)
      rw [identify_degree_other_of_not_common G hxy v hvx (hnocom v.1)]
      exact hw v.1 (hwy ▸ v.2)
    · refine ⟨⟨w, hwy⟩, fun v hv => ?_⟩
      by_cases hvx : v.1 = x
      · have : v = X := Subtype.ext hvx
        rw [this]; exact hXge
      · rw [identify_degree_other_of_not_common G hxy v hvx (hnocom v.1)]
        exact hw v.1 (fun h => hv (Subtype.ext h))
  have hpow : HasPower H := hm.2.2.1 _ H (card_sub_lt y) hnear
  exact dyadic_path_of_identify hxy hm.2.1 hpow

/-- 6-Line Unified Bipartite Exclusion: NO MinimalBad graph is bipartite.
    Covers C-B, S-B, and all H-B-* leaves in a single proof via `dyadic_path_of_dist_ge_three`. -/
theorem no_bipartite_minimal_bad [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G) (hB : Bip G) : False := by
  classical
  obtain ⟨color, hproper⟩ := hB
  have hwalk_par : ∀ {a b : V} (p : G.Walk a b),
      p.length % 2 = 0 → color a = color b := by
    have haux : ∀ {a b : V} (p : G.Walk a b),
        (p.length % 2 = 0 → color a = color b) ∧ (p.length % 2 = 1 → color a ≠ color b) := by
      intro a b p
      induction p with
      | nil => simp
      | @cons u v w huv q ih =>
        have hc := hproper u v huv
        constructor <;> intro h
        · have h1 : q.length % 2 = 1 := by simp at h; omega
          have h2 := ih.2 h1
          cases hu : color u <;> cases hv : color v <;> cases hw : color w <;> simp_all
        · have h0 : q.length % 2 = 0 := by simp at h; omega
          have h2 := ih.1 h0
          rw [← h2]; exact hc
    intro a b p; exact (haux p).1
  have hcomplete : ∀ x y, color x ≠ color y → G.Adj x y := by
    intro x y hne
    by_contra hnadj
    have hxy : x ≠ y := fun h => hne (congrArg color h)
    have hnocom : ∀ u, ¬ (G.Adj x u ∧ G.Adj y u) := by
      rintro u ⟨hxu, hyu⟩
      have h1 := hproper x u hxu
      have h2 := hproper y u hyu
      cases hx : color x <;> cases hy : color y <;> cases hu : color u <;> simp_all
    obtain ⟨k, p, hk, _, hplen⟩ := dyadic_path_of_dist_ge_three G hm hxy hnadj hnocom
    have heven : p.length % 2 = 0 := by
      rw [hplen]
      cases k with
      | zero => omega
      | succ k => rw [pow_succ]; omega
    exact hne (hwalk_par p heven)
  obtain ⟨x, hx⟩ := hm.1.1
  have hpos : 0 < G.degree x := by omega
  obtain ⟨y₁, hxy₁⟩ := (G.degree_pos_iff_exists_adj x).mp hpos
  have hy₁_deg : 2 ≤ G.degree y₁ := no_small_defect G hm y₁
  have hex_x₂ : ∃ x₂, G.Adj y₁ x₂ ∧ x₂ ≠ x := by
    by_contra h
    have hs : G.neighborFinset y₁ ⊆ ({x} : Finset V) := by
      intro z hz
      have hadj := (G.mem_neighborFinset y₁ z).mp hz
      by_cases hzx : z = x
      · simp [hzx]
      · exact False.elim (h ⟨z, hadj, hzx⟩)
    have hc := Finset.card_le_card hs
    rw [G.card_neighborFinset_eq_degree, Finset.card_singleton] at hc
    omega
  obtain ⟨x₂, hy₁x₂, hx₂x⟩ := hex_x₂
  have hex_y₂ : ∃ y₂, G.Adj x y₂ ∧ y₂ ≠ y₁ := by
    by_contra h
    have hs : G.neighborFinset x ⊆ ({y₁} : Finset V) := by
      intro z hz
      have hadj := (G.mem_neighborFinset x z).mp hz
      by_cases hzy : z = y₁
      · simp [hzy]
      · exact False.elim (h ⟨z, hadj, hzy⟩)
    have hc := Finset.card_le_card hs
    rw [G.card_neighborFinset_eq_degree, Finset.card_singleton] at hc
    omega
  obtain ⟨y₂, hxy₂, hy₂y₁⟩ := hex_y₂
  have hcol_x₂y₂ : color x₂ ≠ color y₂ := by
    have h1 := hproper x y₁ hxy₁
    have h2 := hproper y₁ x₂ hy₁x₂
    have h3 := hproper x y₂ hxy₂
    cases hx : color x <;> cases hy₁ : color y₁ <;> cases hx₂ : color x₂ <;> cases hy₂ : color y₂ <;> simp_all
  have hx₂y₂ : G.Adj x₂ y₂ := hcomplete x₂ y₂ hcol_x₂y₂
  exact hm.2.1 (rectangle_power G (G.ne_of_adj hxy₁) hx₂x.symm (G.ne_of_adj hxy₂)
    (G.ne_of_adj hy₁x₂) hy₂y₁.symm (G.ne_of_adj hx₂y₂) hxy₁ hy₁x₂ hx₂y₂ hxy₂.symm)

/-- NEW (Wave 2, Agent #6): Distance-2 Dyadic Path Theorem.
    In MinimalBad(G), if x ≠ y are non-adjacent with common neighbor u, and either:
    (a) G is cubic, or (b) deg(u) ≥ 4, or (c) deg(x) = 2 ∨ deg(y) = 2,
    then G has a simple x-y path of length 2^k (k ≥ 2). -/
theorem dyadic_path_of_dist_two [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {x y u : V} (hxy : x ≠ y) (hnadj : ¬ G.Adj x y)
    (hxu : G.Adj x u) (hyu : G.Adj y u)
    (hcase : (∀ v, G.degree v = 3) ∨ 4 ≤ G.degree u ∨ G.degree x = 2 ∨ G.degree y = 2) :
    ∃ (k : ℕ) (p : G.Walk x y), 2 ≤ k ∧ p.IsPath ∧ p.length = 2 ^ k := by
  classical
  let H := identify G x y
  let _ : DecidableRel H.Adj := fun a b => Classical.dec _
  let X : {z : V // z ≠ y} := ⟨x, hxy⟩
  have huy : u ≠ y := (G.ne_of_adj hyu).symm
  let U : {z : V // z ≠ y} := ⟨u, huy⟩
  have huniq : ∀ z, G.Adj x z ∧ G.Adj y z → z = u :=
    fun z hz => unique_common_neighbor hm.2.1 hxy hz.1 hz.2 hxu hyu
  have hXdeg : H.degree X + 1 = G.degree x + G.degree y := by
    rw [identify_degree_merged_ge G hxy]
    have hxnot : x ∉ G.neighborFinset x ∪ G.neighborFinset y := by
      simp only [Finset.mem_union, SimpleGraph.mem_neighborFinset, not_or]
      exact ⟨G.loopless.irrefl x, fun h => hnadj h.symm⟩
    have hynot : y ∉ (G.neighborFinset x ∪ G.neighborFinset y).erase x := by
      simp only [Finset.mem_erase, Finset.mem_union, SimpleGraph.mem_neighborFinset, not_and, not_or]
      intro _
      exact ⟨hnadj, G.loopless.irrefl y⟩
    rw [Finset.erase_eq_of_notMem hynot, Finset.erase_eq_of_notMem hxnot]
    have hinter : G.neighborFinset x ∩ G.neighborFinset y = {u} := by
      ext z
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
      exact ⟨huniq z, fun hz => hz ▸ ⟨hxu, hyu⟩⟩
    have hcu := Finset.card_union_add_card_inter (G.neighborFinset x) (G.neighborFinset y)
    rw [hinter, Finset.card_singleton, G.card_neighborFinset_eq_degree,
      G.card_neighborFinset_eq_degree] at hcu
    exact hcu
  have hXge : 3 ≤ H.degree X := by
    have hx2 := no_small_defect G hm x
    have hy2 := no_small_defect G hm y
    omega
  have hUdeg : H.degree U + 1 = G.degree u := identify_degree_common G hxy U hxu hyu
  have hother : ∀ v : {z : V // z ≠ y}, v ≠ X → v ≠ U → H.degree v = G.degree v.1 := by
    intro v hvX hvU
    apply identify_degree_other_of_not_common G hxy v (fun h => hvX (Subtype.ext h))
    intro hcom
    exact hvU (Subtype.ext (huniq v.1 hcom))
  obtain ⟨_, w, hw⟩ := hm.1
  have hnear : Near H := by
    refine ⟨⟨X, hXge⟩, ?_⟩
    rcases hcase with hC | hu4 | hxw | hyw
    · refine ⟨U, fun v hv => ?_⟩
      by_cases hvX : v = X
      · rw [hvX]; exact hXge
      · rw [hother v hvX hv, hC]
    · by_cases hwy : w = y
      · refine ⟨X, fun v hv => ?_⟩
        by_cases hvU : v = U
        · rw [hvU]; omega
        · rw [hother v hv hvU]; exact hw v.1 (hwy ▸ v.2)
      · refine ⟨⟨w, hwy⟩, fun v hv => ?_⟩
        by_cases hvX : v = X
        · rw [hvX]; exact hXge
        · by_cases hvU : v = U
          · rw [hvU]; omega
          · rw [hother v hvX hvU]; exact hw v.1 (fun h => hv (Subtype.ext h))
    · have hwx : w = x := by
        by_contra hne; have := hw x (Ne.symm hne); omega
      refine ⟨U, fun v hv => ?_⟩
      by_cases hvX : v = X
      · rw [hvX]; exact hXge
      · rw [hother v hvX hv]; exact hw v.1 (fun h => hvX (Subtype.ext (h.trans hwx)))
    · have hwy : w = y := by
        by_contra hne; have := hw y (Ne.symm hne); omega
      refine ⟨U, fun v hv => ?_⟩
      by_cases hvX : v = X
      · rw [hvX]; exact hXge
      · rw [hother v hvX hv]; exact hw v.1 (hwy ▸ v.2)
  have hpow : HasPower H := hm.2.2.1 _ H (card_sub_lt y) hnear
  exact dyadic_path_of_identify hxy hm.2.1 hpow

/-- NEW (Wave 2, Agent #6): Cubic All-Non-Edge Dyadic Path Theorem.
    In EVERY cubic MinimalBad graph (all 5 open cubic leaves including C-N-R),
    EVERY non-adjacent pair of distinct vertices is joined by a simple 2^k-path (k ≥ 2). -/
theorem cubic_all_nonadj_dyadic_path [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (hC : Cubic G) {x y : V} (hxy : x ≠ y) (hnadj : ¬ G.Adj x y) :
    ∃ (k : ℕ) (p : G.Walk x y), 2 ≤ k ∧ p.IsPath ∧ p.length = 2 ^ k := by
  by_cases hcom : ∃ u, G.Adj x u ∧ G.Adj y u
  · obtain ⟨u, hxu, hyu⟩ := hcom
    exact dyadic_path_of_dist_two G hm hxy hnadj hxu hyu (Or.inl hC)
  · push Not at hcom
    exact dyadic_path_of_dist_ge_three G hm hxy hnadj (fun u h => hcom u h.1 h.2)

/-- Helper: close a simple `x`-`y` path of length `2^k` (`k ≥ 2`) with an edge `x-y`
    to get a simple cycle of length `2^k + 1` containing the edge `s(x, y)`. -/
theorem fermat_cycle_of_path_and_edge {G : SimpleGraph V} {x y : V}
    (hxy : G.Adj x y) {k : ℕ} (hk : 2 ≤ k) (p : G.Walk x y)
    (hp : p.IsPath) (hlen : p.length = 2 ^ k) :
    ∃ c : G.Walk x x, c.IsCycle ∧ c.length = 2 ^ k + 1 ∧ s(x, y) ∈ c.edges := by
  let c : G.Walk x x := p.append (.cons hxy.symm .nil)
  have hclen : c.length = 2 ^ k + 1 := by simp [c, Walk.length_append, hlen]
  have hge4 : 4 ≤ p.length := by
    rw [hlen]; exact Nat.pow_le_pow_right (by decide : 0 < 2) hk
  have hsupp : c.support = p.support ++ [x] := by simp [c, Walk.support_append]
  have htail_nodup : c.support.tail.Nodup := by
    have hpnil : ¬ p.Nil := by
      intro h; have := Walk.length_eq_zero_iff.mpr h; omega
    have hps : p.support = x :: p.support.tail := (p.cons_tail_support).symm
    have htail : c.support.tail = p.support.tail ++ [x] := by
      calc c.support.tail = (p.support ++ [x]).tail := by rw [hsupp]
        _ = (x :: p.support.tail ++ [x]).tail := by rw [← hps]
        _ = p.support.tail ++ [x] := rfl
    have hpn := hp.support_nodup
    rw [hps, List.nodup_cons] at hpn
    rw [htail]
    exact List.nodup_append'.mpr ⟨hpn.2, List.nodup_singleton x,
      fun z hz1 hz2 => hpn.1 ((List.mem_singleton.mp hz2) ▸ hz1)⟩
  have hcnil : ¬ c.Nil := by
    intro h; have := Walk.length_eq_zero_iff.mpr h; omega
  have hc : c.IsCycle := by
    apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    refine ⟨Walk.IsPath.mk' ?_, by omega⟩
    rwa [Walk.support_tail_of_not_nil _ hcnil]
  have hmem : s(x, y) ∈ c.edges := by
    simp only [c, Walk.edges_append, Walk.edges_cons, Walk.edges_nil, List.mem_append,
      List.mem_cons]
    exact Or.inr (Or.inl Sym2.eq_swap)
  exact ⟨c, hc, hclen, hmem⟩

/-- NEW (Wave 2, Agent #6): Universal Fermat-Edge Cycle Theorem (non-triangle edges).
    In ANY MinimalBad(G), every edge xy not in a triangle lies on a simple cycle of
    length 2^k + 1 (k ≥ 2). Applies to EVERY edge in C-N-*, S-N-*, H-N-*. -/
theorem fermat_cycle_of_non_triangle_edge [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {x y : V} (hxy : G.Adj x y) (hntri : ∀ u, ¬ (G.Adj x u ∧ G.Adj y u)) :
    ∃ (k : ℕ) (c : G.Walk x x), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k + 1 ∧
      s(x, y) ∈ c.edges := by
  classical
  have hne : x ≠ y := G.ne_of_adj hxy
  let H := identify G x y
  let _ : DecidableRel H.Adj := fun a b => Classical.dec _
  let X : {z : V // z ≠ y} := ⟨x, hne⟩
  have hXdeg : H.degree X + 2 = G.degree x + G.degree y := by
    rw [identify_degree_merged_ge G hne]
    have hdisj : Disjoint (G.neighborFinset x) (G.neighborFinset y) := by
      rw [Finset.disjoint_left]
      intro u hux huy
      exact hntri u ⟨(G.mem_neighborFinset x u).mp hux, (G.mem_neighborFinset y u).mp huy⟩
    have hxmem : x ∈ G.neighborFinset x ∪ G.neighborFinset y :=
      Finset.mem_union_right _ ((G.mem_neighborFinset y x).mpr hxy.symm)
    have hymem : y ∈ (G.neighborFinset x ∪ G.neighborFinset y).erase x :=
      Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_union_left _ ((G.mem_neighborFinset x y).mpr hxy)⟩
    have h1 := Finset.card_erase_add_one hymem
    have h2 := Finset.card_erase_add_one hxmem
    rw [Finset.card_union_of_disjoint hdisj,
      G.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree] at h2
    omega
  have hXge : 3 ≤ H.degree X := by
    have hx2 := no_small_defect G hm x
    have hy2 := no_small_defect G hm y
    obtain ⟨_, w, hw⟩ := hm.1
    by_cases hwx : x = w
    · have := hw y (hwx ▸ hne.symm); omega
    · have := hw x hwx; omega
  obtain ⟨_, w, hw⟩ := hm.1
  have hnear : Near H := by
    refine ⟨⟨X, hXge⟩, ?_⟩
    by_cases hwy : w = y
    · refine ⟨X, fun v hv => ?_⟩
      rw [identify_degree_other_of_not_common G hne v (fun h => hv (Subtype.ext h)) (hntri v.1)]
      exact hw v.1 (hwy ▸ v.2)
    · refine ⟨⟨w, hwy⟩, fun v hv => ?_⟩
      by_cases hvX : v = X
      · rw [hvX]; exact hXge
      · rw [identify_degree_other_of_not_common G hne v (fun h => hvX (Subtype.ext h)) (hntri v.1)]
        exact hw v.1 (fun h => hv (Subtype.ext h))
  have hpow : HasPower H := hm.2.2.1 _ H (card_sub_lt y) hnear
  obtain ⟨k, p, hk, hp, hplen⟩ := dyadic_path_of_identify hne hm.2.1 hpow
  obtain ⟨c, hc, hclen, hmem⟩ := fermat_cycle_of_path_and_edge hxy hk p hp hplen
  exact ⟨k, c, hk, hc, hclen, hmem⟩

/-- NEW (Wave 2, Agent #6): Cubic Universal Fermat-Edge Cycle Theorem.
    In EVERY cubic MinimalBad graph (all 5 open cubic leaves, with or without triangles),
    EVERY edge lies on a simple cycle of length 2^k + 1 (k ≥ 2). -/
theorem cubic_fermat_cycle_of_edge [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (hC : Cubic G) {x y : V} (hxy : G.Adj x y) :
    ∃ (k : ℕ) (c : G.Walk x x), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k + 1 ∧
      s(x, y) ∈ c.edges := by
  classical
  by_cases htri : ∃ u, G.Adj x u ∧ G.Adj y u
  · obtain ⟨u, hxu, hyu⟩ := htri
    have hne : x ≠ y := G.ne_of_adj hxy
    have huy : u ≠ y := (G.ne_of_adj hyu).symm
    let H := identify G x y
    let _ : DecidableRel H.Adj := fun a b => Classical.dec _
    let X : {z : V // z ≠ y} := ⟨x, hne⟩
    let U : {z : V // z ≠ y} := ⟨u, huy⟩
    have huniq : ∀ z, G.Adj x z ∧ G.Adj y z → z = u :=
      fun z hz => unique_common_neighbor hm.2.1 hne hz.1 hz.2 hxu hyu
    have hXdeg : H.degree X + 3 = G.degree x + G.degree y := by
      rw [identify_degree_merged_ge G hne]
      have hxmem : x ∈ G.neighborFinset x ∪ G.neighborFinset y :=
        Finset.mem_union_right _ ((G.mem_neighborFinset y x).mpr hxy.symm)
      have hymem : y ∈ (G.neighborFinset x ∪ G.neighborFinset y).erase x :=
        Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_union_left _ ((G.mem_neighborFinset x y).mpr hxy)⟩
      have h1 := Finset.card_erase_add_one hymem
      have h2 := Finset.card_erase_add_one hxmem
      have hinter : G.neighborFinset x ∩ G.neighborFinset y = {u} := by
        ext z
        simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
        exact ⟨huniq z, fun hz => hz ▸ ⟨hxu, hyu⟩⟩
      have hcu := Finset.card_union_add_card_inter (G.neighborFinset x) (G.neighborFinset y)
      rw [hinter, Finset.card_singleton, G.card_neighborFinset_eq_degree,
        G.card_neighborFinset_eq_degree] at hcu
      omega
    have hXge : 3 ≤ H.degree X := by rw [hC x, hC y] at hXdeg; omega
    have hnear : Near H := by
      refine ⟨⟨X, hXge⟩, ⟨U, fun v hv => ?_⟩⟩
      by_cases hvX : v = X
      · rw [hvX]; exact hXge
      · rw [identify_degree_other_of_not_common G hne v (fun h => hvX (Subtype.ext h))
          (fun hcom => hv (Subtype.ext (huniq v.1 hcom))), hC]
    have hpow : HasPower H := hm.2.2.1 _ H (card_sub_lt y) hnear
    obtain ⟨k, p, hk, hp, hplen⟩ := dyadic_path_of_identify hne hm.2.1 hpow
    obtain ⟨c, hc, hclen, hmem⟩ := fermat_cycle_of_path_and_edge hxy hk p hp hplen
    exact ⟨k, c, hk, hc, hclen, hmem⟩
  · push Not at htri
    exact fermat_cycle_of_non_triangle_edge G hm hxy (fun u h => htri u h.1 h.2)

/-- Bridgelessness of MinimalBad(G): every edge of any MinimalBad graph lies on a simple cycle
    (either a triangle or a (2^k + 1)-cycle). -/
theorem no_bridge_minimal_bad [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {x y : V} (hxy : G.Adj x y) :
    ∃ c : G.Walk x x, c.IsCycle ∧ s(x, y) ∈ c.edges := by
  by_cases htri : ∃ u, G.Adj x u ∧ G.Adj y u
  · obtain ⟨u, hxu, hyu⟩ := htri
    let c : G.Walk x x := .cons hxy (.cons hyu (.cons hxu.symm .nil))
    have hc : c.IsCycle := by
      apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      refine ⟨Walk.IsPath.mk' ?_, by simp [c]⟩
      simp [c, Walk.tail_cons, Walk.support_cons,
        G.ne_of_adj hyu, (G.ne_of_adj hxy).symm, (G.ne_of_adj hxu).symm]
    exact ⟨c, hc, by simp [c]⟩
  · push Not at htri
    obtain ⟨_, c, _, hc, _, hmem⟩ := fermat_cycle_of_non_triangle_edge G hm hxy (fun u h => htri u h.1 h.2)
    exact ⟨c, hc, hmem⟩

#print axioms dyadic_path_of_identify
#print axioms dyadic_path_of_dist_ge_three
#print axioms no_bipartite_minimal_bad
#print axioms dyadic_path_of_dist_two
#print axioms cubic_all_nonadj_dyadic_path
#print axioms fermat_cycle_of_non_triangle_edge
#print axioms cubic_fermat_cycle_of_edge
#print axioms no_bridge_minimal_bad

end E64Identification
