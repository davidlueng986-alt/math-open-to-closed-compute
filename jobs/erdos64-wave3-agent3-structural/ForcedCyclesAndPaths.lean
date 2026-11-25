import Core
import Leaves
import PairedShadow
import ClosedDefectCore

/-!
Erdos 64 (Wave 3, Agent #3): Forced Cycles & Paths Beyond Wave 2.
Proves three brand-new unconditional all-order theorems (standard axioms only):
1. `cubic_forbidden_edge_dyadic_path` & `cubic_two_distinct_exit_dyadic_paths`
2. `cubic_non_triangle_two_path_fermat_cycle`
3. `defect_three_path_dyadic_plus_two_cycle`
-/

namespace E64Wave3Forced
open SimpleGraph Erdos64Closure E64Core E64Leaves Erdos64Paired E64DefectCore
universe u

variable {V : Type u}

/-- Identify y into x in G (deleting y and redirecting y's incident edges to x). -/
def identify (G : SimpleGraph V) (x y : V) : SimpleGraph {v : V // v ≠ y} where
  Adj u v := u ≠ v ∧
    (G.Adj u.1 v.1 ∨ (u.1 = x ∧ G.Adj y v.1) ∨ (v.1 = x ∧ G.Adj u.1 y))
  symm := ⟨by
    rintro u v ⟨hne, h | ⟨hux, hyv⟩ | ⟨hvx, huy⟩⟩
    · exact ⟨hne.symm, Or.inl h.symm⟩
    · exact ⟨hne.symm, Or.inr (Or.inr ⟨hux, hyv.symm⟩)⟩
    · exact ⟨hne.symm, Or.inr (Or.inl ⟨hvx, huy.symm⟩)⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

/-- Lift a walk in `identify G x y` avoiding `x` back to `G`. -/
def liftAvoid {G : SimpleGraph V} {x y : V}
    {a b : {v : V // v ≠ y}} (p : (identify G x y).Walk a b)
    (havoid : ∀ v ∈ p.support, v.1 ≠ x) : G.Walk a.1 b.1 :=
  match p with
  | .nil => .nil
  | @Walk.cons _ _ u v _ huv q =>
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
  | cons _ _ ih => simp [liftAvoid, ih]

theorem support_liftAvoid {G : SimpleGraph V} {x y : V}
    {a b : {v : V // v ≠ y}} (p : (identify G x y).Walk a b)
    (havoid : ∀ v ∈ p.support, v.1 ≠ x) :
    (liftAvoid p havoid).support = p.support.map Subtype.val := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp [liftAvoid, ih]

theorem isPath_liftAvoid {G : SimpleGraph V} {x y : V}
    {a b : {v : V // v ≠ y}} (p : (identify G x y).Walk a b)
    (hp : p.IsPath) (havoid : ∀ v ∈ p.support, v.1 ≠ x) :
    (liftAvoid p havoid).IsPath := by
  apply Walk.IsPath.mk'
  rw [support_liftAvoid]
  exact (List.nodup_map_iff Subtype.val_injective).mpr hp.support_nodup

theorem cycle_of_path_and_apex {G : SimpleGraph V} {u a b : V}
    (midG : G.Walk a b) (hmid : midG.IsPath) (hpos : 1 ≤ midG.length)
    (hu : u ∉ midG.support) (hua : G.Adj u a) (hbu : G.Adj b u) :
    ∃ c : G.Walk u u, c.IsCycle ∧ c.length = midG.length + 2 := by
  let c : G.Walk u u := .cons hua (midG.append (.cons hbu .nil))
  have hlen : c.length = midG.length + 2 := by simp [c, Walk.length_append]
  have hsupp : c.support = u :: (midG.support ++ [u]) := by
    simp [c, Walk.support_cons, Walk.support_append]
  have htail : c.support.tail = midG.support ++ [u] := by rw [hsupp, List.tail_cons]
  have hnodup : c.support.tail.Nodup := by
    rw [htail]
    exact List.nodup_append'.mpr ⟨hmid.support_nodup, List.nodup_singleton u,
      fun z hz1 hz2 => hu ((List.mem_singleton.mp hz2) ▸ hz1)⟩
  have hnil : ¬ c.Nil := by
    intro h; have := Walk.length_eq_zero_iff.mpr h; omega
  have hc : c.IsCycle := by
    apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    refine ⟨Walk.IsPath.mk' ?_, by omega⟩
    rwa [Walk.support_tail_of_not_nil _ hnil]
  exact ⟨c, hc, hlen⟩

/-- Core Lifting Lemma for `identify G x y \ edge X U`:
    If `H = (identify G x y) \ edge ⟨x, hxy⟩ ⟨u, huy⟩` has a `2^k`-cycle (`k ≥ 2`)
    while `G` is power-free, then `G` contains a simple `x`-`y` path `p` of length `2^k`
    whose first step from `x` is to some `a ≠ u` (so `s(x, u) ∉ p.edges`). -/
theorem dyadic_path_of_identify_erase {G : SimpleGraph V} {x y u : V}
    (hxy : x ≠ y) (huy : u ≠ y) (hfree : ¬ HasPower G)
    (hpow : HasPower (identify G x y \ SimpleGraph.edge (⟨x, hxy⟩ : {v : V // v ≠ y}) ⟨u, huy⟩)) :
    ∃ (k : ℕ) (a : V) (hxa : G.Adj x a) (p : G.Walk x y),
      2 ≤ k ∧ a ≠ u ∧ p.IsPath ∧ p.length = 2 ^ k ∧
      s(x, a) ∈ p.edges ∧ s(x, u) ∉ p.edges := by
  classical
  let X : {v : V // v ≠ y} := ⟨x, hxy⟩
  let U : {v : V // v ≠ y} := ⟨u, huy⟩
  let H := identify G x y \ SimpleGraph.edge X U
  obtain ⟨k, v₀, c, hk, hc, hlen⟩ := hpow
  have hle : H ≤ identify G x y := sdiff_le
  have hge4 : 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide : 0 < 2) hk
  by_cases hmem : X ∈ c.support
  · let c' := c.rotate hmem
    have hc' : c'.IsCycle := hc.rotate hmem
    have hlen' : c'.length = 2 ^ k := by rw [Walk.length_rotate, hlen]
    cases hce : c' with
    | nil => rw [hce] at hlen'; simp at hlen'; omega
    | @cons _ a _ h₁ q =>
      have hqlen : q.length + 1 = 2 ^ k := by
        have := congrArg Walk.length hce; simp only [Walk.length_cons] at this; omega
      have hqpath : q.IsPath := by
        apply Walk.IsPath.mk'
        have hsn := hc'.support_nodup
        rw [hce, Walk.support_cons, List.tail_cons] at hsn
        exact hsn
      have hqrpath : q.reverse.IsPath := hqpath.reverse
      have hqrlen : q.reverse.length = q.length := Walk.length_reverse q
      cases hqre : q.reverse with
      | nil => rw [hqre] at hqrlen; simp at hqrlen; omega
      | @cons _ b _ h₂ r =>
        let midH : H.Walk a b := r.reverse
        let mid : (identify G x y).Walk a b := midH.mapLe hle
        have hmidlen : mid.length + 2 = 2 ^ k := by
          have := congrArg Walk.length hqre
          simp only [Walk.length_cons, hqrlen] at this
          have hml : mid.length = r.length := by
            simp [mid, midH, Walk.length_mapLe, Walk.length_reverse]
          omega
        have hmidpath : mid.IsPath := by
          have hrp : r.IsPath := by
            apply Walk.IsPath.mk'
            have hsn := hqrpath.support_nodup
            rw [hqre, Walk.support_cons, List.nodup_cons] at hsn
            exact hsn.2
          exact (Walk.isPath_mapLe hle).mpr hrp.reverse
        have hXnotr : X ∉ r.support := by
          have hsn := hqrpath.support_nodup
          rw [hqre, Walk.support_cons, List.nodup_cons] at hsn
          exact hsn.1
        have hXnotmid : ∀ v ∈ mid.support, v.1 ≠ x := by
          intro v hv hvx
          have hvX : v = X := Subtype.ext hvx
          rw [hvX] at hv
          have hs1 : mid.support = midH.support := Walk.support_mapLe hle midH
          have hs2 : midH.support = r.support.reverse := Walk.support_reverse r
          rw [hs1, hs2, List.mem_reverse] at hv
          exact hXnotr hv
        let midG := liftAvoid mid hXnotmid
        have hmidGpath : midG.IsPath := isPath_liftAvoid mid hmidpath hXnotmid
        have hmidGlen : midG.length = mid.length := length_liftAvoid mid hXnotmid
        have hxnot : x ∉ midG.support := by
          rw [support_liftAvoid]
          intro hm; obtain ⟨v, hv, hvx⟩ := List.mem_map.mp hm; exact hXnotmid v hv hvx
        have hynot : y ∉ midG.support := by
          rw [support_liftAvoid]
          intro hm; obtain ⟨v, _, hvy⟩ := List.mem_map.mp hm; exact v.2 hvy
        have haU : a ≠ U := by
          intro heq
          have hne : X ≠ U := H.ne_of_adj (heq ▸ h₁)
          have hnot := (SimpleGraph.sdiff_adj (identify G x y) (SimpleGraph.edge X U) X a).mp h₁
          exact hnot.2 ((SimpleGraph.edge_adj X U X a).mpr ⟨Or.inl ⟨rfl, heq⟩, hne⟩)
        have hbU : b ≠ U := by
          intro heq
          have hne : X ≠ U := H.ne_of_adj (heq ▸ h₂)
          have hnot := (SimpleGraph.sdiff_adj (identify G x y) (SimpleGraph.edge X U) X b).mp h₂
          exact hnot.2 ((SimpleGraph.edge_adj X U X b).mpr ⟨Or.inl ⟨rfl, heq⟩, hne⟩)
        have h1I : (identify G x y).Adj X a := hle h₁
        have h2I : (identify G x y).Adj X b := hle h₂
        have h1G : G.Adj x a.1 ∨ G.Adj y a.1 := by
          rcases h1I.2 with h | ⟨_, hy⟩ | ⟨hax, _⟩
          · exact Or.inl h
          · exact Or.inr hy
          · exact False.elim (h1I.1 (Subtype.ext hax.symm))
        have h2G : G.Adj b.1 x ∨ G.Adj b.1 y := by
          rcases h2I.2 with h | ⟨_, hy⟩ | ⟨hbx, _⟩
          · exact Or.inl h.symm
          · exact Or.inr hy.symm
          · exact False.elim (h2I.1 (Subtype.ext hbx.symm))
        have mkPath : ∀ {z₁ z₂ : V} (hz₁u : z₁ ≠ u) (hxz₁ : G.Adj x z₁) (hz₂y : G.Adj z₂ y)
            (w : G.Walk z₁ z₂), w.IsPath → w.length + 2 = 2 ^ k →
            x ∉ w.support → y ∉ w.support →
            ∃ (k : ℕ) (a : V) (hxa : G.Adj x a) (p : G.Walk x y),
              2 ≤ k ∧ a ≠ u ∧ p.IsPath ∧ p.length = 2 ^ k ∧
              s(x, a) ∈ p.edges ∧ s(x, u) ∉ p.edges := by
          intro z₁ z₂ hz₁u hxz₁ hz₂y w hw hwlen hxw hyw
          let p : G.Walk x y := .cons hxz₁ (w.append (.cons hz₂y .nil))
          have hplen : p.length = 2 ^ k := by simp [p, Walk.length_append]; omega
          have hpsupp : p.support = x :: (w.support ++ [y]) := by
            simp [p, Walk.support_cons, Walk.support_append]
          have hp : p.IsPath := by
            apply Walk.IsPath.mk'
            rw [hpsupp, List.nodup_cons]
            refine ⟨?_, List.nodup_append'.mpr ⟨hw.support_nodup, List.nodup_singleton y,
              fun z hz1 hz2 => hyw ((List.mem_singleton.mp hz2) ▸ hz1)⟩⟩
            intro hm
            rcases List.mem_append.mp hm with hm1 | hm2
            · exact hxw hm1
            · exact hxy (List.mem_singleton.mp hm2)
          have hmem_xa : s(x, z₁) ∈ p.edges := by simp [p]
          have hnmem_xu : s(x, u) ∉ p.edges := by
            intro hmem
            simp only [p, Walk.edges_cons, Walk.edges_append, Walk.edges_nil, List.mem_cons,
              List.mem_append] at hmem
            rcases hmem with heq | hmemw | hmemy
            · rcases Sym2.eq_iff.mp heq with ⟨_, h2⟩ | ⟨h1, _⟩
              · exact hz₁u h2.symm
              · exact (G.ne_of_adj hxz₁) h1
            · exact hxw (Walk.fst_mem_support_of_mem_edges w (Sym2.mem_mk_left x u) hmemw)
            · rcases List.mem_singleton.mp hmemy with heq
              rcases Sym2.eq_iff.mp heq with ⟨h1, _⟩ | ⟨_, h2⟩
              · exact hxw (h1 ▸ Walk.end_mem_support w)
              · exact hxy h2
          exact ⟨k, z₁, hxz₁, p, hk, hz₁u, hp, hplen, hmem_xa, hnmem_xu⟩
        rcases h1G with hxa | hya <;> rcases h2G with hbx | hby
        · obtain ⟨d, hd, hdl⟩ := cycle_of_path_and_apex midG hmidGpath (by omega) hxnot hxa hbx
          exact False.elim (hfree ⟨k, x, d, hk, hd, by omega⟩)
        · exact mkPath (fun h => haU (Subtype.ext h)) hxa hby midG hmidGpath (by omega) hxnot hynot
        · exact mkPath (fun h => hbU (Subtype.ext h)) hbx.symm hya.symm midG.reverse hmidGpath.reverse
            (by rw [Walk.length_reverse]; omega)
            (by rw [Walk.support_reverse, List.mem_reverse]; exact hxnot)
            (by rw [Walk.support_reverse, List.mem_reverse]; exact hynot)
        · obtain ⟨d, hd, hdl⟩ := cycle_of_path_and_apex midG hmidGpath (by omega) hynot hya hby
          exact False.elim (hfree ⟨k, y, d, hk, hd, by omega⟩)
  · have havoid : ∀ v ∈ (c.mapLe hle).support, v.1 ≠ x := by
      intro v hv hvx
      rw [Walk.support_mapLe] at hv
      exact hmem (Subtype.ext hvx ▸ hv)
    let d := liftAvoid (c.mapLe hle) havoid
    have hdlen : d.length = 2 ^ k := by rw [length_liftAvoid, Walk.length_mapLe, hlen]
    have hdtail : d.support.tail.Nodup := by
      have hs : d.support = c.support.map Subtype.val := by
        rw [support_liftAvoid, Walk.support_mapLe]
      rw [hs, List.map_tail]
      exact (List.nodup_map_iff Subtype.val_injective).mpr hc.support_nodup
    have hdnil : ¬ d.Nil := by
      intro h; have := Walk.length_eq_zero_iff.mpr h; omega
    have hdc : d.IsCycle := by
      apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      refine ⟨Walk.IsPath.mk' ?_, by omega⟩
      rwa [Walk.support_tail_of_not_nil _ hdnil]
    exact False.elim (hfree ⟨k, v₀.1, d, hk, hdc, hdlen⟩)

theorem card_sub_lt [Fintype V] [DecidableEq V] (y : V) :
    Fintype.card {v : V // v ≠ y} < Fintype.card V := by
  have h : Fintype.card {v : V // v ≠ y} + 1 = Fintype.card V := by
    rw [Fintype.card_subtype,
      show (Finset.univ.filter (fun v : V => v ≠ y)) = Finset.univ.erase y by ext z; simp]
    exact Finset.card_erase_add_one (Finset.mem_univ y)
  omega

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
        rcases u.2.2 with h1 | ⟨_, hyv⟩ | ⟨hvx', _⟩
        · exact False.elim (h (hu ▸ h1))
        · exact hyv.symm
        · exact False.elim (hvx hvx')⟩
    else ⟨u.1.1, by
      rcases u.2.2 with h1 | ⟨hux, _⟩ | ⟨hvx', _⟩
      · exact h1
      · exact False.elim (hu hux)
      · exact False.elim (hvx hvx')⟩
  let g : G.neighborSet v.1 → H.neighborSet v := fun u =>
    if hu : u.1 = y then
      ⟨X, ⟨fun h => hvx (congrArg Subtype.val h), Or.inr (Or.inl ⟨rfl, hu ▸ u.2.symm⟩)⟩⟩
    else
      ⟨⟨u.1, hu⟩, ⟨fun h => (G.ne_of_adj u.2) (congrArg Subtype.val h), Or.inl u.2⟩⟩
  have e : H.neighborSet v ≃ G.neighborSet v.1 :=
    { toFun := f
      invFun := g
      left_inv := by
        intro u; apply Subtype.ext
        by_cases hux : u.1.1 = x
        · by_cases hvxa : G.Adj v.1 x
          · apply Subtype.ext; simp [f, g, hux, hvxa, hxy]
          · apply Subtype.ext; simp [f, g, hux, hvxa, X]
        · have huy : u.1.1 ≠ y := u.1.2
          simp [f, g, hux, huy]
      right_inv := by
        intro u; apply Subtype.ext
        by_cases huy : u.1 = y
        · have hnvx : ¬ G.Adj v.1 x := fun h => hnc ⟨h.symm, (huy ▸ u.2).symm⟩
          simp [f, g, huy, hnvx, X]
        · by_cases hux : u.1 = x
          · have hvxa : G.Adj v.1 x := hux ▸ u.2
            simp [f, g, huy, hux, hvxa]
          · simp [f, g, huy, hux] }
  have hc := Fintype.card_congr e
  rwa [SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.card_neighborSet_eq_degree] at hc

theorem identify_degree_merged [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {x y : V} (hxy : x ≠ y)
    [DecidableRel (identify G x y).Adj] :
    (identify G x y).degree ⟨x, hxy⟩ =
      ((G.neighborFinset x ∪ G.neighborFinset y).erase x |>.erase y).card := by
  classical
  let H := identify G x y
  let X : {z : V // z ≠ y} := ⟨x, hxy⟩
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
  have hc := Fintype.card_congr e
  simpa only [Fintype.card_coe] using hc

/-- NEW THEOREM 1 (Wave 3, Agent #3): Cubic Forbidden-Edge Dyadic Path Theorem.
    In EVERY cubic MinimalBad(G), for every x ≠ y at distance ≥ 3 and every neighbor u of x,
    G contains a simple x-y path of length 2^k (k ≥ 2) avoiding the edge s(x, u). -/
theorem cubic_forbidden_edge_dyadic_path [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G) (hC : Cubic G)
    {x y u : V} (hxy : x ≠ y) (hnadj : ¬ G.Adj x y)
    (hnocom : ∀ z, ¬ (G.Adj x z ∧ G.Adj y z)) (hxu : G.Adj x u) :
    ∃ (k : ℕ) (a : V) (_ : G.Adj x a) (p : G.Walk x y),
      2 ≤ k ∧ a ≠ u ∧ p.IsPath ∧ p.length = 2 ^ k ∧
      s(x, a) ∈ p.edges ∧ s(x, u) ∉ p.edges := by
  classical
  have huy : u ≠ y := fun h => hnadj (h ▸ hxu)
  let X : {v : V // v ≠ y} := ⟨x, hxy⟩
  let U : {v : V // v ≠ y} := ⟨u, huy⟩
  let I := identify G x y
  let H := I \ SimpleGraph.edge X U
  have hXU : I.Adj X U := ⟨fun h => (G.ne_of_adj hxu) (congrArg Subtype.val h), Or.inl hxu⟩
  have hIX : I.degree X = 6 := by
    rw [identify_degree_merged G hxy]
    have hdisj : Disjoint (G.neighborFinset x) (G.neighborFinset y) := by
      rw [Finset.disjoint_left]
      intro z hzx hzy
      exact hnocom z ⟨(G.mem_neighborFinset x z).mp hzx, (G.mem_neighborFinset y z).mp hzy⟩
    have hxnot : x ∉ G.neighborFinset x ∪ G.neighborFinset y := by
      intro h
      rcases Finset.mem_union.mp h with h1 | h2
      · exact G.loopless x ((G.mem_neighborFinset x x).mp h1)
      · exact hnadj ((G.mem_neighborFinset y x).mp h2).symm
    have hynot : y ∉ (G.neighborFinset x ∪ G.neighborFinset y).erase x := by
      intro h
      rcases Finset.mem_union.mp (Finset.mem_erase.mp h).2 with h1 | h2
      · exact hnadj ((G.mem_neighborFinset x y).mp h1)
      · exact G.loopless y ((G.mem_neighborFinset y y).mp h2)
    rw [Finset.erase_eq_of_notMem hynot, Finset.erase_eq_of_notMem hxnot,
      Finset.card_union_of_disjoint hdisj,
      G.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree, hC x, hC y]
  have hHX : H.degree X = 5 := by
    have hd := erase_edge_degree I X U hXU X
    simp only [true_or, ite_true] at hd
    change H.degree X + 1 = I.degree X at hd
    omega
  have hnear : Near H := by
    refine ⟨⟨X, by omega⟩, ⟨U, fun v hv => ?_⟩⟩
    by_cases hvX : v = X
    · rw [hvX]; omega
    · have hd := erase_edge_degree I X U hXU v
      simp only [hvX, hv, or_self, ite_false, add_zero] at hd
      change H.degree v = I.degree v at hd
      rw [hd, identify_degree_other_of_not_common G hxy v (fun h => hvX (Subtype.ext h)) (hnocom v.1), hC]
  have hpow : HasPower H := hm.2.2.1 _ H (card_sub_lt y) hnear
  exact dyadic_path_of_identify_erase hxy huy hm.2.1 hpow

/-- COROLLARY: Every pair x, y at distance ≥ 3 in cubic MinimalBad(G) has TWO simple dyadic
    x-y paths whose first edges at x are distinct. -/
theorem cubic_two_distinct_exit_dyadic_paths [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G) (hC : Cubic G)
    {x y : V} (hxy : x ≠ y) (hnadj : ¬ G.Adj x y)
    (hnocom : ∀ z, ¬ (G.Adj x z ∧ G.Adj y z)) :
    ∃ (a₁ a₂ : V) (k₁ k₂ : ℕ) (p₁ p₂ : G.Walk x y),
      a₁ ≠ a₂ ∧ 2 ≤ k₁ ∧ 2 ≤ k₂ ∧ p₁.IsPath ∧ p₂.IsPath ∧
      p₁.length = 2 ^ k₁ ∧ p₂.length = 2 ^ k₂ ∧
      s(x, a₁) ∈ p₁.edges ∧ s(x, a₂) ∈ p₂.edges := by
  have hpos : 0 < G.degree x := by rw [hC x]; omega
  obtain ⟨u, hxu⟩ := (G.degree_pos_iff_exists_adj x).mp hpos
  obtain ⟨k₁, a₁, hxa₁, p₁, hk₁, _, hp₁, hl₁, hmem₁, _⟩ :=
    cubic_forbidden_edge_dyadic_path G hm hC hxy hnadj hnocom hxu
  obtain ⟨k₂, a₂, _, p₂, hk₂, ha₂ne, hp₂, hl₂, hmem₂, _⟩ :=
    cubic_forbidden_edge_dyadic_path G hm hC hxy hnadj hnocom hxa₁
  exact ⟨a₁, a₂, k₁, k₂, p₁, p₂, ha₂ne.symm, hk₁, hk₂, hp₁, hp₂, hl₁, hl₂, hmem₁, hmem₂⟩

/-- NEW THEOREM 2 (Wave 3, Agent #3): Universal Non-Triangle P3 Fermat-Cycle Theorem.
    In EVERY cubic MinimalBad(G) (hence EVERY 2-path in C-N-R, C-N-2, C-N-3),
    every 2-path a - x - y where xy is not in a triangle lies on a simple cycle of length
    2^k + 1 (k ≥ 2) containing both s(a, x) and s(x, y). -/
theorem cubic_non_triangle_two_path_fermat_cycle [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G) (hC : Cubic G)
    {a x y : V} (hax : G.Adj a x) (hxy : G.Adj x y) (hay : a ≠ y)
    (hntri : ∀ z, ¬ (G.Adj x z ∧ G.Adj y z)) :
    ∃ (k : ℕ) (c : G.Walk x x), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k + 1 ∧
      s(a, x) ∈ c.edges ∧ s(x, y) ∈ c.edges := by
  classical
  have hne : x ≠ y := G.ne_of_adj hxy
  have hex_u : ∃ u : V, G.Adj x u ∧ u ≠ a ∧ u ≠ y := by
    by_contra h
    push Not at h
    have hsub : G.neighborFinset x ⊆ ({a, y} : Finset V) := by
      intro z hz
      have hxz := (G.mem_neighborFinset x z).mp hz
      by_cases hza : z = a
      · simp [hza]
      · simp [h z hxz hza]
    have hc := Finset.card_le_card hsub
    have h2 : ({a, y} : Finset V).card ≤ 2 := Finset.card_le_two
    rw [G.card_neighborFinset_eq_degree, hC x] at hc
    omega
  obtain ⟨u, hxu, hua, huy⟩ := hex_u
  let X : {v : V // v ≠ y} := ⟨x, hne⟩
  let U : {v : V // v ≠ y} := ⟨u, huy⟩
  let I := identify G x y
  let H := I \ SimpleGraph.edge X U
  have hXU : I.Adj X U := ⟨fun h => (G.ne_of_adj hxu) (congrArg Subtype.val h), Or.inl hxu⟩
  have hIX : I.degree X = 4 := by
    rw [identify_degree_merged G hne]
    have hdisj : Disjoint (G.neighborFinset x) (G.neighborFinset y) := by
      rw [Finset.disjoint_left]
      intro z hzx hzy
      exact hntri z ⟨(G.mem_neighborFinset x z).mp hzx, (G.mem_neighborFinset y z).mp hzy⟩
    have hxmem : x ∈ G.neighborFinset x ∪ G.neighborFinset y :=
      Finset.mem_union_right _ ((G.mem_neighborFinset y x).mpr hxy.symm)
    have hymem : y ∈ (G.neighborFinset x ∪ G.neighborFinset y).erase x :=
      Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_union_left _ ((G.mem_neighborFinset x y).mpr hxy)⟩
    have h1 := Finset.card_erase_add_one hymem
    have h2 := Finset.card_erase_add_one hxmem
    rw [Finset.card_union_of_disjoint hdisj,
      G.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree, hC x, hC y] at h2
    omega
  have hHX : H.degree X = 3 := by
    have hd := erase_edge_degree I X U hXU X
    simp only [true_or, ite_true] at hd
    change H.degree X + 1 = I.degree X at hd
    omega
  have hnear : Near H := by
    refine ⟨⟨X, by omega⟩, ⟨U, fun v hv => ?_⟩⟩
    by_cases hvX : v = X
    · rw [hvX]; omega
    · have hd := erase_edge_degree I X U hXU v
      simp only [hvX, hv, or_self, ite_false, add_zero] at hd
      change H.degree v = I.degree v at hd
      rw [hd, identify_degree_other_of_not_common G hne v (fun h => hvX (Subtype.ext h)) (hntri v.1), hC]
  have hpow : HasPower H := hm.2.2.1 _ H (card_sub_lt y) hnear
  obtain ⟨k, a', hxa', p, hk, ha'u, hp, hplen, hmem_xa', _⟩ :=
    dyadic_path_of_identify_erase hne huy hm.2.1 hpow
  have ha'y : a' ≠ y := by
    intro h
    subst h
    cases hp_eq : p with
    | nil => exact hne rfl
    | @cons _ z _ hxz q =>
      have hge4 : 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide : 0 < 2) hk
      have hqlen : q.length + 1 = 2 ^ k := by
        have := congrArg Walk.length hp_eq; simp only [Walk.length_cons] at this; omega
      have hmem' : s(x, y) ∈ (Walk.cons hxz q).edges := hp_eq ▸ hmem_xa'
      simp only [Walk.edges_cons, List.mem_cons] at hmem'
      rcases hmem' with heq | hmemq
      · rcases Sym2.eq_iff.mp heq with ⟨_, hzy⟩ | ⟨hxy', _⟩
        · subst hzy
          have hsn := (hp_eq ▸ hp).support_nodup
          rw [Walk.support_cons, List.nodup_cons] at hsn
          have hqnil : q.Nil := by
            cases hqe : q with
            | nil => exact Walk.Nil.nil
            | cons _ _ =>
              have hsn2 := hsn.2
              rw [hqe, Walk.support_cons, List.nodup_cons] at hsn2
              exact False.elim (hsn2.1 (Walk.end_mem_support _))
          have := Walk.length_eq_zero_iff.mpr hqnil
          omega
        · exact hne hxy'
      · have hxmemq : x ∈ q.support := Walk.fst_mem_support_of_mem_edges q (Sym2.mem_mk_left x y) hmemq
        have hsn := (hp_eq ▸ hp).support_nodup
        rw [Walk.support_cons, List.nodup_cons] at hsn
        exact hsn.1 hxmemq
  have ha'_eq_a : a' = a := by
    by_contra hne_a
    have hsub : ({a, y, u, a'} : Finset V) ⊆ G.neighborFinset x := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      apply (G.mem_neighborFinset x z).mpr
      rcases hz with rfl | rfl | rfl | rfl
      · exact hax.symm
      · exact hxy
      · exact hxu
      · exact hxa'
    have hcard4 : ({a, y, u, a'} : Finset V).card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [ha'u.symm]
      · simp [huy.symm, ha'y.symm]
      · simp [hay, hua.symm, Ne.symm hne_a]
    have hc := Finset.card_le_card hsub
    rw [hcard4, G.card_neighborFinset_eq_degree, hC x] at hc
    omega
  subst a'
  let c : G.Walk x x := p.append (.cons hxy.symm .nil)
  have hclen : c.length = 2 ^ k + 1 := by simp [c, Walk.length_append, hplen]
  have hge4 : 4 ≤ p.length := by rw [hplen]; exact Nat.pow_le_pow_right (by decide : 0 < 2) hk
  have hsupp : c.support = p.support ++ [x] := by simp [c, Walk.support_append]
  have htail_nodup : c.support.tail.Nodup := by
    have hps : p.support = x :: p.support.tail := (p.cons_tail_support).symm
    have htail : c.support.tail = p.support.tail ++ [x] := by
      calc c.support.tail = (p.support ++ [x]).tail := by rw [hsupp]
        _ = (x :: p.support.tail ++ [x]).tail := by rw [hps]
        _ = p.support.tail ++ [x] := rfl
    have hpn := hp.support_nodup
    rw [hps, List.nodup_cons] at hpn
    rw [htail]
    exact List.nodup_append'.mpr ⟨hpn.2, List.nodup_singleton x,
      fun z hz1 hz2 => hpn.1 ((List.mem_singleton.mp hz2) ▸ hz1)⟩
  have hcnil : ¬ c.Nil := by intro h; have := Walk.length_eq_zero_iff.mpr h; omega
  have hc : c.IsCycle := by
    apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    refine ⟨Walk.IsPath.mk' ?_, by omega⟩
    rwa [Walk.support_tail_of_not_nil _ hcnil]
  have hmem_ax : s(a, x) ∈ c.edges := by
    simp only [c, Walk.edges_append, List.mem_append]
    exact Or.inl (Sym2.eq_swap ▸ hmem_xa')
  have hmem_xy : s(x, y) ∈ c.edges := by
    simp only [c, Walk.edges_append, Walk.edges_cons, Walk.edges_nil, List.mem_append, List.mem_cons]
    exact Or.inr (Or.inl Sym2.eq_swap)
  exact ⟨k, c, hk, hc, hclen, hmem_ax, hmem_xy⟩

/-- NEW THEOREM 3 (Wave 3, Agent #3): Defect-Centered P4 (2^k + 2)-Cycle Theorem.
    In ANY MinimalBad(G) with degree-2 defect w whose neighbors a, b are non-adjacent
    (all of S-N-2, S-N-3, H-N-2, H-N-3, S-T-3, H-T-3), for every neighbor a₁ ≠ w of a,
    there exists a simple cycle of length 2^k + 2 (k ≥ 2) containing the 3-path a₁ - a - w - b. -/
theorem defect_three_path_dyadic_plus_two_cycle [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {w a b a₁ : V} (hw : G.degree w = 2)
    (hwa : G.Adj w a) (hwb : G.Adj w b) (hab_ne : a ≠ b) (hnab : ¬ G.Adj a b)
    (haa₁ : G.Adj a a₁) (ha₁w : a₁ ≠ w) :
    ∃ (k : ℕ) (c : G.Walk a a), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k + 2 ∧
      s(a₁, a) ∈ c.edges ∧ s(a, w) ∈ c.edges ∧ s(w, b) ∈ c.edges := by
  classical
  have hda : G.degree a = 3 := defect_neighbor_cubic G hm hw hwa
  have hdb : G.degree b = 3 := defect_neighbor_cubic G hm hw hwb
  have haw : a ≠ w := (G.ne_of_adj hwa).symm
  have hbw : b ≠ w := (G.ne_of_adj hwb).symm
  have hex_a₂ : ∃ a₂ : V, G.Adj a a₂ ∧ a₂ ≠ w ∧ a₂ ≠ a₁ := by
    by_contra h
    push Not at h
    have hsub : G.neighborFinset a ⊆ ({w, a₁} : Finset V) := by
      intro z hz
      have haz := (G.mem_neighborFinset a z).mp hz
      by_cases hzw : z = w
      · simp [hzw]
      · simp [h z haz hzw]
    have hc := Finset.card_le_card hsub
    have h2 : ({w, a₁} : Finset V).card ≤ 2 := Finset.card_le_two
    rw [G.card_neighborFinset_eq_degree, hda] at hc
    omega
  obtain ⟨a₂, haa₂, ha₂w, ha₂a₁⟩ := hex_a₂
  have ha₂b : a₂ ≠ b := fun h => hnab (h ▸ haa₂)
  let V₁ := {v : V // v ≠ w}
  let G₁ : SimpleGraph V₁ := G.induce {v | v ≠ w}
  let A : V₁ := ⟨a, haw⟩
  let B : V₁ := ⟨b, hbw⟩
  let A₁ : V₁ := ⟨a₁, ha₁w⟩
  let A₂ : V₁ := ⟨a₂, ha₂w⟩
  have hAB : A ≠ B := fun h => hab_ne (congrArg Subtype.val h)
  have hA₂B : A₂ ≠ B := fun h => ha₂b (congrArg Subtype.val h)
  have hG₁_free : ¬ HasPower G₁ := fun hp => hm.2.1 (power_induce G {v | v ≠ w} hp)
  have hnocom₁ : ∀ z : V₁, ¬ (G₁.Adj A z ∧ G₁.Adj B z) := by
    rintro z ⟨haz, hbz⟩
    have hazG : G.Adj a z.1 := haz
    have hbzG : G.Adj b z.1 := hbz
    exact hm.2.1 (rectangle_power G (G.ne_of_adj hwa) z.2.symm (G.ne_of_adj hwb)
      (G.ne_of_adj hazG) hab_ne (G.ne_of_adj hbzG).symm hwa hazG hbzG.symm hwb.symm)
  have hdegG₁ : ∀ v : V₁, G₁.degree v + (if G.Adj v.1 w then 1 else 0) = G.degree v.1 :=
    fun v => induce_delete_degree G w v
  have hG₁_A : G₁.degree A = 2 := by
    have := hdegG₁ A; simp [A, hwa.symm, hda] at this; omega
  have hG₁_B : G₁.degree B = 2 := by
    have := hdegG₁ B; simp [B, hwb.symm, hdb] at this; omega
  have hG₁_other : ∀ v : V₁, v ≠ A → v ≠ B → 3 ≤ G₁.degree v := by
    intro v hvA hvB
    have hna : ¬ G.Adj v.1 w := by
      intro hvw
      have hsub : ({a, b, v.1} : Finset V) ⊆ G.neighborFinset w := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        apply (G.mem_neighborFinset w z).mpr
        rcases hz with rfl | rfl | rfl
        · exact hwa
        · exact hwb
        · exact hvw.symm
      have hbv_ne : b ≠ v.1 := fun h => hvB (Subtype.ext h.symm)
      have hav_ne : a ≠ v.1 := fun h => hvA (Subtype.ext h.symm)
      have h3 : ({a, b, v.1} : Finset V).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp [hbv_ne]
        · simp [hab_ne, hav_ne]
      have hc := Finset.card_le_card hsub
      rw [h3, G.card_neighborFinset_eq_degree, hw] at hc
      omega
    have hd := hdegG₁ v
    simp only [hna, ite_false, add_zero] at hd
    obtain ⟨_, r, hr⟩ := hm.1
    have hrw : r = w := by by_contra h; have := hr w (Ne.symm h); omega
    rw [hd]
    exact hr v.1 (hrw ▸ v.2)
  let X : {v : V₁ // v ≠ B} := ⟨A, hAB⟩
  let U : {v : V₁ // v ≠ B} := ⟨A₂, hA₂B⟩
  let I := identify G₁ A B
  let H := I \ SimpleGraph.edge X U
  have hXU : I.Adj X U := ⟨fun h => (G.ne_of_adj haa₂) (congrArg (fun z => z.1.1) h), Or.inl haa₂⟩
  have hIX : I.degree X = 4 := by
    rw [identify_degree_merged G₁ hAB]
    have hdisj : Disjoint (G₁.neighborFinset A) (G₁.neighborFinset B) := by
      rw [Finset.disjoint_left]
      intro z hzA hzB
      exact hnocom₁ z ⟨(G₁.mem_neighborFinset A z).mp hzA, (G₁.mem_neighborFinset B z).mp hzB⟩
    have hAnot : A ∉ G₁.neighborFinset A ∪ G₁.neighborFinset B := by
      intro h
      rcases Finset.mem_union.mp h with h1 | h2
      · exact G₁.loopless A ((G₁.mem_neighborFinset A A).mp h1)
      · exact hnab ((G₁.mem_neighborFinset B A).mp h2).symm
    have hBnot : B ∉ (G₁.neighborFinset A ∪ G₁.neighborFinset B).erase A := by
      intro h
      rcases Finset.mem_union.mp (Finset.mem_erase.mp h).2 with h1 | h2
      · exact hnab ((G₁.mem_neighborFinset A B).mp h1)
      · exact G₁.loopless B ((G₁.mem_neighborFinset B B).mp h2)
    rw [Finset.erase_eq_of_notMem hBnot, Finset.erase_eq_of_notMem hAnot,
      Finset.card_union_of_disjoint hdisj,
      G₁.card_neighborFinset_eq_degree, G₁.card_neighborFinset_eq_degree, hG₁_A, hG₁_B]
  have hHX : H.degree X = 3 := by
    have hd := erase_edge_degree I X U hXU X
    simp only [true_or, ite_true] at hd
    change H.degree X + 1 = I.degree X at hd
    omega
  have hnear : Near H := by
    refine ⟨⟨X, by omega⟩, ⟨U, fun v hv => ?_⟩⟩
    by_cases hvX : v = X
    · rw [hvX]; omega
    · have hd := erase_edge_degree I X U hXU v
      simp only [hvX, hv, or_self, ite_false, add_zero] at hd
      change H.degree v = I.degree v at hd
      rw [hd, identify_degree_other_of_not_common G₁ hAB v (fun h => hvX (Subtype.ext h)) (hnocom₁ v.1)]
      exact hG₁_other v.1 (fun h => hvX (Subtype.ext h)) v.2
  have hcard_lt : Fintype.card {v : V₁ // v ≠ B} < Fintype.card V :=
    (card_sub_lt B).trans (card_sub_lt w)
  have hpow : HasPower H := hm.2.2.1 _ H hcard_lt hnear
  obtain ⟨k, Z, hAZ, p₁, hk, hZU, hp₁, hp₁len, hmem_AZ, _⟩ :=
    dyadic_path_of_identify_erase hAB hA₂B hG₁_free hpow
  have hZ_eq : Z = A₁ := by
    by_contra hne_A₁
    have hsub : ({w, a₁, a₂, Z.1} : Finset V) ⊆ G.neighborFinset a := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      apply (G.mem_neighborFinset a z).mpr
      rcases hz with rfl | rfl | rfl | rfl
      · exact hwa.symm
      · exact haa₁
      · exact haa₂
      · exact hAZ
    have ha₂Z : a₂ ≠ Z.1 := fun h => hZU (Subtype.ext h.symm)
    have ha₁Z : a₁ ≠ Z.1 := fun h => hne_A₁ (Subtype.ext h.symm)
    have h4 : ({w, a₁, a₂, Z.1} : Finset V).card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [ha₂Z]
      · simp [ha₂a₁.symm, ha₁Z]
      · simp [ha₁w.symm, ha₂w.symm, Z.2.symm]
    have hc := Finset.card_le_card hsub
    rw [h4, G.card_neighborFinset_eq_degree, hda] at hc
    omega
  subst Z
  let f : G₁ →g G := ⟨Subtype.val, fun h => h⟩
  let pG : G.Walk a b := p₁.map f
  have hpG_path : pG.IsPath := (Walk.isPath_map_iff_of_injective Subtype.val_injective).mpr hp₁
  have hpG_len : pG.length = 2 ^ k := by rw [Walk.length_map, hp₁len]
  have hwnot : w ∉ pG.support := by
    rw [Walk.support_map]
    intro hm; obtain ⟨v, _, hvw⟩ := List.mem_map.mp hm; exact v.2 hvw
  let c : G.Walk a a := pG.append (.cons hwb.symm (.cons hwa .nil))
  have hclen : c.length = 2 ^ k + 2 := by simp [c, Walk.length_append, hpG_len]
  have hge4 : 4 ≤ pG.length := by rw [hpG_len]; exact Nat.pow_le_pow_right (by decide : 0 < 2) hk
  have hsupp : c.support = pG.support ++ [w, a] := by simp [c, Walk.support_append]
  have htail_nodup : c.support.tail.Nodup := by
    have hps : pG.support = a :: pG.support.tail := (pG.cons_tail_support).symm
    have htail : c.support.tail = pG.support.tail ++ [w, a] := by
      calc c.support.tail = (pG.support ++ [w, a]).tail := by rw [hsupp]
        _ = (a :: pG.support.tail ++ [w, a]).tail := by rw [hps]
        _ = pG.support.tail ++ [w, a] := rfl
    have hpn := hpG_path.support_nodup
    rw [hps, List.nodup_cons] at hpn
    rw [htail]
    refine List.nodup_append'.mpr ⟨hpn.2, ?_, ?_⟩
    · simp [haw.symm]
    · intro z hz1 hz2
      simp only [List.mem_cons, List.mem_singleton] at hz2
      rcases hz2 with rfl | rfl
      · exact hwnot (List.mem_of_mem_tail hz1)
      · exact hpn.1 hz1
  have hcnil : ¬ c.Nil := by intro h; have := Walk.length_eq_zero_iff.mpr h; omega
  have hc : c.IsCycle := by
    apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    refine ⟨Walk.IsPath.mk' ?_, by omega⟩
    rwa [Walk.support_tail_of_not_nil _ hcnil]
  have hmem_a₁a : s(a₁, a) ∈ c.edges := by
    simp only [c, Walk.edges_append, List.mem_append]
    left
    have hm1 : s(a, a₁) ∈ pG.edges := by
      rw [Walk.edges_map]
      exact List.mem_map.mpr ⟨s(A, A₁), hmem_AZ, rfl⟩
    exact Sym2.eq_swap ▸ hm1
  have hmem_aw : s(a, w) ∈ c.edges := by
    simp only [c, Walk.edges_append, Walk.edges_cons, Walk.edges_nil, List.mem_append, List.mem_cons]
    exact Or.inr (Or.inr (Or.inl Sym2.eq_swap))
  have hmem_wb : s(w, b) ∈ c.edges := by
    simp only [c, Walk.edges_append, Walk.edges_cons, Walk.edges_nil, List.mem_append, List.mem_cons]
    exact Or.inr (Or.inl Sym2.eq_swap)
  exact ⟨k, c, hk, hc, hclen, hmem_a₁a, hmem_aw, hmem_wb⟩

#print axioms dyadic_path_of_identify_erase
#print axioms cubic_forbidden_edge_dyadic_path
#print axioms cubic_two_distinct_exit_dyadic_paths
#print axioms cubic_non_triangle_two_path_fermat_cycle
#print axioms defect_three_path_dyadic_plus_two_cycle

end E64Wave3Forced
