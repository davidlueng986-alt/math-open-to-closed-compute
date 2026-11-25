import Leaves
import PairedShadow
import TriangleCut
import ClosedDefectCore
import Descent

/-!
Erdős #64 Wave 2 (Agent #2): All-order structural theorems on `MinimalBad` graphs.
Verified in Lean 4.36.0 (standard axioms only, no `sorry`, no `native_decide`).

Theorems proved in this module:
1. `no_c4_of_minimal_bad` & `common_neighbor_unique`
2. `high_degree_independent` (V_{>=4} is an independent set in every MinimalBad graph)
3. `no_defect_triangle_without_2cut` (no defect-triangle in S-T-3 or H-T-3)
4. `universal_dyadic_path` (dist >= 3 implies simple x-y path of length 2^k, k >= 2)
5. `unified_bipartite_exclusion` (single unified exclusion of all 6 bipartite leaves)
6. `cubic_nonadj_dyadic_path` (in cubic MinimalBad, EVERY non-edge has a simple 2^k-path avoiding any common neighbor)
7. `cubic_two_path_dyadic_plus_two_cycle` (every non-triangle 2-path in cubic MinimalBad lies on a (2^k + 2)-cycle)
8. `cubic_edge_dyadic_plus_one_cycle` (every edge in cubic MinimalBad lies on a (2^k + 1)-cycle)
-/

namespace E64Wave2Structural
open SimpleGraph Erdos64Closure E64Core E64Leaves Erdos64Paired
universe u

/-! ### 1. C4-freeness and unique common neighbors -/

theorem no_c4_of_minimal_bad {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {a b c d : V} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (e1 : G.Adj a b) (e2 : G.Adj b c) (e3 : G.Adj c d) (e4 : G.Adj d a) : False :=
  hm.2.1 (rectangle_power G hab hac had hbc hbd hcd e1 e2 e3 e4)

theorem common_neighbor_unique {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {x y u v : V} (hxy : x ≠ y)
    (hxu : G.Adj x u) (hyu : G.Adj y u)
    (hxv : G.Adj x v) (hyv : G.Adj y v) : u = v := by
  by_contra huv
  exact no_c4_of_minimal_bad G hm
    (G.ne_of_adj hxu) hxy (G.ne_of_adj hxv)
    (G.ne_of_adj hyu).symm huv (G.ne_of_adj hyv)
    hxu hyu.symm hyv hxv.symm

/-! ### 2. High-degree vertices form an independent set -/

theorem high_degree_independent {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {a b : V} (ha : 4 ≤ G.degree a) (hb : 4 ≤ G.degree b) : ¬G.Adj a b := by
  classical
  intro hab
  obtain ⟨_, w, hw⟩ := hm.1
  let H := G \ SimpleGraph.edge a b
  let _ : DecidableRel H.Adj :=
    inferInstanceAs (DecidableRel (G \ SimpleGraph.edge a b).Adj)
  have hcard : 2 ≤ Fintype.card V := by
    have := G.degree_lt_card_verts a
    omega
  have hn : Near H := by
    apply near_of_except H w hcard
    intro v hv
    have hdeg := erase_edge_degree G a b hab v
    change H.degree v + (if v = a ∨ v = b then 1 else 0) = G.degree v at hdeg
    by_cases hva : v = a
    · subst v
      simp at hdeg
      omega
    by_cases hvb : v = b
    · subst v
      simp at hdeg
      omega
    · simp [hva, hvb] at hdeg
      rw [hdeg]
      exact hw v hv
  have hEq : H = G := hm.2.2.2 H sdiff_le hn
  have he : H.Adj a b := hEq ▸ hab
  have hno : ¬H.Adj a b := by
    intro h
    have hs := (SimpleGraph.sdiff_adj G (SimpleGraph.edge a b) a b).mp h
    exact hs.2 ((SimpleGraph.edge_adj a b a b).mpr ⟨Or.inl ⟨rfl, rfl⟩, G.ne_of_adj hab⟩)
  exact hno he

/-! ### 3. No defect-triangle without a nontrivial 2-edge cut (`S-T-3`, `H-T-3`) -/

theorem no_defect_triangle_without_2cut {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (hno2 : ¬SmallCut G 2) {w a b : V}
    (hw : G.degree w = 2) (hwa : G.Adj w a) (hwb : G.Adj w b) : ¬G.Adj a b := by
  classical
  intro hab
  have ha3 : G.degree a = 3 := E64DefectCore.defect_neighbor_cubic G hm hw hwa
  have hb3 : G.degree b = 3 := E64DefectCore.defect_neighbor_cubic G hm hw hwb
  have hwa_ne : w ≠ a := G.ne_of_adj hwa
  have hwb_ne : w ≠ b := G.ne_of_adj hwb
  have hab_ne : a ≠ b := G.ne_of_adj hab
  obtain ⟨a', haa', ha'a, ha'b, ha'w⟩ := E64Triangle.third_neighbor G a b w (by omega)
  obtain ⟨b', hbb', hb'b, hb'a, hb'w⟩ := E64Triangle.third_neighbor G b a w (by omega)
  have ha'b' : a' ≠ b' := by
    intro heq
    subst b'
    exact no_c4_of_minimal_bad G hm hwa_ne ha'w.symm hwb_ne ha'a.symm hab_ne ha'b
      hwa haa' hbb'.symm hwb.symm
  let S : Set V := {w, a, b}
  have hS3 : Nat.card S = 3 := by
    have hfin : S.Finite := Set.toFinite S
    rw [Nat.card_eq_card_finite_toFinset hfin]
    have he : hfin.toFinset = ({w, a, b} : Finset V) := by
      ext v
      simp [S]
    rw [he]
    simp [hwa_ne, hwb_ne, hab_ne]
  have ha'S : a' ∈ (Sᶜ : Set V) := by simp [S, ha'w, ha'a, ha'b]
  have hb'S : b' ∈ (Sᶜ : Set V) := by simp [S, hb'w, hb'a, hb'b]
  have hSc : 2 ≤ Nat.card (Sᶜ : Set V) :=
    E64Triangle.nat_card_ge_two_of_ne ⟨a', ha'S⟩ ⟨b', hb'S⟩
      (fun h => ha'b' (congrArg Subtype.val h))
  have hNw : G.neighborFinset w = {a, b} := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      have hwx := (G.mem_neighborFinset w x).mp hx
      by_contra hnot
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
      have hsub : ({a, b, x} : Finset V) ⊆ G.neighborFinset w := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with hz | hz | hz
        · rw [hz]; exact (G.mem_neighborFinset w a).mpr hwa
        · rw [hz]; exact (G.mem_neighborFinset w b).mpr hwb
        · rw [hz]; exact (G.mem_neighborFinset w x).mpr hwx
      have hc := Finset.card_le_card hsub
      have h3 : ({a, b, x} : Finset V).card = 3 := by
        simp [hab_ne, Ne.symm hnot.1, Ne.symm hnot.2]
      rw [h3, G.card_neighborFinset_eq_degree, hw] at hc
      omega
    · rw [G.card_neighborFinset_eq_degree, hw]
      simp [hab_ne]
  let B := {e : V × V // e.1 ∈ S ∧ e.2 ∉ S ∧ G.Adj e.1 e.2}
  let f : B → Bool := fun e => decide (e.1.1 = a)
  have hne_w (e : B) : e.1.1 ≠ w := by
    intro hew
    have hadj : G.Adj w e.1.2 := hew ▸ e.2.2.2
    have hmem : e.1.2 ∈ G.neighborFinset w := (G.mem_neighborFinset w e.1.2).mpr hadj
    rw [hNw] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · exact e.2.2.1 (by simp [S, h])
    · exact e.2.2.1 (by simp [S, h])
  have hinj : Function.Injective f := by
    intro p q he
    have hpS : p.1.1 = a ∨ p.1.1 = b := by
      have h : p.1.1 = w ∨ p.1.1 = a ∨ p.1.1 = b := by simpa [S] using p.2.1
      exact h.resolve_left (hne_w p)
    have hqS : q.1.1 = a ∨ q.1.1 = b := by
      have h : q.1.1 = w ∨ q.1.1 = a ∨ q.1.1 = b := by simpa [S] using q.2.1
      exact h.resolve_left (hne_w q)
    have hpout : p.1.2 ≠ w ∧ p.1.2 ≠ a ∧ p.1.2 ≠ b := by simpa [S] using p.2.2.1
    have hqout : q.1.2 ≠ w ∧ q.1.2 ≠ a ∧ q.1.2 ≠ b := by simpa [S] using q.2.2.1
    have hfst : p.1.1 = q.1.1 := by
      rcases hpS with hpa | hpb <;> rcases hqS with hqa | hqb
      · exact hpa.trans hqa.symm
      · simp [f, hpa, hqb, hab_ne.symm] at he
      · simp [f, hpb, hqa, hab_ne.symm] at he
      · exact hpb.trans hqb.symm
    have hpedge := p.2.2.2
    have hqedge : G.Adj p.1.1 q.1.2 := hfst ▸ q.2.2.2
    have hsnd : p.1.2 = q.1.2 := by
      rcases hpS with hpa | hpb
      · rw [hpa] at hpedge hqedge
        exact E64Triangle.exterior_unique G (by omega) hwa.symm hab hwb_ne
          hpedge hqedge hpout.1 hpout.2.2 hqout.1 hqout.2.2
      · rw [hpb] at hpedge hqedge
        exact E64Triangle.exterior_unique G (by omega) hwb.symm hab.symm hwa_ne
          hpedge hqedge hpout.1 hpout.2.1 hqout.1 hqout.2.1
    exact Subtype.ext (Prod.ext hfst hsnd)
  have hcut := Nat.card_le_card_of_injective f hinj
  have hbool : Nat.card Bool = 2 := by rw [Nat.card_eq_fintype_card]; decide
  exact hno2 ⟨S, by omega, hSc, by change Nat.card B ≤ 2; omega⟩

/-! ### 4. Vertex-Identification / Edge-Contraction Engine -/

def identifyGraph {V : Type u} (G : SimpleGraph V) (x y : V) :
    SimpleGraph {v : V // v ≠ y} where
  Adj u v := u ≠ v ∧
    (G.Adj u.1 v.1 ∨ (u.1 = x ∧ G.Adj y v.1) ∨ (v.1 = x ∧ G.Adj u.1 y))
  symm := ⟨by
    rintro u v ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr ⟨h1, h2.symm⟩)
    · exact Or.inr (Or.inl ⟨h1, h2.symm⟩)⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Lift a walk in `identifyGraph G x y` whose support avoids `⟨x, hxy⟩` directly to `G`. -/
def liftAvoidWalk {V : Type u} {G : SimpleGraph V} {x y : V} (hxy : x ≠ y)
    {u v : {z : V // z ≠ y}} (p : (identifyGraph G x y).Walk u v)
    (havoid : (⟨x, hxy⟩ : {z : V // z ≠ y}) ∉ p.support) : G.Walk u.1 v.1 :=
  match p with
  | .nil => .nil
  | @Walk.cons _ _ a b _ hab q =>
    have ha : a ≠ ⟨x, hxy⟩ := fun h => havoid (by simp [h])
    have hb : b ≠ ⟨x, hxy⟩ := fun h => havoid (by
      rw [Walk.support_cons]
      exact List.mem_cons_of_mem a (h ▸ Walk.start_mem_support q))
    have habG : G.Adj a.1 b.1 := by
      rcases hab.2 with h | ⟨h1, _⟩ | ⟨h1, _⟩
      · exact h
      · exact False.elim (ha (Subtype.ext h1))
      · exact False.elim (hb (Subtype.ext h1))
    .cons habG (liftAvoidWalk hxy q (fun h => havoid (by simp [h])))

theorem liftAvoidWalk_length {V : Type u} {G : SimpleGraph V} {x y : V} (hxy : x ≠ y)
    {u v : {z : V // z ≠ y}} (p : (identifyGraph G x y).Walk u v)
    (havoid : (⟨x, hxy⟩ : {z : V // z ≠ y}) ∉ p.support) :
    (liftAvoidWalk hxy p havoid).length = p.length := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp [liftAvoidWalk, ih]

theorem liftAvoidWalk_support {V : Type u} {G : SimpleGraph V} {x y : V} (hxy : x ≠ y)
    {u v : {z : V // z ≠ y}} (p : (identifyGraph G x y).Walk u v)
    (havoid : (⟨x, hxy⟩ : {z : V // z ≠ y}) ∉ p.support) :
    (liftAvoidWalk hxy p havoid).support = p.support.map Subtype.val := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp [liftAvoidWalk, ih]

theorem liftAvoidWalk_isPath {V : Type u} {G : SimpleGraph V} {x y : V} (hxy : x ≠ y)
    {u v : {z : V // z ≠ y}} (p : (identifyGraph G x y).Walk u v)
    (havoid : (⟨x, hxy⟩ : {z : V // z ≠ y}) ∉ p.support) (hp : p.IsPath) :
    (liftAvoidWalk hxy p havoid).IsPath := by
  apply Walk.IsPath.mk'
  rw [liftAvoidWalk_support]
  exact hp.support_nodup.map Subtype.val_injective

theorem liftAvoidWalk_isCycle {V : Type u} {G : SimpleGraph V} {x y : V} (hxy : x ≠ y)
    {u : {z : V // z ≠ y}} (c : (identifyGraph G x y).Walk u u)
    (havoid : (⟨x, hxy⟩ : {z : V // z ≠ y}) ∉ c.support) (hc : c.IsCycle) :
    (liftAvoidWalk hxy c havoid).IsCycle := by
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  refine ⟨Walk.IsPath.mk' ?_, ?_⟩
  · have hnil : ¬(liftAvoidWalk hxy c havoid).Nil := by
      intro h
      have hl := Walk.length_eq_zero_iff.mpr h
      rw [liftAvoidWalk_length] at hl
      have := hc.three_le_length
      omega
    rw [Walk.support_tail_of_not_nil _ hnil, liftAvoidWalk_support, ← List.map_tail]
    exact hc.support_nodup.map Subtype.val_injective
  · rw [liftAvoidWalk_length]
    exact hc.three_le_length

/-- Core extraction lemma: any 2^k-cycle in `identifyGraph G x y` (when `¬HasPower G`)
    must pass through the identified vertex `X = ⟨x, hxy⟩`, lifting to a simple path `q`
    in `G - {x, y}` of length `2^k - 2` between a private neighbor of `x` and a private
    neighbor of `y`. -/
theorem identify_power_extract {V : Type u} [Fintype V]
    (G : SimpleGraph V) (hfree : ¬HasPower G)
    {x y : V} (hxy : x ≠ y)
    (hpow : HasPower (identifyGraph G x y)) :
    ∃ (k : ℕ) (a b : {z : V // z ≠ y}) (q : (identifyGraph G x y).Walk a b),
      2 ≤ k ∧ q.IsPath ∧ q.length + 2 = 2 ^ k ∧
      (⟨x, hxy⟩ : {z : V // z ≠ y}) ∉ q.support ∧
      G.Adj x a.1 ∧ ¬G.Adj y a.1 ∧ G.Adj y b.1 ∧ ¬G.Adj x b.1 := by
  classical
  let W := {z : V // z ≠ y}
  let H := identifyGraph G x y
  let X : W := ⟨x, hxy⟩
  obtain ⟨k, v0, c0, hk, hc0, hl0⟩ := hpow
  have hXmem : X ∈ c0.support := by
    by_contra hnot
    exact hfree ⟨k, v0.1, liftAvoidWalk hxy c0 hnot, hk,
      liftAvoidWalk_isCycle hxy c0 hnot hc0, by rw [liftAvoidWalk_length, hl0]⟩
  let c : H.Walk X X := c0.rotate X hXmem
  have hc : c.IsCycle := hc0.rotate hXmem
  have hl : c.length = 2 ^ k := by rw [Walk.length_rotate, hl0]
  have h4 : 4 ≤ 2 ^ k := by
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
    simpa using this
  cases hce : c with
  | nil =>
    rw [hce] at hl
    simp at hl
    omega
  | @cons _ a _ hXa p1 =>
    cases hpe : p1.reverse with
    | nil =>
      have hp1len : p1.length = 0 := by
        have h := congrArg Walk.length hpe
        rw [Walk.length_reverse, Walk.length_nil] at h
        exact h
      rw [hce] at hl
      simp [hp1len] at hl
      omega
    | @cons _ b _ hXb qrev =>
      let q : H.Walk a b := qrev.reverse
      have hp1_eq : p1 = q.append (.cons hXb.symm .nil) := by
        have h1 : p1 = p1.reverse.reverse := p1.reverse_reverse.symm
        rw [hpe] at h1
        simpa [q, Walk.reverse_cons] using h1
      have hcsupp : c.support = X :: (q.support ++ [X]) := by
        rw [hce, hp1_eq]
        simp [Walk.support_append]
      have hctail : c.support.tail = q.support ++ [X] := by
        rw [hcsupp]
        rfl
      have hnodup : (q.support ++ [X]).Nodup := by
        rw [← hctail]
        exact hc.support_nodup
      have hqnodup : q.support.Nodup := (List.nodup_append.mp hnodup).1
      have hqpath : q.IsPath := Walk.IsPath.mk' hqnodup
      have hXnot : X ∉ q.support := by
        intro hm
        have hdisj := (List.nodup_append.mp hnodup).2.2
        exact hdisj X hm X (by simp) rfl
      have hqlen : q.length + 2 = 2 ^ k := by
        rw [hce, hp1_eq] at hl
        simp [Walk.length_append] at hl
        omega
      let qG : G.Walk a.1 b.1 := liftAvoidWalk hxy q hXnot
      have hqGpath : qG.IsPath := liftAvoidWalk_isPath hxy q hXnot hqpath
      have hqGlen : qG.length + 2 = 2 ^ k := by rw [liftAvoidWalk_length]; exact hqlen
      have hxnot : x ∉ qG.support := by
        rw [liftAvoidWalk_support]
        intro hm
        obtain ⟨z, hz, hzx⟩ := List.mem_map.mp hm
        have hzX : z = X := Subtype.ext hzx
        exact hXnot (hzX ▸ hz)
      have hynot : y ∉ qG.support := by
        rw [liftAvoidWalk_support]
        intro hm
        obtain ⟨z, _, hzy⟩ := List.mem_map.mp hm
        exact z.2 hzy
      have hclose_x : ¬(G.Adj x a.1 ∧ G.Adj x b.1) := by
        rintro ⟨hxa, hxb⟩
        let cyc : G.Walk x x := .cons hxa (qG.append (.cons hxb.symm .nil))
        have hcyc_supp : cyc.support.tail = qG.support ++ [x] := by
          simp [cyc, Walk.support_append]
        have hcyc_nodup : cyc.support.tail.Nodup := by
          rw [hcyc_supp]
          exact List.nodup_append.mpr ⟨hqGpath.support_nodup, List.nodup_singleton x,
            fun u hu v hv heq => by
              simp only [List.mem_singleton] at hv
              subst v; subst u; exact hxnot hu⟩
        have hcyc_len : cyc.length = 2 ^ k := by
          simp [cyc, Walk.length_append]
          omega
        have hcyc : cyc.IsCycle := by
          apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
          refine ⟨Walk.IsPath.mk' ?_, by omega⟩
          rwa [Walk.support_tail_of_not_nil _ (by simp [cyc])]
        exact hfree ⟨k, x, cyc, hk, hcyc, hcyc_len⟩
      have hclose_y : ¬(G.Adj y a.1 ∧ G.Adj y b.1) := by
        rintro ⟨hya, hyb⟩
        let cyc : G.Walk y y := .cons hya (qG.append (.cons hyb.symm .nil))
        have hcyc_supp : cyc.support.tail = qG.support ++ [y] := by
          simp [cyc, Walk.support_append]
        have hcyc_nodup : cyc.support.tail.Nodup := by
          rw [hcyc_supp]
          exact List.nodup_append.mpr ⟨hqGpath.support_nodup, List.nodup_singleton y,
            fun u hu v hv heq => by
              simp only [List.mem_singleton] at hv
              subst v; subst u; exact hynot hu⟩
        have hcyc_len : cyc.length = 2 ^ k := by
          simp [cyc, Walk.length_append]
          omega
        have hcyc : cyc.IsCycle := by
          apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
          refine ⟨Walk.IsPath.mk' ?_, by omega⟩
          rwa [Walk.support_tail_of_not_nil _ (by simp [cyc])]
        exact hfree ⟨k, y, cyc, hk, hcyc, hcyc_len⟩
      have ha_adj : G.Adj x a.1 ∨ G.Adj y a.1 := by
        rcases hXa.2 with h | ⟨_, h⟩ | ⟨h, _⟩
        · exact Or.inl h
        · exact Or.inr h
        · exact False.elim (hXa.1 (Subtype.ext h.symm))
      have hb_adj : G.Adj x b.1 ∨ G.Adj y b.1 := by
        rcases hXb.2 with h | ⟨_, h⟩ | ⟨h, _⟩
        · exact Or.inl h
        · exact Or.inr h
        · exact False.elim (hXb.1 (Subtype.ext h.symm))
      rcases ha_adj with hxa | hya <;> rcases hb_adj with hxb | hyb
      · exact False.elim (hclose_x ⟨hxa, hxb⟩)
      · refine ⟨k, a, b, q, hk, hqpath, hqlen, hXnot, hxa,
          fun h => hclose_y ⟨h, hyb⟩, hyb, fun h => hclose_x ⟨hxa, h⟩⟩
      · refine ⟨k, b, a, q.reverse, hk, hqpath.reverse,
          by rw [Walk.length_reverse]; exact hqlen,
          by rwa [Walk.support_reverse, List.mem_reverse],
          hxb, fun h => hclose_y ⟨hya, h⟩, hya, fun h => hclose_x ⟨h, hxb⟩⟩
      · exact False.elim (hclose_y ⟨hya, hyb⟩)

/-- Degree lower bound for `v ≠ X` in `identifyGraph G x y`. -/
theorem identify_degree_other {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {x y : V} (hxy : x ≠ y) [DecidableRel (identifyGraph G x y).Adj]
    (v : {z : V // z ≠ y}) (hv : v.1 ≠ x) :
    G.degree v.1 ≤ (identifyGraph G x y).degree v +
      (if G.Adj x v.1 ∧ G.Adj y v.1 then 1 else 0) := by
  classical
  let X : {z : V // z ≠ y} := ⟨x, hxy⟩
  by_cases hboth : G.Adj x v.1 ∧ G.Adj y v.1
  · rw [ite_eq_left hboth]
    let f : {u : V // G.Adj v.1 u ∧ u ≠ y} → (identifyGraph G x y).neighborSet v := fun u =>
      ⟨⟨u.1, u.2.2⟩, ⟨fun heq => G.ne_of_adj u.2.1 (congrArg Subtype.val heq), Or.inl u.2.1⟩⟩
    have hf : Function.Injective f := by
      intro p q heq
      apply Subtype.ext
      exact congrArg (fun t => t.1.1) heq
    have hc := Fintype.card_le_of_injective f hf
    rw [SimpleGraph.card_neighborSet_eq_degree, Fintype.card_subtype] at hc
    have hfilt : (Finset.univ.filter (fun u : V => G.Adj v.1 u ∧ u ≠ y)) =
        (G.neighborFinset v.1).erase y := by
      ext u; simp [and_comm]
    rw [hfilt] at hc
    have hy : y ∈ G.neighborFinset v.1 := (G.mem_neighborFinset v.1 y).mpr hboth.2.symm
    have he := Finset.card_erase_add_one hy
    rw [G.card_neighborFinset_eq_degree] at he
    omega
  · rw [ite_eq_right hboth, add_zero]
    let f : G.neighborSet v.1 → (identifyGraph G x y).neighborSet v := fun u =>
      if huy : u.1 = y then
        ⟨X, ⟨fun heq => hv (congrArg Subtype.val heq),
          Or.inr (Or.inr ⟨rfl, by have hadj : G.Adj v.1 u.1 := u.2; exact huy ▸ hadj⟩)⟩⟩
      else
        ⟨⟨u.1, huy⟩, ⟨fun heq => G.ne_of_adj u.2 (congrArg Subtype.val heq), Or.inl u.2⟩⟩
    have hf : Function.Injective f := by
      intro p q heq
      by_cases hp : p.1 = y <;> by_cases hq : q.1 = y
      · exact Subtype.ext (hp.trans hq.symm)
      · exfalso
        simp [f, hp, hq] at heq
        have hqx : q.1 = x := (congrArg (fun t : {z : V // z ≠ y} => t.1) heq).symm
        have hp_adj : G.Adj v.1 p.1 := p.2
        have hq_adj : G.Adj v.1 q.1 := q.2
        exact hboth ⟨(hqx ▸ hq_adj).symm, (hp ▸ hp_adj).symm⟩
      · exfalso
        simp [f, hp, hq] at heq
        have hpx : p.1 = x := congrArg (fun t : {z : V // z ≠ y} => t.1) heq
        have hp_adj : G.Adj v.1 p.1 := p.2
        have hq_adj : G.Adj v.1 q.1 := q.2
        exact hboth ⟨(hpx ▸ hp_adj).symm, (hq ▸ hq_adj).symm⟩
      · simp [f, hp, hq] at heq
        exact Subtype.ext (congrArg (fun t : {z : V // z ≠ y} => t.1) heq)
    have hc := Fintype.card_le_of_injective f hf
    rwa [SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.card_neighborSet_eq_degree] at hc

/-- Exact degree upper bound for a cubic common neighbor `u` in `identifyGraph G x y`. -/
theorem identify_degree_common_le_two {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {x y : V} [DecidableRel (identifyGraph G x y).Adj]
    (u : {z : V // z ≠ y})
    (hux : G.Adj x u.1) (huy : G.Adj y u.1) (hdeg3 : G.degree u.1 = 3) :
    (identifyGraph G x y).degree u ≤ 2 := by
  classical
  have huv_x : u.1 ≠ x := (G.ne_of_adj hux).symm
  let f : (identifyGraph G x y).neighborSet u → {z : V // G.Adj u.1 z ∧ z ≠ y} := fun v =>
    ⟨v.1.1, by
      refine ⟨?_, v.1.2⟩
      rcases v.2.2 with h | ⟨h1, _⟩ | ⟨h1, _⟩
      · exact h
      · exact False.elim (huv_x h1)
      · exact h1 ▸ hux.symm⟩
  have hf : Function.Injective f := by
    intro p q heq
    have hval : p.1.1 = q.1.1 :=
      congrArg (fun t : {z : V // G.Adj u.1 z ∧ z ≠ y} => t.1) heq
    exact Subtype.ext (Subtype.ext hval)
  have hc := Fintype.card_le_of_injective f hf
  rw [SimpleGraph.card_neighborSet_eq_degree, Fintype.card_subtype] at hc
  have hfilt : (Finset.univ.filter (fun z : V => G.Adj u.1 z ∧ z ≠ y)) =
      (G.neighborFinset u.1).erase y := by
    ext z; simp [and_comm]
  rw [hfilt] at hc
  have hy : y ∈ G.neighborFinset u.1 := (G.mem_neighborFinset u.1 y).mpr huy.symm
  have he := Finset.card_erase_add_one hy
  rw [G.card_neighborFinset_eq_degree, hdeg3] at he
  omega

/-- Degree lower bound at the identified vertex `X = ⟨x, hxy⟩` when `x, y` are non-adjacent. -/
theorem identify_degree_X_nonadj {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {x y : V} (hxy : x ≠ y) (hnadj : ¬G.Adj x y)
    [DecidableRel (identifyGraph G x y).Adj] :
    G.degree x ≤ (identifyGraph G x y).degree ⟨x, hxy⟩ ∧
      G.degree y ≤ (identifyGraph G x y).degree ⟨x, hxy⟩ := by
  classical
  constructor
  · let f : G.neighborSet x → (identifyGraph G x y).neighborSet ⟨x, hxy⟩ := fun u =>
      ⟨⟨u.1, fun h => hnadj (h ▸ u.2)⟩,
        ⟨fun heq => G.ne_of_adj u.2 (congrArg Subtype.val heq), Or.inl u.2⟩⟩
    have hf : Function.Injective f := fun _ _ h => Subtype.ext (congrArg (fun t => t.1.1) h)
    have hc := Fintype.card_le_of_injective f hf
    rwa [SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.card_neighborSet_eq_degree] at hc
  · let f : G.neighborSet y → (identifyGraph G x y).neighborSet ⟨x, hxy⟩ := fun u =>
      ⟨⟨u.1, (G.ne_of_adj u.2).symm⟩,
        ⟨fun heq => hnadj ((congrArg Subtype.val heq ▸ u.2).symm), Or.inr (Or.inl ⟨rfl, u.2⟩)⟩⟩
    have hf : Function.Injective f := fun _ _ h => Subtype.ext (congrArg (fun t => t.1.1) h)
    have hc := Fintype.card_le_of_injective f hf
    rwa [SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.card_neighborSet_eq_degree] at hc

/-- Cardinality of `{z : V // z ≠ y}` is `Fintype.card V - 1`. -/
theorem card_erase_vertex {V : Type u} [Fintype V] [DecidableEq V] (y : V) :
    Fintype.card {z : V // z ≠ y} + 1 = Fintype.card V := by
  rw [Fintype.card_subtype,
    show (Finset.univ.filter (fun z : V => z ≠ y)) = Finset.univ.erase y by ext z; simp]
  exact Finset.card_erase_add_one (Finset.mem_univ y)

/-! ### 5. Universal Dyadic Path Theorem & 6-Line Unified Bipartite Exclusion -/

/-- Wave 1/2 Universal Dyadic Path Theorem: in ANY `MinimalBad` graph (`C`, `S`, or `H`),
    every pair `x, y` at distance >= 3 has a simple `x`–`y` path of length `2^k` (`k >= 2`). -/
theorem universal_dyadic_path {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {x y : V} (hxy : x ≠ y) (hnadj : ¬G.Adj x y)
    (hnocom : ∀ u, ¬(G.Adj x u ∧ G.Adj y u)) :
    ∃ (k : ℕ) (p : G.Walk x y), 2 ≤ k ∧ p.IsPath ∧ p.length = 2 ^ k := by
  classical
  let H := identifyGraph G x y
  let _ : DecidableRel H.Adj := Classical.decRel _
  let X : {z : V // z ≠ y} := ⟨x, hxy⟩
  obtain ⟨⟨v0, hv0⟩, ⟨w, hw⟩⟩ := hm.1
  have hcardV : 4 ≤ Fintype.card V := by have := G.degree_lt_card_verts v0; omega
  have hcardW : Fintype.card {z : V // z ≠ y} + 1 = Fintype.card V := card_erase_vertex y
  have hdegX : 3 ≤ H.degree X := by
    have hxy_deg := identify_degree_X_nonadj G hxy hnadj
    by_cases hxw : x = w
    · have hyw : y ≠ w := by rwa [← hxw, ne_comm]
      exact (hw y hyw).trans hxy_deg.2
    · exact (hw x hxw).trans hxy_deg.1
  have hnear : Near H := by
    by_cases hwy : w = y
    · apply near_of_except H X (by omega)
      intro v hv
      have hvx : v.1 ≠ x := fun h => hv (Subtype.ext h)
      have hvw : v.1 ≠ w := hwy ▸ v.2
      have hd := identify_degree_other G hxy v hvx
      rw [ite_eq_right (hnocom v.1), add_zero] at hd
      exact (hw v.1 hvw).trans hd
    · apply near_of_except H ⟨w, hwy⟩ (by omega)
      intro v hv
      by_cases hvx : v.1 = x
      · have : v = X := Subtype.ext hvx
        rw [this]; exact hdegX
      · have hvw : v.1 ≠ w := fun h => hv (Subtype.ext h)
        have hd := identify_degree_other G hxy v hvx
        rw [ite_eq_right (hnocom v.1), add_zero] at hd
        exact (hw v.1 hvw).trans hd
  have hpow : HasPower H := hm.2.2.1 {z : V // z ≠ y} H (by omega) hnear
  obtain ⟨k, a, b, q, hk, hqpath, hqlen, hXnot, hxa, _, hyb, _⟩ :=
    identify_power_extract G hm.2.1 hxy hpow
  let qG := liftAvoidWalk hxy q hXnot
  have hqGpath := liftAvoidWalk_isPath hxy q hXnot hqpath
  have hqGlen : qG.length + 2 = 2 ^ k := by rw [liftAvoidWalk_length]; exact hqlen
  have hxnot : x ∉ qG.support := by
    rw [liftAvoidWalk_support]
    intro hm'
    obtain ⟨z, hz, hzx⟩ := List.mem_map.mp hm'
    have hzX : z = ⟨x, hxy⟩ := Subtype.ext hzx
    exact hXnot (hzX ▸ hz)
  have hynot : y ∉ qG.support := by
    rw [liftAvoidWalk_support]
    intro hm'
    obtain ⟨z, _, hzy⟩ := List.mem_map.mp hm'
    exact z.2 hzy
  let p : G.Walk x y := .cons hxa (qG.append (.cons hyb.symm .nil))
  have hp_supp : p.support = x :: (qG.support ++ [y]) := by
    simp [p, Walk.support_append]
  have hp_nodup : p.support.Nodup := by
    rw [hp_supp, List.nodup_cons]
    refine ⟨?_, ?_⟩
    · simp [hxnot, hxy]
    · exact List.nodup_append.mpr ⟨hqGpath.support_nodup, List.nodup_singleton y,
        fun u hu v hv heq => by
          simp only [List.mem_singleton] at hv
          subst v; subst u; exact hynot hu⟩
  refine ⟨k, p, hk, Walk.IsPath.mk' hp_nodup, ?_⟩
  simp [p, Walk.length_append]
  omega

theorem walk_bipartite_parity {V : Type u} {G : SimpleGraph V}
    (color : V → Bool) (hproper : ∀ a b, G.Adj a b → color a ≠ color b)
    {u v : V} (p : G.Walk u v) :
    (p.length % 2 = 0 → color u = color v) ∧ (p.length % 2 = 1 → color u ≠ color v) := by
  induction p with
  | nil => simp
  | @cons a b c hab q ih =>
    have hne := hproper a b hab
    cases ha : color a <;> cases hb : color b <;> cases hc : color c <;>
      simp_all [Walk.length_cons] <;> omega

/-- Single unified exclusion of ALL 6 bipartite leaves (`C-B`, `S-B`, `H-B-*`)
    directly from `universal_dyadic_path`. -/
theorem unified_bipartite_exclusion {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G) (hB : Bip G) : False := by
  classical
  obtain ⟨color, hproper⟩ := hB
  have hcomplete : ∀ x y, color x ≠ color y → G.Adj x y := by
    intro x y hcol
    by_contra hnadj
    have hxy : x ≠ y := fun h => hcol (by rw [h])
    have hnocom : ∀ u, ¬(G.Adj x u ∧ G.Adj y u) := by
      rintro u ⟨hxu, hyu⟩
      have h1 := hproper x u hxu
      have h2 := hproper y u hyu
      cases hx : color x <;> cases hy : color y <;> cases hu : color u <;> simp_all
    obtain ⟨k, p, hk, _, hlen⟩ := universal_dyadic_path G hm hxy hnadj hnocom
    have heven : p.length % 2 = 0 := by
      rw [hlen]
      cases k with
      | zero => omega
      | succ j => rw [pow_succ]; omega
    exact hcol ((walk_bipartite_parity color hproper p).1 heven)
  obtain ⟨⟨v, hv⟩, _⟩ := hm.1
  have hcard_v : 3 ≤ (G.neighborFinset v).card := by
    rwa [G.card_neighborFinset_eq_degree]
  obtain ⟨y1, hy1, y2, hy2, hy12⟩ := Finset.one_lt_card.mp (by omega : 1 < (G.neighborFinset v).card)
  have hvy1 : G.Adj v y1 := (G.mem_neighborFinset v y1).mp hy1
  have hvy2 : G.Adj v y2 := (G.mem_neighborFinset v y2).mp hy2
  have hdy1 : 2 ≤ G.degree y1 := no_small_defect G hm y1
  have hcard_y1 : 2 ≤ (G.neighborFinset y1).card := by
    rwa [G.card_neighborFinset_eq_degree]
  obtain ⟨x1, hx1, x2, hx2, hx12⟩ := Finset.one_lt_card.mp (by omega : 1 < (G.neighborFinset y1).card)
  have hy1x1 : G.Adj y1 x1 := (G.mem_neighborFinset y1 x1).mp hx1
  have hy1x2 : G.Adj y1 x2 := (G.mem_neighborFinset y1 x2).mp hx2
  have hcol_y : color y1 = color y2 := by
    have h1 := hproper v y1 hvy1
    have h2 := hproper v y2 hvy2
    cases hcv : color v <;> cases hcy1 : color y1 <;> cases hcy2 : color y2 <;> simp_all
  have hcol_x1y2 : color x1 ≠ color y2 := by
    rw [← hcol_y]; exact (hproper y1 x1 hy1x1).symm
  have hcol_x2y2 : color x2 ≠ color y2 := by
    rw [← hcol_y]; exact (hproper y1 x2 hy1x2).symm
  have hx1y2 : G.Adj x1 y2 := hcomplete x1 y2 hcol_x1y2
  have hx2y2 : G.Adj x2 y2 := hcomplete x2 y2 hcol_x2y2
  exact no_c4_of_minimal_bad G hm
    (G.ne_of_adj hy1x1).symm hx12 (G.ne_of_adj hx1y2)
    (G.ne_of_adj hy1x2) hy12 (G.ne_of_adj hx2y2)
    hy1x1.symm hy1x2 hx2y2 hx1y2.symm

/-! ### 6. NEW: Strengthened Cubic Non-Edge Dyadic Path & (2^k + 2)-Cycle Theorems -/

/-- Helper: an internal vertex of a path has at least 2 distinct neighbors on the path,
    and if `u` is adjacent to `X ∉ q.support`, then `u` has degree >= 3. -/
theorem mem_path_avoiding_deg_ge_three {V : Type u} [Fintype V]
    {H : SimpleGraph V} [DecidableRel H.Adj]
    {a b X u : V} (q : H.Walk a b) (hq : q.IsPath)
    (hXnot : X ∉ q.support) (hu_mem : u ∈ q.support)
    (hua : u ≠ a) (hub : u ≠ b) (hXu : H.Adj X u) :
    3 ≤ H.degree u := by
  classical
  induction q with
  | nil =>
    simp at hu_mem
    exact False.elim (hua hu_mem)
  | @cons p r s hpr q' ih =>
    simp only [Walk.support_cons, List.mem_cons] at hu_mem
    rcases hu_mem with rfl | hu_q'
    · exact False.elim (hua rfl)
    · by_cases hur : u = r
      · subst u
        cases q' with
        | nil => exact False.elim (hub rfl)
        | @cons _ t _ hrt q'' =>
          have hXne_p : X ≠ p := fun h => hXnot (by simp [h])
          have hXne_t : X ≠ t := fun h => hXnot (by
            rw [Walk.support_cons, Walk.support_cons]
            exact List.mem_cons_of_mem p (List.mem_cons_of_mem r (h ▸ Walk.start_mem_support q'')))
          have hpne_t : p ≠ t := by
            intro heq
            have hnodup := hq.support_nodup
            rw [Walk.support_cons, List.nodup_cons] at hnodup
            have htmem : t ∈ (Walk.cons hrt q'').support := by
              rw [Walk.support_cons]
              exact List.mem_cons_of_mem r (Walk.start_mem_support q'')
            exact hnodup.1 (heq ▸ htmem)
          have hsub : ({X, p, t} : Finset V) ⊆ H.neighborFinset r := by
            intro z hz
            simp only [Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with hz | hz | hz
            · rw [hz]; exact (H.mem_neighborFinset r X).mpr hXu.symm
            · rw [hz]; exact (H.mem_neighborFinset r p).mpr hpr.symm
            · rw [hz]; exact (H.mem_neighborFinset r t).mpr hrt
          have hc := Finset.card_le_card hsub
          have h3 : ({X, p, t} : Finset V).card = 3 := by
            simp [hXne_p, hXne_t, hpne_t]
          rw [h3, H.card_neighborFinset_eq_degree] at hc
          exact hc
      · exact ih hq.of_cons (fun h => hXnot (by simp [h])) hu_q' hur hub

/-- NEW Theorem: In ANY cubic `MinimalBad` graph (`C-N-R`, `C-N-2`, `C-N-3`, `C-T-2`, `C-T-3`),
    EVERY non-adjacent pair `x ≠ y` (including `dist(x, y) = 2`!) has a simple `x`–`y` path
    of length `2^k` (`k >= 2`) avoiding every common neighbor of `x` and `y`. -/
theorem cubic_nonadj_dyadic_path {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G) (hC : Cubic G)
    {x y : V} (hxy : x ≠ y) (hnadj : ¬G.Adj x y) :
    ∃ (k : ℕ) (p : G.Walk x y), 2 ≤ k ∧ p.IsPath ∧ p.length = 2 ^ k ∧
      ∀ u, G.Adj x u → G.Adj y u → u ∉ p.support := by
  classical
  let H := identifyGraph G x y
  let _ : DecidableRel H.Adj := Classical.decRel _
  let X : {z : V // z ≠ y} := ⟨x, hxy⟩
  have hcardV : 4 ≤ Fintype.card V := by
    have := G.degree_lt_card_verts x
    have := hC x
    omega
  have hcardW : Fintype.card {z : V // z ≠ y} + 1 = Fintype.card V := card_erase_vertex y
  have hdegX : 3 ≤ H.degree X := by
    have hxy_deg : G.degree x ≤ H.degree X ∧ G.degree y ≤ H.degree X :=
      identify_degree_X_nonadj G hxy hnadj
    have hx3 := hC x
    omega
  have hnear : Near H := by
    by_cases hcom : ∃ u, G.Adj x u ∧ G.Adj y u
    · obtain ⟨u, hxu, hyu⟩ := hcom
      have huy : u ≠ y := (G.ne_of_adj hyu).symm
      apply near_of_except H ⟨u, huy⟩ (by omega)
      intro v hv
      by_cases hvx : v.1 = x
      · have : v = X := Subtype.ext hvx
        rw [this]; exact hdegX
      · have hvu : v.1 ≠ u := fun h => hv (Subtype.ext h)
        have hnotboth : ¬(G.Adj x v.1 ∧ G.Adj y v.1) := by
          rintro ⟨hxv, hyv⟩
          exact hvu (common_neighbor_unique G hm hxy hxv hyv hxu hyu)
        have hd := identify_degree_other G hxy v hvx
        rw [ite_eq_right hnotboth, add_zero, hC v.1] at hd
        exact hd
    · apply near_of_except H X (by omega)
      intro v hv
      have hvx : v.1 ≠ x := fun h => hv (Subtype.ext h)
      have hnotboth : ¬(G.Adj x v.1 ∧ G.Adj y v.1) := fun hb => hcom ⟨v.1, hb⟩
      have hd := identify_degree_other G hxy v hvx
      rw [ite_eq_right hnotboth, add_zero, hC v.1] at hd
      exact hd
  have hpow : HasPower H := hm.2.2.1 {z : V // z ≠ y} H (by omega) hnear
  obtain ⟨k, a, b, q, hk, hqpath, hqlen, hXnot, hxa, hya_not, hyb, hxb_not⟩ :=
    identify_power_extract G hm.2.1 hxy hpow
  let qG := liftAvoidWalk hxy q hXnot
  have hqGpath := liftAvoidWalk_isPath hxy q hXnot hqpath
  have hqGlen : qG.length + 2 = 2 ^ k := by rw [liftAvoidWalk_length]; exact hqlen
  have hxnot : x ∉ qG.support := by
    rw [liftAvoidWalk_support]
    intro hm'
    obtain ⟨z, hz, hzx⟩ := List.mem_map.mp hm'
    have hzX : z = ⟨x, hxy⟩ := Subtype.ext hzx
    exact hXnot (hzX ▸ hz)
  have hynot : y ∉ qG.support := by
    rw [liftAvoidWalk_support]
    intro hm'
    obtain ⟨z, _, hzy⟩ := List.mem_map.mp hm'
    exact z.2 hzy
  let p : G.Walk x y := .cons hxa (qG.append (.cons hyb.symm .nil))
  have hp_supp : p.support = x :: (qG.support ++ [y]) := by
    simp [p, Walk.support_append]
  have hp_nodup : p.support.Nodup := by
    rw [hp_supp, List.nodup_cons]
    refine ⟨by simp [hxnot, hxy], ?_⟩
    exact List.nodup_append.mpr ⟨hqGpath.support_nodup, List.nodup_singleton y,
      fun u hu v hv heq => by
        simp only [List.mem_singleton] at hv
        subst v; subst u; exact hynot hu⟩
  refine ⟨k, p, hk, Walk.IsPath.mk' hp_nodup, by simp [p, Walk.length_append]; omega, ?_⟩
  intro u hxu hyu humem
  rw [hp_supp, List.mem_cons, List.mem_append, List.mem_singleton] at humem
  rcases humem with rfl | (huq | rfl)
  · exact G.ne_of_adj hxu rfl
  · rw [liftAvoidWalk_support] at huq
    obtain ⟨uW, huW_mem, huW_val⟩ := List.mem_map.mp huq
    have hxuW : G.Adj x uW.1 := huW_val.symm ▸ hxu
    have hyuW : G.Adj y uW.1 := huW_val.symm ▸ hyu
    have hu_ne_a : uW ≠ a := fun h => hya_not (h ▸ hyuW)
    have hu_ne_b : uW ≠ b := fun h => hxb_not (h ▸ hxuW)
    have hXuW : H.Adj X uW := ⟨fun h => G.ne_of_adj hxuW (congrArg Subtype.val h), Or.inl hxuW⟩
    have hdeg3 : 3 ≤ H.degree uW :=
      mem_path_avoiding_deg_ge_three q hqpath hXnot huW_mem hu_ne_a hu_ne_b hXuW
    have hdeg2 : H.degree uW ≤ 2 :=
      identify_degree_common_le_two G uW hxuW hyuW (hC uW.1)
    omega
  · exact G.ne_of_adj hyu rfl

/-- NEW Theorem: Every non-triangle 2-path `x - u - y` in cubic `MinimalBad`
    lies on a simple cycle of length `2^k + 2` (`k >= 2`). -/
theorem cubic_two_path_dyadic_plus_two_cycle {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G) (hC : Cubic G)
    {x u y : V} (hxu : G.Adj x u) (huy : G.Adj u y) (hxy : x ≠ y) (hnadj : ¬G.Adj x y) :
    ∃ (k : ℕ) (c : G.Walk x x), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k + 2 ∧
      u ∈ c.support ∧ y ∈ c.support := by
  obtain ⟨k, p, hk, hppath, hplen, havoid⟩ := cubic_nonadj_dyadic_path G hm hC hxy hnadj
  have hunot : u ∉ p.support := havoid u hxu huy.symm
  let c : G.Walk x x := p.append (.cons huy.symm (.cons hxu.symm .nil))
  have hcsupp : c.support = p.support ++ [u, x] := by
    simp [c, Walk.support_append]
  have hctail : c.support.tail = p.support.tail ++ [u, x] := by
    have h1 : p.support = x :: p.support.tail := p.cons_tail_support.symm
    rw [hcsupp, h1]
    rfl
  have h2k : 4 ≤ 2 ^ k := by
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
    simpa using this
  have hclen : c.length = 2 ^ k + 2 := by
    simp [c, Walk.length_append, hplen]
  have hnodup_p : (x :: p.support.tail).Nodup := by
    rw [p.cons_tail_support]; exact hppath.support_nodup
  have hxnot_tail : x ∉ p.support.tail := (List.nodup_cons.mp hnodup_p).1
  have htail_nodup : p.support.tail.Nodup := (List.nodup_cons.mp hnodup_p).2
  have hunot_tail : u ∉ p.support.tail := fun hm' =>
    hunot (by rw [← p.cons_tail_support]; exact List.mem_cons_of_mem x hm')
  have hctail_nodup : c.support.tail.Nodup := by
    rw [hctail]
    refine List.nodup_append.mpr ⟨htail_nodup, ?_, ?_⟩
    · simp [(G.ne_of_adj hxu).symm]
    · intro a ha b hb heq
      simp at hb
      rcases hb with rfl | rfl
      · exact hunot_tail (heq ▸ ha)
      · exact hxnot_tail (heq ▸ ha)
  have hcnil : ¬c.Nil := by
    intro h
    have := Walk.length_eq_zero_iff.mpr h
    omega
  have hc : c.IsCycle := by
    apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    refine ⟨Walk.IsPath.mk' ?_, by omega⟩
    rwa [Walk.support_tail_of_not_nil _ hcnil]
  refine ⟨k, c, hk, hc, hclen, ?_, ?_⟩
  · rw [hcsupp]; simp
  · rw [hcsupp]; simp [Walk.end_mem_support]

/-! ### 7. NEW: Cubic Edge-Contraction (2^k + 1)-Cycle Theorem -/

/-- Degree lower bound at `X = ⟨x, hxy⟩` when contracting an edge `xy` in a cubic `MinimalBad` graph. -/
theorem identify_degree_X_adj_cubic {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G) (hC : Cubic G)
    {x y : V} (hxy_adj : G.Adj x y)
    [DecidableRel (identifyGraph G x y).Adj] :
    3 ≤ (identifyGraph G x y).degree ⟨x, G.ne_of_adj hxy_adj⟩ := by
  classical
  let H := identifyGraph G x y
  have hxy : x ≠ y := G.ne_of_adj hxy_adj
  let X : {z : V // z ≠ y} := ⟨x, hxy⟩
  have hNx : ((G.neighborFinset x).erase y).card = 2 := by
    have hy : y ∈ G.neighborFinset x := (G.mem_neighborFinset x y).mpr hxy_adj
    have hc := Finset.card_erase_add_one hy
    rw [G.card_neighborFinset_eq_degree, hC x] at hc
    omega
  have hNy : ((G.neighborFinset y).erase x).card = 2 := by
    have hx : x ∈ G.neighborFinset y := (G.mem_neighborFinset y x).mpr hxy_adj.symm
    have hc := Finset.card_erase_add_one hx
    rw [G.card_neighborFinset_eq_degree, hC y] at hc
    omega
  obtain ⟨x1, x2, hx12, hSx⟩ := Finset.card_eq_two.mp hNx
  obtain ⟨y1, y2, hy12, hSy⟩ := Finset.card_eq_two.mp hNy
  have hx1_mem : x1 ∈ (G.neighborFinset x).erase y := by rw [hSx]; simp
  have hx2_mem : x2 ∈ (G.neighborFinset x).erase y := by rw [hSx]; simp
  have hy1_mem : y1 ∈ (G.neighborFinset y).erase x := by rw [hSy]; simp
  have hy2_mem : y2 ∈ (G.neighborFinset y).erase x := by rw [hSy]; simp
  have hx1_adj : G.Adj x x1 := (G.mem_neighborFinset x x1).mp (Finset.mem_of_mem_erase hx1_mem)
  have hx2_adj : G.Adj x x2 := (G.mem_neighborFinset x x2).mp (Finset.mem_of_mem_erase hx2_mem)
  have hy1_adj : G.Adj y y1 := (G.mem_neighborFinset y y1).mp (Finset.mem_of_mem_erase hy1_mem)
  have hy2_adj : G.Adj y y2 := (G.mem_neighborFinset y y2).mp (Finset.mem_of_mem_erase hy2_mem)
  have hx1y : x1 ≠ y := (Finset.mem_erase.mp hx1_mem).1
  have hx2y : x2 ≠ y := (Finset.mem_erase.mp hx2_mem).1
  have hy1y : y1 ≠ y := (G.ne_of_adj hy1_adj).symm
  have hy2y : y2 ≠ y := (G.ne_of_adj hy2_adj).symm
  have hex_y : ∃ z : {v : V // v ≠ y}, G.Adj y z.1 ∧ z.1 ≠ x ∧ z.1 ≠ x1 ∧ z.1 ≠ x2 := by
    by_cases h1 : y1 ≠ x1 ∧ y1 ≠ x2
    · exact ⟨⟨y1, hy1y⟩, hy1_adj, (Finset.mem_erase.mp hy1_mem).1, h1.1, h1.2⟩
    · have h1' : y1 = x1 ∨ y1 = x2 := by tauto
      have hxy1 : G.Adj x y1 := by rcases h1' with rfl | rfl <;> assumption
      have h2x1 : y2 ≠ x1 := by
        intro heq
        have hxy2 : G.Adj x y2 := heq ▸ hx1_adj
        exact hy12 (common_neighbor_unique G hm hxy hxy1 hy1_adj hxy2 hy2_adj)
      have h2x2 : y2 ≠ x2 := by
        intro heq
        have hxy2 : G.Adj x y2 := heq ▸ hx2_adj
        exact hy12 (common_neighbor_unique G hm hxy hxy1 hy1_adj hxy2 hy2_adj)
      exact ⟨⟨y2, hy2y⟩, hy2_adj, (Finset.mem_erase.mp hy2_mem).1, h2x1, h2x2⟩
  obtain ⟨z, hyz, hzx, hzx1, hzx2⟩ := hex_y
  let a1 : {v : V // v ≠ y} := ⟨x1, hx1y⟩
  let a2 : {v : V // v ≠ y} := ⟨x2, hx2y⟩
  have ha12 : a1 ≠ a2 := fun h => hx12 (congrArg Subtype.val h)
  have ha1z : a1 ≠ z := fun h => hzx1 (congrArg Subtype.val h).symm
  have ha2z : a2 ≠ z := fun h => hzx2 (congrArg Subtype.val h).symm
  have hsub : ({a1, a2, z} : Finset {v : V // v ≠ y}) ⊆ H.neighborFinset X := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with hw | hw | hw
    · rw [hw]; exact (H.mem_neighborFinset X a1).mpr
        ⟨fun h => G.ne_of_adj hx1_adj (congrArg Subtype.val h), Or.inl hx1_adj⟩
    · rw [hw]; exact (H.mem_neighborFinset X a2).mpr
        ⟨fun h => G.ne_of_adj hx2_adj (congrArg Subtype.val h), Or.inl hx2_adj⟩
    · rw [hw]; exact (H.mem_neighborFinset X z).mpr
        ⟨fun h => hzx (congrArg Subtype.val h).symm, Or.inr (Or.inl ⟨rfl, hyz⟩)⟩
  have hc := Finset.card_le_card hsub
  have h3 : ({a1, a2, z} : Finset {v : V // v ≠ y}).card = 3 := by
    simp [ha12, ha1z, ha2z]
  rw [h3, H.card_neighborFinset_eq_degree] at hc
  exact hc

/-- NEW Theorem: Every edge `xy` in a cubic `MinimalBad` graph lies on a simple cycle
    of length `2^k + 1` (`k >= 2`). -/
theorem cubic_edge_dyadic_plus_one_cycle {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G) (hC : Cubic G)
    {x y : V} (hxy_adj : G.Adj x y) :
    ∃ (k : ℕ) (c : G.Walk x x), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k + 1 ∧
      s(x, y) ∈ c.edges := by
  classical
  have hxy : x ≠ y := G.ne_of_adj hxy_adj
  let H := identifyGraph G x y
  let _ : DecidableRel H.Adj := Classical.decRel _
  let X : {z : V // z ≠ y} := ⟨x, hxy⟩
  have hcardV : 4 ≤ Fintype.card V := by
    have := G.degree_lt_card_verts x
    have := hC x
    omega
  have hcardW : Fintype.card {z : V // z ≠ y} + 1 = Fintype.card V := card_erase_vertex y
  have hdegX : 3 ≤ H.degree X := identify_degree_X_adj_cubic G hm hC hxy_adj
  have hnear : Near H := by
    by_cases hcom : ∃ t, G.Adj x t ∧ G.Adj y t
    · obtain ⟨t, hxt, hyt⟩ := hcom
      have hty : t ≠ y := (G.ne_of_adj hyt).symm
      apply near_of_except H ⟨t, hty⟩ (by omega)
      intro v hv
      by_cases hvx : v.1 = x
      · have : v = X := Subtype.ext hvx
        rw [this]; exact hdegX
      · have hvt : v.1 ≠ t := fun h => hv (Subtype.ext h)
        have hnotboth : ¬(G.Adj x v.1 ∧ G.Adj y v.1) := by
          rintro ⟨hxv, hyv⟩
          exact hvt (common_neighbor_unique G hm hxy hxv hyv hxt hyt)
        have hd := identify_degree_other G hxy v hvx
        rw [ite_eq_right hnotboth, add_zero, hC v.1] at hd
        exact hd
    · apply near_of_except H X (by omega)
      intro v hv
      have hvx : v.1 ≠ x := fun h => hv (Subtype.ext h)
      have hnotboth : ¬(G.Adj x v.1 ∧ G.Adj y v.1) := fun hb => hcom ⟨v.1, hb⟩
      have hd := identify_degree_other G hxy v hvx
      rw [ite_eq_right hnotboth, add_zero, hC v.1] at hd
      exact hd
  have hpow : HasPower H := hm.2.2.1 {z : V // z ≠ y} H (by omega) hnear
  obtain ⟨k, a, b, q, hk, hqpath, hqlen, hXnot, hxa, _, hyb, _⟩ :=
    identify_power_extract G hm.2.1 hxy hpow
  let qG := liftAvoidWalk hxy q hXnot
  have hqGpath := liftAvoidWalk_isPath hxy q hXnot hqpath
  have hqGlen : qG.length + 2 = 2 ^ k := by rw [liftAvoidWalk_length]; exact hqlen
  have hxnot : x ∉ qG.support := by
    rw [liftAvoidWalk_support]
    intro hm'
    obtain ⟨z, hz, hzx⟩ := List.mem_map.mp hm'
    have hzX : z = ⟨x, hxy⟩ := Subtype.ext hzx
    exact hXnot (hzX ▸ hz)
  have hynot : y ∉ qG.support := by
    rw [liftAvoidWalk_support]
    intro hm'
    obtain ⟨z, _, hzy⟩ := List.mem_map.mp hm'
    exact z.2 hzy
  let c : G.Walk x x := .cons hxa (qG.append (.cons hyb.symm (.cons hxy_adj.symm .nil)))
  have hctail : c.support.tail = qG.support ++ [y, x] := by
    simp [c, Walk.support_append]
  have hctail_nodup : c.support.tail.Nodup := by
    rw [hctail]
    refine List.nodup_append.mpr ⟨hqGpath.support_nodup, by simp [hxy.symm], ?_⟩
    intro u hu v hv heq
    simp at hv
    rcases hv with rfl | rfl
    · exact hynot (heq ▸ hu)
    · exact hxnot (heq ▸ hu)
  have h2k : 4 ≤ 2 ^ k := by
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
    simpa using this
  have hclen : c.length = 2 ^ k + 1 := by
    simp [c, Walk.length_append]
    omega
  have hc : c.IsCycle := by
    apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    refine ⟨Walk.IsPath.mk' ?_, by omega⟩
    rwa [Walk.support_tail_of_not_nil _ (by simp [c])]
  refine ⟨k, c, hk, hc, hclen, ?_⟩
  simp [c, Walk.edges_append, Sym2.eq_swap]

#print axioms no_c4_of_minimal_bad
#print axioms common_neighbor_unique
#print axioms high_degree_independent
#print axioms no_defect_triangle_without_2cut
#print axioms universal_dyadic_path
#print axioms unified_bipartite_exclusion
#print axioms cubic_nonadj_dyadic_path
#print axioms cubic_two_path_dyadic_plus_two_cycle
#print axioms cubic_edge_dyadic_plus_one_cycle
end E64Wave2Structural
