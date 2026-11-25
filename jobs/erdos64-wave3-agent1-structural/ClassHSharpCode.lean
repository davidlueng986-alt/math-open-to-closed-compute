import Core
import Leaves
import Incidence
import ClosedDefectCore
import PairedShadow

/-!
Erdos 64 (Wave 3, Agent #1): Sharp 2-Degeneracy / C4-Free Edge Bounds and
Class H F2-Code Weight Hierarchy (6 / 8 / 10 + excess degree sum).

Strictly upgrades Wave 2's Class H F2-code distance theorem (`wt(M z) ≥ 2d - 4`,
giving `d_min ≥ 4`) to:
- `|S| ≥ 2 → wt(M z) ≥ 6 + ∑ x ∈ S, (deg(x) - 4) ≥ 6`
- `|S| ≥ 4 → wt(M z) ≥ 8 + ∑ x ∈ S, (deg(x) - 4) ≥ 8`
- `|S| ≥ 6 → wt(M z) ≥ 10 + ∑ x ∈ S, (deg(x) - 4) ≥ 10`
via exact extremal degree-sum bounds for C4-free 2-degenerate simple graphs
(`≤ 4k - 6` for `k ≥ 2`, `≤ 4k - 8` for `k ≥ 4`, `≤ 4k - 10` for `k ≥ 6`).
Also proves the global proper-subgraph degree-sum bound for any `MinimalBad(G)`
of order `n ≥ 7`: `∑_{u ≠ v} deg_{G-v}(u) ≤ 4n - 14`.
-/

namespace E64Wave3HighCode
open SimpleGraph Erdos64Closure E64Core E64Leaves Erdos64Paired Erdos64Incidence E64DefectCore
open scoped BigOperators Sym2
universe u

/-- A finite simple graph is 2-degenerate if every nonempty induced subgraph
    has a vertex of degree at most 2. -/
def TwoDegenerate {W : Type u} [Fintype W] (H : SimpleGraph W) : Prop :=
  ∀ (U : Finset W), U.Nonempty →
    ∃ v ∈ U, ∀ [DecidablePred (H.Adj v)], (U.filter (fun u => H.Adj v u)).card ≤ 2

/-- A simple graph is C4-free if no four pairwise distinct vertices form a 4-cycle. -/
def C4Free {W : Type u} (H : SimpleGraph W) : Prop :=
  ∀ a b c d : W, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    H.Adj a b → H.Adj b c → H.Adj c d → H.Adj d a → False

/-- Induced subgraph on `{u : W | u ≠ v}` inherits `TwoDegenerate`. -/
private theorem two_deg_erase {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (h2 : TwoDegenerate H) (v : W) :
    TwoDegenerate (H.induce {u : W | u ≠ v}) := by
  classical
  intro U hU
  let U' : Finset W := U.map ⟨Subtype.val, Subtype.val_injective⟩
  have hU' : U'.Nonempty := Finset.Nonempty.map hU
  obtain ⟨x, hxU', hdeg⟩ := h2 U' hU'
  obtain ⟨⟨x', hx'ne⟩, hxU, rfl⟩ := Finset.mem_map.mp hxU'
  refine ⟨⟨x', hx'ne⟩, hxU, ?_⟩
  intro _
  have hcard : (U.filter (fun u => (H.induce {w : W | w ≠ v}).Adj ⟨x', hx'ne⟩ u)).card =
      (U'.filter (fun u => H.Adj x' u)).card := by
    apply Finset.card_bij (fun a _ => a.1)
    · intro a ha
      simp only [Finset.mem_filter] at ha ⊢
      exact ⟨Finset.mem_map.mpr ⟨a, ha.1, rfl⟩, ha.2⟩
    · intro a _ b _ h; exact Subtype.ext h
    · intro b hb
      simp only [Finset.mem_filter] at hb
      obtain ⟨a, haU, rfl⟩ := Finset.mem_map.mp hb.1
      exact ⟨a, Finset.mem_filter.mpr ⟨haU, hb.2⟩, rfl⟩
  rw [hcard]; exact hdeg

/-- Induced subgraph on `{u : W | u ≠ v}` inherits `C4Free`. -/
private theorem c4_free_erase {W : Type u} (H : SimpleGraph W) (hc4 : C4Free H) (v : W) :
    C4Free (H.induce {u : W | u ≠ v}) := by
  intro a b c d hab hac had hbc hbd hcd h1 h2 h3 h4
  exact hc4 a.1 b.1 c.1 d.1
    (fun h => hab (Subtype.ext h)) (fun h => hac (Subtype.ext h)) (fun h => had (Subtype.ext h))
    (fun h => hbc (Subtype.ext h)) (fun h => hbd (Subtype.ext h)) (fun h => hcd (Subtype.ext h))
    h1 h2 h3 h4

/-- Deleting a vertex `v` reduces the sum of degrees by `2 * H.degree v`. -/
private theorem sum_deg_erase {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (v : W)
    [DecidableRel (H.induce {u : W | u ≠ v}).Adj] :
    (∑ u : {u : W // u ≠ v}, (H.induce {w : W | w ≠ v}).degree u) + 2 * H.degree v =
      ∑ u : W, H.degree u := by
  classical
  let H' := H.induce {w : W | w ≠ v}
  have hdeg_other : ∀ u : {w : W // w ≠ v},
      H'.degree u + (if H.Adj v u.1 then 1 else 0) = H.degree u.1 := by
    intro u
    rw [← H'.card_neighborFinset_eq_degree, ← H.card_neighborFinset_eq_degree]
    have hbij : (H'.neighborFinset u).card = ((H.neighborFinset u.1).erase v).card := by
      apply Finset.card_bij (fun a _ => a.1)
      · intro a ha
        simp only [SimpleGraph.mem_neighborFinset, Finset.mem_erase] at ha ⊢
        exact ⟨a.2, ha⟩
      · intro a _ b _ h; exact Subtype.ext h
      · intro b hb
        simp only [Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hb
        exact ⟨⟨b, hb.1⟩, (H'.mem_neighborFinset u ⟨b, hb.1⟩).mpr hb.2, rfl⟩
    rw [hbij]
    by_cases hadj : H.Adj v u.1
    · simp only [hadj, ite_true]
      exact Finset.card_erase_add_one ((H.mem_neighborFinset u.1 v).mpr hadj.symm)
    · simp only [hadj, ite_false, add_zero]
      have hnot : v ∉ H.neighborFinset u.1 := fun hm => hadj ((H.mem_neighborFinset u.1 v).mp hm).symm
      rw [Finset.erase_eq_of_notMem hnot]
  have hsum_adj : (∑ u : {w : W // w ≠ v}, if H.Adj v u.1 then 1 else 0) = H.degree v := by
    rw [Finset.sum_boole, Nat.cast_id, ← H.card_neighborFinset_eq_degree]
    apply Finset.card_bij (fun a _ => a.1)
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      exact (H.mem_neighborFinset v a.1).mpr ha
    · intro a _ b _ h; exact Subtype.ext h
    · intro b hb
      have hadj := (H.mem_neighborFinset v b).mp hb
      exact ⟨⟨b, (H.ne_of_adj hadj).symm⟩, by simp [hadj], rfl⟩
  have hsum_other : (∑ u : {w : W // w ≠ v}, H.degree u.1) + H.degree v = ∑ u : W, H.degree u := by
    have hsplit : ∑ u : W, H.degree u =
        (∑ u ∈ Finset.univ.erase v, H.degree u) + H.degree v := by
      rw [add_comm]
      exact (Finset.add_sum_erase Finset.univ (fun u => H.degree u) (Finset.mem_univ v)).symm
    rw [hsplit]
    congr 1
    apply Finset.sum_bij (fun (a : {w : W // w ≠ v}) _ => a.1)
    · intro a _; exact Finset.mem_erase.mpr ⟨a.2, Finset.mem_univ _⟩
    · intro a _ b _ h; exact Subtype.ext h
    · intro b hb; exact ⟨⟨b, (Finset.mem_erase.mp hb).1⟩, Finset.mem_univ _, rfl⟩
    · intro _ _; rfl
  have hsum_eq : (∑ u : {w : W // w ≠ v}, H'.degree u) +
      (∑ u : {w : W // w ≠ v}, if H.Adj v u.1 then 1 else 0) =
      ∑ u : {w : W // w ≠ v}, H.degree u.1 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun u _ => hdeg_other u)
  rw [hsum_adj] at hsum_eq
  change (∑ u : {w : W // w ≠ v}, H'.degree u) + 2 * H.degree v = ∑ u : W, H.degree u
  omega

/-- Cardinality of `{u : W // u ≠ v}` plus 1 equals `Fintype.card W`. -/
private theorem card_erase_sub {W : Type u} [Fintype W] [DecidableEq W] (v : W) :
    Fintype.card {u : W // u ≠ v} + 1 = Fintype.card W := by
  rw [Fintype.card_subtype,
    show (Finset.univ.filter (fun u : W => u ≠ v)) = Finset.univ.erase v by ext z; simp]
  exact Finset.card_erase_add_one (Finset.mem_univ v)

/-- 1. Every 2-degenerate simple graph on `k ≥ 2` vertices has degree sum `≤ 4k - 6`. -/
theorem two_deg_sum_deg_le : ∀ (n : ℕ) {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj],
    Fintype.card W = n → 2 ≤ n → TwoDegenerate H →
    ∑ v : W, H.degree v ≤ 4 * n - 6 := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ h2 _; omega
  | succ m ih =>
    intro W _ _ H _ hcard hge2 h2
    classical
    by_cases hm2 : m = 1
    · subst hm2
      have hle1 : ∀ v : W, H.degree v ≤ 1 := by
        intro v
        have hlt := H.degree_lt_card_verts v
        omega
      have hsum : ∑ v : W, H.degree v ≤ ∑ _v : W, 1 := Finset.sum_le_sum (fun v _ => hle1 v)
      simp [hcard] at hsum
      omega
    · have hmge2 : 2 ≤ m := by omega
      have hne : (Finset.univ : Finset W).Nonempty :=
        Finset.card_pos.mp (by rw [Finset.card_univ]; omega)
      obtain ⟨v, _, hvdeg⟩ := h2 Finset.univ hne
      have hdv : H.degree v ≤ 2 := by
        rw [← H.card_neighborFinset_eq_degree]
        have heq : H.neighborFinset v = Finset.univ.filter (fun u => H.Adj v u) := by
          ext u; simp [SimpleGraph.mem_neighborFinset]
        rw [heq]; exact hvdeg
      let H' := H.induce {u : W | u ≠ v}
      have hcard' : Fintype.card {u : W // u ≠ v} = m := by
        have := card_erase_sub v; omega
      have hsub : ∑ u : {u : W // u ≠ v}, H'.degree u ≤ 4 * m - 6 := by
        convert ih H' hcard' hmge2 (two_deg_erase H h2 v)
      have hsplit : (∑ u : {u : W // u ≠ v}, H'.degree u) + 2 * H.degree v = ∑ u : W, H.degree u := by
        convert sum_deg_erase H v
      omega

/-- Base case `k = 4`: a C4-free simple graph on 4 vertices has degree sum `≤ 8`. -/
private theorem c4_free_four_sum_deg_le {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (hcard : Fintype.card W = 4) (hc4 : C4Free H) :
    ∑ v : W, H.degree v ≤ 8 := by
  classical
  by_contra hgt
  have hge9 : 9 ≤ ∑ v : W, H.degree v := by omega
  have heven : Even (∑ v : W, H.degree v) := by
    rw [H.sum_degrees_eq_twice_card_edges]
    exact ⟨H.edgeFinset.card, by ring⟩
  obtain ⟨t, ht⟩ := heven
  have hge10 : 10 ≤ ∑ v : W, H.degree v := by omega
  have hnonadj_sum : ∑ v : W, (3 - H.degree v) ≤ 2 := by
    have hle3 : ∀ v : W, H.degree v ≤ 3 := fun v => by
      have := H.degree_lt_card_verts v; omega
    have hadd : (∑ v : W, H.degree v) + (∑ v : W, (3 - H.degree v)) = ∑ _v : W, 3 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun v _ => by have := hle3 v; omega)
    simp [hcard] at hadd
    omega
  have hex_ac : ∃ a c : W, a ≠ c ∧
      ∀ x y : W, x ≠ y → (x ≠ a ∨ y ≠ c) → (x ≠ c ∨ y ≠ a) → H.Adj x y := by
    by_cases hna : ∃ a c : W, a ≠ c ∧ ¬ H.Adj a c
    · obtain ⟨a, c, hac, hnac⟩ := hna
      refine ⟨a, c, hac, fun x y hxy h1 h2 => ?_⟩
      by_contra hnxy
      have hdef : ∀ u : W, Fintype.card {z : W // z ≠ u ∧ ¬ H.Adj u z} = 3 - H.degree u := by
        intro u
        rw [Fintype.card_subtype]
        have hpart : (Finset.univ.filter (fun z => z ≠ u ∧ ¬ H.Adj u z)).card +
            (H.neighborFinset u).card = (Finset.univ.erase u).card := by
          rw [← Finset.card_union_of_disjoint]
          · congr 1; ext z
            simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
              SimpleGraph.mem_neighborFinset, Finset.mem_erase, and_true]
            constructor
            · rintro (⟨hne, _⟩ | hadj)
              · exact hne
              · exact (H.ne_of_adj hadj).symm
            · intro hne
              by_cases hadj : H.Adj u z
              · exact Or.inr hadj
              · exact Or.inl ⟨hne, hadj⟩
          · rw [Finset.disjoint_left]
            intro z hz1 hz2
            simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hz1 hz2
            exact hz1.2.2 hz2
        rw [H.card_neighborFinset_eq_degree, Finset.card_erase_of_mem (Finset.mem_univ u),
          Finset.card_univ, hcard] at hpart
        omega
      let P : Finset (W × W) := Finset.univ.filter (fun p => p.1 ≠ p.2 ∧ ¬ H.Adj p.1 p.2)
      have hPcard : P.card = ∑ u : W, (3 - H.degree u) := by
        have e : (Σ u : W, {z : W // z ≠ u ∧ ¬ H.Adj u z}) ≃ {p : W × W // p.1 ≠ p.2 ∧ ¬ H.Adj p.1 p.2} :=
          { toFun := fun q => ⟨(q.1, q.2.1), ⟨q.2.2.1.symm, q.2.2.2⟩⟩
            invFun := fun p => ⟨p.1.1, ⟨p.1.2, ⟨p.2.1.symm, p.2.2⟩⟩⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
        have hc := Fintype.card_congr e
        rw [Fintype.card_sigma, Fintype.card_subtype] at hc
        rw [← hc]
        exact Finset.sum_congr rfl (fun u _ => hdef u)
      have hsub : ({(a, c), (c, a), (x, y), (y, x)} : Finset (W × W)) ⊆ P := by
        intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hp with rfl | rfl | rfl | rfl
        · exact ⟨hac, hnac⟩
        · exact ⟨hac.symm, fun h => hnac h.symm⟩
        · exact ⟨hxy, hnxy⟩
        · exact ⟨hxy.symm, fun h => hnxy h.symm⟩
      have h4 : ({(a, c), (c, a), (x, y), (y, x)} : Finset (W × W)).card = 4 := by
        have hne1 : (a, c) ≠ (c, a) := fun h => hac (Prod.mk.inj h).1
        have hne2 : (a, c) ≠ (x, y) := fun h => by
          have hp := Prod.mk.inj h
          rcases h1 with h1' | h1'
          · exact h1' hp.1.symm
          · exact h1' hp.2.symm
        have hne3 : (a, c) ≠ (y, x) := fun h => by
          have hp := Prod.mk.inj h
          rcases h2 with h2' | h2'
          · exact h2' hp.2.symm
          · exact h2' hp.1.symm
        have hne4 : (c, a) ≠ (x, y) := fun h => by
          have hp := Prod.mk.inj h
          rcases h2 with h2' | h2'
          · exact h2' hp.1.symm
          · exact h2' hp.2.symm
        have hne5 : (c, a) ≠ (y, x) := fun h => by
          have hp := Prod.mk.inj h
          rcases h1 with h1' | h1'
          · exact h1' hp.2.symm
          · exact h1' hp.1.symm
        have hne6 : (x, y) ≠ (y, x) := fun h => hxy (Prod.mk.inj h).1
        simp [Finset.card_insert_of_notMem, hne1, hne2, hne3, hne4, hne5, hne6]
      have hle := Finset.card_le_card hsub
      omega
    · push Not at hna
      have hpos : 0 < Fintype.card W := by omega
      obtain ⟨a⟩ := Fintype.card_pos_iff.mp hpos
      have hex_c : ∃ c : W, c ≠ a := by
        by_contra hc; push Not at hc
        have : Fintype.card W ≤ 1 := Fintype.card_le_one_iff.mpr (fun x y => by rw [hc x, hc y])
        omega
      obtain ⟨c, hca⟩ := hex_c
      exact ⟨a, c, hca.symm, fun x y hxy _ _ => hna x y hxy⟩
  obtain ⟨a, c, hac, hadj_all⟩ := hex_ac
  have hrem_card : ((Finset.univ.erase a).erase c).card = 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hac.symm, Finset.mem_univ c⟩),
      Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, hcard]
  obtain ⟨b, d, hbd, heq_rem⟩ := Finset.card_eq_two.mp hrem_card
  have hbmem : b ∈ (Finset.univ.erase a).erase c := by rw [heq_rem]; simp
  have hdmem : d ∈ (Finset.univ.erase a).erase c := by rw [heq_rem]; simp
  simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hbmem hdmem
  have hab : a ≠ b := hbmem.2.symm
  have had : a ≠ d := hdmem.2.symm
  have hbc : b ≠ c := hbmem.1
  have hcd : c ≠ d := hdmem.1.symm
  exact hc4 a b c d hab hac had hbc hbd hcd
    (hadj_all a b hab (Or.inr hbc) (Or.inl hac))
    (hadj_all b c hbc (Or.inl hab.symm) (Or.inl hbc))
    (hadj_all c d hcd (Or.inl hac.symm) (Or.inr had.symm))
    (hadj_all d a had.symm (Or.inl had.symm) (Or.inl hcd.symm))

/-- 2. Every C4-free 2-degenerate simple graph on `k ≥ 4` vertices has degree sum `≤ 4k - 8`. -/
theorem c4_free_two_deg_sum_deg_le_eight : ∀ (n : ℕ) {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj],
    Fintype.card W = n → 4 ≤ n → TwoDegenerate H → C4Free H →
    ∑ v : W, H.degree v ≤ 4 * n - 8 := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ h4 _ _; omega
  | succ m ih =>
    intro W _ _ H _ hcard hge4 h2 hc4
    classical
    by_cases hm3 : m = 3
    · subst hm3
      have h := c4_free_four_sum_deg_le H hcard hc4
      omega
    · have hmge4 : 4 ≤ m := by omega
      have hne : (Finset.univ : Finset W).Nonempty :=
        Finset.card_pos.mp (by rw [Finset.card_univ]; omega)
      obtain ⟨v, _, hvdeg⟩ := h2 Finset.univ hne
      have hdv : H.degree v ≤ 2 := by
        rw [← H.card_neighborFinset_eq_degree]
        have heq : H.neighborFinset v = Finset.univ.filter (fun u => H.Adj v u) := by
          ext u; simp [SimpleGraph.mem_neighborFinset]
        rw [heq]; exact hvdeg
      let H' := H.induce {u : W | u ≠ v}
      have hcard' : Fintype.card {u : W // u ≠ v} = m := by
        have := card_erase_sub v; omega
      have hsub : ∑ u : {u : W // u ≠ v}, H'.degree u ≤ 4 * m - 8 := by
        convert ih H' hcard' hmge4 (two_deg_erase H h2 v) (c4_free_erase H hc4 v)
      have hsplit : (∑ u : {u : W // u ≠ v}, H'.degree u) + 2 * H.degree v = ∑ u : W, H.degree u := by
        convert sum_deg_erase H v
      omega

/-- 3. Five-vertex C4-free common-neighbor lemma:
    In any C4-free simple graph on 5 vertices with degree sum `≥ 12` (`≥ 6` edges),
    every two distinct vertices `x ≠ y` share a common neighbor. -/
theorem c4_free_five_common_neighbor {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (hcard : Fintype.card W = 5) (hc4 : C4Free H)
    (hsum : 12 ≤ ∑ v : W, H.degree v)
    {x y : W} (hxy : x ≠ y) : ∃ z : W, H.Adj x z ∧ H.Adj y z := by
  classical
  by_contra hno
  push Not at hno
  let Z : Finset W := (Finset.univ.erase x).erase y
  have hZcard : Z.card = 3 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hxy.symm, Finset.mem_univ y⟩),
      Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, hcard]
  obtain ⟨z₁, z₂, z₃, h12, h13, h23, hZeq⟩ := Finset.card_eq_three.mp hZcard
  have hz1 : z₁ ∈ Z := by rw [hZeq]; simp
  have hz2 : z₂ ∈ Z := by rw [hZeq]; simp
  have hz3 : z₃ ∈ Z := by rw [hZeq]; simp
  simp only [Z, Finset.mem_erase, Finset.mem_univ, and_true] at hz1 hz2 hz3
  have hne_all :
      x ≠ z₁ ∧ x ≠ z₂ ∧ x ≠ z₃ ∧ y ≠ z₁ ∧ y ≠ z₂ ∧ y ≠ z₃ :=
    ⟨hz1.2.symm, hz2.2.symm, hz3.2.symm, hz1.1.symm, hz2.1.symm, hz3.1.symm⟩
  let b (u v : W) : ℕ := if H.Adj u v then 1 else 0
  have hb_sym : ∀ u v, b u v = b v u := fun u v => by
    simp only [b]; by_cases h : H.Adj u v
    · simp [h, h.symm]
    · have h' : ¬ H.Adj v u := fun hv => h hv.symm
      simp [h, h']
  have huniv : (Finset.univ : Finset W) = {x, y, z₁, z₂, z₃} := by
    ext w
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    by_cases hwx : w = x
    · exact Or.inl hwx
    · by_cases hwy : w = y
      · exact Or.inr (Or.inl hwy)
      · have hwZ : w ∈ Z := Finset.mem_erase.mpr ⟨hwy, Finset.mem_erase.mpr ⟨hwx, Finset.mem_univ w⟩⟩
        rw [hZeq] at hwZ
        simp only [Finset.mem_insert, Finset.mem_singleton] at hwZ
        rcases hwZ with rfl | rfl | rfl
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  have hdeg_f : ∀ u : W, H.degree u = b u x + b u y + b u z₁ + b u z₂ + b u z₃ := by
    intro u
    rw [← H.card_neighborFinset_eq_degree]
    have h1 : (H.neighborFinset u).card = ∑ w : W, b u w := by
      rw [Finset.sum_boole, Nat.cast_id]
      congr 1; ext w; simp [SimpleGraph.mem_neighborFinset]
    rw [h1, huniv]
    rw [Finset.sum_insert (by simp [hxy, hne_all.1, hne_all.2.1, hne_all.2.2.1])]
    rw [Finset.sum_insert (by simp [hne_all.2.2.2.1, hne_all.2.2.2.2.1, hne_all.2.2.2.2.2])]
    rw [Finset.sum_insert (by simp [h12, h13])]
    rw [Finset.sum_insert (by simp [h23])]
    rw [Finset.sum_singleton]
    omega
  have hsum_eq : ∑ v : W, H.degree v =
      2 * (b x y + b x z₁ + b x z₂ + b x z₃ + b y z₁ + b y z₂ + b y z₃ +
           b z₁ z₂ + b z₁ z₃ + b z₂ z₃) := by
    rw [huniv]
    rw [Finset.sum_insert (by simp [hxy, hne_all.1, hne_all.2.1, hne_all.2.2.1])]
    rw [Finset.sum_insert (by simp [hne_all.2.2.2.1, hne_all.2.2.2.2.1, hne_all.2.2.2.2.2])]
    rw [Finset.sum_insert (by simp [h12, h13])]
    rw [Finset.sum_insert (by simp [h23])]
    rw [Finset.sum_singleton]
    simp only [hdeg_f]
    have hloop : ∀ u, b u u = 0 := fun u => by simp [b]
    rw [hloop x, hloop y, hloop z₁, hloop z₂, hloop z₃,
        hb_sym y x, hb_sym z₁ x, hb_sym z₂ x, hb_sym z₃ x,
        hb_sym z₁ y, hb_sym z₂ y, hb_sym z₃ y,
        hb_sym z₂ z₁, hb_sym z₃ z₁, hb_sym z₃ z₂]
    omega
  have hnc1 : ¬ (H.Adj x z₁ ∧ H.Adj y z₁) := fun h => hno z₁ h.1 h.2
  have hnc2 : ¬ (H.Adj x z₂ ∧ H.Adj y z₂) := fun h => hno z₂ h.1 h.2
  have hnc3 : ¬ (H.Adj x z₃ ∧ H.Adj y z₃) := fun h => hno z₃ h.1 h.2
  have htri_c4 : ∀ (u a b c : W),
      u ≠ a → u ≠ b → u ≠ c → a ≠ b → a ≠ c → b ≠ c →
      H.Adj u a → H.Adj u b → H.Adj a c → H.Adj b c → False :=
    fun u a b c hua hub huc hab hac hbc h1 h2 h3 h4 =>
      hc4 u a c b hua huc hub hac hab hbc.symm h1 h3 h4.symm h2.symm
  have hxy_c4 : ∀ (a b : W),
      x ≠ a → x ≠ b → y ≠ a → y ≠ b → a ≠ b →
      H.Adj x y → H.Adj x a → H.Adj y b → H.Adj a b → False :=
    fun a b hxa hxb hya hyb hab h1 h2 h3 h4 =>
      hc4 x y b a hxy hxb hxa hyb hya hab.symm h1 h3 h4.symm h2.symm
  by_cases h1 : H.Adj x z₁ <;> by_cases h2 : H.Adj x z₂ <;> by_cases h3 : H.Adj x z₃ <;>
  by_cases h4 : H.Adj y z₁ <;> by_cases h5 : H.Adj y z₂ <;> by_cases h6 : H.Adj y z₃ <;>
  by_cases h7 : H.Adj z₁ z₂ <;> by_cases h8 : H.Adj z₁ z₃ <;> by_cases h9 : H.Adj z₂ z₃ <;>
  by_cases h0 : H.Adj x y <;>
  first
  | exact hnc1 ⟨h1, h4⟩
  | exact hnc2 ⟨h2, h5⟩
  | exact hnc3 ⟨h3, h6⟩
  | exact htri_c4 x z₁ z₂ z₃ hne_all.1 hne_all.2.1 hne_all.2.2.1 h12 h13 h23 h1 h2 h8 h9
  | exact htri_c4 x z₁ z₃ z₂ hne_all.1 hne_all.2.2.1 hne_all.2.1 h13 h12 h23.symm h1 h3 h7 h9.symm
  | exact htri_c4 x z₂ z₃ z₁ hne_all.2.1 hne_all.2.2.1 hne_all.1 h23 h12.symm h13.symm h2 h3 h7.symm h8.symm
  | exact htri_c4 y z₁ z₂ z₃ hne_all.2.2.2.1 hne_all.2.2.2.2.1 hne_all.2.2.2.2.2 h12 h13 h23 h4 h5 h8 h9
  | exact htri_c4 y z₁ z₃ z₂ hne_all.2.2.2.1 hne_all.2.2.2.2.2 hne_all.2.2.2.2.1 h13 h12 h23.symm h4 h6 h7 h9.symm
  | exact htri_c4 y z₂ z₃ z₁ hne_all.2.2.2.2.1 hne_all.2.2.2.2.2 hne_all.2.2.2.1 h23 h12.symm h13.symm h5 h6 h7.symm h8.symm
  | exact hxy_c4 z₁ z₂ hne_all.1 hne_all.2.1 hne_all.2.2.2.1 hne_all.2.2.2.2.1 h12 h0 h1 h5 h7
  | exact hxy_c4 z₂ z₁ hne_all.2.1 hne_all.1 hne_all.2.2.2.2.1 hne_all.2.2.2.1 h12.symm h0 h2 h4 h7.symm
  | exact hxy_c4 z₁ z₃ hne_all.1 hne_all.2.2.1 hne_all.2.2.2.1 hne_all.2.2.2.2.2 h13 h0 h1 h6 h8
  | exact hxy_c4 z₃ z₁ hne_all.2.2.1 hne_all.1 hne_all.2.2.2.2.2 hne_all.2.2.2.1 h13.symm h0 h3 h4 h8.symm
  | exact hxy_c4 z₂ z₃ hne_all.2.1 hne_all.2.2.1 hne_all.2.2.2.2.1 hne_all.2.2.2.2.2 h23 h0 h2 h6 h9
  | exact hxy_c4 z₃ z₂ hne_all.2.2.1 hne_all.2.1 hne_all.2.2.2.2.2 hne_all.2.2.2.2.1 h23.symm h0 h3 h5 h9.symm
  | (simp only [b, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, ite_true, ite_false] at hsum_eq; omega)

/-- 4. Every C4-free 2-degenerate simple graph on `k ≥ 6` vertices has degree sum `≤ 4k - 10`. -/
theorem c4_free_two_deg_sum_deg_le_ten : ∀ (n : ℕ) {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj],
    Fintype.card W = n → 6 ≤ n → TwoDegenerate H → C4Free H →
    ∑ v : W, H.degree v ≤ 4 * n - 10 := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ h6 _ _; omega
  | succ m ih =>
    intro W _ _ H _ hcard hge6 h2 hc4
    classical
    by_cases hm5 : m = 5
    · subst hm5
      by_contra hgt
      have hge15 : 15 ≤ ∑ v : W, H.degree v := by omega
      have heven : Even (∑ v : W, H.degree v) := by
        rw [H.sum_degrees_eq_twice_card_edges]
        exact ⟨H.edgeFinset.card, by ring⟩
      obtain ⟨t, ht⟩ := heven
      have hge16 : 16 ≤ ∑ v : W, H.degree v := by omega
      have hne : (Finset.univ : Finset W).Nonempty :=
        Finset.card_pos.mp (by rw [Finset.card_univ]; omega)
      obtain ⟨v, _, hvdeg⟩ := h2 Finset.univ hne
      have hdv : H.degree v ≤ 2 := by
        rw [← H.card_neighborFinset_eq_degree]
        have heq : H.neighborFinset v = Finset.univ.filter (fun u => H.Adj v u) := by
          ext u; simp [SimpleGraph.mem_neighborFinset]
        rw [heq]; exact hvdeg
      let H' := H.induce {u : W | u ≠ v}
      have hcard' : Fintype.card {u : W // u ≠ v} = 5 := by
        have := card_erase_sub v; omega
      have hle12 : ∑ u : {u : W // u ≠ v}, H'.degree u ≤ 12 := by
        have h := c4_free_two_deg_sum_deg_le_eight 5 H' hcard' (by omega)
          (two_deg_erase H h2 v) (c4_free_erase H hc4 v)
        have h' : ∑ u : {u : W // u ≠ v}, H'.degree u ≤ 4 * 5 - 8 := by convert h
        omega
      have hsplit : (∑ u : {u : W // u ≠ v}, H'.degree u) + 2 * H.degree v = ∑ u : W, H.degree u := by
        convert sum_deg_erase H v
      have hsum12 : 12 ≤ ∑ u : {u : W // u ≠ v}, H'.degree u := by omega
      have hdv2 : H.degree v = 2 := by omega
      rw [← H.card_neighborFinset_eq_degree] at hdv2
      obtain ⟨x, y, hxy, hNxy⟩ := Finset.card_eq_two.mp hdv2
      have hxv : H.Adj v x := (H.mem_neighborFinset v x).mp (by rw [hNxy]; simp)
      have hyv : H.Adj v y := (H.mem_neighborFinset v y).mp (by rw [hNxy]; simp)
      let X : {u : W // u ≠ v} := ⟨x, (H.ne_of_adj hxv).symm⟩
      let Y : {u : W // u ≠ v} := ⟨y, (H.ne_of_adj hyv).symm⟩
      have hXY : X ≠ Y := fun h => hxy (congrArg Subtype.val h)
      obtain ⟨Z, hXZ, hYZ⟩ := c4_free_five_common_neighbor H' hcard' (c4_free_erase H hc4 v) hsum12 hXY
      exact hc4 v x Z.1 y (H.ne_of_adj hxv) Z.2.symm (H.ne_of_adj hyv)
        (H.ne_of_adj hXZ) hxy (H.ne_of_adj hYZ).symm hxv hXZ hYZ.symm hyv.symm
    · have hmge6 : 6 ≤ m := by omega
      have hne : (Finset.univ : Finset W).Nonempty :=
        Finset.card_pos.mp (by rw [Finset.card_univ]; omega)
      obtain ⟨v, _, hvdeg⟩ := h2 Finset.univ hne
      have hdv : H.degree v ≤ 2 := by
        rw [← H.card_neighborFinset_eq_degree]
        have heq : H.neighborFinset v = Finset.univ.filter (fun u => H.Adj v u) := by
          ext u; simp [SimpleGraph.mem_neighborFinset]
        rw [heq]; exact hvdeg
      let H' := H.induce {u : W | u ≠ v}
      have hcard' : Fintype.card {u : W // u ≠ v} = m := by
        have := card_erase_sub v; omega
      have hsub : ∑ u : {u : W // u ≠ v}, H'.degree u ≤ 4 * m - 10 := by
        convert ih H' hcard' hmge6 (two_deg_erase H h2 v) (c4_free_erase H hc4 v)
      have hsplit : (∑ u : {u : W // u ≠ v}, H'.degree u) + 2 * H.degree v = ∑ u : W, H.degree u := by
        convert sum_deg_erase H v
      omega

/-- Any power-free graph `H` on fewer vertices than a `MinimalBad` graph `G` is both
    `C4Free` and `TwoDegenerate`. -/
private theorem c4_free_and_two_deg_of_power_free {V W : Type u}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (hcard : Fintype.card W < Fintype.card V) (hfree : ¬ HasPower H) :
    C4Free H ∧ TwoDegenerate H := by
  classical
  constructor
  · intro a b c d hab hac had hbc hbd hcd h1 h2 h3 h4
    exact hfree (rectangle_power H hab hac had hbc hbd hcd h1 h2 h3 h4)
  · intro U hU
    by_contra hall
    push Not at hall
    let HU := H.induce (U : Set W)
    have hdeg_ge3 : ∀ x : U, 3 ≤ HU.degree x := by
      intro x
      obtain ⟨_, hgt⟩ := hall x.1 x.2
      rw [← HU.card_neighborFinset_eq_degree]
      have hbij : (HU.neighborFinset x).card = (U.filter (fun u => H.Adj x.1 u)).card := by
        apply Finset.card_bij (fun a _ => a.1)
        · intro a ha
          simp only [SimpleGraph.mem_neighborFinset] at ha
          exact Finset.mem_filter.mpr ⟨a.2, ha⟩
        · intro a _ b _ h; exact Subtype.ext h
        · intro b hb
          simp only [Finset.mem_filter] at hb
          exact ⟨⟨b, hb.1⟩, (HU.mem_neighborFinset x ⟨b, hb.1⟩).mpr hb.2, rfl⟩
      rw [hbij]
      have : 2 < (U.filter (fun u => H.Adj x.1 u)).card := by convert hgt
      omega
    obtain ⟨u₀, hu₀⟩ := hU
    have hnear : Near HU := ⟨⟨⟨u₀, hu₀⟩, hdeg_ge3 ⟨u₀, hu₀⟩⟩, ⟨⟨u₀, hu₀⟩, fun x _ => hdeg_ge3 x⟩⟩
    have hcardU : Fintype.card U < Fintype.card V := by
      have hle : Fintype.card U ≤ Fintype.card W := by
        rw [Fintype.card_coe]; exact Finset.card_le_univ U
      omega
    have hpowU : HasPower HU := hm.2.2.1 U HU hcardU hnear
    obtain ⟨k, v₀, c, hk, hc, hlen⟩ := hpowU
    let emb : HU →g H := ⟨Subtype.val, fun h => h⟩
    let cH : H.Walk v₀.1 v₀.1 := c.map emb
    have hcH_len : cH.length = 2 ^ k := by rw [Walk.length_map, hlen]
    have hcH_supp : cH.support = c.support.map Subtype.val := Walk.support_map emb c
    have hcH_tail : cH.support.tail.Nodup := by
      rw [hcH_supp, ← List.map_tail]
      exact (List.nodup_map_iff Subtype.val_injective).mpr hc.support_nodup
    have h4 : 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide : 0 < 2) hk
    have hcH_nil : ¬ cH.Nil := by
      intro h; have := Walk.length_eq_zero_iff.mpr h; omega
    have hcH_cyc : cH.IsCycle := by
      apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      refine ⟨Walk.IsPath.mk' ?_, by omega⟩
      rwa [Walk.support_tail_of_not_nil _ hcH_nil]
    exact hfree ⟨k, v₀.1, cH, hk, hcH_cyc, hcH_len⟩

/-- 5. Global proper-subgraph degree-sum bound for any `MinimalBad(G)` of order `n ≥ 7`:
    for every `v : V`, the vertex-deleted graph `G - v` has degree sum `≤ 4n - 14`. -/
theorem minimal_bad_proper_sum_deg_le {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (hn : 7 ≤ Fintype.card V) (v : V)
    [DecidableRel (G.induce {u : V | u ≠ v}).Adj] :
    ∑ u : {u : V // u ≠ v}, (G.induce {w : V | w ≠ v}).degree u ≤ 4 * Fintype.card V - 14 := by
  classical
  let G' := G.induce {w : V | w ≠ v}
  have hcard' : Fintype.card {w : V // w ≠ v} = Fintype.card V - 1 := by
    have := card_erase_sub v; omega
  have hcard_lt : Fintype.card {w : V // w ≠ v} < Fintype.card V := by omega
  have hfree' : ¬ HasPower G' := by
    rintro ⟨k, v₀, c, hk, hc, hlen⟩
    let emb : G' →g G := ⟨Subtype.val, fun h => h⟩
    let cG : G.Walk v₀.1 v₀.1 := c.map emb
    have hcG_len : cG.length = 2 ^ k := by rw [Walk.length_map, hlen]
    have hcG_tail : cG.support.tail.Nodup := by
      rw [Walk.support_map, ← List.map_tail]
      exact (List.nodup_map_iff Subtype.val_injective).mpr hc.support_nodup
    have h4 : 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide : 0 < 2) hk
    have hcG_nil : ¬ cG.Nil := by
      intro h; have := Walk.length_eq_zero_iff.mpr h; omega
    have hcG_cyc : cG.IsCycle := by
      apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      refine ⟨Walk.IsPath.mk' ?_, by omega⟩
      rwa [Walk.support_tail_of_not_nil _ hcG_nil]
    exact hm.2.1 ⟨k, v₀.1, cG, hk, hcG_cyc, hcG_len⟩
  obtain ⟨hc4, h2⟩ := c4_free_and_two_deg_of_power_free G hm G' hcard_lt hfree'
  have h := c4_free_two_deg_sum_deg_le_ten (Fintype.card V - 1) G' hcard' (by omega) h2 hc4
  have h' : ∑ u : {w : V // w ≠ v}, (G.induce {w : V | w ≠ v}).degree u ≤
      4 * (Fintype.card V - 1) - 10 := by convert h
  omega

/-- Local helper: V_{>=4} is independent in MinimalBad(G). -/
private theorem high_indep {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {a b : V} (ha : 4 ≤ G.degree a) (hb : 4 ≤ G.degree b) : ¬ G.Adj a b := by
  classical
  intro hab
  obtain ⟨_, w, hw⟩ := hm.1
  have hcard : 2 ≤ Fintype.card V := by have := G.degree_lt_card_verts a; omega
  let H := G \ SimpleGraph.edge a b
  have hnear : Near H := by
    apply near_of_except H w hcard
    intro v hv
    have hdeg := erase_edge_degree G a b hab v
    change H.degree v + (if v = a ∨ v = b then 1 else 0) = G.degree v at hdeg
    by_cases hva : v = a
    · subst v; simp at hdeg; omega
    · by_cases hvb : v = b
      · subst v; simp at hdeg; omega
      · simp [hva, hvb] at hdeg; rw [hdeg]; exact hw v hv
  have hEq : H = G := hm.2.2.2 H sdiff_le hnear
  have he : H.Adj a b := hEq ▸ hab
  have hno : ¬ H.Adj a b := by
    intro h
    have hn := (SimpleGraph.sdiff_adj G (SimpleGraph.edge a b) a b).mp h
    exact hn.2 ((SimpleGraph.edge_adj a b a b).mpr ⟨Or.inl ⟨rfl, rfl⟩, G.ne_of_adj hab⟩)
  exact hno he

/-- Local helper: every neighbor of V_{>=4} has degree 3. -/
private theorem high_nbr_cubic {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {a y : V} (ha : 4 ≤ G.degree a) (hay : G.Adj a y) : G.degree y = 3 := by
  have hy2 := no_small_defect G hm y
  have hy_not2 : G.degree y ≠ 2 := fun hyw => by
    have := defect_neighbor_cubic G hm hyw hay.symm; omega
  have hy_not4 : ¬ 4 ≤ G.degree y := fun hy4 => high_indep G hm ha hy4 hay
  omega

/-- Master midpoint-graph bridge for Class H F2-code weights. -/
private theorem high_code_midpoint_bridge {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (hH : HighDefect G)
    (z : {v : V // 4 ≤ G.degree v} → ZMod 2) :
    let V₄ := {v : V // 4 ≤ G.degree v}
    let V₃ := {v : V // G.degree v = 3}
    let R : V₄ → V₃ → Prop := fun a y => G.Adj a.1 y.1
    letI : DecidableRel R := fun _ _ => Classical.dec _
    ∃ (H : SimpleGraph (Support z)),
      C4Free H ∧ TwoDegenerate H ∧
      ∀ [DecidableRel H.Adj],
        (∑ x : Support z, H.degree x) + Fintype.card {y : V₃ // syndrome R z y = 1} =
          ∑ x : Support z, G.degree x.1.1 := by
  classical
  intro V₄ V₃ R
  let S := Support z
  let O := {y : V₃ // syndrome R z y = 1}
  have hex : ∀ y : O, ∃ x : S, R x.1 y.1 := by
    intro y
    have hmod := support_row_mod R z y.1
    rw [y.2] at hmod
    have hval : (1 : ZMod 2).val = 1 := rfl
    rw [hval] at hmod
    change Fintype.card {x : S // R x.1 y.1} % 2 = 1 at hmod
    have hpos : 0 < Fintype.card {x : S // R x.1 y.1} := by omega
    obtain ⟨⟨x, hx⟩⟩ := Fintype.card_pos_iff.mp hpos
    exact ⟨x, hx⟩
  choose pick hpick using hex
  let R' : S → V₃ → Prop := fun x y => R x.1 y ∧ ∀ hy : syndrome R z y = 1, pick ⟨y, hy⟩ ≠ x
  have hrow : ∀ y : V₃, Fintype.card {x : S // R' x y} = 0 ∨ Fintype.card {x : S // R' x y} = 2 := by
    intro y
    have hle3 : Fintype.card {x : S // R x.1 y} ≤ 3 := by
      let emb : {x : S // R x.1 y} → G.neighborSet y.1 := fun x => ⟨x.1.1.1, x.2.symm⟩
      have hinj : Function.Injective emb := by
        intro a b h
        apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
        exact congrArg (fun t : G.neighborSet y.1 => t.1) h
      have hc := Fintype.card_le_of_injective emb hinj
      rw [SimpleGraph.card_neighborSet_eq_degree, y.2] at hc
      exact hc
    have hmod := support_row_mod R z y
    rcases field_cases (syndrome R z y) with h0 | h1
    · have heq : Fintype.card {x : S // R' x y} = Fintype.card {x : S // R x.1 y} := by
        apply Fintype.card_congr
        exact Equiv.subtypeEquivRight (fun x => by simp [R', h0])
      rw [h0] at hmod
      have hval : (0 : ZMod 2).val = 0 := rfl
      rw [hval] at hmod
      change Fintype.card {x : S // R x.1 y} % 2 = 0 at hmod
      omega
    · have heq : Fintype.card {x : S // R' x y} = Fintype.card {x : S // R x.1 y ∧ x ≠ pick ⟨y, h1⟩} := by
        apply Fintype.card_congr
        refine Equiv.subtypeEquivRight (fun x => ?_)
        constructor
        · rintro ⟨hr, hne⟩; exact ⟨hr, (hne h1).symm⟩
        · rintro ⟨hr, hne⟩; exact ⟨hr, fun _ => hne.symm⟩
      rw [heq]
      have hrem := card_remove_one (fun x : S => R x.1 y) (pick ⟨y, h1⟩) (hpick ⟨y, h1⟩)
      rw [h1] at hmod
      have hval : (1 : ZMod 2).val = 1 := rfl
      rw [hval] at hmod
      change Fintype.card {x : S // R x.1 y} % 2 = 1 at hmod
      omega
  have hpaired : Paired R' :=
    paired_of_two_rows R' (fun y => by simpa only [Fintype.card_subtype] using hrow y)
  let H : SimpleGraph S := shadow R'
  have hdisj : ∀ x : S, ∀ y : V₃, x.1.1 ≠ y.1 := fun x y heq => by
    have h1 := x.1.2; have h2 := y.2; rw [heq] at h1; omega
  have huniq : ∀ (a b : S) (y z : V₃), a ≠ b → R' a y → R' b y →
      R' a z → R' b z → y = z := by
    intro a b y z hab hay hby haz hbz
    by_contra hn
    exact hm.2.1 (rectangle_power G (hdisj a y) (fun h => hab (Subtype.ext (Subtype.ext h)))
      (hdisj a z) (Ne.symm (hdisj b y)) (fun h => hn (Subtype.ext h)) (hdisj b z)
      hay.1 hby.1.symm hbz.1 haz.1.symm)
  have hfreeH : ¬ HasPower H := by
    rintro ⟨k, a₀, c, hk, hc, hlen⟩
    have hge4 : 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide : 0 < 2) hk
    have hV₃ : Nonempty V₃ := by
      cases hce : c with
      | nil => rw [hce] at hlen; simp at hlen; omega
      | cons hadj _ => obtain ⟨_, y, _, _⟩ := hadj; exact ⟨y⟩
    let midY : Sym2 S → V₃ := fun e =>
      if h : ∃ y : V₃, ∀ x ∈ e, R' x y then Classical.choose h
      else Classical.choice hV₃
    have hmid : ∀ {a b : S}, H.Adj a b → R' a (midY s(a, b)) ∧ R' b (midY s(a, b)) := by
      intro a b he
      obtain ⟨_, y, ha, hb⟩ := he
      have hex' : ∃ y : V₃, ∀ x ∈ s(a, b), R' x y := ⟨y, Sym2.ball.mpr ⟨ha, hb⟩⟩
      unfold midY
      simp only [hex', dite_true]
      exact Sym2.ball.mp (Classical.choose_spec hex')
    have hinjMid : ∀ e ∈ H.edgeSet, ∀ e' ∈ H.edgeSet, midY e = midY e' → e = e' := by
      intro e he e' he' hmeq
      obtain ⟨a, b⟩ := e
      obtain ⟨c', d⟩ := e'
      have h1 : H.Adj a b := H.mem_edgeSet.mp he
      have h2 : H.Adj c' d := H.mem_edgeSet.mp he'
      have h1' := hmid h1
      have h2' := hmid h2
      rw [← hmeq] at h2'
      have all : ∀ w : S, R' w (midY s(a, b)) → w = a ∨ w = b := by
        intro w hw
        by_cases hwa : w = a
        · exact Or.inl hwa
        · exact Or.inr ((hpaired _ a h1'.1).unique ⟨hwa, hw⟩ ⟨h1.1.symm, h1'.2⟩)
      rcases all c' h2'.1 with rfl | rfl <;> rcases all d h2'.2 with rfl | rfl
      · exact False.elim (h2.1 rfl)
      · rfl
      · exact Sym2.eq_swap
      · exact False.elim (h2.1 rfl)
    let f : S → V := fun x => x.1.1
    let mid : Sym2 S → V := fun e => (midY e).1
    have hf : Function.Injective f := fun p q h => Subtype.ext (Subtype.ext h)
    have hnodup_mid : (c.edges.map mid).Nodup := by
      apply (List.nodup_map_iff_inj_on hc.isTrail.edges_nodup).mpr
      intro e he e' he' hh
      exact hinjMid e (c.edges_subset_edgeSet he) e' (c.edges_subset_edgeSet he') (Subtype.ext hh)
    have hdisj_mid : (c.support.tail.map f).Disjoint (c.edges.map mid) := by
      intro v h1 h2
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp h1
      obtain ⟨e, _, he⟩ := List.mem_map.mp h2
      exact hdisj x (midY e) he.symm
    exact hm.2.1 (Erdos64Shadow.power_cycle_expand f mid
      (fun h => (hmid h).1.1) (fun h => (hmid h).2.1.symm)
      c hc hf hnodup_mid hdisj_mid hk hlen)
  obtain ⟨w₀, hw₀, _, _⟩ := hH
  have hcardS : Fintype.card S < Fintype.card V := by
    apply Fintype.card_lt_of_injective_not_surjective (fun x : S => x.1.1)
      (fun p q h => Subtype.ext (Subtype.ext h))
    intro hsurj
    obtain ⟨x, hx⟩ := hsurj w₀
    dsimp only at hx
    have := x.1.2; rw [hx, hw₀] at this; omega
  obtain ⟨hc4, h2⟩ := c4_free_and_two_deg_of_power_free G hm H hcardS hfreeH
  refine ⟨H, hc4, h2, ?_⟩
  intro _
  let del : S → ℕ := fun x => Fintype.card {y : O // pick y = x}
  have hsum_del : ∑ x : S, del x = Fintype.card O := by
    have e : (Σ x : S, {y : O // pick y = x}) ≃ O :=
      { toFun := fun p => p.2.1
        invFun := fun y => ⟨pick y, ⟨y, rfl⟩⟩
        left_inv := by rintro ⟨x, ⟨y, rfl⟩⟩; rfl
        right_inv := by intro y; rfl }
    rw [← Fintype.card_congr e, Fintype.card_sigma]
  have hdeg_mid : ∀ x : S, H.degree x = Fintype.card {y : V₃ // R' x y} := by
    intro x
    let pickNbr : {y : V₃ // R' x y} → H.neighborSet x := fun y =>
      let b := Classical.choose (hpaired y.1 x y.2).exists
      let hb := Classical.choose_spec (hpaired y.1 x y.2).exists
      ⟨b, ⟨hb.1.symm, y.1, y.2, hb.2⟩⟩
    have hpinj : Function.Injective pickNbr := by
      intro y z heq
      apply Subtype.ext
      let b := Classical.choose (hpaired y.1 x y.2).exists
      have hb := Classical.choose_spec (hpaired y.1 x y.2).exists
      have hz := Classical.choose_spec (hpaired z.1 x z.2).exists
      have hbe : b = Classical.choose (hpaired z.1 x z.2).exists := congrArg Subtype.val heq
      have hbz : R' b z.1 := by rw [hbe]; exact hz.2
      exact huniq x b y.1 z.1 hb.1.symm y.2 hb.2 z.2 hbz
    have hpsurj : Function.Surjective pickNbr := by
      rintro ⟨b, ⟨hxb, y, hxy, hby⟩⟩
      refine ⟨⟨y, hxy⟩, Subtype.ext ?_⟩
      have hb := Classical.choose_spec (hpaired y x hxy).exists
      exact (hpaired y x hxy).unique hb ⟨hxb.symm, hby⟩
    have hc := Fintype.card_congr (Equiv.ofBijective pickNbr ⟨hpinj, hpsurj⟩)
    rw [SimpleGraph.card_neighborSet_eq_degree] at hc
    exact hc.symm
  have hdeg_eq : ∀ x : S, H.degree x + del x = G.degree x.1.1 := by
    intro x
    rw [hdeg_mid x]
    let e_all : {y : V₃ // R x.1 y} ≃ G.neighborSet x.1.1 :=
      { toFun := fun y => ⟨y.1.1, y.2⟩
        invFun := fun u => ⟨⟨u.1, high_nbr_cubic G hm x.1.2 u.2⟩, u.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hall : Fintype.card {y : V₃ // R x.1 y} = G.degree x.1.1 := by
      rw [Fintype.card_congr e_all, SimpleGraph.card_neighborSet_eq_degree]
    let e_split : {y : V₃ // R x.1 y} ≃ {y : V₃ // R' x y} ⊕ {y : O // pick y = x} :=
      { toFun := fun y =>
          if h : ∃ hy : syndrome R z y.1 = 1, pick ⟨y.1, hy⟩ = x then
            Sum.inr ⟨⟨y.1, h.1⟩, h.2⟩
          else
            Sum.inl ⟨y.1, ⟨y.2, fun hy heq => h ⟨hy, heq⟩⟩⟩
        invFun := Sum.elim (fun y => ⟨y.1, y.2.1⟩)
          (fun y => ⟨y.1.1, by have hp := hpick y.1; rw [y.2] at hp; exact hp⟩)
        left_inv := by
          intro y
          by_cases h : ∃ hy : syndrome R z y.1 = 1, pick ⟨y.1, hy⟩ = x <;> simp [h]
        right_inv := by
          rintro (y | ⟨⟨y, hy⟩, hpick_eq⟩)
          · have hnot : ¬ ∃ hy : syndrome R z y.1 = 1, pick ⟨y.1, hy⟩ = x :=
              fun ⟨hy, heq⟩ => y.2.2 hy heq
            simp [hnot]
          · have hex' : ∃ hy' : syndrome R z y = 1, pick ⟨y, hy'⟩ = x := ⟨hy, hpick_eq⟩
            simp [hex'] }
    have hc := Fintype.card_congr e_split
    rw [hall, Fintype.card_sum] at hc
    exact hc.symm
  have hsum_all : (∑ x : S, H.degree x) + Fintype.card O = ∑ x : S, G.degree x.1.1 := by
    rw [← hsum_del, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => hdeg_eq x)
  convert hsum_all

/-- Arithmetic helper: `∑_{x : S} deg(x) = 4 * |S| + ∑_{x : S} (deg(x) - 4)`. -/
private theorem sum_deg_eq_four_add_excess {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (z : {v : V // 4 ≤ G.degree v} → ZMod 2) :
    ∑ x : Support z, G.degree x.1.1 =
      4 * Fintype.card (Support z) + ∑ x : Support z, (G.degree x.1.1 - 4) := by
  have h : ∑ x : Support z, G.degree x.1.1 =
      ∑ x : Support z, (4 + (G.degree x.1.1 - 4)) :=
    Finset.sum_congr rfl (fun x _ => by have := x.1.2; omega)
  rw [h, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]

/-- 6. NEW (Wave 3, Agent #1): Class H Sharp Code Weight (`|S| ≥ 2`). -/
theorem high_code_weight_ge_six {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G) (hH : HighDefect G)
    (z : {v : V // 4 ≤ G.degree v} → ZMod 2)
    (hS2 : 2 ≤ Fintype.card (Support z)) :
    let V₄ := {v : V // 4 ≤ G.degree v}
    let V₃ := {v : V // G.degree v = 3}
    let R : V₄ → V₃ → Prop := fun a y => G.Adj a.1 y.1
    letI : DecidableRel R := fun _ _ => Classical.dec _
    6 + (∑ x : Support z, (G.degree x.1.1 - 4)) ≤
      Fintype.card {y : V₃ // syndrome R z y = 1} := by
  classical
  intro V₄ V₃ R
  suffices h : 6 + (∑ x : Support z, (G.degree x.1.1 - 4)) ≤
      Fintype.card {y : V₃ // syndrome R z y = 1} by convert h
  obtain ⟨H, _, h2, hbridge⟩ := high_code_midpoint_bridge G hm hH z
  have hsum : (∑ x : Support z, H.degree x) + Fintype.card {y : V₃ // syndrome R z y = 1} =
      ∑ x : Support z, G.degree x.1.1 := by convert hbridge
  have hle := two_deg_sum_deg_le (Fintype.card (Support z)) H rfl hS2 h2
  have hex := sum_deg_eq_four_add_excess G z
  omega

/-- 7. NEW (Wave 3, Agent #1): Class H Sharp Code Weight (`|S| ≥ 4`). -/
theorem high_code_weight_ge_eight {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G) (hH : HighDefect G)
    (z : {v : V // 4 ≤ G.degree v} → ZMod 2)
    (hS4 : 4 ≤ Fintype.card (Support z)) :
    let V₄ := {v : V // 4 ≤ G.degree v}
    let V₃ := {v : V // G.degree v = 3}
    let R : V₄ → V₃ → Prop := fun a y => G.Adj a.1 y.1
    letI : DecidableRel R := fun _ _ => Classical.dec _
    8 + (∑ x : Support z, (G.degree x.1.1 - 4)) ≤
      Fintype.card {y : V₃ // syndrome R z y = 1} := by
  classical
  intro V₄ V₃ R
  suffices h : 8 + (∑ x : Support z, (G.degree x.1.1 - 4)) ≤
      Fintype.card {y : V₃ // syndrome R z y = 1} by convert h
  obtain ⟨H, hc4, h2, hbridge⟩ := high_code_midpoint_bridge G hm hH z
  have hsum : (∑ x : Support z, H.degree x) + Fintype.card {y : V₃ // syndrome R z y = 1} =
      ∑ x : Support z, G.degree x.1.1 := by convert hbridge
  have hle := c4_free_two_deg_sum_deg_le_eight (Fintype.card (Support z)) H rfl hS4 h2 hc4
  have hex := sum_deg_eq_four_add_excess G z
  omega

/-- 8. NEW (Wave 3, Agent #1): Class H Sharp Code Weight (`|S| ≥ 6`). -/
theorem high_code_weight_ge_ten {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G) (hH : HighDefect G)
    (z : {v : V // 4 ≤ G.degree v} → ZMod 2)
    (hS6 : 6 ≤ Fintype.card (Support z)) :
    let V₄ := {v : V // 4 ≤ G.degree v}
    let V₃ := {v : V // G.degree v = 3}
    let R : V₄ → V₃ → Prop := fun a y => G.Adj a.1 y.1
    letI : DecidableRel R := fun _ _ => Classical.dec _
    10 + (∑ x : Support z, (G.degree x.1.1 - 4)) ≤
      Fintype.card {y : V₃ // syndrome R z y = 1} := by
  classical
  intro V₄ V₃ R
  suffices h : 10 + (∑ x : Support z, (G.degree x.1.1 - 4)) ≤
      Fintype.card {y : V₃ // syndrome R z y = 1} by convert h
  obtain ⟨H, hc4, h2, hbridge⟩ := high_code_midpoint_bridge G hm hH z
  have hsum : (∑ x : Support z, H.degree x) + Fintype.card {y : V₃ // syndrome R z y = 1} =
      ∑ x : Support z, G.degree x.1.1 := by convert hbridge
  have hle := c4_free_two_deg_sum_deg_le_ten (Fintype.card (Support z)) H rfl hS6 h2 hc4
  have hex := sum_deg_eq_four_add_excess G z
  omega

#print axioms two_deg_sum_deg_le
#print axioms c4_free_two_deg_sum_deg_le_eight
#print axioms c4_free_five_common_neighbor
#print axioms c4_free_two_deg_sum_deg_le_ten
#print axioms minimal_bad_proper_sum_deg_le
#print axioms high_code_weight_ge_six
#print axioms high_code_weight_ge_eight
#print axioms high_code_weight_ge_ten

end E64Wave3HighCode
