import Core
import Leaves
import PairedShadow
import ClosedDefectCore

/-!
Erdos 64 (Wave 3, Agent #3): Class H Auxiliary Graph 2-Degeneracy & Sharp C4-Free Edge Bound.
Covers ALL 4 open Class H leaves (`H-T-2`, `H-T-3`, `H-N-2`, `H-N-3`, with or without triangles).

For any subset S ⊆ V_{≥4} in a Class H MinimalBad(G) graph, let
  M(S) = {y ∈ V₃ : |N_G(y) ∩ S| ≥ 2} = N₂(S) ∪ N₃(S).
Each y ∈ M(S) has at least two neighbors in S; choosing one pair {u(y), v(y)} ⊆ N_G(y) ∩ S
defines a simple auxiliary graph H*(S) on S with |E(H*(S))| = |M(S)| (distinct y give distinct
pairs because G is C4-free). Every L-cycle in H*(S) lifts to a simple 2L-cycle in G, so H*(S) is
power-free (in particular C4-free) and has no Near induced subgraph (since |S| < |V(G)|).

Main unconditional all-order theorems (standard axioms only):
1. `no_near_two_degenerate_edges_induce`: Any finite simple graph H with no Near induced
   subgraph satisfies |E(H[T])| ≤ 2|T| - 3 for every T with |T| ≥ 2.
2. `no_near_c4free_edges_induce`: If H is additionally C4-free and |T| ≥ 4, then |E(H[T])| ≤ 2|T| - 4.
3. `class_h_n2_n3_le_two_sub_three`: For every S ⊆ V_{≥4} with |S| ≥ 2 in Class H MinimalBad(G),
   |N₂(S) ∪ N₃(S)| ≤ 2|S| - 3.
4. `class_h_n2_n3_le_two_sub_four`: For every S ⊆ V_{≥4} with |S| ≥ 4 in Class H MinimalBad(G),
   |N₂(S) ∪ N₃(S)| ≤ 2|S| - 4.
-/

namespace E64Wave3ClassH
open SimpleGraph Erdos64Closure E64Core E64Leaves Erdos64Paired E64DefectCore
universe u

variable {V : Type u}

/-- In a graph H on W with no Near induced subgraph, every subset T of size ≥ 2
    contains a vertex of induced degree ≤ 2. -/
theorem exists_deg_le_two_of_no_near {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (hnonear : ∀ (T : Finset W), ¬ Near (H.induce (T : Set W)))
    (T : Finset W) (hT : 2 ≤ T.card) :
    ∃ v : {x : W // x ∈ T}, (H.induce (T : Set W)).degree v ≤ 2 := by
  classical
  by_contra h
  push Not at h
  have hcard : 2 ≤ Fintype.card {x : W // x ∈ T} := by
    rw [Fintype.card_coe]; exact hT
  obtain ⟨v₀⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card {x : W // x ∈ T})
  have hnear : Near (H.induce (T : Set W)) :=
    near_of_except (H.induce (T : Set W)) v₀ hcard (fun v _ => by have := h v; omega)
  exact hnonear T hnear

/-- Edge count of H[T] when deleting one vertex v ∈ T:
    |E(H[T])| = |E(H[T.erase v])| + deg_{H[T]}(v). -/
theorem card_edgeFinset_induce_erase {W : Type u} [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (T : Finset W) (v : W) (hv : v ∈ T) :
    (H.induce (T : Set W)).edgeFinset.card =
      (H.induce ((T.erase v : Finset W) : Set W)).edgeFinset.card +
      (H.induce (T : Set W)).degree ⟨v, hv⟩ := by
  classical
  let HT := H.induce (T : Set W)
  let HT' := H.induce ((T.erase v : Finset W) : Set W)
  let vT : {x : W // x ∈ T} := ⟨v, hv⟩
  let E_inc : Finset (Sym2 {x : W // x ∈ T}) := HT.edgeFinset.filter (fun e => vT ∈ e)
  let E_rem : Finset (Sym2 {x : W // x ∈ T}) := HT.edgeFinset.filter (fun e => vT ∉ e)
  have hsplit : HT.edgeFinset.card = E_rem.card + E_inc.card := by
    rw [add_comm]
    exact (Finset.filter_card_add_filter_neg_card_eq_card (s := HT.edgeFinset) (p := fun e => vT ∈ e)).symm
  have hinc : E_inc.card = HT.degree vT := by
    let φ : HT.neighborFinset vT → E_inc := fun u =>
      ⟨s(vT, u.1), Finset.mem_filter.mpr ⟨(HT.mem_edgeFinset).mpr ((HT.mem_neighborFinset vT u.1).mp u.2),
        Sym2.mem_mk_left vT u.1⟩⟩
    have hφinj : Function.Injective φ := by
      intro a b hab
      have heq : s(vT, a.1) = s(vT, b.1) := congrArg Subtype.val hab
      rcases Sym2.eq_iff.mp heq with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact Subtype.ext h2
      · exact False.elim (HT.ne_of_adj ((HT.mem_neighborFinset vT a.1).mp a.2) h1)
    have hφsurj : Function.Surjective φ := by
      rintro ⟨e, he⟩
      obtain ⟨heE, hvmem⟩ := Finset.mem_filter.mp he
      induction e using Sym2.ind with
      | _ x y =>
        have hadj : HT.Adj x y := HT.mem_edgeFinset.mp heE
        rcases Sym2.mem_iff.mp hvmem with rfl | rfl
        · exact ⟨⟨y, (HT.mem_neighborFinset x y).mpr hadj⟩, Subtype.ext rfl⟩
        · exact ⟨⟨x, (HT.mem_neighborFinset y x).mpr hadj.symm⟩, Subtype.ext Sym2.eq_swap⟩
    have hc := Fintype.card_congr (Equiv.ofBijective φ ⟨hφinj, hφsurj⟩)
    rw [Fintype.card_coe, Fintype.card_coe, HT.card_neighborFinset_eq_degree] at hc
    exact hc.symm
  have hrem : E_rem.card = HT'.edgeFinset.card := by
    let liftV : {x : W // x ∈ T.erase v} → {x : W // x ∈ T} :=
      fun x => ⟨x.1, Finset.mem_of_mem_erase x.2⟩
    have hlift_inj : Function.Injective liftV := fun a b h =>
      Subtype.ext (congrArg Subtype.val h)
    let ψ : HT'.edgeFinset → E_rem := fun e =>
      ⟨e.1.map liftV, by
        refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · induction e.1 using Sym2.ind with
          | _ x y =>
            have hadj : HT'.Adj x y := HT'.mem_edgeFinset.mp e.2
            exact HT.mem_edgeFinset.mpr hadj
        · intro hmem
          obtain ⟨z, _, hz⟩ := Sym2.mem_map.mp hmem
          exact (Finset.mem_erase.mp z.2).1 (congrArg Subtype.val hz)⟩
    have hψinj : Function.Injective ψ := by
      intro a b hab
      apply Subtype.ext
      exact Sym2.map.injective hlift_inj (congrArg Subtype.val hab)
    have hψsurj : Function.Surjective ψ := by
      rintro ⟨e, he⟩
      obtain ⟨heE, hnv⟩ := Finset.mem_filter.mp he
      induction e using Sym2.ind with
      | _ x y =>
        have hadj : HT.Adj x y := HT.mem_edgeFinset.mp heE
        have hxv : x.1 ≠ v := fun h => hnv (by rw [show x = vT from Subtype.ext h]; exact Sym2.mem_mk_left _ _)
        have hyv : y.1 ≠ v := fun h => hnv (by rw [show y = vT from Subtype.ext h]; exact Sym2.mem_mk_right _ _)
        let x' : {z : W // z ∈ T.erase v} := ⟨x.1, Finset.mem_erase.mpr ⟨hxv, x.2⟩⟩
        let y' : {z : W // z ∈ T.erase v} := ⟨y.1, Finset.mem_erase.mpr ⟨hyv, y.2⟩⟩
        exact ⟨⟨s(x', y'), HT'.mem_edgeFinset.mpr hadj⟩, Subtype.ext rfl⟩
    have hc := Fintype.card_congr (Equiv.ofBijective ψ ⟨hψinj, hψsurj⟩)
    rw [Fintype.card_coe, Fintype.card_coe] at hc
    exact hc.symm
  rw [hsplit, hrem, hinc]

/-- Base case: a simple graph on 2 vertices has at most 1 edge. -/
theorem card_edgeFinset_le_one_of_card_two {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (h2 : Fintype.card W = 2) :
    H.edgeFinset.card ≤ 1 := by
  have hsum := H.sum_degrees_eq_twice_card_edges
  have hle : ∑ v : W, H.degree v ≤ ∑ _v : W, 1 := by
    apply Finset.sum_le_sum
    intro v _
    have := H.degree_lt_card_verts v
    omega
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, h2] at hle
  omega

/-- Base case: a C4-free simple graph on 4 vertices has at most 4 edges. -/
theorem card_edgeFinset_le_four_of_card_four_c4free {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (h4 : Fintype.card W = 4)
    (hfree : ¬ HasPower H) :
    H.edgeFinset.card ≤ 4 := by
  classical
  by_contra hgt
  have hge5 : 5 ≤ H.edgeFinset.card := by omega
  have hsum := H.sum_degrees_eq_twice_card_edges
  have hdeg_le3 : ∀ v : W, H.degree v ≤ 3 := fun v => by
    have := H.degree_lt_card_verts v; omega
  have hex_a : ∃ a : W, H.degree a = 3 := by
    by_contra h
    have hle2 : ∀ v : W, H.degree v ≤ 2 := fun v => by
      have := hdeg_le3 v
      have : H.degree v ≠ 3 := fun he => h ⟨v, he⟩
      omega
    have hle : ∑ v : W, H.degree v ≤ ∑ _v : W, 2 := Finset.sum_le_sum (fun v _ => hle2 v)
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, h4] at hle
    omega
  obtain ⟨a, ha⟩ := hex_a
  have hex_b : ∃ b : W, b ≠ a ∧ H.degree b = 3 := by
    by_contra h
    have hle2 : ∀ v : W, v ≠ a → H.degree v ≤ 2 := fun v hva => by
      have := hdeg_le3 v
      have : H.degree v ≠ 3 := fun he => h ⟨v, hva, he⟩
      omega
    have hle : ∑ v ∈ Finset.univ.erase a, H.degree v ≤ ∑ _v ∈ Finset.univ.erase a, 2 :=
      Finset.sum_le_sum (fun v hv => hle2 v (Finset.mem_erase.mp hv).1)
    have hsum_split : ∑ v : W, H.degree v = H.degree a + ∑ v ∈ Finset.univ.erase a, H.degree v :=
      (Finset.add_sum_erase Finset.univ H.degree (Finset.mem_univ a)).symm
    have hce : (Finset.univ.erase a).card = 3 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, h4]
    simp only [Finset.sum_const, hce, smul_eq_mul] at hle
    omega
  obtain ⟨b, hba, hb⟩ := hex_b
  let rest := (Finset.univ.erase a).erase b
  have hrest_card : rest.card = 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hba, Finset.mem_univ b⟩),
      Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, h4]
  obtain ⟨c, d, hcd, hrest_eq⟩ := Finset.card_eq_two.mp hrest_card
  have hc_mem : c ∈ rest := by rw [hrest_eq]; simp
  have hd_mem : d ∈ rest := by rw [hrest_eq]; simp
  have hca : c ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hc_mem).2).1
  have hcb : c ≠ b := (Finset.mem_erase.mp hc_mem).1
  have hda : d ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hd_mem).2).1
  have hdb : d ≠ b := (Finset.mem_erase.mp hd_mem).1
  have hall_adj : ∀ u v : W, H.degree u = 3 → v ≠ u → H.Adj u v := by
    intro u v hu hvu
    by_contra hna
    have hsub : H.neighborFinset u ⊆ (Finset.univ.erase u).erase v := by
      intro z hz
      have hadj := (H.mem_neighborFinset u z).mp hz
      refine Finset.mem_erase.mpr ⟨fun hzv => hna (hzv ▸ hadj),
        Finset.mem_erase.mpr ⟨(H.ne_of_adj hadj).symm, Finset.mem_univ z⟩⟩
    have hc := Finset.card_le_card hsub
    rw [H.card_neighborFinset_eq_degree, hu,
      Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hvu, Finset.mem_univ v⟩),
      Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ, h4] at hc
    omega
  have hac : H.Adj a c := hall_adj a c ha hca
  have had : H.Adj a d := hall_adj a d ha hda
  have hbc : H.Adj b c := hall_adj b c hb hcb
  have hbd : H.Adj b d := hall_adj b d hb hdb
  exact hfree (rectangle_power H hca.symm hba.symm hda.symm hcb hcd hdb hac hbc.symm hbd had.symm)

/-- General 2-degeneracy edge bound: any finite simple graph H with no Near induced subgraph
    satisfies |E(H[T])| ≤ 2|T| - 3 for every T with |T| ≥ 2. -/
theorem no_near_two_degenerate_edges_induce {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (hnonear : ∀ (T : Finset W), ¬ Near (H.induce (T : Set W))) :
    ∀ (n : ℕ) (T : Finset W), T.card = n → 2 ≤ n →
      (H.induce (T : Set W)).edgeFinset.card ≤ 2 * n - 3 := by
  intro n
  induction n with
  | zero => intro _ _ h2; omega
  | succ m ih =>
    intro T hcard h2
    by_cases hm2 : m + 1 = 2
    · have hc2 : Fintype.card {x : W // x ∈ T} = 2 := by rw [Fintype.card_coe]; omega
      have hle := card_edgeFinset_le_one_of_card_two (H.induce (T : Set W)) hc2
      omega
    · obtain ⟨⟨v, hv⟩, hdeg⟩ := exists_deg_le_two_of_no_near H hnonear T (by omega)
      have herase : (T.erase v).card = m := by
        rw [Finset.card_erase_of_mem hv]; omega
      have hih := ih (T.erase v) herase (by omega)
      have hsplit := card_edgeFinset_induce_erase H T v hv
      omega

/-- Sharp C4-free 2-degeneracy edge bound: any C4-free finite simple graph H with no Near
    induced subgraph satisfies |E(H[T])| ≤ 2|T| - 4 for every T with |T| ≥ 4. -/
theorem no_near_c4free_edges_induce {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (hfree : ¬ HasPower H)
    (hnonear : ∀ (T : Finset W), ¬ Near (H.induce (T : Set W))) :
    ∀ (n : ℕ) (T : Finset W), T.card = n → 4 ≤ n →
      (H.induce (T : Set W)).edgeFinset.card ≤ 2 * n - 4 := by
  intro n
  induction n with
  | zero => intro _ _ h4; omega
  | succ m ih =>
    intro T hcard h4
    by_cases hm4 : m + 1 = 4
    · have hc4 : Fintype.card {x : W // x ∈ T} = 4 := by rw [Fintype.card_coe]; omega
      have hfreeT : ¬ HasPower (H.induce (T : Set W)) :=
        fun hp => hfree (power_induce H (T : Set W) hp)
      have hle := card_edgeFinset_le_four_of_card_four_c4free (H.induce (T : Set W)) hc4 hfreeT
      omega
    · obtain ⟨⟨v, hv⟩, hdeg⟩ := exists_deg_le_two_of_no_near H hnonear T (by omega)
      have herase : (T.erase v).card = m := by
        rw [Finset.card_erase_of_mem hv]; omega
      have hih := ih (T.erase v) herase (by omega)
      have hsplit := card_edgeFinset_induce_erase H T v hv
      omega

/-- Helper: in MinimalBad(G), no two distinct vertices share two distinct common neighbors. -/
theorem unique_common_neighbor_h {G : SimpleGraph V} (hfree : ¬ HasPower G)
    {x y u v : V} (hxy : x ≠ y)
    (hxu : G.Adj x u) (hyu : G.Adj y u) (hxv : G.Adj x v) (hyv : G.Adj y v) :
    u = v := by
  by_contra huv
  exact hfree (rectangle_power G (G.ne_of_adj hxu) hxy (G.ne_of_adj hxv)
    (G.ne_of_adj hyu).symm huv (G.ne_of_adj hyv) hxu hyu.symm hyv hxv.symm)

/-- Helper: build the paired auxiliary graph on S ⊆ V_{≥4} from M(S) = {y ∈ V₃ | |N(y) ∩ S| ≥ 2}
    and prove it is power-free, has no Near induced subgraph, and has |E| = |M(S)|. -/
theorem class_h_aux_edges_eq_and_no_near [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G) (hH : HighDefect G)
    (S : Finset V) (hS4 : ∀ x ∈ S, 4 ≤ G.degree x) :
    let M : Finset V := Finset.univ.filter (fun y => G.degree y = 3 ∧ 2 ≤ (G.neighborFinset y ∩ S).card)
    ∃ (Haux : SimpleGraph {x : V // x ∈ S}) (_ : DecidableRel Haux.Adj),
      ¬ HasPower Haux ∧
      (∀ T : Finset {x : V // x ∈ S}, ¬ Near (Haux.induce (T : Set {x : V // x ∈ S}))) ∧
      Haux.edgeFinset.card = M.card := by
  classical
  intro M
  have hex_pair : ∀ y : {z : V // z ∈ M},
      ∃ a b : {x : V // x ∈ S}, a ≠ b ∧ G.Adj a.1 y.1 ∧ G.Adj b.1 y.1 := by
    intro y
    have hyM := (Finset.mem_filter.mp y.2).2.2
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (by omega : 1 < (G.neighborFinset y.1 ∩ S).card)
    obtain ⟨huN, huS⟩ := Finset.mem_inter.mp hu
    obtain ⟨hvN, hvS⟩ := Finset.mem_inter.mp hv
    exact ⟨⟨u, huS⟩, ⟨v, hvS⟩, fun h => huv (congrArg Subtype.val h),
      ((G.mem_neighborFinset y.1 u).mp huN).symm,
      ((G.mem_neighborFinset y.1 v).mp hvN).symm⟩
  choose p1 p2 hp_ne hp_adj1 hp_adj2 using hex_pair
  let R : {x : V // x ∈ S} → {z : V // z ∈ M} → Prop := fun x y => x = p1 y ∨ x = p2 y
  let Haux : SimpleGraph {x : V // x ∈ S} := pairedGraph R
  letI : DecidableRel Haux.Adj := fun a b => Classical.dec _
  have hpaired : Paired R := by
    intro y
    refine Or.inr ⟨p1 y, p2 y, hp_ne y, fun x => Iff.rfl⟩
  have hdisj : ∀ (x : {x : V // x ∈ S}) (y : {z : V // z ∈ M}), x.1 ≠ y.1 := by
    intro x y h
    have hx4 := hS4 x.1 x.2
    have hy3 := (Finset.mem_filter.mp y.2).2.1
    omega
  have hR_adj : ∀ (x : {x : V // x ∈ S}) (y : {z : V // z ∈ M}), R x y → G.Adj x.1 y.1 := by
    intro x y h
    rcases h with rfl | rfl
    · exact hp_adj1 y
    · exact hp_adj2 y
  have hHaux_free : ¬ HasPower Haux := by
    intro hpow
    have hrect : ∀ x₁ x₂ y₁ y₂, x₁ ≠ x₂ → y₁ ≠ y₂ →
        R x₁ y₁ → R x₁ y₂ → R x₂ y₁ → R x₂ y₂ → False := by
      intro x₁ x₂ y₁ y₂ hx hy h11 h12 h21 h22
      have heq := unique_common_neighbor_h hm.2.1 (fun h => hx (Subtype.ext h))
        (hR_adj x₁ y₁ h11) (hR_adj x₂ y₁ h21) (hR_adj x₁ y₂ h12) (hR_adj x₂ y₂ h22)
      exact hy (Subtype.ext heq)
    exact hm.2.1 (paired_power_lift G Subtype.val Subtype.val
      Subtype.val_injective Subtype.val_injective hdisj R hR_adj hpaired hrect hpow)
  obtain ⟨w₀, hw₀, _, _⟩ := hH
  have hScard_lt : Fintype.card {x : V // x ∈ S} < Fintype.card V := by
    apply Fintype.card_lt_of_injective_not_surjective Subtype.val Subtype.val_injective
    intro hsurj
    obtain ⟨x, hx⟩ := hsurj w₀
    have := hS4 x.1 x.2
    rw [hx, hw₀] at this
    omega
  have hnonear : ∀ T : Finset {x : V // x ∈ S}, ¬ Near (Haux.induce (T : Set {x : V // x ∈ S})) := by
    intro T hnear
    have hTlt : Fintype.card {x : {x : V // x ∈ S} // x ∈ T} < Fintype.card V := by
      have hle : Fintype.card {x : {x : V // x ∈ S} // x ∈ T} ≤ Fintype.card {x : V // x ∈ S} := by
        rw [Fintype.card_coe]
        exact Finset.card_le_univ T
      omega
    have hpow := hm.2.2.1 _ (Haux.induce (T : Set {x : V // x ∈ S})) hTlt hnear
    exact hHaux_free (power_induce Haux (T : Set {x : V // x ∈ S}) hpow)
  have hedge_eq : Haux.edgeFinset.card = M.card := by
    let φ : {z : V // z ∈ M} → Haux.edgeFinset := fun y =>
      ⟨s(p1 y, p2 y), Haux.mem_edgeFinset.mpr ⟨hp_ne y, y, Or.inl rfl, Or.inr rfl⟩⟩
    have hφinj : Function.Injective φ := by
      intro y₁ y₂ heq
      have hs : s(p1 y₁, p2 y₁) = s(p1 y₂, p2 y₂) := congrArg Subtype.val heq
      apply Subtype.ext
      rcases Sym2.eq_iff.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact unique_common_neighbor_h hm.2.1 (fun h => hp_ne y₁ (Subtype.ext h))
          (hp_adj1 y₁) (hp_adj2 y₁) (h1 ▸ hp_adj1 y₂) (h2 ▸ hp_adj2 y₂)
      · exact unique_common_neighbor_h hm.2.1 (fun h => hp_ne y₁ (Subtype.ext h))
          (hp_adj1 y₁) (hp_adj2 y₁) (h1 ▸ hp_adj2 y₂) (h2 ▸ hp_adj1 y₂)
    have hφsurj : Function.Surjective φ := by
      rintro ⟨e, he⟩
      induction e using Sym2.ind with
      | _ a b =>
        obtain ⟨hab, y, ha, hb⟩ := Haux.mem_edgeFinset.mp he
        refine ⟨y, Subtype.ext ?_⟩
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact False.elim (hab rfl)
        · rfl
        · exact Sym2.eq_swap
        · exact False.elim (hab rfl)
    have hc := Fintype.card_congr (Equiv.ofBijective φ ⟨hφinj, hφsurj⟩)
    rw [Fintype.card_coe, Fintype.card_coe] at hc
    exact hc.symm
  exact ⟨Haux, inferInstance, hHaux_free, hnonear, hedge_eq⟩

/-- Helper: inducing on `Finset.univ` preserves edgeFinset cardinality. -/
theorem card_edgeFinset_induce_univ {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] :
    (H.induce ((Finset.univ : Finset W) : Set W)).edgeFinset.card = H.edgeFinset.card := by
  classical
  let HU := H.induce ((Finset.univ : Finset W) : Set W)
  let e : HU.edgeFinset ≃ H.edgeFinset :=
    { toFun := fun x => ⟨x.1.map Subtype.val, by
        induction x.1 using Sym2.ind with
        | _ a b => exact H.mem_edgeFinset.mpr (HU.mem_edgeFinset.mp x.2)⟩
      invFun := fun x => ⟨x.1.map (fun v => ⟨v, Finset.mem_univ v⟩), by
        induction x.1 using Sym2.ind with
        | _ a b => exact HU.mem_edgeFinset.mpr (H.mem_edgeFinset.mp x.2)⟩
      left_inv := by
        intro x; apply Subtype.ext
        induction x.1 using Sym2.ind with
        | _ a b => rfl
      right_inv := by
        intro x; apply Subtype.ext
        induction x.1 using Sym2.ind with
        | _ a b => rfl }
  have hc := Fintype.card_congr e
  simpa only [Fintype.card_coe] using hc

/-- MAIN THEOREM 1 (Wave 3, Agent #3): Class H Structural Bound (|S| ≥ 2).
    In ANY Class H MinimalBad(G) (H-T-2, H-T-3, H-N-2, H-N-3), for every S ⊆ V_{≥4} with |S| ≥ 2,
    the number of cubic vertices with ≥ 2 neighbors in S satisfies |N₂(S) ∪ N₃(S)| ≤ 2|S| - 3. -/
theorem class_h_n2_n3_le_two_sub_three [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G) (hH : HighDefect G)
    (S : Finset V) (hS4 : ∀ x ∈ S, 4 ≤ G.degree x) (hS2 : 2 ≤ S.card) :
    (Finset.univ.filter (fun y : V => G.degree y = 3 ∧ 2 ≤ (G.neighborFinset y ∩ S).card)).card
      ≤ 2 * S.card - 3 := by
  classical
  obtain ⟨Haux, _, _, hnonear, hedge_eq⟩ := class_h_aux_edges_eq_and_no_near G hm hH S hS4
  rw [← hedge_eq, ← card_edgeFinset_induce_univ Haux]
  have hcard : (Finset.univ : Finset {x : V // x ∈ S}).card = S.card := by
    rw [Finset.card_univ, Fintype.card_coe]
  exact no_near_two_degenerate_edges_induce Haux hnonear S.card Finset.univ hcard hS2

/-- MAIN THEOREM 2 (Wave 3, Agent #3): Sharp C4-Free Class H Structural Bound (|S| ≥ 4).
    In ANY Class H MinimalBad(G) (H-T-2, H-T-3, H-N-2, H-N-3), for every S ⊆ V_{≥4} with |S| ≥ 4,
    |N₂(S) ∪ N₃(S)| ≤ 2|S| - 4. -/
theorem class_h_n2_n3_le_two_sub_four [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G) (hH : HighDefect G)
    (S : Finset V) (hS4 : ∀ x ∈ S, 4 ≤ G.degree x) (hS_ge4 : 4 ≤ S.card) :
    (Finset.univ.filter (fun y : V => G.degree y = 3 ∧ 2 ≤ (G.neighborFinset y ∩ S).card)).card
      ≤ 2 * S.card - 4 := by
  classical
  obtain ⟨Haux, _, hfree, hnonear, hedge_eq⟩ := class_h_aux_edges_eq_and_no_near G hm hH S hS4
  rw [← hedge_eq, ← card_edgeFinset_induce_univ Haux]
  have hcard : (Finset.univ : Finset {x : V // x ∈ S}).card = S.card := by
    rw [Finset.card_univ, Fintype.card_coe]
  exact no_near_c4free_edges_induce Haux hfree hnonear S.card Finset.univ hcard hS_ge4

#print axioms exists_deg_le_two_of_no_near
#print axioms card_edgeFinset_induce_erase
#print axioms no_near_two_degenerate_edges_induce
#print axioms no_near_c4free_edges_induce
#print axioms class_h_n2_n3_le_two_sub_three
#print axioms class_h_n2_n3_le_two_sub_four

end E64Wave3ClassH
