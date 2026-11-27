import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic

/-!
# Erdős Problem #64 — Wave 8 Guided Agent #3 (`wave8_agent3`)
## Part 2: Universal Girth-`g` Safe `V₃`-Component Deletion & Global Discharging on `H[V₃]`

Unconditionally proves for every girth `g ≥ 4` that every edge-and-vertex-minimal `MinimalBad2`
graph satisfies:
  `(5g - 3) * |V₃(G)| ≥ 4(g - 1) * |V(G)| - 6(g - 1) * |D|`
unifying `8/11` (`g=5`), `20/27` (`g=6`), and strictly improving to `3/4` (`g=7`) and
`16/21` (`g=8 → 9`, automatically via `PowerFree`).
-/

namespace E64Wave8Agent3P2

open SimpleGraph

def IsPow2 (n : ℕ) : Prop := ∃ k : ℕ, 2 ≤ k ∧ n = 2 ^ k

def HasPow2Cycle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ IsPow2 p.length

def PowerFree {V : Type*} (G : SimpleGraph V) : Prop := ¬ HasPow2Cycle G

def GirthGe {V : Type*} (G : SimpleGraph V) (g : ℕ) : Prop :=
  ∀ (v : V) (p : G.Walk v v), p.IsCycle → g ≤ p.length

noncomputable def Defects {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Finset V :=
  Finset.univ.filter (fun v => G.degree v < 3)

noncomputable def V3 {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Finset V :=
  Finset.univ.filter (fun v => G.degree v = 3)

noncomputable def V4 {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Finset V :=
  Finset.univ.filter (fun v => 4 ≤ G.degree v)

/-- `MinimalBad2EV G`: an edge-and-vertex-minimal `PowerFree` graph with `δ(G) ≥ 2` and
at most 2 defects (as realized by `G = H - ab` for any edge-and-vertex-minimal counterexample
to `EGRob3ConnCore`). -/
structure MinimalBad2EV.{u} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop where
  power_free : PowerFree G
  min_deg_two : ∀ v : V, 2 ≤ G.degree v
  defects_le_two : (Defects G).card ≤ 2
  vertex_minimal : ∀ {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj],
    Nonempty W →
    Fintype.card W < Fintype.card V →
    (∀ w : W, 2 ≤ H.degree w) →
    (Defects H).card ≤ 2 →
    HasPow2Cycle H
  edge_minimal : ∀ (H : SimpleGraph V) [DecidableRel H.Adj],
    H ≤ G →
    (∃ u v : V, G.Adj u v ∧ ¬ H.Adj u v) →
    (∀ w : V, 2 ≤ H.degree w) →
    (Defects H).card ≤ 2 →
    HasPow2Cycle H

/-- Lift a simple cycle from an induced subgraph `G.induce S` back to `G`. -/
lemma hasPow2Cycle_of_induce {V : Type*} (G : SimpleGraph V) (S : Set V)
    (h : HasPow2Cycle (G.induce S)) : HasPow2Cycle G := by
  rcases h with ⟨v, p, hcyc, hpow⟩
  let f : G.induce S →g G :=
    ⟨Subtype.val, fun h => h⟩
  have hinj : Function.Injective f := Subtype.val_injective
  refine ⟨v.1, p.map f, ?_, ?_⟩
  · exact hcyc.map hinj
  · simpa [Walk.length_map] using hpow

/-- Lift a simple cycle from a subgraph `H ≤ G` back to `G`. -/
lemma hasPow2Cycle_of_le {V : Type*} {H G : SimpleGraph V} (hle : H ≤ G)
    (h : HasPow2Cycle H) : HasPow2Cycle G := by
  rcases h with ⟨v, p, hcyc, hpow⟩
  let f : H →g G := ⟨id, fun hadj => hle hadj⟩
  refine ⟨v, p.map f, hcyc.map Function.injective_id, ?_⟩
  simpa [Walk.length_map] using hpow

/--
Theorem 1 (`minimal_bad2_vge4_independent`):
In any edge-and-vertex-minimal `MinimalBad2EV` graph `G`, `V₄(G)` is an independent set:
no two vertices of degree `≥ 4` are adjacent.
-/
theorem minimal_bad2_vge4_independent.{u} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmb : MinimalBad2EV G) {u v : V}
    (hu : 4 ≤ G.degree u) (hv : 4 ≤ G.degree v) :
    ¬ G.Adj u v := by
  classical
  intro huv
  let H : SimpleGraph V := G.deleteEdges {s(u, v)}
  have hle : H ≤ G := deleteEdges_le {s(u, v)}
  have hnot_adj : ¬ H.Adj u v := by
    simp [H, deleteEdges_adj]
  have hdeg_ge : ∀ w : V, (w ≠ u ∧ w ≠ v → H.degree w = G.degree w) ∧
      (w = u → G.degree u - 1 ≤ H.degree u) ∧
      (w = v → G.degree v - 1 ≤ H.degree v) := by
    intro w
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨hwu, hwv⟩
      rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
      congr 1; ext z
      simp only [mem_neighborFinset, H, deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff]
      constructor
      · exact fun h => h.1
      · intro hadj
        refine ⟨hadj, ?_⟩
        rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact hwu rfl
        · exact hwv rfl
    · intro _
      rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
      have hsub : (G.neighborFinset u).erase v ⊆ H.neighborFinset u := by
        intro z hz
        have hzv : z ≠ v := (Finset.mem_erase.mp hz).1
        have huz : G.Adj u z := (mem_neighborFinset G u z).mp (Finset.mem_erase.mp hz).2
        rw [mem_neighborFinset, deleteEdges_adj]
        refine ⟨huz, ?_⟩
        simp only [Set.mem_singleton_iff, Sym2.eq_iff]
        rintro (⟨_, rfl⟩ | ⟨rfl, _⟩)
        · exact hzv rfl
        · exact G.ne_of_adj huv rfl
      have hcard := Finset.card_le_card hsub
      have hv_mem : v ∈ G.neighborFinset u := (mem_neighborFinset G u v).mpr huv
      rw [Finset.card_erase_of_mem hv_mem] at hcard
      exact hcard
    · intro _
      rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
      have hsub : (G.neighborFinset v).erase u ⊆ H.neighborFinset v := by
        intro z hz
        have hzu : z ≠ u := (Finset.mem_erase.mp hz).1
        have hvz : G.Adj v z := (mem_neighborFinset G v z).mp (Finset.mem_erase.mp hz).2
        rw [mem_neighborFinset, deleteEdges_adj]
        refine ⟨hvz, ?_⟩
        simp only [Set.mem_singleton_iff, Sym2.eq_iff]
        rintro (⟨rfl, _⟩ | ⟨_, rfl⟩)
        · exact G.ne_of_adj huv.symm rfl
        · exact hzu rfl
      have hcard := Finset.card_le_card hsub
      have hu_mem : u ∈ G.neighborFinset v := (mem_neighborFinset G v u).mpr huv.symm
      rw [Finset.card_erase_of_mem hu_mem] at hcard
      exact hcard
  have hH_min2 : ∀ w : V, 2 ≤ H.degree w := by
    intro w
    by_cases hwu : w = u
    · rw [hwu]; have := (hdeg_ge u).2.1 rfl; omega
    · by_cases hwv : w = v
      · rw [hwv]; have := (hdeg_ge v).2.2 rfl; omega
      · rw [(hdeg_ge w).1 ⟨hwu, hwv⟩]; exact hmb.min_deg_two w
  have hH_def : (Defects H).card ≤ (Defects G).card := by
    refine Finset.card_le_card ?_
    intro w hw
    simp only [Defects, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    by_cases hwu : w = u
    · rw [hwu] at hw ⊢; have := (hdeg_ge u).2.1 rfl; omega
    · by_cases hwv : w = v
      · rw [hwv] at hw ⊢; have := (hdeg_ge v).2.2 rfl; omega
      · rw [← (hdeg_ge w).1 ⟨hwu, hwv⟩]; exact hw
  have hpow := hmb.edge_minimal H hle ⟨u, v, huv, hnot_adj⟩ hH_min2
    (le_trans hH_def hmb.defects_le_two)
  exact hmb.power_free (hasPow2Cycle_of_le hle hpow)

/-- Helper: deleting a subset `S ⊆ V₃(G)` whose external boundary lies in `V₄(G)` with each
`w ∈ V₄(G)` having at most 1 neighbor in `S` is impossible in `MinimalBad2EV`. -/
lemma safe_delete_v3_subset_impossible.{u} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmb : MinimalBad2EV G) (S : Finset V) (hSne : S.Nonempty)
    (hcomp_ne : ∃ z : V, z ∉ S)
    (hno_nonV4 : ∀ x ∈ S, ∀ y : V, G.Adj x y → y ∉ S → 4 ≤ G.degree y)
    (hat_most_one : ∀ y : V, y ∉ S → 4 ≤ G.degree y → (G.neighborFinset y ∩ S).card ≤ 1) :
    False := by
  classical
  let W := {w : V // w ∉ S}
  let H : SimpleGraph W := G.induce {w : V | w ∉ S}
  have hneW : Nonempty W := by rcases hcomp_ne with ⟨z, hz⟩; exact ⟨⟨z, hz⟩⟩
  have hcard_lt : Fintype.card W < Fintype.card V := by
    rcases hSne with ⟨s, hs⟩
    have hlt : (Finset.univ.filter (fun w : V => w ∉ S)).card <
        (Finset.univ : Finset V).card := by
      refine Finset.card_lt_card ?_
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.filter_subset _ _, ?_⟩
      intro heq
      have hm : s ∈ Finset.univ.filter (fun w : V => w ∉ S) := by
        rw [heq]; exact Finset.mem_univ s
      exact (Finset.mem_filter.mp hm).2 hs
    simpa [W, Fintype.card_subtype] using hlt
  have hdeg_H : ∀ x : W,
      H.degree x + (G.neighborFinset x.1 ∩ S).card = G.degree x.1 := by
    intro x
    rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
    have hbij : (H.neighborFinset x).card = (G.neighborFinset x.1 \ S).card := by
      refine Finset.card_bij (fun y _ => y.1) ?_ ?_ ?_
      · intro y hy
        exact Finset.mem_sdiff.mpr
          ⟨(mem_neighborFinset G x.1 y.1).mpr ((mem_neighborFinset H x y).mp hy), y.2⟩
      · intro y₁ _ y₂ _ heq; exact Subtype.ext heq
      · intro w hw
        have hw1 := (mem_neighborFinset G x.1 w).mp (Finset.mem_sdiff.mp hw).1
        have hw2 := (Finset.mem_sdiff.mp hw).2
        exact ⟨⟨w, hw2⟩, (mem_neighborFinset H x ⟨w, hw2⟩).mpr hw1, rfl⟩
    rw [hbij, Finset.card_sdiff_add_card_inter]
  have hH_min2 : ∀ x : W, 2 ≤ H.degree x := by
    intro x
    have hd := hdeg_H x
    by_cases h4 : 4 ≤ G.degree x.1
    · have h1 := hat_most_one x.1 x.2 h4
      omega
    · have h0 : (G.neighborFinset x.1 ∩ S).card = 0 := by
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro s hs
        have hs1 := (mem_neighborFinset G x.1 s).mp (Finset.mem_inter.mp hs).1
        have hs2 := (Finset.mem_inter.mp hs).2
        exact h4 (hno_nonV4 s hs2 x.1 hs1.symm x.2)
      have := hmb.min_deg_two x.1
      omega
  have hH_def : (Defects H).card ≤ (Defects G).card := by
    refine Finset.card_le_card_of_injOn (fun x => x.1) ?_ ?_
    · intro x hx
      rw [Finset.mem_coe, Defects, Finset.mem_filter] at hx ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      dsimp only
      have hxlt : H.degree x < 3 := hx.2
      have hd := hdeg_H x
      by_cases h4 : 4 ≤ G.degree x.1
      · have h1 := hat_most_one x.1 x.2 h4
        omega
      · have h0 : (G.neighborFinset x.1 ∩ S).card = 0 := by
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro s hs
          have hs1 := (mem_neighborFinset G x.1 s).mp (Finset.mem_inter.mp hs).1
          have hs2 := (Finset.mem_inter.mp hs).2
          exact h4 (hno_nonV4 s hs2 x.1 hs1.symm x.2)
        omega
    · intro x₁ _ x₂ _ heq; exact Subtype.ext heq
  have hpow := hmb.vertex_minimal H hneW hcard_lt hH_min2 (le_trans hH_def hmb.defects_le_two)
  exact hmb.power_free (hasPow2Cycle_of_induce G {w : V | w ∉ S} hpow)

/--
Theorem 2 (`minimal_bad2_v3_no_all_high_neighbors`):
In any `MinimalBad2EV` graph `G`, no vertex `u ∈ V₃(G)` can have all 3 of its neighbors in `V₄(G)`.
-/
theorem minimal_bad2_v3_no_all_high_neighbors.{u} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmb : MinimalBad2EV G) {u : V} (hu : G.degree u = 3) :
    ∃ w : V, G.Adj u w ∧ G.degree w < 4 := by
  by_contra hall
  push Not at hall
  have hex : ∃ z : V, z ∉ ({u} : Finset V) := by
    have hpos : 0 < (G.neighborFinset u).card := by
      rw [card_neighborFinset_eq_degree, hu]; omega
    rcases Finset.card_pos.mp hpos with ⟨w, hw⟩
    have huw := (mem_neighborFinset G u w).mp hw
    exact ⟨w, by simp [(G.ne_of_adj huw).symm]⟩
  exact safe_delete_v3_subset_impossible G hmb {u} (Finset.singleton_nonempty u) hex
    (by
      intro x hx y hxy _
      rw [Finset.mem_singleton] at hx; subst hx
      exact hall y hxy)
    (by
      intro y _ _
      exact le_trans (Finset.card_le_card Finset.inter_subset_right) (by simp))

/-- Helper: closing a simple path `p : a ↝ b` (length ≥ 1) via a single cherry `a - w - b`
avoiding `p.support` gives a simple `(p.length + 2)`-cycle. -/
private lemma cycle_of_path_and_cherry' {V : Type*} (G : SimpleGraph V)
    {w a b : V} (p : G.Walk a b) (hp : p.IsPath) (hab : a ≠ b)
    (hwa : G.Adj w a) (hwb : G.Adj w b) (hw_not : w ∉ p.support) :
    ∃ q : G.Walk w w, q.IsCycle ∧ q.length = p.length + 2 := by
  let q : G.Walk w w := Walk.cons hwa (p.append (Walk.cons hwb.symm Walk.nil))
  have hlen : q.length = p.length + 2 := by simp [q, Walk.length_cons, Walk.length_append]
  have hsup : q.support = w :: (p.support ++ [w]) := by
    simp [q, Walk.support_cons, Walk.support_append, Walk.support_nil]
  have htail_nodup : q.support.tail.Nodup := by
    rw [hsup, List.tail_cons, List.nodup_append]
    refine ⟨hp.support_nodup, List.nodup_singleton w, ?_⟩
    intro x hx y hxw rfl
    rw [List.mem_singleton] at hxw
    exact hw_not (hxw ▸ hx)
  have h_no_w : ∀ e ∈ p.edges, w ∉ e := fun e he hm => by
    rcases Sym2.mem_iff_exists.mp hm with ⟨z, rfl⟩
    exact hw_not (Walk.fst_mem_support_of_mem_edges p he)
  have hq_cyc : q.IsCycle := by
    rw [Walk.isCycle_def]
    refine ⟨?_, ?_, htail_nodup⟩
    · rw [Walk.isTrail_def]
      have heq : q.edges = s(w, a) :: (p.edges ++ [s(b, w)]) := by
        simp [q, Walk.edges_cons, Walk.edges_append, Walk.edges_nil]
      rw [heq, List.nodup_cons]
      refine ⟨?_, ?_⟩
      · simp only [List.mem_append, List.mem_singleton, not_or, Sym2.eq_iff]
        exact ⟨fun hm => h_no_w s(w, a) hm (Sym2.mem_mk_left w a),
          ⟨fun ⟨h, _⟩ => hw_not (h ▸ Walk.end_mem_support p), fun ⟨_, h⟩ => hab h⟩⟩
      · rw [List.nodup_append]
        refine ⟨hp.isTrail.edges_nodup, List.nodup_singleton _, ?_⟩
        intro e he e' hbw rfl
        rw [List.mem_singleton] at hbw
        subst hbw
        exact h_no_w s(b, w) he (Sym2.mem_mk_right b w)
    · simp [q]
  exact ⟨q, hq_cyc, hlen⟩

/--
Theorem 3 (`minimal_bad2_v3_component_size_ge_girth_sub_one`):
**Universal Girth-`g` Component Size Lower Bound**:
In any `MinimalBad2EV` graph `G` with `GirthGe G g` (`g ≥ 4`) and `(V4 G).Nonempty`,
every nonempty connected subset `S ⊆ V₃(G)` whose external neighbors all lie in `V₄(G)`
satisfies `g - 1 ≤ S.card`.
-/
theorem minimal_bad2_v3_component_size_ge_girth_sub_one.{u} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmb : MinimalBad2EV G) {g : ℕ} (hg : GirthGe G g)
    (hV4 : (V4 G).Nonempty)
    (S : Finset V) (hSne : S.Nonempty) (hS3 : S ⊆ V3 G)
    (hconn : (G.induce (S : Set V)).Connected)
    (hno_nonV4 : ∀ x ∈ S, ∀ y : V, G.Adj x y → y ∉ S → 4 ≤ G.degree y) :
    g - 1 ≤ S.card := by
  classical
  by_contra hlt
  have hle : S.card ≤ g - 2 := by omega
  have hcomp_ne : ∃ z : V, z ∉ S := by
    rcases hV4 with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    intro hzS
    have h3 : G.degree z = 3 := (Finset.mem_filter.mp (hS3 hzS)).2
    have h4 : 4 ≤ G.degree z := (Finset.mem_filter.mp hz).2
    omega
  refine safe_delete_v3_subset_impossible G hmb S hSne hcomp_ne hno_nonV4 ?_
  intro y hyS hy4
  by_contra hgt1
  have hge2 : 1 < (G.neighborFinset y ∩ S).card := by omega
  rcases Finset.one_lt_card.mp hge2 with ⟨a, ha, b, hb, hab⟩
  have ha_adj : G.Adj y a := (mem_neighborFinset G y a).mp (Finset.mem_inter.mp ha).1
  have ha_S : a ∈ S := (Finset.mem_inter.mp ha).2
  have hb_adj : G.Adj y b := (mem_neighborFinset G y b).mp (Finset.mem_inter.mp hb).1
  have hb_S : b ∈ S := (Finset.mem_inter.mp hb).2
  have hreach : (G.induce (S : Set V)).Reachable ⟨a, ha_S⟩ ⟨b, hb_S⟩ := hconn ⟨a, ha_S⟩ ⟨b, hb_S⟩
  rcases hreach with ⟨w0⟩
  let p0 := w0.toPath
  let f : G.induce (S : Set V) →g G := ⟨Subtype.val, fun h => h⟩
  let p : G.Walk a b := p0.1.map f
  have hp_path : p.IsPath := p0.2.map Subtype.val_injective
  have hsup_sub : ∀ x ∈ p.support, x ∈ S := by
    intro x hx
    rw [Walk.support_map] at hx
    rcases List.mem_map.mp hx with ⟨u, _, rfl⟩
    exact u.2
  have hlen_le : p.length ≤ S.card - 1 := by
    have hnodup : p.support.Nodup := hp_path.support_nodup
    have hsub_fin : p.support.toFinset ⊆ S := by
      intro x hx; exact hsup_sub x (List.mem_toFinset.mp hx)
    have hcard_le : p.support.length ≤ S.card := by
      rw [← List.toFinset_card_of_nodup hnodup]
      exact Finset.card_le_card hsub_fin
    have hsup_len : p.support.length = p.length + 1 := Walk.length_support p
    omega
  have hy_not : y ∉ p.support := fun hm => hyS (hsup_sub y hm)
  rcases cycle_of_path_and_cherry' G p hp_path hab ha_adj hb_adj hy_not with ⟨q, hq_cyc, hq_len⟩
  have hqg := hg y q hq_cyc
  have hSpos : 1 ≤ S.card := Finset.card_pos.mpr hSne
  omega

/-- Helper: in any nonempty connected finset `S`, `2 * (S.card - 1) ≤ ∑ v ∈ S, deg_S(v)`. -/
lemma connected_sum_deg_ge {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hSne : S.Nonempty)
    (hconn : (G.induce (S : Set V)).Connected) :
    2 * (S.card - 1) ≤ ∑ v ∈ S, (G.neighborFinset v ∩ S).card := by
  classical
  have hstep : ∀ k : ℕ, 1 ≤ k → k ≤ S.card →
      ∃ T : Finset V, T ⊆ S ∧ T.card = k ∧
        2 * (k - 1) ≤ ∑ v ∈ T, (G.neighborFinset v ∩ T).card := by
    intro k hk1 hkS
    induction k with
    | zero => omega
    | succ m ih =>
      rcases Nat.eq_zero_or_pos m with rfl | hmpos
      · rcases hSne with ⟨r, hr⟩
        exact ⟨{r}, Finset.singleton_subset_iff.mpr hr, by simp, by simp⟩
      · rcases ih (by omega) (by omega) with ⟨T, hTS, hTcard, hTsum⟩
        have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
        have hSdiff_ne : (S \ T).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro hemp
          have hST : S ⊆ T := Finset.sdiff_eq_empty_iff_subset.mp hemp
          have : S.card ≤ T.card := Finset.card_le_card hST
          omega
        have hcross : ∃ u ∈ T, ∃ w ∈ S \ T, G.Adj u w := by
          rcases hTne with ⟨t0, ht0⟩
          rcases hSdiff_ne with ⟨s0, hs0⟩
          have hs0S : s0 ∈ S := (Finset.mem_sdiff.mp hs0).1
          rcases hconn ⟨t0, hTS ht0⟩ ⟨s0, hs0S⟩ with ⟨walk⟩
          have hwalk_cross : ∀ {a b : {x : V // x ∈ S}} (p : (G.induce (S : Set V)).Walk a b),
              a.1 ∈ T → b.1 ∉ T → ∃ u ∈ T, ∃ z ∈ S \ T, G.Adj u z := by
            intro a b p
            induction p with
            | nil => intro ha hb; exact absurd ha hb
            | cons hxy r ihr =>
              rename_i x y z
              intro hx hz
              by_cases hy : y.1 ∈ T
              · exact ihr hy hz
              · exact ⟨x.1, hx, y.1, Finset.mem_sdiff.mpr ⟨y.2, hy⟩, hxy⟩
          exact hwalk_cross walk ht0 (Finset.mem_sdiff.mp hs0).2
        rcases hcross with ⟨u, huT, w, hwST, huw⟩
        have hwS : w ∈ S := (Finset.mem_sdiff.mp hwST).1
        have hwT : w ∉ T := (Finset.mem_sdiff.mp hwST).2
        let T' := insert w T
        refine ⟨T', Finset.insert_subset_iff.mpr ⟨hwS, hTS⟩,
          by rw [Finset.card_insert_of_notMem hwT, hTcard], ?_⟩
        rw [Finset.sum_insert hwT]
        have hw_deg : 1 ≤ (G.neighborFinset w ∩ T').card := by
          refine Finset.card_pos.mpr ⟨u, Finset.mem_inter.mpr
            ⟨(mem_neighborFinset G w u).mpr huw.symm, Finset.mem_insert_of_mem huT⟩⟩
        have hu_gain : (G.neighborFinset u ∩ T).card + 1 ≤ (G.neighborFinset u ∩ T').card := by
          have hsub : insert w (G.neighborFinset u ∩ T) ⊆ G.neighborFinset u ∩ T' := by
            intro z hz
            rcases Finset.mem_insert.mp hz with hzw | hz
            · rw [hzw]
              exact Finset.mem_inter.mpr
                ⟨(mem_neighborFinset G u w).mpr huw, Finset.mem_insert_self w T⟩
            · exact Finset.mem_inter.mpr
                ⟨(Finset.mem_inter.mp hz).1, Finset.mem_insert_of_mem (Finset.mem_inter.mp hz).2⟩
          have hw_not_in : w ∉ G.neighborFinset u ∩ T := fun hm => hwT (Finset.mem_inter.mp hm).2
          have hcard := Finset.card_le_card hsub
          rw [Finset.card_insert_of_notMem hw_not_in] at hcard
          exact hcard
        have hT_gain : (∑ v ∈ T, (G.neighborFinset v ∩ T).card) + 1 ≤
            ∑ v ∈ T, (G.neighborFinset v ∩ T').card := by
          have hsplit1 := (Finset.add_sum_erase T (fun v => (G.neighborFinset v ∩ T).card) huT).symm
          have hsplit2 := (Finset.add_sum_erase T (fun v => (G.neighborFinset v ∩ T').card) huT).symm
          have hrest : ∑ v ∈ T.erase u, (G.neighborFinset v ∩ T).card ≤
              ∑ v ∈ T.erase u, (G.neighborFinset v ∩ T').card := by
            refine Finset.sum_le_sum ?_
            intro v _
            exact Finset.card_le_card
              (Finset.inter_subset_inter_left (Finset.subset_insert w T))
          omega
        omega
  rcases hstep S.card (Finset.card_pos.mpr hSne) le_rfl with ⟨T, hTS, hTcard, hTsum⟩
  have hTeq : T = S := Finset.eq_of_subset_of_card_le hTS (by omega)
  rwa [hTeq] at hTsum

/-- Helper: double-counting edges between two finsets `A, B`. -/
lemma sum_inter_card_comm {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    ∑ a ∈ A, (G.neighborFinset a ∩ B).card = ∑ b ∈ B, (G.neighborFinset b ∩ A).card := by
  classical
  have h1 : ∀ a : V, (G.neighborFinset a ∩ B).card = ∑ b ∈ B, if G.Adj a b then 1 else 0 := by
    intro a
    rw [← Finset.card_filter]
    congr 1; ext b
    simp [mem_neighborFinset, and_comm]
  have h2 : ∀ b : V, (G.neighborFinset b ∩ A).card = ∑ a ∈ A, if G.Adj a b then 1 else 0 := by
    intro b
    rw [← Finset.card_filter]
    congr 1; ext a
    simp [mem_neighborFinset, adj_comm, and_comm]
  simp_rw [h1, h2]
  exact Finset.sum_comm

/--
Theorem 4 (`minimal_bad2_girth_g_v3_density_universal`):
**Master Universal Girth-`g` Global Discharging Theorem**:
In any `MinimalBad2EV` graph `G` with `GirthGe G g` (`g ≥ 4`):
  `(5 * g - 3) * (V3 G).card + 6 * (g - 1) * (Defects G).card ≥ 4 * (g - 1) * Fintype.card V`.
-/
theorem minimal_bad2_girth_g_v3_density_universal.{u} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmb : MinimalBad2EV G) {g : ℕ} (hg4 : 4 ≤ g) (hg : GirthGe G g) :
    4 * (g - 1) * Fintype.card V ≤
      (5 * g - 3) * (V3 G).card + 6 * (g - 1) * (Defects G).card := by
  classical
  have hpart : (Defects G).card + (V3 G).card + (V4 G).card = Fintype.card V := by
    have hdisj1 : Disjoint (Defects G) (V3 G) := by
      rw [Finset.disjoint_left]; intro v h1 h2
      simp only [Defects, V3, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2; omega
    have hdisj2 : Disjoint (Defects G ∪ V3 G) (V4 G) := by
      rw [Finset.disjoint_left]; intro v h1 h2
      simp only [Finset.mem_union, Defects, V3, V4, Finset.mem_filter, Finset.mem_univ,
        true_and] at h1 h2; omega
    have hunion : (Defects G ∪ V3 G) ∪ V4 G = Finset.univ := by
      ext v
      simp only [Finset.mem_union, Defects, V3, V4, Finset.mem_filter, Finset.mem_univ,
        true_and, iff_true]
      omega
    rw [← Finset.card_union_of_disjoint hdisj1, ← Finset.card_union_of_disjoint hdisj2,
      hunion, Finset.card_univ]
  by_cases hV4_empty : (V4 G).card = 0
  · have h1 : (Defects G).card + (V3 G).card = Fintype.card V := by omega
    have h2 : 4 * (g - 1) ≤ 5 * g - 3 := by omega
    have h3 : 4 * (g - 1) ≤ 6 * (g - 1) := by omega
    calc 4 * (g - 1) * Fintype.card V
        = 4 * (g - 1) * (V3 G).card + 4 * (g - 1) * (Defects G).card := by rw [← h1]; ring
      _ ≤ (5 * g - 3) * (V3 G).card + 6 * (g - 1) * (Defects G).card :=
          Nat.add_le_add (Nat.mul_le_mul_right _ h2) (Nat.mul_le_mul_right _ h3)
  · have hV4_ne : (V4 G).Nonempty := Finset.card_pos.mp (by omega)
    have hV4_edges : 4 * (V4 G).card ≤
        (∑ v ∈ V3 G, (G.neighborFinset v ∩ V4 G).card) +
        (∑ d ∈ Defects G, (G.neighborFinset d ∩ V4 G).card) := by
      rw [sum_inter_card_comm G (V3 G) (V4 G), sum_inter_card_comm G (Defects G) (V4 G)]
      rw [← Finset.sum_add_distrib]
      have hle : ∑ w ∈ V4 G, 4 ≤
          ∑ w ∈ V4 G, ((G.neighborFinset w ∩ V3 G).card + (G.neighborFinset w ∩ Defects G).card) := by
        refine Finset.sum_le_sum ?_
        intro w hw
        have hw4 : 4 ≤ G.degree w := (Finset.mem_filter.mp hw).2
        have hdisj : Disjoint (G.neighborFinset w ∩ V3 G) (G.neighborFinset w ∩ Defects G) := by
          rw [Finset.disjoint_left]; intro z h1 h2
          have h1' := (Finset.mem_filter.mp (Finset.mem_inter.mp h1).2).2
          have h2' := (Finset.mem_filter.mp (Finset.mem_inter.mp h2).2).2
          omega
        rw [← Finset.card_union_of_disjoint hdisj]
        have hsub : G.neighborFinset w ⊆
            (G.neighborFinset w ∩ V3 G) ∪ (G.neighborFinset w ∩ Defects G) := by
          intro z hz
          have hwz : G.Adj w z := (mem_neighborFinset G w z).mp hz
          have hz_not4 : ¬ 4 ≤ G.degree z := fun hz4 =>
            minimal_bad2_vge4_independent G hmb hw4 hz4 hwz
          by_cases hz3 : G.degree z = 3
          · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hz, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz3⟩⟩)
          · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hz, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩)
        have hcard := Finset.card_le_card hsub
        rw [card_neighborFinset_eq_degree] at hcard
        omega
      simpa [Finset.sum_const, mul_comm] using hle
    let H3 := G.induce (V3 G : Set V)
    let compOf (v : {x : V // x ∈ V3 G}) : H3.ConnectedComponent := H3.connectedComponentMk v
    let compSet (K : H3.ConnectedComponent) : Finset V :=
      (Finset.univ.filter (fun u : {x : V // x ∈ V3 G} => compOf u = K)).map
        ⟨Subtype.val, Subtype.val_injective⟩
    have hcomp_bound : ∀ K : H3.ConnectedComponent,
        (g - 1) * (∑ v ∈ compSet K, (G.neighborFinset v ∩ V4 G).card) ≤
        (g + 1) * (compSet K).card +
        (g - 1) * (∑ v ∈ compSet K, (G.neighborFinset v ∩ Defects G).card) := by
      intro K
      let S := compSet K
      have hS3 : S ⊆ V3 G := by
        intro v hv
        rcases Finset.mem_map.mp hv with ⟨u, _, rfl⟩
        exact u.2
      have hSne : S.Nonempty := by
        rcases K.exists_rep with ⟨u, hu⟩
        exact ⟨u.1, Finset.mem_map.mpr ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩, rfl⟩⟩
      have hS_no_V3_out : ∀ x ∈ S, ∀ y ∈ V3 G, G.Adj x y → y ∈ S := by
        intro x hx y hy hxy
        rcases Finset.mem_map.mp hx with ⟨ux, hux, rfl⟩
        have hux_eq : compOf ux = K := (Finset.mem_filter.mp hux).2
        refine Finset.mem_map.mpr ⟨⟨y, hy⟩, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, compOf]
        have hreach : H3.Reachable ux ⟨y, hy⟩ := Adj.reachable hxy
        exact (ConnectedComponent.eq.mpr hreach).symm.trans hux_eq
      have hS_conn : (G.induce (S : Set V)).Connected := by
        have : Nonempty ↑(S : Set V) := let ⟨u0, hu0⟩ := hSne; ⟨⟨u0, hu0⟩⟩
        refine ⟨?_⟩
        intro ⟨x, hx⟩ ⟨y, hy⟩
        rcases Finset.mem_map.mp hx with ⟨ux, hux, rfl⟩
        rcases Finset.mem_map.mp hy with ⟨uy, huy, rfl⟩
        have hreach : H3.Reachable ux uy :=
          ConnectedComponent.eq.mp ((Finset.mem_filter.mp hux).2.trans (Finset.mem_filter.mp huy).2.symm)
        rcases hreach with ⟨w⟩
        have hlift : ∀ {a b : {z : V // z ∈ V3 G}} (p : H3.Walk a b) (ha : compOf a = K),
            (G.induce (S : Set V)).Reachable
              ⟨a.1, Finset.mem_map.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩, rfl⟩⟩
              ⟨b.1, Finset.mem_map.mpr ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
                (ConnectedComponent.eq.mpr p.reachable).symm.trans ha⟩, rfl⟩⟩ := by
          intro a b p
          induction p with
          | nil => intro _; exact Reachable.refl _
          | @cons a₁ a₂ a₃ h₁₂ r ihr =>
            intro ha1
            have ha2 : compOf a₂ = K := (ConnectedComponent.eq.mpr h₁₂.reachable).symm.trans ha1
            have hadjS : (G.induce (S : Set V)).Adj
                ⟨a₁.1, Finset.mem_map.mpr ⟨a₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha1⟩, rfl⟩⟩
                ⟨a₂.1, Finset.mem_map.mpr ⟨a₂, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha2⟩, rfl⟩⟩ := h₁₂
            exact Reachable.trans (Adj.reachable hadjS) (ihr ha2)
        have hux_eq : compOf ux = K := (Finset.mem_filter.mp hux).2
        have hres := hlift w hux_eq
        exact hres
      have hbal : (∑ v ∈ S, (G.neighborFinset v ∩ S).card) +
          (∑ v ∈ S, (G.neighborFinset v ∩ V4 G).card) +
          (∑ v ∈ S, (G.neighborFinset v ∩ Defects G).card) = 3 * S.card := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        have h3 : ∑ v ∈ S, 3 = 3 * S.card := by simp [Finset.sum_const, mul_comm]
        rw [← h3]
        refine Finset.sum_congr rfl ?_
        intro v hv
        have hv3 : G.degree v = 3 := (Finset.mem_filter.mp (hS3 hv)).2
        have hd1 : Disjoint (G.neighborFinset v ∩ S) (G.neighborFinset v ∩ V4 G) := by
          rw [Finset.disjoint_left]; intro z h1 h2
          have hz3 : G.degree z = 3 := (Finset.mem_filter.mp (hS3 (Finset.mem_inter.mp h1).2)).2
          have hz4 : 4 ≤ G.degree z := (Finset.mem_filter.mp (Finset.mem_inter.mp h2).2).2
          omega
        have hd2 : Disjoint ((G.neighborFinset v ∩ S) ∪ (G.neighborFinset v ∩ V4 G))
            (G.neighborFinset v ∩ Defects G) := by
          rw [Finset.disjoint_left]; intro z h1 h2
          have hzD : G.degree z < 3 := (Finset.mem_filter.mp (Finset.mem_inter.mp h2).2).2
          rcases Finset.mem_union.mp h1 with h1a | h1b
          · have hz3 : G.degree z = 3 := (Finset.mem_filter.mp (hS3 (Finset.mem_inter.mp h1a).2)).2
            omega
          · have hz4 : 4 ≤ G.degree z := (Finset.mem_filter.mp (Finset.mem_inter.mp h1b).2).2
            omega
        rw [← Finset.card_union_of_disjoint hd1, ← Finset.card_union_of_disjoint hd2]
        have heq_set : ((G.neighborFinset v ∩ S) ∪ (G.neighborFinset v ∩ V4 G)) ∪
            (G.neighborFinset v ∩ Defects G) = G.neighborFinset v := by
          ext z
          simp only [Finset.mem_union, Finset.mem_inter]
          constructor
          · rintro ((⟨hz, _⟩ | ⟨hz, _⟩) | ⟨hz, _⟩) <;> exact hz
          · intro hz
            have hvz := (mem_neighborFinset G v z).mp hz
            by_cases hz4 : 4 ≤ G.degree z
            · exact Or.inl (Or.inr ⟨hz, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz4⟩⟩)
            · by_cases hz3 : G.degree z = 3
              · exact Or.inl (Or.inl ⟨hz, hS_no_V3_out v hv z
                  (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz3⟩) hvz⟩)
              · exact Or.inr ⟨hz, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩
        rw [heq_set, card_neighborFinset_eq_degree, hv3]
      have hconn_deg := connected_sum_deg_ge G S hSne hS_conn
      have hSpos : 1 ≤ S.card := Finset.card_pos.mpr hSne
      have he4_le : (∑ v ∈ S, (G.neighborFinset v ∩ V4 G).card) +
          (∑ v ∈ S, (G.neighborFinset v ∩ Defects G).card) ≤ S.card + 2 := by
        omega
      by_cases heD0 : (∑ v ∈ S, (G.neighborFinset v ∩ Defects G).card) = 0
      · have hno_nonV4 : ∀ x ∈ S, ∀ y : V, G.Adj x y → y ∉ S → 4 ≤ G.degree y := by
          intro x hx y hxy hyS
          by_contra hlt4
          by_cases hy3 : G.degree y = 3
          · exact hyS (hS_no_V3_out x hx y (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy3⟩) hxy)
          · have hpos : 0 < (G.neighborFinset x ∩ Defects G).card :=
              Finset.card_pos.mpr ⟨y, Finset.mem_inter.mpr
                ⟨(mem_neighborFinset G x y).mpr hxy,
                 Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩⟩
            have hle_sum : (G.neighborFinset x ∩ Defects G).card ≤
                ∑ v ∈ S, (G.neighborFinset v ∩ Defects G).card :=
              Finset.single_le_sum (f := fun v => (G.neighborFinset v ∩ Defects G).card) (fun _ _ => Nat.zero_le _) hx
            omega
        have hSge : g - 1 ≤ S.card :=
          minimal_bad2_v3_component_size_ge_girth_sub_one G hmb hg hV4_ne S hSne hS3
            hS_conn hno_nonV4
        have he4_only : ∑ v ∈ S, (G.neighborFinset v ∩ V4 G).card ≤ S.card + 2 := by omega
        calc (g - 1) * (∑ v ∈ S, (G.neighborFinset v ∩ V4 G).card)
            ≤ (g - 1) * (S.card + 2) := Nat.mul_le_mul_left (g - 1) he4_only
          _ = (g - 1) * S.card + 2 * (g - 1) := by ring
          _ ≤ (g - 1) * S.card + 2 * S.card := by omega
          _ = (g + 1) * S.card := by
              have : (g - 1) + 2 = g + 1 := by omega
              calc (g - 1) * S.card + 2 * S.card = ((g - 1) + 2) * S.card := by ring
                _ = (g + 1) * S.card := by rw [this]
          _ ≤ (g + 1) * S.card +
              (g - 1) * (∑ v ∈ S, (G.neighborFinset v ∩ Defects G).card) := Nat.le_add_right _ _
      · have heD1 : 1 ≤ ∑ v ∈ S, (G.neighborFinset v ∩ Defects G).card := by omega
        have he4_le' : ∑ v ∈ S, (G.neighborFinset v ∩ V4 G).card ≤ S.card + 1 := by omega
        calc (g - 1) * (∑ v ∈ S, (G.neighborFinset v ∩ V4 G).card)
            ≤ (g - 1) * (S.card + 1) := Nat.mul_le_mul_left (g - 1) he4_le'
          _ = (g - 1) * S.card + (g - 1) * 1 := by ring
          _ ≤ (g + 1) * S.card + (g - 1) * (∑ v ∈ S, (G.neighborFinset v ∩ Defects G).card) := by
              have h1 : (g - 1) * S.card ≤ (g + 1) * S.card :=
                Nat.mul_le_mul_right S.card (by omega)
              have h2 : (g - 1) * 1 ≤ (g - 1) * (∑ v ∈ S, (G.neighborFinset v ∩ Defects G).card) :=
                Nat.mul_le_mul_left (g - 1) heD1
              omega
    have hsum_V3 : ∀ f : V → ℕ,
        ∑ K : H3.ConnectedComponent, ∑ v ∈ compSet K, f v = ∑ v ∈ V3 G, f v := by
      intro f
      have hdisj_K : Set.PairwiseDisjoint (Finset.univ : Finset H3.ConnectedComponent) compSet := by
        intro K₁ _ K₂ _ hne
        change Disjoint (compSet K₁) (compSet K₂)
        rw [Finset.disjoint_left]
        intro v hv1 hv2
        rcases Finset.mem_map.mp hv1 with ⟨u1, hu1, rfl⟩
        rcases Finset.mem_map.mp hv2 with ⟨u2, hu2, heq⟩
        have hu_eq : u1 = u2 := Subtype.ext heq.symm
        subst hu_eq
        exact hne ((Finset.mem_filter.mp hu1).2.symm.trans (Finset.mem_filter.mp hu2).2)
      rw [← Finset.sum_biUnion hdisj_K]
      congr 1; ext v
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, compSet, Finset.mem_map,
        Finset.mem_filter, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨_, u, _, rfl⟩; exact u.2
      · intro hv; exact ⟨compOf ⟨v, hv⟩, ⟨v, hv⟩, rfl, rfl⟩
    have hcard_V3 : ∑ K : H3.ConnectedComponent, (compSet K).card = (V3 G).card := by
      simpa using hsum_V3 (fun _ => 1)
    have htot := Finset.sum_le_sum (s := Finset.univ) (fun K _ => hcomp_bound K)
    simp only [← Finset.mul_sum, Finset.sum_add_distrib, hsum_V3, hcard_V3] at htot
    have hD_edges : (∑ v ∈ V3 G, (G.neighborFinset v ∩ Defects G).card) +
        (∑ d ∈ Defects G, (G.neighborFinset d ∩ V4 G).card) ≤ 2 * (Defects G).card := by
      rw [sum_inter_card_comm G (V3 G) (Defects G), ← Finset.sum_add_distrib]
      have hle : ∑ d ∈ Defects G,
            ((G.neighborFinset d ∩ V3 G).card + (G.neighborFinset d ∩ V4 G).card) ≤
          ∑ d ∈ Defects G, 2 := by
        refine Finset.sum_le_sum ?_
        intro d hd
        have hd2 : G.degree d < 3 := (Finset.mem_filter.mp hd).2
        have hdisj : Disjoint (G.neighborFinset d ∩ V3 G) (G.neighborFinset d ∩ V4 G) := by
          rw [Finset.disjoint_left]; intro z h1 h2
          have h1' := (Finset.mem_filter.mp (Finset.mem_inter.mp h1).2).2
          have h2' := (Finset.mem_filter.mp (Finset.mem_inter.mp h2).2).2
          omega
        rw [← Finset.card_union_of_disjoint hdisj]
        have hsub : (G.neighborFinset d ∩ V3 G) ∪ (G.neighborFinset d ∩ V4 G) ⊆
            G.neighborFinset d := Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left
        have hcard := Finset.card_le_card hsub
        rw [card_neighborFinset_eq_degree] at hcard
        omega
      simpa [Finset.sum_const, mul_comm] using hle
    have h4g : 4 * (g - 1) * (V4 G).card ≤
        (g + 1) * (V3 G).card + 2 * (g - 1) * (Defects G).card := by
      have h1 : (g - 1) * (4 * (V4 G).card) ≤
          (g - 1) * ((∑ v ∈ V3 G, (G.neighborFinset v ∩ V4 G).card) +
                     (∑ d ∈ Defects G, (G.neighborFinset d ∩ V4 G).card)) :=
        Nat.mul_le_mul_left (g - 1) hV4_edges
      have h2 : (g - 1) * ((∑ v ∈ V3 G, (G.neighborFinset v ∩ Defects G).card) +
                           (∑ d ∈ Defects G, (G.neighborFinset d ∩ V4 G).card)) ≤
          (g - 1) * (2 * (Defects G).card) :=
        Nat.mul_le_mul_left (g - 1) hD_edges
      linarith
    have hmul_part : 4 * (g - 1) * Fintype.card V =
        4 * (g - 1) * (Defects G).card + 4 * (g - 1) * (V3 G).card + 4 * (g - 1) * (V4 G).card := by
      rw [← hpart]; ring
    have hcoeff : 4 * (g - 1) + (g + 1) = 5 * g - 3 := by omega
    have h6 : 4 * (g - 1) * (Defects G).card + 2 * (g - 1) * (Defects G).card =
        6 * (g - 1) * (Defects G).card := by ring
    have h5 : 4 * (g - 1) * (V3 G).card + (g + 1) * (V3 G).card =
        (5 * g - 3) * (V3 G).card := by
      calc 4 * (g - 1) * (V3 G).card + (g + 1) * (V3 G).card
          = (4 * (g - 1) + (g + 1)) * (V3 G).card := by ring
        _ = (5 * g - 3) * (V3 G).card := by rw [hcoeff]
    linarith

/--
Theorem 5 (`minimal_bad2_girth7_v3_density_3_4`):
Explicit girth-`≥ 7` corollary: `3 * |V(G)| ≤ 4 * |V₃(G)| + 9` (`|V₃| ≥ 3/4 n - 9/4`),
strictly tightening Wave 7 Agent #2's `20/27` (`0.7407`) bound to `3/4` (`0.7500`).
-/
theorem minimal_bad2_girth7_v3_density_3_4.{u} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmb : MinimalBad2EV G) (hg : GirthGe G 7) :
    3 * Fintype.card V ≤ 4 * (V3 G).card + 9 := by
  have h := minimal_bad2_girth_g_v3_density_universal G hmb (g := 7) (by decide) hg
  have hd := hmb.defects_le_two
  omega

/--
Theorem 6 (`minimal_bad2_girth8_auto_girth9_v3_density_16_21`):
Because `PowerFree G` forbids `C₈`, girth `≥ 8` automatically implies girth `≥ 9`, giving
`16 * |V(G)| ≤ 21 * |V₃(G)| + 48` (`|V₃| ≥ 16/21 n - 16/7 ≈ 0.7619 n`).
-/
theorem minimal_bad2_girth8_auto_girth9_v3_density_16_21.{u} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmb : MinimalBad2EV G) (hg8 : GirthGe G 8) :
    16 * Fintype.card V ≤ 21 * (V3 G).card + 48 := by
  have hg9 : GirthGe G 9 := by
    intro v p hp
    have h8 := hg8 v p hp
    by_contra hlt
    have heq8 : p.length = 8 := by omega
    exact hmb.power_free ⟨v, p, hp, ⟨3, by decide, by omega⟩⟩
  have h := minimal_bad2_girth_g_v3_density_universal G hmb (g := 9) (by decide) hg9
  have hd := hmb.defects_le_two
  omega

/--
Theorem 7 (`minimal_bad2_girth_g_v3_internal_degree_bound`):
Universal internal degree lower bound on `G[V₃]`: for every girth `g ≥ 4`,
  `2 * (g - 2) * |V₃(G)| ≤ (g - 1) * (∑ v ∈ V₃(G), deg_{V₃}(v)) + 4 * (g - 1) * |D|`,
forcing average internal degree `≥ 2 - 2/(g - 1) - O(1/n)` inside `G[V₃]`.
-/
theorem minimal_bad2_girth_g_v3_internal_degree_bound.{u} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmb : MinimalBad2EV G) {g : ℕ} (hg4 : 4 ≤ g) (hg : GirthGe G g) :
    2 * (g - 2) * (V3 G).card ≤
      (g - 1) * (∑ v ∈ V3 G, (G.neighborFinset v ∩ V3 G).card) +
      4 * (g - 1) * (Defects G).card := by
  classical
  have hbal_V3 : (∑ v ∈ V3 G, (G.neighborFinset v ∩ V3 G).card) +
      (∑ v ∈ V3 G, (G.neighborFinset v ∩ V4 G).card) +
      (∑ v ∈ V3 G, (G.neighborFinset v ∩ Defects G).card) = 3 * (V3 G).card := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    have h3 : ∑ v ∈ V3 G, 3 = 3 * (V3 G).card := by simp [Finset.sum_const, mul_comm]
    rw [← h3]
    refine Finset.sum_congr rfl ?_
    intro v hv
    have hv3 : G.degree v = 3 := (Finset.mem_filter.mp hv).2
    have hd1 : Disjoint (G.neighborFinset v ∩ V3 G) (G.neighborFinset v ∩ V4 G) := by
      rw [Finset.disjoint_left]; intro z h1 h2
      have h1' := (Finset.mem_filter.mp (Finset.mem_inter.mp h1).2).2
      have h2' := (Finset.mem_filter.mp (Finset.mem_inter.mp h2).2).2
      omega
    have hd2 : Disjoint ((G.neighborFinset v ∩ V3 G) ∪ (G.neighborFinset v ∩ V4 G))
        (G.neighborFinset v ∩ Defects G) := by
      rw [Finset.disjoint_left]; intro z h1 h2
      have h2' := (Finset.mem_filter.mp (Finset.mem_inter.mp h2).2).2
      rcases Finset.mem_union.mp h1 with h1a | h1b
      · have h1' := (Finset.mem_filter.mp (Finset.mem_inter.mp h1a).2).2; omega
      · have h1' := (Finset.mem_filter.mp (Finset.mem_inter.mp h1b).2).2; omega
    rw [← Finset.card_union_of_disjoint hd1, ← Finset.card_union_of_disjoint hd2]
    have heq_set : ((G.neighborFinset v ∩ V3 G) ∪ (G.neighborFinset v ∩ V4 G)) ∪
        (G.neighborFinset v ∩ Defects G) = G.neighborFinset v := by
      ext z
      simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · rintro ((⟨hz, _⟩ | ⟨hz, _⟩) | ⟨hz, _⟩) <;> exact hz
      · intro hz
        by_cases hz4 : 4 ≤ G.degree z
        · exact Or.inl (Or.inr ⟨hz, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz4⟩⟩)
        · by_cases hz3 : G.degree z = 3
          · exact Or.inl (Or.inl ⟨hz, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz3⟩⟩)
          · exact Or.inr ⟨hz, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩
    rw [heq_set, card_neighborFinset_eq_degree, hv3]
  have heD_le : ∑ v ∈ V3 G, (G.neighborFinset v ∩ Defects G).card ≤ 2 * (Defects G).card := by
    rw [sum_inter_card_comm G (V3 G) (Defects G)]
    have hle : ∑ d ∈ Defects G, (G.neighborFinset d ∩ V3 G).card ≤ ∑ d ∈ Defects G, 2 := by
      refine Finset.sum_le_sum ?_
      intro d hd
      have hd2 : G.degree d < 3 := (Finset.mem_filter.mp hd).2
      have hcard := Finset.card_le_card (Finset.inter_subset_left (s₁ := G.neighborFinset d) (s₂ := V3 G))
      rw [card_neighborFinset_eq_degree] at hcard
      omega
    simpa [Finset.sum_const, mul_comm] using hle
  by_cases hV4_empty : (V4 G).card = 0
  · have hV4_eq : V4 G = ∅ := Finset.card_eq_zero.mp hV4_empty
    have he4_zero : ∑ v ∈ V3 G, (G.neighborFinset v ∩ V4 G).card = 0 := by simp [hV4_eq]
    have h1 : 2 * (V3 G).card ≤ (∑ v ∈ V3 G, (G.neighborFinset v ∩ V3 G).card) + 2 * (Defects G).card := by
      omega
    have h2 : 2 * (g - 2) * (V3 G).card ≤ (g - 1) * (2 * (V3 G).card) := by
      have : 2 * (g - 2) ≤ 2 * (g - 1) := by omega
      calc 2 * (g - 2) * (V3 G).card ≤ (2 * (g - 1)) * (V3 G).card :=
            Nat.mul_le_mul_right _ this
        _ = (g - 1) * (2 * (V3 G).card) := by ring
    have h3 : (g - 1) * (2 * (V3 G).card) ≤
        (g - 1) * ((∑ v ∈ V3 G, (G.neighborFinset v ∩ V3 G).card) + 2 * (Defects G).card) :=
      Nat.mul_le_mul_left (g - 1) h1
    rw [Nat.mul_add] at h3
    have h4 : (g - 1) * (2 * (Defects G).card) ≤ 4 * (g - 1) * (Defects G).card := by
      have : 2 * (g - 1) ≤ 4 * (g - 1) := by omega
      calc (g - 1) * (2 * (Defects G).card) = (2 * (g - 1)) * (Defects G).card := by ring
        _ ≤ (4 * (g - 1)) * (Defects G).card := Nat.mul_le_mul_right _ this
        _ = 4 * (g - 1) * (Defects G).card := by ring
    linarith
  · have hV4_ne : (V4 G).Nonempty := Finset.card_pos.mp (by omega)
    let H3 := G.induce (V3 G : Set V)
    let compOf (v : {x : V // x ∈ V3 G}) : H3.ConnectedComponent := H3.connectedComponentMk v
    let compSet (K : H3.ConnectedComponent) : Finset V :=
      (Finset.univ.filter (fun u : {x : V // x ∈ V3 G} => compOf u = K)).map
        ⟨Subtype.val, Subtype.val_injective⟩
    have hcomp_deg : ∀ K : H3.ConnectedComponent,
        2 * (g - 2) * (compSet K).card ≤
        (g - 1) * (∑ v ∈ compSet K, (G.neighborFinset v ∩ V3 G).card) +
        2 * (g - 1) * (∑ v ∈ compSet K, (G.neighborFinset v ∩ Defects G).card) := by
      intro K
      let S := compSet K
      have hS3 : S ⊆ V3 G := by
        intro v hv; rcases Finset.mem_map.mp hv with ⟨u, _, rfl⟩; exact u.2
      have hSne : S.Nonempty := by
        rcases K.exists_rep with ⟨u, hu⟩
        exact ⟨u.1, Finset.mem_map.mpr ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩, rfl⟩⟩
      have hS_no_V3_out : ∀ x ∈ S, ∀ y ∈ V3 G, G.Adj x y → y ∈ S := by
        intro x hx y hy hxy
        rcases Finset.mem_map.mp hx with ⟨ux, hux, rfl⟩
        refine Finset.mem_map.mpr ⟨⟨y, hy⟩, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, compOf]
        have hreach : H3.Reachable ux ⟨y, hy⟩ := Adj.reachable hxy
        exact (ConnectedComponent.eq.mpr hreach).symm.trans (Finset.mem_filter.mp hux).2
      have hS_conn : (G.induce (S : Set V)).Connected := by
        have : Nonempty ↑(S : Set V) := let ⟨u0, hu0⟩ := hSne; ⟨⟨u0, hu0⟩⟩
        refine ⟨?_⟩
        intro ⟨x, hx⟩ ⟨y, hy⟩
        rcases Finset.mem_map.mp hx with ⟨ux, hux, rfl⟩
        rcases Finset.mem_map.mp hy with ⟨uy, huy, rfl⟩
        rcases ConnectedComponent.eq.mp
          ((Finset.mem_filter.mp hux).2.trans (Finset.mem_filter.mp huy).2.symm) with ⟨w⟩
        have hlift : ∀ {a b : {z : V // z ∈ V3 G}} (p : H3.Walk a b) (ha : compOf a = K),
            (G.induce (S : Set V)).Reachable
              ⟨a.1, Finset.mem_map.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩, rfl⟩⟩
              ⟨b.1, Finset.mem_map.mpr ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
                (ConnectedComponent.eq.mpr p.reachable).symm.trans ha⟩, rfl⟩⟩ := by
          intro a b p
          induction p with
          | nil => intro _; exact Reachable.refl _
          | @cons a₁ a₂ a₃ h₁₂ r ihr =>
            intro ha1
            have ha2 : compOf a₂ = K := (ConnectedComponent.eq.mpr h₁₂.reachable).symm.trans ha1
            have hadjS : (G.induce (S : Set V)).Adj
                ⟨a₁.1, Finset.mem_map.mpr ⟨a₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha1⟩, rfl⟩⟩
                ⟨a₂.1, Finset.mem_map.mpr ⟨a₂, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha2⟩, rfl⟩⟩ := h₁₂
            exact Reachable.trans (Adj.reachable hadjS) (ihr ha2)
        exact hlift w (Finset.mem_filter.mp hux).2
      have hsub_deg : ∑ v ∈ S, (G.neighborFinset v ∩ S).card ≤
          ∑ v ∈ S, (G.neighborFinset v ∩ V3 G).card :=
        Finset.sum_le_sum (fun v _ => Finset.card_le_card (Finset.inter_subset_inter_left hS3))
      have hconn_deg := connected_sum_deg_ge G S hSne hS_conn
      have hSpos : 1 ≤ S.card := Finset.card_pos.mpr hSne
      by_cases heD0 : (∑ v ∈ S, (G.neighborFinset v ∩ Defects G).card) = 0
      · have hno_nonV4 : ∀ x ∈ S, ∀ y : V, G.Adj x y → y ∉ S → 4 ≤ G.degree y := by
          intro x hx y hxy hyS
          by_contra hlt4
          by_cases hy3 : G.degree y = 3
          · exact hyS (hS_no_V3_out x hx y (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy3⟩) hxy)
          · have hpos : 0 < (G.neighborFinset x ∩ Defects G).card :=
              Finset.card_pos.mpr ⟨y, Finset.mem_inter.mpr
                ⟨(mem_neighborFinset G x y).mpr hxy,
                 Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩⟩
            have hle_sum : (G.neighborFinset x ∩ Defects G).card ≤
                ∑ v ∈ S, (G.neighborFinset v ∩ Defects G).card :=
              Finset.single_le_sum (f := fun v => (G.neighborFinset v ∩ Defects G).card) (fun _ _ => Nat.zero_le _) hx
            omega
        have hSge : g - 1 ≤ S.card :=
          minimal_bad2_v3_component_size_ge_girth_sub_one G hmb hg hV4_ne S hSne hS3
            hS_conn hno_nonV4
        have hmul : (g - 1) * (2 * (S.card - 1)) ≤
            (g - 1) * (∑ v ∈ S, (G.neighborFinset v ∩ V3 G).card) :=
          Nat.mul_le_mul_left (g - 1) (le_trans hconn_deg hsub_deg)
        have hlhs : 2 * (g - 2) * S.card ≤ (g - 1) * (2 * (S.card - 1)) := by
          zify [hSpos, (by omega : 1 ≤ g), (by omega : 2 ≤ g)]
          have hSgeZ : (g : ℤ) - 1 ≤ (S.card : ℤ) := by omega
          nlinarith
        exact le_trans hlhs (le_trans hmul (Nat.le_add_right _ _))
      · have heD1 : 1 ≤ ∑ v ∈ S, (G.neighborFinset v ∩ Defects G).card := by omega
        have hmul : (g - 1) * (2 * (S.card - 1)) ≤
            (g - 1) * (∑ v ∈ S, (G.neighborFinset v ∩ V3 G).card) :=
          Nat.mul_le_mul_left (g - 1) (le_trans hconn_deg hsub_deg)
        have hlhs : 2 * (g - 2) * S.card ≤
            (g - 1) * (2 * (S.card - 1)) + 2 * (g - 1) * 1 := by
          zify [hSpos, (by omega : 1 ≤ g), (by omega : 2 ≤ g)]
          nlinarith
        have hmulD : 2 * (g - 1) * 1 ≤
            2 * (g - 1) * (∑ v ∈ S, (G.neighborFinset v ∩ Defects G).card) :=
          Nat.mul_le_mul_left (2 * (g - 1)) heD1
        dsimp only [S] at hmul hlhs hmulD
        omega
    have hsum_V3 : ∀ f : V → ℕ,
        ∑ K : H3.ConnectedComponent, ∑ v ∈ compSet K, f v = ∑ v ∈ V3 G, f v := by
      intro f
      have hdisj_K : Set.PairwiseDisjoint (Finset.univ : Finset H3.ConnectedComponent) compSet := by
        intro K₁ _ K₂ _ hne
        change Disjoint (compSet K₁) (compSet K₂)
        rw [Finset.disjoint_left]
        intro v hv1 hv2
        rcases Finset.mem_map.mp hv1 with ⟨u1, hu1, rfl⟩
        rcases Finset.mem_map.mp hv2 with ⟨u2, hu2, heq⟩
        have hu_eq : u1 = u2 := Subtype.ext heq.symm
        subst hu_eq
        exact hne ((Finset.mem_filter.mp hu1).2.symm.trans (Finset.mem_filter.mp hu2).2)
      rw [← Finset.sum_biUnion hdisj_K]
      congr 1; ext v
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, compSet, Finset.mem_map,
        Finset.mem_filter, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨_, u, _, rfl⟩; exact u.2
      · intro hv; exact ⟨compOf ⟨v, hv⟩, ⟨v, hv⟩, rfl, rfl⟩
    have hcard_V3 : ∑ K : H3.ConnectedComponent, (compSet K).card = (V3 G).card := by
      simpa using hsum_V3 (fun _ => 1)
    have htot := Finset.sum_le_sum (s := Finset.univ) (fun K _ => hcomp_deg K)
    simp only [← Finset.mul_sum, Finset.sum_add_distrib, hsum_V3, hcard_V3] at htot
    have hDmul : 2 * (g - 1) * (∑ v ∈ V3 G, (G.neighborFinset v ∩ Defects G).card) ≤
        4 * (g - 1) * (Defects G).card := by
      calc 2 * (g - 1) * (∑ v ∈ V3 G, (G.neighborFinset v ∩ Defects G).card)
          ≤ 2 * (g - 1) * (2 * (Defects G).card) := Nat.mul_le_mul_left _ heD_le
        _ = 4 * (g - 1) * (Defects G).card := by ring
    omega

end E64Wave8Agent3P2
