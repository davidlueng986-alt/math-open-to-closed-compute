import Core
import Leaves
import PairedShadow
import ClosedDefectCore

/-!
Erdos 64 (Wave 3, Agent #1): Universal Induced-P3 and Defect-Neighborhood Fermat Cycle Forcing.
Proves (unconditionally, all finite orders, standard axioms only):
1. `cubic_p3_fermat_cycle`: In every cubic `MinimalBad(G)`, every induced P3 `a - v - b`
   (`¬ G.Adj a b`) lies on a simple `(2^k + 1)`-cycle (`k ≥ 2`) containing both `s(a,v)` and `s(v,b)`.
   (Complements Wave 2's `(2^k + 2)`-cycle theorem.)
2. `defect_p3_fermat_cycle`: In every `S` or `H` `MinimalBad(G)` with `deg(w) = 2` and
   non-adjacent neighbors `b₁, b₂`, `b₁ - w - b₂` lies on a simple `(2^k + 1)`-cycle (`k ≥ 2`).
3. `defect_neighbor_p3_fermat_cycle`: In every `S` or `H` `MinimalBad(G)` with `deg(w) = 2`,
   `b₁ ∈ N(w)`, and non-adjacent neighbors `a, b ∈ N(b₁) \ {w}`, `a - b₁ - b` lies on a
   simple `(2^k + 1)`-cycle (`k ≥ 2`) avoiding `w`.
-/

namespace E64Wave3PathCycle
open SimpleGraph Erdos64Closure E64Core E64Leaves Erdos64Paired E64DefectCore
universe u

variable {V : Type u}

/-- Transfer a walk in `(G.induce S) ⊔ edge a b` that avoids `s(a, b)` into `G`. -/
private def liftAvoidEdge {G : SimpleGraph V} {S : Set V}
    {a b u w : S}
    (p : ((G.induce S) ⊔ SimpleGraph.edge a b).Walk u w)
    (havoid : s(a, b) ∉ p.edges) : G.Walk u.1 w.1 :=
  match p with
  | .nil => .nil
  | .cons (u := x) (v := y) hxy q =>
    have hne_edge : s(x, y) ≠ s(a, b) := fun heq =>
      havoid (by rw [Walk.edges_cons, List.mem_cons]; exact Or.inl heq.symm)
    have hG : G.Adj x.1 y.1 := by
      rcases hxy with h | h
      · exact h
      · exfalso
        have hsym : s(x, y) = s(a, b) := by
          rcases h.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rfl
          · exact Sym2.eq_swap
        exact hne_edge hsym
    .cons hG (liftAvoidEdge q (fun hm => havoid (by rw [Walk.edges_cons, List.mem_cons]; exact Or.inr hm)))

private theorem length_liftAvoidEdge {G : SimpleGraph V} {S : Set V}
    {a b u w : S}
    (p : ((G.induce S) ⊔ SimpleGraph.edge a b).Walk u w)
    (havoid : s(a, b) ∉ p.edges) :
    (liftAvoidEdge p havoid).length = p.length := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp [liftAvoidEdge, ih]

private theorem support_liftAvoidEdge {G : SimpleGraph V} {S : Set V}
    {a b u w : S}
    (p : ((G.induce S) ⊔ SimpleGraph.edge a b).Walk u w)
    (havoid : s(a, b) ∉ p.edges) :
    (liftAvoidEdge p havoid).support = p.support.map Subtype.val := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp [liftAvoidEdge, ih]

/-- Extract a simple `a`-`b` path of length `L - 1` avoiding `s(a,b)` from a cycle of length `L ≥ 4`
    that uses the edge `s(a, b)`. -/
private theorem extract_path_of_cycle_edge {W : Type u} [DecidableEq W]
    {H : SimpleGraph W} {a b v₀ : W} (hab : a ≠ b)
    (c : H.Walk v₀ v₀) (hc : c.IsCycle) (hmem : s(a, b) ∈ c.edges) :
    ∃ p : H.Walk a b, p.IsPath ∧ p.length + 1 = c.length ∧ s(a, b) ∉ p.edges := by
  classical
  have ha : a ∈ c.support := Walk.fst_mem_support_of_mem_edges c hmem
  let c₁ := c.rotate a ha
  have hc₁ : c₁.IsCycle := SimpleGraph.Walk.IsCycle.rotate ha hc
  have hlen₁ : c₁.length = c.length := Walk.length_rotate c a ha
  have hmem₁ : s(a, b) ∈ c₁.edges := by
    have hspec := Walk.take_spec c ha
    rw [← hspec, Walk.edges_append, List.mem_append] at hmem
    change s(a, b) ∈ ((c.dropUntil a ha).append (c.takeUntil a ha)).edges
    rw [Walk.edges_append, List.mem_append]
    exact hmem.symm
  cases hce : c₁ with
  | nil => exact False.elim (hc₁.ne_nil hce)
  | @cons _ u _ hau rest =>
    by_cases hub : u = b
    · subst hub
      have hrest_path : rest.IsPath := by
        apply Walk.IsPath.mk'
        have hn := hc₁.support_nodup
        rw [hce, Walk.support_cons, List.tail_cons] at hn; exact hn
      have hrest_len : rest.length + 1 = c.length := by
        have := congrArg Walk.length hce; simp only [Walk.length_cons] at this; omega
      have hnot_mem : s(a, b) ∉ rest.edges := by
        have hnd := hc₁.edges_nodup; rw [hce, Walk.edges_cons, List.nodup_cons] at hnd; exact hnd.1
      refine ⟨rest.reverse, hrest_path.reverse, ?_, ?_⟩
      · rw [Walk.length_reverse]; exact hrest_len
      · rw [Walk.edges_reverse, List.mem_reverse]; exact hnot_mem
    · have hrev_cyc : c₁.reverse.IsCycle := hc₁.reverse
      have hrev_len : c₁.reverse.length = c.length := by rw [Walk.length_reverse, hlen₁]
      cases hre : c₁.reverse with
      | nil => exact False.elim (hrev_cyc.ne_nil hre)
      | @cons _ w _ haw rest' =>
        have hwb : w = b := by
          have hmem_rev : s(a, b) ∈ c₁.reverse.edges := by
            rw [Walk.edges_reverse, List.mem_reverse]; exact hmem₁
          rw [hre, Walk.edges_cons, List.mem_cons] at hmem_rev
          rcases hmem_rev with hfirst | hin
          · rcases Sym2.eq_iff.mp hfirst with ⟨_, rfl⟩ | ⟨h1, _⟩
            · rfl
            · exact False.elim (hab h1)
          · exfalso
            have hrest'_path : rest'.IsPath := by
              apply Walk.IsPath.mk'
              have hn := hrev_cyc.support_nodup
              rw [hre, Walk.support_cons, List.tail_cons] at hn; exact hn
            have hc1_eq : c₁ = rest'.reverse.append (.cons haw.symm .nil) := by
              have h1 := congrArg Walk.reverse hre
              rw [Walk.reverse_reverse, Walk.reverse_cons] at h1; exact h1
            cases hrr : rest'.reverse with
            | nil =>
              have := congrArg Walk.edges hrr
              rw [Walk.edges_reverse, List.reverse_eq_nil_iff] at this
              rw [this] at hin; simp at hin
            | @cons _ u' _ hau' rest'' =>
              have hu' : u' = u := by
                rw [hrr, Walk.cons_append] at hc1_eq; rw [hce] at hc1_eq
                exact (Walk.cons.inj hc1_eq).1.symm
              subst hu'
              have hin_rr : s(a, b) ∈ (rest'.reverse).edges := by
                rw [Walk.edges_reverse, List.mem_reverse]; exact hin
              rw [hrr, Walk.edges_cons, List.mem_cons] at hin_rr
              rcases hin_rr with h1 | h2
              · rcases Sym2.eq_iff.mp h1 with ⟨_, rfl⟩ | ⟨h1, _⟩
                · exact hub rfl
                · exact hab h1
              · have ha_in : a ∈ rest''.support := Walk.fst_mem_support_of_mem_edges rest'' h2
                have hnd := hrest'_path.reverse.support_nodup
                rw [hrr, Walk.support_cons, List.nodup_cons] at hnd; exact hnd.1 ha_in
        subst hwb
        have hrest'_path : rest'.IsPath := by
          apply Walk.IsPath.mk'
          have hn := hrev_cyc.support_nodup
          rw [hre, Walk.support_cons, List.tail_cons] at hn; exact hn
        have hrest'_len : rest'.length + 1 = c.length := by
          have := congrArg Walk.length hre; simp only [Walk.length_cons] at this; omega
        have hnot_mem : s(a, b) ∉ rest'.edges := by
          have hnd := hrev_cyc.edges_nodup; rw [hre, Walk.edges_cons, List.nodup_cons] at hnd; exact hnd.1
        refine ⟨rest'.reverse, hrest'_path.reverse, ?_, ?_⟩
        · rw [Walk.length_reverse]; exact hrest'_len
        · rw [Walk.edges_reverse, List.mem_reverse]; exact hnot_mem

/-- Master P3-to-(2^k+1)-cycle lifting lemma. -/
private theorem fermat_cycle_of_delete_add_edge [DecidableEq V]
    {G : SimpleGraph V} {S : Set V} {v : V} (hv : v ∉ S)
    {a b : S} (hab : a ≠ b)
    (hva : G.Adj v a.1) (hvb : G.Adj v b.1)
    (hfree : ¬ HasPower G)
    (hpow : HasPower ((G.induce S) ⊔ SimpleGraph.edge a b)) :
    ∃ (k : ℕ) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k + 1 ∧
      s(v, a.1) ∈ c.edges ∧ s(v, b.1) ∈ c.edges ∧ ∀ u ∈ c.support, u = v ∨ u ∈ S := by
  classical
  obtain ⟨k, v₀, c, hk, hc, hlen⟩ := hpow
  have hge4 : 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide : 0 < 2) hk
  by_cases huses : s(a, b) ∈ c.edges
  · obtain ⟨p, hp, hplen, hnot⟩ := extract_path_of_cycle_edge hab c hc huses
    let pG : G.Walk a.1 b.1 := liftAvoidEdge p hnot
    have hpG_len : pG.length = 2 ^ k - 1 := by rw [length_liftAvoidEdge]; omega
    have hpG_supp : pG.support = p.support.map Subtype.val := support_liftAvoidEdge p hnot
    have hpG_nodup : pG.support.Nodup := by
      rw [hpG_supp]; exact (List.nodup_map_iff Subtype.val_injective).mpr hp.support_nodup
    have hvnot : v ∉ pG.support := by
      rw [hpG_supp]; intro hm
      obtain ⟨u, _, huv⟩ := List.mem_map.mp hm
      exact hv (huv ▸ u.2)
    let cyc : G.Walk v v := .cons hva (pG.append (.cons hvb.symm .nil))
    have hclen : cyc.length = 2 ^ k + 1 := by
      simp only [cyc, Walk.length_cons, Walk.length_append, Walk.length_nil, hpG_len]; omega
    have hcsupp : cyc.support = v :: (pG.support ++ [v]) := by
      simp [cyc, Walk.support_cons, Walk.support_append]
    have hctail : cyc.support.tail.Nodup := by
      rw [hcsupp, List.tail_cons]
      exact List.nodup_append'.mpr ⟨hpG_nodup, List.nodup_singleton v,
        fun z hz1 hz2 => hvnot ((List.mem_singleton.mp hz2) ▸ hz1)⟩
    have hcnil : ¬ cyc.Nil := fun h => by have := Walk.length_eq_zero_iff.mpr h; omega
    have hcyc : cyc.IsCycle := by
      apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      refine ⟨Walk.IsPath.mk' ?_, by omega⟩
      rwa [Walk.support_tail_of_not_nil _ hcnil]
    have hmem1 : s(v, a.1) ∈ cyc.edges := by simp [cyc]
    have hmem2 : s(v, b.1) ∈ cyc.edges := by
      simp only [cyc, Walk.edges_cons, Walk.edges_append, Walk.edges_nil, List.mem_cons, List.mem_append]
      exact Or.inr (Or.inr (Or.inl Sym2.eq_swap))
    have hsuppP : ∀ u ∈ cyc.support, u = v ∨ u ∈ S := by
      intro u hu
      rw [hcsupp, List.mem_cons] at hu
      rcases hu with rfl | hu
      · exact Or.inl rfl
      · rcases List.mem_append.mp hu with h1 | h2
        · rw [hpG_supp] at h1
          obtain ⟨w, _, rfl⟩ := List.mem_map.mp h1
          exact Or.inr w.2
        · exact Or.inl (List.mem_singleton.mp h2)
    exact ⟨k, cyc, hk, hcyc, hclen, hmem1, hmem2, hsuppP⟩
  · let cG : G.Walk v₀.1 v₀.1 := liftAvoidEdge c huses
    have hcG_len : cG.length = 2 ^ k := by rw [length_liftAvoidEdge, hlen]
    have hcG_tail : cG.support.tail.Nodup := by
      rw [support_liftAvoidEdge, ← List.map_tail]
      exact (List.nodup_map_iff Subtype.val_injective).mpr hc.support_nodup
    have hcG_nil : ¬ cG.Nil := fun h => by have := Walk.length_eq_zero_iff.mpr h; omega
    have hcG_cyc : cG.IsCycle := by
      apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      refine ⟨Walk.IsPath.mk' ?_, by omega⟩
      rwa [Walk.support_tail_of_not_nil _ hcG_nil]
    exact False.elim (hfree ⟨k, v₀.1, cG, hk, hcG_cyc, hcG_len⟩)

private theorem degree_sup_edge {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] {a b : W} (hab : a ≠ b) (hnadj : ¬ H.Adj a b)
    [DecidableRel (H ⊔ SimpleGraph.edge a b).Adj] (u : W) :
    (H ⊔ SimpleGraph.edge a b).degree u = H.degree u + (if u = a ∨ u = b then 1 else 0) := by
  classical
  let H' := H ⊔ SimpleGraph.edge a b
  rw [← H'.card_neighborFinset_eq_degree, ← H.card_neighborFinset_eq_degree]
  by_cases hua : u = a
  · subst hua; simp only [true_or, ite_true]
    have heq : H'.neighborFinset u = insert b (H.neighborFinset u) := by
      ext z; simp only [H', SimpleGraph.mem_neighborFinset, Finset.mem_insert,
        SimpleGraph.sup_adj, SimpleGraph.edge_adj]
      constructor
      · rintro (h | ⟨⟨_, rfl⟩ | ⟨h1, _⟩, _⟩)
        · exact Or.inr h
        · exact Or.inl rfl
        · exact False.elim (hab h1)
      · rintro (rfl | h)
        · exact Or.inr ⟨Or.inl ⟨trivial, rfl⟩, hab⟩
        · exact Or.inl h
    rw [heq, Finset.card_insert_of_notMem (by simp [SimpleGraph.mem_neighborFinset, hnadj])]
  · by_cases hub : u = b
    · subst hub; simp only [or_true, ite_true]
      have heq : H'.neighborFinset u = insert a (H.neighborFinset u) := by
        ext z; simp only [H', SimpleGraph.mem_neighborFinset, Finset.mem_insert,
          SimpleGraph.sup_adj, SimpleGraph.edge_adj]
        constructor
        · rintro (h | ⟨⟨h1, _⟩ | ⟨_, rfl⟩, _⟩)
          · exact Or.inr h
          · exact False.elim (hab h1.symm)
          · exact Or.inl rfl
        · rintro (rfl | h)
          · exact Or.inr ⟨Or.inr ⟨trivial, rfl⟩, hab.symm⟩
          · exact Or.inl h
      rw [heq, Finset.card_insert_of_notMem (by simp [SimpleGraph.mem_neighborFinset]; exact fun h => hnadj h.symm)]
    · simp only [hua, hub, or_self, ite_false, add_zero]
      congr 1; ext z
      simp only [H', SimpleGraph.mem_neighborFinset, SimpleGraph.sup_adj, SimpleGraph.edge_adj]
      constructor
      · rintro (h | ⟨⟨h1, _⟩ | ⟨h1, _⟩, _⟩)
        · exact h
        · exact False.elim (hua h1)
        · exact False.elim (hub h1)
      · exact Or.inl

private theorem degree_delete_one [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    [DecidableRel (G.induce {u : V | u ≠ v}).Adj] (u : {u : V // u ≠ v}) :
    (G.induce {w : V | w ≠ v}).degree u + (if G.Adj v u.1 then 1 else 0) = G.degree u.1 := by
  classical
  let H := G.induce {w : V | w ≠ v}
  rw [← H.card_neighborFinset_eq_degree, ← G.card_neighborFinset_eq_degree]
  have hbij : (H.neighborFinset u).card = ((G.neighborFinset u.1).erase v).card := by
    apply Finset.card_bij (fun a _ => a.1)
    · intro a ha; simp only [SimpleGraph.mem_neighborFinset, Finset.mem_erase] at ha ⊢; exact ⟨a.2, ha⟩
    · intro a _ b _ h; exact Subtype.ext h
    · intro b hb; simp only [Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hb
      exact ⟨⟨b, hb.1⟩, (H.mem_neighborFinset u ⟨b, hb.1⟩).mpr hb.2, rfl⟩
  rw [hbij]
  by_cases hadj : G.Adj v u.1
  · simp only [hadj, ite_true]; exact Finset.card_erase_add_one ((G.mem_neighborFinset u.1 v).mpr hadj.symm)
  · simp only [hadj, ite_false, add_zero]
    rw [Finset.erase_eq_of_notMem (fun hm => hadj ((G.mem_neighborFinset u.1 v).mp hm).symm)]

/-- 1. NEW (Wave 3, Agent #1): Cubic Induced-P3 Fermat Cycle Theorem. -/
theorem cubic_p3_fermat_cycle [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G) (hC : Cubic G)
    {v a b : V} (hab : a ≠ b) (hva : G.Adj v a) (hvb : G.Adj v b) (hnadj : ¬ G.Adj a b) :
    ∃ (k : ℕ) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k + 1 ∧
      s(v, a) ∈ c.edges ∧ s(v, b) ∈ c.edges := by
  classical
  have hdv : (G.neighborFinset v).card = 3 := by rw [G.card_neighborFinset_eq_degree, hC v]
  have ha_mem : a ∈ G.neighborFinset v := (G.mem_neighborFinset v a).mpr hva
  have hb_mem : b ∈ (G.neighborFinset v).erase a :=
    Finset.mem_erase.mpr ⟨hab.symm, (G.mem_neighborFinset v b).mpr hvb⟩
  have h1 : (((G.neighborFinset v).erase a).erase b).card = 1 := by
    rw [Finset.card_erase_of_mem hb_mem, Finset.card_erase_of_mem ha_mem, hdv]
  obtain ⟨c₀, hc₀_eq⟩ := Finset.card_eq_one.mp h1
  have hc₀_mem : c₀ ∈ ((G.neighborFinset v).erase a).erase b := by rw [hc₀_eq]; simp
  simp only [Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hc₀_mem
  have hvc₀ : G.Adj v c₀ := hc₀_mem.2.2
  let S : Set V := {u : V | u ≠ v}
  let A : S := ⟨a, (G.ne_of_adj hva).symm⟩
  let B : S := ⟨b, (G.ne_of_adj hvb).symm⟩
  let C₀ : S := ⟨c₀, (G.ne_of_adj hvc₀).symm⟩
  have hAB : A ≠ B := fun h => hab (congrArg Subtype.val h)
  let H := (G.induce S) ⊔ SimpleGraph.edge A B
  have hdegH : ∀ u : S, u ≠ C₀ → 3 ≤ H.degree u := by
    intro u huC
    have h1 : H.degree u = (G.induce S).degree u + (if u = A ∨ u = B then 1 else 0) := by
      convert degree_sup_edge (G.induce S) hAB hnadj u
    have h2 : (G.induce S).degree u + (if G.Adj v u.1 then 1 else 0) = G.degree u.1 := by
      convert degree_delete_one G v u
    have h3 := hC u.1
    by_cases huA : u = A
    · simp only [huA, true_or, ite_true] at h1; omega
    · by_cases huB : u = B
      · simp only [huB, or_true, ite_true] at h1; omega
      · have hnot : ¬ G.Adj v u.1 := by
          intro hadj
          have hm' : u.1 ∈ ((G.neighborFinset v).erase a).erase b := by
            simp only [Finset.mem_erase, SimpleGraph.mem_neighborFinset]
            exact ⟨fun h => huB (Subtype.ext h), fun h => huA (Subtype.ext h), hadj⟩
          rw [hc₀_eq, Finset.mem_singleton] at hm'
          exact huC (Subtype.ext hm')
        simp only [hnot, ite_false, add_zero] at h2; omega
  have hnear : Near H := ⟨⟨A, hdegH A (fun h => hc₀_mem.2.1 (congrArg Subtype.val h).symm)⟩, ⟨C₀, hdegH⟩⟩
  have hcard : Fintype.card S < Fintype.card V := by
    apply Fintype.card_lt_of_injective_not_surjective Subtype.val Subtype.val_injective
    intro hsurj; obtain ⟨x, hx⟩ := hsurj v; exact x.2 hx
  have hpow : HasPower H := hm.2.2.1 _ H hcard hnear
  obtain ⟨k, c, hk, hc, hlen, hm1, hm2, _⟩ :=
    fermat_cycle_of_delete_add_edge (show v ∉ S from fun h => h rfl) hAB hva hvb hm.2.1 hpow
  exact ⟨k, c, hk, hc, hlen, hm1, hm2⟩

/-- 2. NEW (Wave 3, Agent #1): Defect-Vertex Induced-P3 Fermat Cycle Theorem. -/
theorem defect_p3_fermat_cycle [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {w b₁ b₂ : V} (hw : G.degree w = 2) (hb12 : b₁ ≠ b₂)
    (hwb₁ : G.Adj w b₁) (hwb₂ : G.Adj w b₂) (hnadj : ¬ G.Adj b₁ b₂) :
    ∃ (k : ℕ) (c : G.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k + 1 ∧
      s(w, b₁) ∈ c.edges ∧ s(w, b₂) ∈ c.edges := by
  classical
  have hNw : G.neighborFinset w = {b₁, b₂} := by
    symm; apply Finset.eq_of_subset_of_card_le
    · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with hz | hz
      · rw [hz]; exact (G.mem_neighborFinset w b₁).mpr hwb₁
      · rw [hz]; exact (G.mem_neighborFinset w b₂).mpr hwb₂
    · rw [G.card_neighborFinset_eq_degree, hw, Finset.card_pair hb12]
  let S : Set V := {u : V | u ≠ w}
  let B₁ : S := ⟨b₁, (G.ne_of_adj hwb₁).symm⟩
  let B₂ : S := ⟨b₂, (G.ne_of_adj hwb₂).symm⟩
  have hB12 : B₁ ≠ B₂ := fun h => hb12 (congrArg Subtype.val h)
  let H := (G.induce S) ⊔ SimpleGraph.edge B₁ B₂
  obtain ⟨_, w₀, hw₀⟩ := hm.1
  have hww₀ : w = w₀ := by by_contra hne; have := hw₀ w hne; omega
  have hdegH : ∀ u : S, 3 ≤ H.degree u := by
    intro u
    have h1 : H.degree u = (G.induce S).degree u + (if u = B₁ ∨ u = B₂ then 1 else 0) := by
      convert degree_sup_edge (G.induce S) hB12 hnadj u
    have h2 : (G.induce S).degree u + (if G.Adj w u.1 then 1 else 0) = G.degree u.1 := by
      convert degree_delete_one G w u
    have h3 : 3 ≤ G.degree u.1 := hw₀ u.1 (hww₀ ▸ u.2)
    by_cases hu1 : u = B₁
    · simp only [hu1, true_or, ite_true] at h1; omega
    · by_cases hu2 : u = B₂
      · simp only [hu2, or_true, ite_true] at h1; omega
      · have hnot : ¬ G.Adj w u.1 := by
          intro hadj
          have hm' : u.1 ∈ G.neighborFinset w := (G.mem_neighborFinset w u.1).mpr hadj
          rw [hNw] at hm'
          simp only [Finset.mem_insert, Finset.mem_singleton] at hm'
          rcases hm' with h | h
          · exact hu1 (Subtype.ext h)
          · exact hu2 (Subtype.ext h)
        simp only [hnot, ite_false, add_zero] at h2; omega
  have hnear : Near H := ⟨⟨B₁, hdegH B₁⟩, ⟨B₁, fun u _ => hdegH u⟩⟩
  have hcard : Fintype.card S < Fintype.card V := by
    apply Fintype.card_lt_of_injective_not_surjective Subtype.val Subtype.val_injective
    intro hsurj; obtain ⟨x, hx⟩ := hsurj w; exact x.2 hx
  have hpow : HasPower H := hm.2.2.1 _ H hcard hnear
  obtain ⟨k, c, hk, hc, hlen, hm1, hm2, _⟩ :=
    fermat_cycle_of_delete_add_edge (show w ∉ S from fun h => h rfl) hB12 hwb₁ hwb₂ hm.2.1 hpow
  exact ⟨k, c, hk, hc, hlen, hm1, hm2⟩

/-- 3. NEW (Wave 3, Agent #1): Defect-Neighbor Induced-P3 Fermat Cycle Theorem (avoiding `w`). -/
theorem defect_neighbor_p3_fermat_cycle [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {w b₁ b₂ a b : V} (hw : G.degree w = 2) (hb12 : b₁ ≠ b₂)
    (hwb₁ : G.Adj w b₁) (hwb₂ : G.Adj w b₂)
    (hab : a ≠ b) (haw : a ≠ w) (hbw : b ≠ w)
    (hb₁a : G.Adj b₁ a) (hb₁b : G.Adj b₁ b) (hnadj : ¬ G.Adj a b) :
    ∃ (k : ℕ) (c : G.Walk b₁ b₁), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k + 1 ∧
      s(b₁, a) ∈ c.edges ∧ s(b₁, b) ∈ c.edges ∧ w ∉ c.support := by
  classical
  have hdb₁ : G.degree b₁ = 3 := defect_neighbor_cubic G hm hw hwb₁
  have hNw : G.neighborFinset w = {b₁, b₂} := by
    symm; apply Finset.eq_of_subset_of_card_le
    · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with hz | hz
      · rw [hz]; exact (G.mem_neighborFinset w b₁).mpr hwb₁
      · rw [hz]; exact (G.mem_neighborFinset w b₂).mpr hwb₂
    · rw [G.card_neighborFinset_eq_degree, hw, Finset.card_pair hb12]
  have hNb₁ : G.neighborFinset b₁ = {w, a, b} := by
    symm; apply Finset.eq_of_subset_of_card_le
    · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with hz | hz | hz
      · rw [hz]; exact (G.mem_neighborFinset b₁ w).mpr hwb₁.symm
      · rw [hz]; exact (G.mem_neighborFinset b₁ a).mpr hb₁a
      · rw [hz]; exact (G.mem_neighborFinset b₁ b).mpr hb₁b
    · rw [G.card_neighborFinset_eq_degree, hdb₁]
      have h3 : ({w, a, b} : Finset V).card = 3 := by
        simp [Finset.card_insert_of_notMem, haw.symm, hbw.symm, hab]
      omega
  let S : Set V := {u : V | u ≠ w ∧ u ≠ b₁}
  let A : S := ⟨a, ⟨haw, (G.ne_of_adj hb₁a).symm⟩⟩
  let B : S := ⟨b, ⟨hbw, (G.ne_of_adj hb₁b).symm⟩⟩
  let B₂ : S := ⟨b₂, ⟨(G.ne_of_adj hwb₂).symm, hb12.symm⟩⟩
  have hAB : A ≠ B := fun h => hab (congrArg Subtype.val h)
  let H := (G.induce S) ⊔ SimpleGraph.edge A B
  obtain ⟨_, w₀, hw₀⟩ := hm.1
  have hww₀ : w = w₀ := by by_contra hne; have := hw₀ w hne; omega
  have hdeg_ind : ∀ u : S,
      (G.induce S).degree u + (if G.Adj w u.1 then 1 else 0) + (if G.Adj b₁ u.1 then 1 else 0) =
        G.degree u.1 := by
    intro u
    rw [← (G.induce S).card_neighborFinset_eq_degree, ← G.card_neighborFinset_eq_degree]
    have hbij : ((G.induce S).neighborFinset u).card =
        (((G.neighborFinset u.1).erase w).erase b₁).card := by
      apply Finset.card_bij (fun x _ => x.1)
      · intro x hx; simp only [SimpleGraph.mem_neighborFinset, Finset.mem_erase] at hx ⊢
        exact ⟨x.2.2, x.2.1, hx⟩
      · intro x _ y _ h; exact Subtype.ext h
      · intro y hy; simp only [Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hy
        exact ⟨⟨y, ⟨hy.2.1, hy.1⟩⟩, ((G.induce S).mem_neighborFinset u ⟨y, ⟨hy.2.1, hy.1⟩⟩).mpr hy.2.2, rfl⟩
    rw [hbij]
    have h1 : (((G.neighborFinset u.1).erase w).erase b₁).card + (if G.Adj b₁ u.1 then 1 else 0) =
        ((G.neighborFinset u.1).erase w).card := by
      by_cases h : G.Adj b₁ u.1
      · simp only [h, ite_true]
        exact Finset.card_erase_add_one (Finset.mem_erase.mpr
          ⟨(G.ne_of_adj hwb₁).symm, (G.mem_neighborFinset u.1 b₁).mpr h.symm⟩)
      · simp only [h, ite_false, add_zero]
        exact congrArg Finset.card (Finset.erase_eq_of_notMem (fun hm =>
          h ((G.mem_neighborFinset u.1 b₁).mp (Finset.mem_erase.mp hm).2).symm))
    have h2 : ((G.neighborFinset u.1).erase w).card + (if G.Adj w u.1 then 1 else 0) =
        (G.neighborFinset u.1).card := by
      by_cases h : G.Adj w u.1
      · simp only [h, ite_true]
        exact Finset.card_erase_add_one ((G.mem_neighborFinset u.1 w).mpr h.symm)
      · simp only [h, ite_false, add_zero]
        exact congrArg Finset.card (Finset.erase_eq_of_notMem (fun hm =>
          h ((G.mem_neighborFinset u.1 w).mp hm).symm))
    omega
  have hdegH : ∀ u : S, u ≠ B₂ → 3 ≤ H.degree u := by
    intro u huB2
    have h1 : H.degree u = (G.induce S).degree u + (if u = A ∨ u = B then 1 else 0) := by
      convert degree_sup_edge (G.induce S) hAB hnadj u
    have h2 := hdeg_ind u
    have h3 : 3 ≤ G.degree u.1 := hw₀ u.1 (hww₀ ▸ u.2.1)
    have hnotw : ¬ G.Adj w u.1 := by
      intro hadj
      have hm' : u.1 ∈ G.neighborFinset w := (G.mem_neighborFinset w u.1).mpr hadj
      rw [hNw] at hm'; simp only [Finset.mem_insert, Finset.mem_singleton] at hm'
      rcases hm' with h | h
      · exact u.2.2 h
      · exact huB2 (Subtype.ext h)
    simp only [hnotw, ite_false, add_zero] at h2
    by_cases huA : u = A
    · simp only [huA, true_or, ite_true] at h1; omega
    · by_cases huB : u = B
      · simp only [huB, or_true, ite_true] at h1; omega
      · have hnotb1 : ¬ G.Adj b₁ u.1 := by
          intro hadj
          have hm' : u.1 ∈ G.neighborFinset b₁ := (G.mem_neighborFinset b₁ u.1).mpr hadj
          rw [hNb₁] at hm'; simp only [Finset.mem_insert, Finset.mem_singleton] at hm'
          rcases hm' with h | h | h
          · exact u.2.1 h
          · exact huA (Subtype.ext h)
          · exact huB (Subtype.ext h)
        simp only [hnotb1, ite_false, add_zero] at h2; omega
  have hex_good : ∃ u : S, u ≠ B₂ := by
    by_cases hAB2 : A = B₂
    · exact ⟨B, fun h => hAB (hAB2.trans h.symm)⟩
    · exact ⟨A, hAB2⟩
  obtain ⟨u₀, hu₀⟩ := hex_good
  have hnear : Near H := ⟨⟨u₀, hdegH u₀ hu₀⟩, ⟨B₂, hdegH⟩⟩
  have hcard : Fintype.card S < Fintype.card V := by
    apply Fintype.card_lt_of_injective_not_surjective Subtype.val Subtype.val_injective
    intro hsurj; obtain ⟨x, hx⟩ := hsurj w; exact x.2.1 hx
  have hpow : HasPower H := hm.2.2.1 _ H hcard hnear
  obtain ⟨k, c, hk, hc, hlen, hm1, hm2, hsuppP⟩ :=
    fermat_cycle_of_delete_add_edge (show b₁ ∉ S from fun h => h.2 rfl) hAB hb₁a hb₁b hm.2.1 hpow
  have hwnot : w ∉ c.support := by
    intro hwm
    rcases hsuppP w hwm with h | h
    · exact (G.ne_of_adj hwb₁) h
    · exact h.1 rfl
  exact ⟨k, c, hk, hc, hlen, hm1, hm2, hwnot⟩

#print axioms cubic_p3_fermat_cycle
#print axioms defect_p3_fermat_cycle
#print axioms defect_neighbor_p3_fermat_cycle

end E64Wave3PathCycle
