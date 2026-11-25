import Core
import Leaves
import ClosedDefectCore

/-!
# Erdős #64 Wave 2 Agent #3 — Lean 4.36.0 Structural Theorems on `MinimalBad`

All-order, unconditional theorems on any `MinimalBad G` counterexample
(no finite bound, standard axioms `propext`, `Classical.choice`, `Quot.sound` only):
1. `minimal_bad_no_c4`: Every `MinimalBad G` is $C_4$-free.
2. `unique_common_neighbor`: Non-adjacent vertices in `MinimalBad G` have at most one common neighbor.
3. `minimal_bad_no_high_adj`: In any `MinimalBad G`, $V_{\ge 4}$ is an independent set.
4. `universal_dyadic_path`: For any $x \neq y$ with $\neg G.\text{Adj}\ x\ y$ and $N(x) \cap N(y) = \emptyset$,
   $G$ contains a simple $x$–$y$ path of length $2^k$ ($k \ge 2$).
5. `unified_bipartite_exclusion`: Unified exclusion of all bipartite `MinimalBad` graphs (`C-B`, `S-B`, `H-B-*`).
6. `cubic_dist2_dyadic_path` (NEW): In any cubic `MinimalBad G`, for any non-adjacent $x, y$ with
   common neighbor $z$, $G - z$ contains a simple $x$–$y$ path of length $2^k$ ($k \ge 2$).
7. `cubic_all_nonadj_dyadic_path` (NEW): In any cubic `MinimalBad G`, EVERY non-adjacent pair
   has a simple $x$–$y$ path of length $2^k$ ($k \ge 2$).
8. `cubic_p3_dyadic_plus_two_cycle` (NEW): Every induced $P_3$ in cubic `MinimalBad G` lies on a
   simple cycle of length $2^k + 2$ ($k \ge 2$).
9. `defect_dist2_dyadic_path` (NEW): In any one-defect (`S` or `H`) `MinimalBad G` with degree-2
   defect $w$ and neighbors $b_1, b_2$, for every $v \in N(b_1) \setminus \{w, b_2\}$, $G - \{w, b_1\}$
   contains a simple $b_2$–$v$ path of length $2^k - 1$ ($k \ge 2$).
-/

namespace E64Wave2Structural
open SimpleGraph Erdos64Closure E64Core E64Leaves E64DefectCore
universe u

def HasDyadicPath {V : Type u} (G : SimpleGraph V) (x y : V) : Prop :=
  ∃ (k : ℕ) (p : G.Walk x y), 2 ≤ k ∧ p.IsPath ∧ p.length = 2 ^ k

def HasDyadicPathAvoiding {V : Type u} (G : SimpleGraph V) (x y z : V) : Prop :=
  ∃ (k : ℕ) (p : G.Walk x y), 2 ≤ k ∧ p.IsPath ∧ p.length = 2 ^ k ∧ z ∉ p.support

/-- Every `MinimalBad G` is $C_4$-free. -/
theorem minimal_bad_no_c4 {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {a b c d : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) : False := by
  have hab_ne : a ≠ b := G.ne_of_adj hab
  have hbc_ne : b ≠ c := G.ne_of_adj hbc
  have hcd_ne : c ≠ d := G.ne_of_adj hcd
  have hda_ne : d ≠ a := G.ne_of_adj hda
  let w : G.Walk a a := Walk.cons hab (Walk.cons hbc (Walk.cons hcd (Walk.cons hda Walk.nil)))
  have htrail : w.IsTrail := by
    rw [Walk.isTrail_def]
    simp [w, Sym2.eq_iff, hab_ne, hbc_ne, hcd_ne, hda_ne, hac, hbd,
      hab_ne.symm, hbc_ne.symm, hcd_ne.symm, hda_ne.symm, hac.symm]
  have hcyc : w.IsCycle := by
    refine ⟨⟨htrail, by simp [w]⟩, ?_⟩
    simp [w, hab_ne, hbc_ne, hcd_ne, hda_ne, hac, hbd,
      hab_ne.symm, hbc_ne.symm, hcd_ne.symm, hda_ne.symm, hac.symm]
  exact hm.2.1 ⟨2, a, w, le_rfl, hcyc, rfl⟩

/-- Non-adjacent distinct vertices in `MinimalBad G` have at most one common neighbor. -/
theorem unique_common_neighbor {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {x y z₁ z₂ : V} (hxy : x ≠ y)
    (hxz₁ : G.Adj x z₁) (hyz₁ : G.Adj y z₁)
    (hxz₂ : G.Adj x z₂) (hyz₂ : G.Adj y z₂) : z₁ = z₂ := by
  by_contra hne
  exact minimal_bad_no_c4 G hm hxz₁ hyz₁.symm hyz₂ hxz₂.symm hxy hne

/-- In any `MinimalBad G`, no two vertices of degree ≥ 4 are adjacent. -/
theorem minimal_bad_no_high_adj {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {a b : V} (ha : 4 ≤ G.degree a) (hb : 4 ≤ G.degree b) : ¬G.Adj a b := by
  classical
  intro hab
  obtain ⟨_, r, hr⟩ := hm.1
  let H := G \ SimpleGraph.edge a b
  let _ : DecidableRel H.Adj :=
    inferInstanceAs (DecidableRel (G \ SimpleGraph.edge a b).Adj)
  have hcard : 2 ≤ Fintype.card V := by
    have := G.degree_lt_card_verts a
    omega
  have hn : Near H := by
    apply near_of_except H r hcard
    intro v hv
    have hdeg := erase_edge_degree G a b hab v
    change H.degree v + (if v = a ∨ v = b then 1 else 0) = G.degree v at hdeg
    by_cases hva : v = a
    · subst v; simp at hdeg; omega
    by_cases hvb : v = b
    · subst v; simp at hdeg; omega
    · simp [hva, hvb] at hdeg
      rw [hdeg]
      exact hr v hv
  have hEq : H = G := hm.2.2.2 H sdiff_le hn
  have he : H.Adj a b := hEq ▸ hab
  have hno : ¬H.Adj a b := by
    intro h
    have hn' := (SimpleGraph.sdiff_adj G (SimpleGraph.edge a b) a b).mp h
    exact hn'.2 ((SimpleGraph.edge_adj a b a b).mpr ⟨Or.inl ⟨rfl, rfl⟩, G.ne_of_adj hab⟩)
  exact hno he

/-! ### Vertex Identification Graph $G / (x = y)$ on `{v : V // v ≠ y}` -/

section Identification

variable {V : Type u} (G : SimpleGraph V)

def identGraph (x y : V) : SimpleGraph {v : V // v ≠ y} where
  Adj a b := a ≠ b ∧ (G.Adj a.1 b.1 ∨ (a.1 = x ∧ G.Adj y b.1) ∨ (b.1 = x ∧ G.Adj a.1 y))
  symm := ⟨by
    intro a b ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    rcases h with h | ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr ⟨hx, hy.symm⟩)
    · exact Or.inr (Or.inl ⟨hx, hy.symm⟩)⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

/-- Lift a walk in `identGraph G x y` that avoids `u = ⟨x, hxy⟩` directly to a walk in `G`. -/
def liftWalkAvoidU {x y : V} (hxy : x ≠ y) :
    ∀ {a b : {v : V // v ≠ y}} (p : (identGraph G x y).Walk a b),
      (⟨x, hxy⟩ : {v : V // v ≠ y}) ∉ p.support → G.Walk a.1 b.1
  | _, _, Walk.nil, _ => Walk.nil
  | a, _, @Walk.cons _ _ _ b _ h rest, hnot =>
    have ha_ne : a.1 ≠ x := by
      intro hax
      apply hnot
      simp only [Walk.support_cons, List.mem_cons]
      exact Or.inl (Subtype.ext hax.symm)
    have hb_ne : b.1 ≠ x := by
      intro hbx
      apply hnot
      simp only [Walk.support_cons, List.mem_cons]
      right
      have hbeq : b = (⟨x, hxy⟩ : {v : V // v ≠ y}) := Subtype.ext hbx
      rw [← hbeq]
      exact Walk.start_mem_support rest
    have hadj : G.Adj a.1 b.1 := by
      rcases h.2 with h1 | ⟨h2, _⟩ | ⟨h3, _⟩
      · exact h1
      · exact False.elim (ha_ne h2)
      · exact False.elim (hb_ne h3)
    have hnot_rest : (⟨x, hxy⟩ : {v : V // v ≠ y}) ∉ rest.support := by
      intro hmem
      exact hnot (List.mem_cons_of_mem _ hmem)
    Walk.cons hadj (liftWalkAvoidU hxy rest hnot_rest)

theorem liftWalkAvoidU_support {x y : V} (hxy : x ≠ y) :
    ∀ {a b : {v : V // v ≠ y}} (p : (identGraph G x y).Walk a b)
      (hnot : (⟨x, hxy⟩ : {v : V // v ≠ y}) ∉ p.support),
      (liftWalkAvoidU G hxy p hnot).support = p.support.map Subtype.val
  | _, _, Walk.nil, _ => rfl
  | _, _, Walk.cons _ rest, hnot => by
    simp only [liftWalkAvoidU, Walk.support_cons, List.map_cons]
    congr 1
    exact liftWalkAvoidU_support hxy rest (fun hm => hnot (List.mem_cons_of_mem _ hm))

theorem liftWalkAvoidU_length {x y : V} (hxy : x ≠ y) :
    ∀ {a b : {v : V // v ≠ y}} (p : (identGraph G x y).Walk a b)
      (hnot : (⟨x, hxy⟩ : {v : V // v ≠ y}) ∉ p.support),
      (liftWalkAvoidU G hxy p hnot).length = p.length
  | _, _, Walk.nil, _ => rfl
  | _, _, Walk.cons _ rest, hnot => by
    simp only [liftWalkAvoidU, Walk.length_cons]
    congr 1
    exact liftWalkAvoidU_length hxy rest (fun hm => hnot (List.mem_cons_of_mem _ hm))

/-- A closed walk of length ≥ 3 whose `support.tail` is `Nodup` is a cycle. -/
theorem isCycle_of_support_tail_nodup {a : V} (c : G.Walk a a)
    (hlen : 3 ≤ c.length) (hnodup : c.support.tail.Nodup) : c.IsCycle := by
  have hne : c ≠ Walk.nil := by
    intro h; subst h; simp at hlen
  have htrail : c.IsTrail := by
    cases c with
    | nil => exact False.elim (hne rfl)
    | @cons _ b _ hab rest =>
      have hrest_nodup : rest.support.Nodup := by
        simpa [Walk.support_cons] using hnodup
      have hrest_path : rest.IsPath := Walk.IsPath.mk' hrest_nodup
      have hrest_trail : rest.IsTrail := hrest_path.isTrail
      rw [Walk.isTrail_def, Walk.edges_cons, List.nodup_cons]
      refine ⟨?_, hrest_trail.edges_nodup⟩
      intro hmem
      have hrest_len : 2 ≤ rest.length := by simp at hlen; omega
      cases rest with
      | nil => simp at hrest_len
      | @cons _ c' _ hbc rest2 =>
        simp only [Walk.edges_cons, List.mem_cons] at hmem
        rcases hmem with heq | hmem2
        · have hac' : a = c' := by
            rw [Sym2.eq_iff] at heq
            rcases heq with ⟨h1, _⟩ | ⟨h1, _⟩
            · exact False.elim (G.ne_of_adj hab h1)
            · exact h1
          subst hac'
          cases rest2 with
          | nil => simp at hrest_len
          | @cons _ d' _ had' rest3 =>
            simp only [Walk.support_cons, List.nodup_cons] at hrest_nodup
            have ha_end : a ∈ rest3.support := Walk.end_mem_support rest3
            exact hrest_nodup.2.1 ha_end
        · have hb_in : b ∈ rest2.support :=
            Walk.mem_support_of_mem_edges hmem2 (by simp)
          simp only [Walk.support_cons, List.nodup_cons] at hrest_nodup
          exact hrest_nodup.1 hb_in
  exact ⟨⟨htrail, hne⟩, hnodup⟩

/-- Core unified cycle-to-path lifting theorem for vertex identification $G / (x = y)$. -/
theorem ident_cycle_lifts {x y : V} (hxy : x ≠ y)
    (hfree : ¬HasPower G)
    {k : ℕ} (hk : 2 ≤ k) {a : {v : V // v ≠ y}}
    (c : (identGraph G x y).Walk a a) (hc : c.IsCycle) (hlen : c.length = 2 ^ k) :
    ∃ (p : G.Walk x y), p.IsPath ∧ p.length = 2 ^ k ∧
      (∀ z : V, (hz : z ≠ y) → G.Adj x z → G.Adj y z →
        (∀ w₁ w₂ : {v : V // v ≠ y},
          (identGraph G x y).Adj ⟨z, hz⟩ w₁ →
          (identGraph G x y).Adj ⟨z, hz⟩ w₂ →
          w₁ ≠ ⟨x, hxy⟩ → w₂ ≠ ⟨x, hxy⟩ → w₁ = w₂) →
        z ∉ p.support) := by
  classical
  let H := identGraph G x y
  let u : {v : V // v ≠ y} := ⟨x, hxy⟩
  have hu_mem : u ∈ c.support := by
    by_contra hnot
    let cG : G.Walk a.1 a.1 := liftWalkAvoidU G hxy c hnot
    have hcG_len : cG.length = 2 ^ k := by rw [liftWalkAvoidU_length, hlen]
    have hcG_sup : cG.support = c.support.map Subtype.val := liftWalkAvoidU_support G hxy c hnot
    have hcG_tail : cG.support.tail.Nodup := by
      rw [hcG_sup, ← List.map_tail]
      exact hc.support_nodup.map Subtype.val_injective
    have h4 : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    have hcG_cyc : cG.IsCycle := isCycle_of_support_tail_nodup G cG (by omega) hcG_tail
    exact hfree ⟨k, a.1, cG, hk, hcG_cyc, hcG_len⟩
  let c' : H.Walk u u := c.rotate hu_mem
  have hc' : c'.IsCycle := hc.rotate hu_mem
  have hc'_len : c'.length = 2 ^ k := by rw [Walk.length_rotate, hlen]
  have h4 : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  cases hce : c' with
  | nil => simp [hce] at hc'_len; omega
  | @cons _ a₁ _ h₁ rest =>
    cases hre : rest.reverse with
    | nil =>
      have hlen_r : rest.reverse.length = 0 := by rw [hre]; rfl
      rw [Walk.length_reverse] at hlen_r
      simp [hce] at hc'_len
      omega
    | @cons _ a₂ _ h₂ mid_rev =>
      let q : H.Walk a₁ a₂ := mid_rev.reverse
      have hrest_eq : rest = q.concat h₂.symm := by
        rw [Walk.concat_eq_append]
        have := congrArg Walk.reverse hre
        simpa [q, Walk.reverse_reverse, Walk.reverse_cons] using this
      have hq_len : q.length + 2 = 2 ^ k := by
        have h1 : c'.length = rest.length + 1 := by simp [hce]
        have h2 : rest.length = q.length + 1 := by simp [hrest_eq]
        omega
      have hc'_tail_eq : c'.support.tail = q.support ++ [u] := by
        rw [hce, Walk.support_cons, List.tail_cons, hrest_eq, Walk.support_concat]
      have hnodup_q_u : (q.support ++ [u]).Nodup := by
        rw [← hc'_tail_eq]
        exact hc'.support_nodup
      have hq_nodup : q.support.Nodup := (List.nodup_append.mp hnodup_q_u).1
      have hu_not_q : u ∉ q.support := by
        intro hm
        exact (List.nodup_append.mp hnodup_q_u).2.2 u hm u (by simp) rfl
      let qG : G.Walk a₁.1 a₂.1 := liftWalkAvoidU G hxy q hu_not_q
      have hqG_sup : qG.support = q.support.map Subtype.val := liftWalkAvoidU_support G hxy q hu_not_q
      have hqG_len : qG.length = q.length := liftWalkAvoidU_length G hxy q hu_not_q
      have hqG_nodup : qG.support.Nodup := by
        rw [hqG_sup]; exact hq_nodup.map Subtype.val_injective
      have hx_not_qG : x ∉ qG.support := by
        rw [hqG_sup, List.mem_map]
        rintro ⟨v, hv, hvx⟩
        have hveq : v = u := Subtype.ext hvx
        exact hu_not_q (hveq ▸ hv)
      have hy_not_qG : y ∉ qG.support := by
        rw [hqG_sup, List.mem_map]
        rintro ⟨v, _, hvy⟩
        exact v.2 hvy
      have no_both_x : ¬(G.Adj x a₁.1 ∧ G.Adj x a₂.1) := by
        rintro ⟨hxa₁, hxa₂⟩
        let cyc : G.Walk x x := Walk.cons hxa₁ (qG.concat hxa₂.symm)
        have hcyc_len : cyc.length = 2 ^ k := by simp [cyc, hqG_len]; omega
        have hcyc_tail : cyc.support.tail.Nodup := by
          rw [Walk.support_cons, List.tail_cons, Walk.support_concat, List.nodup_append]
          exact ⟨hqG_nodup, List.nodup_singleton x, fun v hv w hw heq => by
            rw [List.mem_singleton] at hw
            subst hw; subst heq; exact hx_not_qG hv⟩
        exact hfree ⟨k, x, cyc, hk, isCycle_of_support_tail_nodup G cyc (by omega) hcyc_tail, hcyc_len⟩
      have no_both_y : ¬(G.Adj y a₁.1 ∧ G.Adj y a₂.1) := by
        rintro ⟨hya₁, hya₂⟩
        let cyc : G.Walk y y := Walk.cons hya₁ (qG.concat hya₂.symm)
        have hcyc_len : cyc.length = 2 ^ k := by simp [cyc, hqG_len]; omega
        have hcyc_tail : cyc.support.tail.Nodup := by
          rw [Walk.support_cons, List.tail_cons, Walk.support_concat, List.nodup_append]
          exact ⟨hqG_nodup, List.nodup_singleton y, fun v hv w hw heq => by
            rw [List.mem_singleton] at hw
            subst hw; subst heq; exact hy_not_qG hv⟩
        exact hfree ⟨k, y, cyc, hk, isCycle_of_support_tail_nodup G cyc (by omega) hcyc_tail, hcyc_len⟩
      have h₁_disj : G.Adj x a₁.1 ∨ G.Adj y a₁.1 := by
        rcases h₁.2 with h | ⟨_, h⟩ | ⟨hax, _⟩
        · exact Or.inl h
        · exact Or.inr h
        · have heq : a₁ = u := Subtype.ext hax
          exact False.elim (hu_not_q (heq ▸ Walk.start_mem_support q))
      have h₂_disj : G.Adj x a₂.1 ∨ G.Adj y a₂.1 := by
        rcases h₂.2 with h | ⟨_, h⟩ | ⟨hax, _⟩
        · exact Or.inl h
        · exact Or.inr h
        · have heq : a₂ = u := Subtype.ext hax
          exact False.elim (hu_not_q (heq ▸ Walk.end_mem_support q))
      have hz_avoid : ∀ z : V, (hz : z ≠ y) → G.Adj x z → G.Adj y z →
          (∀ w₁ w₂ : {v : V // v ≠ y},
            H.Adj ⟨z, hz⟩ w₁ → H.Adj ⟨z, hz⟩ w₂ →
            w₁ ≠ u → w₂ ≠ u → w₁ = w₂) →
          z ∉ qG.support := by
        intro z hz hxz hyz hdeg2 hzm
        have hza₁ : (⟨z, hz⟩ : {v : V // v ≠ y}) ≠ a₁ := by
          intro heq
          have h1 : z = a₁.1 := congrArg Subtype.val heq
          rw [h1] at hxz hyz
          rcases h₂_disj with h2x | h2y
          · exact no_both_x ⟨hxz, h2x⟩
          · exact no_both_y ⟨hyz, h2y⟩
        have hza₂ : (⟨z, hz⟩ : {v : V // v ≠ y}) ≠ a₂ := by
          intro heq
          have h2 : z = a₂.1 := congrArg Subtype.val heq
          rw [h2] at hxz hyz
          rcases h₁_disj with h1x | h1y
          · exact no_both_x ⟨h1x, hxz⟩
          · exact no_both_y ⟨h1y, hyz⟩
        have hz_in_q : (⟨z, hz⟩ : {v : V // v ≠ y}) ∈ q.support := by
          rw [hqG_sup, List.mem_map] at hzm
          rcases hzm with ⟨v, hv, hvz⟩
          have hveq : v = (⟨z, hz⟩ : {v : V // v ≠ y}) := Subtype.ext hvz
          exact hveq ▸ hv
        let q₁ := q.takeUntil ⟨z, hz⟩ hz_in_q
        let q₂ := q.dropUntil ⟨z, hz⟩ hz_in_q
        have hspec : q₁.append q₂ = q := Walk.take_spec q hz_in_q
        cases hq₂e : q₂ with
        | nil => exact False.elim (hza₂ rfl)
        | @cons _ w₂ _ hzw₂ q₂' =>
          cases hq₁e : q₁.reverse with
          | nil => exact False.elim (hza₁ rfl)
          | @cons _ w₁ _ hzw₁ q₁' =>
            have hw₁_mem : w₁ ∈ q₁.support := by
              have : w₁ ∈ q₁.reverse.support := by
                rw [hq₁e, Walk.support_cons]; exact List.mem_cons_of_mem _ (Walk.start_mem_support _)
              simpa [Walk.support_reverse] using this
            have hw₂_mem : w₂ ∈ q₂.support := by
              rw [hq₂e, Walk.support_cons]; exact List.mem_cons_of_mem _ (Walk.start_mem_support _)
            have hw₁_ne_u : w₁ ≠ u := by
              intro h; subst h
              exact hu_not_q (by rw [← hspec]; exact Walk.support_append_subset_left q₁ q₂ hw₁_mem)
            have hw₂_ne_u : w₂ ≠ u := by
              intro h; subst h
              exact hu_not_q (by rw [← hspec]; exact Walk.support_append_subset_right q₁ q₂ hw₂_mem)
            have hw_eq : w₁ = w₂ := hdeg2 w₁ w₂ hzw₁ hzw₂ hw₁_ne_u hw₂_ne_u
            have hq_sup_split : q.support = q₁.support.dropLast ++ q₂.support := by
              rw [← hspec, Walk.support_append]
            have hw₁_ne_z : w₁ ≠ ⟨z, hz⟩ := (H.ne_of_adj hzw₁).symm
            have hw₁_in_dl : w₁ ∈ q₁.support.dropLast := by
              have hq₁_sup : q₁.support = q₁.support.dropLast ++ [⟨z, hz⟩] := by
                have hne_s : q₁.support ≠ [] := Walk.support_ne_nil q₁
                have hlast : q₁.support.getLast hne_s = ⟨z, hz⟩ := Walk.getLast_support q₁
                rw [← hlast]; exact (List.dropLast_append_getLast hne_s).symm
              rw [hq₁_sup, List.mem_append, List.mem_singleton] at hw₁_mem
              exact hw₁_mem.resolve_right hw₁_ne_z
            rw [hq_sup_split, List.nodup_append] at hq_nodup
            exact hq_nodup.2.2 w₁ hw₁_in_dl w₁ (hw_eq ▸ hw₂_mem) rfl
      rcases h₁_disj with h1x | h1y
      · rcases h₂_disj with h2x | h2y
        · exact False.elim (no_both_x ⟨h1x, h2x⟩)
        · let p : G.Walk x y := Walk.cons h1x (qG.concat h2y.symm)
          refine ⟨p, ?_, ?_, ?_⟩
          · rw [Walk.isPath_def, Walk.support_cons, Walk.support_concat, List.nodup_cons, List.nodup_append]
            refine ⟨?_, hqG_nodup, List.nodup_singleton y, fun v hv w hw heq => by
              rw [List.mem_singleton] at hw; subst hw; subst heq; exact hy_not_qG hv⟩
            rw [List.mem_append, List.mem_singleton]
            rintro (hx | hxy')
            · exact hx_not_qG hx
            · exact hxy hxy'
          · simp [p, hqG_len]; omega
          · intro z hz hxz hyz hdeg2 hzm
            simp only [p, Walk.support_cons, Walk.support_concat, List.mem_cons, List.mem_append] at hzm
            rcases hzm with rfl | hzq | hzy
            · exact G.loopless.irrefl z hxz
            · exact hz_avoid z hz hxz hyz hdeg2 hzq
            · simp at hzy; exact hz hzy
      · rcases h₂_disj with h2x | h2y
        · let p : G.Walk x y := Walk.cons h2x (qG.reverse.concat h1y.symm)
          have hrev_nodup : qG.reverse.support.Nodup := by
            rw [Walk.support_reverse]; exact List.nodup_reverse.mpr hqG_nodup
          have hx_not_rev : x ∉ qG.reverse.support := by
            rw [Walk.support_reverse, List.mem_reverse]; exact hx_not_qG
          have hy_not_rev : y ∉ qG.reverse.support := by
            rw [Walk.support_reverse, List.mem_reverse]; exact hy_not_qG
          refine ⟨p, ?_, ?_, ?_⟩
          · rw [Walk.isPath_def, Walk.support_cons, Walk.support_concat, List.nodup_cons, List.nodup_append]
            refine ⟨?_, hrev_nodup, List.nodup_singleton y, fun v hv w hw heq => by
              rw [List.mem_singleton] at hw; subst hw; subst heq; exact hy_not_rev hv⟩
            rw [List.mem_append, List.mem_singleton]
            rintro (hx | hxy')
            · exact hx_not_rev hx
            · exact hxy hxy'
          · simp [p, hqG_len]; omega
          · intro z hz hxz hyz hdeg2 hzm
            simp only [p, Walk.support_cons, Walk.support_concat, List.mem_cons, List.mem_append,
              Walk.support_reverse, List.mem_reverse] at hzm
            rcases hzm with rfl | hzq | hzy
            · exact G.loopless.irrefl z hxz
            · exact hz_avoid z hz hxz hyz hdeg2 hzq
            · simp at hzy; exact hz hzy
        · exact False.elim (no_both_y ⟨h1y, h2y⟩)

end Identification

/-! ### Degree Calculations for `identGraph` -/

section IdentDegrees

variable {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem ident_card_lt (y : V) :
    Fintype.card {v : V // v ≠ y} < Fintype.card V := by
  have hW : Fintype.card {v : V // v ≠ y} + 1 = Fintype.card V := by
    rw [Fintype.card_subtype,
      show (Finset.univ.filter (fun x : V => x ≠ y)) = Finset.univ.erase y by ext x; simp]
    exact Finset.card_erase_add_one (Finset.mem_univ y)
  omega

/-- For `v ∉ {x, y}` that is NOT a common neighbor of `x` and `y`, `identGraph` preserves degree. -/
theorem ident_degree_non_common {x y : V} (hxy : x ≠ y)
    (v : {v : V // v ≠ y}) (hvx : v.1 ≠ x)
    (hnot_common : ¬(G.Adj v.1 x ∧ G.Adj v.1 y))
    [DecidableRel (identGraph G x y).Adj] :
    (identGraph G x y).degree v = G.degree v.1 := by
  let H := identGraph G x y
  change H.degree v = G.degree v.1
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
  by_cases hvy : G.Adj v.1 y
  · have hnvx : ¬G.Adj v.1 x := fun h => hnot_common ⟨h, hvy⟩
    let e : H.neighborSet v ≃ G.neighborSet v.1 :=
      { toFun := fun w =>
          if hw : w.1.1 = x then ⟨y, hvy⟩
          else ⟨w.1.1, by
            rcases w.2.2 with h1 | ⟨h2, _⟩ | ⟨h3, _⟩
            · exact h1
            · exact False.elim (hvx h2)
            · exact False.elim (hw h3)⟩
        invFun := fun w =>
          if hw : w.1 = y then
            ⟨⟨x, hxy⟩, ⟨fun h => hvx (congrArg Subtype.val h), Or.inr (Or.inr ⟨rfl, hvy⟩)⟩⟩
          else
            ⟨⟨w.1, hw⟩, ⟨fun h => G.ne_of_adj w.2 (congrArg Subtype.val h), Or.inl w.2⟩⟩
        left_inv := by
          intro ⟨⟨w, hwy⟩, hw⟩
          by_cases hwx : w = x
          · subst hwx; simp
          · simp [hwx, hwy]
        right_inv := by
          intro ⟨w, hw⟩
          by_cases hwy : w = y
          · subst hwy; simp
          · have hwx : w ≠ x := fun h => hnvx (h ▸ hw)
            simp [hwy, hwx] }
    exact Fintype.card_congr e
  · let e : H.neighborSet v ≃ G.neighborSet v.1 :=
      { toFun := fun w =>
          ⟨w.1.1, by
            rcases w.2.2 with h1 | ⟨h2, _⟩ | ⟨_, h3⟩
            · exact h1
            · exact False.elim (hvx h2)
            · exact False.elim (hvy h3)⟩
        invFun := fun w =>
          ⟨⟨w.1, fun h => hvy (h ▸ w.2)⟩,
           ⟨fun h => G.ne_of_adj w.2 (congrArg Subtype.val h), Or.inl w.2⟩⟩
        left_inv := by intro ⟨⟨w, hwy⟩, _⟩; rfl
        right_inv := by intro ⟨w, _⟩; rfl }
    exact Fintype.card_congr e

/-- For a common neighbor `z` of `x` and `y`, `identGraph` drops its degree by exactly 1. -/
theorem ident_degree_common {x y z : V} (hxy : x ≠ y)
    (hxz : G.Adj x z) (hyz : G.Adj y z)
    [DecidableRel (identGraph G x y).Adj] :
    (identGraph G x y).degree ⟨z, (G.ne_of_adj hyz).symm⟩ + 1 = G.degree z := by
  let H := identGraph G x y
  let zv : {v : V // v ≠ y} := ⟨z, (G.ne_of_adj hyz).symm⟩
  have hzx : z ≠ x := (G.ne_of_adj hxz).symm
  change H.degree zv + 1 = G.degree z
  let e : H.neighborSet zv ≃ ↥((G.neighborFinset z).erase y) :=
    { toFun := fun w =>
        ⟨w.1.1, Finset.mem_erase.mpr ⟨w.1.2, (G.mem_neighborFinset z w.1.1).mpr (by
          rcases w.2.2 with h1 | ⟨h2, _⟩ | ⟨h3, _⟩
          · exact h1
          · exact False.elim (hzx h2)
          · exact h3 ▸ hxz.symm)⟩⟩
      invFun := fun w =>
        ⟨⟨w.1, (Finset.mem_erase.mp w.2).1⟩,
         ⟨fun h => G.ne_of_adj ((G.mem_neighborFinset z w.1).mp (Finset.mem_erase.mp w.2).2)
            (congrArg Subtype.val h),
          Or.inl ((G.mem_neighborFinset z w.1).mp (Finset.mem_erase.mp w.2).2)⟩⟩
      left_inv := by intro ⟨⟨w, _⟩, _⟩; rfl
      right_inv := by intro ⟨w, _⟩; rfl }
  have hc := Fintype.card_congr e
  rw [SimpleGraph.card_neighborSet_eq_degree, Fintype.card_coe] at hc
  rw [hc, Finset.card_erase_add_one ((G.mem_neighborFinset z y).mpr hyz.symm),
    SimpleGraph.card_neighborFinset_eq_degree]

/-- Degree of the merged vertex `u = ⟨x, hxy⟩` when `N(x) ∩ N(y) = ∅`. -/
theorem ident_degree_merged_ge_add {x y : V} (hxy : x ≠ y) (hnadj : ¬G.Adj x y)
    (hdisj : ∀ z, ¬(G.Adj x z ∧ G.Adj y z))
    [DecidableRel (identGraph G x y).Adj] :
    (identGraph G x y).degree ⟨x, hxy⟩ = G.degree x + G.degree y := by
  let H := identGraph G x y
  let u : {v : V // v ≠ y} := ⟨x, hxy⟩
  change H.degree u = G.degree x + G.degree y
  let e : H.neighborSet u ≃ G.neighborSet x ⊕ G.neighborSet y :=
    { toFun := fun w =>
        if h : G.Adj x w.1.1 then Sum.inl ⟨w.1.1, h⟩
        else Sum.inr ⟨w.1.1, by
          rcases w.2.2 with h1 | ⟨_, h2⟩ | ⟨h3, _⟩
          · exact False.elim (h h1)
          · exact h2
          · exact False.elim (w.2.1 (Subtype.ext h3.symm))⟩
      invFun := Sum.elim
        (fun w => ⟨⟨w.1, fun h => hnadj (h ▸ w.2)⟩,
          ⟨fun h => G.ne_of_adj w.2 (congrArg Subtype.val h), Or.inl w.2⟩⟩)
        (fun w => ⟨⟨w.1, (G.ne_of_adj w.2).symm⟩,
          ⟨fun h => hnadj (by rw [← congrArg Subtype.val h]; exact w.2.symm),
           Or.inr (Or.inl ⟨rfl, w.2⟩)⟩⟩)
      left_inv := by
        intro ⟨⟨w, hwy⟩, hw⟩
        by_cases h : G.Adj x w
        · simp [h]
        · simp [h]
      right_inv := by
        rintro (⟨w, hw⟩ | ⟨w, hw⟩)
        · simp [hw]
        · have hnx : ¬G.Adj x w := fun h => hdisj w ⟨h, hw⟩
          simp [hnx] }
  have hc := Fintype.card_congr e
  rw [SimpleGraph.card_neighborSet_eq_degree, Fintype.card_sum,
    SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.card_neighborSet_eq_degree] at hc
  exact hc

/-- Lower bound on the degree of the merged vertex `u = ⟨x, hxy⟩` when `¬G.Adj x y`. -/
theorem ident_degree_merged_ge_left {x y : V} (hxy : x ≠ y) (hnadj : ¬G.Adj x y)
    [DecidableRel (identGraph G x y).Adj] :
    G.degree x ≤ (identGraph G x y).degree ⟨x, hxy⟩ := by
  let H := identGraph G x y
  let u : {v : V // v ≠ y} := ⟨x, hxy⟩
  change G.degree x ≤ H.degree u
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
  let f : G.neighborSet x → H.neighborSet u := fun w =>
    ⟨⟨w.1, fun h => hnadj (h ▸ w.2)⟩,
     ⟨fun h => G.ne_of_adj w.2 (congrArg Subtype.val h), Or.inl w.2⟩⟩
  have hinj : Function.Injective f := by
    intro a b h
    exact Subtype.ext (congrArg (fun t => t.1.1) h)
  exact Fintype.card_le_of_injective f hinj

end IdentDegrees

/-! ### Main Structural Theorems -/

/-- **Theorem 1 (Universal Dyadic Path Theorem)**: In any `MinimalBad G` (`C`, `S`, or `H`),
    every pair $x \neq y$ with $\operatorname{dist}_G(x, y) \ge 3$ has a simple $x$–$y$ path
    of length $2^k$ ($k \ge 2$). -/
theorem universal_dyadic_path {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {x y : V} (hxy : x ≠ y) (hnadj : ¬G.Adj x y)
    (hdisj : ∀ z, ¬(G.Adj x z ∧ G.Adj y z)) :
    HasDyadicPath G x y := by
  classical
  let W := {v : V // v ≠ y}
  let H := identGraph G x y
  let _ : DecidableRel H.Adj := Classical.decRel _
  have hlt : Fintype.card W < Fintype.card V := ident_card_lt y
  have hux : H.degree ⟨x, hxy⟩ = G.degree x + G.degree y :=
    ident_degree_merged_ge_add G hxy hnadj hdisj
  have hdx : 2 ≤ G.degree x := no_small_defect G hm x
  have hdy : 2 ≤ G.degree y := no_small_defect G hm y
  have hu3 : 3 ≤ H.degree ⟨x, hxy⟩ := by omega
  obtain ⟨_, r, hr⟩ := hm.1
  have hnear : Near H := by
    refine ⟨⟨⟨x, hxy⟩, hu3⟩, ?_⟩
    by_cases hry : r = y
    · refine ⟨⟨x, hxy⟩, fun v hv => ?_⟩
      have hvx : v.1 ≠ x := fun h => hv (Subtype.ext h)
      have hdeg := ident_degree_non_common G hxy v hvx (fun hc => hdisj v.1 ⟨hc.1.symm, hc.2.symm⟩)
      change H.degree v = G.degree v.1 at hdeg
      rw [hdeg]
      exact hr v.1 (hry ▸ v.2)
    · refine ⟨⟨r, hry⟩, fun v hv => ?_⟩
      by_cases hvx : v.1 = x
      · have : v = ⟨x, hxy⟩ := Subtype.ext hvx
        rw [this]; exact hu3
      · have hdeg := ident_degree_non_common G hxy v hvx (fun hc => hdisj v.1 ⟨hc.1.symm, hc.2.symm⟩)
        change H.degree v = G.degree v.1 at hdeg
        rw [hdeg]
        exact hr v.1 (fun h => hv (Subtype.ext h))
  obtain ⟨k, a, c, hk, hc, hlen⟩ := hm.2.2.1 W H hlt hnear
  obtain ⟨p, hp, hplen, _⟩ := ident_cycle_lifts G hxy hm.2.1 hk c hc hlen
  exact ⟨k, p, hk, hp, hplen⟩

/-- **Theorem 2 (Unified Bipartite Exclusion)**: No `MinimalBad G` graph is bipartite
    (6-line unified proof of `C-B`, `S-B`, and all `H-B-*` leaves via `universal_dyadic_path`). -/
theorem unified_bipartite_exclusion {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (hB : Bip G) : False := by
  classical
  obtain ⟨color, hproper⟩ := hB
  have hwalk_parity : ∀ {a b : V} (p : G.Walk a b),
      (color a = color b ↔ Even p.length) := by
    intro a b p
    induction p with
    | nil => simp
    | @cons u v w huv rest ih =>
      have hc : color u ≠ color v := hproper u v huv
      simp only [Walk.length_cons, Nat.even_add_one]
      cases hcu : color u <;> cases hcv : color v <;> cases hcw : color w <;> simp_all
  have hcomplete : ∀ x y : V, color x ≠ color y → G.Adj x y := by
    intro x y hcol
    by_contra hnadj
    have hxy : x ≠ y := fun h => hcol (by rw [h])
    have hdisj : ∀ z, ¬(G.Adj x z ∧ G.Adj y z) := by
      rintro z ⟨hxz, hyz⟩
      have h1 := hproper x z hxz
      have h2 := hproper y z hyz
      cases hcx : color x <;> cases hcy : color y <;> cases hcz : color z <;> simp_all
    obtain ⟨k, p, hk, _, hplen⟩ := universal_dyadic_path G hm hxy hnadj hdisj
    have heven : Even p.length := by
      rw [hplen]
      have hk1 : 1 ≤ k := by omega
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk1
      refine ⟨2 ^ m, ?_⟩
      ring
    exact hcol ((hwalk_parity p).mpr heven)
  obtain ⟨⟨v, hv3⟩, _⟩ := hm.1
  have hcard_nv : 3 ≤ (G.neighborFinset v).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hv3
  obtain ⟨b₁, hb₁, b₂, hb₂, hbne⟩ :
      ∃ b₁ ∈ G.neighborFinset v, ∃ b₂ ∈ G.neighborFinset v, b₁ ≠ b₂ := by
    obtain ⟨b₁, hb₁⟩ := Finset.card_pos.mp (by omega : 0 < (G.neighborFinset v).card)
    have hpos2 : 0 < ((G.neighborFinset v).erase b₁).card := by
      rw [Finset.card_erase_of_mem hb₁]; omega
    obtain ⟨b₂, hb₂⟩ := Finset.card_pos.mp hpos2
    exact ⟨b₁, hb₁, b₂, (Finset.mem_erase.mp hb₂).2, (Finset.mem_erase.mp hb₂).1.symm⟩
  have hvb₁ : G.Adj v b₁ := (G.mem_neighborFinset v b₁).mp hb₁
  have hvb₂ : G.Adj v b₂ := (G.mem_neighborFinset v b₂).mp hb₂
  have hb₁2 : 2 ≤ (G.neighborFinset b₁).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; exact no_small_defect G hm b₁
  have hpos_a : 0 < ((G.neighborFinset b₁).erase v).card := by
    rw [Finset.card_erase_of_mem ((G.mem_neighborFinset b₁ v).mpr hvb₁.symm)]; omega
  obtain ⟨a₂, ha₂⟩ := Finset.card_pos.mp hpos_a
  have ha₂_ne_v : a₂ ≠ v := (Finset.mem_erase.mp ha₂).1
  have hb₁a₂ : G.Adj b₁ a₂ := (G.mem_neighborFinset b₁ a₂).mp (Finset.mem_erase.mp ha₂).2
  have hcol_a₂_b₂ : color a₂ ≠ color b₂ := by
    have h1 := hproper v b₁ hvb₁
    have h2 := hproper v b₂ hvb₂
    have h3 := hproper b₁ a₂ hb₁a₂
    cases hcv : color v <;> cases hcb₁ : color b₁ <;> cases hcb₂ : color b₂ <;>
      cases hca₂ : color a₂ <;> simp_all
  have ha₂b₂ : G.Adj a₂ b₂ := hcomplete a₂ b₂ hcol_a₂_b₂
  exact minimal_bad_no_c4 G hm hvb₁ hb₁a₂ ha₂b₂ hvb₂.symm ha₂_ne_v.symm hbne

/-- **Theorem 3 (NEW — Distance-2 Dyadic Path Theorem for Cubic `MinimalBad`)**:
    In any cubic `MinimalBad G` (covering all 5 open cubic leaves `C-N-R, C-N-2, C-N-3, C-T-2, C-T-3`),
    for any non-adjacent $x, y$ with common neighbor $z$, $G - z$ contains a simple $x$–$y$ path
    of length $2^k$ ($k \ge 2$). -/
theorem cubic_dist2_dyadic_path {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (hC : Cubic G) {x y z : V} (hxy : x ≠ y) (hnadj : ¬G.Adj x y)
    (hxz : G.Adj x z) (hyz : G.Adj y z) :
    HasDyadicPathAvoiding G x y z := by
  classical
  let W := {v : V // v ≠ y}
  let H := identGraph G x y
  let _ : DecidableRel H.Adj := Classical.decRel _
  have hlt : Fintype.card W < Fintype.card V := ident_card_lt y
  have hzy : z ≠ y := (G.ne_of_adj hyz).symm
  have hzx : z ≠ x := (G.ne_of_adj hxz).symm
  have hu3 : 3 ≤ H.degree ⟨x, hxy⟩ := by
    have hle := ident_degree_merged_ge_left G hxy hnadj
    change G.degree x ≤ H.degree ⟨x, hxy⟩ at hle
    rw [hC x] at hle
    exact hle
  have hz2 : H.degree ⟨z, hzy⟩ = 2 := by
    have hd := ident_degree_common G hxy hxz hyz
    change H.degree ⟨z, hzy⟩ + 1 = G.degree z at hd
    rw [hC z] at hd
    omega
  have hnear : Near H := by
    refine ⟨⟨⟨x, hxy⟩, hu3⟩, ⟨⟨z, hzy⟩, fun v hv => ?_⟩⟩
    by_cases hvx : v.1 = x
    · have : v = ⟨x, hxy⟩ := Subtype.ext hvx
      rw [this]; exact hu3
    · have hvz : v.1 ≠ z := fun h => hv (Subtype.ext h)
      have hnc : ¬(G.Adj v.1 x ∧ G.Adj v.1 y) := by
        rintro ⟨h1, h2⟩
        exact hvz (unique_common_neighbor G hm hxy h1.symm h2.symm hxz hyz)
      have hd := ident_degree_non_common G hxy v hvx hnc
      change H.degree v = G.degree v.1 at hd
      rw [hd, hC v.1]
  obtain ⟨k, a, c, hk, hc, hlen⟩ := hm.2.2.1 W H hlt hnear
  obtain ⟨p, hp, hplen, havoid⟩ := ident_cycle_lifts G hxy hm.2.1 hk c hc hlen
  refine ⟨k, p, hk, hp, hplen, havoid z hzy hxz hyz ?_⟩
  intro w₁ w₂ hw₁ hw₂ hw₁u hw₂u
  have hzu : H.Adj ⟨z, hzy⟩ ⟨x, hxy⟩ := ⟨fun h => hzx (congrArg Subtype.val h), Or.inl hxz.symm⟩
  have hcard : (H.neighborFinset ⟨z, hzy⟩).card = 2 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hz2
  have hu_in : (⟨x, hxy⟩ : W) ∈ H.neighborFinset ⟨z, hzy⟩ :=
    (H.mem_neighborFinset _ _).mpr hzu
  have herase : ((H.neighborFinset ⟨z, hzy⟩).erase ⟨x, hxy⟩).card = 1 := by
    rw [Finset.card_erase_of_mem hu_in, hcard]
  obtain ⟨w0, hw0⟩ := Finset.card_eq_one.mp herase
  have h1 : w₁ ∈ ({w0} : Finset W) := by
    rw [← hw0]; exact Finset.mem_erase.mpr ⟨hw₁u, (H.mem_neighborFinset _ _).mpr hw₁⟩
  have h2 : w₂ ∈ ({w0} : Finset W) := by
    rw [← hw0]; exact Finset.mem_erase.mpr ⟨hw₂u, (H.mem_neighborFinset _ _).mpr hw₂⟩
  simp only [Finset.mem_singleton] at h1 h2
  exact h1.trans h2.symm

/-- **Theorem 4 (NEW — Complete Non-Adjacent Dyadic Path Theorem for Cubic `MinimalBad`)**:
    In any cubic `MinimalBad G`, EVERY pair of non-adjacent distinct vertices has a simple
    $x$–$y$ path of length $2^k$ ($k \ge 2$). -/
theorem cubic_all_nonadj_dyadic_path {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (hC : Cubic G) {x y : V} (hxy : x ≠ y) (hnadj : ¬G.Adj x y) :
    HasDyadicPath G x y := by
  by_cases hcom : ∃ z, G.Adj x z ∧ G.Adj y z
  · obtain ⟨z, hxz, hyz⟩ := hcom
    obtain ⟨k, p, hk, hp, hplen, _⟩ := cubic_dist2_dyadic_path G hm hC hxy hnadj hxz hyz
    exact ⟨k, p, hk, hp, hplen⟩
  · push Not at hcom
    exact universal_dyadic_path G hm hxy hnadj (fun z ⟨h1, h2⟩ => hcom z h1 h2)

/-- **Theorem 5 (NEW — Induced $P_3$ $(2^k + 2)$-Cycle Theorem)**:
    In any cubic `MinimalBad G`, every induced $P_3$ ($x - z - y$ with $\neg G.\text{Adj}\ x\ y$)
    lies on a simple cycle of length $2^k + 2$ ($k \ge 2$). -/
theorem cubic_p3_dyadic_plus_two_cycle {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (hC : Cubic G) {x y z : V} (hxy : x ≠ y) (hnadj : ¬G.Adj x y)
    (hxz : G.Adj x z) (hyz : G.Adj y z) :
    ∃ (k : ℕ) (c : G.Walk z z), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k + 2 := by
  obtain ⟨k, p, hk, hp, hplen, hznot⟩ := cubic_dist2_dyadic_path G hm hC hxy hnadj hxz hyz
  let c : G.Walk z z := Walk.cons hxz.symm (p.concat hyz)
  have h4 : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hclen : c.length = 2 ^ k + 2 := by simp [c, hplen]
  have hctail : c.support.tail.Nodup := by
    rw [Walk.support_cons, List.tail_cons, Walk.support_concat, List.nodup_append]
    exact ⟨hp.support_nodup, List.nodup_singleton z, fun v hv w hw heq => by
      rw [List.mem_singleton] at hw; subst hw; subst heq; exact hznot hv⟩
  exact ⟨k, c, hk, isCycle_of_support_tail_nodup G c (by omega) hctail, hclen⟩

/-- **Theorem 6 (NEW — Defect Distance-2 Dyadic Path Theorem for `S` and `H`)**:
    In any one-defect `MinimalBad G` with degree-2 defect $w$ and distinct neighbors $b_1, b_2$,
    for every $v \in N(b_1) \setminus \{w, b_2\}$, $G - \{w, b_1\}$ contains a simple $b_2$–$v$
    path of length $2^k - 1$ ($k \ge 2$). -/
theorem defect_dist2_dyadic_path {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {w b₁ b₂ v : V} (hw : G.degree w = 2)
    (hwb₁ : G.Adj w b₁) (hwb₂ : G.Adj w b₂) (hbne : b₁ ≠ b₂)
    (hb₁v : G.Adj b₁ v) (hvw : v ≠ w) (hvb₂ : v ≠ b₂) :
    ∃ (k : ℕ) (p : G.Walk b₂ v), 2 ≤ k ∧ p.IsPath ∧ p.length + 1 = 2 ^ k ∧
      w ∉ p.support ∧ b₁ ∉ p.support := by
  classical
  have hb₁_deg : G.degree b₁ = 3 := defect_neighbor_cubic G hm hw hwb₁
  have hnwv : ¬G.Adj w v := by
    intro hwv
    have hcard : (G.neighborFinset w).card = 2 := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hw
    have hsub : ({b₁, b₂} : Finset V) ⊆ G.neighborFinset w := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx
      · rw [hx]; exact (G.mem_neighborFinset w b₁).mpr hwb₁
      · rw [hx]; exact (G.mem_neighborFinset w b₂).mpr hwb₂
    have heq : ({b₁, b₂} : Finset V) = G.neighborFinset w :=
      Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hbne, hcard])
    have hv_in : v ∈ ({b₁, b₂} : Finset V) := heq ▸ (G.mem_neighborFinset w v).mpr hwv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv_in
    rcases hv_in with hv1 | hv2
    · rw [hv1] at hb₁v; exact G.loopless.irrefl b₁ hb₁v
    · exact hvb₂ hv2
  let W := {x : V // x ≠ v}
  let H := identGraph G w v
  let _ : DecidableRel H.Adj := Classical.decRel _
  have hlt : Fintype.card W < Fintype.card V := ident_card_lt v
  have hvb₁_ne : b₁ ≠ v := G.ne_of_adj hb₁v
  have hwb₁_ne : b₁ ≠ w := (G.ne_of_adj hwb₁).symm
  obtain ⟨_, r, hr⟩ := hm.1
  have hrw : r = w := by
    by_contra h; have := hr w (Ne.symm h); omega
  subst r
  have hv3 : 3 ≤ G.degree v := hr v hvw
  have hu3 : 3 ≤ H.degree ⟨w, hvw.symm⟩ := by
    have hle : G.degree v ≤ H.degree ⟨w, hvw.symm⟩ := by
      rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
      let f : G.neighborSet v → H.neighborSet ⟨w, hvw.symm⟩ := fun z =>
        ⟨⟨z.1, (G.ne_of_adj z.2).symm⟩,
         ⟨fun h => hnwv (by rw [congrArg Subtype.val h]; exact z.2.symm),
          Or.inr (Or.inl ⟨rfl, z.2⟩)⟩⟩
      have hinj : Function.Injective f := fun a b h =>
        Subtype.ext (congrArg (fun t => t.1.1) h)
      exact Fintype.card_le_of_injective f hinj
    omega
  have hb₁2 : H.degree ⟨b₁, hvb₁_ne⟩ = 2 := by
    have hd := ident_degree_common G hvw.symm hwb₁ hb₁v.symm
    change H.degree ⟨b₁, hvb₁_ne⟩ + 1 = G.degree b₁ at hd
    rw [hb₁_deg] at hd
    omega
  have hnear : Near H := by
    refine ⟨⟨⟨w, hvw.symm⟩, hu3⟩, ⟨⟨b₁, hvb₁_ne⟩, fun z hz => ?_⟩⟩
    by_cases hzw : z.1 = w
    · have : z = ⟨w, hvw.symm⟩ := Subtype.ext hzw
      rw [this]; exact hu3
    · have hzb₁ : z.1 ≠ b₁ := fun h => hz (Subtype.ext h)
      have hnc : ¬(G.Adj z.1 w ∧ G.Adj z.1 v) := by
        rintro ⟨h1, h2⟩
        exact hzb₁ (unique_common_neighbor G hm hvw.symm h1.symm h2.symm hwb₁ hb₁v.symm)
      have hd := ident_degree_non_common G hvw.symm z hzw hnc
      change H.degree z = G.degree z.1 at hd
      rw [hd]
      exact hr z.1 hzw
  obtain ⟨k, a, c, hk, hc, hlen⟩ := hm.2.2.1 W H hlt hnear
  obtain ⟨p, hp, hplen, havoid⟩ := ident_cycle_lifts G hvw.symm hm.2.1 hk c hc hlen
  have hb₁_not_p : b₁ ∉ p.support := by
    apply havoid b₁ hvb₁_ne hwb₁ hb₁v.symm
    intro w₁ w₂ hw₁ hw₂ hw₁u hw₂u
    have hzu : H.Adj ⟨b₁, hvb₁_ne⟩ ⟨w, hvw.symm⟩ :=
      ⟨fun h => hwb₁_ne (congrArg Subtype.val h), Or.inl hwb₁.symm⟩
    have hcard : (H.neighborFinset ⟨b₁, hvb₁_ne⟩).card = 2 := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hb₁2
    have hu_in : (⟨w, hvw.symm⟩ : W) ∈ H.neighborFinset ⟨b₁, hvb₁_ne⟩ :=
      (H.mem_neighborFinset _ _).mpr hzu
    have herase : ((H.neighborFinset ⟨b₁, hvb₁_ne⟩).erase ⟨w, hvw.symm⟩).card = 1 := by
      rw [Finset.card_erase_of_mem hu_in, hcard]
    obtain ⟨w0, hw0⟩ := Finset.card_eq_one.mp herase
    have h1 : w₁ ∈ ({w0} : Finset W) := by
      rw [← hw0]; exact Finset.mem_erase.mpr ⟨hw₁u, (H.mem_neighborFinset _ _).mpr hw₁⟩
    have h2 : w₂ ∈ ({w0} : Finset W) := by
      rw [← hw0]; exact Finset.mem_erase.mpr ⟨hw₂u, (H.mem_neighborFinset _ _).mpr hw₂⟩
    simp only [Finset.mem_singleton] at h1 h2
    exact h1.trans h2.symm
  cases hpe : p with
  | nil => exact False.elim (hvw rfl)
  | @cons _ next _ hwn rest =>
    have hnext : next = b₂ := by
      have hcard : (G.neighborFinset w).card = 2 := by
        rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hw
      have hsub : ({b₁, b₂} : Finset V) ⊆ G.neighborFinset w := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hx | hx
        · rw [hx]; exact (G.mem_neighborFinset w b₁).mpr hwb₁
        · rw [hx]; exact (G.mem_neighborFinset w b₂).mpr hwb₂
      have heq : ({b₁, b₂} : Finset V) = G.neighborFinset w :=
        Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hbne, hcard])
      have hn_in : next ∈ ({b₁, b₂} : Finset V) := heq ▸ (G.mem_neighborFinset w next).mpr hwn
      simp only [Finset.mem_insert, Finset.mem_singleton] at hn_in
      rcases hn_in with hn1 | hn2
      · rw [hn1] at hpe
        exact False.elim (hb₁_not_p (by rw [hpe, Walk.support_cons]; exact List.mem_cons_of_mem _ (Walk.start_mem_support _)))
      · exact hn2
    subst hnext
    have hnodup : (w :: rest.support).Nodup := by
      simpa [hpe, Walk.support_cons] using hp.support_nodup
    rw [List.nodup_cons] at hnodup
    have hb₁_not_rest : b₁ ∉ rest.support := fun hm =>
      hb₁_not_p (by rw [hpe, Walk.support_cons]; exact List.mem_cons_of_mem _ hm)
    refine ⟨k, rest, hk, Walk.IsPath.mk' hnodup.2, ?_, hnodup.1, hb₁_not_rest⟩
    simp [hpe] at hplen
    omega

#print axioms minimal_bad_no_c4
#print axioms unique_common_neighbor
#print axioms minimal_bad_no_high_adj
#print axioms universal_dyadic_path
#print axioms unified_bipartite_exclusion
#print axioms cubic_dist2_dyadic_path
#print axioms cubic_all_nonadj_dyadic_path
#print axioms cubic_p3_dyadic_plus_two_cycle
#print axioms defect_dist2_dyadic_path
end E64Wave2Structural
