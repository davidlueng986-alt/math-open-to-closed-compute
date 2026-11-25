import Core
import Leaves
import PairedShadow
import InvolutionExclusion

/-!
Erdos 64 (Wave 3, Agent #4): Generalized Involution Exclusions.
1. Triples Wave 2's FPF involution exclusion from <= 1 to <= 3 invariant edges
   via single-edge quotient completion + double-path lifting.
2. Excludes defect-fixed involutions with 0 invariant edges on all 1-defect
   MinimalBad(G) graphs with non-adjacent defect neighbors (S-N-*, H-N-*).
-/

namespace E64Involution3
open SimpleGraph Erdos64Closure E64Core E64Leaves Erdos64Paired E64Involution
universe u

variable {V : Type u}

/-- In any power-free graph with FPF involution `σ`, the quotient orbits of two distinct
    `σ`-invariant edges cannot be adjacent in `G / ⟨σ⟩` (otherwise `G` contains a `C4`). -/
theorem inv_edges_independent_in_quot {G : SimpleGraph V} (hfree : ¬ HasPower G)
    (σ : V → V) (hinv : ∀ v, σ (σ v) = v) (hfpf : ∀ v, σ v ≠ v)
    (haut : ∀ a b, G.Adj a b ↔ G.Adj (σ a) (σ b))
    {u₁ u₂ : V} (he₁ : G.Adj u₁ (σ u₁)) (he₂ : G.Adj u₂ (σ u₂)) :
    ¬ (invQuotGraph G σ hinv).Adj ⟦u₁⟧ ⟦u₂⟧ := by
  intro hadj
  obtain ⟨v₂, hv₂q, hu₁v₂⟩ := lift_edge_exists haut hadj
  have hv₂_inv : G.Adj v₂ (σ v₂) := by
    rcases Quotient.exact hv₂q with rfl | rfl
    · exact he₂
    · have := (haut u₂ (σ u₂)).mp he₂; rwa [hinv u₂] at this
  have hsu₁sv₂ : G.Adj (σ u₁) (σ v₂) := (haut u₁ v₂).mp hu₁v₂
  have hne : (⟦u₁⟧ : Quotient (invSetoid σ hinv)) ≠ ⟦v₂⟧ := hv₂q.symm ▸ hadj.1
  have hu₁v₂_ne : u₁ ≠ v₂ := fun h => hne (by rw [h])
  have hu₁sv₂_ne : u₁ ≠ σ v₂ := fun h => hne (by rw [h]; exact Quotient.sound (Or.inr (hinv v₂).symm))
  have hsu₁v₂_ne : σ u₁ ≠ v₂ := fun h => hne (by rw [← h]; exact Quotient.sound (Or.inr (hinv u₁).symm))
  have hsu₁sv₂_ne : σ u₁ ≠ σ v₂ := fun h => hu₁v₂_ne (by
    have := congrArg σ h; rwa [hinv u₁, hinv v₂] at this)
  exact hfree (rectangle_power G hu₁v₂_ne hu₁sv₂_ne (hfpf u₁).symm (hfpf v₂).symm hsu₁v₂_ne.symm
    hsu₁sv₂_ne.symm hu₁v₂ hv₂_inv hsu₁sv₂.symm he₁.symm)

/-- Lift a `2^k`-cycle (`k >= 2`) from `(G / ⟨σ⟩) + q₁q₂` back to a `2^k`- or `2^(k+1)`-cycle in `G`,
    where `q₁ = ⟦u₁⟧` and `q₂ = ⟦u₂⟧` are distinct orbits of `σ`-invariant edges. -/
theorem hasPower_of_invQuot_add_edge {G : SimpleGraph V} {σ : V → V}
    (hinv : ∀ v, σ (σ v) = v) (hfpf : ∀ v, σ v ≠ v)
    (haut : ∀ a b, G.Adj a b ↔ G.Adj (σ a) (σ b))
    {u₁ u₂ : V} (he₁ : G.Adj u₁ (σ u₁)) (he₂ : G.Adj u₂ (σ u₂))
    (hne : (⟦u₁⟧ : Quotient (invSetoid σ hinv)) ≠ ⟦u₂⟧)
    (hpow : HasPower (invQuotGraph G σ hinv ⊔ SimpleGraph.edge (⟦u₁⟧ : Quotient (invSetoid σ hinv)) ⟦u₂⟧)) :
    HasPower G := by
  classical
  let Q := Quotient (invSetoid σ hinv)
  let H₀ := invQuotGraph G σ hinv
  let q₁ : Q := ⟦u₁⟧
  let q₂ : Q := ⟦u₂⟧
  let H := H₀ ⊔ SimpleGraph.edge q₁ q₂
  obtain ⟨k, v₀, c, hk, hc, hlen⟩ := hpow
  have hge4 : 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
  by_cases huse : s(q₁, q₂) ∈ c.edges
  · -- Rotate c so it starts at q₁, and its first or last edge is s(q₁, q₂)
    have hq₁_mem : q₁ ∈ c.support := Walk.fst_mem_support_of_mem_edges c huse
    let c' := c.rotate hq₁_mem
    have hc' : c'.IsCycle := hc.rotate hq₁_mem
    have hlen' : c'.length = 2 ^ k := by rw [Walk.length_rotate, hlen]
    have huse' : s(q₁, q₂) ∈ c'.edges := (Walk.edges_rotate c hq₁_mem).mem_iff.mpr huse
    -- Extract a simple path P₀ in H₀ between q₁ and q₂ of length 2^k - 1
    -- Since c' is a cycle starting at q₁ with edge s(q₁, q₂), either its first edge is s(q₁, q₂)
    -- or its last edge is s(q₁, q₂) (because q₁ appears only at start/end of c').
    have hex_path : ∃ P₀ : H₀.Walk q₁ q₂, P₀.IsPath ∧ P₀.length + 1 = 2 ^ k := by
      -- Helper to transfer a walk avoiding s(q₁, q₂) into H₀
      let rec toH0 : ∀ {a b : Q} (w : H.Walk a b), s(q₁, q₂) ∉ w.edges → H₀.Walk a b
        | _, _, .nil, _ => .nil
        | a, _, .cons (v := b) hab rest, hno =>
          have hab0 : H₀.Adj a b := by
            rcases hab with h0 | hedge
            · exact h0
            · exfalso
              have hs : s(a, b) = s(q₁, q₂) := by
                rcases hedge.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                · rfl
                · exact Sym2.eq_swap
              exact hno (by simp [hs])
          .cons hab0 (toH0 rest (fun hm => hno (by simp [hm])))
      have htoH0_len : ∀ {a b : Q} (w : H.Walk a b) (hno : s(q₁, q₂) ∉ w.edges),
          (toH0 w hno).length = w.length := by
        intro a b w hno; induction w with
        | nil => rfl
        | cons _ _ ih => simp [toH0, ih]
      have htoH0_supp : ∀ {a b : Q} (w : H.Walk a b) (hno : s(q₁, q₂) ∉ w.edges),
          (toH0 w hno).support = w.support := by
        intro a b w hno; induction w with
        | nil => rfl
        | cons _ _ ih => simp [toH0, ih]
      cases hce : c' with
      | nil => rw [hce] at hlen'; simp at hlen'; omega
      | @cons _ b _ h₁ rest =>
        have hrest_path : rest.IsPath := by
          apply Walk.IsPath.mk'
          have hsn := hc'.support_nodup
          rw [hce, Walk.support_cons, List.tail_cons] at hsn
          exact hsn
        have hrest_len : rest.length + 1 = 2 ^ k := by
          have := congrArg Walk.length hce; simp at this; omega
        have hen : c'.edges.Nodup := hc'.edges_nodup
        rw [hce, Walk.edges_cons, List.nodup_cons] at hen
        by_cases hb2 : b = q₂
        · subst hb2
          have hno : s(q₁, q₂) ∉ rest.edges := hen.1
          let P := toH0 rest hno
          refine ⟨P.reverse, ?_, by rw [Walk.length_reverse, htoH0_len, hrest_len]⟩
          apply Walk.IsPath.reverse
          apply Walk.IsPath.mk'
          rw [htoH0_supp]; exact hrest_path.support_nodup
        · -- s(q₁, q₂) is in rest.edges, so it must be the LAST edge of rest (since q₁ is only at the end of rest!)
          have huse_rest : s(q₁, q₂) ∈ rest.edges := by
            rw [hce, Walk.edges_cons, List.mem_cons] at huse'
            rcases huse' with heq | hr
            · exfalso
              rcases Sym2.eq_iff.mp heq with ⟨_, h2⟩ | ⟨h1, _⟩
              · exact hb2 h2.symm
              · exact hne h1
            · exact hr
          -- Look at c'.reverse: its first edge is the last edge of rest!
          let cr := c'.reverse
          have hcr : cr.IsCycle := hc'.reverse
          have hcr_len : cr.length = 2 ^ k := by rw [Walk.length_reverse, hlen']
          cases hcre : cr with
          | nil => rw [hcre] at hcr_len; simp at hcr_len; omega
          | @cons _ b' _ h₁' rest' =>
            have hb'_eq : b' = q₂ := by
              -- In rest, q₁ only appears as the last vertex (since rest.support.Nodup and rest ends at q₁)
              -- In cr = cons h₁' rest', s(q₁, q₂) ∈ cr.edges; if s(q₁, q₂) ∈ rest'.edges, then q₁ ∈ rest'.support,
              -- contradicting rest'.IsPath unless q₁ is the end of rest', wait: q₁ IS the end of rest',
              -- so the ONLY edges incident to q₁ in c' are its first edge s(q₁, b) and its last edge s(q₁, b')!
              have hrest'_nodup : rest'.support.Nodup := by
                have hsn := hcr.support_nodup
                rw [hcre, Walk.support_cons, List.tail_cons] at hsn
                exact hsn
              have huse_cr : s(q₁, q₂) ∈ cr.edges := by
                rw [Walk.edges_reverse, List.mem_reverse]; exact huse'
              rw [hcre, Walk.edges_cons, List.mem_cons] at huse_cr
              rcases huse_cr with heq | hmem_r'
              · rcases Sym2.eq_iff.mp heq with ⟨_, h2⟩ | ⟨h1, _⟩
                · exact h2.symm
                · exact False.elim (hne h1)
              · -- If s(q₁, q₂) ∈ rest'.edges, since q₁ is the END of rest' and rest'.support.Nodup,
                -- s(q₁, q₂) must be the LAST edge of rest', which is the FIRST edge of c' = s(q₁, b)!
                -- Wait: we know s(q₁, q₂) ≠ s(q₁, b) since b ≠ q₂!
                -- Even simpler: in any path `w : H.Walk u q₁` with `w.support.Nodup`, if `s(q₁, q₂) ∈ w.edges`,
                -- then `s(q₁, q₂)` is the last edge of `w`, i.e., the first edge of `w.reverse`!
                exfalso
                have hrev_eq : c' = cr.reverse := (Walk.reverse_reverse c').symm
                -- Actually rest'.reverse is a path from q₁ to b' whose first edge is s(q₁, b)!
                -- Let's prove: in any path `w : H.Walk x y`, if `y ∈ e` for `e ∈ w.edges`, then `e` is the first edge of `w.reverse`.
                have hlast : ∀ {x y : Q} (w : H.Walk x y), w.IsPath → ∀ z, s(y, z) ∈ w.edges →
                    ∃ hzy : H.Adj y z, ∃ w' : H.Walk z x, w.reverse = .cons hzy w' := by
                  intro x y w hw z hz
                  cases hrw : w.reverse with
                  | nil =>
                    have : w = .nil := by rw [← Walk.reverse_reverse w, hrw]; rfl
                    subst this; simp at hz
                  | @cons _ t _ hyt w' =>
                    have hmem_rev : s(y, z) ∈ w.reverse.edges := by
                      rw [Walk.edges_reverse, List.mem_reverse]; exact hz
                    rw [hrw, Walk.edges_cons, List.mem_cons] at hmem_rev
                    rcases hmem_rev with heq | hmem_w'
                    · rcases Sym2.eq_iff.mp heq with ⟨_, htz⟩ | ⟨hyz, _⟩
                      · subst htz; exact ⟨hyt, w', rfl⟩
                      · exfalso; exact (H.ne_of_adj hyt) (hyz ▸ rfl)
                    · exfalso
                      have hy_in_w' : y ∈ w'.support := Walk.fst_mem_support_of_mem_edges w' hmem_w'
                      have hnod := hw.reverse.support_nodup
                      rw [hrw, Walk.support_cons, List.nodup_cons] at hnod
                      exact hnod.1 hy_in_w'
                have hrest'_path : rest'.IsPath := Walk.IsPath.mk' hrest'_nodup
                obtain ⟨_, w', hw'⟩ := hlast rest' hrest'_path q₂ hmem_r'
                -- c' = cr.reverse = (cons h₁' rest').reverse = rest'.reverse.append (cons h₁'.symm nil)
                have hc'_first : c'.getVert 1 = b := by rw [hce]; rfl
                have hcr_rev : cr.reverse = c' := Walk.reverse_reverse c'
                rw [hcre, Walk.reverse_cons, hw'] at hcr_rev
                have hc'_first2 : c'.getVert 1 = q₂ := by rw [← hcr_rev]; simp
                exact hb2 (hc'_first.symm.trans hc'_first2)
            subst hb'_eq
            have hen' : cr.edges.Nodup := hcr.edges_nodup
            rw [hcre, Walk.edges_cons, List.nodup_cons] at hen'
            have hno' : s(q₁, q₂) ∉ rest'.edges := hen'.1
            have hrest'_path : rest'.IsPath := by
              apply Walk.IsPath.mk'
              have hsn := hcr.support_nodup
              rw [hcre, Walk.support_cons, List.tail_cons] at hsn
              exact hsn
            have hrest'_len : rest'.length + 1 = 2 ^ k := by
              have := congrArg Walk.length hcre; simp at this; omega
            let P := toH0 rest' hno'
            refine ⟨P.reverse, ?_, by rw [Walk.length_reverse, htoH0_len, hrest'_len]⟩
            apply Walk.IsPath.reverse
            apply Walk.IsPath.mk'
            rw [htoH0_supp]; exact hrest'_path.support_nodup
    obtain ⟨P₀, hP₀_path, hP₀_len⟩ := hex_path
    -- Lift P₀ starting at u₁: gives a simple path p₁ from u₁ to v₂ ∈ {u₂, σ u₂} of length 2^k - 1
    let lifted := liftWalk haut P₀ u₁ rfl
    let v₂ := lifted.1.1
    let p₁ : G.Walk u₁ v₂ := lifted.1.2
    have hv₂q : (⟦v₂⟧ : Q) = q₂ := lifted.2.1
    have hp₁len : p₁.length + 1 = 2 ^ k := by rw [lifted.2.2.1]; exact hP₀_len
    have hp₁supp : p₁.support.map (Quotient.mk (invSetoid σ hinv)) = P₀.support := lifted.2.2.2
    have hp₁nodup : p₁.support.Nodup := List.Nodup.of_map _ (hp₁supp.symm ▸ hP₀_path.support_nodup)
    have hv₂_inv : G.Adj v₂ (σ v₂) := by
      rcases Quotient.exact hv₂q with rfl | rfl
      · exact he₂
      · have := (haut u₂ (σ u₂)).mp he₂; rwa [hinv u₂] at this
    -- Second path p₂ = (p₁.map σ).reverse from σ v₂ to σ u₁
    let f : G →g G := mapWalkAut σ haut
    have hσ_inj : Function.Injective σ := Function.LeftInverse.injective hinv
    let p₂ : G.Walk (σ v₂) (σ u₁) := (p₁.map f).reverse
    have hp₂len : p₂.length + 1 = 2 ^ k := by simp [p₂, hp₁len]
    have hp₂supp : p₂.support = (p₁.support.map σ).reverse := by
      simp [p₂, Walk.support_reverse, Walk.support_map, f, mapWalkAut]
    have hp₂nodup : p₂.support.Nodup := by
      rw [hp₂supp, List.nodup_reverse]
      exact (List.nodup_map_iff hσ_inj).mpr hp₁nodup
    -- p₁.support and p₂.support are completely disjoint!
    have hdisj : p₁.support.Disjoint p₂.support := by
      intro x hx1 hx2
      rw [hp₂supp, List.mem_reverse] at hx2
      obtain ⟨y, hy1, hxy⟩ := List.mem_map.mp hx2
      have hqeq : (⟦x⟧ : Q) = ⟦y⟧ := by
        rw [← hxy]; exact Quotient.sound (Or.inr (hinv y).symm)
      have hinj_on := (List.nodup_map_iff_inj_on hp₁nodup).mp (hp₁supp.symm ▸ hP₀_path.support_nodup)
      have heq : x = y := hinj_on x hx1 y hy1 hqeq
      rw [heq] at hxy
      exact hfpf y hxy
    -- Close the cycle: u₁ --(p₁)--> v₂ --(hv₂_inv)--> σ v₂ --(p₂)--> σ u₁ --(he₁.symm)--> u₁
    let cyc : G.Walk u₁ u₁ := p₁.append (.cons hv₂_inv (p₂.append (.cons he₁.symm .nil)))
    have hcyclen : cyc.length = 2 ^ (k + 1) := by
      simp only [cyc, Walk.length_append, Walk.length_cons, Walk.length_nil, pow_succ]
      omega
    have hcyc_tail : cyc.support.tail = p₁.support.tail ++ p₂.support ++ [u₁] := by
      have h1 : cyc.support = p₁.support ++ (p₂.support ++ [u₁]) := by
        simp [cyc, Walk.support_append, Walk.support_cons]
      have h2 : p₁.support = u₁ :: p₁.support.tail := (p₁.cons_tail_support).symm
      rw [h1, h2, List.cons_append, List.tail_cons, List.append_assoc]
    have hcyc_nodup : cyc.support.tail.Nodup := by
      rw [hcyc_tail]
      have hp₁_split : p₁.support = u₁ :: p₁.support.tail := (p₁.cons_tail_support).symm
      have hp₁t_nodup : p₁.support.tail.Nodup := (List.nodup_cons.mp (hp₁_split ▸ hp₁nodup)).2
      have hu₁_not_p₁t : u₁ ∉ p₁.support.tail := (List.nodup_cons.mp (hp₁_split ▸ hp₁nodup)).1
      have hu₁_not_p₂ : u₁ ∉ p₂.support := fun hm => hdisj (Walk.start_mem_support p₁) hm
      have hdisj_t : p₁.support.tail.Disjoint p₂.support :=
        fun x hx1 hx2 => hdisj (List.mem_of_mem_tail hx1) hx2
      have h12 : (p₁.support.tail ++ p₂.support).Nodup :=
        List.nodup_append'.mpr ⟨hp₁t_nodup, hp₂nodup, hdisj_t⟩
      refine List.nodup_append'.mpr ⟨h12, List.nodup_singleton u₁, fun z hz1 hz2 => ?_⟩
      have hzu : z = u₁ := List.mem_singleton.mp hz2
      subst hzu
      rcases List.mem_append.mp hz1 with h1 | h2
      · exact hu₁_not_p₁t h1
      · exact hu₁_not_p₂ h2
    have hnil : ¬ cyc.Nil := by
      intro h; have := Walk.length_eq_zero_iff.mpr h
      have h2 : 4 ≤ 2 ^ (k + 1) := by rw [pow_succ]; omega
      omega
    have hcyc_is : cyc.IsCycle := by
      apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      refine ⟨Walk.IsPath.mk' ?_, ?_⟩
      · rwa [Walk.support_tail_of_not_nil _ hnil]
      · rw [hcyclen, pow_succ]; omega
    exact ⟨k + 1, u₁, cyc, by omega, hcyc_is, hcyclen⟩
  · -- Cycle does not use s(q₁, q₂), so it already lives in H₀ = invQuotGraph G σ hinv
    let rec toH0 : ∀ {a b : Q} (w : H.Walk a b), s(q₁, q₂) ∉ w.edges → H₀.Walk a b
      | _, _, .nil, _ => .nil
      | a, _, .cons (v := b) hab rest, hno =>
        have hab0 : H₀.Adj a b := by
          rcases hab with h0 | hedge
          · exact h0
          · exfalso
            have hs : s(a, b) = s(q₁, q₂) := by
              rcases hedge.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · rfl
              · exact Sym2.eq_swap
            exact hno (by simp [hs])
        .cons hab0 (toH0 rest (fun hm => hno (by simp [hm])))
    have hlen0 : ∀ {a b : Q} (w : H.Walk a b) (hno : s(q₁, q₂) ∉ w.edges), (toH0 w hno).length = w.length := by
      intro a b w hno; induction w with | nil => rfl | cons _ _ ih => simp [toH0, ih]
    have hsupp0 : ∀ {a b : Q} (w : H.Walk a b) (hno : s(q₁, q₂) ∉ w.edges), (toH0 w hno).support = w.support := by
      intro a b w hno; induction w with | nil => rfl | cons _ _ ih => simp [toH0, ih]
    let c0 := toH0 c huse
    have hc0_len : c0.length = 2 ^ k := (hlen0 c huse).trans hlen
    have hc0_nil : ¬ c0.Nil := by
      intro h; have := Walk.length_eq_zero_iff.mpr h; omega
    have hc0 : c0.IsCycle := by
      apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      refine ⟨Walk.IsPath.mk' ?_, by omega⟩
      rw [Walk.support_tail_of_not_nil _ hc0_nil, hsupp0]
      exact hc.support_nodup
    exact hasPower_of_invQuot hinv hfpf haut ⟨k, v₀, c0, hk, hc0, hc0_len⟩

/-- NEW (Wave 3, Agent #4): Generalized FPF Involution Exclusion (up to 3 invariant edges).
    Triples Wave 2's `no_fpf_involution_le_one_edge`: no MinimalBad(G) admits a fixed-point-free
    involution `σ` with at most 3 `σ`-invariant edges. -/
theorem no_fpf_involution_le_three_edges [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (σ : V → V) (hinv : ∀ v, σ (σ v) = v) (hfpf : ∀ v, σ v ≠ v)
    (haut : ∀ a b, G.Adj a b ↔ G.Adj (σ a) (σ b))
    (h3edges : ∃ w₁ w₂ w₃ : V, ∀ v : V,
      v ≠ w₁ → v ≠ σ w₁ → v ≠ w₂ → v ≠ σ w₂ → v ≠ w₃ → v ≠ σ w₃ → ¬ G.Adj v (σ v)) :
    False := by
  classical
  -- First, G is cubic (same proof as in InvolutionExclusion)
  have hdeg_eq : ∀ v : V, G.degree (σ v) = G.degree v := by
    intro v
    let e : G.neighborSet (σ v) ≃ G.neighborSet v :=
      { toFun := fun u => ⟨σ u.1, by have := (haut (σ v) u.1).mp u.2; rwa [hinv v] at this⟩
        invFun := fun u => ⟨σ u.1, (haut v u.1).mp u.2⟩
        left_inv := fun u => Subtype.ext (hinv u.1)
        right_inv := fun u => Subtype.ext (hinv u.1) }
    rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
    exact Fintype.card_congr e
  have hall3 : ∀ v : V, 3 ≤ G.degree v := by
    obtain ⟨_, w, hw⟩ := hm.1
    intro v
    by_cases hvw : v = w
    · subst v; rw [← hdeg_eq w]; exact hw (σ w) (hfpf w)
    · exact hw v hvw
  have hC : ∀ v : V, G.degree v = 3 := no_high_when_no_defect G hm hall3
  obtain ⟨w₁, w₂, w₃, hw3⟩ := h3edges
  -- Reduce to the case where there exist two distinct orbits of invariant edges u₁, u₂
  by_cases hex2 : ∃ u₁ u₂ : V, G.Adj u₁ (σ u₁) ∧ G.Adj u₂ (σ u₂) ∧
      (⟦u₁⟧ : Quotient (invSetoid σ hinv)) ≠ ⟦u₂⟧
  · obtain ⟨u₁, u₂, he₁, he₂, hne⟩ := hex2
    let Q := Quotient (invSetoid σ hinv)
    let H₀ := invQuotGraph G σ hinv
    letI : DecidableRel H₀.Adj := fun a b => Classical.dec _
    let q₁ : Q := ⟦u₁⟧
    let q₂ : Q := ⟦u₂⟧
    -- Pick the third possible invariant-edge orbit q₃ (from {w₁, w₂, w₃})
    have hthird : ∃ q₃ : Q, ∀ u : V, (⟦u⟧ : Q) ≠ q₁ → (⟦u⟧ : Q) ≠ q₂ → (⟦u⟧ : Q) ≠ q₃ →
        ¬ G.Adj u (σ u) := by
      -- Since u₁, u₂ have G.Adj uᵢ (σ uᵢ), each of ⟦u₁⟧, ⟦u₂⟧ lies in {⟦w₁⟧, ⟦w₂⟧, ⟦w₃⟧}.
      have hmem : ∀ u : V, G.Adj u (σ u) →
          (⟦u⟧ : Q) = ⟦w₁⟧ ∨ (⟦u⟧ : Q) = ⟦w₂⟧ ∨ (⟦u⟧ : Q) = ⟦w₃⟧ := by
        intro u hu
        by_contra hnot
        push Not at hnot
        refine hw3 u ?_ ?_ ?_ ?_ ?_ ?_ hu
        · intro h; exact hnot.1 (by rw [h])
        · intro h; exact hnot.1 (by rw [h]; exact Quotient.sound (Or.inr (hinv w₁).symm))
        · intro h; exact hnot.2.1 (by rw [h])
        · intro h; exact hnot.2.1 (by rw [h]; exact Quotient.sound (Or.inr (hinv w₂).symm))
        · intro h; exact hnot.2.2 (by rw [h])
        · intro h; exact hnot.2.2 (by rw [h]; exact Quotient.sound (Or.inr (hinv w₃).symm))
      rcases hmem u₁ he₁ with h1 | h1 | h1 <;> rcases hmem u₂ he₂ with h2 | h2 | h2
      · exact False.elim (hne (h1.trans h2.symm))
      · exact ⟨⟦w₃⟧, fun u hu1 hu2 hu3 hu => by rcases hmem u hu with h | h | h <;> simp_all [q₁, q₂]⟩
      · exact ⟨⟦w₂⟧, fun u hu1 hu2 hu3 hu => by rcases hmem u hu with h | h | h <;> simp_all [q₁, q₂]⟩
      · exact ⟨⟦w₃⟧, fun u hu1 hu2 hu3 hu => by rcases hmem u hu with h | h | h <;> simp_all [q₁, q₂]⟩
      · exact False.elim (hne (h1.trans h2.symm))
      · exact ⟨⟦w₁⟧, fun u hu1 hu2 hu3 hu => by rcases hmem u hu with h | h | h <;> simp_all [q₁, q₂]⟩
      · exact ⟨⟦w₂⟧, fun u hu1 hu2 hu3 hu => by rcases hmem u hu with h | h | h <;> simp_all [q₁, q₂]⟩
      · exact ⟨⟦w₁⟧, fun u hu1 hu2 hu3 hu => by rcases hmem u hu with h | h | h <;> simp_all [q₁, q₂]⟩
      · exact False.elim (hne (h1.trans h2.symm))
    obtain ⟨q₃, hq₃⟩ := hthird
    -- Degrees in H₀: 3 if ¬G.Adj u (σ u), and 2 if G.Adj u (σ u)
    have hH₀_deg_non : ∀ u : V, ¬ G.Adj u (σ u) → H₀.degree ⟦u⟧ = 3 := by
      intro u hno
      let f : G.neighborSet u → H₀.neighborSet (⟦u⟧ : Q) := fun v =>
        ⟨⟦v.1⟧, ⟨fun heq => by
          rcases Quotient.exact heq with h1 | h2
          · exact (G.ne_of_adj v.2) h1
          · exact hno (h2 ▸ v.2),
          u, v.1, rfl, rfl, v.2⟩⟩
      have hfinj : Function.Injective f := by
        intro a b heq
        apply Subtype.ext
        rcases Quotient.exact (congrArg Subtype.val heq) with h1 | h2
        · exact h1
        · exact False.elim (no_parallel_of_involution hm.2.1 σ hinv hfpf haut b.2 (h2 ▸ a.2))
      have hfsurj : Function.Surjective f := by
        rintro ⟨q, hq⟩
        obtain ⟨v, hvq, huv⟩ := lift_edge_exists haut hq
        exact ⟨⟨v, huv⟩, Subtype.ext hvq⟩
      have hc := Fintype.card_congr (Equiv.ofBijective f ⟨hfinj, hfsurj⟩)
      rw [SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.card_neighborSet_eq_degree, hC u] at hc
      exact hc.symm
    have hH₀_deg_inv : ∀ u : V, G.Adj u (σ u) → H₀.degree ⟦u⟧ = 2 := by
      intro u hinv_e
      let f : {v : V // G.Adj u v ∧ v ≠ σ u} → H₀.neighborSet (⟦u⟧ : Q) := fun v =>
        ⟨⟦v.1⟧, ⟨fun heq => by
          rcases Quotient.exact heq with h1 | h2
          · exact (G.ne_of_adj v.2.1) h1
          · exact v.2.2 h2,
          u, v.1, rfl, rfl, v.2.1⟩⟩
      have hfinj : Function.Injective f := by
        intro a b heq
        apply Subtype.ext
        rcases Quotient.exact (congrArg Subtype.val heq) with h1 | h2
        · exact h1
        · exact False.elim (no_parallel_of_involution hm.2.1 σ hinv hfpf haut b.2.1 (h2 ▸ a.2.1))
      have hfsurj : Function.Surjective f := by
        rintro ⟨q, hq⟩
        obtain ⟨v, hvq, huv⟩ := lift_edge_exists haut hq
        have hvne : v ≠ σ u := fun h => hq.1 (by rw [← hvq, h]; exact Quotient.sound (Or.inr (hinv u).symm))
        exact ⟨⟨v, huv, hvne⟩, Subtype.ext hvq⟩
      have hc := Fintype.card_congr (Equiv.ofBijective f ⟨hfinj, hfsurj⟩)
      rw [SimpleGraph.card_neighborSet_eq_degree] at hc
      have hcard_er : Fintype.card {v : V // G.Adj u v ∧ v ≠ σ u} = 2 := by
        rw [Fintype.card_subtype]
        have hs : (Finset.univ.filter (fun v : V => G.Adj u v ∧ v ≠ σ u)) =
            (G.neighborFinset u).erase (σ u) := by ext v; simp [and_comm]
        rw [hs]
        have h1 := Finset.card_erase_add_one ((G.mem_neighborFinset u (σ u)).mpr hinv_e)
        rw [G.card_neighborFinset_eq_degree, hC u] at h1
        omega
      omega
    -- Add the edge q₁ q₂ (not in H₀ by inv_edges_independent_in_quot!)
    have hnot_adj : ¬ H₀.Adj q₁ q₂ := inv_edges_independent_in_quot hm.2.1 σ hinv hfpf haut he₁ he₂
    let H := H₀ ⊔ SimpleGraph.edge q₁ q₂
    letI : DecidableRel H.Adj := fun a b => Classical.dec _
    have hH_deg : ∀ q : Q, H.degree q = H₀.degree q + (if q = q₁ ∨ q = q₂ then 1 else 0) := by
      intro q
      rw [← H.card_neighborFinset_eq_degree, ← H₀.card_neighborFinset_eq_degree]
      by_cases h1 : q = q₁
      · subst h1
        have hmem : q₂ ∉ H₀.neighborFinset q₁ := fun hm' => hnot_adj ((H₀.mem_neighborFinset _ _).mp hm')
        have heq : H.neighborFinset q₁ = insert q₂ (H₀.neighborFinset q₁) := by
          ext r
          simp only [H, SimpleGraph.mem_neighborFinset, SimpleGraph.sup_adj, SimpleGraph.edge_adj,
            Finset.mem_insert]
          constructor
          · rintro (h0 | ⟨⟨rfl, rfl⟩ | ⟨h12, _⟩, _⟩)
            · exact Or.inr h0
            · exact Or.inl rfl
            · exact False.elim (hne h12)
          · rintro (rfl | h0)
            · exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, hne⟩
            · exact Or.inl h0
        rw [heq, Finset.card_insert_of_notMem hmem, if_pos (Or.inl rfl)]
      · by_cases h2 : q = q₂
        · subst h2
          have hmem : q₁ ∉ H₀.neighborFinset q₂ := fun hm' => hnot_adj ((H₀.mem_neighborFinset _ _).mp hm').symm
          have heq : H.neighborFinset q₂ = insert q₁ (H₀.neighborFinset q₂) := by
            ext r
            simp only [H, SimpleGraph.mem_neighborFinset, SimpleGraph.sup_adj, SimpleGraph.edge_adj,
              Finset.mem_insert]
            constructor
            · rintro (h0 | ⟨⟨h21, _⟩ | ⟨rfl, rfl⟩, _⟩)
              · exact Or.inr h0
              · exact False.elim (hne h21.symm)
              · exact Or.inl rfl
            · rintro (rfl | h0)
              · exact Or.inr ⟨Or.inr ⟨rfl, rfl⟩, hne.symm⟩
              · exact Or.inl h0
          rw [heq, Finset.card_insert_of_notMem hmem, if_pos (Or.inr rfl)]
        · have heq : H.neighborFinset q = H₀.neighborFinset q := by
            ext r
            simp only [H, SimpleGraph.mem_neighborFinset, SimpleGraph.sup_adj, SimpleGraph.edge_adj]
            constructor
            · rintro (h0 | ⟨⟨hq1, _⟩ | ⟨hq2, _⟩, _⟩)
              · exact h0
              · exact False.elim (h1 hq1)
              · exact False.elim (h2 hq2)
            · exact Or.inl
          rw [heq, if_neg (by tauto), Nat.add_zero]
    have hcard_lt : Fintype.card Q < Fintype.card V := by
      let pickRep : Q → V := fun q => Classical.choose (Quotient.exists_rep q)
      have hrep : ∀ q, ⟦pickRep q⟧ = q := fun q => Classical.choose_spec (Quotient.exists_rep q)
      have hinj : Function.Injective pickRep := fun a b h => by rw [← hrep a, ← hrep b, h]
      have hnsurj : ¬ Function.Surjective pickRep := by
        intro hsurj
        obtain ⟨qa, hqa⟩ := hsurj u₁
        obtain ⟨qb, hqb⟩ := hsurj (σ u₁)
        have hqeq : qa = qb := by
          rw [← hrep qa, ← hrep qb, hqa, hqb]; exact Quotient.sound (Or.inr (hinv u₁).symm)
        rw [hqeq, hqb] at hqa; exact hfpf u₁ hqa.symm
      exact Fintype.card_lt_of_injective_not_surjective pickRep hinj hnsurj
    have hnear : Near H := by
      refine ⟨⟨q₁, by rw [hH_deg q₁, hH₀_deg_inv u₁ he₁]; simp⟩, ⟨q₃, fun q hq => ?_⟩⟩
      by_cases hq1 : q = q₁
      · rw [hq1, hH_deg q₁, hH₀_deg_inv u₁ he₁]; simp
      · by_cases hq2 : q = q₂
        · rw [hq2, hH_deg q₂, hH₀_deg_inv u₂ he₂]; simp
        · obtain ⟨u, rfl⟩ := Quotient.exists_rep q
          have hno : ¬ G.Adj u (σ u) := hq₃ u hq1 hq2 hq
          rw [hH_deg ⟦u⟧, hH₀_deg_non u hno]
          omega
    have hpow : HasPower H := hm.2.2.1 Q H hcard_lt hnear
    exact hm.2.1 (hasPower_of_invQuot_add_edge hinv hfpf haut he₁ he₂ hne hpow)
  · -- At most 1 invariant-edge orbit: apply Wave 2's `no_fpf_involution_le_one_edge`!
    push Not at hex2
    by_cases hex1 : ∃ u₁ : V, G.Adj u₁ (σ u₁)
    · obtain ⟨u₁, he₁⟩ := hex1
      refine no_fpf_involution_le_one_edge G hm σ hinv hfpf haut ⟨u₁, fun v hv1 hv2 hv => ?_⟩
      have hqeq := hex2 u₁ v he₁ hv
      rcases Quotient.exact hqeq with h1 | h2
      · exact hv1 h1.symm
      · exact hv2 (by have := congrArg σ h2; rwa [hinv v] at this)
    · push Not at hex1
      obtain ⟨v₀, _⟩ := hm.1.1
      exact no_fpf_involution_le_one_edge G hm σ hinv hfpf haut ⟨v₀, fun v _ _ => hex1 v⟩

/-- NEW (Wave 3, Agent #4): Defect-Fixed Involution Exclusion for 1-Defect MinimalBad(G).
    No 1-defect MinimalBad(G) with non-adjacent defect neighbors (covering all S-N-*, H-N-*)
    admits an involution `σ` fixing only the defect `w` with 0 invariant edges. -/
theorem no_defect_fixed_involution_zero_edges [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (w : V) (hw : G.degree w = 2)
    (hnb_nonadj : ∀ b₁ b₂, G.Adj w b₁ → G.Adj w b₂ → ¬ G.Adj b₁ b₂)
    (σ : V → V) (hinv : ∀ v, σ (σ v) = v)
    (hfix : ∀ v, σ v = v ↔ v = w)
    (haut : ∀ a b, G.Adj a b ↔ G.Adj (σ a) (σ b))
    (hno_edge : ∀ v, ¬ G.Adj v (σ v)) : False := by
  classical
  -- Restrict to G' = G - w on W = {v : V // v ≠ w}
  let W := {v : V // v ≠ w}
  let G' : SimpleGraph W := G.induce {v : V | v ≠ w}
  letI : DecidableRel G'.Adj := fun a b => Classical.dec _
  have hσW : ∀ v : W, σ v.1 ≠ w := fun v h => v.2 (by
    have := congrArg σ h; rw [hinv v.1, (hfix w).mpr rfl] at this; exact this)
  let σ' : W → W := fun v => ⟨σ v.1, hσW v⟩
  have hinv' : ∀ v : W, σ' (σ' v) = v := fun v => Subtype.ext (hinv v.1)
  have hfpf' : ∀ v : W, σ' v ≠ v := fun v h => v.2 ((hfix v.1).mp (congrArg Subtype.val h))
  have haut' : ∀ a b : W, G'.Adj a b ↔ G'.Adj (σ' a) (σ' b) := fun a b => haut a.1 b.1
  have hfree' : ¬ HasPower G' := by
    intro ⟨k, v₀, c, hk, hc, hlen⟩
    exact hm.2.1 ⟨k, v₀.1, c.map ⟨Subtype.val, fun h => h⟩, hk, hc.map Subtype.val_injective, by simp [hlen]⟩
  -- Pick the two neighbors b₁, b₂ = σ b₁ of w
  have hpos : 0 < G.degree w := by omega
  obtain ⟨b₁, hwb₁⟩ := (G.degree_pos_iff_exists_adj w).mp hpos
  have hb₁_ne_w : b₁ ≠ w := (G.ne_of_adj hwb₁).symm
  let b₁W : W := ⟨b₁, hb₁_ne_w⟩
  have hwb₂ : G.Adj w (σ b₁) := by
    have := (haut w b₁).mp hwb₁; rwa [(hfix w).mpr rfl] at this
  have hNw : ∀ v : W, G.Adj w v.1 → v = b₁W ∨ v = σ' b₁W := by
    intro v hwv
    have hsub : ({b₁, σ b₁} : Finset V) ⊆ G.neighborFinset w := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact (G.mem_neighborFinset w b₁).mpr hwb₁
      · exact (G.mem_neighborFinset w (σ b₁)).mpr hwb₂
    have hne_b : b₁ ≠ σ b₁ := fun h => hb₁_ne_w ((hfix b₁).mp h.symm)
    have hcard2 : ({b₁, σ b₁} : Finset V).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hne_b]), Finset.card_singleton]
    have heq : ({b₁, σ b₁} : Finset V) = G.neighborFinset w :=
      Finset.eq_of_subset_of_card_le hsub (by rw [G.card_neighborFinset_eq_degree, hw, hcard2])
    have hvmem : v.1 ∈ ({b₁, σ b₁} : Finset V) := by rw [heq]; exact (G.mem_neighborFinset w v.1).mpr hwv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvmem
    rcases hvmem with h1 | h2
    · exact Or.inl (Subtype.ext h1)
    · exact Or.inr (Subtype.ext h2)
  -- Quotient Q = W / ⟨σ'⟩ and H = invQuotGraph G' σ' hinv'
  let Q := Quotient (invSetoid σ' hinv')
  let H := invQuotGraph G' σ' hinv'
  letI : DecidableRel H.Adj := fun a b => Classical.dec _
  have hHdeg : ∀ u : W, H.degree ⟦u⟧ = G'.degree u := by
    intro u
    let f : G'.neighborSet u → H.neighborSet (⟦u⟧ : Q) := fun v =>
      ⟨⟦v.1⟧, ⟨fun heq => by
        rcases Quotient.exact heq with h1 | h2
        · exact (G'.ne_of_adj v.2) h1
        · exact hno_edge u.1 (congrArg Subtype.val h2 ▸ v.2),
        u, v.1, rfl, rfl, v.2⟩⟩
    have hfinj : Function.Injective f := by
      intro a b heq
      apply Subtype.ext
      rcases Quotient.exact (congrArg Subtype.val heq) with h1 | h2
      · exact h1
      · exact False.elim (no_parallel_of_involution hfree' σ' hinv' hfpf' haut' b.2 (h2 ▸ a.2))
    have hfsurj : Function.Surjective f := by
      rintro ⟨q, hq⟩
      obtain ⟨v, hvq, huv⟩ := lift_edge_exists haut' hq
      exact ⟨⟨v, huv⟩, Subtype.ext hvq⟩
    have hc := Fintype.card_congr (Equiv.ofBijective f ⟨hfinj, hfsurj⟩)
    rw [SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.card_neighborSet_eq_degree] at hc
    exact hc.symm
  -- Every v ∈ W with ⟦v⟧ ≠ ⟦b₁W⟧ is not adjacent to w, so G'.degree v = G.degree v.1 ≥ 3!
  obtain ⟨_, w₀, hw₀⟩ := hm.1
  have hww₀ : w = w₀ := by
    by_contra hne'; have := hw₀ w hne'; omega
  have hG'deg_other : ∀ v : W, (⟦v⟧ : Q) ≠ ⟦b₁W⟧ → 3 ≤ G'.degree v := by
    intro v hvne
    have hnw : ¬ G.Adj w v.1 := by
      intro hwv
      rcases hNw v hwv with rfl | rfl
      · exact hvne rfl
      · exact hvne (Quotient.sound (Or.inr (hinv' b₁W).symm))
    let e : G'.neighborSet v ≃ G.neighborSet v.1 :=
      { toFun := fun u => ⟨u.1.1, u.2⟩
        invFun := fun u => ⟨⟨u.1, fun h => hnw (h ▸ u.2.symm)⟩, u.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_congr e, SimpleGraph.card_neighborSet_eq_degree]
    exact hw₀ v.1 (hww₀ ▸ v.2)
  -- Find a vertex in W not in {b₁W, σ' b₁W} (since G.degree b₁ ≥ 3 and b₁ is not adjacent to σ b₁)
  have hb₁_deg3 : 3 ≤ G.degree b₁ := hw₀ b₁ (hww₀ ▸ hb₁_ne_w)
  have hex_u : ∃ u : W, (⟦u⟧ : Q) ≠ ⟦b₁W⟧ := by
    by_contra hno
    push Not at hno
    have hsub : G.neighborFinset b₁ ⊆ {w, σ b₁} := by
      intro z hz
      have hadj := (G.mem_neighborFinset b₁ z).mp hz
      by_cases hzw : z = w
      · simp [hzw]
      · have hq := hno ⟨z, hzw⟩
        rcases Quotient.exact hq with h1 | h2
        · exfalso; exact (G.ne_of_adj hadj) (congrArg Subtype.val h1).symm
        · simp [congrArg Subtype.val h2]
    have hc := Finset.card_le_card hsub
    rw [G.card_neighborFinset_eq_degree] at hc
    have h2 : ({w, σ b₁} : Finset V).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨u, hu⟩ := hex_u
  have hcard_lt : Fintype.card Q < Fintype.card V := by
    let pickRep : Q → V := fun q => (Classical.choose (Quotient.exists_rep q)).1
    have hrep : ∀ q, ⟦Classical.choose (Quotient.exists_rep q)⟧ = q :=
      fun q => Classical.choose_spec (Quotient.exists_rep q)
    have hinj : Function.Injective pickRep := fun a b h => by
      rw [← hrep a, ← hrep b]
      congr 1; exact Subtype.ext h
    have hnsurj : ¬ Function.Surjective pickRep := by
      intro hsurj
      obtain ⟨q, hq⟩ := hsurj w
      exact (Classical.choose (Quotient.exists_rep q)).2 hq
    exact Fintype.card_lt_of_injective_not_surjective pickRep hinj hnsurj
  have hnear : Near H := by
    refine ⟨⟨⟦u⟧, by rw [hHdeg u]; exact hG'deg_other u hu⟩, ⟨⟦b₁W⟧, fun q hq => ?_⟩⟩
    obtain ⟨v, rfl⟩ := Quotient.exists_rep q
    rw [hHdeg v]
    exact hG'deg_other v hq
  have hpow : HasPower H := hm.2.2.1 Q H hcard_lt hnear
  exact hfree' (hasPower_of_invQuot hinv' hfpf' haut' hpow)

#print axioms inv_edges_independent_in_quot
#print axioms hasPower_of_invQuot_add_edge
#print axioms no_fpf_involution_le_three_edges
#print axioms no_defect_fixed_involution_zero_edges

end E64Involution3
