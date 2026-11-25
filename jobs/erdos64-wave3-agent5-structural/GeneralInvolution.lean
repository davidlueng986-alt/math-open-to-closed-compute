import Core
import Leaves
import PairedShadow
import InvolutionExclusion

/-!
Erdos 64 (Wave 3, Agent #5): Complete General Involution & Mirror-Symmetry Exclusion.
Strictly generalizes Wave 2's `no_fpf_involution_le_one_edge` by removing the fixed-point-free
assumption completely:
1. `no_parallel_of_gen_involution`: no parallel edges between 2-orbits in G/⟨σ⟩.
2. `hasPower_of_genInvQuot`: for ANY involution σ ∈ Aut(G) with ANY fixed-point set F,
   every 2^k-cycle in G/⟨σ⟩ lifts to a 2^k-cycle (if meeting F) or 2^k/2^(k+1)-cycle in G.
3. `genInvQuot_degree_of_nonfixed`: every non-fixed vertex without a σ-invariant edge
   preserves its exact degree in G/⟨σ⟩.
4. `no_gen_involution_near_quot`: master exclusion — no MinimalBad(G) admits a non-trivial
   involution σ whose quotient G/⟨σ⟩ is Near.
5. `no_single_fixed_involution_zero_inv_edge`: excludes odd-order / defect-fixing involutions
   with a unique fixed vertex and zero invariant edges (targeting S-* and H-* leaves).
6. `no_mirror_involution_ge3_fixed`: excludes mirror symmetries whose fixed set induces a
   subgraph of minimum degree >= 3 with <= 1 invariant edge.
-/

namespace E64GenInvolution
open SimpleGraph Erdos64Closure E64Core E64Leaves Erdos64Paired E64Involution
universe u

variable {V : Type u}

/-- In a power-free graph, an involution σ cannot map a non-fixed neighbor v of a non-fixed
    vertex u to another neighbor of u (otherwise u - v - σu - σv - u is a C4). -/
theorem no_parallel_of_gen_involution {G : SimpleGraph V} (hfree : ¬ HasPower G)
    (σ : V → V) (hinv : ∀ v, σ (σ v) = v)
    (haut : ∀ a b, G.Adj a b ↔ G.Adj (σ a) (σ b))
    {u v : V} (hu : σ u ≠ u) (hv : σ v ≠ v)
    (h1 : G.Adj u v) (h2 : G.Adj u (σ v)) : False := by
  have h3 : G.Adj (σ u) (σ v) := (haut u v).mp h1
  have h4 : G.Adj (σ u) v := by
    have := (haut u (σ v)).mp h2
    rwa [hinv v] at this
  have huv : u ≠ v := G.ne_of_adj h1
  have husu : u ≠ σ u := hu.symm
  have husv : u ≠ σ v := G.ne_of_adj h2
  have hvsu : v ≠ σ u := (G.ne_of_adj h4).symm
  have hvsv : v ≠ σ v := hv.symm
  have hsusv : σ u ≠ σ v := by
    intro h
    have := congrArg σ h
    rw [hinv u, hinv v] at this
    exact huv this
  exact hfree (rectangle_power G huv husu husv hvsu hvsv hsusv h1 h4.symm h3 h2.symm)

/-- NEW (Wave 3, Agent #5): Exact Cycle Lifting for Arbitrary Involutions (any fixed-point set F).
    Every 2^k-cycle (k >= 2) in G/⟨σ⟩ lifts to a 2^k-cycle or 2^(k+1)-cycle in G. -/
theorem hasPower_of_genInvQuot {G : SimpleGraph V} {σ : V → V}
    (hinv : ∀ v, σ (σ v) = v)
    (haut : ∀ a b, G.Adj a b ↔ G.Adj (σ a) (σ b))
    (hpow : HasPower (invQuotGraph G σ hinv)) : HasPower G := by
  classical
  obtain ⟨k, q₀, c, hk, hc, hlen⟩ := hpow
  have hge4 : 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide : 0 < 2) hk
  by_cases hfix : ∃ q ∈ c.support, ∃ x : V, (⟦x⟧ : Quotient (invSetoid σ hinv)) = q ∧ σ x = x
  · obtain ⟨qf, hqf, x, hxq, hσx⟩ := hfix
    let c' := c.rotate qf hqf
    have hc' : c'.IsCycle := SimpleGraph.Walk.IsCycle.rotate hqf hc
    have hlen' : c'.length = 2 ^ k := by rw [Walk.length_rotate, hlen]
    let lifted := liftWalk haut c' x hxq
    let u₁ := lifted.1.1
    let p₁ : G.Walk x u₁ := lifted.1.2
    have hu₁q : (⟦u₁⟧ : Quotient (invSetoid σ hinv)) = qf := lifted.2.1
    have hp₁len : p₁.length = 2 ^ k := lifted.2.2.1.trans hlen'
    have hp₁supp : p₁.support.map (Quotient.mk (invSetoid σ hinv)) = c'.support := lifted.2.2.2
    have hp₁tail_map : p₁.support.tail.map (Quotient.mk (invSetoid σ hinv)) = c'.support.tail := by
      rw [List.map_tail, hp₁supp]
    have hp₁tail_nodup : p₁.support.tail.Nodup :=
      List.Nodup.of_map _ (hp₁tail_map.symm ▸ hc'.support_nodup)
    have hrel : u₁ = x ∨ u₁ = σ x := Quotient.exact (hu₁q.trans hxq.symm)
    have hsame : u₁ = x := by
      rcases hrel with h | h
      · exact h
      · rw [hσx] at h; exact h
    let p₁' : G.Walk x x := p₁.copy rfl hsame
    have hp₁'len : p₁'.length = 2 ^ k := (copy_length_eq p₁ rfl hsame).trans hp₁len
    have hp₁'supp : p₁'.support = p₁.support := copy_support_eq p₁ rfl hsame
    have hnil : ¬ p₁'.Nil := by
      intro h; have := Walk.length_eq_zero_iff.mpr h; omega
    have hcyc : p₁'.IsCycle := by
      apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      refine ⟨Walk.IsPath.mk' ?_, by omega⟩
      rw [Walk.support_tail_of_not_nil _ hnil, hp₁'supp]
      exact hp₁tail_nodup
    exact ⟨k, x, p₁', hk, hcyc, hp₁'len⟩
  · obtain ⟨u₀, hu₀⟩ := Quotient.exists_rep q₀
    let lifted := liftWalk haut c u₀ hu₀
    let u₁ := lifted.1.1
    let p₁ : G.Walk u₀ u₁ := lifted.1.2
    have hu₁q : (⟦u₁⟧ : Quotient (invSetoid σ hinv)) = q₀ := lifted.2.1
    have hp₁len : p₁.length = 2 ^ k := lifted.2.2.1.trans hlen
    have hp₁supp : p₁.support.map (Quotient.mk (invSetoid σ hinv)) = c.support := lifted.2.2.2
    have hp₁tail_map : p₁.support.tail.map (Quotient.mk (invSetoid σ hinv)) = c.support.tail := by
      rw [List.map_tail, hp₁supp]
    have hp₁tail_nodup : p₁.support.tail.Nodup :=
      List.Nodup.of_map _ (hp₁tail_map.symm ▸ hc.support_nodup)
    have hrel : u₁ = u₀ ∨ u₁ = σ u₀ := Quotient.exact (hu₁q.trans hu₀.symm)
    rcases hrel with hsame | hflip
    · let p₁' : G.Walk u₀ u₀ := p₁.copy rfl hsame
      have hp₁'len : p₁'.length = 2 ^ k := (copy_length_eq p₁ rfl hsame).trans hp₁len
      have hp₁'supp : p₁'.support = p₁.support := copy_support_eq p₁ rfl hsame
      have hnil : ¬ p₁'.Nil := by
        intro h; have := Walk.length_eq_zero_iff.mpr h; omega
      have hcyc : p₁'.IsCycle := by
        apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
        refine ⟨Walk.IsPath.mk' ?_, by omega⟩
        rw [Walk.support_tail_of_not_nil _ hnil, hp₁'supp]
        exact hp₁tail_nodup
      exact ⟨k, u₀, p₁', hk, hcyc, hp₁'len⟩
    · let f : G →g G := mapWalkAut σ haut
      have hσ_inj : Function.Injective σ := Function.LeftInverse.injective hinv
      let p₂_raw : G.Walk (σ u₀) (σ u₁) := p₁.map f
      have hσu₁ : σ u₁ = u₀ := by rw [hflip, hinv u₀]
      let p₂ : G.Walk u₁ u₀ := p₂_raw.copy hflip.symm hσu₁
      let p : G.Walk u₀ u₀ := p₁.append p₂
      have hp₂len : p₂.length = 2 ^ k := by
        rw [copy_length_eq]
        exact (Walk.length_map f p₁).trans hp₁len
      have hplen : p.length = 2 ^ (k + 1) := by
        simp only [p, Walk.length_append, hp₁len, hp₂len, pow_succ]
        omega
      have hp₂supp : p₂.support = p₁.support.map σ := by
        rw [copy_support_eq]
        exact Walk.support_map f p₁
      have hp₂tail : p₂.support.tail = p₁.support.tail.map σ := by
        rw [hp₂supp, ← List.map_tail]
      have hp_tail : p.support.tail = p₁.support.tail ++ p₂.support.tail := by
        have hps : p.support = p₁.support ++ p₂.support.tail := Walk.support_append p₁ p₂
        have hp₁s : p₁.support = u₀ :: p₁.support.tail := (p₁.cons_tail_support).symm
        calc p.support.tail = (p₁.support ++ p₂.support.tail).tail := by rw [hps]
          _ = (u₀ :: p₁.support.tail ++ p₂.support.tail).tail := by rw [← hp₁s]
          _ = p₁.support.tail ++ p₂.support.tail := rfl
      have hdisj : p₁.support.tail.Disjoint p₂.support.tail := by
        intro x hx1 hx2
        rw [hp₂tail] at hx2
        obtain ⟨y, hy1, hxy⟩ := List.mem_map.mp hx2
        have hqeq : (⟦x⟧ : Quotient (invSetoid σ hinv)) = ⟦y⟧ := by
          rw [← hxy]
          exact Quotient.sound (Or.inr rfl)
        have hinj_on := (List.nodup_map_iff_inj_on hp₁tail_nodup).mp
          (hp₁tail_map.symm ▸ hc.support_nodup)
        have heq : x = y := hinj_on x hx1 y hy1 hqeq
        rw [heq] at hxy
        have hymem : y ∈ p₁.support := List.mem_of_mem_tail hy1
        have hqmem : (⟦y⟧ : Quotient (invSetoid σ hinv)) ∈ c.support := by
          rw [← hp₁supp]
          exact List.mem_map_of_mem hymem
        exact hfix ⟨⟦y⟧, hqmem, y, rfl, hxy⟩
      have hp₂tail_nodup : p₂.support.tail.Nodup := by
        rw [hp₂tail]
        exact (List.nodup_map_iff hσ_inj).mpr hp₁tail_nodup
      have hptail_nodup : p.support.tail.Nodup := by
        rw [hp_tail]
        exact List.nodup_append'.mpr ⟨hp₁tail_nodup, hp₂tail_nodup, hdisj⟩
      have hpnil : ¬ p.Nil := by
        intro h; have := Walk.length_eq_zero_iff.mpr h
        have h2 : 4 ≤ 2 ^ (k + 1) := by rw [pow_succ]; omega
        omega
      have hcyc : p.IsCycle := by
        apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
        refine ⟨Walk.IsPath.mk' ?_, ?_⟩
        · rwa [Walk.support_tail_of_not_nil _ hpnil]
        · rw [hplen, pow_succ]; omega
      exact ⟨k + 1, u₀, p, by omega, hcyc, hplen⟩

/-- Every non-fixed vertex u without a σ-invariant edge preserves its exact degree in G/⟨σ⟩. -/
theorem genInvQuot_degree_of_nonfixed [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hfree : ¬ HasPower G)
    (σ : V → V) (hinv : ∀ v, σ (σ v) = v)
    (haut : ∀ a b, G.Adj a b ↔ G.Adj (σ a) (σ b))
    [Fintype (Quotient (invSetoid σ hinv))]
    [DecidableRel (invQuotGraph G σ hinv).Adj]
    {u : V} (hu : σ u ≠ u) (hno : ¬ G.Adj u (σ u)) :
    (invQuotGraph G σ hinv).degree (⟦u⟧ : Quotient (invSetoid σ hinv)) = G.degree u := by
  classical
  let Q := Quotient (invSetoid σ hinv)
  let H := invQuotGraph G σ hinv
  let f : G.neighborSet u → H.neighborSet (⟦u⟧ : Q) := fun v =>
    ⟨⟦v.1⟧, ⟨fun heq => by
      rcases Quotient.exact heq with h1 | h2
      · exact (G.ne_of_adj v.2) h1
      · have hv2 : G.Adj u v.1 := v.2
        have h3 : G.Adj (σ u) (σ v.1) := (haut u v.1).mp hv2
        rw [← h2] at h3
        exact hno h3.symm,
      u, v.1, rfl, rfl, v.2⟩⟩
  have hfinj : Function.Injective f := by
    intro a b heq
    apply Subtype.ext
    rcases Quotient.exact (congrArg Subtype.val heq) with h1 | h2
    · exact h1
    · by_cases hbfix : σ b.1 = b.1
      · rw [hbfix] at h2; exact h2
      · exact False.elim (no_parallel_of_gen_involution hfree σ hinv haut hu hbfix b.2 (h2 ▸ a.2))
  have hfsurj : Function.Surjective f := by
    rintro ⟨q, hq⟩
    obtain ⟨v, hvq, huv⟩ := lift_edge_exists haut hq
    exact ⟨⟨v, huv⟩, Subtype.ext hvq⟩
  have hc := Fintype.card_congr (Equiv.ofBijective f ⟨hfinj, hfsurj⟩)
  rw [SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.card_neighborSet_eq_degree] at hc
  exact hc.symm

/-- Master General Involution Exclusion: no MinimalBad(G) admits a non-trivial involution σ
    whose quotient G/⟨σ⟩ is Near. -/
theorem no_gen_involution_near_quot [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (σ : V → V) (hinv : ∀ v, σ (σ v) = v)
    (haut : ∀ a b, G.Adj a b ↔ G.Adj (σ a) (σ b))
    (hnontriv : ∃ u₀ : V, σ u₀ ≠ u₀)
    [Fintype (Quotient (invSetoid σ hinv))]
    [DecidableRel (invQuotGraph G σ hinv).Adj]
    (hnear : Near (invQuotGraph G σ hinv)) : False := by
  classical
  let Q := Quotient (invSetoid σ hinv)
  let H := invQuotGraph G σ hinv
  obtain ⟨u₀, hu₀⟩ := hnontriv
  have hcard_lt : Fintype.card Q < Fintype.card V := by
    let pickRep : Q → V := fun q => Classical.choose (Quotient.exists_rep q)
    have hrep : ∀ q, ⟦pickRep q⟧ = q := fun q => Classical.choose_spec (Quotient.exists_rep q)
    have hinj : Function.Injective pickRep := fun a b h => by rw [← hrep a, ← hrep b, h]
    have hnsurj : ¬ Function.Surjective pickRep := by
      intro hsurj
      obtain ⟨q₁, hq₁⟩ := hsurj u₀
      obtain ⟨q₂, hq₂⟩ := hsurj (σ u₀)
      have hqeq : q₁ = q₂ := by
        rw [← hrep q₁, ← hrep q₂, hq₁, hq₂]
        exact Quotient.sound (Or.inr (hinv u₀).symm)
      rw [hqeq, hq₂] at hq₁
      exact hu₀ hq₁
    exact Fintype.card_lt_of_injective_not_surjective pickRep hinj hnsurj
  have hpow : HasPower H := hm.2.2.1 Q H hcard_lt hnear
  exact hm.2.1 (hasPower_of_genInvQuot hinv haut hpow)

/-- NEW (Wave 3, Agent #5): Odd-Order / Defect-Fixing Involution Exclusion (targets S-* and H-*).
    No MinimalBad(G) admits an involution σ with a unique fixed vertex w₀ and zero σ-invariant edges. -/
theorem no_single_fixed_involution_zero_inv_edge [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (σ : V → V) (hinv : ∀ v, σ (σ v) = v)
    (haut : ∀ a b, G.Adj a b ↔ G.Adj (σ a) (σ b))
    (w₀ : V) (huniq_fix : ∀ v : V, σ v = v ↔ v = w₀)
    (hno_edge : ∀ v : V, ¬ G.Adj v (σ v)) : False := by
  classical
  have hdeg_eq : ∀ v : V, G.degree (σ v) = G.degree v := by
    intro v
    let e : G.neighborSet (σ v) ≃ G.neighborSet v :=
      { toFun := fun u => ⟨σ u.1, by have := (haut (σ v) u.1).mp u.2; rwa [hinv v] at this⟩
        invFun := fun u => ⟨σ u.1, (haut v u.1).mp u.2⟩
        left_inv := fun u => Subtype.ext (hinv u.1)
        right_inv := fun u => Subtype.ext (hinv u.1) }
    rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
    exact Fintype.card_congr e
  have hge3 : ∀ v : V, v ≠ w₀ → 3 ≤ G.degree v := by
    obtain ⟨_, w, hw⟩ := hm.1
    intro v hvw₀
    by_cases hvw : v = w
    · subst v
      have hσw : σ w ≠ w := fun h => hvw₀ ((huniq_fix w).mp h)
      rw [← hdeg_eq w]
      exact hw (σ w) hσw
    · exact hw v hvw
  obtain ⟨a, ha⟩ := hm.1.1
  have hV4 : 4 ≤ Fintype.card V := by
    have := G.degree_lt_card_verts a; omega
  have hex_u₀ : ∃ u₀ : V, u₀ ≠ w₀ := by
    by_contra h
    push Not at h
    have hinj : Function.Injective (fun _ : V => ()) := fun p q _ => (h p).trans (h q).symm
    have hc := Fintype.card_le_of_injective _ hinj
    simp at hc; omega
  obtain ⟨u₀, hu₀⟩ := hex_u₀
  have hσu₀ : σ u₀ ≠ u₀ := fun h => hu₀ ((huniq_fix u₀).mp h)
  let H := invQuotGraph G σ hinv
  let _ : DecidableRel H.Adj := fun a b => Classical.dec _
  have hnear : Near H := by
    refine ⟨⟨⟦u₀⟧, ?_⟩, ⟨⟦w₀⟧, fun q hq => ?_⟩⟩
    · rw [genInvQuot_degree_of_nonfixed G hm.2.1 σ hinv haut hσu₀ (hno_edge u₀)]
      exact hge3 u₀ hu₀
    · obtain ⟨u, rfl⟩ := Quotient.exists_rep q
      have huw : u ≠ w₀ := fun h => hq (by rw [h])
      have hσu : σ u ≠ u := fun h => huw ((huniq_fix u).mp h)
      rw [genInvQuot_degree_of_nonfixed G hm.2.1 σ hinv haut hσu (hno_edge u)]
      exact hge3 u huw
  exact no_gen_involution_near_quot G hm σ hinv haut ⟨u₀, hσu₀⟩ hnear

/-- NEW (Wave 3, Agent #5): Mirror-Symmetry / δ>=3-Fixed-Subgraph Exclusion.
    No MinimalBad(G) admits a non-trivial involution σ whose fixed-point set F induces a
    subgraph with δ(G[F]) >= 3 and which has at most one σ-invariant edge. -/
theorem no_mirror_involution_ge3_fixed [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (σ : V → V) (hinv : ∀ v, σ (σ v) = v)
    (haut : ∀ a b, G.Adj a b ↔ G.Adj (σ a) (σ b))
    (hnontriv : ∃ u₀ : V, σ u₀ ≠ u₀)
    (hfix_deg : ∀ x : V, σ x = x → 3 ≤ ((G.neighborFinset x).filter (fun y => σ y = y)).card)
    (h1edge : ∃ e₀ : V, ∀ v : V, v ≠ e₀ → v ≠ σ e₀ → ¬ G.Adj v (σ v)) : False := by
  classical
  have hdeg_eq : ∀ v : V, G.degree (σ v) = G.degree v := by
    intro v
    let e : G.neighborSet (σ v) ≃ G.neighborSet v :=
      { toFun := fun u => ⟨σ u.1, by have := (haut (σ v) u.1).mp u.2; rwa [hinv v] at this⟩
        invFun := fun u => ⟨σ u.1, (haut v u.1).mp u.2⟩
        left_inv := fun u => Subtype.ext (hinv u.1)
        right_inv := fun u => Subtype.ext (hinv u.1) }
    rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
    exact Fintype.card_congr e
  have hnonfix_ge3 : ∀ v : V, σ v ≠ v → 3 ≤ G.degree v := by
    obtain ⟨_, w, hw⟩ := hm.1
    intro v hv
    by_cases hvw : v = w
    · subst v; rw [← hdeg_eq w]; exact hw (σ w) hv
    · exact hw v hvw
  let Q := Quotient (invSetoid σ hinv)
  let H := invQuotGraph G σ hinv
  let _ : DecidableRel H.Adj := fun a b => Classical.dec _
  have hfix_qdeg : ∀ x : V, σ x = x → 3 ≤ H.degree (⟦x⟧ : Q) := by
    intro x hσx
    let S := (G.neighborFinset x).filter (fun y => σ y = y)
    let f : S → H.neighborSet (⟦x⟧ : Q) := fun y =>
      ⟨⟦y.1⟧, ⟨fun heq => by
        rcases Quotient.exact heq with h1 | h2
        · exact (G.ne_of_adj ((G.mem_neighborFinset x y.1).mp (Finset.mem_filter.mp y.2).1)) h1
        · rw [(Finset.mem_filter.mp y.2).2] at h2
          exact (G.ne_of_adj ((G.mem_neighborFinset x y.1).mp (Finset.mem_filter.mp y.2).1)) h2,
        x, y.1, rfl, rfl, (G.mem_neighborFinset x y.1).mp (Finset.mem_filter.mp y.2).1⟩⟩
    have hfinj : Function.Injective f := by
      intro a b heq
      apply Subtype.ext
      rcases Quotient.exact (congrArg Subtype.val heq) with h1 | h2
      · exact h1
      · rw [(Finset.mem_filter.mp b.2).2] at h2; exact h2
    have hc := Fintype.card_le_of_injective f hfinj
    rw [Fintype.card_coe, SimpleGraph.card_neighborSet_eq_degree] at hc
    exact (hfix_deg x hσx).trans hc
  obtain ⟨e₀, he₀⟩ := h1edge
  have hq_all : ∀ q : Q, q ≠ ⟦e₀⟧ → 3 ≤ H.degree q := by
    intro q hq
    obtain ⟨u, rfl⟩ := Quotient.exists_rep q
    by_cases hfix : σ u = u
    · exact hfix_qdeg u hfix
    · have hu1 : u ≠ e₀ := fun h => hq (by rw [h])
      have hu2 : u ≠ σ e₀ := fun h => hq (by rw [h]; exact Quotient.sound (Or.inr rfl))
      rw [genInvQuot_degree_of_nonfixed G hm.2.1 σ hinv haut hfix (he₀ u hu1 hu2)]
      exact hnonfix_ge3 u hfix
  have hQ2 : 2 ≤ Fintype.card Q := by
    obtain ⟨a, ha⟩ := hm.1.1
    have hV4 : 4 ≤ Fintype.card V := by have := G.degree_lt_card_verts a; omega
    by_contra hlt
    have hle1 : Fintype.card Q ≤ 1 := by omega
    have hall_eq : ∀ v : V, v = e₀ ∨ v = σ e₀ := by
      intro v
      have hq : (⟦v⟧ : Q) = ⟦e₀⟧ := by
        have _ : Subsingleton Q := Fintype.card_le_one_iff_subsingleton.mp hle1
        exact Subsingleton.elim _ _
      exact Quotient.exact hq
    have hs : (Finset.univ : Finset V) ⊆ {e₀, σ e₀} := by
      intro v _
      rcases hall_eq v with rfl | rfl <;> simp
    have hc := Finset.card_le_card hs
    have h2 : ({e₀, σ e₀} : Finset V).card ≤ 2 := Finset.card_le_two
    rw [Finset.card_univ] at hc
    omega
  have hnear : Near H := near_of_except H ⟦e₀⟧ hQ2 hq_all
  exact no_gen_involution_near_quot G hm σ hinv haut hnontriv hnear

#print axioms no_parallel_of_gen_involution
#print axioms hasPower_of_genInvQuot
#print axioms genInvQuot_degree_of_nonfixed
#print axioms no_gen_involution_near_quot
#print axioms no_single_fixed_involution_zero_inv_edge
#print axioms no_mirror_involution_ge3_fixed

end E64GenInvolution
