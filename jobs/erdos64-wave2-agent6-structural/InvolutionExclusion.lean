import Core
import Leaves
import PairedShadow

/-!
Erdos 64 (Wave 2, Agent #6): Fixed-Point-Free Involution / 2-Lift Exclusion Theorem.
Proves (unconditionally, all finite orders, standard axioms only):
No MinimalBad(G) graph admits a fixed-point-free graph automorphism σ of order 2
with at most one σ-invariant edge.
In particular, no 2-lift (double cover) of any graph with δ ≥ 3 can be MinimalBad(G),
and every fixed-point-free involution of a cubic MinimalBad(G) has at least 2 invariant edges.
-/

namespace E64Involution
open SimpleGraph Erdos64Closure E64Core E64Leaves Erdos64Paired
universe u

variable {V : Type u}

/-- Equivalence relation induced by an involution σ : V → V. -/
def invSetoid (σ : V → V) (hinv : ∀ v, σ (σ v) = v) : Setoid V where
  r a b := a = b ∨ a = σ b
  iseqv :=
    { refl := fun _ => Or.inl rfl
      symm := by
        rintro a b (rfl | rfl)
        · exact Or.inl rfl
        · exact Or.inr (hinv _).symm
      trans := by
        rintro a b c (rfl | rfl) (rfl | rfl)
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact Or.inr rfl
        · exact Or.inl (hinv _) }

/-- In any power-free graph, a fixed-point-free involution σ cannot map a neighbor of u
    to another neighbor of u (otherwise u - v - σu - σv - u is a C4). -/
theorem no_parallel_of_involution {G : SimpleGraph V} (hfree : ¬ HasPower G)
    (σ : V → V) (hinv : ∀ v, σ (σ v) = v) (hfpf : ∀ v, σ v ≠ v)
    (haut : ∀ a b, G.Adj a b ↔ G.Adj (σ a) (σ b))
    {u v : V} (h1 : G.Adj u v) (h2 : G.Adj u (σ v)) : False := by
  have h3 : G.Adj (σ u) (σ v) := (haut u v).mp h1
  have h4 : G.Adj (σ u) v := by
    have := (haut u (σ v)).mp h2
    rwa [hinv v] at this
  have huv : u ≠ v := G.ne_of_adj h1
  have husu : u ≠ σ u := (hfpf u).symm
  have husv : u ≠ σ v := G.ne_of_adj h2
  have hvsu : v ≠ σ u := (G.ne_of_adj h4).symm
  have hvsv : v ≠ σ v := (hfpf v).symm
  have hsusv : σ u ≠ σ v := by
    intro h
    have := congrArg σ h
    rw [hinv u, hinv v] at this
    exact huv this
  exact hfree (rectangle_power G huv husu husv hvsu hvsv hsusv h1 h4.symm h3 h2.symm)

/-- Simple quotient graph G / ⟨σ⟩ on the orbits of a fixed-point-free involution σ. -/
def invQuotGraph (G : SimpleGraph V) (σ : V → V) (hinv : ∀ v, σ (σ v) = v) :
    SimpleGraph (Quotient (invSetoid σ hinv)) where
  Adj q₁ q₂ := q₁ ≠ q₂ ∧ ∃ u v, ⟦u⟧ = q₁ ∧ ⟦v⟧ = q₂ ∧ G.Adj u v
  symm := ⟨by
    rintro q₁ q₂ ⟨hne, u, v, hu, hv, hadj⟩
    exact ⟨hne.symm, v, u, hv, hu, hadj.symm⟩⟩
  loopless := ⟨by intro q h; exact h.1 rfl⟩

/-- Unique lifting of a single edge from `G / ⟨σ⟩` to `G` at a given starting vertex `u`. -/
theorem lift_edge_exists {G : SimpleGraph V} {σ : V → V} {hinv : ∀ v, σ (σ v) = v}
    (haut : ∀ a b, G.Adj a b ↔ G.Adj (σ a) (σ b))
    {u : V} {q₂ : Quotient (invSetoid σ hinv)}
    (hadj : (invQuotGraph G σ hinv).Adj ⟦u⟧ q₂) :
    ∃ v : V, ⟦v⟧ = q₂ ∧ G.Adj u v := by
  obtain ⟨_, a, b, ha, hb, hab⟩ := hadj
  have hrel : a = u ∨ a = σ u := Quotient.exact ha
  rcases hrel with rfl | rfl
  · exact ⟨b, hb, hab⟩
  · refine ⟨σ b, ?_, ?_⟩
    · rw [← hb]
      exact Quotient.sound (Or.inr rfl)
    · have := (haut (σ u) b).mp hab
      rwa [hinv u] at this

/-- Lift an arbitrary walk in `G / ⟨σ⟩` starting at `u₀ ∈ q₀`. -/
noncomputable def liftWalk {G : SimpleGraph V} {σ : V → V} {hinv : ∀ v, σ (σ v) = v}
    (haut : ∀ a b, G.Adj a b ↔ G.Adj (σ a) (σ b))
    {q₁ q₂ : Quotient (invSetoid σ hinv)} (p : (invQuotGraph G σ hinv).Walk q₁ q₂)
    (u : V) (hu : ⟦u⟧ = q₁) :
    {res : Σ w : V, G.Walk u w // ⟦res.1⟧ = q₂ ∧ res.2.length = p.length ∧
      res.2.support.map (Quotient.mk (invSetoid σ hinv)) = p.support} :=
  match p with
  | .nil => ⟨⟨u, .nil⟩, hu, rfl, by simp [hu]⟩
  | @Walk.cons _ _ qa qb qc hab q =>
    let hex := lift_edge_exists haut (hu.symm ▸ hab)
    let v := Classical.choose hex
    let hv := Classical.choose_spec hex
    let rest := liftWalk haut q v hv.1
    ⟨⟨rest.1.1, .cons hv.2 rest.1.2⟩,
      rest.2.1,
      by simp [rest.2.2.1],
      by simp [Walk.support_cons, hu, rest.2.2.2]⟩

/-- Apply automorphism `σ` to a walk in `G`. -/
def mapWalkAut {G : SimpleGraph V} (σ : V → V)
    (haut : ∀ a b, G.Adj a b ↔ G.Adj (σ a) (σ b)) : G →g G :=
  ⟨σ, fun h => (haut _ _).mp h⟩

/-- Every `2^k`-cycle (`k ≥ 2`) in `G / ⟨σ⟩` lifts to a `2^k`-cycle or `2^(k+1)`-cycle in `G`. -/
theorem hasPower_of_invQuot {G : SimpleGraph V} {σ : V → V}
    (hinv : ∀ v, σ (σ v) = v) (hfpf : ∀ v, σ v ≠ v)
    (haut : ∀ a b, G.Adj a b ↔ G.Adj (σ a) (σ b))
    (hpow : HasPower (invQuotGraph G σ hinv)) : HasPower G := by
  classical
  obtain ⟨k, q₀, c, hk, hc, hlen⟩ := hpow
  obtain ⟨u₀, hu₀⟩ := Quotient.exists_rep q₀
  let lifted := liftWalk haut c u₀ hu₀
  let u₁ := lifted.1.1
  let p₁ : G.Walk u₀ u₁ := lifted.1.2
  have hu₁q : ⟦u₁⟧ = q₀ := lifted.2.1
  have hp₁len : p₁.length = 2 ^ k := lifted.2.2.1.trans hlen
  have hp₁supp : p₁.support.map (Quotient.mk (invSetoid σ hinv)) = c.support := lifted.2.2.2
  have hp₁tail_map : p₁.support.tail.map (Quotient.mk (invSetoid σ hinv)) = c.support.tail := by
    rw [List.map_tail, hp₁supp]
  have hp₁tail_nodup : p₁.support.tail.Nodup :=
    List.Nodup.of_map _ (hp₁tail_map.symm ▸ hc.support_nodup)
  have hge4 : 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide : 0 < 2) hk
  have hrel : u₁ = u₀ ∨ u₁ = σ u₀ := Quotient.exact (hu₁q.trans hu₀.symm)
  rcases hrel with hsame | hflip
  · subst hsame
    have hnil : ¬ p₁.Nil := by
      intro h; have := Walk.length_eq_zero_iff.mpr h; omega
    have hcyc : p₁.IsCycle := by
      apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      refine ⟨Walk.IsPath.mk' ?_, by omega⟩
      rwa [Walk.support_tail_of_not_nil _ hnil]
    exact ⟨k, u₀, p₁, hk, hcyc, hp₁len⟩
  · let f : G →g G := mapWalkAut σ haut
    have hσ_inj : Function.Injective σ := Function.LeftInverse.injective hinv
    let p₂_raw : G.Walk (σ u₀) (σ u₁) := p₁.map f
    have hσu₁ : σ u₁ = u₀ := by rw [hflip, hinv u₀]
    let p₂ : G.Walk u₁ u₀ := p₂_raw.copy hflip.symm hσu₁
    let p : G.Walk u₀ u₀ := p₁.append p₂
    have hp₂len : p₂.length = 2 ^ k := by
      simp [p₂, p₂_raw, Walk.length_copy, Walk.length_map, hp₁len]
    have hplen : p.length = 2 ^ (k + 1) := by
      simp only [p, Walk.length_append, hp₁len, hp₂len, pow_succ]
      omega
    have hp₂supp : p₂.support = p₁.support.map σ := by
      simp [p₂, p₂_raw, Walk.support_copy, Walk.support_map, f, mapWalkAut]
    have hp₂tail : p₂.support.tail = p₁.support.tail.map σ := by
      rw [hp₂supp, ← List.map_tail]
    have hp_tail : p.support.tail = p₁.support.tail ++ p₂.support.tail := by
      have hps : p.support = p₁.support ++ p₂.support.tail := Walk.support_append p₁ p₂
      have hp₁s : p₁.support = u₀ :: p₁.support.tail := (p₁.cons_tail_support).symm
      rw [hps, hp₁s, List.cons_append, List.tail_cons]
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
      exact hfpf y hxy
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

/-- NEW (Wave 2, Agent #6): Fixed-Point-Free Involution / 2-Lift Exclusion Theorem.
    No MinimalBad(G) admits a fixed-point-free automorphism σ of order 2 with at most
    one σ-invariant edge. -/
theorem no_fpf_involution_le_one_edge [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (σ : V → V) (hinv : ∀ v, σ (σ v) = v) (hfpf : ∀ v, σ v ≠ v)
    (haut : ∀ a b, G.Adj a b ↔ G.Adj (σ a) (σ b))
    (h1edge : ∃ w₀ : V, ∀ v : V, v ≠ w₀ → v ≠ σ w₀ → ¬ G.Adj v (σ v)) : False := by
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
  have hall3 : ∀ v : V, 3 ≤ G.degree v := by
    obtain ⟨_, w, hw⟩ := hm.1
    intro v
    by_cases hvw : v = w
    · subst v
      rw [← hdeg_eq w]
      exact hw (σ w) (hfpf w)
    · exact hw v hvw
  have hC : ∀ v : V, G.degree v = 3 := no_high_when_no_defect G hm hall3
  let Q := Quotient (invSetoid σ hinv)
  let H := invQuotGraph G σ hinv
  let _ : DecidableRel H.Adj := fun a b => Classical.dec _
  obtain ⟨w₀, hw₀⟩ := h1edge
  have hcard_lt : Fintype.card Q < Fintype.card V := by
    let pickRep : Q → V := fun q => Classical.choose (Quotient.exists_rep q)
    have hrep : ∀ q, ⟦pickRep q⟧ = q := fun q => Classical.choose_spec (Quotient.exists_rep q)
    have hinj : Function.Injective pickRep := fun a b h => by rw [← hrep a, ← hrep b, h]
    have hnsurj : ¬ Function.Surjective pickRep := by
      intro hsurj
      obtain ⟨q₁, hq₁⟩ := hsurj w₀
      obtain ⟨q₂, hq₂⟩ := hsurj (σ w₀)
      have hqeq : q₁ = q₂ := by
        rw [← hrep q₁, ← hrep q₂, hq₁, hq₂]
        exact Quotient.sound (Or.inr (hinv w₀).symm)
      rw [hqeq, hq₂] at hq₁
      exact hfpf w₀ hq₁
    exact Fintype.card_lt_of_injective_not_surjective pickRep hinj hnsurj
  have hHdeg : ∀ u : V, ¬ G.Adj u (σ u) → H.degree ⟦u⟧ = 3 := by
    intro u hno
    let f : G.neighborSet u → H.neighborSet (⟦u⟧ : Q) := fun v =>
      ⟨⟦v.1⟧, ⟨fun heq => by
        rcases Quotient.exact heq with h1 | h2
        · exact (G.ne_of_adj v.2) h1.symm
        · have hv2 : G.Adj u v.1 := v.2; rw [h2] at hv2; exact hno hv2,
        u, v.1, rfl, rfl, v.2⟩⟩
    have hfinj : Function.Injective f := by
      intro a b heq
      apply Subtype.ext
      rcases Quotient.exact (congrArg Subtype.val heq) with h1 | h2
      · exact h1
      · have ha2 : G.Adj u a.1 := a.2
        rw [h2] at ha2
        exact False.elim (no_parallel_of_involution hm.2.1 σ hinv hfpf haut b.2 ha2)
    have hfsurj : Function.Surjective f := by
      rintro ⟨q, hq⟩
      obtain ⟨v, hvq, huv⟩ := lift_edge_exists haut hq
      exact ⟨⟨v, huv⟩, Subtype.ext hvq⟩
    have hc := Fintype.card_congr (Equiv.ofBijective f ⟨hfinj, hfsurj⟩)
    rw [SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.card_neighborSet_eq_degree, hC u] at hc
    exact hc.symm
  have hV4 : 4 ≤ Fintype.card V := by
    have := G.degree_lt_card_verts w₀; rw [hC w₀] at this; omega
  have hex_u₁ : ∃ u₁ : V, u₁ ≠ w₀ ∧ u₁ ≠ σ w₀ := by
    by_contra h
    push Not at h
    have hs : (Finset.univ : Finset V) ⊆ {w₀, σ w₀} := by
      intro v _
      by_cases hv : v = w₀
      · simp [hv]
      · simp [h v hv]
    have hc := Finset.card_le_card hs
    have h2 : ({w₀, σ w₀} : Finset V).card ≤ 2 := Finset.card_le_two
    rw [Finset.card_univ] at hc
    omega
  obtain ⟨u₁, hu₁a, hu₁b⟩ := hex_u₁
  have hnear : Near H := by
    refine ⟨⟨⟦u₁⟧, (hHdeg u₁ (hw₀ u₁ hu₁a hu₁b)).ge⟩, ⟨⟦w₀⟧, fun q hq => ?_⟩⟩
    obtain ⟨u, rfl⟩ := Quotient.exists_rep q
    have hu1 : u ≠ w₀ := fun h => hq (by rw [h])
    have hu2 : u ≠ σ w₀ := fun h => hq (by rw [h]; exact Quotient.sound (Or.inr rfl))
    exact (hHdeg u (hw₀ u hu1 hu2)).ge
  have hpow : HasPower H := hm.2.2.1 Q H hcard_lt hnear
  exact hm.2.1 (hasPower_of_invQuot hinv hfpf haut hpow)

#print axioms no_parallel_of_involution
#print axioms hasPower_of_invQuot
#print axioms no_fpf_involution_le_one_edge

end E64Involution
