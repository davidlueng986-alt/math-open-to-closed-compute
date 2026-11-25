import Core
import Leaves
import PairedShadow

/-!
Erdos 64 (Wave 3, Agent #6): Generalized Involution Exclusion (Arbitrary Fixed-Point Sets).
Strictly generalizes Wave 2's fixed-point-free involution theorem to ALL nontrivial
involutions σ ∈ Aut(G) with arbitrarily many fixed points:
1. `hasPower_of_any_invQuot`: For ANY involution σ ∈ Aut(G) (with or without fixed points),
   every 2^k-cycle (k ≥ 2) in G / ⟨σ⟩ lifts to a 2^k-cycle (if it meets Fix(σ)) or a
   2^k- or 2^(k+1)-cycle (if it avoids Fix(σ)) in G.
2. `no_nontrivial_involution_near_quot`: No MinimalBad(G) admits a nontrivial involution σ
   whose quotient G / ⟨σ⟩ is Near.
3. `no_involution_le_one_boundary`: Explicit exclusion of any MinimalBad(G) admitting a
   nontrivial involution σ with at most one boundary orbit (defect, invariant edge, or
   fixed point sending edges outside Fix(σ)).
-/

namespace E64GenInvolution
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

/-- Simple quotient graph G / ⟨σ⟩ on the orbits of an involution σ (allowing fixed points). -/
def invQuotGraph (G : SimpleGraph V) (σ : V → V) (hinv : ∀ v, σ (σ v) = v) :
    SimpleGraph (Quotient (invSetoid σ hinv)) where
  Adj q₁ q₂ := q₁ ≠ q₂ ∧ ∃ u v, ⟦u⟧ = q₁ ∧ ⟦v⟧ = q₂ ∧ G.Adj u v
  symm := ⟨by
    rintro q₁ q₂ ⟨hne, u, v, hu, hv, hadj⟩
    exact ⟨hne.symm, v, u, hv, hu, hadj.symm⟩⟩
  loopless := ⟨by intro q h; exact h.1 rfl⟩

/-- Lifting of a single edge from `G / ⟨σ⟩` to `G` at a given starting vertex `u`. -/
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

/-- Lift an arbitrary walk in `G / ⟨σ⟩` starting at `u ∈ q₁`. -/
noncomputable def liftWalk {G : SimpleGraph V} {σ : V → V} {hinv : ∀ v, σ (σ v) = v}
    (haut : ∀ a b, G.Adj a b ↔ G.Adj (σ a) (σ b))
    {q₁ q₂ : Quotient (invSetoid σ hinv)} (p : (invQuotGraph G σ hinv).Walk q₁ q₂)
    (u : V) (hu : ⟦u⟧ = q₁) :
    {res : Σ w : V, G.Walk u w // ⟦res.1⟧ = q₂ ∧ res.2.length = p.length ∧
      res.2.support.map (Quotient.mk (invSetoid σ hinv)) = p.support} :=
  match p with
  | .nil => ⟨⟨u, .nil⟩, hu, rfl, by simp [hu]⟩
  | .cons hab q =>
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

/-- NEW (Wave 3, Agent #6): Arbitrary-Fixed-Point Involution Cycle Lifting.
    For ANY involution σ ∈ Aut(G) (with arbitrarily many fixed points), every 2^k-cycle
    (k ≥ 2) in G / ⟨σ⟩ lifts to a simple 2^k-cycle or 2^(k+1)-cycle in G. -/
theorem hasPower_of_any_invQuot {G : SimpleGraph V} {σ : V → V}
    (hinv : ∀ v, σ (σ v) = v)
    (haut : ∀ a b, G.Adj a b ↔ G.Adj (σ a) (σ b))
    (hpow : HasPower (invQuotGraph G σ hinv)) : HasPower G := by
  classical
  obtain ⟨k, q₀, c, hk, hc, hlen⟩ := hpow
  have hge4 : 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide : 0 < 2) hk
  by_cases hfix : ∃ v : V, σ v = v ∧ (⟦v⟧ : Quotient (invSetoid σ hinv)) ∈ c.support
  · obtain ⟨v₀, hv₀fix, hv₀mem⟩ := hfix
    let c' := c.rotate (⟦v₀⟧ : Quotient (invSetoid σ hinv)) hv₀mem
    have hc' : c'.IsCycle := hc.rotate hv₀mem
    have hlen' : c'.length = 2 ^ k := by rw [Walk.length_rotate, hlen]
    let lifted := liftWalk haut c' v₀ rfl
    let v₁ := lifted.1.1
    let p₁ : G.Walk v₀ v₁ := lifted.1.2
    have hv₁q : (⟦v₁⟧ : Quotient (invSetoid σ hinv)) = ⟦v₀⟧ := lifted.2.1
    have hp₁len : p₁.length = 2 ^ k := lifted.2.2.1.trans hlen'
    have hp₁supp : p₁.support.map (Quotient.mk (invSetoid σ hinv)) = c'.support := lifted.2.2.2
    have hp₁tail_map : p₁.support.tail.map (Quotient.mk (invSetoid σ hinv)) = c'.support.tail := by
      rw [List.map_tail, hp₁supp]
    have hp₁tail_nodup : p₁.support.tail.Nodup :=
      List.Nodup.of_map _ (hp₁tail_map.symm ▸ hc'.support_nodup)
    have hrel : v₁ = v₀ ∨ v₁ = σ v₀ := Quotient.exact hv₁q
    have hsame : v₁ = v₀ := by
      rcases hrel with h | h
      · exact h
      · exact h.trans hv₀fix
    let p₁' : G.Walk v₀ v₀ := p₁.copy rfl hsame
    have hp₁'len : p₁'.length = 2 ^ k := by rw [Walk.length_copy, hp₁len]
    have hp₁'supp : p₁'.support = p₁.support := Walk.support_copy p₁ rfl hsame
    have hnil : ¬ p₁'.Nil := by
      intro h; have := Walk.length_eq_zero_iff.mpr h; omega
    have hcyc : p₁'.IsCycle := by
      apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      refine ⟨Walk.IsPath.mk' ?_, by omega⟩
      rw [Walk.support_tail_of_not_nil _ hnil, hp₁'supp]
      exact hp₁tail_nodup
    exact ⟨k, v₀, p₁', hk, hcyc, hp₁'len⟩
  · push Not at hfix
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
    have hrel : u₁ = u₀ ∨ u₁ = σ u₀ := Quotient.exact (hu₁q.trans hu₀.symm)
    rcases hrel with hsame | hflip
    · let p₁' : G.Walk u₀ u₀ := p₁.copy rfl hsame
      have hp₁'len : p₁'.length = 2 ^ k := by rw [Walk.length_copy, hp₁len]
      have hp₁'supp : p₁'.support = p₁.support := Walk.support_copy p₁ rfl hsame
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
      have hp₂len : p₂.length = 2 ^ k :=
        (Walk.length_copy p₂_raw hflip.symm hσu₁).trans ((Walk.length_map f p₁).trans hp₁len)
      have hplen : p.length = 2 ^ (k + 1) := by
        simp only [p, Walk.length_append, hp₁len, hp₂len, pow_succ]
        omega
      have hp₂supp : p₂.support = p₁.support.map σ := by
        simp [p₂, p₂_raw, Walk.support_copy, Walk.support_map, f, mapWalkAut]
      have hp₂tail : p₂.support.tail = p₁.support.tail.map σ := by
        rw [hp₂supp, List.map_tail]
      have hp_tail : p.support.tail = p₁.support.tail ++ p₂.support.tail := by
        have hps : p.support = p₁.support ++ p₂.support.tail := Walk.support_append p₁ p₂
        have hp₁s : p₁.support = u₀ :: p₁.support.tail := (p₁.cons_tail_support).symm
        conv_lhs => rw [hps, hp₁s, List.cons_append, List.tail_cons]
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
        have hymem : (⟦y⟧ : Quotient (invSetoid σ hinv)) ∈ c.support := by
          rw [← hp₁supp]
          exact List.mem_map_of_mem (List.mem_of_mem_tail hy1)
        exact hfix y hxy hymem
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

/-- Strict cardinality drop for any nontrivial involution σ (∃ u₀, σ u₀ ≠ u₀). -/
theorem card_invQuot_lt [Fintype V] (σ : V → V) (hinv : ∀ v, σ (σ v) = v)
    [Fintype (Quotient (invSetoid σ hinv))]
    (hnontriv : ∃ u₀ : V, σ u₀ ≠ u₀) :
    Fintype.card (Quotient (invSetoid σ hinv)) < Fintype.card V := by
  classical
  obtain ⟨u₀, hu₀⟩ := hnontriv
  let Q := Quotient (invSetoid σ hinv)
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

/-- NEW (Wave 3, Agent #6): No MinimalBad(G) admits a nontrivial involution whose quotient is Near. -/
theorem no_nontrivial_involution_near_quot [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (σ : V → V) (hinv : ∀ v, σ (σ v) = v) (hnontriv : ∃ u₀ : V, σ u₀ ≠ u₀)
    (haut : ∀ a b, G.Adj a b ↔ G.Adj (σ a) (σ b))
    [Fintype (Quotient (invSetoid σ hinv))]
    [DecidableRel (invQuotGraph G σ hinv).Adj]
    (hnear : Near (invQuotGraph G σ hinv)) : False := by
  have hlt := card_invQuot_lt σ hinv hnontriv
  have hpow : HasPower (invQuotGraph G σ hinv) :=
    hm.2.2.1 (Quotient (invSetoid σ hinv)) (invQuotGraph G σ hinv) hlt hnear
  exact hm.2.1 (hasPower_of_any_invQuot hinv haut hpow)

/-- For any power-free graph, a non-fixed vertex u cannot be adjacent to both v and σ v
    when v is also non-fixed (otherwise u - v - σu - σv - u is a C4). -/
theorem no_parallel_nonfixed {G : SimpleGraph V} (hfree : ¬ HasPower G)
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

/-- Exact quotient degree for a non-fixed vertex u with ¬G.Adj u (σ u) in a power-free graph:
    its quotient degree equals its original degree G.degree u. -/
theorem invQuot_degree_nonfixed [Fintype V] [DecidableEq V]
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
      · have hv_eq : v.1 = σ u := (hinv v.1).symm.trans (congrArg σ h2).symm
        exact hno (hv_eq ▸ (v.2 : G.Adj u v.1)),
      u, v.1, rfl, rfl, v.2⟩⟩
  have hfinj : Function.Injective f := by
    intro a b heq
    apply Subtype.ext
    rcases Quotient.exact (congrArg Subtype.val heq) with h1 | h2
    · exact h1
    · by_cases hbfix : σ b.1 = b.1
      · exact h2.trans hbfix
      · exact False.elim (no_parallel_nonfixed hfree σ hinv haut hu hbfix b.2 (h2 ▸ (a.2 : G.Adj u a.1)))
  have hfsurj : Function.Surjective f := by
    rintro ⟨q, hq⟩
    obtain ⟨v, hvq, huv⟩ := lift_edge_exists haut hq
    exact ⟨⟨v, huv⟩, Subtype.ext hvq⟩
  have hc := Fintype.card_congr (Equiv.ofBijective f ⟨hfinj, hfsurj⟩)
  rw [SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.card_neighborSet_eq_degree] at hc
  exact hc.symm

/-- Exact quotient degree for a fixed vertex u (σ u = u) whose neighbors are all fixed:
    its quotient degree equals its original degree G.degree u. -/
theorem invQuot_degree_fixed_interior [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (σ : V → V) (hinv : ∀ v, σ (σ v) = v)
    (haut : ∀ a b, G.Adj a b ↔ G.Adj (σ a) (σ b))
    [Fintype (Quotient (invSetoid σ hinv))]
    [DecidableRel (invQuotGraph G σ hinv).Adj]
    {u : V} (_hufix : σ u = u) (hallfix : ∀ v, G.Adj u v → σ v = v) :
    (invQuotGraph G σ hinv).degree (⟦u⟧ : Quotient (invSetoid σ hinv)) = G.degree u := by
  classical
  let Q := Quotient (invSetoid σ hinv)
  let H := invQuotGraph G σ hinv
  let f : G.neighborSet u → H.neighborSet (⟦u⟧ : Q) := fun v =>
    ⟨⟦v.1⟧, ⟨fun heq => by
      rcases Quotient.exact heq with h1 | h2
      · exact (G.ne_of_adj v.2) h1
      · exact (G.ne_of_adj v.2) (h2.trans (hallfix v.1 v.2)),
      u, v.1, rfl, rfl, v.2⟩⟩
  have hfinj : Function.Injective f := by
    intro a b heq
    apply Subtype.ext
    rcases Quotient.exact (congrArg Subtype.val heq) with h1 | h2
    · exact h1
    · exact h2.trans (hallfix b.1 b.2)
  have hfsurj : Function.Surjective f := by
    rintro ⟨q, hq⟩
    obtain ⟨v, hvq, huv⟩ := lift_edge_exists haut hq
    exact ⟨⟨v, huv⟩, Subtype.ext hvq⟩
  have hc := Fintype.card_congr (Equiv.ofBijective f ⟨hfinj, hfsurj⟩)
  rw [SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.card_neighborSet_eq_degree] at hc
  exact hc.symm

/-- NEW (Wave 3, Agent #6): Explicit General Involution Exclusion (Boundary-Orbit Bound).
    No MinimalBad(G) admits a nontrivial involution σ such that all orbits except at most
    one orbit `q₀` consist of vertices of degree ≥ 3 that are either:
    (a) non-fixed with ¬G.Adj u (σ u), or (b) fixed with all neighbors fixed. -/
theorem no_involution_le_one_boundary [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (σ : V → V) (hinv : ∀ v, σ (σ v) = v) (hnontriv : ∃ u₀ : V, σ u₀ ≠ u₀)
    (haut : ∀ a b, G.Adj a b ↔ G.Adj (σ a) (σ b))
    (q₀ : Quotient (invSetoid σ hinv))
    (hgood : ∀ u : V, (⟦u⟧ : Quotient (invSetoid σ hinv)) ≠ q₀ →
      3 ≤ G.degree u ∧ ((σ u ≠ u ∧ ¬ G.Adj u (σ u)) ∨ (σ u = u ∧ ∀ v, G.Adj u v → σ v = v)))
    (hex : ∃ u₁ : V, (⟦u₁⟧ : Quotient (invSetoid σ hinv)) ≠ q₀) : False := by
  classical
  let _ : Fintype (Quotient (invSetoid σ hinv)) := Quotient.fintype (invSetoid σ hinv)
  let _ : DecidableRel (invQuotGraph G σ hinv).Adj := fun _ _ => Classical.dec _
  have hdeg3 : ∀ q : Quotient (invSetoid σ hinv), q ≠ q₀ →
      3 ≤ (invQuotGraph G σ hinv).degree q := by
    intro q hq
    obtain ⟨u, rfl⟩ := Quotient.exists_rep q
    obtain ⟨hdu, hcase⟩ := hgood u hq
    rcases hcase with ⟨hu, hno⟩ | ⟨hufix, hallfix⟩
    · rw [invQuot_degree_nonfixed G hm.2.1 σ hinv haut hu hno]; exact hdu
    · rw [invQuot_degree_fixed_interior G σ hinv haut hufix hallfix]; exact hdu
  obtain ⟨u₁, hu₁⟩ := hex
  exact no_nontrivial_involution_near_quot G hm σ hinv hnontriv haut
    ⟨⟨⟦u₁⟧, hdeg3 ⟦u₁⟧ hu₁⟩, ⟨q₀, hdeg3⟩⟩

#print axioms hasPower_of_any_invQuot
#print axioms no_nontrivial_involution_near_quot
#print axioms invQuot_degree_nonfixed
#print axioms invQuot_degree_fixed_interior
#print axioms no_involution_le_one_boundary

end E64GenInvolution
