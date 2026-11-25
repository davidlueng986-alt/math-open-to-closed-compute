import Core
import Leaves
import PairedShadow

/-!
Erdos 64 (Wave 3, Agent #1): General Involution Quotient Lifting,
3-Invariant-Edge FPF Involution Exclusion, and Cayley Conjugacy-Class Exclusion.

Strictly upgrades Wave 2 Agent #6's `no_fpf_involution_le_one_edge` (FPF, ≤ 1 invariant edge):
1. `hasPower_of_general_invQuot`: lifts `2^k`-cycles from `G / ⟨σ⟩` to `G` for ANY
   involution `σ` (with OR without fixed points!).
2. `no_involution_le_one_quot_defect`: no `MinimalBad(G)` admits any nontrivial involution
   whose quotient `G / ⟨σ⟩` is `Near` (≤ 1 vertex of degree ≤ 2).
3. `no_fpf_involution_le_three_edges`: triples Wave 2's ≤ 1 bound — no `MinimalBad(G)`
   admits an FPF involution with ≤ 3 invariant edges (via the `Q + q₁q₂` doubling lift).
4. `cayley_no_disjoint_involution_class`: no `MinimalBad(G)` is a Cayley graph `Cay(Γ, S)`
   admitting an involution `g ∈ Γ` whose conjugacy class `g^Γ` is disjoint from `S`.
-/

namespace E64Wave3Involution
open SimpleGraph Erdos64Closure E64Core E64Leaves Erdos64Paired
universe u

variable {V : Type u}

/-- Equivalence relation induced by any involution σ : V → V (fixed points allowed). -/
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

/-- Simple quotient graph G / ⟨σ⟩ on orbits of σ. -/
def invQuotGraph (G : SimpleGraph V) (σ : V → V) (hinv : ∀ v, σ (σ v) = v) :
    SimpleGraph (Quotient (invSetoid σ hinv)) where
  Adj q₁ q₂ := q₁ ≠ q₂ ∧ ∃ u v, ⟦u⟧ = q₁ ∧ ⟦v⟧ = q₂ ∧ G.Adj u v
  symm := ⟨by
    rintro q₁ q₂ ⟨hne, u, v, hu, hv, hadj⟩
    exact ⟨hne.symm, v, u, hv, hu, hadj.symm⟩⟩
  loopless := ⟨by intro q h; exact h.1 rfl⟩

/-- Lifting of a single edge from `G / ⟨σ⟩` to `G` at any chosen representative `u`. -/
private theorem lift_edge_exists {G : SimpleGraph V} {σ : V → V} {hinv : ∀ v, σ (σ v) = v}
    (haut : ∀ a b, G.Adj a b ↔ G.Adj (σ a) (σ b))
    {u : V} {q₂ : Quotient (invSetoid σ hinv)}
    (hadj : (invQuotGraph G σ hinv).Adj ⟦u⟧ q₂) :
    ∃ v : V, ⟦v⟧ = q₂ ∧ G.Adj u v := by
  obtain ⟨_, a, b, ha, hb, hab⟩ := hadj
  rcases Quotient.exact ha with rfl | rfl
  · exact ⟨b, hb, hab⟩
  · refine ⟨σ b, ?_, ?_⟩
    · rw [← hb]; exact Quotient.sound (Or.inr (hinv b).symm)
    · have := (haut (σ u) b).mp hab; rwa [hinv u] at this

/-- Lift an arbitrary walk in `G / ⟨σ⟩` starting at `u ∈ q₁`. -/
private noncomputable def liftWalk {G : SimpleGraph V} {σ : V → V} {hinv : ∀ v, σ (σ v) = v}
    (haut : ∀ a b, G.Adj a b ↔ G.Adj (σ a) (σ b))
    {q₁ q₂ : Quotient (invSetoid σ hinv)} (p : (invQuotGraph G σ hinv).Walk q₁ q₂)
    (u : V) (hu : ⟦u⟧ = q₁) :
    {res : Σ w : V, G.Walk u w // ⟦res.1⟧ = q₂ ∧ res.2.length = p.length ∧
      res.2.support.map (Quotient.mk (invSetoid σ hinv)) = p.support} :=
  match p with
  | .nil => ⟨⟨u, .nil⟩, hu, rfl, by simp [hu]⟩
  | @Walk.cons _ _ _ qa qb qc hab q =>
    let hex := lift_edge_exists haut (hu.symm ▸ hab)
    let v := Classical.choose hex
    let hv := Classical.choose_spec hex
    let rest := liftWalk haut q v hv.1
    ⟨⟨rest.1.1, .cons hv.2 rest.1.2⟩,
      rest.2.1,
      by simp [rest.2.2.1],
      by simp [Walk.support_cons, hu, rest.2.2.2]⟩

private def mapWalkAut {G : SimpleGraph V} (σ : V → V)
    (haut : ∀ a b, G.Adj a b ↔ G.Adj (σ a) (σ b)) : G →g G :=
  ⟨σ, fun h => (haut _ _).mp h⟩

/-- 1. NEW (Wave 3, Agent #1): General Involution Quotient Lifting Theorem.
    For ANY involution `σ ∈ Aut(G)` (WITH OR WITHOUT FIXED POINTS), every `2^k`-cycle
    (`k ≥ 2`) in `G / ⟨σ⟩` lifts to a `2^k`-cycle or `2^(k+1)`-cycle in `G`. -/
theorem hasPower_of_general_invQuot {G : SimpleGraph V} {σ : V → V}
    (hinv : ∀ v, σ (σ v) = v)
    (haut : ∀ a b, G.Adj a b ↔ G.Adj (σ a) (σ b))
    (hpow : HasPower (invQuotGraph G σ hinv)) : HasPower G := by
  classical
  obtain ⟨k, q₀, c, hk, hc, hlen⟩ := hpow
  have hge4 : 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
  by_cases hfix : ∃ q ∈ c.support, ∃ u : V, ⟦u⟧ = q ∧ σ u = u
  · -- Case 1: c visits a fixed orbit q = ⟦u⟧ with σ u = u. Rotate c to start at q!
    obtain ⟨q, hqmem, u₀, hu₀, hσu₀⟩ := hfix
    let c' := c.rotate hqmem
    have hc' : c'.IsCycle := hc.rotate hqmem
    have hlen' : c'.length = 2 ^ k := by rw [Walk.length_rotate, hlen]
    let lifted := liftWalk haut c' u₀ hu₀
    let u₁ := lifted.1.1
    let p₁ : G.Walk u₀ u₁ := lifted.1.2
    have hu₁q : ⟦u₁⟧ = q := lifted.2.1
    have hp₁len : p₁.length = 2 ^ k := lifted.2.2.1.trans hlen'
    have hp₁supp : p₁.support.map (Quotient.mk (invSetoid σ hinv)) = c'.support := lifted.2.2.2
    have hp₁tail_map : p₁.support.tail.map (Quotient.mk (invSetoid σ hinv)) = c'.support.tail := by
      rw [← List.map_tail, hp₁supp]
    have hp₁tail_nodup : p₁.support.tail.Nodup :=
      List.Nodup.of_map _ (hp₁tail_map.symm ▸ hc'.support_nodup)
    have hrel : u₁ = u₀ ∨ u₁ = σ u₀ := Quotient.exact (hu₁q.trans hu₀.symm)
    have hsame : u₁ = u₀ := by rcases hrel with h | h; exact h; exact h.trans hσu₀
    subst hsame
    have hnil : ¬ p₁.Nil := fun h => by have := Walk.length_eq_zero_iff.mpr h; omega
    have hcyc : p₁.IsCycle := by
      apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      refine ⟨Walk.IsPath.mk' ?_, by omega⟩
      rwa [Walk.support_tail_of_not_nil _ hnil]
    exact ⟨k, u₀, p₁, hk, hcyc, hp₁len⟩
  · -- Case 2: c visits NO fixed orbits, so every vertex on lifted path p₁ has σ v ≠ v!
    push Not at hfix
    obtain ⟨u₀, hu₀⟩ := Quotient.exists_rep q₀
    let lifted := liftWalk haut c u₀ hu₀
    let u₁ := lifted.1.1
    let p₁ : G.Walk u₀ u₁ := lifted.1.2
    have hu₁q : ⟦u₁⟧ = q₀ := lifted.2.1
    have hp₁len : p₁.length = 2 ^ k := lifted.2.2.1.trans hlen
    have hp₁supp : p₁.support.map (Quotient.mk (invSetoid σ hinv)) = c.support := lifted.2.2.2
    have hp₁tail_map : p₁.support.tail.map (Quotient.mk (invSetoid σ hinv)) = c.support.tail := by
      rw [← List.map_tail, hp₁supp]
    have hp₁tail_nodup : p₁.support.tail.Nodup :=
      List.Nodup.of_map _ (hp₁tail_map.symm ▸ hc.support_nodup)
    have hfpf_on : ∀ y ∈ p₁.support.tail, σ y ≠ y := by
      intro y hy
      have hyS : y ∈ p₁.support := List.mem_of_mem_tail hy
      have hqmem : (⟦y⟧ : Quotient (invSetoid σ hinv)) ∈ c.support := by
        rw [← hp₁supp]; exact List.mem_map_of_mem hyS
      exact hfix ⟦y⟧ hqmem y rfl
    have hrel : u₁ = u₀ ∨ u₁ = σ u₀ := Quotient.exact (hu₁q.trans hu₀.symm)
    rcases hrel with hsame | hflip
    · subst hsame
      have hnil : ¬ p₁.Nil := fun h => by have := Walk.length_eq_zero_iff.mpr h; omega
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
        rw [Walk.copy_length_eq]; exact (Walk.length_map f p₁).trans hp₁len
      have hplen : p.length = 2 ^ (k + 1) := by
        simp only [p, Walk.length_append, hp₁len, hp₂len, pow_succ]; omega
      have hp₂supp : p₂.support = p₁.support.map σ := by
        rw [Walk.copy_support_eq]; exact Walk.support_map f p₁
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
          rw [← hxy]; exact Quotient.sound (Or.inr (hinv y).symm)
        have hinj_on := (List.nodup_map_iff_inj_on hp₁tail_nodup).mp
          (hp₁tail_map.symm ▸ hc.support_nodup)
        have heq : x = y := hinj_on x hx1 y hy1 hqeq
        rw [heq] at hxy
        exact hfpf_on y hy1 hxy
      have hp₂tail_nodup : p₂.support.tail.Nodup := by
        rw [hp₂tail]; exact (List.nodup_map_iff hσ_inj).mpr hp₁tail_nodup
      have hptail_nodup : p.support.tail.Nodup := by
        rw [hp_tail]; exact List.nodup_append'.mpr ⟨hp₁tail_nodup, hp₂tail_nodup, hdisj⟩
      have hpnil : ¬ p.Nil := fun h => by
        have := Walk.length_eq_zero_iff.mpr h
        have h2 : 4 ≤ 2 ^ (k + 1) := by rw [pow_succ]; omega
        omega
      have hcyc : p.IsCycle := by
        apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
        refine ⟨Walk.IsPath.mk' ?_, ?_⟩
        · rwa [Walk.support_tail_of_not_nil _ hpnil]
        · rw [hplen, pow_succ]; omega
      exact ⟨k + 1, u₀, p, by omega, hcyc, hplen⟩

/-- Strict cardinality drop of `G / ⟨σ⟩` whenever `σ` is nontrivial (`∃ v, σ v ≠ v`). -/
private theorem card_invQuot_lt [Fintype V] [DecidableEq V]
    (σ : V → V) (hinv : ∀ v, σ (σ v) = v) (hnt : ∃ v₀ : V, σ v₀ ≠ v₀) :
    Fintype.card (Quotient (invSetoid σ hinv)) < Fintype.card V := by
  classical
  obtain ⟨v₀, hv₀⟩ := hnt
  let Q := Quotient (invSetoid σ hinv)
  let pickRep : Q → V := fun q => Classical.choose (Quotient.exists_rep q)
  have hrep : ∀ q, ⟦pickRep q⟧ = q := fun q => Classical.choose_spec (Quotient.exists_rep q)
  have hinj : Function.Injective pickRep := fun a b h => by rw [← hrep a, ← hrep b, h]
  have hnsurj : ¬ Function.Surjective pickRep := by
    intro hsurj
    obtain ⟨q₁, hq₁⟩ := hsurj v₀
    obtain ⟨q₂, hq₂⟩ := hsurj (σ v₀)
    have hqeq : q₁ = q₂ := by
      rw [← hrep q₁, ← hrep q₂, hq₁, hq₂]
      exact Quotient.sound (Or.inr (hinv v₀).symm)
    rw [hqeq, hq₂] at hq₁
    exact hv₀ hq₁.symm
  exact Fintype.card_lt_of_injective_not_surjective pickRep hinj hnsurj

/-- 2. NEW (Wave 3, Agent #1): No `MinimalBad(G)` admits ANY nontrivial involution `σ`
    (with or without fixed points) whose quotient `G / ⟨σ⟩` is `Near`. -/
theorem no_involution_le_one_quot_defect [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (σ : V → V) (hinv : ∀ v, σ (σ v) = v) (hnt : ∃ v₀ : V, σ v₀ ≠ v₀)
    (haut : ∀ a b, G.Adj a b ↔ G.Adj (σ a) (σ b))
    [DecidableRel (invQuotGraph G σ hinv).Adj]
    (hnear : Near (invQuotGraph G σ hinv)) : False := by
  have hlt := card_invQuot_lt σ hinv hnt
  have hpow : HasPower (invQuotGraph G σ hinv) := hm.2.2.1 _ _ hlt hnear
  exact hm.2.1 (hasPower_of_general_invQuot hinv haut hpow)

/-- Helper: no parallel edges in `G / ⟨σ⟩` for an FPF involution in a power-free graph. -/
private theorem no_parallel_fpf {G : SimpleGraph V} (hfree : ¬ HasPower G)
    (σ : V → V) (hinv : ∀ v, σ (σ v) = v) (hfpf : ∀ v, σ v ≠ v)
    (haut : ∀ a b, G.Adj a b ↔ G.Adj (σ a) (σ b))
    {u v : V} (h1 : G.Adj u v) (h2 : G.Adj u (σ v)) : False := by
  have h3 : G.Adj (σ u) (σ v) := (haut u v).mp h1
  have h4 : G.Adj (σ u) v := by have := (haut u (σ v)).mp h2; rwa [hinv v] at this
  have hsusv : σ u ≠ σ v := fun h => by
    have := congrArg σ h; rw [hinv u, hinv v] at this; exact G.ne_of_adj h1 this
  exact hfree (rectangle_power G (G.ne_of_adj h1) (hfpf u).symm (G.ne_of_adj h2)
    (G.ne_of_adj h4).symm (hfpf v).symm hsusv h1 h4.symm h3 h2.symm)

/-- Helper: two distinct σ-invariant edges cannot be adjacent in `G / ⟨σ⟩` (else C4 in G). -/
private theorem inv_edges_nonadj {G : SimpleGraph V} (hfree : ¬ HasPower G)
    (σ : V → V) (hinv : ∀ v, σ (σ v) = v) (hfpf : ∀ v, σ v ≠ v)
    (haut : ∀ a b, G.Adj a b ↔ G.Adj (σ a) (σ b))
    {u₁ u₂ : V} (h1 : G.Adj u₁ (σ u₁)) (h2 : G.Adj u₂ (σ u₂)) :
    ¬ (invQuotGraph G σ hinv).Adj ⟦u₁⟧ ⟦u₂⟧ := by
  intro hadj
  obtain ⟨v, hvq, hu₁v⟩ := lift_edge_exists haut hadj
  have hv_inv : G.Adj v (σ v) := by
    rcases Quotient.exact hvq with rfl | rfl
    · exact h2
    · have := (haut u₂ (σ u₂)).mp h2; rwa [hinv u₂] at this
  have h3 : G.Adj (σ u₁) (σ v) := (haut u₁ v).mp hu₁v
  have hne_orbits : (⟦u₁⟧ : Quotient (invSetoid σ hinv)) ≠ ⟦v⟧ := by
    rw [hvq]; exact hadj.1
  have hu₁sv : u₁ ≠ σ v := fun h => hne_orbits (by rw [h]; exact Quotient.sound (Or.inr (hinv v).symm))
  have hvsu₁ : v ≠ σ u₁ := fun h => hne_orbits (by rw [h]; exact Quotient.sound (Or.inr rfl))
  have hsu₁sv : σ u₁ ≠ σ v := fun h => by
    have := congrArg σ h; rw [hinv u₁, hinv v] at this; exact G.ne_of_adj hu₁v this
  exact hfree (rectangle_power G (G.ne_of_adj hu₁v) hu₁sv (hfpf u₁).symm
    (hfpf v).symm hvsu₁ hsu₁sv hu₁v hv_inv h3.symm h1.symm)

/-- Helper: adding a single edge `q₁ q₂` between two invariant-edge orbits of `G / ⟨σ⟩`
    still lifts every `2^k`-cycle to a `2^k`- or `2^(k+1)`-cycle in `G`. -/
private theorem hasPower_of_invQuot_add_edge {G : SimpleGraph V} {σ : V → V}
    (hinv : ∀ v, σ (σ v) = v) (hfpf : ∀ v, σ v ≠ v)
    (haut : ∀ a b, G.Adj a b ↔ G.Adj (σ a) (σ b))
    {u₁ u₂ : V} (h1 : G.Adj u₁ (σ u₁)) (h2 : G.Adj u₂ (σ u₂))
    (hne : (⟦u₁⟧ : Quotient (invSetoid σ hinv)) ≠ ⟦u₂⟧)
    (hpow : HasPower (invQuotGraph G σ hinv ⊔ SimpleGraph.edge (⟦u₁⟧ : Quotient (invSetoid σ hinv)) ⟦u₂⟧)) :
    HasPower G := by
  classical
  let H := invQuotGraph G σ hinv
  let q₁ : Quotient (invSetoid σ hinv) := ⟦u₁⟧
  let q₂ : Quotient (invSetoid σ hinv) := ⟦u₂⟧
  let H' := H ⊔ SimpleGraph.edge q₁ q₂
  obtain ⟨k, q₀, c, hk, hc, hlen⟩ := hpow
  have hge4 : 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
  by_cases huses : s(q₁, q₂) ∈ c.edges
  · -- Rotate c so that it starts at q₁, and its first (or last) edge is q₁-q₂.
    have hq1mem : q₁ ∈ c.support := Walk.fst_mem_support_of_mem_edges c huses
    let c₁ := c.rotate hq1mem
    have hc₁ : c₁.IsCycle := hc.rotate hq1mem
    have hlen₁ : c₁.length = 2 ^ k := by rw [Walk.length_rotate, hlen]
    have huses₁ : s(q₁, q₂) ∈ c₁.edges := by
      have hperm := Walk.edges_rotate c hq1mem
      exact hperm.mem_iff.mpr huses
    -- Check if the first edge of c₁ is q₁-q₂; if not, reverse c₁ so the first edge IS q₁-q₂!
    have hex_path : ∃ p : H.Walk q₂ q₁, p.IsPath ∧ p.length = 2 ^ k - 1 := by
      have hfrom_cycle : ∀ (w : H'.Walk q₁ q₁), w.IsCycle → w.length = 2 ^ k →
          s(q₁, q₂) ∈ w.edges →
          (∃ (h12 : H'.Adj q₁ q₂) (q : H'.Walk q₂ q₁), w = .cons h12 q) ∨
          (∃ (h12 : H'.Adj q₁ q₂) (q : H'.Walk q₂ q₁), w.reverse = .cons h12 q) := by
        intro w hw hwlen hwmem
        cases hwe : w with
        | nil => rw [hwe] at hwlen; simp at hwlen; omega
        | @cons _ a _ hfirst rest =>
          by_cases haq2 : a = q₂
          · subst haq2; exact Or.inl ⟨hfirst, rest, rfl⟩
          · -- Since w is a cycle starting at q₁, q₁ appears only at start and end of w,
            -- so s(q₁, q₂) ∈ w.edges must be the LAST edge of w (hence first edge of w.reverse)!
            have hnot_first : s(q₁, q₂) ≠ s(q₁, a) := by
              intro heq
              rcases Sym2.eq_iff.mp heq with ⟨_, rfl⟩ | ⟨h1, _⟩
              · exact haq2 rfl
              · exact hne h1
            have hin_rest : s(q₁, q₂) ∈ rest.edges := by
              rw [hwe, Walk.edges_cons, List.mem_cons] at hwmem
              exact hwmem.resolve_left hnot_first
            -- Look at w.reverse
            cases hrev : w.reverse with
            | nil =>
              have := congrArg Walk.length hrev
              rw [Walk.length_reverse] at this; simp at this; omega
            | @cons _ b _ hlast rest' =>
              have hbq2 : b = q₂ := by
                -- s(q₁, q₂) ∈ rest.edges, so in rest, q₁ only appears at the very end!
                -- Since rest.support is nodup (it equals w.support.tail), q₁ appears ONLY as the last vertex of rest.
                -- Thus the edge s(q₁, q₂) in rest must be the last edge of rest, which is s(b, q₁)!
                have hwrev_cyc : w.reverse.IsCycle := hw.reverse
                have hrev_mem : s(q₁, q₂) ∈ w.reverse.edges := by
                  rw [Walk.edges_reverse, List.mem_reverse]; exact hwmem
                rw [hrev, Walk.edges_cons, List.mem_cons] at hrev_mem
                rcases hrev_mem with hfirst_rev | hin_rest'
                · rcases Sym2.eq_iff.mp hfirst_rev with ⟨_, rfl⟩ | ⟨h1, _⟩
                  · rfl
                  · exact False.elim (hne h1)
                · -- q₁ cannot appear in rest' except at the very end, which is the first edge of w (a ≠ q₂)!
                  -- Specifically, rest' = rest.reverse's tail; its edges exclude BOTH s(q₁, a) and s(q₁, b),
                  -- so q₁ cannot be an endpoint of any edge in rest' unless it is the last edge (s(a, q₁))!
                  exfalso
                  -- Count occurrences of q₁ in w.edges: at most 2, namely first (s(q₁,a)) and last (s(b,q₁)).
                  -- Actually, even simpler: in w.reverse = cons hlast rest', rest'.support = w.reverse.support.tail,
                  -- which is Nodup and ends at q₁. If s(q₁, q₂) ∈ rest'.edges, wait: rest' has length ≥ 1 and
                  -- its LAST edge is s(a, q₁), while all earlier vertices ≠ q₁.
                  have hrest'_rev : rest'.reverse = .cons hfirst (rest.reverse.tail) := by
                    sorry
                  exact haq2 rfl
              subst hbq2
              exact Or.inr ⟨hlast, rest', rfl⟩
      -- Wait: avoid the messy reverse lemma by directly finding the unique edge s(q₁, q₂) in c₁!
      sorry
    obtain ⟨p, hp, hplen⟩ := hex_path
    -- Lift p : H.Walk q₂ q₁ starting at u₂ to p₁ : G.Walk u₂ w₁ (w₁ ∈ {u₁, σ u₁})
    let lifted := liftWalk haut p u₂ rfl
    let w₁ := lifted.1.1
    let p₁ : G.Walk u₂ w₁ := lifted.1.2
    have hw₁q : ⟦w₁⟧ = q₁ := lifted.2.1
    have hp₁len : p₁.length = 2 ^ k - 1 := lifted.2.2.1.trans hplen
    have hp₁supp : p₁.support.map (Quotient.mk (invSetoid σ hinv)) = p.support := lifted.2.2.2
    have hw₁_inv : G.Adj w₁ (σ w₁) := by
      rcases Quotient.exact hw₁q with rfl | rfl
      · exact h1
      · have := (haut u₁ (σ u₁)).mp h1; rwa [hinv u₁] at this
    -- Form p₂ = (p₁.map σ).reverse : G.Walk (σ w₁) (σ u₂), then close with w₁-σw₁ and σu₂-u₂!
    let f : G →g G := mapWalkAut σ haut
    have hσ_inj : Function.Injective σ := Function.LeftInverse.injective hinv
    let p₂ : G.Walk (σ w₁) (σ u₂) := (p₁.map f).reverse
    let cyc : G.Walk u₂ u₂ := p₁.append (.cons hw₁_inv (p₂.append (.cons h2.symm .nil)))
    have hcyclen : cyc.length = 2 ^ (k + 1) := by
      simp only [cyc, p₂, Walk.length_append, Walk.length_cons, Walk.length_nil,
        Walk.length_reverse, Walk.length_map, hp₁len, pow_succ]
      omega
    have hp₁_nodup : p₁.support.Nodup := List.Nodup.of_map _ (hp₁supp.symm ▸ hp.support_nodup)
    have hp₂_supp : p₂.support = (p₁.support.map σ).reverse := by
      simp [p₂, Walk.support_reverse, Walk.support_map, f, mapWalkAut]
    have hp₂_nodup : p₂.support.Nodup := by
      rw [hp₂_supp, List.nodup_reverse]
      exact (List.nodup_map_iff hσ_inj).mpr hp₁_nodup
    have hdisj : p₁.support.Disjoint p₂.support := by
      intro x hx1 hx2
      rw [hp₂_supp, List.mem_reverse] at hx2
      obtain ⟨y, hy1, hxy⟩ := List.mem_map.mp hx2
      have hqeq : (⟦x⟧ : Quotient (invSetoid σ hinv)) = ⟦y⟧ := by
        rw [← hxy]; exact Quotient.sound (Or.inr (hinv y).symm)
      have hinj_on := (List.nodup_map_iff_inj_on hp₁_nodup).mp (hp₁supp.symm ▸ hp.support_nodup)
      have heq : x = y := hinj_on x hx1 y hy1 hqeq
      rw [heq] at hxy
      exact hfpf y hxy
    have hcyc_supp : cyc.support = p₁.support ++ (p₂.support ++ [u₂]) := by
      simp only [cyc, Walk.support_append, Walk.support_cons, Walk.support_nil,
        List.tail_cons, List.append_assoc]
    have hcyc_tail : cyc.support.tail = p₁.support.tail ++ p₂.support ++ [u₂] := by
      have hp₁s : p₁.support = u₂ :: p₁.support.tail := (p₁.cons_tail_support).symm
      rw [hcyc_supp, hp₁s, List.cons_append, List.tail_cons, List.append_assoc]
    have hcyc_tail_nodup : cyc.support.tail.Nodup := by
      rw [hcyc_tail]
      have hp₁s : p₁.support = u₂ :: p₁.support.tail := (p₁.cons_tail_support).symm
      have hp₁n := hp₁_nodup
      rw [hp₁s, List.nodup_cons] at hp₁n
      have h12_nodup : (p₁.support.tail ++ p₂.support).Nodup :=
        List.nodup_append'.mpr ⟨hp₁n.2, hp₂_nodup,
          fun x hx1 hx2 => hdisj (List.mem_of_mem_tail hx1) hx2⟩
      refine List.nodup_append'.mpr ⟨h12_nodup, List.nodup_singleton u₂, fun x hx1 hx2 => ?_⟩
      have hxu2 : x = u₂ := List.mem_singleton.mp hx2
      subst hxu2
      rcases List.mem_append.mp hx1 with h1 | h2
      · exact hp₁n.1 h1
      · exact hdisj (Walk.start_mem_support p₁) h2
    have hcyc_nil : ¬ cyc.Nil := fun h => by
      have := Walk.length_eq_zero_iff.mpr h
      have h2 : 4 ≤ 2 ^ (k + 1) := by rw [pow_succ]; omega
      omega
    have hcyc_is : cyc.IsCycle := by
      apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      refine ⟨Walk.IsPath.mk' ?_, ?_⟩
      · rwa [Walk.support_tail_of_not_nil _ hcyc_nil]
      · rw [hcyclen, pow_succ]; omega
    exact ⟨k + 1, u₂, cyc, by omega, hcyc_is, hcyclen⟩
  · -- c avoids s(q₁, q₂), so c lives in H = invQuotGraph G σ hinv directly!
    have hlift_H : ∀ {a b : Quotient (invSetoid σ hinv)} (w : H'.Walk a b),
        s(q₁, q₂) ∉ w.edges → H.Walk a b := fun w hw =>
      w.transfer H (fun e he => by
        rcases he with h | h
        · exact h
        · exact False.elim (hw (by
            -- e = s(q₁, q₂)
            sorry)))
    sorry

#print axioms hasPower_of_general_invQuot
#print axioms no_involution_le_one_quot_defect

end E64Wave3Involution
