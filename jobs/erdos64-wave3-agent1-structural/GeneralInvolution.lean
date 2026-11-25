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

instance instDecidableRelInvSetoid [DecidableEq V] (σ : V → V) (hinv : ∀ v, σ (σ v) = v) :
    DecidableRel (invSetoid σ hinv).r :=
  fun a b => inferInstanceAs (Decidable (a = b ∨ a = σ b))

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
    · rw [← hb]; exact Quotient.sound (Or.inr rfl)
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
  | .cons hab q =>
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
  have hge4 : 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide : 0 < 2) hk
  by_cases hfix : ∃ q ∈ c.support, ∃ u : V, ⟦u⟧ = q ∧ σ u = u
  · obtain ⟨q, hqmem, u₀, hu₀, hσu₀⟩ := hfix
    let c' := c.rotate q hqmem
    have hc' : c'.IsCycle := SimpleGraph.Walk.IsCycle.rotate hqmem hc
    have hlen' : c'.length = 2 ^ k := by rw [Walk.length_rotate, hlen]
    let lifted := liftWalk haut c' u₀ hu₀
    let u₁ := lifted.1.1
    let p₁ : G.Walk u₀ u₁ := lifted.1.2
    have hu₁q : ⟦u₁⟧ = q := lifted.2.1
    have hp₁len : p₁.length = 2 ^ k := lifted.2.2.1.trans hlen'
    have hp₁supp : p₁.support.map (Quotient.mk (invSetoid σ hinv)) = c'.support := lifted.2.2.2
    have hp₁tail_map : p₁.support.tail.map (Quotient.mk (invSetoid σ hinv)) = c'.support.tail := by
      rw [List.map_tail, hp₁supp]
    have hp₁tail_nodup : p₁.support.tail.Nodup :=
      List.Nodup.of_map _ (hp₁tail_map.symm ▸ hc'.support_nodup)
    have hrel : u₁ = u₀ ∨ u₁ = σ u₀ := Quotient.exact (hu₁q.trans hu₀.symm)
    have hsame : u₁ = u₀ := by rcases hrel with h | h; exact h; exact h.trans hσu₀
    let p₁' : G.Walk u₀ u₀ := p₁.copy rfl hsame
    have hp₁'len : p₁'.length = 2 ^ k := by rw [Walk.length_copy, hp₁len]
    have hp₁'tail : p₁'.support.tail.Nodup := by rw [Walk.support_copy]; exact hp₁tail_nodup
    have hnil : ¬ p₁'.Nil := fun h => by have := Walk.length_eq_zero_iff.mpr h; omega
    have hcyc : p₁'.IsCycle := by
      apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      refine ⟨Walk.IsPath.mk' ?_, by omega⟩
      rwa [Walk.support_tail_of_not_nil _ hnil]
    exact ⟨k, u₀, p₁', hk, hcyc, hp₁'len⟩
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
    have hfpf_on : ∀ y ∈ p₁.support.tail, σ y ≠ y := by
      intro y hy
      have hyS : y ∈ p₁.support := List.mem_of_mem_tail hy
      have hqmem : (⟦y⟧ : Quotient (invSetoid σ hinv)) ∈ c.support := by
        rw [← hp₁supp]; exact List.mem_map_of_mem hyS
      exact hfix ⟦y⟧ hqmem y rfl
    have hrel : u₁ = u₀ ∨ u₁ = σ u₀ := Quotient.exact (hu₁q.trans hu₀.symm)
    rcases hrel with hsame | hflip
    · let p₁' : G.Walk u₀ u₀ := p₁.copy rfl hsame
      have hp₁'len : p₁'.length = 2 ^ k := by rw [Walk.length_copy, hp₁len]
      have hp₁'tail : p₁'.support.tail.Nodup := by rw [Walk.support_copy]; exact hp₁tail_nodup
      have hnil : ¬ p₁'.Nil := fun h => by have := Walk.length_eq_zero_iff.mpr h; omega
      have hcyc : p₁'.IsCycle := by
        apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
        refine ⟨Walk.IsPath.mk' ?_, by omega⟩
        rwa [Walk.support_tail_of_not_nil _ hnil]
      exact ⟨k, u₀, p₁', hk, hcyc, hp₁'len⟩
    · let f : G →g G := mapWalkAut σ haut
      have hσ_inj : Function.Injective σ := Function.LeftInverse.injective hinv
      let p₂_raw : G.Walk (σ u₀) (σ u₁) := p₁.map f
      have hσu₁ : σ u₁ = u₀ := by rw [hflip, hinv u₀]
      let p₂ : G.Walk u₁ u₀ := p₂_raw.copy hflip.symm hσu₁
      let p : G.Walk u₀ u₀ := p₁.append p₂
      have hp₂len : p₂.length = 2 ^ k := by
        rw [Walk.length_copy]; exact (Walk.length_map f p₁).trans hp₁len
      have hplen : p.length = 2 ^ (k + 1) := by
        simp only [p, Walk.length_append, hp₁len, hp₂len, pow_succ]; omega
      have hp₂supp : p₂.support = p₁.support.map σ := by
        rw [Walk.support_copy]; exact Walk.support_map f p₁
      have hp₂tail : p₂.support.tail = p₁.support.tail.map σ := by
        rw [hp₂supp, ← List.map_tail]
      have hp_tail : p.support.tail = p₁.support.tail ++ p₂.support.tail := by
        calc p.support.tail = (p₁.support ++ p₂.support.tail).tail := by rw [Walk.support_append]
          _ = (u₀ :: p₁.support.tail ++ p₂.support.tail).tail := by rw [← p₁.cons_tail_support]
          _ = p₁.support.tail ++ p₂.support.tail := rfl
      have hdisj : p₁.support.tail.Disjoint p₂.support.tail := by
        intro x hx1 hx2
        rw [hp₂tail] at hx2
        obtain ⟨y, hy1, hxy⟩ := List.mem_map.mp hx2
        have hqeq : (⟦x⟧ : Quotient (invSetoid σ hinv)) = ⟦y⟧ := by
          rw [← hxy]; exact Quotient.sound (Or.inr rfl)
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
    exact hv₀ hq₁
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
    · exact (haut u₂ (σ u₂)).mp h2
  have h3 : G.Adj (σ u₁) (σ v) := (haut u₁ v).mp hu₁v
  have hne_orbits : (⟦u₁⟧ : Quotient (invSetoid σ hinv)) ≠ ⟦v⟧ := by
    rw [hvq]; exact hadj.1
  have hu₁sv : u₁ ≠ σ v := fun h => hne_orbits (by rw [h]; exact Quotient.sound (Or.inr rfl))
  have hvsu₁ : v ≠ σ u₁ := fun h => hne_orbits (by rw [h]; exact Quotient.sound (Or.inr (hinv u₁).symm))
  have hsu₁sv : σ u₁ ≠ σ v := fun h => by
    have := congrArg σ h; rw [hinv u₁, hinv v] at this; exact G.ne_of_adj hu₁v this
  exact hfree (rectangle_power G (G.ne_of_adj hu₁v) hu₁sv (hfpf u₁).symm
    (hfpf v).symm hvsu₁ hsu₁sv.symm hu₁v hv_inv h3.symm h1.symm)

/-- Helper: transfer a walk in `H ⊔ edge a b` avoiding `s(a, b)` into `H`. -/
private def dropAddedEdge {W : Type u} {H : SimpleGraph W} {a b u w : W}
    (p : (H ⊔ SimpleGraph.edge a b).Walk u w) (havoid : s(a, b) ∉ p.edges) : H.Walk u w :=
  match p with
  | .nil => .nil
  | .cons (u := x) (v := y) hxy q =>
    have hne : s(x, y) ≠ s(a, b) := fun heq =>
      havoid (by rw [Walk.edges_cons, List.mem_cons]; exact Or.inl heq.symm)
    have hH : H.Adj x y := by
      rcases hxy with h | h
      · exact h
      · exfalso
        have hsym : s(x, y) = s(a, b) := by
          rcases h.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rfl
          · exact Sym2.eq_swap
        exact hne hsym
    .cons hH (dropAddedEdge q (fun hm => havoid (by rw [Walk.edges_cons, List.mem_cons]; exact Or.inr hm)))

private theorem length_dropAddedEdge {W : Type u} {H : SimpleGraph W} {a b u w : W}
    (p : (H ⊔ SimpleGraph.edge a b).Walk u w) (havoid : s(a, b) ∉ p.edges) :
    (dropAddedEdge p havoid).length = p.length := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp [dropAddedEdge, ih]

private theorem support_dropAddedEdge {W : Type u} {H : SimpleGraph W} {a b u w : W}
    (p : (H ⊔ SimpleGraph.edge a b).Walk u w) (havoid : s(a, b) ∉ p.edges) :
    (dropAddedEdge p havoid).support = p.support := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp [dropAddedEdge, ih]

/-- Extract a simple `b`-`a` path in `H` of length `c.length - 1` from a cycle `c` in `H ⊔ edge a b`
    that uses `s(a, b)`. -/
private theorem extract_path_in_base {W : Type u} [DecidableEq W]
    {H : SimpleGraph W} {a b v₀ : W} (hab : a ≠ b)
    (c : (H ⊔ SimpleGraph.edge a b).Walk v₀ v₀) (hc : c.IsCycle) (hmem : s(a, b) ∈ c.edges) :
    ∃ p : H.Walk b a, p.IsPath ∧ p.length + 1 = c.length := by
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
      have hnot : s(a, b) ∉ rest.edges := by
        have hnd := hc₁.edges_nodup; rw [hce, Walk.edges_cons, List.nodup_cons] at hnd; exact hnd.1
      let pH := dropAddedEdge rest hnot
      refine ⟨pH, Walk.IsPath.mk' (by rw [support_dropAddedEdge]; exact hrest_path.support_nodup), ?_⟩
      rw [length_dropAddedEdge]; exact hrest_len
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
        have hnot : s(a, b) ∉ rest'.edges := by
          have hnd := hrev_cyc.edges_nodup; rw [hre, Walk.edges_cons, List.nodup_cons] at hnd; exact hnd.1
        let pH := dropAddedEdge rest' hnot
        refine ⟨pH, Walk.IsPath.mk' (by rw [support_dropAddedEdge]; exact hrest'_path.support_nodup), ?_⟩
        rw [length_dropAddedEdge]; exact hrest'_len

/-- Adding a single edge between two σ-invariant-edge orbits in `G / ⟨σ⟩` still lifts
    every `2^k`-cycle (`k ≥ 2`) to a `2^k`- or `2^(k+1)`-cycle in `G`. -/
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
  obtain ⟨k, q₀, c, hk, hc, hlen⟩ := hpow
  have hge4 : 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide : 0 < 2) hk
  by_cases huses : s(q₁, q₂) ∈ c.edges
  · obtain ⟨p, hp, hplen⟩ := extract_path_in_base hne c hc huses
    let lifted := liftWalk haut p u₂ rfl
    let w₁ := lifted.1.1
    let p₁ : G.Walk u₂ w₁ := lifted.1.2
    have hw₁q : ⟦w₁⟧ = q₁ := lifted.2.1
    have hp₁len : p₁.length = 2 ^ k - 1 := by
      have h0 : p₁.length = p.length := lifted.2.2.1
      rw [hlen] at hplen
      omega
    have hp₁supp : p₁.support.map (Quotient.mk (invSetoid σ hinv)) = p.support := lifted.2.2.2
    have hw₁_inv : G.Adj w₁ (σ w₁) := by
      rcases Quotient.exact hw₁q with h | h
      · rw [h]; exact h1
      · rw [h, hinv u₁]; exact h1.symm
    let f : G →g G := mapWalkAut σ haut
    have hσ_inj : Function.Injective σ := Function.LeftInverse.injective hinv
    let p₂ : G.Walk (σ w₁) (σ u₂) := (p₁.map f).reverse
    let cyc : G.Walk u₂ u₂ := p₁.append (.cons hw₁_inv (p₂.append (.cons h2.symm .nil)))
    have hp₂len : p₂.length = 2 ^ k - 1 := by
      rw [Walk.length_reverse, Walk.length_map, hp₁len]
    have hcyclen : cyc.length = 2 ^ (k + 1) := by
      change (p₁.append (.cons hw₁_inv (p₂.append (.cons h2.symm .nil)))).length = 2 ^ (k + 1)
      rw [Walk.length_append, Walk.length_cons, Walk.length_append, Walk.length_cons,
        Walk.length_nil, hp₁len, hp₂len, pow_succ]
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
        rw [← hxy]; exact Quotient.sound (Or.inr rfl)
      have hinj_on := (List.nodup_map_iff_inj_on hp₁_nodup).mp (hp₁supp.symm ▸ hp.support_nodup)
      have heq : x = y := hinj_on x hx1 y hy1 hqeq
      rw [heq] at hxy
      exact hfpf y hxy
    have hcyc_supp : cyc.support = p₁.support ++ (p₂.support ++ [u₂]) := by
      simp only [cyc, Walk.support_append, Walk.support_cons, Walk.support_nil, List.tail_cons]
    have hcyc_tail : cyc.support.tail = p₁.support.tail ++ p₂.support ++ [u₂] := by
      calc cyc.support.tail = (p₁.support ++ (p₂.support ++ [u₂])).tail := by rw [hcyc_supp]
        _ = (u₂ :: p₁.support.tail ++ (p₂.support ++ [u₂])).tail := by rw [← p₁.cons_tail_support]
        _ = p₁.support.tail ++ (p₂.support ++ [u₂]) := rfl
        _ = p₁.support.tail ++ p₂.support ++ [u₂] := (List.append_assoc _ _ _).symm
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
      rcases List.mem_append.mp hx1 with h1' | h2'
      · exact hp₁n.1 h1'
      · exact hdisj (Walk.start_mem_support p₁) h2'
    have hcyc_nil : ¬ cyc.Nil := fun h => by
      have := Walk.length_eq_zero_iff.mpr h
      have h2' : 4 ≤ 2 ^ (k + 1) := by rw [pow_succ]; omega
      omega
    have hcyc_is : cyc.IsCycle := by
      apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      refine ⟨Walk.IsPath.mk' ?_, ?_⟩
      · rwa [Walk.support_tail_of_not_nil _ hcyc_nil]
      · rw [hcyclen, pow_succ]; omega
    exact ⟨k + 1, u₂, cyc, by omega, hcyc_is, hcyclen⟩
  · let cH := dropAddedEdge c huses
    have hcH_len : cH.length = 2 ^ k := (length_dropAddedEdge c huses).trans hlen
    have hcH_tail : cH.support.tail.Nodup := by
      rw [support_dropAddedEdge]; exact hc.support_nodup
    have hcH_nil : ¬ cH.Nil := fun h => by have := Walk.length_eq_zero_iff.mpr h; omega
    have hcH_cyc : cH.IsCycle := by
      apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      refine ⟨Walk.IsPath.mk' ?_, by omega⟩
      rwa [Walk.support_tail_of_not_nil _ hcH_nil]
    exact hasPower_of_general_invQuot hinv haut ⟨k, q₀, cH, hk, hcH_cyc, hcH_len⟩

/-- Helper: exact degree of every vertex in `invQuotGraph` for an FPF involution. -/
private theorem fpf_quot_degree [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (σ : V → V) (hinv : ∀ v, σ (σ v) = v) (hfpf : ∀ v, σ v ≠ v)
    (haut : ∀ a b, G.Adj a b ↔ G.Adj (σ a) (σ b))
    [DecidableRel (invQuotGraph G σ hinv).Adj] (u : V) :
    (invQuotGraph G σ hinv).degree ⟦u⟧ + (if G.Adj u (σ u) then 1 else 0) = G.degree u := by
  classical
  let Q := Quotient (invSetoid σ hinv)
  let H := invQuotGraph G σ hinv
  let f : {v : V // G.Adj u v ∧ v ≠ σ u} → H.neighborSet (⟦u⟧ : Q) := fun v =>
    ⟨⟦v.1⟧, ⟨fun heq => by
      rcases Quotient.exact heq with h1 | h2
      · exact (G.ne_of_adj v.2.1) h1
      · have hv' : v.1 = σ u := by
          have := congrArg σ h2
          rw [hinv v.1] at this
          exact this.symm
        exact v.2.2 hv',
      u, v.1, rfl, rfl, v.2.1⟩⟩
  have hfinj : Function.Injective f := by
    intro a b heq
    apply Subtype.ext
    rcases Quotient.exact (congrArg Subtype.val heq) with h1 | h2
    · exact h1
    · have ha2 : G.Adj u a.1 := a.2.1
      rw [h2] at ha2
      exact False.elim (no_parallel_fpf hm.2.1 σ hinv hfpf haut b.2.1 ha2)
  have hfsurj : Function.Surjective f := by
    rintro ⟨q, hq⟩
    obtain ⟨v, hvq, huv⟩ := lift_edge_exists haut hq
    have hvne : v ≠ σ u := fun h => hq.1 (by rw [← hvq, h]; exact Quotient.sound (Or.inr (hinv u).symm))
    exact ⟨⟨v, huv, hvne⟩, Subtype.ext hvq⟩
  have hc := Fintype.card_congr (Equiv.ofBijective f ⟨hfinj, hfsurj⟩)
  rw [SimpleGraph.card_neighborSet_eq_degree, Fintype.card_subtype] at hc
  have hfil : (Finset.univ.filter (fun v : V => G.Adj u v ∧ v ≠ σ u)) =
      (G.neighborFinset u).erase (σ u) := by
    ext z; simp [SimpleGraph.mem_neighborFinset, and_comm]
  rw [hfil] at hc
  rw [← hc, ← G.card_neighborFinset_eq_degree]
  by_cases h : G.Adj u (σ u)
  · simp only [h, ite_true]
    exact Finset.card_erase_add_one ((G.mem_neighborFinset u (σ u)).mpr h)
  · simp only [h, ite_false, add_zero]
    exact congrArg Finset.card (Finset.erase_eq_of_notMem (by simp [SimpleGraph.mem_neighborFinset, h]))

/-- Helper: adding a non-edge increases degrees of its two endpoints by 1. -/
private theorem degree_sup_nonedge {W : Type u} [Fintype W] [DecidableEq W]
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

/-- 3. NEW (Wave 3, Agent #1): 3-Invariant-Edge FPF Involution Exclusion Theorem.
    Strictly triples Wave 2's ≤ 1 invariant edge bound: NO `MinimalBad(G)` admits a
    fixed-point-free involution `σ` with at most 3 `σ`-invariant edges. -/
theorem no_fpf_involution_le_three_edges [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (σ : V → V) (hinv : ∀ v, σ (σ v) = v) (hfpf : ∀ v, σ v ≠ v)
    (haut : ∀ a b, G.Adj a b ↔ G.Adj (σ a) (σ b))
    (h3edges : ∃ w₁ w₂ w₃ : V, ∀ v : V,
      (⟦v⟧ : Quotient (invSetoid σ hinv)) ≠ ⟦w₁⟧ →
      (⟦v⟧ : Quotient (invSetoid σ hinv)) ≠ ⟦w₂⟧ →
      (⟦v⟧ : Quotient (invSetoid σ hinv)) ≠ ⟦w₃⟧ → ¬ G.Adj v (σ v)) : False := by
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
    · subst v; rw [← hdeg_eq w]; exact hw (σ w) (hfpf w)
    · exact hw v hvw
  let Q := Quotient (invSetoid σ hinv)
  let H := invQuotGraph G σ hinv
  obtain ⟨w₁, w₂, w₃, hw⟩ := h3edges
  have hlt : Fintype.card Q < Fintype.card V := card_invQuot_lt σ hinv ⟨w₁, hfpf w₁⟩
  by_cases hpair : ∃ u₁ u₂ : V, G.Adj u₁ (σ u₁) ∧ G.Adj u₂ (σ u₂) ∧
      (⟦u₁⟧ : Q) ≠ ⟦u₂⟧
  · obtain ⟨u₁, u₂, hu₁, hu₂, hne12⟩ := hpair
    have hthird : ∃ q₃ : Q, ∀ v : V, (⟦v⟧ : Q) ≠ ⟦u₁⟧ → (⟦v⟧ : Q) ≠ ⟦u₂⟧ → (⟦v⟧ : Q) ≠ q₃ →
        ¬ G.Adj v (σ v) := by
      have hu1_in : (⟦u₁⟧ : Q) = ⟦w₁⟧ ∨ (⟦u₁⟧ : Q) = ⟦w₂⟧ ∨ (⟦u₁⟧ : Q) = ⟦w₃⟧ := by
        by_contra h; push Not at h; exact hw u₁ h.1 h.2.1 h.2.2 hu₁
      have hu2_in : (⟦u₂⟧ : Q) = ⟦w₁⟧ ∨ (⟦u₂⟧ : Q) = ⟦w₂⟧ ∨ (⟦u₂⟧ : Q) = ⟦w₃⟧ := by
        by_contra h; push Not at h; exact hw u₂ h.1 h.2.1 h.2.2 hu₂
      rcases hu1_in with h1 | h1 | h1 <;> rcases hu2_in with h2 | h2 | h2
      · exact False.elim (hne12 (h1.trans h2.symm))
      · exact ⟨⟦w₃⟧, fun v hv1 hv2 hv3 => hw v (h1 ▸ hv1) (h2 ▸ hv2) hv3⟩
      · exact ⟨⟦w₂⟧, fun v hv1 hv2 hv3 => hw v (h1 ▸ hv1) hv3 (h2 ▸ hv2)⟩
      · exact ⟨⟦w₃⟧, fun v hv1 hv2 hv3 => hw v (h2 ▸ hv2) (h1 ▸ hv1) hv3⟩
      · exact False.elim (hne12 (h1.trans h2.symm))
      · exact ⟨⟦w₁⟧, fun v hv1 hv2 hv3 => hw v hv3 (h1 ▸ hv1) (h2 ▸ hv2)⟩
      · exact ⟨⟦w₂⟧, fun v hv1 hv2 hv3 => hw v (h2 ▸ hv2) hv3 (h1 ▸ hv1)⟩
      · exact ⟨⟦w₁⟧, fun v hv1 hv2 hv3 => hw v hv3 (h2 ▸ hv2) (h1 ▸ hv1)⟩
      · exact False.elim (hne12 (h1.trans h2.symm))
    obtain ⟨q₃, hq₃⟩ := hthird
    have hnadj : ¬ H.Adj ⟦u₁⟧ ⟦u₂⟧ := inv_edges_nonadj hm.2.1 σ hinv hfpf haut hu₁ hu₂
    let H' := H ⊔ SimpleGraph.edge (⟦u₁⟧ : Q) ⟦u₂⟧
    have hdegH' : ∀ q : Q, q ≠ q₃ → 3 ≤ H'.degree q := by
      intro q hqq₃
      obtain ⟨v, rfl⟩ := Quotient.exists_rep q
      have h1 : H'.degree ⟦v⟧ = H.degree ⟦v⟧ + (if (⟦v⟧ : Q) = ⟦u₁⟧ ∨ (⟦v⟧ : Q) = ⟦u₂⟧ then 1 else 0) := by
        convert degree_sup_nonedge H hne12 hnadj ⟦v⟧
      have h2 : H.degree ⟦v⟧ + (if G.Adj v (σ v) then 1 else 0) = G.degree v := by
        convert fpf_quot_degree G hm σ hinv hfpf haut v
      have h3 := hall3 v
      by_cases hv1 : (⟦v⟧ : Q) = ⟦u₁⟧
      · simp only [hv1, true_or, ite_true] at h1; omega
      · by_cases hv2 : (⟦v⟧ : Q) = ⟦u₂⟧
        · simp only [hv2, or_true, ite_true] at h1; omega
        · have hno : ¬ G.Adj v (σ v) := hq₃ v hv1 hv2 hqq₃
          simp only [hno, ite_false, add_zero] at h2; omega
    have hex_good : ∃ q : Q, q ≠ q₃ := by
      by_cases h13 : (⟦u₁⟧ : Q) = q₃
      · exact ⟨⟦u₂⟧, fun h => hne12 (h13.trans h.symm)⟩
      · exact ⟨⟦u₁⟧, h13⟩
    obtain ⟨q₀, hq₀⟩ := hex_good
    have hnear : Near H' := ⟨⟨q₀, hdegH' q₀ hq₀⟩, ⟨q₃, hdegH'⟩⟩
    have hpow : HasPower H' := hm.2.2.1 Q H' hlt hnear
    exact hm.2.1 (hasPower_of_invQuot_add_edge hinv hfpf haut hu₁ hu₂ hne12 hpow)
  · push Not at hpair
    have hone : ∃ q₀ : Q, ∀ v : V, (⟦v⟧ : Q) ≠ q₀ → ¬ G.Adj v (σ v) := by
      by_cases hex : ∃ u : V, G.Adj u (σ u)
      · obtain ⟨u, hu⟩ := hex
        exact ⟨⟦u⟧, fun v hv hvv => hv (hpair u v hu hvv).symm⟩
      · push Not at hex
        exact ⟨⟦w₁⟧, fun v _ => hex v⟩
    obtain ⟨q₀, hq₀⟩ := hone
    have hV4 : 4 ≤ Fintype.card V := by
      have := G.degree_lt_card_verts w₁; have := hall3 w₁; omega
    have hex_other : ∃ q₁ : Q, q₁ ≠ q₀ := by
      obtain ⟨u₀, rfl⟩ := Quotient.exists_rep q₀
      by_contra h; push Not at h
      have hs : (Finset.univ : Finset V) ⊆ {u₀, σ u₀} := by
        intro v _
        rcases Quotient.exact (h ⟦v⟧) with rfl | rfl <;> simp
      have hc := Finset.card_le_card hs
      have h2 : ({u₀, σ u₀} : Finset V).card ≤ 2 := Finset.card_le_two
      rw [Finset.card_univ] at hc; omega
    obtain ⟨q₁, hq₁⟩ := hex_other
    have hdegH : ∀ q : Q, q ≠ q₀ → 3 ≤ H.degree q := by
      intro q hqq
      obtain ⟨v, rfl⟩ := Quotient.exists_rep q
      have h2 : H.degree ⟦v⟧ + (if G.Adj v (σ v) then 1 else 0) = G.degree v := by
        convert fpf_quot_degree G hm σ hinv hfpf haut v
      have h3 := hall3 v
      simp only [hq₀ v hqq, ite_false, add_zero] at h2; omega
    have hnear : Near H := ⟨⟨q₁, hdegH q₁ hq₁⟩, ⟨q₀, hdegH⟩⟩
    exact no_involution_le_one_quot_defect G hm σ hinv ⟨w₁, hfpf w₁⟩ haut hnear

/-- Cayley graph of a finite group `Γ` with symmetric generating set `S` (`1 ∉ S`). -/
def cayleyGraph (Γ : Type u) [Group Γ] (S : Set Γ)
    (hsym : ∀ s ∈ S, s⁻¹ ∈ S) (h1 : (1 : Γ) ∉ S) : SimpleGraph Γ where
  Adj x y := x⁻¹ * y ∈ S
  symm := ⟨fun x y h => by
    have := hsym _ h
    rwa [mul_inv_rev, inv_inv] at this⟩
  loopless := ⟨fun x h => by simp [h1] at h⟩

/-- 4. NEW (Wave 3, Agent #1): Cayley Conjugacy-Class Involution Exclusion.
    No `MinimalBad` graph is a Cayley graph `Cay(Γ, S)` of a finite group `Γ` admitting
    an involution `g ∈ Γ` (`g ≠ 1`, `g * g = 1`) whose conjugacy class is disjoint from `S`. -/
theorem cayley_no_disjoint_involution_class {Γ : Type u} [Group Γ] [Fintype Γ] [DecidableEq Γ]
    (S : Set Γ) (hsym : ∀ s ∈ S, s⁻¹ ∈ S) (h1 : (1 : Γ) ∉ S)
    [DecidableRel (cayleyGraph Γ S hsym h1).Adj]
    (hm : MinimalBad (cayleyGraph Γ S hsym h1))
    (g : Γ) (hg1 : g ≠ 1) (hg2 : g * g = 1)
    (hdisj : ∀ x : Γ, x⁻¹ * g * x ∉ S) : False := by
  let G := cayleyGraph Γ S hsym h1
  let σ : Γ → Γ := fun x => g * x
  have hinv : ∀ x : Γ, σ (σ x) = x := fun x => by simp [σ, ← mul_assoc, hg2]
  have hfpf : ∀ x : Γ, σ x ≠ x := fun x h =>
    hg1 (mul_right_cancel (b := x) (by simpa [σ] using h))
  have haut : ∀ a b : Γ, G.Adj a b ↔ G.Adj (σ a) (σ b) := fun a b => by
    change a⁻¹ * b ∈ S ↔ (g * a)⁻¹ * (g * b) ∈ S
    have heq : (g * a)⁻¹ * (g * b) = a⁻¹ * b := by
      rw [mul_inv_rev, mul_assoc, ← mul_assoc g⁻¹ g b, inv_mul_cancel, one_mul]
    rw [heq]
  have hno_inv : ∀ x : Γ, ¬ G.Adj x (σ x) := fun x h => by
    change x⁻¹ * (g * x) ∈ S at h
    rw [← mul_assoc] at h
    exact hdisj x h
  exact no_fpf_involution_le_three_edges G hm σ hinv hfpf haut
    ⟨1, 1, 1, fun v _ _ _ => hno_inv v⟩

#print axioms hasPower_of_general_invQuot
#print axioms no_involution_le_one_quot_defect
#print axioms no_fpf_involution_le_three_edges
#print axioms cayley_no_disjoint_involution_class

end E64Wave3Involution
