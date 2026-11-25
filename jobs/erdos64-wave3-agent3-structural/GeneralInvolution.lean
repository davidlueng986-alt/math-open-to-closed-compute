import Core
import Leaves
import PairedShadow

/-!
Erdos 64 (Wave 3, Agent #3): General Involution Quotient Theorem (Arbitrary Fixed Points).
Strictly generalizes Wave 2's fixed-point-free involution exclusion (`no_fpf_involution_le_one_edge`)
to ALL nontrivial order-2 automorphisms σ ∈ Aut(G) — with OR without fixed points — across all 13
open MinimalBad leaves (cubic C, subcubic 1-defect S, and high-degree 1-defect H).
-/

namespace E64Wave3Involution
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

/-- Simple quotient graph G / ⟨σ⟩ on the orbits of an arbitrary involution σ. -/
def invQuotGraph (G : SimpleGraph V) (σ : V → V) (hinv : ∀ v, σ (σ v) = v) :
    SimpleGraph (Quotient (invSetoid σ hinv)) where
  Adj q₁ q₂ := q₁ ≠ q₂ ∧ ∃ u v, ⟦u⟧ = q₁ ∧ ⟦v⟧ = q₂ ∧ G.Adj u v
  symm := ⟨by
    rintro q₁ q₂ ⟨hne, u, v, hu, hv, hadj⟩
    exact ⟨hne.symm, v, u, hv, hu, hadj.symm⟩⟩
  loopless := ⟨by intro q h; exact h.1 rfl⟩

/-- In a power-free graph, a non-fixed vertex u cannot be adjacent to both v and σ v
    when v is also non-fixed (otherwise u - v - σ u - σ v - u is a C4). -/
theorem no_parallel_of_nonfixed_involution {G : SimpleGraph V} (hfree : ¬ HasPower G)
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

/-- Lifting a single edge from `G / ⟨σ⟩` to `G` at any chosen representative `u`. -/
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
  | @Walk.cons _ _ _ _ _ hab q =>
    let hex := lift_edge_exists haut (hu.symm ▸ hab)
    let v := Classical.choose hex
    let hv := Classical.choose_spec hex
    let rest := liftWalk haut q v hv.1
    ⟨⟨rest.1.1, .cons hv.2 rest.1.2⟩,
      rest.2.1,
      by simp [rest.2.2.1],
      by simp [Walk.support_cons, hu, rest.2.2.2]⟩

/-- Automorphism homomorphism `G →g G` induced by `σ`. -/
def mapWalkAut {G : SimpleGraph V} (σ : V → V)
    (haut : ∀ a b, G.Adj a b ↔ G.Adj (σ a) (σ b)) : G →g G :=
  ⟨σ, fun h => (haut _ _).mp h⟩

/-- NEW (Wave 3, Agent #3): General Involution Quotient Power-Lifting Theorem.
    For ANY involution automorphism σ of G (with or without fixed points),
    every 2^k-cycle (k ≥ 2) in G / ⟨σ⟩ lifts to a 2^k-cycle or 2^(k+1)-cycle in G. -/
theorem hasPower_of_invQuot_general {G : SimpleGraph V} {σ : V → V}
    (hinv : ∀ v, σ (σ v) = v)
    (haut : ∀ a b, G.Adj a b ↔ G.Adj (σ a) (σ b))
    (hpow : HasPower (invQuotGraph G σ hinv)) : HasPower G := by
  classical
  obtain ⟨k, q₀, c, hk, hc, hlen⟩ := hpow
  have hge4 : 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide : 0 < 2) hk
  by_cases hfix : ∃ f : V, σ f = f ∧ (⟦f⟧ : Quotient (invSetoid σ hinv)) ∈ c.support
  · obtain ⟨f, hff, hfmem⟩ := hfix
    let c' := c.rotate (⟦f⟧ : Quotient (invSetoid σ hinv)) hfmem
    have hc' : c'.IsCycle := hc.rotate hfmem
    have hlen' : c'.length = 2 ^ k := by rw [Walk.length_rotate, hlen]
    let lifted := liftWalk haut c' f rfl
    let u₁ := lifted.1.1
    let p₁ : G.Walk f u₁ := lifted.1.2
    have hu₁q : (⟦u₁⟧ : Quotient (invSetoid σ hinv)) = ⟦f⟧ := lifted.2.1
    have hp₁len : p₁.length = 2 ^ k := lifted.2.2.1.trans hlen'
    have hp₁supp : p₁.support.map (Quotient.mk (invSetoid σ hinv)) = c'.support := lifted.2.2.2
    have hrel : u₁ = f ∨ u₁ = σ f := Quotient.exact hu₁q
    have hsame : u₁ = f := by
      rcases hrel with h | h
      · exact h
      · rwa [hff] at h
    let p₁' : G.Walk f f := p₁.copy rfl hsame
    have hp₁'len : p₁'.length = 2 ^ k := by rw [Walk.length_copy]; exact hp₁len
    have hp₁'supp : p₁'.support = p₁.support := Walk.support_copy p₁ rfl hsame
    have hp₁tail_map : p₁'.support.tail.map (Quotient.mk (invSetoid σ hinv)) = c'.support.tail := by
      rw [hp₁'supp, List.map_tail, hp₁supp]
    have hp₁tail_nodup : p₁'.support.tail.Nodup :=
      List.Nodup.of_map _ (hp₁tail_map.symm ▸ hc'.support_nodup)
    have hnil : ¬ p₁'.Nil := by
      intro h; have := Walk.length_eq_zero_iff.mpr h; omega
    have hcyc : p₁'.IsCycle := by
      apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      refine ⟨Walk.IsPath.mk' ?_, by omega⟩
      rwa [Walk.support_tail_of_not_nil _ hnil]
    exact ⟨k, f, p₁', hk, hcyc, hp₁'len⟩
  · push Not at hfix
    obtain ⟨u₀, hu₀⟩ := Quotient.exists_rep q₀
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
      have hp₁'len : p₁'.length = 2 ^ k := by rw [Walk.length_copy]; exact hp₁len
      have hp₁'supp : p₁'.support = p₁.support := Walk.support_copy p₁ rfl hsame
      have hp₁'nodup : p₁'.support.tail.Nodup := hp₁'supp ▸ hp₁tail_nodup
      have hnil : ¬ p₁'.Nil := by
        intro h; have := Walk.length_eq_zero_iff.mpr h; omega
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
        rw [Walk.length_copy]
        exact (Walk.length_map f p₁).trans hp₁len
      have hplen : p.length = 2 ^ (k + 1) := by
        simp only [p, Walk.length_append, hp₁len, hp₂len, pow_succ]
        omega
      have hp₂supp : p₂.support = p₁.support.map σ := by
        rw [Walk.support_copy]
        exact Walk.support_map f p₁
      have hp₂tail : p₂.support.tail = p₁.support.tail.map σ := by
        rw [hp₂supp, ← List.map_tail]
      have hp_tail : p.support.tail = p₁.support.tail ++ p₂.support.tail := by
        rw [Walk.support_append]
        exact congrArg (fun l => (l ++ p₂.support.tail).tail) (p₁.cons_tail_support).symm
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
          exact List.mem_map.mpr ⟨y, List.mem_of_mem_tail hy1, rfl⟩
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

/-- Exact quotient degree of a non-fixed vertex u not on a flipped edge: unchanged! -/
theorem invQuot_degree_nonfixed [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hfree : ¬ HasPower G)
    (σ : V → V) (hinv : ∀ v, σ (σ v) = v)
    (haut : ∀ a b, G.Adj a b ↔ G.Adj (σ a) (σ b))
    [Fintype (Quotient (invSetoid σ hinv))]
    [DecidableRel (invQuotGraph G σ hinv).Adj]
    {u : V} (hu : σ u ≠ u) (hno : ¬ G.Adj u (σ u)) :
    (invQuotGraph G σ hinv).degree ⟦u⟧ = G.degree u := by
  let Q := Quotient (invSetoid σ hinv)
  let f : G.neighborSet u → (invQuotGraph G σ hinv).neighborSet (⟦u⟧ : Q) := fun v =>
    ⟨⟦v.1⟧, ⟨fun heq => by
      rcases Quotient.exact heq with h1 | h2
      · exact (G.ne_of_adj v.2) h1
      · have hvσu : v.1 = σ u := by
          calc v.1 = σ (σ v.1) := (hinv v.1).symm
            _ = σ u := congrArg σ h2.symm
        exact hno (hvσu ▸ v.2),
      u, v.1, rfl, rfl, v.2⟩⟩
  have hfinj : Function.Injective f := by
    intro a b heq
    apply Subtype.ext
    rcases Quotient.exact (congrArg Subtype.val heq) with h1 | h2
    · exact h1
    · by_cases hbf : σ b.1 = b.1
      · rwa [hbf] at h2
      · exact False.elim (no_parallel_of_nonfixed_involution hfree σ hinv haut hu hbf b.2 (h2 ▸ a.2))
  have hfsurj : Function.Surjective f := by
    rintro ⟨q, hq⟩
    obtain ⟨v, hvq, huv⟩ := lift_edge_exists haut hq
    exact ⟨⟨v, huv⟩, Subtype.ext hvq⟩
  have hc := Fintype.card_congr (Equiv.ofBijective f ⟨hfinj, hfsurj⟩)
  rw [SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.card_neighborSet_eq_degree] at hc
  exact hc.symm

/-- For any fixed vertex f, G.degree f ≤ 2 * (G / ⟨σ⟩).degree ⟦f⟧. -/
theorem invQuot_degree_fixed_double_ge [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (σ : V → V) (hinv : ∀ v, σ (σ v) = v)
    (haut : ∀ a b, G.Adj a b ↔ G.Adj (σ a) (σ b))
    [Fintype (Quotient (invSetoid σ hinv))]
    [DecidableRel (invQuotGraph G σ hinv).Adj]
    {f : V} (hf : σ f = f) :
    G.degree f ≤ 2 * (invQuotGraph G σ hinv).degree ⟦f⟧ := by
  let Q := Quotient (invSetoid σ hinv)
  let rep : (invQuotGraph G σ hinv).neighborSet (⟦f⟧ : Q) → V := fun q =>
    Classical.choose (lift_edge_exists haut q.2)
  have hrep_q : ∀ q, (⟦rep q⟧ : Q) = q.1 := fun q =>
    (Classical.choose_spec (lift_edge_exists haut q.2)).1
  let map2 : (invQuotGraph G σ hinv).neighborSet (⟦f⟧ : Q) × Bool → V := fun p =>
    if p.2 then rep p.1 else σ (rep p.1)
  have hsurj_sub : ∀ v : G.neighborSet f,
      ∃ p : (invQuotGraph G σ hinv).neighborSet (⟦f⟧ : Q) × Bool, map2 p = v.1 := by
    intro v
    have hqadj : (invQuotGraph G σ hinv).Adj (⟦f⟧ : Q) ⟦v.1⟧ := by
      refine ⟨fun heq => ?_, f, v.1, rfl, rfl, v.2⟩
      rcases Quotient.exact heq with h1 | h2
      · exact (G.ne_of_adj v.2) h1
      · have hfv : f = v.1 := by
          calc f = σ f := hf.symm
            _ = σ (σ v.1) := congrArg σ h2
            _ = v.1 := hinv v.1
        exact (G.ne_of_adj v.2) hfv
    let q : (invQuotGraph G σ hinv).neighborSet (⟦f⟧ : Q) := ⟨⟦v.1⟧, hqadj⟩
    have hrel : rep q = v.1 ∨ rep q = σ v.1 := Quotient.exact (hrep_q q)
    rcases hrel with h1 | h2
    · exact ⟨(q, true), by simp [map2, h1]⟩
    · exact ⟨(q, false), by simp [map2, h2, hinv]⟩
  choose g hg using hsurj_sub
  have hginj : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    rw [← hg a, ← hg b, hab]
  have hc := Fintype.card_le_of_injective g hginj
  rw [SimpleGraph.card_neighborSet_eq_degree, Fintype.card_prod,
    SimpleGraph.card_neighborSet_eq_degree, Fintype.card_bool] at hc
  omega

/-- For any fixed vertex f all of whose neighbors are fixed, its quotient degree is unchanged. -/
theorem invQuot_degree_fixed_all_fixed [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (σ : V → V) (hinv : ∀ v, σ (σ v) = v)
    (haut : ∀ a b, G.Adj a b ↔ G.Adj (σ a) (σ b))
    [Fintype (Quotient (invSetoid σ hinv))]
    [DecidableRel (invQuotGraph G σ hinv).Adj]
    {f : V} (_hf : σ f = f) (hall : ∀ v, G.Adj f v → σ v = v) :
    (invQuotGraph G σ hinv).degree ⟦f⟧ = G.degree f := by
  let Q := Quotient (invSetoid σ hinv)
  let φ : G.neighborSet f → (invQuotGraph G σ hinv).neighborSet (⟦f⟧ : Q) := fun v =>
    ⟨⟦v.1⟧, ⟨fun heq => by
      rcases Quotient.exact heq with h1 | h2
      · exact (G.ne_of_adj v.2) h1
      · rw [hall v.1 v.2] at h2; exact (G.ne_of_adj v.2) h2,
      f, v.1, rfl, rfl, v.2⟩⟩
  have hφinj : Function.Injective φ := by
    intro a b heq
    apply Subtype.ext
    rcases Quotient.exact (congrArg Subtype.val heq) with h1 | h2
    · exact h1
    · rw [hall b.1 b.2] at h2; exact h2
  have hφsurj : Function.Surjective φ := by
    rintro ⟨q, hq⟩
    obtain ⟨v, hvq, hfv⟩ := lift_edge_exists haut hq
    exact ⟨⟨v, hfv⟩, Subtype.ext hvq⟩
  have hc := Fintype.card_congr (Equiv.ofBijective φ ⟨hφinj, hφsurj⟩)
  rw [SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.card_neighborSet_eq_degree] at hc
  exact hc.symm

/-- MAIN THEOREM (Wave 3, Agent #3): General Involution Quotient Defect Bound.
    In ANY MinimalBad(G) (cubic C, subcubic 1-defect S, or high-degree 1-defect H),
    for EVERY nontrivial involution automorphism σ (∃ x, σ x ≠ x),
    the quotient graph G / ⟨σ⟩ has at least TWO distinct orbits of degree ≤ 2. -/
theorem general_involution_two_low_orbits [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (σ : V → V) (hinv : ∀ v, σ (σ v) = v) (hnontriv : ∃ x : V, σ x ≠ x)
    (haut : ∀ a b, G.Adj a b ↔ G.Adj (σ a) (σ b))
    [Fintype (Quotient (invSetoid σ hinv))]
    [DecidableRel (invQuotGraph G σ hinv).Adj] :
    ∃ q₁ q₂ : Quotient (invSetoid σ hinv), q₁ ≠ q₂ ∧
      (invQuotGraph G σ hinv).degree q₁ ≤ 2 ∧ (invQuotGraph G σ hinv).degree q₂ ≤ 2 := by
  let Q := Quotient (invSetoid σ hinv)
  let _ : DecidableEq Q := Classical.decEq Q
  obtain ⟨x₀, hx₀⟩ := hnontriv
  have hcard_lt : Fintype.card Q < Fintype.card V := by
    let pickRep : Q → V := fun q => Classical.choose (Quotient.exists_rep q)
    have hrep : ∀ q, (⟦pickRep q⟧ : Q) = q := fun q => Classical.choose_spec (Quotient.exists_rep q)
    have hinj : Function.Injective pickRep := fun a b h => by rw [← hrep a, ← hrep b, h]
    have hnsurj : ¬ Function.Surjective pickRep := by
      intro hsurj
      obtain ⟨q₁, hq₁⟩ := hsurj x₀
      obtain ⟨q₂, hq₂⟩ := hsurj (σ x₀)
      have hqeq : q₁ = q₂ := by
        rw [← hrep q₁, ← hrep q₂, hq₁, hq₂]
        exact Quotient.sound (Or.inr (hinv x₀).symm)
      rw [hqeq, hq₂] at hq₁
      exact hx₀ hq₁
    exact Fintype.card_lt_of_injective_not_surjective pickRep hinj hnsurj
  have hcardQ_ge2 : 2 ≤ Fintype.card Q := by
    obtain ⟨a, ha⟩ := hm.1.1
    have hV4 : 4 ≤ Fintype.card V := by
      have := G.degree_lt_card_verts a
      omega
    let pickRep : Q → V := fun q => Classical.choose (Quotient.exists_rep q)
    have hrep : ∀ q, (⟦pickRep q⟧ : Q) = q := fun q => Classical.choose_spec (Quotient.exists_rep q)
    let f : V → Q × Bool := fun v => (⟦v⟧, decide (v = pickRep ⟦v⟧))
    have hfinj : Function.Injective f := by
      intro u v heq
      have h1 : (⟦u⟧ : Q) = ⟦v⟧ := congrArg Prod.fst heq
      have h2 : decide (u = pickRep ⟦u⟧) = decide (v = pickRep ⟦v⟧) := congrArg Prod.snd heq
      rw [h1] at h2
      have hu : u = pickRep ⟦v⟧ ∨ u = σ (pickRep ⟦v⟧) := Quotient.exact (h1.trans (hrep ⟦v⟧).symm)
      have hv : v = pickRep ⟦v⟧ ∨ v = σ (pickRep ⟦v⟧) := Quotient.exact (hrep ⟦v⟧).symm
      by_cases hp : v = pickRep ⟦v⟧
      · rw [decide_eq_true hp] at h2
        exact (of_decide_eq_true h2).trans hp.symm
      · rw [decide_eq_false hp] at h2
        have hu' : u ≠ pickRep ⟦v⟧ := of_decide_eq_false h2
        rcases hu with h | h
        · exact False.elim (hu' h)
        · rcases hv with hv1 | hv2
          · exact False.elim (hp hv1)
          · exact h.trans hv2.symm
    have hc := Fintype.card_le_of_injective f hfinj
    rw [Fintype.card_prod, Fintype.card_bool] at hc
    omega
  by_contra hno
  push Not at hno
  have hnear : Near (invQuotGraph G σ hinv) := by
    by_cases hex : ∃ q₀ : Q, (invQuotGraph G σ hinv).degree q₀ ≤ 2
    · obtain ⟨q₀, hq₀⟩ := hex
      apply near_of_except (invQuotGraph G σ hinv) q₀ hcardQ_ge2
      intro q hq
      have hgt := hno q₀ q hq.symm hq₀
      omega
    · push Not at hex
      obtain ⟨q₀⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card Q)
      apply near_of_except (invQuotGraph G σ hinv) q₀ hcardQ_ge2
      intro q _
      have := hex q
      omega
  have hpow : HasPower (invQuotGraph G σ hinv) := hm.2.2.1 Q (invQuotGraph G σ hinv) hcard_lt hnear
  exact hm.2.1 (hasPower_of_invQuot_general hinv haut hpow)

/-- COROLLARY 1 (covers all 8 open S/H leaves): No 1-defect MinimalBad(G) admits a nontrivial
    involution σ fixing the unique degree-2 defect w with 0 flipped edges and no other fixed
    vertex of quotient degree ≤ 2. -/
theorem no_defect_fixing_involution_no_other_low [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (w : V) (hw : ∀ v, v ≠ w → 3 ≤ G.degree v)
    (σ : V → V) (hinv : ∀ v, σ (σ v) = v) (hnontriv : ∃ x : V, σ x ≠ x)
    (haut : ∀ a b, G.Adj a b ↔ G.Adj (σ a) (σ b))
    [Fintype (Quotient (invSetoid σ hinv))]
    [DecidableRel (invQuotGraph G σ hinv).Adj]
    (hfixw : σ w = w)
    (hnoflip : ∀ v : V, σ v ≠ v → ¬ G.Adj v (σ v))
    (hno_other_fix : ∀ f : V, σ f = f → f ≠ w → 3 ≤ (invQuotGraph G σ hinv).degree ⟦f⟧) :
    False := by
  obtain ⟨q₁, q₂, hne, h1, h2⟩ := general_involution_two_low_orbits G hm σ hinv hnontriv haut
  have hbad_eq_w : ∀ q : Quotient (invSetoid σ hinv),
      (invQuotGraph G σ hinv).degree q ≤ 2 → q = ⟦w⟧ := by
    intro q hq
    obtain ⟨u, rfl⟩ := Quotient.exists_rep q
    by_cases hfu : σ u = u
    · by_cases huw : u = w
      · rw [huw]
      · have h3 := hno_other_fix u hfu huw
        omega
    · have huw : u ≠ w := fun h => hfu (h ▸ hfixw)
      have hdeg := invQuot_degree_nonfixed G hm.2.1 σ hinv haut hfu (hnoflip u hfu)
      have h3 := hw u huw
      omega
  exact hne ((hbad_eq_w q₁ h1).trans (hbad_eq_w q₂ h2).symm)

/-- COROLLARY 2 (covers all 5 cubic leaves including C-N-R): Every nontrivial involution σ of
    a cubic MinimalBad(G) has at least TWO distinct seam orbits, where a seam orbit is either
    a flipped edge or a boundary fixed vertex (adjacent to a non-fixed vertex). -/
theorem cubic_involution_two_seam_orbits [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G) (hC : Cubic G)
    (σ : V → V) (hinv : ∀ v, σ (σ v) = v) (hnontriv : ∃ x : V, σ x ≠ x)
    (haut : ∀ a b, G.Adj a b ↔ G.Adj (σ a) (σ b)) :
    let Q := Quotient (invSetoid σ hinv)
    let IsSeam : Q → Prop := fun q =>
      (∃ u : V, ⟦u⟧ = q ∧ G.Adj u (σ u)) ∨
      (∃ f : V, ⟦f⟧ = q ∧ σ f = f ∧ ∃ v : V, G.Adj f v ∧ σ v ≠ v)
    ∃ q₁ q₂ : Q, q₁ ≠ q₂ ∧ IsSeam q₁ ∧ IsSeam q₂ := by
  classical
  intro Q IsSeam
  obtain ⟨q₁, q₂, hne, h1, h2⟩ := general_involution_two_low_orbits G hm σ hinv hnontriv haut
  have hseam : ∀ q : Q, (invQuotGraph G σ hinv).degree q ≤ 2 → IsSeam q := by
    intro q hq
    obtain ⟨u, rfl⟩ := Quotient.exists_rep q
    by_cases hfu : σ u = u
    · right
      refine ⟨u, rfl, hfu, ?_⟩
      by_contra hall
      push Not at hall
      have hdeg := invQuot_degree_fixed_all_fixed G σ hinv haut hfu hall
      rw [hC u] at hdeg
      omega
    · left
      refine ⟨u, rfl, ?_⟩
      by_contra hno
      have hdeg := invQuot_degree_nonfixed G hm.2.1 σ hinv haut hfu hno
      rw [hC u] at hdeg
      omega
  exact ⟨q₁, q₂, hne, hseam q₁ h1, hseam q₂ h2⟩

#print axioms no_parallel_of_nonfixed_involution
#print axioms hasPower_of_invQuot_general
#print axioms invQuot_degree_nonfixed
#print axioms invQuot_degree_fixed_double_ge
#print axioms invQuot_degree_fixed_all_fixed
#print axioms general_involution_two_low_orbits
#print axioms no_defect_fixing_involution_no_other_low
#print axioms cubic_involution_two_seam_orbits

end E64Wave3Involution
