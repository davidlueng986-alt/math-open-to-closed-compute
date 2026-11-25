import Core
import ClassHSharpCode

/-!
# Wave 3 Agent #2 — Module 2: Generalized Involution & Fixed-Point Quotient Exclusion

Strictly generalizes Wave 2 Agent #6's `no_fpf_involution_le_one_edge` (fixed-point-free involutions)
to ARBITRARY involutions σ ∈ Aut(G) WITH OR WITHOUT FIXED POINTS across ALL 13 open leaves:
1. `hasPower_of_general_invQuot`: For ANY involution σ ∈ Aut(G) on a C4-free graph G,
   every simple 2^k-cycle (k ≥ 2) in G/⟨σ⟩ lifts to a simple 2^k-cycle (if it touches ≥ 1 fixed point
   or has even monodromy on 2-orbits) or a simple 2^(k+1)-cycle (if it avoids fixed points and has
   odd monodromy) in G.
2. `cubic_involution_defect_ge_two`: Every nontrivial involution σ ∈ Aut(G) on a cubic MinimalBad G
   has at least 2 defect orbits (σ-invariant edges + boundary fixed points).
3. `one_defect_no_symmetric_involution`: No one-defect (S or H) MinimalBad G admits a nontrivial
   involution σ fixing only the degree-2 defect w with no σ-invariant edges.
-/

namespace E64Wave3Involution
open SimpleGraph Erdos64Closure E64Core E64Wave3ClassH
universe u

/-- Orbit equivalence relation for an involution σ. -/
def invRel {V : Type u} (σ : V → V) (u v : V) : Prop :=
  u = v ∨ u = σ v

/-- Orbit quotient type V / ⟨σ⟩. -/
abbrev InvOrb {V : Type u} (σ : V → V) := Quot (invRel σ)

/-- Quotient projection V → InvOrb σ. -/
def mkOrb {V : Type u} (σ : V → V) (v : V) : InvOrb σ := Quot.mk (invRel σ) v

lemma mkOrb_eq_iff {V : Type u} {σ : V → V} (hinv : ∀ v, σ (σ v) = v) (u v : V) :
    mkOrb σ u = mkOrb σ v ↔ u = v ∨ u = σ v := by
  constructor
  · intro h
    let s : Setoid V :=
      { r := invRel σ
        iseqv :=
          { refl := fun x => Or.inl rfl
            symm := by
              rintro x y (rfl | rfl)
              · exact Or.inl rfl
              · exact Or.inr (hinv _).symm
            trans := by
              rintro x y z (rfl | rfl) (rfl | rfl)
              · exact Or.inl rfl
              · exact Or.inr rfl
              · exact Or.inr rfl
              · exact Or.inl (hinv _) } }
    have hq : Quotient.mk s u = Quotient.mk s v := h
    exact Quotient.exact hq
  · rintro (rfl | rfl)
    · rfl
    · exact (Quot.sound (Or.inr rfl)).symm

/-- Simple quotient graph G / ⟨σ⟩ (self-loops from invariant edges dropped). -/
def invQuot {V : Type u} (G : SimpleGraph V) (σ : V → V) : SimpleGraph (InvOrb σ) where
  Adj a b := a ≠ b ∧ ∃ u v : V, mkOrb σ u = a ∧ mkOrb σ v = b ∧ G.Adj u v
  symm := fun _ _ ⟨hne, u, v, hu, hv, hadj⟩ => ⟨hne.symm, v, u, hv, hu, hadj.symm⟩
  loopless := fun _ ⟨hne, _⟩ => hne rfl

/-- In a C4-free graph, if mkOrb σ u is adjacent to b in invQuot, then u has a neighbor v with mkOrb σ v = b. -/
lemma invQuot_lift_step {V : Type u} {G : SimpleGraph V} {σ : V → V}
    (hinv : ∀ v, σ (σ v) = v) (hauto : ∀ u v, G.Adj u v → G.Adj (σ u) (σ v))
    {a b : InvOrb σ} (hab : (invQuot G σ).Adj a b) (u : V) (hu : mkOrb σ u = a) :
    ∃ v : V, mkOrb σ v = b ∧ G.Adj u v := by
  obtain ⟨_, u', v', hu', hv', hadj⟩ := hab
  have hrel := (mkOrb_eq_iff hinv u u').mp (hu.trans hu'.symm)
  rcases hrel with rfl | rfl
  · exact ⟨v', hv', hadj⟩
  · exact ⟨σ v', (Quot.sound (Or.inr rfl)).symm.trans hv', hauto u' v' hadj⟩

/-- Lift any walk in invQuot G σ starting at a chosen preimage u0 of the start orbit. -/
lemma invQuot_lift_walk {V : Type u} {G : SimpleGraph V} {σ : V → V}
    (hinv : ∀ v, σ (σ v) = v) (hauto : ∀ u v, G.Adj u v → G.Adj (σ u) (σ v))
    {a b : InvOrb σ} (p : (invQuot G σ).Walk a b) (u0 : V) (hu0 : mkOrb σ u0 = a) :
    ∃ (u1 : V) (q : G.Walk u0 u1),
      mkOrb σ u1 = b ∧ q.length = p.length ∧ q.support.map (mkOrb σ) = p.support := by
  induction p generalizing u0 with
  | nil =>
    exact ⟨u0, Walk.nil, hu0, rfl, by simp [hu0]⟩
  | @cons a b c hab p ih =>
    obtain ⟨u1, hu1, hadj⟩ := invQuot_lift_step hinv hauto hab u0 hu0
    obtain ⟨u2, q, hu2, hlen, hsupp⟩ := ih u1 hu1
    exact ⟨u2, Walk.cons hadj q, hu2, by simp [hlen], by simp [hu0, hsupp]⟩

/-- Copy a walk along equal endpoints preserves length and support. -/
private lemma copy_length_eq {V : Type u} {G : SimpleGraph V} {u v u' v' : V}
    (p : G.Walk u v) (hu : u = u') (hv : v = v') : (p.copy hu hv).length = p.length := by
  subst hu; subst hv; rfl

private lemma copy_support_eq {V : Type u} {G : SimpleGraph V} {u v u' v' : V}
    (p : G.Walk u v) (hu : u = u') (hv : v = v') : (p.copy hu hv).support = p.support := by
  subst hu; subst hv; rfl

/-- Generalized Quotient Cycle Lifting:
    For ANY involution σ ∈ Aut(G) (with or without fixed points!),
    HasPower (invQuot G σ) → HasPower G. -/
theorem hasPower_of_general_invQuot {V : Type u} {G : SimpleGraph V} {σ : V → V}
    (hinv : ∀ v, σ (σ v) = v) (hauto : ∀ u v, G.Adj u v → G.Adj (σ u) (σ v)) :
    HasPower (invQuot G σ) → HasPower G := by
  classical
  rintro ⟨k, a0, c, hk, hcyc, hlen⟩
  -- Pick a preimage u0 of a0; if c visits a fixed point, rotate c to start at that fixed point!
  -- Actually even simpler: lift c starting from ANY u0 with mkOrb σ u0 = a0 to get p1 : u0 → u1!
  -- Case 1: u1 = u0 -> p1 is ALREADY a simple 2^k-cycle in G!
  -- Case 2: u1 = σ u0 (with σ u0 ≠ u0):
  --   Subcase 2a: c visits NO fixed point (every vertex x on p1 has σ x ≠ x).
  --     Then p1 and σ(p1) have disjoint support tails (since mkOrb maps them to the same nodup list,
  --     wait: if p1.support.tail and (σ p1).support.tail shared a vertex z, then z = p1[i] = σ(p1[j]);
  --     applying mkOrb gives c[i] = c[j], so by Nodup of c.support.tail, i = j, hence p1[i] = σ(p1[i]),
  --     a FIXED POINT!!).
  --     So if NO fixed point is on p1, p1 ++ σ(p1) is a simple 2^(k+1)-cycle in G!
  --   Subcase 2b: c DOES visit a fixed point z (σ z = z) on p1!
  --     Rotate c to start at mkOrb σ z! Lifting starting at z ends at u1 with mkOrb σ u1 = mkOrb σ z,
  --     so u1 = z ∨ u1 = σ z = z, hence u1 = z! Thus the lifted walk is a simple 2^k-cycle in G!
  have hlift_from : ∀ (a : InvOrb σ) (c' : (invQuot G σ).Walk a a),
      c'.IsCycle → c'.length = 2 ^ k →
      (∀ u0 : V, mkOrb σ u0 = a →
        (∃ z : V, z ∈ c'.support ∧ σ z = z) → False) ∨ HasPower G := by
    -- Cleaner: do a direct by_cases on whether ∃ z : V, mkOrb σ z ∈ c.support ∧ σ z = z!
    intro _ _ _ _; exact Or.inl (fun _ _ _ => by contradiction)
  by_cases hfix : ∃ z : V, mkOrb σ z ∈ c.support ∧ σ z = z
  · obtain ⟨z, hzmem, hzfix⟩ := hfix
    let c' := c.rotate hzmem
    have hc' : c'.IsCycle := hcyc.rotate hzmem
    have hlen' : c'.length = 2 ^ k := by rw [Walk.length_rotate, hlen]
    obtain ⟨u1, p, hu1, hplen, hpsupp⟩ := invQuot_lift_walk hinv hauto c' z rfl
    have hu1_eq : u1 = z := by
      rcases (mkOrb_eq_iff hinv u1 z).mp hu1 with h | h
      · exact h
      · rw [hzfix] at h; exact h
    let q : G.Walk z z := p.copy rfl hu1_eq
    have hqlen : q.length = 2 ^ k := (copy_length_eq p rfl hu1_eq).trans (hplen.trans hlen')
    have hqtail : q.support.tail.map (mkOrb σ) = c'.support.tail := by
      rw [copy_support_eq, ← List.map_tail, hpsupp]
    have hqnodup : q.support.tail.Nodup := List.Nodup.of_map (mkOrb σ) (hqtail.symm ▸ hc'.support_nodup)
    have hqne : q ≠ Walk.nil := by
      intro h; have : q.length = 0 := by rw [h]; rfl
      have : 0 < 2 ^ k := pow_pos (by decide) _; omega
    exact ⟨k, z, q, hk, Walk.IsCycle.mk_of_support_nodup hqne hqnodup, hqlen⟩
  · -- No fixed point on c!
    obtain ⟨u0, hu0⟩ := Quot.exists_rep a0
    obtain ⟨u1, p1, hu1, hp1len, hp1supp⟩ := invQuot_lift_walk hinv hauto c u0 hu0
    have htail1 : p1.support.tail.map (mkOrb σ) = c.support.tail := by
      rw [← List.map_tail, hp1supp]
    have hnodup1 : p1.support.tail.Nodup := List.Nodup.of_map (mkOrb σ) (htail1.symm ▸ hcyc.support_nodup)
    rcases (mkOrb_eq_iff hinv u1 u0).mp (hu1.trans hu0.symm) with hsame | hflip
    · -- Even monodromy: u1 = u0 -> simple 2^k-cycle!
      let q : G.Walk u0 u0 := p1.copy rfl hsame
      have hqlen : q.length = 2 ^ k := (copy_length_eq p1 rfl hsame).trans (hp1len.trans hlen)
      have hqnodup : q.support.tail.Nodup := by rw [copy_support_eq]; exact hnodup1
      have hqne : q ≠ Walk.nil := by
        intro h; have : q.length = 0 := by rw [h]; rfl
        have : 0 < 2 ^ k := pow_pos (by decide) _; omega
      exact ⟨k, u0, q, hk, Walk.IsCycle.mk_of_support_nodup hqne hqnodup, hqlen⟩
    · -- Odd monodromy: u1 = σ u0 -> concatenate p1 with σ(p1) for a simple 2^(k+1)-cycle!
      let f : G →g G := ⟨σ, fun h => hauto _ _ h⟩
      let p2_raw : G.Walk (σ u0) (σ u1) := p1.map f
      have hσu1 : σ u1 = u0 := by rw [hflip, hinv]
      let p2 : G.Walk u1 u0 := p2_raw.copy hflip.symm hσu1
      let q : G.Walk u0 u0 := p1.append p2
      have hp2len : p2.length = 2 ^ k := by
        rw [copy_length_eq]
        exact (Walk.length_map f p1).trans (hp1len.trans hlen)
      have hqlen : q.length = 2 ^ (k + 1) := by
        simp only [q, Walk.length_append, hp1len, hlen, hp2len, pow_succ]
        omega
      have hp2supp : p2.support = p1.support.map σ := by
        rw [copy_support_eq]; exact Walk.support_map f p1
      have hp2tail : p2.support.tail = p1.support.tail.map σ := by
        rw [hp2supp, ← List.map_tail]
      have hqtail : q.support.tail = p1.support.tail ++ p2.support.tail := by
        simp only [q, Walk.support_append, List.tail_append_of_ne_nil (Walk.support_ne_nil p1)]
      have hnodup2 : p2.support.tail.Nodup := by
        rw [hp2tail]
        exact hnodup1.map (fun x y hxy => by have := congrArg σ hxy; rwa [hinv, hinv] at this)
      have hdisj : p1.support.tail.Disjoint p2.support.tail := by
        intro x hx1 hx2
        rw [hp2tail, List.mem_map] at hx2
        obtain ⟨y, hy1, rfl⟩ := hx2
        -- Both σ y and y are in p1.support.tail, and mkOrb σ (σ y) = mkOrb σ y!
        have horb_eq : mkOrb σ (σ y) = mkOrb σ y := (mkOrb_eq_iff hinv (σ y) y).mpr (Or.inr rfl)
        -- Since p1.support.tail maps injectively (Nodup of mapped list!) under mkOrb σ, σ y = y!
        have hsy_eq_y : σ y = y := by
          have hmap_nd : (p1.support.tail.map (mkOrb σ)).Nodup := htail1.symm ▸ hcyc.support_nodup
          -- If σ y ≠ y, then mkOrb σ maps two distinct elements of p1.support.tail to the same orbit!
          by_contra hne
          -- Use List.nodup_map_iff_inj_on
          exact hne ((List.nodup_map_iff_inj_on hnodup1).mp hmap_nd (σ y) hx1 y hy1 horb_eq)
        have hmem_c : mkOrb σ y ∈ c.support := by
          rw [← hp1supp]
          exact List.mem_map.mpr ⟨y, List.mem_of_mem_tail hy1, rfl⟩
        exact hfix ⟨y, hmem_c, hsy_eq_y⟩
      have hqnodup : q.support.tail.Nodup := by
        rw [hqtail]
        exact List.nodup_append.mpr ⟨hnodup1, hnodup2, hdisj⟩
      have hqne : q ≠ Walk.nil := by
        intro h; have : q.length = 0 := by rw [h]; rfl
        have : 0 < 2 ^ (k + 1) := pow_pos (by decide) _; omega
      exact ⟨k + 1, u0, q, by omega, Walk.IsCycle.mk_of_support_nodup hqne hqnodup, hqlen⟩

/-- Orbit degree formula for a 2-orbit (σ u ≠ u) in a C4-free graph:
    d_{Q}(mkOrb σ u) + (if G.Adj u (σ u) then 1 else 0) = G.degree u. -/
private lemma invQuot_degree_two_orbit {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hc4 : NoC4 G)
    (σ : V → V) (hinv : ∀ v, σ (σ v) = v) (hauto : ∀ u v, G.Adj u v → G.Adj (σ u) (σ v))
    [Fintype (InvOrb σ)] [DecidableRel (invQuot G σ).Adj]
    (u : V) (hmove : σ u ≠ u) :
    (invQuot G σ).degree (mkOrb σ u) + (if G.Adj u (σ u) then 1 else 0) = G.degree u := by
  classical
  -- No two distinct neighbors x, y of u can lie in the same σ-orbit (otherwise y = σ x,
  -- so {x, σ x} ⊆ N(u) ∩ N(σ u), contradicting NoC4 G!).
  have hnb_inj : ∀ x ∈ (G.neighborFinset u).erase (σ u), ∀ y ∈ (G.neighborFinset u).erase (σ u),
      mkOrb σ x = mkOrb σ y → x = y := by
    intro x hx y hy heq
    have hux : G.Adj u x := (G.mem_neighborFinset u x).mp (Finset.mem_erase.mp hx).2
    have huy : G.Adj u y := (G.mem_neighborFinset u y).mp (Finset.mem_erase.mp hy).2
    rcases (mkOrb_eq_iff hinv x y).mp heq with rfl | rfl
    · rfl
    · -- u is adj to y and σ y, so σ u is ALSO adj to σ y and y -> C4!
      have hσuy : G.Adj (σ u) y := by have := hauto u (σ y) hux; rwa [hinv] at this
      have hσuσy : G.Adj (σ u) (σ y) := hauto u y huy
      by_cases hyf : σ y = y
      · exact hyf
      · have hsub : ({y, σ y} : Finset V) ⊆ G.neighborFinset u ∩ G.neighborFinset (σ u) := by
          intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl
          · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset u y).mpr huy, (G.mem_neighborFinset (σ u) y).mpr hσuy⟩
          · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset u (σ y)).mpr hux, (G.mem_neighborFinset (σ u) (σ y)).mpr hσuσy⟩
        have hc := (Finset.card_le_card hsub).trans (hc4 u (σ u) hmove.symm)
        rw [Finset.card_pair (fun h => hyf h.symm)] at hc
        omega
  -- Image of (G.neighborFinset u).erase (σ u) under mkOrb σ is EXACTLY (invQuot G σ).neighborFinset (mkOrb σ u)!
  have himg : ((G.neighborFinset u).erase (σ u)).image (mkOrb σ) = (invQuot G σ).neighborFinset (mkOrb σ u) := by
    ext b
    simp only [Finset.mem_image, Finset.mem_erase, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨x, ⟨hxne, hux⟩, rfl⟩
      refine ⟨?_, u, x, rfl, rfl, hux⟩
      intro heq
      rcases (mkOrb_eq_iff hinv u x).mp heq with rfl | h
      · exact G.loopless u hux
      · exact hxne (by rw [h, hinv])
    · intro hab
      obtain ⟨v, hv, huv⟩ := invQuot_lift_step hinv hauto hab u rfl
      refine ⟨v, ⟨?_, huv⟩, hv⟩
      intro hveq
      exact hab.1 (hv.symm.trans ((mkOrb_eq_iff hinv v u).mpr (Or.inr (by rw [hveq, hinv]))))
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← himg,
    Finset.card_image_of_injOn (fun x hx y hy => hnb_inj x hx y hy)]
  by_cases hself : G.Adj u (σ u)
  · rw [if_pos hself, Finset.card_erase_add_one ((G.mem_neighborFinset u (σ u)).mpr hself),
      SimpleGraph.card_neighborFinset_eq_degree]
  · rw [if_neg hself, add_zero, Finset.erase_eq_of_notMem (fun h => hself ((G.mem_neighborFinset u (σ u)).mp h)),
      SimpleGraph.card_neighborFinset_eq_degree]

/-- Orbit degree bound for a fixed point v (σ v = v) with all neighbors fixed: degree is preserved! -/
private lemma invQuot_degree_interior_fixed {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (σ : V → V) (hinv : ∀ v, σ (σ v) = v) (hauto : ∀ u v, G.Adj u v → G.Adj (σ u) (σ v))
    [Fintype (InvOrb σ)] [DecidableRel (invQuot G σ).Adj]
    (v : V) (hfix : σ v = v) (hall : ∀ x, G.Adj v x → σ x = x) :
    (invQuot G σ).degree (mkOrb σ v) = G.degree v := by
  classical
  have himg : (G.neighborFinset v).image (mkOrb σ) = (invQuot G σ).neighborFinset (mkOrb σ v) := by
    ext b
    simp only [Finset.mem_image, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨x, hvx, rfl⟩
      refine ⟨?_, v, x, rfl, rfl, hvx⟩
      intro heq
      rcases (mkOrb_eq_iff hinv v x).mp heq with rfl | h
      · exact G.loopless v hvx
      · rw [hall x hvx] at h; exact G.loopless v (h ▸ hvx)
    · intro hab
      obtain ⟨x, hx, hvx⟩ := invQuot_lift_step hinv hauto hab v rfl
      exact ⟨x, hvx, hx⟩
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← himg, Finset.card_image_of_injOn,
    SimpleGraph.card_neighborFinset_eq_degree]
  intro x hx y hy heq
  have hvx := (G.mem_neighborFinset v x).mp hx
  have hvy := (G.mem_neighborFinset v y).mp hy
  rcases (mkOrb_eq_iff hinv x y).mp heq with rfl | h
  · rfl
  · rw [hall y hvy] at h; exact h

/-- Orbit cardinality is strictly smaller than |V| whenever σ is nontrivial (∃ u, σ u ≠ u). -/
private lemma card_invOrb_lt {V : Type u} [Fintype V] [DecidableEq V]
    (σ : V → V) (hinv : ∀ v, σ (σ v) = v) (u0 : V) (hmove : σ u0 ≠ u0)
    [Fintype (InvOrb σ)] : Fintype.card (InvOrb σ) < Fintype.card V := by
  classical
  have hsurj : Function.Surjective (mkOrb σ) := Quot.exists_rep
  have hnot_inj : ¬Function.Injective (mkOrb σ) := fun hinj =>
    hmove (hinj ((mkOrb_eq_iff hinv (σ u0) u0).mpr (Or.inr rfl)))
  exact Fintype.card_lt_of_surjective_not_injective (mkOrb σ) hsurj hnot_inj

/-- A defect orbit of an involution σ on G is an orbit a ∈ InvOrb σ that either:
    - comes from a σ-invariant edge {u, σ u} ∈ E(G) (with σ u ≠ u), OR
    - is a boundary fixed point {v} with σ v = v and some neighbor x with σ x ≠ x. -/
def isDefectOrbit {V : Type u} (G : SimpleGraph V) (σ : V → V) (a : InvOrb σ) : Prop :=
  (∃ u : V, mkOrb σ u = a ∧ σ u ≠ u ∧ G.Adj u (σ u)) ∨
  (∃ v : V, mkOrb σ v = a ∧ σ v = v ∧ ∃ x : V, G.Adj v x ∧ σ x ≠ x)

/-- Cubic General Involution Bound:
    In ANY cubic MinimalBad G, EVERY nontrivial involution σ ∈ Aut(G) (with or without fixed points!)
    has at least 2 defect orbits! (Strictly generalizes Wave 2's FPF-only theorem.) -/
theorem cubic_involution_defect_ge_two {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (hcubic : ∀ v : V, G.degree v = 3)
    (σ : V → V) (hinv : ∀ v, σ (σ v) = v) (hauto : ∀ u v, G.Adj u v → G.Adj (σ u) (σ v))
    (hnontriv : ∃ u : V, σ u ≠ u)
    [Fintype (InvOrb σ)] [DecidableRel (invQuot G σ).Adj]
    [DecidablePred (isDefectOrbit G σ)] :
    2 ≤ (Finset.univ.filter (isDefectOrbit G σ)).card := by
  classical
  have hc4 := minimal_bad_noC4 G hm
  obtain ⟨u0, hu0⟩ := hnontriv
  have hlt := card_invOrb_lt σ hinv u0 hu0
  by_contra hle1
  -- Every non-defect orbit has degree 3 in invQuot G σ!
  have hnondef : ∀ a : InvOrb σ, ¬isDefectOrbit G σ a → 3 ≤ (invQuot G σ).degree a := by
    intro a hnd
    obtain ⟨u, rfl⟩ := Quot.exists_rep a
    by_cases hfix : σ u = u
    · have hall : ∀ x, G.Adj u x → σ x = x := by
        intro x hux
        by_contra hmx
        exact hnd (Or.inr ⟨u, rfl, hfix, x, hux, hmx⟩)
      rw [invQuot_degree_interior_fixed G σ hinv hauto u hfix hall, hcubic u]
    · have hnself : ¬G.Adj u (σ u) := fun hadj => hnd (Or.inl ⟨u, rfl, hfix, hadj⟩)
      have hd := invQuot_degree_two_orbit G hc4 σ hinv hauto u hfix
      simp [hnself, hcubic u] at hd
      omega
  -- Check |InvOrb σ| ≥ 2: if |InvOrb σ| ≤ 1, then |V| ≤ 2, impossible since G is cubic (|V| ≥ 4)!
  have hQcard : 2 ≤ Fintype.card (InvOrb σ) := by
    by_contra hlt2
    have hVge4 : 4 ≤ Fintype.card V := by have := G.degree_lt_card_verts u0; rw [hcubic u0] at this; omega
    -- Each orbit has at most 2 elements, so |V| ≤ 2 * |InvOrb σ| ≤ 2, contradiction!
    have hle2 : Fintype.card V ≤ 2 * Fintype.card (InvOrb σ) := by
      have hfib : ∀ a : InvOrb σ, (Finset.univ.filter fun x : V => mkOrb σ x = a).card ≤ 2 := by
        intro a
        obtain ⟨x0, rfl⟩ := Quot.exists_rep a
        have hsub : (Finset.univ.filter fun x : V => mkOrb σ x = mkOrb σ x0) ⊆ {x0, σ x0} := by
          intro x hx
          rcases (mkOrb_eq_iff hinv x x0).mp (Finset.mem_filter.mp hx).2 with rfl | rfl <;> simp
        exact (Finset.card_le_card hsub).trans Finset.card_le_two
      calc Fintype.card V = ∑ a : InvOrb σ, (Finset.univ.filter fun x : V => mkOrb σ x = a).card := by
            rw [← Finset.card_biUnion]
            · congr 1; ext x; simp
            · intro a _ b _ hab
              rw [Finset.disjoint_left]; intro x hxa hxb
              exact hab ((Finset.mem_filter.mp hxa).2.symm.trans (Finset.mem_filter.mp hxb).2)
        _ ≤ ∑ _a : InvOrb σ, 2 := Finset.sum_le_sum fun a _ => hfib a
        _ = 2 * Fintype.card (InvOrb σ) := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]; omega
    omega
  -- Since ≤ 1 defect orbit, invQuot G σ is Near!
  have hnear : Near (invQuot G σ) := by
    by_cases hempty : (Finset.univ.filter (isDefectOrbit G σ)).card = 0
    · exact near_of_except (invQuot G σ) (mkOrb σ u0) hQcard (fun a _ => hnondef a (fun hd => by
        have : a ∈ Finset.univ.filter (isDefectOrbit G σ) := Finset.mem_filter.mpr ⟨Finset.mem_univ a, hd⟩
        rw [Finset.card_eq_zero.mp hempty] at this; exact Finset.notMem_empty a this))
    · have h1 : (Finset.univ.filter (isDefectOrbit G σ)).card = 1 := by omega
      obtain ⟨d0, hd0⟩ := Finset.card_eq_one.mp h1
      exact near_of_except (invQuot G σ) d0 hQcard (fun a ha => hnondef a (fun hd => by
        have : a ∈ Finset.univ.filter (isDefectOrbit G σ) := Finset.mem_filter.mpr ⟨Finset.mem_univ a, hd⟩
        rw [hd0, Finset.mem_singleton] at this; exact ha this))
  exact hm.2.1 (hasPower_of_general_invQuot hinv hauto (hm.2.2.1 (InvOrb σ) (invQuot G σ) hlt hnear))

/-- First symmetry exclusion for all 8 one-defect (S and H) leaves:
    No one-defect MinimalBad G admits a nontrivial involution σ fixing only w
    with no σ-invariant edges. -/
theorem one_defect_no_symmetric_involution {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (w : V) (hw : G.degree w = 2) (hrest : ∀ v : V, v ≠ w → 3 ≤ G.degree v)
    (σ : V → V) (hinv : ∀ v, σ (σ v) = v) (hauto : ∀ u v, G.Adj u v → G.Adj (σ u) (σ v))
    (hfix_only_w : ∀ v : V, σ v = v ↔ v = w)
    (hno_inv_edge : ∀ u : V, ¬G.Adj u (σ u)) : False := by
  classical
  have hc4 := minimal_bad_noC4 G hm
  -- Pick a neighbor b1 of w; since σ w = w and σ b1 ≠ b1, {b1, σ b1} are the two neighbors of w!
  obtain ⟨b1, hwb1⟩ := (G.degree_pos_iff_exists_adj w).mp (by omega : 0 < G.degree w)
  have hb1_ne_w : b1 ≠ w := (G.ne_of_adj hwb1).symm
  have hb1_move : σ b1 ≠ b1 := fun h => hb1_ne_w ((hfix_only_w b1).mp h)
  have hlt := card_invOrb_lt σ hinv b1 hb1_move
  let W := {a : InvOrb σ // a ≠ mkOrb σ w}
  let Q := invQuot G σ
  let _ : DecidableRel Q.Adj := Classical.decRel _
  let H := Q.induce {a : InvOrb σ | a ≠ mkOrb σ w}
  let _ : DecidableRel H.Adj := inferInstanceAs (DecidableRel (Q.induce {a : InvOrb σ | a ≠ mkOrb σ w}).Adj)
  -- Every neighbor of w in G lies in the orbit mkOrb σ b1!
  have hw_nb_orb : ∀ a : InvOrb σ, Q.Adj (mkOrb σ w) a → a = mkOrb σ b1 := by
    intro a hwa
    obtain ⟨v, hv, hwv⟩ := invQuot_lift_step hinv hauto hwa w rfl
    have hwb2 : G.Adj w (σ b1) := by
      have := hauto w b1 hwb1
      rwa [(hfix_only_w w).mpr rfl] at this
    have hsub : ({b1, σ b1} : Finset V) ⊆ G.neighborFinset w := by
      intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact (G.mem_neighborFinset w b1).mpr hwb1
      · exact (G.mem_neighborFinset w (σ b1)).mpr hwb2
    have heq : ({b1, σ b1} : Finset V) = G.neighborFinset w :=
      Finset.eq_of_subset_of_card_le hsub (by
        rw [SimpleGraph.card_neighborFinset_eq_degree, hw, Finset.card_pair hb1_move.symm])
    have hvmem : v ∈ ({b1, σ b1} : Finset V) := heq.symm ▸ (G.mem_neighborFinset w v).mpr hwv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvmem
    rcases hvmem with rfl | rfl
    · exact hv.symm
    · exact hv.symm.trans ((mkOrb_eq_iff hinv (σ b1) b1).mpr (Or.inr rfl))
  -- Every a ∈ W with a ≠ mkOrb σ b1 has H.degree a = Q.degree a = G.degree u ≥ 3!
  have hge3 : ∀ a : W, a.1 ≠ mkOrb σ b1 → 3 ≤ H.degree a := by
    intro a hab1
    have hd := induce_delete_degree Q (mkOrb σ w) a
    change H.degree a + (if Q.Adj a.1 (mkOrb σ w) then 1 else 0) = Q.degree a.1 at hd
    have hna : ¬Q.Adj a.1 (mkOrb σ w) := fun h => hab1 (hw_nb_orb a.1 h.symm)
    simp [hna] at hd
    obtain ⟨u, hu⟩ := Quot.exists_rep a.1
    have huw : u ≠ w := fun h => a.2 (hu.symm.trans (by rw [h]))
    have hmove : σ u ≠ u := fun h => huw ((hfix_only_w u).mp h)
    have hQd := invQuot_degree_two_orbit G hc4 σ hinv hauto u hmove
    simp [hno_inv_edge u] at hQd
    have hu3 := hrest u huw
    rw [← hu] at hd
    omega
  -- Check |W| ≥ 2: b1 has G.degree b1 ≥ 3, so Q.degree (mkOrb σ b1) ≥ 3, so H.degree (mkOrb σ b1) ≥ 2 ⇒ |W| ≥ 3!
  have hb1_orb_ne_w : mkOrb σ b1 ≠ mkOrb σ w := by
    intro h
    rcases (mkOrb_eq_iff hinv b1 w).mp h with h1 | h1
    · exact hb1_ne_w h1
    · rw [(hfix_only_w w).mpr rfl] at h1; exact hb1_ne_w h1
  have hW_ge2 : 2 ≤ Fintype.card W := by
    have hd := induce_delete_degree Q (mkOrb σ w) ⟨mkOrb σ b1, hb1_orb_ne_w⟩
    change H.degree ⟨mkOrb σ b1, hb1_orb_ne_w⟩ + _ = Q.degree (mkOrb σ b1) at hd
    have hQd := invQuot_degree_two_orbit G hc4 σ hinv hauto b1 hb1_move
    simp [hno_inv_edge b1] at hQd
    have hb1_3 := hrest b1 hb1_ne_w
    have hltW := H.degree_lt_card_verts ⟨mkOrb σ b1, hb1_orb_ne_w⟩
    omega
  have hWlt : Fintype.card W < Fintype.card V :=
    (Fintype.card_subtype_le _).trans_lt hlt
  have hnear : Near H :=
    near_of_except H ⟨mkOrb σ b1, hb1_orb_ne_w⟩ hW_ge2 (fun a ha => hge3 a (fun h => ha (Subtype.ext h)))
  have hpowH := hm.2.2.1 W H hWlt hnear
  exact hm.2.1 (hasPower_of_general_invQuot hinv hauto (power_induce Q _ hpowH))

#print axioms hasPower_of_general_invQuot
#print axioms cubic_involution_defect_ge_two
#print axioms one_defect_no_symmetric_involution

end E64Wave3Involution
