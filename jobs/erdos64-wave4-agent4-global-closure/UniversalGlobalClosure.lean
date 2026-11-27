import Leaves
import Descent

/-!
Wave 4 Agent #4: Universal Global Contraction & Whole-Problem Closure Bridge
for Erdős Problem #64 (Erdős–Gyárfás Conjecture).

All theorems in this module apply uniformly to ALL 13 remaining nonbipartite
`MinimalBad` leaves (`C-*`, `S-*`, `H-*`) simultaneously, with zero finite-order
restrictions, zero `sorry`, and standard axioms only.
-/

namespace E64Wave4Agent4
open SimpleGraph Erdos64Closure E64Core E64Leaves Erdos64Descent
universe u

/-- No vertex outside `S` has two distinct neighbors inside `S`. -/
def NoMultiAttach {V : Type u} (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ x, x ∉ S → ∀ u ∈ S, ∀ v ∈ S, G.Adj x u → G.Adj x v → u = v

/-- A 2-packing: pairwise distance at least 3 (independent and no common neighbors). -/
def IsTwoPacking {V : Type u} (G : SimpleGraph V) (I : Set V) : Prop :=
  ∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬G.Adj u v ∧ ∀ z, ¬(G.Adj u z ∧ G.Adj v z)

/-- The simple quotient graph obtained by contracting `S` into a single vertex `none`,
    while keeping `Sᶜ` as `some x`. -/
def ContractSet {V : Type u} (G : SimpleGraph V) (S : Set V) :
    SimpleGraph (Option {v : V // v ∉ S}) where
  Adj a b :=
    match a, b with
    | none, none => False
    | none, some x => ∃ u ∈ S, G.Adj u x.1
    | some x, none => ∃ u ∈ S, G.Adj u x.1
    | some x, some y => G.Adj x.1 y.1
  symm := ⟨by
    intro a b h
    cases a with
    | none =>
      cases b with
      | none => exact h
      | some y => exact h
    | some x =>
      cases b with
      | none => exact h
      | some y => exact h.symm⟩
  loopless := ⟨by
    intro a h
    cases a with
    | none => exact h
    | some x => exact G.loopless.irrefl x.1 h⟩

theorem contractSet_adj_some_some {V : Type u} {G : SimpleGraph V} {S : Set V}
    {x y : {v : V // v ∉ S}} (h : (ContractSet G S).Adj (some x) (some y)) :
    G.Adj x.1 y.1 := h

/-- Contracting any set of size at least 2 strictly decreases the vertex count. -/
theorem contractSet_card_lt {V : Type u} [Fintype V] [DecidableEq V]
    (S : Set V) [DecidablePred (· ∈ S)] (hS : 2 ≤ Nat.card S) :
    Fintype.card (Option {v : V // v ∉ S}) < Fintype.card V := by
  classical
  have hS' : 2 ≤ Fintype.card {v : V // v ∈ S} := by
    simpa only [Nat.card_eq_fintype_card] using hS
  have hcompl : Fintype.card {v : V // v ∉ S} = Fintype.card V - Fintype.card {v : V // v ∈ S} :=
    Fintype.card_subtype_compl (fun v => v ∈ S)
  have hle : Fintype.card {v : V // v ∈ S} ≤ Fintype.card V :=
    Fintype.card_subtype_le (fun v => v ∈ S)
  rw [Fintype.card_option]
  omega

/-- Under `NoMultiAttach G S`, every outside vertex preserves its exact degree in `ContractSet G S`. -/
theorem contractSet_degree_some {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Set V) [DecidablePred (· ∈ S)]
    [DecidableRel (ContractSet G S).Adj]
    (hnm : NoMultiAttach G S) (x : {v : V // v ∉ S}) :
    (ContractSet G S).degree (some x) = G.degree x.1 := by
  classical
  let toF : (ContractSet G S).neighborSet (some x) → G.neighborSet x.1 := fun p =>
    match hp : p.1 with
    | none =>
      have h : ∃ u ∈ S, G.Adj u x.1 := by simpa [ContractSet, hp] using p.2
      ⟨Classical.choose h, (Classical.choose_spec h).2.symm⟩
    | some y =>
      ⟨y.1, by simpa [ContractSet, hp] using p.2⟩
  let invF : G.neighborSet x.1 → (ContractSet G S).neighborSet (some x) := fun q =>
    if hq : q.1 ∈ S then
      ⟨none, by exact ⟨q.1, hq, q.2.symm⟩⟩
    else
      ⟨some ⟨q.1, hq⟩, by exact q.2⟩
  let e : (ContractSet G S).neighborSet (some x) ≃ G.neighborSet x.1 :=
    { toFun := toF
      invFun := invF
      left_inv := by
        intro p
        rcases p with ⟨a, ha⟩
        cases a with
        | none =>
          have h : ∃ u ∈ S, G.Adj u x.1 := ha
          have huS : Classical.choose h ∈ S := (Classical.choose_spec h).1
          simp [toF, invF, huS]
        | some y =>
          simp [toF, invF, y.2]
      right_inv := by
        intro q
        rcases q with ⟨w, hw⟩
        by_cases hwS : w ∈ S
        · have hinv : invF ⟨w, hw⟩ = ⟨none, ⟨w, hwS, hw.symm⟩⟩ := by simp [invF, hwS]
          rw [hinv]
          apply Subtype.ext
          have h : ∃ u ∈ S, G.Adj u x.1 := ⟨w, hwS, hw.symm⟩
          have hspec := Classical.choose_spec h
          exact hnm x.1 x.2 (Classical.choose h) hspec.1 w hwS hspec.2.symm hw
        · have hinv : invF ⟨w, hw⟩ = ⟨some ⟨w, hwS⟩, hw⟩ := by simp [invF, hwS]
          rw [hinv]
          rfl }
  calc
    (ContractSet G S).degree (some x)
        = Nat.card ((ContractSet G S).neighborSet (some x)) := by
          rw [Nat.card_eq_fintype_card, (ContractSet G S).card_neighborSet_eq_degree]
    _ = Nat.card (G.neighborSet x.1) := Nat.card_congr e
    _ = G.degree x.1 := by
          rw [Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree]

/-- Sufficient condition for `ContractSet G S` to be `Near` (covers all 13 remaining leaves). -/
theorem contractSet_near {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Set V) [DecidablePred (· ∈ S)]
    [DecidableRel (ContractSet G S).Adj]
    (hG : Near G) (hnm : NoMultiAttach G S)
    (hSc : (Sᶜ : Set V).Nonempty)
    (hnone : 3 ≤ (ContractSet G S).degree none ∨ ∀ x, x ∉ S → 3 ≤ G.degree x) :
    Near (ContractSet G S) := by
  classical
  have hcard2 : 2 ≤ Fintype.card (Option {v : V // v ∉ S}) := by
    obtain ⟨x, hx⟩ := hSc
    have hpos : 0 < Fintype.card {v : V // v ∉ S} := Fintype.card_pos_iff.mpr ⟨⟨x, hx⟩⟩
    rw [Fintype.card_option]
    omega
  rcases hnone with hdeg3 | hall3
  · obtain ⟨w, hw⟩ := hG.2
    by_cases hwS : w ∈ S
    · apply near_of_except (ContractSet G S) none hcard2
      intro z hz
      cases z with
      | none => exact absurd rfl hz
      | some x =>
        rw [contractSet_degree_some G S hnm x]
        exact hw x.1 (fun h => x.2 (h ▸ hwS))
    · apply near_of_except (ContractSet G S) (some ⟨w, hwS⟩) hcard2
      intro z hz
      cases z with
      | none => exact hdeg3
      | some x =>
        rw [contractSet_degree_some G S hnm x]
        apply hw x.1
        intro hxw
        apply hz
        exact congrArg some (Subtype.ext hxw)
  · apply near_of_except (ContractSet G S) none hcard2
    intro z hz
    cases z with
    | none => exact absurd rfl hz
    | some x =>
      rw [contractSet_degree_some G S hnm x]
      exact hall3 x.1 x.2

/-- Lift a walk in `ContractSet G S` that avoids `none` directly to a walk in `G`. -/
def liftWalkAvoiding {V : Type u} {G : SimpleGraph V} {S : Set V} :
    ∀ {x y : {v : V // v ∉ S}} (p : (ContractSet G S).Walk (some x) (some y)),
      none ∉ p.support → G.Walk x.1 y.1
  | _, _, .nil, _ => .nil
  | _, _, .cons (v := none) _ _, h => absurd (by simp) h
  | _, _, .cons (v := some _) hadj q, h =>
      .cons (contractSet_adj_some_some hadj) (liftWalkAvoiding q (fun hm => h (by simp [hm])))

theorem liftWalkAvoiding_length {V : Type u} {G : SimpleGraph V} {S : Set V} :
    ∀ {x y : {v : V // v ∉ S}} (p : (ContractSet G S).Walk (some x) (some y))
      (h : none ∉ p.support),
      (liftWalkAvoiding p h).length = p.length
  | _, _, .nil, _ => by simp [liftWalkAvoiding]
  | _, _, .cons (v := none) _ _, h => absurd (by simp) h
  | _, _, .cons (v := some _) _ q, h => by
      simp only [liftWalkAvoiding, Walk.length_cons]
      rw [liftWalkAvoiding_length q (fun hm => h (by simp [hm]))]

theorem liftWalkAvoiding_support_map {V : Type u} {G : SimpleGraph V} {S : Set V} :
    ∀ {x y : {v : V // v ∉ S}} (p : (ContractSet G S).Walk (some x) (some y))
      (h : none ∉ p.support),
      p.support.map (fun o => o.elim x.1 Subtype.val) = (liftWalkAvoiding p h).support
  | _, _, .nil, _ => by simp [liftWalkAvoiding]
  | _, _, .cons (v := none) _ _, h => absurd (by simp) h
  | x, _, .cons (v := some z) _ q, h => by
      have hq : none ∉ q.support := fun hm => h (by simp [hm])
      have hmap : q.support.map (fun o => o.elim x.1 Subtype.val) =
          q.support.map (fun o => o.elim z.1 Subtype.val) := by
        apply List.map_congr_left
        intro o ho
        cases o with
        | none => exact absurd ho hq
        | some t => rfl
      simp only [liftWalkAvoiding, Walk.support_cons, List.map_cons, Option.elim_some]
      rw [hmap, liftWalkAvoiding_support_map q hq]

theorem liftWalkAvoiding_mem_compl {V : Type u} {G : SimpleGraph V} {S : Set V} :
    ∀ {x y : {v : V // v ∉ S}} (p : (ContractSet G S).Walk (some x) (some y))
      (h : none ∉ p.support),
      ∀ v ∈ (liftWalkAvoiding p h).support, v ∉ S
  | x, _, .nil, _, v, hv => by
      simp only [liftWalkAvoiding, Walk.support_nil, List.mem_singleton] at hv
      exact hv ▸ x.2
  | _, _, .cons (v := none) _ _, h, _, _ => absurd (by simp) h
  | x, _, .cons (v := some _) _ q, h, v, hv => by
      simp only [liftWalkAvoiding, Walk.support_cons, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact x.2
      · exact liftWalkAvoiding_mem_compl q (fun hm => h (by simp [hm])) v hv

theorem liftWalkAvoiding_support_nodup {V : Type u} {G : SimpleGraph V} {S : Set V}
    {x y : {v : V // v ∉ S}} (p : (ContractSet G S).Walk (some x) (some y))
    (h : none ∉ p.support) (hnd : p.support.Nodup) :
    (liftWalkAvoiding p h).support.Nodup := by
  rw [← liftWalkAvoiding_support_map p h]
  refine List.Nodup.map_on ?_ hnd
  intro a ha b hb hab
  cases a with
  | none => exact absurd ha h
  | some xa =>
    cases b with
    | none => exact absurd hb h
    | some xb =>
      simp only [Option.elim_some] at hab
      exact congrArg some (Subtype.ext hab)

theorem liftWalkAvoiding_isCycle {V : Type u} {G : SimpleGraph V} {S : Set V}
    {x : {v : V // v ∉ S}} (c : (ContractSet G S).Walk (some x) (some x))
    (h : none ∉ c.support) (hc : c.IsCycle) :
    (liftWalkAvoiding c h).IsCycle := by
  have hlen : 3 ≤ (liftWalkAvoiding c h).length := by
    rw [liftWalkAvoiding_length]
    exact hc.three_le_length
  have hnil : ¬(liftWalkAvoiding c h).Nil := by
    intro hn
    have hz := Walk.length_eq_zero_iff.mpr hn
    omega
  have htail_eq : (liftWalkAvoiding c h).support.tail =
      c.support.tail.map (fun o => o.elim x.1 Subtype.val) := by
    rw [← liftWalkAvoiding_support_map c h, List.map_tail]
  have htail_nd : (liftWalkAvoiding c h).support.tail.Nodup := by
    rw [htail_eq]
    refine List.Nodup.map_on ?_ hc.support_nodup
    intro a ha b hb hab
    have ha' : a ∈ c.support := List.mem_of_mem_tail ha
    have hb' : b ∈ c.support := List.mem_of_mem_tail hb
    cases a with
    | none => exact absurd ha' h
    | some xa =>
      cases b with
      | none => exact absurd hb' h
      | some xb =>
        simp only [Option.elim_some] at hab
        exact congrArg some (Subtype.ext hab)
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  refine ⟨Walk.IsPath.mk' ?_, hlen⟩
  rwa [Walk.support_tail_of_not_nil _ hnil]

/-- **Universal Subset Contraction Theorem (ALL 13 Remaining Leaves)**:
    In any `MinimalBad G`, any contractible subset `S` (`|S| ≥ 2`, `NoMultiAttach G S`,
    `Near (ContractSet G S)`) admits two distinct vertices `u ≠ v ∈ S` joined by an
    `S`-internally-disjoint simple path of dyadic length `2 ^ k` (`k ≥ 2`). -/
theorem minimal_bad_contractSet_dyadic_ear {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hm : MinimalBad G)
    (S : Set V) [DecidablePred (· ∈ S)]
    [DecidableRel (ContractSet G S).Adj]
    (hS : 2 ≤ Nat.card S) (hnm : NoMultiAttach G S)
    (hSc : (Sᶜ : Set V).Nonempty)
    (hnone : 3 ≤ (ContractSet G S).degree none ∨ ∀ x, x ∉ S → 3 ≤ G.degree x) :
    ∃ (u v : V) (k : ℕ) (p : G.Walk u v),
      u ∈ S ∧ v ∈ S ∧ u ≠ v ∧ 2 ≤ k ∧ p.IsPath ∧ p.length = 2 ^ k ∧
      ∀ w ∈ p.support, w ≠ u → w ≠ v → w ∉ S := by
  classical
  have hlt := contractSet_card_lt S hS
  have hnear := contractSet_near G S hm.1 hnm hSc hnone
  obtain ⟨k, a, c, hk, hc, hlen⟩ := hm.2.2.1 _ (ContractSet G S) hlt hnear
  -- `c` must pass through `none`; otherwise it lifts directly to a `2^k`-cycle in `G`.
  have hmem : none ∈ c.support := by
    by_contra hnot
    cases a with
    | none => exact hnot (Walk.start_mem_support c)
    | some x =>
      exact hm.2.1 ⟨k, x.1, liftWalkAvoiding c hnot, hk,
        liftWalkAvoiding_isCycle c hnot hc, by rw [liftWalkAvoiding_length, hlen]⟩
  -- Rotate `c` so it starts and ends at `none`.
  let c0 : (ContractSet G S).Walk none none := c.rotate none hmem
  have hc0 : c0.IsCycle := Walk.IsCycle.rotate hmem hc
  have hlen0 : c0.length = 2 ^ k := by rw [Walk.length_rotate, hlen]
  have hpow4 : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by decide
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
  -- Peel off the first edge `none → some x`.
  cases hce : c0 with
  | nil =>
    have h0 : c0.length = 0 := by rw [hce]; rfl
    omega
  | @cons _ b _ h1 p1 =>
    cases b with
    | none => exact absurd h1 ((ContractSet G S).loopless.irrefl none)
    | some x =>
      -- Peel off the last edge `some y → none` via `p1.reverse`.
      cases hpe : p1.reverse with
      | @cons _ d _ h2 p2 =>
        cases d with
        | none => exact absurd h2 ((ContractSet G S).loopless.irrefl none)
        | some y =>
          let q : (ContractSet G S).Walk (some x) (some y) := p2.reverse
          have hq_len : q.length = 2 ^ k - 2 := by
            have h1l : c0.length = p1.length + 1 := by simp [hce]
            have h2l : p1.length = p2.length + 1 := by
              have := congrArg Walk.length hpe
              simpa [Walk.length_reverse] using this
            have h3l : q.length = p2.length := Walk.length_reverse p2
            omega
          -- `c0.support.tail = p1.support` is `Nodup` and ends with `none`,
          -- while `p1.reverse.support = none :: p2.support`, so `none ∉ p2.support = q.support.reverse`.
          have hp1_nd : p1.support.Nodup := by
            have hnd := hc0.support_nodup
            simpa [hce] using hnd
          have hp1rev_nd : p1.reverse.support.Nodup := by
            rw [Walk.support_reverse]
            exact List.nodup_reverse.mpr hp1_nd
          have hnone_not_p2 : none ∉ p2.support := by
            rw [hpe, Walk.support_cons, List.nodup_cons] at hp1rev_nd
            exact hp1rev_nd.1
          have hnone_not_q : none ∉ q.support := by
            intro hm
            exact hnone_not_p2 (by simpa [q, Walk.support_reverse] using hm)
          have hq_nd : q.support.Nodup := by
            rw [hpe, Walk.support_cons, List.nodup_cons] at hp1rev_nd
            have hp2_nd : p2.support.Nodup := hp1rev_nd.2
            simpa [q, Walk.support_reverse] using List.nodup_reverse.mpr hp2_nd
          -- Lift `q` to a simple path `qG` in `G` completely outside `S`.
          let qG : G.Walk x.1 y.1 := liftWalkAvoiding q hnone_not_q
          have hqG_len : qG.length = 2 ^ k - 2 := by
            rw [liftWalkAvoiding_length, hq_len]
          have hqG_nd : qG.support.Nodup := liftWalkAvoiding_support_nodup q hnone_not_q hq_nd
          have hqG_compl : ∀ w ∈ qG.support, w ∉ S := liftWalkAvoiding_mem_compl q hnone_not_q
          obtain ⟨u, huS, hux⟩ := h1
          obtain ⟨v, hvS, hvy⟩ := h2
          -- Build the walk `P : u → x → ... → y → v` of length `2^k`.
          let P : G.Walk u v := Walk.cons hux (qG.concat hvy.symm)
          have hP_len : P.length = 2 ^ k := by
            simp only [P, Walk.length_cons, Walk.length_concat, hqG_len]
            omega
          -- If `u = v`, then `P` is a simple `2^k`-cycle in `G`, contradicting `¬HasPower G`.
          have huv : u ≠ v := by
            intro heq
            subst heq
            have hP_tail_nd : P.support.tail.Nodup := by
              have hsup : P.support.tail = qG.support ++ [u] := by
                simp [P, Walk.support_cons, Walk.support_concat]
              rw [hsup, List.nodup_append]
              refine ⟨hqG_nd, List.nodup_singleton u, ?_⟩
              intro a ha b hb
              simp only [List.mem_singleton] at hb
              subst hb
              intro hab
              exact hqG_compl a ha (hab ▸ huS)
            have hP_nil : ¬P.Nil := by
              intro hn
              have := Walk.length_eq_zero_iff.mpr hn
              omega
            have hP_cyc : P.IsCycle := by
              apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
              refine ⟨Walk.IsPath.mk' ?_, by omega⟩
              rwa [Walk.support_tail_of_not_nil _ hP_nil]
            exact hm.2.1 ⟨k, u, P, hk, hP_cyc, hP_len⟩
          -- Hence `u ≠ v` and `P` is a simple `S`-internally-disjoint path of length `2^k`.
          have hP_nd : P.support.Nodup := by
            have hsup : P.support = u :: (qG.support ++ [v]) := by
              simp [P, Walk.support_cons, Walk.support_concat]
            rw [hsup, List.nodup_cons]
            refine ⟨?_, ?_⟩
            · intro hmem_u
              simp only [List.mem_append, List.mem_singleton] at hmem_u
              rcases hmem_u with hmq | rfl
              · exact hqG_compl u hmq huS
              · exact huv rfl
            · rw [List.nodup_append]
              refine ⟨hqG_nd, List.nodup_singleton v, ?_⟩
              intro a ha b hb
              simp only [List.mem_singleton] at hb
              subst hb
              intro hab
              exact hqG_compl a ha (hab ▸ hvS)
          refine ⟨u, v, k, P, huS, hvS, huv, hk, Walk.IsPath.mk' hP_nd, hP_len, ?_⟩
          intro w hw hwu hwv
          have hsup : P.support = u :: (qG.support ++ [v]) := by
            simp [P, Walk.support_cons, Walk.support_concat]
          rw [hsup] at hw
          simp only [List.mem_cons, List.mem_append] at hw
          rcases hw with rfl | hmq | hmv
          · exact absurd rfl hwu
          · exact hqG_compl w hmq
          · simp at hmv
            exact absurd hmv hwv

/-- **Universal 2-Packing Dyadic-Avoidance Theorem (ALL 13 Remaining Leaves)**:
    In any `MinimalBad G`, every 2-packing `I` of size at least 2 admits two distinct
    vertices `u ≠ v ∈ I` joined by an `I`-internally-disjoint simple path of length `2^k`. -/
theorem minimal_bad_two_packing_dyadic_path {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hm : MinimalBad G)
    (I : Set V) [DecidablePred (· ∈ I)]
    [DecidableRel (ContractSet G I).Adj]
    (hI : 2 ≤ Nat.card I) (hpack : IsTwoPacking G I) :
    ∃ (u v : V) (k : ℕ) (p : G.Walk u v),
      u ∈ I ∧ v ∈ I ∧ u ≠ v ∧ 2 ≤ k ∧ p.IsPath ∧ p.length = 2 ^ k ∧
      ∀ w ∈ p.support, w ≠ u → w ≠ v → w ∉ I := by
  classical
  have hnm : NoMultiAttach G I := by
    intro x _ u hu v hv hxu hxv
    by_contra huv
    exact (hpack u hu v hv huv).2 x ⟨hxu.symm, hxv.symm⟩
  -- `I` is independent (since `|I| ≥ 2`), and `G` has a vertex of degree ≥ 3, so `Iᶜ` is nonempty.
  have hIc : (Iᶜ : Set V).Nonempty := by
    obtain ⟨v0, hv0⟩ := hm.1.1
    by_cases hv0I : v0 ∈ I
    · have hpos : 0 < G.degree v0 := by omega
      obtain ⟨y, hy⟩ := (G.degree_pos_iff_exists_adj v0).mp hpos
      refine ⟨y, ?_⟩
      intro hyI
      have hne : v0 ≠ y := G.ne_of_adj hy
      exact (hpack v0 hv0I y hyI hne).1 hy
    · exact ⟨v0, hv0I⟩
  -- `none` has degree at least 3 in `ContractSet G I` because `I` contains a vertex of degree ≥ 3.
  have hdeg_none : 3 ≤ (ContractSet G I).degree none := by
    obtain ⟨w, hw⟩ := hm.1.2
    have hIcard : 2 ≤ Fintype.card {v : V // v ∈ I} := by
      simpa only [Nat.card_eq_fintype_card] using hI
    have hex : ∃ u : {v : V // v ∈ I}, u.1 ≠ w := by
      by_contra hno
      have hall : ∀ u : {v : V // v ∈ I}, u.1 = w := fun u => by
        by_contra hne
        exact hno ⟨u, hne⟩
      have hinj : Function.Injective (fun _ : {v : V // v ∈ I} => ()) := by
        intro a b _
        exact Subtype.ext ((hall a).trans (hall b).symm)
      have hc := Fintype.card_le_of_injective _ hinj
      rw [Fintype.card_unit] at hc
      omega
    obtain ⟨⟨u, huI⟩, huw⟩ := hex
    have hdu : 3 ≤ G.degree u := hw u huw
    let f : G.neighborSet u → (ContractSet G I).neighborSet none := fun y =>
      have hyI : y.1 ∉ I := by
        intro hyI
        exact (hpack u huI y.1 hyI (G.ne_of_adj y.2)).1 y.2
      ⟨some ⟨y.1, hyI⟩, ⟨u, huI, y.2⟩⟩
    have hf : Function.Injective f := by
      intro a b hab
      have hval := congrArg (fun p : (ContractSet G I).neighborSet none => p.1) hab
      simp only [f, Option.some.injEq, Subtype.mk.injEq] at hval
      exact Subtype.ext hval
    have hle : Nat.card (G.neighborSet u) ≤ Nat.card ((ContractSet G I).neighborSet none) :=
      Nat.card_le_card_of_injective f hf
    rw [Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree,
        Nat.card_eq_fintype_card, (ContractSet G I).card_neighborSet_eq_degree] at hle
    omega
  exact minimal_bad_contractSet_dyadic_ear G hm I hI hnm hIc (Or.inl hdeg_none)

/-- **Whole-Problem-Closing Target (`HasSynchronizedContraction`)**:
    `G` admits a contractible subset `S` (`|S| ≥ 2`, `NoMultiAttach G S`, `Near (ContractSet G S)`)
    such that every `S`-internally-disjoint dyadic ear `p` of length `2^k` (`k ≥ 2`) between
    `u ≠ v ∈ S` is matched by a simple `u–v` path `q` of the same length `2^k` lying inside `S`. -/
def HasSynchronizedContraction {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ (S : Set V) (_ : DecidablePred (· ∈ S)) (_ : DecidableRel (ContractSet G S).Adj),
    2 ≤ Nat.card S ∧ NoMultiAttach G S ∧ (Sᶜ : Set V).Nonempty ∧
    (3 ≤ (ContractSet G S).degree none ∨ ∀ x, x ∉ S → 3 ≤ G.degree x) ∧
    ∀ (u v : V) (k : ℕ), u ∈ S → v ∈ S → u ≠ v → 2 ≤ k →
      (∃ p : G.Walk u v, p.IsPath ∧ p.length = 2 ^ k ∧
        ∀ w ∈ p.support, w ≠ u → w ≠ v → w ∉ S) →
      ∃ q : G.Walk u v, q.IsPath ∧ q.length = 2 ^ k ∧ ∀ w ∈ q.support, w ∈ S

/-- Any `HasSynchronizedContraction` contradicts `MinimalBad G` by creating a `2^{k+1}`-cycle. -/
theorem minimal_bad_no_synchronized_contraction {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hm : MinimalBad G) (hsync : HasSynchronizedContraction G) : False := by
  classical
  rcases hsync with ⟨S, hdecS, hdecC, hS, hnm, hSc, hnone, hmatch⟩
  let _ : DecidablePred (· ∈ S) := hdecS
  let _ : DecidableRel (ContractSet G S).Adj := hdecC
  obtain ⟨u, v, k, p, huS, hvS, huv, hk, hp, hplen, hpout⟩ :=
    minimal_bad_contractSet_dyadic_ear G hm S hS hnm hSc hnone
  obtain ⟨q, hq, hqlen, hqin⟩ := hmatch u v k huS hvS huv hk ⟨p, hp, hplen, hpout⟩
  have hdisj : p.support.tail.Disjoint q.reverse.support.tail := by
    intro w hwp hwq
    have hwu : w ≠ u := by
      have hnd := hp.support_nodup
      rw [← p.cons_tail_support, List.nodup_cons] at hnd
      intro h
      exact hnd.1 (h ▸ hwp)
    have hwv : w ≠ v := by
      have hnd := hq.reverse.support_nodup
      rw [← q.reverse.cons_tail_support, List.nodup_cons] at hnd
      intro h
      exact hnd.1 (h ▸ hwq)
    have hw_not_S : w ∉ S := hpout w (List.mem_of_mem_tail hwp) hwu hwv
    have hw_in_S : w ∈ S := by
      have hmq : w ∈ q.reverse.support := List.mem_of_mem_tail hwq
      rw [Walk.support_reverse, List.mem_reverse] at hmq
      exact hqin w hmq
    exact hw_not_S hw_in_S
  obtain ⟨c, hc, hclen⟩ := dyadic_collision p q hp hq hdisj hk hplen hqlen
  exact hm.2.1 ⟨k + 1, u, c, by omega, hc, hclen⟩

/-- **WHOLE-PROBLEM CLOSURE GATE (`Target ==> Full Erdős #64 CLOSED`)**:
    Proving that every `MinimalBad G` admits either a `HasSynchronizedContraction` or a
    `SafeStep` closes the ENTIRE Erdős–Gyárfás Conjecture unconditionally. -/
theorem erdos64_closed_of_global_target
    (hTarget : ∀ (V : Type u) (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj],
      MinimalBad G → HasSynchronizedContraction G ∨ SafeStep G) :
    ∀ (V : Type u) (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj],
      G.minDegree ≥ 3 → ∃ (k : ℕ) (v : V) (c : G.Walk v v),
        k ≥ 2 ∧ c.IsCycle ∧ c.length = 2 ^ k := by
  classical
  intro V G _ _ _ hmin
  by_contra hno
  have hnotpow : ¬HasPower G := hno
  have hne : Nonempty V := by
    by_contra hempty
    have hemp : IsEmpty V := not_nonempty_iff.mp hempty
    have h0 : G.minDegree = 0 := by
      simp [SimpleGraph.minDegree]
    omega
  obtain ⟨v0⟩ := hne
  have hnear : Near G :=
    ⟨⟨v0, le_trans hmin (G.minDegree_le_degree v0)⟩,
     ⟨v0, fun v _ => le_trans hmin (G.minDegree_le_degree v)⟩⟩
  obtain ⟨W, fW, H, dH, hmH⟩ := minimal_bad_exists ⟨V, inferInstance, G, inferInstance, hnear, hnotpow⟩
  let _ : Fintype W := fW
  let _ : DecidableRel H.Adj := dH
  let _ : DecidableEq W := Classical.decEq W
  rcases hTarget W H hmH with hsync | hsafe
  · exact minimal_bad_no_synchronized_contraction H hmH hsync
  · exact no_safe_step H hmH hsafe

#print axioms contractSet_card_lt
#print axioms contractSet_degree_some
#print axioms contractSet_near
#print axioms minimal_bad_contractSet_dyadic_ear
#print axioms minimal_bad_two_packing_dyadic_path
#print axioms minimal_bad_no_synchronized_contraction
#print axioms erdos64_closed_of_global_target

end E64Wave4Agent4
