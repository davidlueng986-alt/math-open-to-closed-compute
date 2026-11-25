import Leaves
import PairedShadow
import ClosedDefectCore

/-!
Wave 2 Agent #5 — Vertex-Identification & Edge-Contraction Dyadic Path/Cycle Theorems.
Proves unconditionally for all finite MinimalBad(G) graphs:
1. Universal Dyadic Path Theorem (dist >= 3 => simple 2^k-path, k >= 2).
2. NEW Cubic Distance-2 Dyadic Path Theorem (dist = 2 with common neighbor c0 => simple 2^k-path avoiding c0).
3. NEW Complete Non-Adjacent Dyadic Path Theorem for all Cubic MinimalBad(G).
4. NEW Universal Edge-Contraction (2^k + 1)-Cycle Theorem (every triangle-free edge lies on a (2^k+1)-cycle).
-/

namespace E64Wave2Ident
open SimpleGraph Erdos64Closure E64Core E64Leaves Erdos64Paired E64DefectCore
open scoped Sym2
universe u

/-- Simple graph on W = {v // v ≠ y} obtained by identifying y into x
    (suppressing loops and parallel edges). -/
def identGraph {V : Type u} (G : SimpleGraph V) (x y : V) :
    SimpleGraph {v : V // v ≠ y} where
  Adj u v := u ≠ v ∧ (G.Adj u.1 v.1 ∨ (u.1 = x ∧ G.Adj y v.1) ∨ (v.1 = x ∧ G.Adj u.1 y))
  symm := by
    rintro u v ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    rcases h with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl h1.symm
    · exact Or.inr (Or.inr ⟨h1, h2.symm⟩)
    · exact Or.inr (Or.inl ⟨h1, h2.symm⟩)
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Lift a walk in identGraph G x y that completely avoids z = ⟨x, hxy⟩ back into G. -/
def liftNoZ {V : Type u} {G : SimpleGraph V} {x y : V} (hxy : x ≠ y)
    {a b : {v : V // v ≠ y}} (q : (identGraph G x y).Walk a b)
    (hq : ∀ u ∈ q.support, u ≠ ⟨x, hxy⟩) : G.Walk a.1 b.1 :=
  match q with
  | .nil => .nil
  | .cons (v := m) hadj rest =>
    have ha : a ≠ ⟨x, hxy⟩ := hq a (by simp)
    have hm : m ≠ ⟨x, hxy⟩ := hq m (by simp)
    have hG : G.Adj a.1 m.1 := by
      rcases hadj.2 with h | ⟨hax, _⟩ | ⟨hmx, _⟩
      · exact h
      · exact False.elim (ha (Subtype.ext hax))
      · exact False.elim (hm (Subtype.ext hmx))
    .cons hG (liftNoZ hxy rest (fun u hu => hq u (by simp [hu])))

theorem length_liftNoZ {V : Type u} {G : SimpleGraph V} {x y : V} (hxy : x ≠ y)
    {a b : {v : V // v ≠ y}} (q : (identGraph G x y).Walk a b)
    (hq : ∀ u ∈ q.support, u ≠ ⟨x, hxy⟩) :
    (liftNoZ hxy q hq).length = q.length := by
  induction q with
  | nil => rfl
  | cons hadj rest ih =>
    simp only [liftNoZ, Walk.length_cons]
    rw [ih]

theorem support_liftNoZ {V : Type u} {G : SimpleGraph V} {x y : V} (hxy : x ≠ y)
    {a b : {v : V // v ≠ y}} (q : (identGraph G x y).Walk a b)
    (hq : ∀ u ∈ q.support, u ≠ ⟨x, hxy⟩) :
    (liftNoZ hxy q hq).support = q.support.map Subtype.val := by
  induction q with
  | nil => rfl
  | cons hadj rest ih =>
    simp only [liftNoZ, Walk.support_cons, List.map_cons]
    rw [ih]

/-- Decompose a cycle starting at z into its first neighbor a, last neighbor b,
    and internal path m : Walk a b avoiding z. -/
theorem decompose_cycle_at_start {W : Type u} {H : SimpleGraph W} {z : W}
    (d : H.Walk z z) (hd : d.IsCycle) :
    ∃ (a b : W) (hza : H.Adj z a) (hbz : H.Adj b z) (m : H.Walk a b),
      m.length + 2 = d.length ∧
      m.support.Nodup ∧
      (∀ u ∈ m.support, u ≠ z) ∧
      (∀ u ∈ m.support, u ∈ d.support) ∧
      a ∈ m.support ∧ b ∈ m.support := by
  cases d with
  | nil => exact False.elim (hd.ne_nil rfl)
  | @cons _ a _ hza q =>
    cases hqr : q.reverse with
    | nil =>
      have hlen := hd.three_le_length
      have hqnil : q.length = 0 := by
        have := congrArg Walk.length hqr
        simp at this
        exact this
      simp [Walk.length_cons, hqnil] at hlen
    | @cons _ b _ hzb r =>
      let m : H.Walk a b := r.reverse
      have hq_eq : q = m.append (.cons hzb.symm .nil) := by
        have h1 : q = q.reverse.reverse := (Walk.reverse_reverse q).symm
        rw [hqr] at h1
        simpa [m, Walk.reverse_cons] using h1
      have hlen : m.length + 2 = (Walk.cons hza q).length := by
        rw [Walk.length_cons, hq_eq, Walk.length_append]
        simp
        omega
      have htail_nodup : q.support.Nodup := by
        have h := hd.support_nodup
        simpa [Walk.support_cons] using h
      have hq_supp : q.support = m.support ++ [z] := by
        rw [hq_eq, Walk.support_append]
        simp [Walk.support_cons]
      rw [hq_supp] at htail_nodup
      have hm_nodup : m.support.Nodup := (List.nodup_append.mp htail_nodup).1
      have hm_noZ : ∀ u ∈ m.support, u ≠ z := by
        intro u hu heq
        subst heq
        exact (List.nodup_append.mp htail_nodup).2.2 z hu z (by simp) rfl
      have hm_sub : ∀ u ∈ m.support, u ∈ (Walk.cons hza q).support := by
        intro u hu
        rw [Walk.support_cons, hq_supp]
        exact List.mem_cons_of_mem z (List.mem_append_left [z] hu)
      exact ⟨a, b, hza, hzb.symm, m, hlen, hm_nodup, hm_noZ, hm_sub,
        Walk.start_mem_support m, Walk.end_mem_support m⟩

/-- Unified cycle-lifting engine: any 2^k-cycle in identGraph G x y (when G is PowerFree)
    must pass through z = ⟨x, hxy⟩ and lift to a simple x-y path of length 2^k in G. -/
theorem lift_ident_cycle {V : Type u} {G : SimpleGraph V} {x y : V} (hxy : x ≠ y)
    (hfree : ¬ HasPower G)
    {k : ℕ} (hk : 2 ≤ k) {v0 : {v : V // v ≠ y}}
    (c : (identGraph G x y).Walk v0 v0) (hc : c.IsCycle) (hlen : c.length = 2 ^ k) :
    ∃ (p : G.Walk x y), p.IsPath ∧ p.length = 2 ^ k ∧
      (∀ u ∈ p.support, u = x ∨ u = y ∨
        ∃ (w : {v : V // v ≠ y}), w ∈ c.support ∧ w ≠ ⟨x, hxy⟩ ∧ w.1 = u) := by
  classical
  let H := identGraph G x y
  let z : {v : V // v ≠ y} := ⟨x, hxy⟩
  have hpow4 : 4 ≤ 2 ^ k := by
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
    simpa using this
  by_cases hz : z ∈ c.support
  · let d : H.Walk z z := c.rotate hz
    have hd : d.IsCycle := hc.rotate hz
    have hdlen : d.length = 2 ^ k := by
      simpa [d, Walk.length_rotate] using hlen
    obtain ⟨a, b, hza, hbz, m, hmlen, hmnodup, hmnoZ, hmsub, _, _⟩ :=
      decompose_cycle_at_start d hd
    let mG : G.Walk a.1 b.1 := liftNoZ hxy m hmnoZ
    have hmGlen : mG.length = m.length := length_liftNoZ hxy m hmnoZ
    have hmGsupp : mG.support = m.support.map Subtype.val := support_liftNoZ hxy m hmnoZ
    have hmGnodup : mG.support.Nodup := by
      rw [hmGsupp]
      exact (List.nodup_map_iff Subtype.val_injective).mpr hmnodup
    have hx_not : x ∉ mG.support := by
      rw [hmGsupp, List.mem_map]
      rintro ⟨w, hw, hwx⟩
      exact hmnoZ w hw (Subtype.ext hwx)
    have hy_not : y ∉ mG.support := by
      rw [hmGsupp, List.mem_map]
      rintro ⟨w, _, hwy⟩
      exact w.2 hwy
    have ha_adj : G.Adj x a.1 ∨ G.Adj y a.1 := by
      rcases hza.2 with h | ⟨_, h⟩ | ⟨hax, _⟩
      · exact Or.inl h
      · exact Or.inr h
      · exact False.elim (hza.1 (Subtype.ext hax.symm))
    have hb_adj : G.Adj b.1 x ∨ G.Adj b.1 y := by
      rcases hbz.2 with h | ⟨hbx, _⟩ | ⟨_, h⟩
      · exact Or.inl h
      · exact False.elim (hbz.1 (Subtype.ext hbx))
      · exact Or.inr h
    have no_same : ∀ (u : V), u ∉ mG.support → G.Adj u a.1 → G.Adj b.1 u → False := by
      intro u hu hua hbu
      let cyc : G.Walk u u := .cons hua (mG.append (.cons hbu .nil))
      have hcycsupp : cyc.support.tail = mG.support ++ [u] := by
        simp [cyc, Walk.support_cons, Walk.support_append]
      have htail_nd : cyc.support.tail.Nodup := by
        rw [hcycsupp]
        exact List.nodup_append.mpr ⟨hmGnodup, List.nodup_singleton u, fun t ht _ htu =>
          hu (List.mem_singleton.mp htu ▸ ht)⟩
      have hcyclen : cyc.length = 2 ^ k := by
        simp [cyc, Walk.length_cons, Walk.length_append, hmGlen]
        omega
      have hcyc_is : cyc.IsCycle := by
        apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
        refine ⟨Walk.IsPath.mk' ?_, by omega⟩
        have hnil : ¬ cyc.Nil := by intro h; simp [cyc] at h
        rwa [Walk.support_tail_of_not_nil _ hnil]
      exact hfree ⟨k, u, cyc, hk, hcyc_is, hcyclen⟩
    have hm_in_c : ∀ w ∈ m.support, w ∈ c.support := fun w hw =>
      (Walk.mem_support_rotate_iff c hz).mp (hmsub w hw)
    rcases ha_adj with hxa | hya <;> rcases hb_adj with hbx | hby
    · exact False.elim (no_same x hx_not hxa hbx)
    · let p : G.Walk x y := .cons hxa (mG.append (.cons hby .nil))
      have hpsupp : p.support = x :: (mG.support ++ [y]) := by
        simp [p, Walk.support_cons, Walk.support_append]
      have hp_nd : p.support.Nodup := by
        rw [hpsupp, List.nodup_cons]
        refine ⟨?_, List.nodup_append.mpr ⟨hmGnodup, List.nodup_singleton y,
          fun t ht _ hty => hy_not (List.mem_singleton.mp hty ▸ ht)⟩⟩
        intro hxmem
        rcases List.mem_append.mp hxmem with h1 | h2
        · exact hx_not h1
        · exact hxy (List.mem_singleton.mp h2)
      refine ⟨p, Walk.IsPath.mk' hp_nd, ?_, ?_⟩
      · simp [p, Walk.length_cons, Walk.length_append, hmGlen]; omega
      · intro u hu
        rw [hpsupp, List.mem_cons] at hu
        rcases hu with rfl | hu'
        · exact Or.inl rfl
        · rcases List.mem_append.mp hu' with hm_u | hy_u
          · rw [hmGsupp, List.mem_map] at hm_u
            obtain ⟨w, hw, rfl⟩ := hm_u
            exact Or.inr (Or.inr ⟨w, hm_in_c w hw, hmnoZ w hw, rfl⟩)
          · exact Or.inr (Or.inl (List.mem_singleton.mp hy_u))
    · let q : G.Walk y x := .cons hya (mG.append (.cons hbx .nil))
      have hqsupp : q.support = y :: (mG.support ++ [x]) := by
        simp [q, Walk.support_cons, Walk.support_append]
      have hq_nd : q.support.Nodup := by
        rw [hqsupp, List.nodup_cons]
        refine ⟨?_, List.nodup_append.mpr ⟨hmGnodup, List.nodup_singleton x,
          fun t ht _ htx => hx_not (List.mem_singleton.mp htx ▸ ht)⟩⟩
        intro hymem
        rcases List.mem_append.mp hymem with h1 | h2
        · exact hy_not h1
        · exact hxy.symm (List.mem_singleton.mp h2)
      let p : G.Walk x y := q.reverse
      refine ⟨p, (Walk.IsPath.mk' hq_nd).reverse, ?_, ?_⟩
      · simp [p, q, Walk.length_reverse, Walk.length_cons, Walk.length_append, hmGlen]; omega
      · intro u hu
        have huq : u ∈ q.support := by
          simpa [p, Walk.support_reverse] using hu
        rw [hqsupp, List.mem_cons] at huq
        rcases huq with rfl | hu'
        · exact Or.inr (Or.inl rfl)
        · rcases List.mem_append.mp hu' with hm_u | hx_u
          · rw [hmGsupp, List.mem_map] at hm_u
            obtain ⟨w, hw, rfl⟩ := hm_u
            exact Or.inr (Or.inr ⟨w, hm_in_c w hw, hmnoZ w hw, rfl⟩)
          · exact Or.inl (List.mem_singleton.mp hx_u)
    · exact False.elim (no_same y hy_not hya hby)
  · have hnoZ : ∀ u ∈ c.support, u ≠ z := fun u hu heq => hz (heq ▸ hu)
    let cG : G.Walk v0.1 v0.1 := liftNoZ hxy c hnoZ
    have hcGlen : cG.length = 2 ^ k := by rw [length_liftNoZ, hlen]
    have hcGsupp : cG.support = c.support.map Subtype.val := support_liftNoZ hxy c hnoZ
    have htail : cG.support.tail = c.support.tail.map Subtype.val := by
      rw [hcGsupp, List.map_tail]
    have htail_nd : cG.support.tail.Nodup := by
      rw [htail]
      exact (List.nodup_map_iff Subtype.val_injective).mpr hc.support_nodup
    have hcG_is : cG.IsCycle := by
      apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      refine ⟨Walk.IsPath.mk' ?_, by omega⟩
      have hnil : ¬ cG.Nil := by
        intro h; have := Walk.length_eq_zero_iff.mpr h; omega
      rwa [Walk.support_tail_of_not_nil _ hnil]
    exact False.elim (hfree ⟨k, v0.1, cG, hk, hcG_is, hcGlen⟩)

/-- Helper: cardinality of W = {v : V // v ≠ y} is card V - 1. -/
theorem card_delete_one {V : Type u} [Fintype V] [DecidableEq V] (y : V) :
    Fintype.card {v : V // v ≠ y} + 1 = Fintype.card V := by
  rw [Fintype.card_subtype,
    show (Finset.univ.filter (fun v : V => v ≠ y)) = Finset.univ.erase y by ext v; simp]
  exact Finset.card_erase_add_one (Finset.mem_univ y)

/-- 1. Universal Dyadic Path Theorem (Wave 1 Theorem 1.1, Lean-verified):
In any MinimalBad(G), any two non-adjacent vertices x ≠ y with no common neighbor
(dist >= 3) are joined by a simple path of length 2^k (k >= 2). -/
theorem universal_dyadic_path {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hm : MinimalBad G) {x y : V} (hxy : x ≠ y)
    (hnadj : ¬ G.Adj x y) (hdist3 : ∀ c, ¬ (G.Adj x c ∧ G.Adj y c)) :
    ∃ (k : ℕ) (p : G.Walk x y), 2 ≤ k ∧ p.IsPath ∧ p.length = 2 ^ k := by
  classical
  let W := {v : V // v ≠ y}
  let H := identGraph G x y
  let _ : DecidableRel H.Adj := fun a b => Classical.propDecidable (H.Adj a b)
  let z : W := ⟨x, hxy⟩
  have hWcard : Fintype.card W + 1 = Fintype.card V := card_delete_one y
  have hz_deg : 3 ≤ H.degree z := by
    let f : G.neighborSet x ⊕ G.neighborSet y → H.neighborSet z :=
      Sum.elim
        (fun u => ⟨⟨u.1, fun h => hnadj (h ▸ u.2)⟩,
          ⟨fun h => (G.ne_of_adj u.2) (congrArg Subtype.val h), Or.inl u.2⟩⟩)
        (fun u => ⟨⟨u.1, (G.ne_of_adj u.2).symm⟩,
          ⟨fun h => hnadj ((congrArg Subtype.val h).symm ▸ u.2).symm, Or.inr (Or.inl ⟨rfl, u.2⟩)⟩⟩)
    have hf : Function.Injective f := by
      rintro (u | u) (v | v) heq
      · exact congrArg Sum.inl (Subtype.ext (congrArg (fun t => t.1.1) heq))
      · have hval : u.1 = v.1 := congrArg (fun t => t.1.1) heq
        exact False.elim (hdist3 u.1 ⟨u.2, hval ▸ v.2⟩)
      · have hval : u.1 = v.1 := congrArg (fun t => t.1.1) heq
        exact False.elim (hdist3 u.1 ⟨hval ▸ v.2, u.2⟩)
      · exact congrArg Sum.inr (Subtype.ext (congrArg (fun t => t.1.1) heq))
    have hc := Fintype.card_le_of_injective f hf
    rw [Fintype.card_sum, SimpleGraph.card_neighborSet_eq_degree,
      SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.card_neighborSet_eq_degree] at hc
    have hx2 := no_small_defect G hm x
    have hy2 := no_small_defect G hm y
    omega
  have hv_deg (v : W) (hvz : v ≠ z) : G.degree v.1 ≤ H.degree v := by
    let f : G.neighborSet v.1 → H.neighborSet v := fun u =>
      if huy : u.1 = y then
        ⟨z, ⟨hvz, Or.inr (Or.inr ⟨rfl, huy ▸ u.2⟩)⟩⟩
      else
        ⟨⟨u.1, huy⟩, ⟨fun h => (G.ne_of_adj u.2) (congrArg Subtype.val h), Or.inl u.2⟩⟩
    have hf : Function.Injective f := by
      intro u1 u2 heq
      by_cases h1 : u1.1 = y <;> by_cases h2 : u2.1 = y
      · exact Subtype.ext (h1.trans h2.symm)
      · simp only [f, dif_pos h1, dif_neg h2] at heq
        have h2x : u2.1 = x := (congrArg (fun t => t.1.1) heq).symm
        exact False.elim (hdist3 v.1 ⟨(h2x ▸ u2.2).symm, (h1 ▸ u1.2).symm⟩)
      · simp only [f, dif_neg h1, dif_pos h2] at heq
        have h1x : u1.1 = x := congrArg (fun t => t.1.1) heq
        exact False.elim (hdist3 v.1 ⟨(h1x ▸ u1.2).symm, (h2 ▸ u2.2).symm⟩)
      · simp only [f, dif_neg h1, dif_neg h2] at heq
        exact Subtype.ext (congrArg (fun t => t.1.1) heq)
    have hc := Fintype.card_le_of_injective f hf
    rwa [SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.card_neighborSet_eq_degree] at hc
  have hnear : Near H := by
    obtain ⟨_, w, hw⟩ := hm.1
    by_cases hwy : w = y
    · refine ⟨⟨z, hz_deg⟩, ⟨z, fun v hvz => ?_⟩⟩
      exact (hw v.1 (hwy ▸ v.2)).trans (hv_deg v hvz)
    · refine ⟨⟨z, hz_deg⟩, ⟨⟨w, hwy⟩, fun v hvw => ?_⟩⟩
      by_cases hvz : v = z
      · subst hvz; exact hz_deg
      · exact (hw v.1 (fun h => hvw (Subtype.ext h))).trans (hv_deg v hvz)
  obtain ⟨k, v0, c, hk, hc, hlen⟩ := hm.2.2.1 W H (by omega) hnear
  obtain ⟨p, hp, hplen, _⟩ := lift_ident_cycle hxy hm.2.1 hk c hc hlen
  exact ⟨k, p, hk, hp, hplen⟩

/-- 2. NEW Wave 2 Theorem — Cubic Distance-2 Dyadic Path Theorem:
In any cubic MinimalBad(G), for any non-adjacent x ≠ y with common neighbor c0,
G contains a simple x-y path of length 2^k (k >= 2) avoiding c0. -/
theorem cubic_dist2_dyadic_path {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hm : MinimalBad G) (hC : Cubic G) {x y c0 : V}
    (hxy : x ≠ y) (hnadj : ¬ G.Adj x y) (hxc : G.Adj x c0) (hyc : G.Adj y c0) :
    ∃ (k : ℕ) (p : G.Walk x y), 2 ≤ k ∧ p.IsPath ∧ p.length = 2 ^ k ∧ c0 ∉ p.support := by
  classical
  have huniq : ∀ c, G.Adj x c → G.Adj y c → c = c0 := by
    intro c hxc' hyc'
    by_contra hne
    have hxc0_ne : x ≠ c0 := G.ne_of_adj hxc
    have hyc0_ne : y ≠ c0 := G.ne_of_adj hyc
    have hxc_ne : x ≠ c := G.ne_of_adj hxc'
    have hyc_ne : y ≠ c := G.ne_of_adj hyc'
    exact hm.2.1 (rectangle_power G hxc0_ne hxy hxc_ne hyc0_ne.symm hne.symm hyc_ne.symm
      hxc hyc.symm hyc' hxc'.symm)
  let W := {v : V // v ≠ y}
  let H := identGraph G x y
  let _ : DecidableRel H.Adj := fun a b => Classical.propDecidable (H.Adj a b)
  let z : W := ⟨x, hxy⟩
  have hc0y : c0 ≠ y := (G.ne_of_adj hyc).symm
  let wc : W := ⟨c0, hc0y⟩
  have hWcard : Fintype.card W + 1 = Fintype.card V := card_delete_one y
  have hV4 : 4 ≤ Fintype.card V := by
    have := G.degree_lt_card_verts x
    rw [hC x] at this
    omega
  have hz_deg : 3 ≤ H.degree z := by
    let f : G.neighborSet x → H.neighborSet z := fun u =>
      ⟨⟨u.1, fun h => hnadj (h ▸ u.2)⟩,
        ⟨fun h => (G.ne_of_adj u.2) (congrArg Subtype.val h), Or.inl u.2⟩⟩
    have hf : Function.Injective f := fun _ _ h => Subtype.ext (congrArg (fun t => t.1.1) h)
    have hc := Fintype.card_le_of_injective f hf
    rw [SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.card_neighborSet_eq_degree, hC x] at hc
    exact hc
  have hv_deg (v : W) (hvz : v ≠ z) (hvwc : v ≠ wc) : 3 ≤ H.degree v := by
    have hvc : v.1 ≠ c0 := fun h => hvwc (Subtype.ext h)
    let f : G.neighborSet v.1 → H.neighborSet v := fun u =>
      if huy : u.1 = y then
        ⟨z, ⟨hvz, Or.inr (Or.inr ⟨rfl, huy ▸ u.2⟩)⟩⟩
      else
        ⟨⟨u.1, huy⟩, ⟨fun h => (G.ne_of_adj u.2) (congrArg Subtype.val h), Or.inl u.2⟩⟩
    have hf : Function.Injective f := by
      intro u1 u2 heq
      by_cases h1 : u1.1 = y <;> by_cases h2 : u2.1 = y
      · exact Subtype.ext (h1.trans h2.symm)
      · simp only [f, dif_pos h1, dif_neg h2] at heq
        have h2x : u2.1 = x := (congrArg (fun t => t.1.1) heq).symm
        exact False.elim (hvc (huniq v.1 (h2x ▸ u2.2).symm (h1 ▸ u1.2).symm))
      · simp only [f, dif_neg h1, dif_pos h2] at heq
        have h1x : u1.1 = x := congrArg (fun t => t.1.1) heq
        exact False.elim (hvc (huniq v.1 (h1x ▸ u1.2).symm (h2 ▸ u2.2).symm))
      · simp only [f, dif_neg h1, dif_neg h2] at heq
        exact Subtype.ext (congrArg (fun t => t.1.1) heq)
    have hc := Fintype.card_le_of_injective f hf
    rw [SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.card_neighborSet_eq_degree, hC v.1] at hc
    exact hc
  have hwc_deg : H.degree wc ≤ 2 := by
    have hcx : c0 ≠ x := (G.ne_of_adj hxc).symm
    let g : H.neighborSet wc → {u : V // u ∈ (G.neighborFinset c0).erase y} := fun u =>
      ⟨u.1.1, Finset.mem_erase.mpr ⟨u.1.2, (G.mem_neighborFinset c0 u.1.1).mpr (by
        rcases u.2.2 with h | ⟨h1, _⟩ | ⟨h2, _⟩
        · exact h
        · exact False.elim (hcx h1)
        · exact h2 ▸ hxc.symm)⟩⟩
    have hg : Function.Injective g := fun _ _ h => Subtype.ext (Subtype.ext (congrArg Subtype.val h))
    have hc := Fintype.card_le_of_injective g hg
    rw [SimpleGraph.card_neighborSet_eq_degree, Fintype.card_coe] at hc
    have her := Finset.card_erase_add_one ((G.mem_neighborFinset c0 y).mpr hyc.symm)
    rw [G.card_neighborFinset_eq_degree, hC c0] at her
    omega
  have hnear : Near H := by
    apply near_of_except H wc (by omega)
    intro v hvwc
    by_cases hvz : v = z
    · subst hvz; exact hz_deg
    · exact hv_deg v hvz hvwc
  obtain ⟨k, v0, c, hk, hc, hlen⟩ := hm.2.2.1 W H (by omega) hnear
  have hpow4 : 4 ≤ 2 ^ k := by
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
    simpa using this
  have hz_mem : z ∈ c.support := by
    by_contra hz
    have hnoZ : ∀ u ∈ c.support, u ≠ z := fun u hu heq => hz (heq ▸ hu)
    let cG : G.Walk v0.1 v0.1 := liftNoZ hxy c hnoZ
    have hcGlen : cG.length = 2 ^ k := by rw [length_liftNoZ, hlen]
    have htail : cG.support.tail = c.support.tail.map Subtype.val := by
      rw [support_liftNoZ, List.map_tail]
    have htail_nd : cG.support.tail.Nodup := by
      rw [htail]
      exact (List.nodup_map_iff Subtype.val_injective).mpr hc.support_nodup
    have hcG_is : cG.IsCycle := by
      apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      refine ⟨Walk.IsPath.mk' ?_, by omega⟩
      have hnil : ¬ cG.Nil := by intro h; have := Walk.length_eq_zero_iff.mpr h; omega
      rwa [Walk.support_tail_of_not_nil _ hnil]
    exact hm.2.1 ⟨k, v0.1, cG, hk, hcG_is, hcGlen⟩
  let d : H.Walk z z := c.rotate hz_mem
  have hd : d.IsCycle := hc.rotate hz_mem
  have hdlen : d.length = 2 ^ k := by simpa [d, Walk.length_rotate] using hlen
  obtain ⟨a, b, hza, hbz, m, hmlen, hmnodup, hmnoZ, _, _, _⟩ :=
    decompose_cycle_at_start d hd
  let mG : G.Walk a.1 b.1 := liftNoZ hxy m hmnoZ
  have hmGlen : mG.length = m.length := length_liftNoZ hxy m hmnoZ
  have hmGsupp : mG.support = m.support.map Subtype.val := support_liftNoZ hxy m hmnoZ
  have hmGnodup : mG.support.Nodup := by
    rw [hmGsupp]; exact (List.nodup_map_iff Subtype.val_injective).mpr hmnodup
  have hx_not : x ∉ mG.support := by
    rw [hmGsupp, List.mem_map]; rintro ⟨w, hw, hwx⟩; exact hmnoZ w hw (Subtype.ext hwx)
  have hy_not : y ∉ mG.support := by
    rw [hmGsupp, List.mem_map]; rintro ⟨w, _, hwy⟩; exact w.2 hwy
  have no_same : ∀ (u : V), u ∉ mG.support → G.Adj u a.1 → G.Adj b.1 u → False := by
    intro u hu hua hbu
    let cyc : G.Walk u u := .cons hua (mG.append (.cons hbu .nil))
    have hcycsupp : cyc.support.tail = mG.support ++ [u] := by
      simp [cyc, Walk.support_cons, Walk.support_append]
    have htail_nd : cyc.support.tail.Nodup := by
      rw [hcycsupp]
      exact List.nodup_append.mpr ⟨hmGnodup, List.nodup_singleton u, fun t ht _ htu =>
        hu (List.mem_singleton.mp htu ▸ ht)⟩
    have hcyclen : cyc.length = 2 ^ k := by
      simp [cyc, Walk.length_cons, Walk.length_append, hmGlen]; omega
    have hcyc_is : cyc.IsCycle := by
      apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      refine ⟨Walk.IsPath.mk' ?_, by omega⟩
      have hnil : ¬ cyc.Nil := by intro h; simp [cyc] at h
      rwa [Walk.support_tail_of_not_nil _ hnil]
    exact hm.2.1 ⟨k, u, cyc, hk, hcyc_is, hcyclen⟩
  have ha_adj : G.Adj x a.1 ∨ G.Adj y a.1 := by
    rcases hza.2 with h | ⟨_, h⟩ | ⟨hax, _⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (hza.1 (Subtype.ext hax.symm))
  have hb_adj : G.Adj b.1 x ∨ G.Adj b.1 y := by
    rcases hbz.2 with h | ⟨hbx, _⟩ | ⟨_, h⟩
    · exact Or.inl h
    · exact False.elim (hbz.1 (Subtype.ext hbx))
    · exact Or.inr h
  have ha_not_wc : a ≠ wc := by
    intro hawc
    have ha1 : a.1 = c0 := congrArg Subtype.val hawc
    rcases hb_adj with hbx | hby
    · exact no_same x hx_not (ha1 ▸ hxc) hbx
    · exact no_same y hy_not (ha1 ▸ hyc) hby
  have hb_not_wc : b ≠ wc := by
    intro hbwc
    have hb1 : b.1 = c0 := congrArg Subtype.val hbwc
    rcases ha_adj with hxa | hya
    · exact no_same x hx_not hxa (hb1 ▸ hxc.symm)
    · exact no_same y hy_not hya (hb1 ▸ hyc.symm)
  have hwc_not_m : wc ∉ m.support := by
    intro hmem
    let m1 := m.takeUntil wc hmem
    let m2 := m.dropUntil wc hmem
    have hm1_ne : ¬ m1.Nil := by
      intro hnil
      exact ha_not_wc (Walk.eq_of_nil hnil)
    have hm2_ne : ¬ m2.Nil := by
      intro hnil
      exact hb_not_wc (Walk.eq_of_nil hnil).symm
    cases hm1r : m1.reverse with
    | nil =>
      have : m1.length = 0 := by
        have := congrArg Walk.length hm1r; simp at this; exact this
      exact hm1_ne (Walk.length_eq_zero_iff.mp this)
    | @cons _ u1 _ hwu1 _ =>
      cases hm2c : m2 with
      | nil => exact hm2_ne (by rw [hm2c]; exact Walk.Nil.nil)
      | @cons _ u2 _ hwu2 _ =>
        have hu1_in : u1 ∈ m.support := by
          have : u1 ∈ m1.support := by
            rw [← Walk.support_reverse, hm1r]; simp
          exact Walk.support_takeUntil_subset m hmem this
        have hu2_in : u2 ∈ m.support := by
          have : u2 ∈ m2.support := by rw [hm2c]; simp
          exact Walk.support_dropUntil_subset m hmem this
        have hu1z : u1 ≠ z := hmnoZ u1 hu1_in
        have hu2z : u2 ≠ z := hmnoZ u2 hu2_in
        have hu12 : u1 ≠ u2 := by
          intro heq
          subst heq
          have hms : m.support = m1.support ++ m2.support.tail := by
            have := Walk.take_spec m hmem
            rw [← this, Walk.support_append]
          rw [hms] at hmnodup
          have hu1_m1 : u1 ∈ m1.support := by
            rw [← Walk.support_reverse, hm1r]; simp
          have hu1_m2t : u1 ∈ m2.support.tail := by
            rw [hm2c]; simp
          exact (List.nodup_append.mp hmnodup).2.2 u1 hu1_m1 u1 hu1_m2t rfl
        have hzwc : H.Adj wc z :=
          ⟨fun h => (G.ne_of_adj hxc).symm (congrArg Subtype.val h), Or.inl hxc.symm⟩
        have hsub : ({u1, u2, z} : Finset W) ⊆ H.neighborFinset wc := by
          intro t ht
          simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl | rfl
          · exact (H.mem_neighborFinset wc _).mpr hwu1
          · exact (H.mem_neighborFinset wc _).mpr hwu2
          · exact (H.mem_neighborFinset wc _).mpr hzwc
        have h3 : ({u1, u2, z} : Finset W).card = 3 := by
          simp [hu12, hu1z, hu2z]
        have hle := Finset.card_le_card hsub
        rw [h3, H.card_neighborFinset_eq_degree] at hle
        omega
  have hc0_not_mG : c0 ∉ mG.support := by
    rw [hmGsupp, List.mem_map]
    rintro ⟨w, hw, hwc0⟩
    exact hwc_not_m (Subtype.ext hwc0 ▸ hw)
  have hcx : c0 ≠ x := (G.ne_of_adj hxc).symm
  rcases ha_adj with hxa | hya <;> rcases hb_adj with hbx | hby
  · exact False.elim (no_same x hx_not hxa hbx)
  · let p : G.Walk x y := .cons hxa (mG.append (.cons hby .nil))
    have hpsupp : p.support = x :: (mG.support ++ [y]) := by
      simp [p, Walk.support_cons, Walk.support_append]
    have hp_nd : p.support.Nodup := by
      rw [hpsupp, List.nodup_cons]
      refine ⟨?_, List.nodup_append.mpr ⟨hmGnodup, List.nodup_singleton y,
        fun t ht _ hty => hy_not (List.mem_singleton.mp hty ▸ ht)⟩⟩
      intro hxmem
      rcases List.mem_append.mp hxmem with h1 | h2
      · exact hx_not h1
      · exact hxy (List.mem_singleton.mp h2)
    refine ⟨k, p, hk, Walk.IsPath.mk' hp_nd, ?_, ?_⟩
    · simp [p, Walk.length_cons, Walk.length_append, hmGlen]; omega
    · rw [hpsupp]; simp [hcx, hc0_not_mG, hc0y]
  · let q : G.Walk y x := .cons hya (mG.append (.cons hbx .nil))
    have hqsupp : q.support = y :: (mG.support ++ [x]) := by
      simp [q, Walk.support_cons, Walk.support_append]
    have hq_nd : q.support.Nodup := by
      rw [hqsupp, List.nodup_cons]
      refine ⟨?_, List.nodup_append.mpr ⟨hmGnodup, List.nodup_singleton x,
        fun t ht _ htx => hx_not (List.mem_singleton.mp htx ▸ ht)⟩⟩
      intro hymem
      rcases List.mem_append.mp hymem with h1 | h2
      · exact hy_not h1
      · exact hxy.symm (List.mem_singleton.mp h2)
    let p : G.Walk x y := q.reverse
    refine ⟨k, p, hk, (Walk.IsPath.mk' hq_nd).reverse, ?_, ?_⟩
    · simp [p, q, Walk.length_reverse, Walk.length_cons, Walk.length_append, hmGlen]; omega
    · intro hc0p
      have hc0q : c0 ∈ q.support := by simpa [p, Walk.support_reverse] using hc0p
      rw [hqsupp] at hc0q; simp [hc0y, hc0_not_mG, hcx] at hc0q
  · exact False.elim (no_same y hy_not hya hby)

/-- 3. NEW Wave 2 Corollary — Complete Non-Adjacent Dyadic Path Theorem for Cubic MinimalBad(G):
In EVERY cubic MinimalBad(G) (all 5 open cubic leaves: C-N-R, C-N-2, C-N-3, C-T-2, C-T-3),
EVERY pair of distinct non-adjacent vertices has a simple path of length 2^k (k >= 2). -/
theorem cubic_nonadj_dyadic_path {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hm : MinimalBad G) (hC : Cubic G) {x y : V} (hxy : x ≠ y) (hnadj : ¬ G.Adj x y) :
    ∃ (k : ℕ) (p : G.Walk x y), 2 ≤ k ∧ p.IsPath ∧ p.length = 2 ^ k := by
  by_cases hcom : ∃ c, G.Adj x c ∧ G.Adj y c
  · obtain ⟨c0, hxc, hyc⟩ := hcom
    obtain ⟨k, p, hk, hp, hlen, _⟩ := cubic_dist2_dyadic_path G hm hC hxy hnadj hxc hyc
    exact ⟨k, p, hk, hp, hlen⟩
  · push_neg at hcom
    exact universal_dyadic_path G hm hxy hnadj hcom

/-- 4. NEW Wave 2 Theorem — Universal Edge-Contraction (2^k + 1)-Cycle Theorem:
In ANY MinimalBad(G) (C, S, or H), every edge uv not contained in a triangle
lies on a simple cycle of length 2^k + 1 for some k >= 2.
Applies to EVERY edge in all 7 triangle-free open leaves (C-N-*, S-N-*, H-N-*). -/
theorem edge_contraction_dyadic_plus_one {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hm : MinimalBad G) {u v : V} (huv : G.Adj u v)
    (hnotri : ∀ c, ¬ (G.Adj u c ∧ G.Adj v c)) :
    ∃ (k : ℕ) (c : G.Walk u u), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k + 1 ∧
      s(u, v) ∈ c.edges := by
  classical
  have hne : u ≠ v := G.ne_of_adj huv
  let W := {x : V // x ≠ v}
  let H := identGraph G u v
  let _ : DecidableRel H.Adj := fun a b => Classical.propDecidable (H.Adj a b)
  let z : W := ⟨u, hne⟩
  have hWcard : Fintype.card W + 1 = Fintype.card V := card_delete_one v
  have hz_deg : 3 ≤ H.degree z := by
    let Nu := {x : V // x ∈ (G.neighborFinset u).erase v}
    let Nv := {x : V // x ∈ (G.neighborFinset v).erase u}
    let f : Nu ⊕ Nv → H.neighborSet z :=
      Sum.elim
        (fun a => ⟨⟨a.1, (Finset.mem_erase.mp a.2).1⟩,
          ⟨fun h => (G.ne_of_adj ((G.mem_neighborFinset u a.1).mp (Finset.mem_erase.mp a.2).2))
            (congrArg Subtype.val h),
           Or.inl ((G.mem_neighborFinset u a.1).mp (Finset.mem_erase.mp a.2).2)⟩⟩)
        (fun a => ⟨⟨a.1, (G.ne_of_adj ((G.mem_neighborFinset v a.1).mp (Finset.mem_erase.mp a.2).2)).symm⟩,
          ⟨fun h => (Finset.mem_erase.mp a.2).1 (congrArg Subtype.val h).symm,
           Or.inr (Or.inl ⟨rfl, (G.mem_neighborFinset v a.1).mp (Finset.mem_erase.mp a.2).2⟩)⟩⟩)
    have hf : Function.Injective f := by
      rintro (a | a) (b | b) heq
      · exact congrArg Sum.inl (Subtype.ext (congrArg (fun t => t.1.1) heq))
      · have hval : a.1 = b.1 := congrArg (fun t => t.1.1) heq
        have ha := (G.mem_neighborFinset u a.1).mp (Finset.mem_erase.mp a.2).2
        have hb := (G.mem_neighborFinset v b.1).mp (Finset.mem_erase.mp b.2).2
        exact False.elim (hnotri a.1 ⟨ha, hval ▸ hb⟩)
      · have hval : a.1 = b.1 := congrArg (fun t => t.1.1) heq
        have ha := (G.mem_neighborFinset v a.1).mp (Finset.mem_erase.mp a.2).2
        have hb := (G.mem_neighborFinset u b.1).mp (Finset.mem_erase.mp b.2).2
        exact False.elim (hnotri a.1 ⟨hval ▸ hb, ha⟩)
      · exact congrArg Sum.inr (Subtype.ext (congrArg (fun t => t.1.1) heq))
    have hc := Fintype.card_le_of_injective f hf
    rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe,
      SimpleGraph.card_neighborSet_eq_degree] at hc
    have hcu := Finset.card_erase_add_one ((G.mem_neighborFinset u v).mpr huv)
    have hcv := Finset.card_erase_add_one ((G.mem_neighborFinset v u).mpr huv.symm)
    rw [G.card_neighborFinset_eq_degree] at hcu hcv
    have hdu := no_small_defect G hm u
    have hdv := no_small_defect G hm v
    have hsum : 5 ≤ G.degree u + G.degree v := by
      by_cases hu2 : G.degree u = 2
      · have hv3 := defect_neighbor_cubic G hm hu2 huv
        omega
      · omega
    omega
  have hx_deg (x : W) (hxz : x ≠ z) : G.degree x.1 ≤ H.degree x := by
    let f : G.neighborSet x.1 → H.neighborSet x := fun a =>
      if hav : a.1 = v then
        ⟨z, ⟨hxz, Or.inr (Or.inr ⟨rfl, hav ▸ a.2⟩)⟩⟩
      else
        ⟨⟨a.1, hav⟩, ⟨fun h => (G.ne_of_adj a.2) (congrArg Subtype.val h), Or.inl a.2⟩⟩
    have hf : Function.Injective f := by
      intro a1 a2 heq
      by_cases h1 : a1.1 = v <;> by_cases h2 : a2.1 = v
      · exact Subtype.ext (h1.trans h2.symm)
      · simp only [f, dif_pos h1, dif_neg h2] at heq
        have h2u : a2.1 = u := (congrArg (fun t => t.1.1) heq).symm
        exact False.elim (hnotri x.1 ⟨(h2u ▸ a2.2).symm, (h1 ▸ a1.2).symm⟩)
      · simp only [f, dif_neg h1, dif_pos h2] at heq
        have h1u : a1.1 = u := congrArg (fun t => t.1.1) heq
        exact False.elim (hnotri x.1 ⟨(h1u ▸ a1.2).symm, (h2 ▸ a2.2).symm⟩)
      · simp only [f, dif_neg h1, dif_neg h2] at heq
        exact Subtype.ext (congrArg (fun t => t.1.1) heq)
    have hc := Fintype.card_le_of_injective f hf
    rwa [SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.card_neighborSet_eq_degree] at hc
  have hnear : Near H := by
    obtain ⟨_, w, hw⟩ := hm.1
    by_cases hwv : w = v
    · refine ⟨⟨z, hz_deg⟩, ⟨z, fun x hxz => ?_⟩⟩
      exact (hw x.1 (hwv ▸ x.2)).trans (hx_deg x hxz)
    · refine ⟨⟨z, hz_deg⟩, ⟨⟨w, hwv⟩, fun x hxw => ?_⟩⟩
      by_cases hxz : x = z
      · subst hxz; exact hz_deg
      · exact (hw x.1 (fun h => hxw (Subtype.ext h))).trans (hx_deg x hxz)
  obtain ⟨k, v0, c, hk, hc, hlen⟩ := hm.2.2.1 W H (by omega) hnear
  obtain ⟨p, hp, hplen, _⟩ := lift_ident_cycle hne hm.2.1 hk c hc hlen
  have hpow4 : 4 ≤ 2 ^ k := by
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
    simpa using this
  let cyc : G.Walk u u := p.append (.cons huv.symm .nil)
  have hcyc_is : cyc.IsCycle := by
    have hq : (Walk.cons huv.symm Walk.nil : G.Walk v u).IsPath := by
      apply Walk.IsPath.mk'
      simp [hne.symm]
    have hdisj : p.support.tail.Disjoint (Walk.cons huv.symm Walk.nil : G.Walk v u).support.tail := by
      simp only [Walk.support_cons, Walk.support_nil, List.tail_cons, List.disjoint_singleton]
      intro hu_tail
      have hnd := hp.support_nodup
      have hps : p.support = u :: p.support.tail := (p.cons_tail_support).symm
      rw [hps, List.nodup_cons] at hnd
      exact hnd.1 hu_tail
    exact hp.isCycle_append hq hdisj (Or.inl (by omega))
  refine ⟨k, cyc, hk, hcyc_is, ?_, ?_⟩
  · simp [cyc, Walk.length_append, hplen]
  · simp [cyc, Walk.edges_append, Sym2.eq_swap]

#print axioms universal_dyadic_path
#print axioms cubic_dist2_dyadic_path
#print axioms cubic_nonadj_dyadic_path
#print axioms edge_contraction_dyadic_plus_one
end E64Wave2Ident
