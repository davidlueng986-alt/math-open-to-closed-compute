import Core
import Leaves
import Incidence
import ClosedDefectCore
import HighCodeDistance

/-!
Erdos 64 (Wave 3, Agent #4): Auxiliary Pair-Graph Subdivision Engine,
Class H Multi-Column Code-Weight Hierarchy (wt >= 6, 8, 10),
Upgraded Class H Cubic Density Bounds, and Cubic Independent-Set |J2|+|J3| Bounds.
-/

namespace E64AuxPair
open SimpleGraph Erdos64Closure E64Core E64Leaves Erdos64Paired Erdos64Incidence E64DefectCore E64HighCode
open scoped BigOperators
universe u

variable {α V : Type u}

/-- A graph is `C4Free` if it contains no 4-cycle. -/
def C4Free (F : SimpleGraph α) : Prop :=
  ∀ a b c d : α, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    F.Adj a b → F.Adj b c → F.Adj c d → F.Adj d a → False

/-- A graph is `NearFree` if no induced subgraph on a Finset is `Near`. -/
def NearFree [DecidableEq α] (F : SimpleGraph α) : Prop :=
  ∀ (S : Finset α),
    letI : DecidableRel (F.induce (S : Set α)).Adj := fun _ _ => Classical.dec _
    ¬ Near (F.induce (S : Set α))

/-- Helper: degree of `x : S` in `F.induce (S : Set α)` equals `(S.filter (fun y => F.Adj x.1 y)).card`. -/
lemma induce_degree_eq_filter [DecidableEq α] (F : SimpleGraph α) [DecidableRel F.Adj]
    (S : Finset α) (x : (S : Set α)) :
    (F.induce (S : Set α)).degree x = (S.filter (fun y => F.Adj x.1 y)).card := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  let e : (F.induce (S : Set α)).neighborFinset x ≃ S.filter (fun y => F.Adj x.1 y) :=
    { toFun := fun y => ⟨y.1.1, Finset.mem_filter.mpr ⟨y.1.2,
        (SimpleGraph.mem_neighborFinset (F.induce (S : Set α)) x y.1).mp y.2⟩⟩
      invFun := fun y => ⟨⟨y.1, (Finset.mem_filter.mp y.2).1⟩,
        (SimpleGraph.mem_neighborFinset (F.induce (S : Set α)) x ⟨y.1, (Finset.mem_filter.mp y.2).1⟩).mpr
          (Finset.mem_filter.mp y.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc := Fintype.card_congr e
  rwa [Fintype.card_coe, Fintype.card_coe] at hc

/-- Helper: sum of degrees in `F.induce (S : Set α)` equals `∑ x ∈ S, (S.filter (fun y => F.Adj x y)).card`. -/
lemma induce_deg_sum_eq_filter [DecidableEq α] (F : SimpleGraph α) [DecidableRel F.Adj]
    (S : Finset α) :
    (∑ x : (S : Set α), (F.induce (S : Set α)).degree x) =
      ∑ x ∈ S, (S.filter (fun y => F.Adj x y)).card := by
  classical
  have h1 : ∀ x : (S : Set α), (F.induce (S : Set α)).degree x = (S.filter (fun y => F.Adj x.1 y)).card :=
    fun x => induce_degree_eq_filter F S x
  simp_rw [h1]
  exact Finset.sum_coe_sort S (fun x => (S.filter (fun y => F.Adj x y)).card)

/-- Handshaking peel: removing a vertex `v` from an induced subgraph `F[S]` drops the
    degree sum by `2 * deg_{F[S]}(v)`. -/
lemma induce_deg_sum_erase [DecidableEq α] (F : SimpleGraph α) [DecidableRel F.Adj]
    (S : Finset α) (v : α) (hv : v ∈ S) :
    (∑ x : (S : Set α), (F.induce (S : Set α)).degree x) =
      (∑ x : ((S.erase v : Finset α) : Set α), (F.induce ((S.erase v : Finset α) : Set α)).degree x) +
      2 * (F.induce (S : Set α)).degree ⟨v, hv⟩ := by
  classical
  let S' := S.erase v
  rw [induce_deg_sum_eq_filter F S, induce_deg_sum_eq_filter F S', induce_degree_eq_filter F S ⟨v, hv⟩]
  dsimp only
  have hsplit := Finset.add_sum_erase S (fun x => (S.filter (fun y => F.Adj x y)).card) hv
  rw [← hsplit]
  have hterm : ∀ x ∈ S',
      (S.filter (fun y => F.Adj x y)).card =
        (S'.filter (fun y => F.Adj x y)).card + (if F.Adj x v then 1 else 0) := by
    intro x _
    by_cases hxv : F.Adj x v
    · have hmem : v ∈ S.filter (fun y => F.Adj x y) := Finset.mem_filter.mpr ⟨hv, hxv⟩
      have heq : (S.filter (fun y => F.Adj x y)).erase v = S'.filter (fun y => F.Adj x y) := by
        ext y; simp [S', Finset.mem_erase, Finset.mem_filter, and_assoc]
      simp only [hxv, ↓reduceIte]
      rw [← heq, Finset.card_erase_add_one hmem]
    · have heq : S.filter (fun y => F.Adj x y) = S'.filter (fun y => F.Adj x y) := by
        ext y
        simp only [S', Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨hyS, hxy⟩
          exact ⟨⟨fun hyv => hxv (hyv ▸ hxy), hyS⟩, hxy⟩
        · rintro ⟨⟨_, hyS⟩, hxy⟩
          exact ⟨hyS, hxy⟩
      simp only [hxv, ↓reduceIte, Nat.add_zero, heq]
  have hsum_s' : ∑ x ∈ S', (S.filter (fun y => F.Adj x y)).card =
      (∑ x ∈ S', (S'.filter (fun y => F.Adj x y)).card) +
      ∑ x ∈ S', (if F.Adj x v then 1 else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hterm
  have hcount : (∑ x ∈ S', (if F.Adj x v then 1 else 0)) = (S.filter (fun y => F.Adj v y)).card := by
    rw [← Finset.card_filter]
    congr 1
    ext x
    simp only [S', Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨_, hxS⟩, hxv⟩; exact ⟨hxS, hxv.symm⟩
    · rintro ⟨hxS, hvx⟩; exact ⟨⟨(F.ne_of_adj hvx).symm, hxS⟩, hvx.symm⟩
  rw [hsum_s', hcount]
  omega

/-- Every `NearFree` simple graph has `∑_{v ∈ S} deg_{F[S]}(v) ≤ 4 * |S| - 6` for `|S| ≥ 2`. -/
theorem near_free_deg_sum_le [DecidableEq α] (F : SimpleGraph α) [DecidableRel F.Adj]
    (hnf : NearFree F) :
    ∀ (n : ℕ) (S : Finset α), S.card = n → 2 ≤ n →
      (∑ v : (S : Set α), (F.induce (S : Set α)).degree v) ≤ 4 * n - 6 := by
  classical
  intro n
  induction n with
  | zero => intro _ _ h; omega
  | succ m ih =>
    intro S hcard hge
    have hcardS : Fintype.card (S : Set α) = S.card := Fintype.card_coe S
    by_cases hm3 : m ≤ 2
    · have hle : ∀ v : (S : Set α), (F.induce (S : Set α)).degree v ≤ m := by
        intro v
        have hlt := (F.induce (S : Set α)).degree_lt_card_verts v
        omega
      have hsum : (∑ v : (S : Set α), (F.induce (S : Set α)).degree v) ≤ ∑ _v : (S : Set α), m :=
        Finset.sum_le_sum (fun v _ => hle v)
      have hc : (∑ _v : (S : Set α), m) = (m + 1) * m := by
        rw [Finset.sum_const, Finset.card_univ, hcardS, hcard, smul_eq_mul]
      rw [hc] at hsum
      interval_cases m <;> omega
    · have hm_ge : 3 ≤ m := by omega
      by_cases hall2 : ∀ v : (S : Set α), (F.induce (S : Set α)).degree v ≤ 2
      · have hsum : (∑ v : (S : Set α), (F.induce (S : Set α)).degree v) ≤ ∑ _v : (S : Set α), 2 :=
          Finset.sum_le_sum (fun v _ => hall2 v)
        have hc : (∑ _v : (S : Set α), 2) = (m + 1) * 2 := by
          rw [Finset.sum_const, Finset.card_univ, hcardS, hcard, smul_eq_mul]
        rw [hc] at hsum
        omega
      · push Not at hall2
        obtain ⟨u, hu⟩ := hall2
        have hex2 : ∃ v : (S : Set α), (F.induce (S : Set α)).degree v ≤ 2 := by
          by_contra hno
          push Not at hno
          have hnear : Near (F.induce (S : Set α)) := ⟨⟨u, hu⟩, ⟨u, fun v _ => hno v⟩⟩
          exact hnf S (by convert hnear)
        obtain ⟨v, hv⟩ := hex2
        have hpeel := induce_deg_sum_erase F S v.1 v.2
        have hcard' : (S.erase v.1).card = m := by
          rw [Finset.card_erase_of_mem v.2, hcard]; omega
        have hih := ih (S.erase v.1) hcard' (by omega)
        have hv_eq : (F.induce (S : Set α)).degree ⟨v.1, v.2⟩ = (F.induce (S : Set α)).degree v := rfl
        rw [hv_eq] at hpeel
        omega

/-- Base case `|S| = 4` for `C4Free`: degree sum is at most 8 (i.e. at most 4 edges). -/
lemma c4_free_card4_deg_sum_le [DecidableEq α] (F : SimpleGraph α) [DecidableRel F.Adj]
    (hc4 : C4Free F) (S : Finset α) (hcard : S.card = 4) :
    (∑ v : (S : Set α), (F.induce (S : Set α)).degree v) ≤ 8 := by
  classical
  by_contra hgt
  have hge9 : 9 ≤ ∑ v : (S : Set α), (F.induce (S : Set α)).degree v := by omega
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hS⟩ := Finset.card_eq_four.mp hcard
  have hsum_eq : (∑ v : (S : Set α), (F.induce (S : Set α)).degree v) =
      2 * ((if F.Adj a b then 1 else 0) + (if F.Adj a c then 1 else 0) +
           (if F.Adj a d then 1 else 0) + (if F.Adj b c then 1 else 0) +
           (if F.Adj b d then 1 else 0) + (if F.Adj c d then 1 else 0)) := by
    rw [induce_deg_sum_eq_filter F S]
    have hfilt : ∀ x : α, (S.filter (fun y => F.Adj x y)).card =
        (if F.Adj x a then 1 else 0) + (if F.Adj x b then 1 else 0) +
        (if F.Adj x c then 1 else 0) + (if F.Adj x d then 1 else 0) := by
      intro x
      rw [Finset.card_filter, hS,
          Finset.sum_insert (by simp [hab, hac, had]),
          Finset.sum_insert (by simp [hbc, hbd]),
          Finset.sum_insert (by simp [hcd]),
          Finset.sum_singleton]
      omega
    rw [Finset.sum_congr rfl (fun x _ => hfilt x), hS,
        Finset.sum_insert (by simp [hab, hac, had]),
        Finset.sum_insert (by simp [hbc, hbd]),
        Finset.sum_insert (by simp [hcd]),
        Finset.sum_singleton]
    have hlo : ∀ u, ¬ F.Adj u u := fun u => F.loopless.irrefl u
    have hsym : ∀ u v, (if F.Adj v u then (1 : ℕ) else 0) = if F.Adj u v then 1 else 0 :=
      fun u v => by by_cases h : F.Adj u v <;> simp [h, F.adj_comm]
    simp only [hlo, ↓reduceIte, hsym b a, hsym c a, hsym d a, hsym c b, hsym d b, hsym d c]
    omega
  rw [hsum_eq] at hge9
  by_cases h1 : F.Adj a b <;> by_cases h2 : F.Adj a c <;> by_cases h3 : F.Adj a d <;>
    by_cases h4 : F.Adj b c <;> by_cases h5 : F.Adj b d <;> by_cases h6 : F.Adj c d
  all_goals simp only [h1, h2, h3, h4, h5, h6, ↓reduceIte] at hge9
  all_goals first
    | omega
    | exact hc4 a b c d hab hac had hbc hbd hcd h1 h4 h6 h3.symm
    | exact hc4 a b d c hab had hac hbd hbc hcd.symm h1 h5 h6.symm h2.symm
    | exact hc4 a c b d hac hab had hbc.symm hcd hbd h2 h4.symm h5 h3.symm

/-- For every `C4Free` and `NearFree` simple graph, `∑_{v ∈ S} deg_{F[S]}(v) ≤ 4 * |S| - 8`
    for all `|S| ≥ 4`. -/
theorem c4_near_free_deg_sum_le_four [DecidableEq α] (F : SimpleGraph α) [DecidableRel F.Adj]
    (hc4 : C4Free F) (hnf : NearFree F) :
    ∀ (n : ℕ) (S : Finset α), S.card = n → 4 ≤ n →
      (∑ v : (S : Set α), (F.induce (S : Set α)).degree v) ≤ 4 * n - 8 := by
  classical
  intro n
  induction n with
  | zero => intro _ _ h; omega
  | succ m ih =>
    intro S hcard hge
    have hcardS : Fintype.card (S : Set α) = S.card := Fintype.card_coe S
    by_cases hm3 : m = 3
    · subst hm3
      exact c4_free_card4_deg_sum_le F hc4 S hcard
    · have hm4 : 4 ≤ m := by omega
      by_cases hall2 : ∀ v : (S : Set α), (F.induce (S : Set α)).degree v ≤ 2
      · have hsum : (∑ v : (S : Set α), (F.induce (S : Set α)).degree v) ≤ ∑ _v : (S : Set α), 2 :=
          Finset.sum_le_sum (fun v _ => hall2 v)
        have hc : (∑ _v : (S : Set α), 2) = (m + 1) * 2 := by
          rw [Finset.sum_const, Finset.card_univ, hcardS, hcard, smul_eq_mul]
        rw [hc] at hsum
        omega
      · push Not at hall2
        obtain ⟨u, hu⟩ := hall2
        have hex2 : ∃ v : (S : Set α), (F.induce (S : Set α)).degree v ≤ 2 := by
          by_contra hno
          push Not at hno
          have hnear : Near (F.induce (S : Set α)) := ⟨⟨u, hu⟩, ⟨u, fun v _ => hno v⟩⟩
          exact hnf S (by convert hnear)
        obtain ⟨v, hv⟩ := hex2
        have hpeel := induce_deg_sum_erase F S v.1 v.2
        have hcard' : (S.erase v.1).card = m := by
          rw [Finset.card_erase_of_mem v.2, hcard]; omega
        have hih := ih (S.erase v.1) hcard' hm4
        have hv_eq : (F.induce (S : Set α)).degree ⟨v.1, v.2⟩ = (F.induce (S : Set α)).degree v := rfl
        rw [hv_eq] at hpeel
        omega

/-- Helper: in a 5-vertex `C4Free` graph with 6 edges, every pair of distinct vertices has
    a common neighbor, so no degree-2 vertex can attach to it without creating a `C4`. -/
lemma c4_free_card5_no_pair_without_common [DecidableEq α] (F : SimpleGraph α) [DecidableRel F.Adj]
    (hc4 : C4Free F)
    (u₁ u₂ t₁ t₂ t₃ : α)
    (h12 : u₁ ≠ u₂) (h13 : u₁ ≠ t₁) (h14 : u₁ ≠ t₂) (h15 : u₁ ≠ t₃)
    (h23 : u₂ ≠ t₁) (h24 : u₂ ≠ t₂) (h25 : u₂ ≠ t₃)
    (h34 : t₁ ≠ t₂) (h35 : t₁ ≠ t₃) (h45 : t₂ ≠ t₃)
    (hnocom : ∀ z, z ∈ ({t₁, t₂, t₃} : Finset α) → ¬ (F.Adj u₁ z ∧ F.Adj u₂ z))
    (h6 : 6 ≤ (if F.Adj u₁ u₂ then 1 else 0) + (if F.Adj u₁ t₁ then 1 else 0) +
              (if F.Adj u₁ t₂ then 1 else 0) + (if F.Adj u₁ t₃ then 1 else 0) +
              (if F.Adj u₂ t₁ then 1 else 0) + (if F.Adj u₂ t₂ then 1 else 0) +
              (if F.Adj u₂ t₃ then 1 else 0) + (if F.Adj t₁ t₂ then 1 else 0) +
              (if F.Adj t₁ t₃ then 1 else 0) + (if F.Adj t₂ t₃ then 1 else 0)) : False := by
  have hnc1 : ¬ (F.Adj u₁ t₁ ∧ F.Adj u₂ t₁) := hnocom t₁ (by simp)
  have hnc2 : ¬ (F.Adj u₁ t₂ ∧ F.Adj u₂ t₂) := hnocom t₂ (by simp)
  have hnc3 : ¬ (F.Adj u₁ t₃ ∧ F.Adj u₂ t₃) := hnocom t₃ (by simp)
  by_cases e12 : F.Adj u₁ u₂ <;>
  by_cases e13 : F.Adj u₁ t₁ <;> by_cases e23 : F.Adj u₂ t₁ <;>
  (try exact hnc1 ⟨e13, e23⟩) <;>
  by_cases e14 : F.Adj u₁ t₂ <;> by_cases e24 : F.Adj u₂ t₂ <;>
  (try exact hnc2 ⟨e14, e24⟩) <;>
  by_cases e15 : F.Adj u₁ t₃ <;> by_cases e25 : F.Adj u₂ t₃ <;>
  (try exact hnc3 ⟨e15, e25⟩) <;>
  by_cases e34 : F.Adj t₁ t₂ <;> by_cases e35 : F.Adj t₁ t₃ <;> by_cases e45 : F.Adj t₂ t₃
  all_goals simp only [e12, e13, e23, e14, e24, e15, e25, e34, e35, e45, ↓reduceIte] at h6
  all_goals first
    | omega
    | exact hc4 u₁ t₁ t₃ t₂ h13 h15 h14 h35 h34 h45.symm e13 e35 e45.symm e14.symm
    | exact hc4 u₁ t₁ t₂ t₃ h13 h14 h15 h34 h35 h45 e13 e34 e45 e15.symm
    | exact hc4 u₁ t₂ t₁ t₃ h14 h13 h15 h34.symm h45 h35 e14 e34.symm e35 e15.symm
    | exact hc4 u₂ t₁ t₃ t₂ h23 h25 h24 h35 h34 h45.symm e23 e35 e45.symm e24.symm
    | exact hc4 u₂ t₁ t₂ t₃ h23 h24 h25 h34 h35 h45 e23 e34 e45 e25.symm
    | exact hc4 u₂ t₂ t₁ t₃ h24 h23 h25 h34.symm h45 h35 e24 e34.symm e35 e25.symm
    | exact hc4 u₁ u₂ t₂ t₁ h12 h14 h13 h24 h23 h34.symm e12 e24 e34.symm e13.symm
    | exact hc4 u₁ u₂ t₁ t₂ h12 h13 h14 h23 h24 h34 e12 e23 e34 e14.symm
    | exact hc4 u₁ u₂ t₃ t₁ h12 h15 h13 h25 h23 h35.symm e12 e25 e35.symm e13.symm
    | exact hc4 u₁ u₂ t₁ t₃ h12 h13 h15 h23 h25 h35 e12 e23 e35 e15.symm
    | exact hc4 u₁ u₂ t₃ t₂ h12 h15 h14 h25 h24 h45.symm e12 e25 e45.symm e14.symm
    | exact hc4 u₁ u₂ t₂ t₃ h12 h14 h15 h24 h25 h45 e12 e24 e45 e15.symm

/-- Base case `|S| = 6` for `C4Free` + `NearFree`: degree sum is at most 14 (i.e. at most 7 edges). -/
lemma c4_near_free_card6_deg_sum_le [DecidableEq α] (F : SimpleGraph α) [DecidableRel F.Adj]
    (hc4 : C4Free F) (hnf : NearFree F) (S : Finset α) (hcard : S.card = 6) :
    (∑ v : (S : Set α), (F.induce (S : Set α)).degree v) ≤ 14 := by
  classical
  have hcardS : Fintype.card (S : Set α) = S.card := Fintype.card_coe S
  by_contra hgt
  have hge15 : 15 ≤ ∑ v : (S : Set α), (F.induce (S : Set α)).degree v := by omega
  by_cases hall2 : ∀ v : (S : Set α), (F.induce (S : Set α)).degree v ≤ 2
  · have hsum : (∑ v : (S : Set α), (F.induce (S : Set α)).degree v) ≤ ∑ _v : (S : Set α), 2 :=
      Finset.sum_le_sum (fun v _ => hall2 v)
    have hc : (∑ _v : (S : Set α), 2) = 12 := by
      rw [Finset.sum_const, Finset.card_univ, hcardS, hcard, smul_eq_mul]
    rw [hc] at hsum; omega
  · push Not at hall2
    obtain ⟨u0, hu0⟩ := hall2
    have hex2 : ∃ v : (S : Set α), (F.induce (S : Set α)).degree v ≤ 2 := by
      by_contra hno
      push Not at hno
      have hnear : Near (F.induce (S : Set α)) := ⟨⟨u0, hu0⟩, ⟨u0, fun v _ => hno v⟩⟩
      exact hnf S (by convert hnear)
    obtain ⟨v, hv⟩ := hex2
    have hpeel := induce_deg_sum_erase F S v.1 v.2
    have hv_eq : (F.induce (S : Set α)).degree ⟨v.1, v.2⟩ = (F.induce (S : Set α)).degree v := rfl
    rw [hv_eq] at hpeel
    let S' := S.erase v.1
    have hcard' : S'.card = 5 := by rw [Finset.card_erase_of_mem v.2, hcard]
    have hle12 := c4_near_free_deg_sum_le_four F hc4 hnf 5 S' hcard' (by omega)
    dsimp only [S'] at hle12
    have hv_eq2 : (F.induce (S : Set α)).degree v = 2 := by omega
    have hS'_ge11 : 11 ≤ ∑ x : (S' : Set α), (F.induce (S' : Set α)).degree x := by
      dsimp only [S']; omega
    have hnv_card : ((F.induce (S : Set α)).neighborFinset v).card = 2 := by
      rw [SimpleGraph.card_neighborFinset_eq_degree, hv_eq2]
    obtain ⟨a1, a2, ha12, hnv_eq⟩ := Finset.card_eq_two.mp hnv_card
    have ha1_adj : F.Adj v.1 a1.1 :=
      (SimpleGraph.mem_neighborFinset (F.induce (S : Set α)) v a1).mp (by rw [hnv_eq]; simp)
    have ha2_adj : F.Adj v.1 a2.1 :=
      (SimpleGraph.mem_neighborFinset (F.induce (S : Set α)) v a2).mp (by rw [hnv_eq]; simp)
    have ha1_ne_v : a1.1 ≠ v.1 := (F.ne_of_adj ha1_adj).symm
    have ha2_ne_v : a2.1 ≠ v.1 := (F.ne_of_adj ha2_adj).symm
    have hu12 : a1.1 ≠ a2.1 := fun h => ha12 (Subtype.ext h)
    have ha1_S' : a1.1 ∈ S' := Finset.mem_erase.mpr ⟨ha1_ne_v, a1.2⟩
    have ha2_S' : a2.1 ∈ S' := Finset.mem_erase.mpr ⟨ha2_ne_v, a2.2⟩
    let T := (S'.erase a1.1).erase a2.1
    have ha2_er : a2.1 ∈ S'.erase a1.1 := Finset.mem_erase.mpr ⟨hu12.symm, ha2_S'⟩
    have hT_card : T.card = 3 := by
      rw [Finset.card_erase_of_mem ha2_er, Finset.card_erase_of_mem ha1_S', hcard']
    obtain ⟨t1, t2, t3, ht12, ht13, ht23, hT_eq⟩ := Finset.card_eq_three.mp hT_card
    have hS'_eq : S' = {a1.1, a2.1, t1, t2, t3} := by
      ext z
      by_cases hz1 : z = a1.1
      · subst hz1; simp [ha1_S']
      · by_cases hz2 : z = a2.1
        · subst hz2; simp [ha2_S']
        · have : z ∈ T ↔ z ∈ S' := by simp [T, Finset.mem_erase, hz1, hz2]
          rw [← this, hT_eq]; simp [hz1, hz2]
    have ht1_T : t1 ∈ T := by rw [hT_eq]; simp
    have ht2_T : t2 ∈ T := by rw [hT_eq]; simp
    have ht3_T : t3 ∈ T := by rw [hT_eq]; simp
    have h13 : a1.1 ≠ t1 := (Finset.mem_erase.mp (Finset.mem_erase.mp ht1_T).2).1.symm
    have h14 : a1.1 ≠ t2 := (Finset.mem_erase.mp (Finset.mem_erase.mp ht2_T).2).1.symm
    have h15 : a1.1 ≠ t3 := (Finset.mem_erase.mp (Finset.mem_erase.mp ht3_T).2).1.symm
    have h23 : a2.1 ≠ t1 := (Finset.mem_erase.mp ht1_T).1.symm
    have h24 : a2.1 ≠ t2 := (Finset.mem_erase.mp ht2_T).1.symm
    have h25 : a2.1 ≠ t3 := (Finset.mem_erase.mp ht3_T).1.symm
    have hnocom : ∀ z, z ∈ ({t1, t2, t3} : Finset α) → ¬ (F.Adj a1.1 z ∧ F.Adj a2.1 z) := by
      intro z hz ⟨hza1, hza2⟩
      have hzT : z ∈ T := by rw [hT_eq]; exact hz
      have hzv : z ≠ v.1 := (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hzT).2).2).1
      exact hc4 v.1 a1.1 z a2.1 ha1_ne_v.symm hzv.symm ha2_ne_v.symm
        (F.ne_of_adj hza1) hu12 (F.ne_of_adj hza2).symm ha1_adj hza1 hza2.symm ha2_adj.symm
    have hsum5 : (∑ x : (S' : Set α), (F.induce (S' : Set α)).degree x) =
        2 * ((if F.Adj a1.1 a2.1 then 1 else 0) + (if F.Adj a1.1 t1 then 1 else 0) +
             (if F.Adj a1.1 t2 then 1 else 0) + (if F.Adj a1.1 t3 then 1 else 0) +
             (if F.Adj a2.1 t1 then 1 else 0) + (if F.Adj a2.1 t2 then 1 else 0) +
             (if F.Adj a2.1 t3 then 1 else 0) + (if F.Adj t1 t2 then 1 else 0) +
             (if F.Adj t1 t3 then 1 else 0) + (if F.Adj t2 t3 then 1 else 0)) := by
      rw [induce_deg_sum_eq_filter F S']
      have hfilt : ∀ x : α, (S'.filter (fun y => F.Adj x y)).card =
          (if F.Adj x a1.1 then 1 else 0) + (if F.Adj x a2.1 then 1 else 0) +
          (if F.Adj x t1 then 1 else 0) + (if F.Adj x t2 then 1 else 0) +
          (if F.Adj x t3 then 1 else 0) := by
        intro x
        rw [Finset.card_filter, hS'_eq,
            Finset.sum_insert (by simp [hu12, h13, h14, h15]),
            Finset.sum_insert (by simp [h23, h24, h25]),
            Finset.sum_insert (by simp [ht12, ht13]),
            Finset.sum_insert (by simp [ht23]),
            Finset.sum_singleton]
        omega
      rw [Finset.sum_congr rfl (fun x _ => hfilt x), hS'_eq,
          Finset.sum_insert (by simp [hu12, h13, h14, h15]),
          Finset.sum_insert (by simp [h23, h24, h25]),
          Finset.sum_insert (by simp [ht12, ht13]),
          Finset.sum_insert (by simp [ht23]),
          Finset.sum_singleton]
      have hlo : ∀ u, ¬ F.Adj u u := fun u => F.loopless.irrefl u
      have hsym : ∀ u w, (if F.Adj w u then (1 : ℕ) else 0) = if F.Adj u w then 1 else 0 :=
        fun u w => by by_cases h : F.Adj u w <;> simp [h, F.adj_comm]
      simp only [hlo, ↓reduceIte,
        hsym a2.1 a1.1, hsym t1 a1.1, hsym t2 a1.1, hsym t3 a1.1,
        hsym t1 a2.1, hsym t2 a2.1, hsym t3 a2.1,
        hsym t2 t1, hsym t3 t1, hsym t3 t2]
      omega
    rw [hsum5] at hS'_ge11
    exact c4_free_card5_no_pair_without_common F hc4 a1.1 a2.1 t1 t2 t3
      hu12 h13 h14 h15 h23 h24 h25 ht12 ht13 ht23 hnocom (by omega)

/-- For every `C4Free` and `NearFree` simple graph, `∑_{v ∈ S} deg_{F[S]}(v) ≤ 4 * |S| - 10`
    for all `|S| ≥ 6` (EXACTLY SHARP). -/
theorem c4_near_free_deg_sum_le_six [DecidableEq α] (F : SimpleGraph α) [DecidableRel F.Adj]
    (hc4 : C4Free F) (hnf : NearFree F) :
    ∀ (n : ℕ) (S : Finset α), S.card = n → 6 ≤ n →
      (∑ v : (S : Set α), (F.induce (S : Set α)).degree v) ≤ 4 * n - 10 := by
  classical
  intro n
  induction n with
  | zero => intro _ _ h; omega
  | succ m ih =>
    intro S hcard hge
    have hcardS : Fintype.card (S : Set α) = S.card := Fintype.card_coe S
    by_cases hm5 : m = 5
    · subst hm5
      exact c4_near_free_card6_deg_sum_le F hc4 hnf S hcard
    · have hm6 : 6 ≤ m := by omega
      by_cases hall2 : ∀ v : (S : Set α), (F.induce (S : Set α)).degree v ≤ 2
      · have hsum : (∑ v : (S : Set α), (F.induce (S : Set α)).degree v) ≤ ∑ _v : (S : Set α), 2 :=
          Finset.sum_le_sum (fun v _ => hall2 v)
        have hc : (∑ _v : (S : Set α), 2) = (m + 1) * 2 := by
          rw [Finset.sum_const, Finset.card_univ, hcardS, hcard, smul_eq_mul]
        rw [hc] at hsum
        omega
      · push Not at hall2
        obtain ⟨u, hu⟩ := hall2
        have hex2 : ∃ v : (S : Set α), (F.induce (S : Set α)).degree v ≤ 2 := by
          by_contra hno
          push Not at hno
          have hnear : Near (F.induce (S : Set α)) := ⟨⟨u, hu⟩, ⟨u, fun v _ => hno v⟩⟩
          exact hnf S (by convert hnear)
        obtain ⟨v, hv⟩ := hex2
        have hpeel := induce_deg_sum_erase F S v.1 v.2
        have hv_eq : (F.induce (S : Set α)).degree ⟨v.1, v.2⟩ = (F.induce (S : Set α)).degree v := rfl
        rw [hv_eq] at hpeel
        have hcard' : (S.erase v.1).card = m := by
          rw [Finset.card_erase_of_mem v.2, hcard]; omega
        have hih := ih (S.erase v.1) hcard' hm6
        omega

/-- Top-level subdivision walk lifter: lifts a walk in `F` to a walk of double length in `G`. -/
def liftSubdivWalk {G : SimpleGraph V} {F : SimpleGraph α}
    (ι : α ↪ V) (mid : Sym2 α → V)
    (hmid_adj : ∀ x y, F.Adj x y → G.Adj (ι x) (mid s(x, y)) ∧ G.Adj (mid s(x, y)) (ι y)) :
    ∀ {a b : α}, F.Walk a b → G.Walk (ι a) (ι b)
  | _, _, .nil => .nil
  | a, _, .cons (v := b) hab q =>
    .cons (hmid_adj a b hab).1 (.cons (hmid_adj a b hab).2 (liftSubdivWalk ι mid hmid_adj q))

lemma liftSubdivWalk_length {G : SimpleGraph V} {F : SimpleGraph α}
    (ι : α ↪ V) (mid : Sym2 α → V)
    (hmid_adj : ∀ x y, F.Adj x y → G.Adj (ι x) (mid s(x, y)) ∧ G.Adj (mid s(x, y)) (ι y))
    {a b : α} (w : F.Walk a b) :
    (liftSubdivWalk ι mid hmid_adj w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons _ q ih => simp only [liftSubdivWalk, Walk.length_cons, ih]; omega

lemma liftSubdivWalk_mem_tail {G : SimpleGraph V} {F : SimpleGraph α}
    (ι : α ↪ V) (mid : Sym2 α → V)
    (hmid_adj : ∀ x y, F.Adj x y → G.Adj (ι x) (mid s(x, y)) ∧ G.Adj (mid s(x, y)) (ι y))
    {a b : α} (w : F.Walk a b) (z : V) :
    z ∈ (liftSubdivWalk ι mid hmid_adj w).support.tail ↔
      (∃ x ∈ w.support.tail, ι x = z) ∨ (∃ e ∈ w.edges, mid e = z) := by
  induction w with
  | nil => simp [liftSubdivWalk]
  | @cons u v c huv q ih =>
    simp only [liftSubdivWalk, Walk.support_cons, List.tail_cons, List.mem_cons, Walk.edges_cons]
    rw [← (liftSubdivWalk ι mid hmid_adj q).cons_tail_support, List.mem_cons, ih]
    constructor
    · rintro (rfl | rfl | ⟨x, hx, rfl⟩ | ⟨e, he, rfl⟩)
      · exact Or.inr ⟨s(u, v), Or.inl rfl, rfl⟩
      · exact Or.inl ⟨v, Walk.start_mem_support q, rfl⟩
      · exact Or.inl ⟨x, List.mem_of_mem_tail hx, rfl⟩
      · exact Or.inr ⟨e, Or.inr he, rfl⟩
    · rintro (⟨x, hx, rfl⟩ | ⟨e, he, rfl⟩)
      · rw [← q.cons_tail_support, List.mem_cons] at hx
        rcases hx with rfl | hx'
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl ⟨x, hx', rfl⟩))
      · rcases he with rfl | he'
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inr ⟨e, he', rfl⟩))

lemma liftSubdivWalk_nodup {G : SimpleGraph V} {F : SimpleGraph α}
    (ι : α ↪ V) (mid : Sym2 α → V)
    (hmid_disj : ∀ x y, F.Adj x y → ∀ z, mid s(x, y) ≠ ι z)
    (hmid_adj : ∀ x y, F.Adj x y → G.Adj (ι x) (mid s(x, y)) ∧ G.Adj (mid s(x, y)) (ι y))
    (hmid_inj : ∀ e₁ e₂ : Sym2 α, e₁ ∈ F.edgeSet → e₂ ∈ F.edgeSet → mid e₁ = mid e₂ → e₁ = e₂)
    {a b : α} (w : F.Walk a b) (hsn : w.support.tail.Nodup) (hen : w.edges.Nodup) :
    (liftSubdivWalk ι mid hmid_adj w).support.tail.Nodup := by
  induction w with
  | nil => simp [liftSubdivWalk]
  | @cons u v c huv q ih =>
    rw [Walk.support_cons, List.tail_cons] at hsn
    have hq_split : q.support = v :: q.support.tail := (q.cons_tail_support).symm
    have hsn' : v ∉ q.support.tail ∧ q.support.tail.Nodup :=
      List.nodup_cons.mp (hq_split ▸ hsn)
    have hnot_uv : s(u, v) ∉ q.edges := (List.nodup_cons.mp hen).1
    have hqe : q.edges.Nodup := (List.nodup_cons.mp hen).2
    have hne_uv : ∀ e ∈ q.edges, e ∈ F.edgeSet := fun e he => q.edges_subset_edgeSet he
    simp only [liftSubdivWalk, Walk.support_cons, List.tail_cons]
    rw [← (liftSubdivWalk ι mid hmid_adj q).cons_tail_support, List.nodup_cons, List.nodup_cons]
    refine ⟨?_, ?_, ih hsn'.2 hqe⟩
    · intro hm'
      rcases List.mem_cons.mp hm' with hm1 | hm2
      · exact hmid_disj u v huv v hm1
      · rw [liftSubdivWalk_mem_tail] at hm2
        rcases hm2 with ⟨x, _, hx⟩ | ⟨e, he, heq⟩
        · exact hmid_disj u v huv x hx.symm
        · have heq' : e = s(u, v) := hmid_inj e s(u, v) (hne_uv e he) huv heq
          exact hnot_uv (heq' ▸ he)
    · intro hm'
      rw [liftSubdivWalk_mem_tail] at hm'
      rcases hm' with ⟨x, hx, hxi⟩ | ⟨e, he, heq⟩
      · have hxv : x = v := ι.injective hxi
        subst hxv
        exact hsn'.1 hx
      · have heF : e ∈ F.edgeSet := hne_uv e he
        induction e using Sym2.ind with
        | _ p r => exact hmid_disj p r heF v heq

/-- Auxiliary Pair-Graph Subdivision Lifting Theorem:
    Every simple `L`-cycle in `F` lifts to a simple `2L`-cycle in `G`.
    Hence in `MinimalBad(G)` with `|α| < |V|`, `F` is `C4Free` and `NearFree`. -/
theorem aux_pair_graph_power_free [Fintype V] [DecidableEq V] [DecidableEq α]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (F : SimpleGraph α) [Fintype α]
    (ι : α ↪ V)
    (mid : Sym2 α → V)
    (hmid_disj : ∀ x y, F.Adj x y → ∀ z, mid s(x, y) ≠ ι z)
    (hmid_adj : ∀ x y, F.Adj x y → G.Adj (ι x) (mid s(x, y)) ∧ G.Adj (mid s(x, y)) (ι y))
    (hmid_inj : ∀ e₁ e₂ : Sym2 α, e₁ ∈ F.edgeSet → e₂ ∈ F.edgeSet → mid e₁ = mid e₂ → e₁ = e₂)
    (hlt : Fintype.card α < Fintype.card V) :
    C4Free F ∧ NearFree F := by
  classical
  have hlift_cycle : ∀ {a : α} (c : F.Walk a a), c.IsCycle →
      ∃ d : G.Walk (ι a) (ι a), d.IsCycle ∧ d.length = 2 * c.length := by
    intro a c hc
    refine ⟨liftSubdivWalk ι mid hmid_adj c, ?_, liftSubdivWalk_length ι mid hmid_adj c⟩
    have hnod := liftSubdivWalk_nodup ι mid hmid_disj hmid_adj hmid_inj c hc.support_nodup hc.edges_nodup
    have hge3 : 3 ≤ c.length := hc.three_le_length
    have hlen := liftSubdivWalk_length ι mid hmid_adj c
    have hnil : ¬ (liftSubdivWalk ι mid hmid_adj c).Nil := by
      intro h; have := Walk.length_eq_zero_iff.mpr h; omega
    apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    refine ⟨Walk.IsPath.mk' ?_, ?_⟩
    · rwa [Walk.support_tail_of_not_nil _ hnil]
    · omega
  constructor
  · intro a b c d hab hac had hbc hbd hcd h1 h2 h3 h4
    let cyc : F.Walk a a := .cons h1 (.cons h2 (.cons h3 (.cons h4 .nil)))
    have hcyc_len : cyc.length = 4 := rfl
    have hcyc : cyc.IsCycle := by
      apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      refine ⟨Walk.IsPath.mk' ?_, by rw [hcyc_len]; omega⟩
      simp [cyc, Walk.tail_cons, Walk.support_cons, hbc, hbd, hcd, hab.symm, hac.symm, had.symm]
    obtain ⟨g, hg, hglen⟩ := hlift_cycle cyc hcyc
    exact hm.2.1 ⟨3, ι a, g, by decide, hg, by rw [hglen, hcyc_len]; decide⟩
  · intro S hnear
    have hcard_lt : Fintype.card (S : Set α) < Fintype.card V := by
      have hcardS : Fintype.card (S : Set α) = S.card := Fintype.card_coe S
      have hle : S.card ≤ Fintype.card α := Finset.card_le_univ S
      omega
    have hpow : HasPower (F.induce (S : Set α)) := hm.2.2.1 (S : Set α) (F.induce (S : Set α)) hcard_lt hnear
    obtain ⟨k, v₀, c, hk, hc, hlen⟩ := hpow
    let f : (F.induce (S : Set α)) →g F := ⟨Subtype.val, fun h => h⟩
    let cF : F.Walk v₀.1 v₀.1 := c.map f
    have hcF : cF.IsCycle := hc.map (Subtype.val_injective)
    have hcFlen : cF.length = 2 ^ k := by simp [cF, hlen]
    obtain ⟨g, hg, hglen⟩ := hlift_cycle cF hcF
    exact hm.2.1 ⟨k + 1, ι v₀.1, g, by omega, hg, by rw [hglen, hcFlen, pow_succ]; omega⟩

/-- Auxiliary pair-graph `F_S` on a subset `S ⊆ V_{\ge 4}` in Class H. -/
def highPairGraph [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset {v : V // 4 ≤ G.degree v}) : SimpleGraph S where
  Adj x y := x ≠ y ∧ ∃ w : V, G.degree w = 3 ∧ G.Adj x.1.1 w ∧ G.Adj y.1.1 w
  symm := ⟨by rintro x y ⟨hne, w, hw, hx, hy⟩; exact ⟨hne.symm, w, hw, hy, hx⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

/-- No cubic vertex `y` in Class H can be adjacent to 3 distinct vertices in `V_{\ge 4}`. -/
lemma cubic_at_most_two_high_neighbors [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (y : V) (hy : G.degree y = 3)
    {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha4 : 4 ≤ G.degree a) (hb4 : 4 ≤ G.degree b) (hc4 : 4 ≤ G.degree c)
    (hya : G.Adj y a) (hyb : G.Adj y b) (hyc : G.Adj y c) : False := by
  classical
  let H := G.induce ({v : V | v ≠ y})
  have hcard_lt : Fintype.card {v : V // v ≠ y} < Fintype.card V := by
    have h : Fintype.card {v : V // v ≠ y} + 1 = Fintype.card V := by
      rw [Fintype.card_subtype,
        show (Finset.univ.filter (fun v : V => v ≠ y)) = Finset.univ.erase y by ext z; simp]
      exact Finset.card_erase_add_one (Finset.mem_univ y)
    omega
  have hN_eq : ∀ z : V, G.Adj y z → z = a ∨ z = b ∨ z = c := by
    intro z hzy
    have hsub : ({a, b, c} : Finset V) ⊆ G.neighborFinset y := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with h | h | h
      · rw [h]; exact (G.mem_neighborFinset y a).mpr hya
      · rw [h]; exact (G.mem_neighborFinset y b).mpr hyb
      · rw [h]; exact (G.mem_neighborFinset y c).mpr hyc
    have hcard3 : ({a, b, c} : Finset V).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
          Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
    have heq : ({a, b, c} : Finset V) = G.neighborFinset y :=
      Finset.eq_of_subset_of_card_le hsub (by rw [G.card_neighborFinset_eq_degree, hy, hcard3])
    have hzmem : z ∈ ({a, b, c} : Finset V) := by rw [heq]; exact (G.mem_neighborFinset y z).mpr hzy
    simpa using hzmem
  have hdegH : ∀ v : {u : V // u ≠ y}, H.degree v + (if G.Adj v.1 y then 1 else 0) = G.degree v.1 := by
    intro v
    rw [← H.card_neighborFinset_eq_degree, ← G.card_neighborFinset_eq_degree]
    let e : H.neighborFinset v ≃ (G.neighborFinset v.1).erase y :=
      { toFun := fun u => ⟨u.1.1, Finset.mem_erase.mpr ⟨u.1.2, (G.mem_neighborFinset _ _).mpr ((H.mem_neighborFinset _ _).mp u.2)⟩⟩
        invFun := fun u => ⟨⟨u.1, (Finset.mem_erase.mp u.2).1⟩,
          (H.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp u.2).2)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hc := Fintype.card_congr e
    simp only [Fintype.card_coe] at hc
    rw [hc]
    by_cases hvy : G.Adj v.1 y
    · simp only [hvy, ↓reduceIte]
      exact Finset.card_erase_add_one ((G.mem_neighborFinset v.1 y).mpr hvy)
    · simp only [hvy, ↓reduceIte, Nat.add_zero]
      exact congrArg Finset.card (Finset.erase_eq_of_notMem (fun hm' => hvy ((G.mem_neighborFinset v.1 y).mp hm')))
  obtain ⟨_, w, hw⟩ := hm.1
  have ha_ne_y : a ≠ y := (G.ne_of_adj hya).symm
  have ha_degH : 3 ≤ H.degree ⟨a, ha_ne_y⟩ := by
    have hd := hdegH ⟨a, ha_ne_y⟩
    dsimp only at hd
    split_ifs at hd <;> omega
  by_cases hwy : w = y
  · subst hwy
    have hnear : Near H := by
      refine ⟨⟨⟨a, ha_ne_y⟩, ha_degH⟩, ⟨⟨a, ha_ne_y⟩, fun v _ => ?_⟩⟩
      have hd := hdegH v
      by_cases hvy : G.Adj v.1 w
      · simp only [hvy, ↓reduceIte] at hd
        rcases hN_eq v.1 hvy.symm with h | h | h <;> rw [h] at hd <;> omega
      · simp only [hvy, ↓reduceIte, Nat.add_zero] at hd
        rw [hd]; exact hw v.1 v.2
    have hpow := hm.2.2.1 _ H hcard_lt hnear
    obtain ⟨k, v₀, cyc, hk, hcyc, hlen⟩ := hpow
    exact hm.2.1 ⟨k, v₀.1, cyc.map ⟨Subtype.val, fun h => h⟩, hk, hcyc.map Subtype.val_injective, by simp [hlen]⟩
  · have hnear : Near H := by
      refine ⟨⟨⟨a, ha_ne_y⟩, ha_degH⟩, ⟨⟨w, hwy⟩, fun v hv => ?_⟩⟩
      have hd := hdegH v
      by_cases hvy : G.Adj v.1 y
      · simp only [hvy, ↓reduceIte] at hd
        rcases hN_eq v.1 hvy.symm with h | h | h <;> rw [h] at hd <;> omega
      · simp only [hvy, ↓reduceIte, Nat.add_zero] at hd
        rw [hd]; exact hw v.1 (fun h => hv (Subtype.ext h))
    have hpow := hm.2.2.1 _ H hcard_lt hnear
    obtain ⟨k, v₀, cyc, hk, hcyc, hlen⟩ := hpow
    exact hm.2.1 ⟨k, v₀.1, cyc.map ⟨Subtype.val, fun h => h⟩, hk, hcyc.map Subtype.val_injective, by simp [hlen]⟩

/-- Fundamental identity for `highPairGraph`:
    `wt(M 1_S) + ∑_{x ∈ S} deg_{F_S}(x) = ∑_{x ∈ S} deg_G(x)`. -/
lemma class_h_syndrome_plus_pair_deg [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (z : {v : V // 4 ≤ G.degree v} → ZMod 2)
    [DecidableRel (highPairGraph G (Finset.univ.filter (fun x => z x = 1))).Adj] :
    let V₄ := {v : V // 4 ≤ G.degree v}
    let V₃ := {v : V // G.degree v = 3}
    let R : V₄ → V₃ → Prop := fun a y => G.Adj a.1 y.1
    let S : Finset V₄ := Finset.univ.filter (fun x => z x = 1)
    let F := highPairGraph G S
    Fintype.card {y : V₃ // syndrome R z y = 1} + (∑ x : S, F.degree x) =
      ∑ x : S, G.degree x.1.1 := by
  classical
  intro V₄ V₃ R S F
  have hdeg_le2 : ∀ y : V₃, Fintype.card {x : S // G.Adj x.1.1 y.1} ≤ 2 := by
    intro y
    by_contra hgt
    have h3 : 3 ≤ Fintype.card {x : S // G.Adj x.1.1 y.1} := by omega
    have hcard_f : (Finset.univ : Finset {x : S // G.Adj x.1.1 y.1}).card ≥ 3 := by simpa using h3
    obtain ⟨t, _, ht_card⟩ := Finset.exists_subset_card_eq hcard_f
    obtain ⟨a, b, c, hab, hac, hbc, _⟩ := Finset.card_eq_three.mp ht_card
    exact cubic_at_most_two_high_neighbors G hm y.1 y.2
      (fun h => hab (Subtype.ext (Subtype.ext (Subtype.ext h))))
      (fun h => hac (Subtype.ext (Subtype.ext (Subtype.ext h))))
      (fun h => hbc (Subtype.ext (Subtype.ext (Subtype.ext h))))
      a.1.1.2 b.1.1.2 c.1.1.2 a.2.symm b.2.symm c.2.symm
  have hdouble : (∑ x : S, G.degree x.1.1) = ∑ y : V₃, Fintype.card {x : S // G.Adj x.1.1 y.1} := by
    have h1 : ∀ x : S, G.degree x.1.1 = Fintype.card {y : V₃ // G.Adj x.1.1 y.1} := by
      intro x
      let e : G.neighborSet x.1.1 ≃ {y : V₃ // G.Adj x.1.1 y.1} :=
        { toFun := fun u => ⟨⟨u.1, high_neighbor_cubic G hm x.1.2 u.2⟩, u.2⟩
          invFun := fun u => ⟨u.1.1, u.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_congr e]
    simp_rw [h1, ← Fintype.card_sigma]
    let e : (Σ x : S, {y : V₃ // G.Adj x.1.1 y.1}) ≃ (Σ y : V₃, {x : S // G.Adj x.1.1 y.1}) :=
      { toFun := fun p => ⟨p.2.1, ⟨p.1, p.2.2⟩⟩
        invFun := fun p => ⟨p.2.1, ⟨p.1, p.2.2⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact Fintype.card_congr e
  have hF_sum : (∑ x : S, F.degree x) =
      ∑ y : V₃, if Fintype.card {x : S // G.Adj x.1.1 y.1} = 2 then 2 else 0 := by
    have huniq_y : ∀ (x₁ x₂ : S) (y₁ y₂ : V₃), x₁ ≠ x₂ →
        G.Adj x₁.1.1 y₁.1 → G.Adj x₂.1.1 y₁.1 → G.Adj x₁.1.1 y₂.1 → G.Adj x₂.1.1 y₂.1 → y₁ = y₂ := by
      intro x₁ x₂ y₁ y₂ hne h1 h2 h3 h4
      by_contra hyne
      have hxv : x₁.1.1 ≠ x₂.1.1 := fun h => hne (Subtype.ext (Subtype.ext h))
      have hyv : y₁.1 ≠ y₂.1 := fun h => hyne (Subtype.ext h)
      exact hm.2.1 (rectangle_power G (G.ne_of_adj h1) hxv (G.ne_of_adj h3)
        (G.ne_of_adj h2).symm hyv (G.ne_of_adj h4) h1 h2.symm h4 h3.symm)
    have hL : (∑ x : S, F.degree x) = Fintype.card (Σ x : S, F.neighborSet x) := by
      rw [Fintype.card_sigma]
      exact Finset.sum_congr rfl (fun x _ => (F.card_neighborSet_eq_degree x).symm)
    let P (y : V₃) := {p : S × S // p.1 ≠ p.2 ∧ G.Adj p.1.1.1 y.1 ∧ G.Adj p.2.1.1 y.1}
    have hP_card : ∀ y : V₃, Fintype.card (P y) =
        if Fintype.card {x : S // G.Adj x.1.1 y.1} = 2 then 2 else 0 := by
      intro y
      by_cases h2 : Fintype.card {x : S // G.Adj x.1.1 y.1} = 2
      · simp only [h2, ↓reduceIte]
        have hcf : (Finset.univ : Finset {x : S // G.Adj x.1.1 y.1}).card = 2 := by simpa using h2
        obtain ⟨a, b, hab, hab_eq⟩ := Finset.card_eq_two.mp hcf
        have habS : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
        let e : Bool ≃ P y :=
          { toFun := fun t => if t then ⟨(a.1, b.1), habS, a.2, b.2⟩ else ⟨(b.1, a.1), habS.symm, b.2, a.2⟩
            invFun := fun p => decide (p.1.1 = a.1)
            left_inv := fun t => by cases t <;> simp [habS.symm]
            right_inv := fun p => by
              have h1 : (⟨p.1.1, p.2.2.1⟩ : {x : S // G.Adj x.1.1 y.1}) ∈ ({a, b} : Finset _) := by
                rw [← hab_eq]; exact Finset.mem_univ _
              have h2' : (⟨p.1.2, p.2.2.2⟩ : {x : S // G.Adj x.1.1 y.1}) ∈ ({a, b} : Finset _) := by
                rw [← hab_eq]; exact Finset.mem_univ _
              simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2'
              rcases h1 with h1a | h1b <;> rcases h2' with h2a | h2b
              · have hp1 : p.1.1 = a.1 := congrArg Subtype.val h1a
                have hp2 : p.1.2 = a.1 := congrArg Subtype.val h2a
                exact False.elim (p.2.1 (hp1.trans hp2.symm))
              · have hp1 : p.1.1 = a.1 := congrArg Subtype.val h1a
                have hp2 : p.1.2 = b.1 := congrArg Subtype.val h2b
                apply Subtype.ext
                simp only [hp1, decide_true, ↓reduceIte]
                exact Prod.ext hp1.symm hp2.symm
              · have hp1 : p.1.1 = b.1 := congrArg Subtype.val h1b
                have hp2 : p.1.2 = a.1 := congrArg Subtype.val h2a
                apply Subtype.ext
                simp only [hp1, decide_eq_false_iff_not.mpr habS.symm, Bool.false_eq_true, ↓reduceIte]
                exact Prod.ext hp1.symm hp2.symm
              · have hp1 : p.1.1 = b.1 := congrArg Subtype.val h1b
                have hp2 : p.1.2 = b.1 := congrArg Subtype.val h2b
                exact False.elim (p.2.1 (hp1.trans hp2.symm)) }
        rw [← Fintype.card_congr e]; rfl
      · simp only [h2, ↓reduceIte]
        apply Fintype.card_eq_zero_iff.mpr
        refine ⟨fun p => ?_⟩
        have hle := hdeg_le2 y
        have hge2 : 2 ≤ Fintype.card {x : S // G.Adj x.1.1 y.1} := by
          let f : Bool → {x : S // G.Adj x.1.1 y.1} := fun t =>
            if t then ⟨p.1.1, p.2.2.1⟩ else ⟨p.1.2, p.2.2.2⟩
          have hf : Function.Injective f := by
            intro t1 t2 ht
            cases t1 <;> cases t2
            · rfl
            · exfalso; exact p.2.1 (congrArg Subtype.val ht).symm
            · exfalso; exact p.2.1 (congrArg Subtype.val ht)
            · rfl
          have hc := Fintype.card_le_of_injective f hf
          rwa [Fintype.card_bool] at hc
        omega
    let f_all : (Σ y : V₃, P y) → (Σ x : S, F.neighborSet x) := fun p =>
      ⟨p.2.1.1, ⟨p.2.1.2, ⟨p.2.2.1, ⟨p.1.1, p.1.2, p.2.2.2.1, p.2.2.2.2⟩⟩⟩⟩
    have hf_inj : Function.Injective f_all := by
      rintro ⟨y1, ⟨⟨x1, x2⟩, hne1, h11, h12⟩⟩ ⟨y2, ⟨⟨x1', x2'⟩, hne2, h21, h22⟩⟩ heq
      have hx1 : x1 = x1' := congrArg Sigma.fst heq
      have hx2 : x2 = x2' := congrArg (fun q : (Σ x : S, F.neighborSet x) => q.2.1) heq
      subst hx1; subst hx2
      have hy : y1 = y2 := huniq_y x1 x2 y1 y2 hne1 h11 h12 h21 h22
      subst hy; rfl
    have hf_surj : Function.Surjective f_all := by
      rintro ⟨x1, ⟨x2, ⟨hne, ⟨w, hw3, h1, h2⟩⟩⟩⟩
      exact ⟨⟨⟨w, hw3⟩, ⟨(x1, x2), hne, h1, h2⟩⟩, rfl⟩
    rw [hL, ← Fintype.card_congr (Equiv.ofBijective f_all ⟨hf_inj, hf_surj⟩), Fintype.card_sigma]
    exact Finset.sum_congr rfl (fun y _ => hP_card y)
  have hwt : Fintype.card {y : V₃ // syndrome R z y = 1} =
      ∑ y : V₃, if Fintype.card {x : S // G.Adj x.1.1 y.1} = 1 then 1 else 0 := by
    rw [Fintype.card_subtype, Finset.card_filter]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    have hmod := support_row_mod R z y
    have hcard_eq : Fintype.card {x : Support z // R x.1 y} = Fintype.card {x : S // G.Adj x.1.1 y.1} := by
      apply Fintype.card_congr
      exact
        { toFun := fun p => ⟨⟨p.1.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, p.1.2⟩⟩, p.2⟩
          invFun := fun p => ⟨⟨p.1.1, (Finset.mem_filter.mp p.1.2).2⟩, p.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rw [hcard_eq] at hmod
    have hle := hdeg_le2 y
    rcases field_cases (syndrome R z y) with h0 | h1
    · rw [h0] at hmod ⊢
      have : (0 : ZMod 2).val = 0 := rfl
      have hne1 : Fintype.card {x : S // G.Adj x.1.1 y.1} ≠ 1 := by omega
      simp [hne1]
    · rw [h1] at hmod ⊢
      have : (1 : ZMod 2).val = 1 := rfl
      have heq1 : Fintype.card {x : S // G.Adj x.1.1 y.1} = 1 := by omega
      simp [heq1]
  rw [hwt, hF_sum, hdouble, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  have hle := hdeg_le2 y
  interval_cases h : Fintype.card {x : S // G.Adj x.1.1 y.1} <;> simp

/-- `highPairGraph G S` is `C4Free` and `NearFree` in Class H `MinimalBad`. -/
lemma highPairGraph_c4_near_free [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G) (hH : HighDefect G)
    (S : Finset {v : V // 4 ≤ G.degree v}) :
    C4Free (highPairGraph G S) ∧ NearFree (highPairGraph G S) := by
  classical
  let F := highPairGraph G S
  let ι : S ↪ V := ⟨fun x => x.1.1, fun _ _ h => Subtype.ext (Subtype.ext h)⟩
  let mid : Sym2 S → V := fun e =>
    if h : ∃ w : V, G.degree w = 3 ∧ ∀ x ∈ e, G.Adj x.1.1 w then
      Classical.choose h
    else
      Classical.choose hm.1.1
  have hmid_spec : ∀ x y : S, F.Adj x y →
      G.degree (mid s(x, y)) = 3 ∧ G.Adj x.1.1 (mid s(x, y)) ∧ G.Adj y.1.1 (mid s(x, y)) := by
    intro x y hxy
    have hex : ∃ w : V, G.degree w = 3 ∧ ∀ z ∈ s(x, y), G.Adj z.1.1 w := by
      obtain ⟨w, hw3, hxw, hyw⟩ := hxy.2
      exact ⟨w, hw3, fun z hz => by rcases Sym2.mem_iff.mp hz with rfl | rfl; exact hxw; exact hyw⟩
    have hsp := Classical.choose_spec hex
    have hmeq : mid s(x, y) = Classical.choose hex := by
      dsimp only [mid]
      exact dite_eq_left.mpr (fun h => absurd hex h)
    have hgoal : ∀ w : V, w = Classical.choose hex →
        G.degree w = 3 ∧ G.Adj x.1.1 w ∧ G.Adj y.1.1 w := by
      rintro _ rfl
      exact ⟨hsp.1, hsp.2 x (Sym2.mem_mk_left x y), hsp.2 y (Sym2.mem_mk_right x y)⟩
    exact hgoal (mid s(x, y)) hmeq
  have hmid_disj : ∀ x y : S, F.Adj x y → ∀ z : S, mid s(x, y) ≠ ι z := by
    intro x y hxy z heq
    have h3 := (hmid_spec x y hxy).1
    have h4 := z.1.2
    change mid s(x, y) = z.1.1 at heq
    rw [heq] at h3; omega
  have hmid_adj : ∀ x y : S, F.Adj x y → G.Adj (ι x) (mid s(x, y)) ∧ G.Adj (mid s(x, y)) (ι y) := by
    intro x y hxy
    exact ⟨(hmid_spec x y hxy).2.1, (hmid_spec x y hxy).2.2.symm⟩
  have hmid_inj : ∀ e₁ e₂ : Sym2 S, e₁ ∈ F.edgeSet → e₂ ∈ F.edgeSet → mid e₁ = mid e₂ → e₁ = e₂ := by
    intro e₁ e₂ h1 h2 heq
    induction e₁ using Sym2.ind with
    | _ a b =>
      induction e₂ using Sym2.ind with
      | _ c d =>
        have hs1 := hmid_spec a b h1
        have hs2 := hmid_spec c d h2
        rw [heq] at hs1
        by_contra hne
        have hab : a.1.1 ≠ b.1.1 := fun h => h1.1 (Subtype.ext (Subtype.ext h))
        have hcd : c.1.1 ≠ d.1.1 := fun h => h2.1 (Subtype.ext (Subtype.ext h))
        by_cases hca : c = a
        · have hdb : d ≠ b := fun h => hne (by rw [hca, h])
          have hdbv : d.1.1 ≠ b.1.1 := fun h => hdb (Subtype.ext (Subtype.ext h))
          have hadv : a.1.1 ≠ d.1.1 := by rw [← hca]; exact hcd
          exact cubic_at_most_two_high_neighbors G hm (mid s(c, d)) hs2.1
            hab hadv hdbv.symm a.1.2 b.1.2 d.1.2 hs1.2.1.symm hs1.2.2.symm hs2.2.2.symm
        · by_cases hcb : c = b
          · have hda : d ≠ a := fun h => hne (by rw [hcb, h, Sym2.eq_swap])
            have hdav : d.1.1 ≠ a.1.1 := fun h => hda (Subtype.ext (Subtype.ext h))
            have hbdv : b.1.1 ≠ d.1.1 := by rw [← hcb]; exact hcd
            exact cubic_at_most_two_high_neighbors G hm (mid s(c, d)) hs2.1
              hab hdav.symm hbdv a.1.2 b.1.2 d.1.2 hs1.2.1.symm hs1.2.2.symm hs2.2.2.symm
          · have hcav : c.1.1 ≠ a.1.1 := fun h => hca (Subtype.ext (Subtype.ext h))
            have hcbv : c.1.1 ≠ b.1.1 := fun h => hcb (Subtype.ext (Subtype.ext h))
            exact cubic_at_most_two_high_neighbors G hm (mid s(c, d)) hs2.1
              hab hcav.symm hcbv.symm a.1.2 b.1.2 c.1.2 hs1.2.1.symm hs1.2.2.symm hs2.2.1.symm
  obtain ⟨w₀, hw₀, _, _⟩ := hH
  have hlt : Fintype.card S < Fintype.card V := by
    apply Fintype.card_lt_of_injective_not_surjective ι ι.injective
    intro hsurj
    obtain ⟨x, hx⟩ := hsurj w₀
    have h4 := x.1.2
    change x.1.1 = w₀ at hx
    rw [hx, hw₀] at h4; omega
  exact aux_pair_graph_power_free G hm F ι mid hmid_disj hmid_adj hmid_inj hlt

/-- Helper: degree sum of `F` equals degree sum of `F.induce Finset.univ`. -/
lemma deg_sum_eq_induce_univ [Fintype α] [DecidableEq α] (F : SimpleGraph α) [DecidableRel F.Adj] :
    (∑ x : α, F.degree x) =
      ∑ x : ((Finset.univ : Finset α) : Set α), (F.induce ((Finset.univ : Finset α) : Set α)).degree x := by
  classical
  let e : ((Finset.univ : Finset α) : Set α) ≃ α := Equiv.subtypeUnivEquiv (fun _ => Finset.mem_univ _)
  rw [← Equiv.sum_comp e.symm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  let en : F.neighborFinset x ≃ (F.induce ((Finset.univ : Finset α) : Set α)).neighborFinset (e.symm x) :=
    { toFun := fun u => ⟨⟨u.1, Finset.mem_univ _⟩,
        (SimpleGraph.mem_neighborFinset (F.induce ((Finset.univ : Finset α) : Set α)) (e.symm x) ⟨u.1, Finset.mem_univ _⟩).mpr
          ((SimpleGraph.mem_neighborFinset F x u.1).mp u.2)⟩
      invFun := fun u => ⟨u.1.1,
        (SimpleGraph.mem_neighborFinset F x u.1.1).mpr
          ((SimpleGraph.mem_neighborFinset (F.induce ((Finset.univ : Finset α) : Set α)) (e.symm x) u.1).mp u.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc := Fintype.card_congr en
  rwa [Fintype.card_coe, Fintype.card_coe] at hc

/-- NEW (Wave 3, Agent #4): Class H Multi-Column Code-Weight >= 6 (for |S| >= 2). -/
theorem class_h_code_weight_ge_six [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G) (hH : HighDefect G)
    (z : {v : V // 4 ≤ G.degree v} → ZMod 2)
    (hS2 : 2 ≤ Fintype.card (Support z)) :
    let V₄ := {v : V // 4 ≤ G.degree v}
    let V₃ := {v : V // G.degree v = 3}
    let R : V₄ → V₃ → Prop := fun a y => G.Adj a.1 y.1
    6 ≤ Fintype.card {y : V₃ // syndrome R z y = 1} := by
  classical
  intro V₄ V₃ R
  let S : Finset V₄ := Finset.univ.filter (fun x => z x = 1)
  have hScard : S.card = Fintype.card (Support z) := by rw [Fintype.card_subtype]
  let F := highPairGraph G S
  have hid : Fintype.card {y : V₃ // syndrome R z y = 1} + (∑ x : S, F.degree x) =
      ∑ x : S, G.degree x.1.1 := class_h_syndrome_plus_pair_deg G hm z
  have ⟨_, hnf⟩ := highPairGraph_c4_near_free G hm hH S
  have hbound := near_free_deg_sum_le F hnf S.card Finset.univ (by simp) (by omega)
  have hdeg_eq := deg_sum_eq_induce_univ F
  have hsum4 : 4 * S.card ≤ ∑ x : S, G.degree x.1.1 := by
    calc 4 * S.card = ∑ _x : S, 4 := by simp [mul_comm]
      _ ≤ ∑ x : S, G.degree x.1.1 := Finset.sum_le_sum (fun x _ => x.1.2)
  omega

/-- NEW (Wave 3, Agent #4): Class H Multi-Column Code-Weight >= 8 (for |S| >= 4). -/
theorem class_h_code_weight_ge_eight [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G) (hH : HighDefect G)
    (z : {v : V // 4 ≤ G.degree v} → ZMod 2)
    (hS4 : 4 ≤ Fintype.card (Support z)) :
    let V₄ := {v : V // 4 ≤ G.degree v}
    let V₃ := {v : V // G.degree v = 3}
    let R : V₄ → V₃ → Prop := fun a y => G.Adj a.1 y.1
    8 ≤ Fintype.card {y : V₃ // syndrome R z y = 1} := by
  classical
  intro V₄ V₃ R
  let S : Finset V₄ := Finset.univ.filter (fun x => z x = 1)
  have hScard : S.card = Fintype.card (Support z) := by rw [Fintype.card_subtype]
  let F := highPairGraph G S
  have hid : Fintype.card {y : V₃ // syndrome R z y = 1} + (∑ x : S, F.degree x) =
      ∑ x : S, G.degree x.1.1 := class_h_syndrome_plus_pair_deg G hm z
  have ⟨hc4, hnf⟩ := highPairGraph_c4_near_free G hm hH S
  have hbound := c4_near_free_deg_sum_le_four F hc4 hnf S.card Finset.univ (by simp) (by omega)
  have hdeg_eq := deg_sum_eq_induce_univ F
  have hsum4 : 4 * S.card ≤ ∑ x : S, G.degree x.1.1 := by
    calc 4 * S.card = ∑ _x : S, 4 := by simp [mul_comm]
      _ ≤ ∑ x : S, G.degree x.1.1 := Finset.sum_le_sum (fun x _ => x.1.2)
  omega

/-- NEW (Wave 3, Agent #4): Class H Multi-Column Code-Weight >= 10 (for |S| >= 6). -/
theorem class_h_code_weight_ge_ten [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G) (hH : HighDefect G)
    (z : {v : V // 4 ≤ G.degree v} → ZMod 2)
    (hS6 : 6 ≤ Fintype.card (Support z)) :
    let V₄ := {v : V // 4 ≤ G.degree v}
    let V₃ := {v : V // G.degree v = 3}
    let R : V₄ → V₃ → Prop := fun a y => G.Adj a.1 y.1
    10 ≤ Fintype.card {y : V₃ // syndrome R z y = 1} := by
  classical
  intro V₄ V₃ R
  let S : Finset V₄ := Finset.univ.filter (fun x => z x = 1)
  have hScard : S.card = Fintype.card (Support z) := by rw [Fintype.card_subtype]
  let F := highPairGraph G S
  have hid : Fintype.card {y : V₃ // syndrome R z y = 1} + (∑ x : S, F.degree x) =
      ∑ x : S, G.degree x.1.1 := class_h_syndrome_plus_pair_deg G hm z
  have ⟨hc4, hnf⟩ := highPairGraph_c4_near_free G hm hH S
  have hbound := c4_near_free_deg_sum_le_six F hc4 hnf S.card Finset.univ (by simp) (by omega)
  have hdeg_eq := deg_sum_eq_induce_univ F
  have hsum4 : 4 * S.card ≤ ∑ x : S, G.degree x.1.1 := by
    calc 4 * S.card = ∑ _x : S, 4 := by simp [mul_comm]
      _ ≤ ∑ x : S, G.degree x.1.1 := Finset.sum_le_sum (fun x _ => x.1.2)
  omega

/-- NEW (Wave 3, Agent #4): Upgraded General Class H Cubic Density Bound. -/
theorem class_h_v3_density_sharp [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G) (hH : HighDefect G) :
    let h := Fintype.card {v : V // 4 ≤ G.degree v}
    let c := Fintype.card {v : V // G.degree v = 3}
    (2 ≤ h → 2 * h + 3 ≤ c) ∧ (4 ≤ h → 2 * h + 4 ≤ c) ∧ (6 ≤ h → 2 * h + 5 ≤ c) := by
  classical
  intro h c
  let V₄ := {v : V // 4 ≤ G.degree v}
  let V₃ := {v : V // G.degree v = 3}
  let z : V₄ → ZMod 2 := fun _ => 1
  let R : V₄ → V₃ → Prop := fun a y => G.Adj a.1 y.1
  let S : Finset V₄ := Finset.univ.filter (fun x => z x = 1)
  have hS_univ : S = Finset.univ := by ext x; simp [S, z]
  have hScard : S.card = h := by rw [hS_univ, Finset.card_univ]
  have hsupp_card : Fintype.card (Support z) = h := by
    rw [Fintype.card_subtype]; simp [z, h, V₄]
  have h2c : (∑ x : S, G.degree x.1.1) + Fintype.card {y : V₃ // syndrome R z y = 1} ≤ 2 * c := by
    have hdeg_le2 : ∀ y : V₃, Fintype.card {x : S // G.Adj x.1.1 y.1} ≤ 2 := by
      intro y
      by_contra hgt
      have h3 : 3 ≤ Fintype.card {x : S // G.Adj x.1.1 y.1} := by omega
      have hcard_f : (Finset.univ : Finset {x : S // G.Adj x.1.1 y.1}).card ≥ 3 := by simpa using h3
      obtain ⟨t, _, ht_card⟩ := Finset.exists_subset_card_eq hcard_f
      obtain ⟨a, b, c', hab, hac, hbc, _⟩ := Finset.card_eq_three.mp ht_card
      exact cubic_at_most_two_high_neighbors G hm y.1 y.2
        (fun h' => hab (Subtype.ext (Subtype.ext (Subtype.ext h'))))
        (fun h' => hac (Subtype.ext (Subtype.ext (Subtype.ext h'))))
        (fun h' => hbc (Subtype.ext (Subtype.ext (Subtype.ext h'))))
        a.1.1.2 b.1.1.2 c'.1.1.2 a.2.symm b.2.symm c'.2.symm
    have hdouble : (∑ x : S, G.degree x.1.1) = ∑ y : V₃, Fintype.card {x : S // G.Adj x.1.1 y.1} := by
      have h1 : ∀ x : S, G.degree x.1.1 = Fintype.card {y : V₃ // G.Adj x.1.1 y.1} := by
        intro x
        let e : G.neighborSet x.1.1 ≃ {y : V₃ // G.Adj x.1.1 y.1} :=
          { toFun := fun u => ⟨⟨u.1, high_neighbor_cubic G hm x.1.2 u.2⟩, u.2⟩
            invFun := fun u => ⟨u.1.1, u.2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
        rw [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_congr e]
      simp_rw [h1, ← Fintype.card_sigma]
      let e : (Σ x : S, {y : V₃ // G.Adj x.1.1 y.1}) ≃ (Σ y : V₃, {x : S // G.Adj x.1.1 y.1}) :=
        { toFun := fun p => ⟨p.2.1, ⟨p.1, p.2.2⟩⟩
          invFun := fun p => ⟨p.2.1, ⟨p.1, p.2.2⟩⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      exact Fintype.card_congr e
    have hwt : Fintype.card {y : V₃ // syndrome R z y = 1} =
        ∑ y : V₃, if Fintype.card {x : S // G.Adj x.1.1 y.1} = 1 then 1 else 0 := by
      rw [Fintype.card_subtype, Finset.card_filter]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      have hmod := support_row_mod R z y
      have hcard_eq : Fintype.card {x : Support z // R x.1 y} = Fintype.card {x : S // G.Adj x.1.1 y.1} := by
        apply Fintype.card_congr
        exact
          { toFun := fun p => ⟨⟨p.1.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, p.1.2⟩⟩, p.2⟩
            invFun := fun p => ⟨⟨p.1.1, (Finset.mem_filter.mp p.1.2).2⟩, p.2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
      rw [hcard_eq] at hmod
      have hle := hdeg_le2 y
      rcases field_cases (syndrome R z y) with h0 | h1
      · rw [h0] at hmod ⊢
        have : (0 : ZMod 2).val = 0 := rfl
        have hne1 : Fintype.card {x : S // G.Adj x.1.1 y.1} ≠ 1 := by omega
        simp [hne1]
      · rw [h1] at hmod ⊢
        have : (1 : ZMod 2).val = 1 := rfl
        have heq1 : Fintype.card {x : S // G.Adj x.1.1 y.1} = 1 := by omega
        simp [heq1]
    rw [hdouble, hwt, ← Finset.sum_add_distrib]
    calc (∑ y : V₃, (Fintype.card {x : S // G.Adj x.1.1 y.1} +
            if Fintype.card {x : S // G.Adj x.1.1 y.1} = 1 then 1 else 0))
        ≤ ∑ _y : V₃, 2 := by
          refine Finset.sum_le_sum (fun y _ => ?_)
          have hle := hdeg_le2 y
          interval_cases h' : Fintype.card {x : S // G.Adj x.1.1 y.1} <;> simp
      _ = 2 * c := by simp [c, V₃, mul_comm]
  have hsum4 : 4 * h ≤ ∑ x : S, G.degree x.1.1 := by
    calc 4 * h = ∑ _x : S, 4 := by simp [hScard, mul_comm]
      _ ≤ ∑ x : S, G.degree x.1.1 := Finset.sum_le_sum (fun x _ => x.1.2)
  refine ⟨fun h2 => ?_, fun h4 => ?_, fun h6 => ?_⟩
  · have hw : 6 ≤ Fintype.card {y : V₃ // syndrome R z y = 1} :=
      class_h_code_weight_ge_six G hm hH z (by omega)
    omega
  · have hw : 8 ≤ Fintype.card {y : V₃ // syndrome R z y = 1} :=
      class_h_code_weight_ge_eight G hm hH z (by omega)
    omega
  · have hw : 10 ≤ Fintype.card {y : V₃ // syndrome R z y = 1} :=
      class_h_code_weight_ge_ten G hm hH z (by omega)
    omega

/-- NEW (Wave 3, Agent #4): Cubic Independent-Set |J2| + |J3| Bound (applies to C-N-R & all C-*-*). -/
theorem cubic_indep_j2_j3_bound [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G) (hC : Cubic G)
    (I : Finset V) (hindep : ∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y) :
    let J23 := (Finset.univ \ I).filter (fun y => 2 ≤ (I.filter (fun x => G.Adj x y)).card)
    (2 ≤ I.card → J23.card ≤ 2 * I.card - 3) ∧
    (4 ≤ I.card → J23.card ≤ 2 * I.card - 4) ∧
    (6 ≤ I.card → J23.card ≤ 2 * I.card - 5) := by
  classical
  intro J23
  have hpair_ex : ∀ y : J23, ∃ p : I × I, p.1 ≠ p.2 ∧ G.Adj p.1.1 y.1 ∧ G.Adj p.2.1 y.1 := by
    intro y
    have hge2 : 2 ≤ (I.filter (fun x => G.Adj x y.1)).card := (Finset.mem_filter.mp y.2).2
    obtain ⟨t, ht_sub, ht_card⟩ := Finset.exists_subset_card_eq hge2
    obtain ⟨a, b, hab, ht_eq⟩ := Finset.card_eq_two.mp ht_card
    have ha := Finset.mem_filter.mp (ht_sub (show a ∈ t by rw [ht_eq]; simp))
    have hb := Finset.mem_filter.mp (ht_sub (show b ∈ t by rw [ht_eq]; simp))
    exact ⟨(⟨a, ha.1⟩, ⟨b, hb.1⟩), fun h => hab (congrArg Subtype.val h), ha.2, hb.2⟩
  choose pair hpair using hpair_ex
  let F : SimpleGraph I :=
    { Adj := fun a b => ∃ y : J23, s(a, b) = s((pair y).1, (pair y).2)
      symm := ⟨by rintro a b ⟨y, hy⟩; exact ⟨y, by rw [Sym2.eq_swap, hy]⟩⟩
      loopless := ⟨by
        rintro a ⟨y, hy⟩
        have h := Sym2.eq_iff.mp hy
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact (hpair y).1 (h1.symm.trans h2)
        · exact (hpair y).1 (h2.symm.trans h1)⟩ }
  have hpair_inj : Function.Injective (fun y : J23 => s((pair y).1, (pair y).2)) := by
    intro y1 y2 heq
    by_contra hne
    have hyne : y1.1 ≠ y2.1 := fun h => hne (Subtype.ext h)
    have h1 := hpair y1
    have h2 := hpair y2
    have hcase := Sym2.eq_iff.mp heq
    have hab : (pair y1).1.1 ≠ (pair y1).2.1 := fun h => h1.1 (Subtype.ext h)
    rcases hcase with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact hm.2.1 (rectangle_power G (G.ne_of_adj h1.2.1) hab (G.ne_of_adj (ha ▸ h2.2.1))
        (G.ne_of_adj h1.2.2).symm hyne (G.ne_of_adj (hb ▸ h2.2.2))
        h1.2.1 h1.2.2.symm (hb ▸ h2.2.2) (ha ▸ h2.2.1).symm)
    · exact hm.2.1 (rectangle_power G (G.ne_of_adj h1.2.1) hab (G.ne_of_adj (ha ▸ h2.2.2))
        (G.ne_of_adj h1.2.2).symm hyne (G.ne_of_adj (hb ▸ h2.2.1))
        h1.2.1 h1.2.2.symm (hb ▸ h2.2.1) (ha ▸ h2.2.2).symm)
  have hlt : Fintype.card I < Fintype.card V := by
    by_cases hIe : I.Nonempty
    · obtain ⟨x0, hx0⟩ := hIe
      have hpos : 0 < G.degree x0 := by rw [hC x0]; omega
      obtain ⟨y0, hxy0⟩ := (G.degree_pos_iff_exists_adj x0).mp hpos
      have hy0_notI : y0 ∉ I := fun hmI => hindep x0 hx0 y0 hmI hxy0
      apply Fintype.card_lt_of_injective_not_surjective (fun x : I => x.1) Subtype.val_injective
      intro hsurj
      obtain ⟨x, hx⟩ := hsurj y0
      exact hy0_notI (hx ▸ x.2)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hIe, Fintype.card_coe, Finset.card_empty]
      obtain ⟨v0, _⟩ := hm.1.1
      exact Fintype.card_pos_iff.mpr ⟨v0⟩
  let ι : I ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  let mid : Sym2 I → V := fun e =>
    if h : ∃ y : J23, s((pair y).1, (pair y).2) = e then (Classical.choose h).1 else Classical.choose hm.1.1
  have hmid_eq : ∀ y : J23, mid s((pair y).1, (pair y).2) = y.1 := by
    intro y
    have hex : ∃ y' : J23, s((pair y').1, (pair y').2) = s((pair y).1, (pair y).2) := ⟨y, rfl⟩
    simp only [mid, hex, ↓reduceDIte]
    exact congrArg Subtype.val (hpair_inj (Classical.choose_spec hex))
  have hmid_disj : ∀ a b : I, F.Adj a b → ∀ z : I, mid s(a, b) ≠ ι z := by
    rintro a b ⟨y, hy⟩ z heq
    rw [hy, hmid_eq y] at heq
    have hy_notI : y.1 ∉ I := (Finset.mem_sdiff.mp (Finset.mem_filter.mp y.2).1).2
    exact hy_notI (heq ▸ z.2)
  have hmid_adj : ∀ a b : I, F.Adj a b → G.Adj (ι a) (mid s(a, b)) ∧ G.Adj (mid s(a, b)) (ι b) := by
    rintro a b ⟨y, hy⟩
    rw [hy, hmid_eq y]
    rcases Sym2.eq_iff.mp hy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨(hpair y).2.1, (hpair y).2.2.symm⟩
    · exact ⟨(hpair y).2.2, (hpair y).2.1.symm⟩
  have hmid_inj : ∀ e₁ e₂ : Sym2 I, e₁ ∈ F.edgeSet → e₂ ∈ F.edgeSet → mid e₁ = mid e₂ → e₁ = e₂ := by
    intro e₁ e₂ h1 h2 heq
    induction e₁ using Sym2.ind with
    | _ a b =>
      induction e₂ using Sym2.ind with
      | _ c d =>
        obtain ⟨y1, hy1⟩ := (h1 : F.Adj a b)
        obtain ⟨y2, hy2⟩ := (h2 : F.Adj c d)
        rw [hy1, hy2, hmid_eq y1, hmid_eq y2] at heq
        have hy_eq : y1 = y2 := Subtype.ext heq
        rw [hy1, hy2, hy_eq]
  have ⟨hc4, hnf⟩ := aux_pair_graph_power_free G hm F ι mid hmid_disj hmid_adj hmid_inj hlt
  have hhand : 2 * J23.card =
      ∑ a : ((Finset.univ : Finset I) : Set I), (F.induce ((Finset.univ : Finset I) : Set I)).degree a := by
    rw [← deg_sum_eq_induce_univ F]
    have hsum_card : (∑ a : I, F.degree a) = Fintype.card (Σ a : I, F.neighborSet a) := by
      rw [Fintype.card_sigma]
      exact Finset.sum_congr rfl (fun a _ => (F.card_neighborSet_eq_degree a).symm)
    rw [hsum_card]
    let f_to : Bool × J23 → (Σ a : I, F.neighborSet a) := fun p =>
      if p.1 then ⟨(pair p.2).1, ⟨(pair p.2).2, ⟨p.2, rfl⟩⟩⟩
      else ⟨(pair p.2).2, ⟨(pair p.2).1, ⟨p.2, Sym2.eq_swap⟩⟩⟩
    have hf_inj : Function.Injective f_to := by
      rintro ⟨t1, y1⟩ ⟨t2, y2⟩ heq
      have hy_eq : y1 = y2 := by
        apply hpair_inj
        dsimp only
        cases t1 <;> cases t2 <;> simp only [f_to, Bool.false_eq_true, ↓reduceIte] at heq
        · have h1 : (pair y1).2 = (pair y2).2 := congrArg Sigma.fst heq
          have h2 : (pair y1).1 = (pair y2).1 := congrArg (fun p : (Σ a : I, F.neighborSet a) => p.2.1) heq
          rw [h1, h2]
        · have h1 : (pair y1).2 = (pair y2).1 := congrArg Sigma.fst heq
          have h2 : (pair y1).1 = (pair y2).2 := congrArg (fun p : (Σ a : I, F.neighborSet a) => p.2.1) heq
          rw [h1, h2, Sym2.eq_swap]
        · have h1 : (pair y1).1 = (pair y2).2 := congrArg Sigma.fst heq
          have h2 : (pair y1).2 = (pair y2).1 := congrArg (fun p : (Σ a : I, F.neighborSet a) => p.2.1) heq
          rw [h1, h2, Sym2.eq_swap]
        · have h1 : (pair y1).1 = (pair y2).1 := congrArg Sigma.fst heq
          have h2 : (pair y1).2 = (pair y2).2 := congrArg (fun p : (Σ a : I, F.neighborSet a) => p.2.1) heq
          rw [h1, h2]
      subst hy_eq
      cases t1 <;> cases t2
      · rfl
      · exfalso; simp only [f_to, Bool.false_eq_true, ↓reduceIte] at heq
        exact (hpair y1).1 (congrArg Sigma.fst heq).symm
      · exfalso; simp only [f_to, Bool.false_eq_true, ↓reduceIte] at heq
        exact (hpair y1).1 (congrArg Sigma.fst heq)
      · rfl
    have hf_surj : Function.Surjective f_to := by
      rintro ⟨a, ⟨b, ⟨y, hy⟩⟩⟩
      rcases Sym2.eq_iff.mp hy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨(true, y), rfl⟩
      · exact ⟨(false, y), rfl⟩
    rw [← Fintype.card_congr (Equiv.ofBijective f_to ⟨hf_inj, hf_surj⟩),
      Fintype.card_prod, Fintype.card_bool, Fintype.card_coe]
  refine ⟨fun h2 => ?_, fun h4 => ?_, fun h6 => ?_⟩
  · have hb := near_free_deg_sum_le F hnf I.card Finset.univ (by simp) h2
    omega
  · have hb := c4_near_free_deg_sum_le_four F hc4 hnf I.card Finset.univ (by simp) h4
    omega
  · have hb := c4_near_free_deg_sum_le_six F hc4 hnf I.card Finset.univ (by simp) h6
    omega

#print axioms near_free_deg_sum_le
#print axioms c4_near_free_deg_sum_le_four
#print axioms c4_near_free_deg_sum_le_six
#print axioms aux_pair_graph_power_free
#print axioms class_h_code_weight_ge_six
#print axioms class_h_code_weight_ge_eight
#print axioms class_h_code_weight_ge_ten
#print axioms class_h_v3_density_sharp
#print axioms cubic_indep_j2_j3_bound

end E64AuxPair
