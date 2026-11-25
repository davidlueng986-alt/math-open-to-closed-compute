import Core
import Descent
import Incidence

/-!
# Wave 3 Agent #2 — Module 1: Sharp Class H F2 Weight-Enumerator & 8/11 Density Bound
-/

namespace E64Wave3ClassH
open SimpleGraph Erdos64Closure E64Core Erdos64Incidence
open scoped BigOperators
universe u

/-- A closed walk with nodup support.tail and length ≥ 3 is a simple cycle. -/
theorem isCycle_of_support_tail_nodup {W : Type u} {H : SimpleGraph W} {u : W}
    (c : H.Walk u u) (hnd : c.support.tail.Nodup) (hlen : 3 ≤ c.length) :
    c.IsCycle := by
  cases c with
  | nil => simp at hlen
  | @cons _ v _ huv p =>
    have hnd_p : p.support.Nodup := by simpa [Walk.support_cons] using hnd
    have hp_path : p.IsPath := Walk.IsPath.mk' hnd_p
    have hp_len : 2 ≤ p.length := by simp at hlen; omega
    have hnotmem : s(u, v) ∉ p.edges := by
      intro hmem
      cases p with
      | nil => simp at hp_len
      | @cons _ w _ hvw q =>
        simp only [Walk.edges_cons, List.mem_cons] at hmem
        rcases hmem with heq | hq
        · rw [Sym2.eq_iff] at heq
          rcases heq with ⟨h1, _⟩ | ⟨huw, _⟩
          · exact H.ne_of_adj huv h1
          · subst huw
            cases q with
            | nil => simp at hp_len
            | cons _ q' =>
              simp only [Walk.support_cons, List.nodup_cons] at hnd_p
              exact hnd_p.2.1 q'.end_mem_support
        · have hvq : v ∈ q.support := Walk.snd_mem_support_of_mem_edges q hq
          simp only [Walk.support_cons, List.nodup_cons] at hnd_p
          exact hnd_p.1 hvq
    have htrail : (Walk.cons huv p).IsTrail := by
      refine ⟨?_⟩
      simp only [Walk.edges_cons, List.nodup_cons]
      exact ⟨hnotmem, hp_path.isTrail.edges_nodup⟩
    exact ⟨⟨htrail, by simp⟩, hnd⟩

/-- A graph is C4-free iff any two distinct vertices share at most one common neighbor. -/
def NoC4 {W : Type u} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj] : Prop :=
  ∀ u v : W, u ≠ v → (H.neighborFinset u ∩ H.neighborFinset v).card ≤ 1

/-- A graph has no Near induced subgraph. -/
def NoNearSubgraph {W : Type u} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj] : Prop :=
  ∀ (T : Set W) [Fintype T] [DecidableRel (H.induce T).Adj], ¬Near (H.induce T)

/-- Reiman cherry-counting inequality for C4-free graphs: ∑ d(u)(d(u)-1) ≤ n(n-1). -/
theorem c4_free_sum_choose_two_le {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (hc4 : NoC4 H) :
    ∑ u : W, H.degree u * (H.degree u - 1) ≤ Fintype.card W * (Fintype.card W - 1) := by
  classical
  have h1 : ∀ u : W, H.degree u * (H.degree u - 1) =
      ∑ a : W, ∑ b : W, if a ≠ b ∧ H.Adj u a ∧ H.Adj u b then 1 else 0 := by
    intro u
    have hinner : ∀ a : W, (∑ b : W, if a ≠ b ∧ H.Adj u a ∧ H.Adj u b then 1 else 0) =
        if H.Adj u a then H.degree u - 1 else 0 := by
      intro a
      by_cases hua : H.Adj u a
      · simp only [hua, true_and, ite_true]
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
        have hset : (Finset.univ.filter fun b : W => a ≠ b ∧ H.Adj u b) =
            (H.neighborFinset u).erase a := by
          ext b
          simp [SimpleGraph.mem_neighborFinset, ne_comm]
        rw [hset, Finset.card_erase_of_mem ((H.mem_neighborFinset u a).mpr hua),
          SimpleGraph.card_neighborFinset_eq_degree]
      · simp [hua]
    simp_rw [hinner]
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    have hset : (Finset.univ.filter fun a : W => H.Adj u a) = H.neighborFinset u := by
      ext a; simp [SimpleGraph.mem_neighborFinset]
    rw [hset, SimpleGraph.card_neighborFinset_eq_degree]
  simp_rw [h1]
  rw [Finset.sum_comm]
  have hswap2 : (∑ a : W, ∑ u : W, ∑ b : W, if a ≠ b ∧ H.Adj u a ∧ H.Adj u b then 1 else 0) =
      ∑ a : W, ∑ b : W, if a ≠ b then (H.neighborFinset a ∩ H.neighborFinset b).card else 0 := by
    apply Finset.sum_congr rfl; intro a _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro b _
    by_cases hab : a ≠ b
    · rw [if_pos hab]
      have hterm : ∀ u : W, (if a ≠ b ∧ H.Adj u a ∧ H.Adj u b then (1 : ℕ) else 0) =
          if H.Adj u a ∧ H.Adj u b then 1 else 0 := fun u => by simp [hab]
      simp_rw [hterm]
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
      congr 1; ext u
      simp [SimpleGraph.mem_neighborFinset, SimpleGraph.adj_comm]
    · simp [hab]
  rw [hswap2]
  calc
    ∑ a : W, ∑ b : W, (if a ≠ b then (H.neighborFinset a ∩ H.neighborFinset b).card else 0)
        ≤ ∑ a : W, ∑ b : W, (if a ≠ b then 1 else 0) := by
          apply Finset.sum_le_sum; intro a _
          apply Finset.sum_le_sum; intro b _
          by_cases hab : a ≠ b
          · rw [if_pos hab, if_pos hab]; exact hc4 a b hab
          · rw [if_neg hab, if_neg hab]
    _ = ∑ a : W, (Fintype.card W - 1) := by
          apply Finset.sum_congr rfl; intro a _
          rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
          have hset : (Finset.univ.filter fun b : W => a ≠ b) = Finset.univ.erase a := by
            ext b; simp [ne_comm]
          rw [hset, Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ]
    _ = Fintype.card W * (Fintype.card W - 1) := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

private lemma quad_linear_bound (d : ℕ) : 4 * d ≤ d * (d - 1) + 6 := by
  cases d with
  | zero => omega
  | succ k =>
    cases k with
    | zero => omega
    | succ m =>
      cases m with
      | zero => omega
      | succ r =>
        have h1 : 4 * (r + 3) ≤ (r + 3) * (r + 2) + 6 := by nlinarith
        simpa [Nat.add_sub_cancel] using h1

/-- Turán bound ex(4, C4) ≤ 4. -/
theorem c4_free_four_edges_le_four {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (hc4 : NoC4 H) (hcard : Fintype.card W = 4) :
    H.edgeFinset.card ≤ 4 := by
  classical
  by_contra hgt
  have hsum := H.sum_degrees_eq_twice_card_edges
  have hdeg3 : 2 ≤ (Finset.univ.filter fun u : W => H.degree u = 3).card := by
    by_contra hlt
    have hle : ∑ u : W, H.degree u ≤ ∑ u : W, (if H.degree u = 3 then 3 else 2) := by
      apply Finset.sum_le_sum; intro u _
      have hlt4 := H.degree_lt_card_verts u
      split_ifs <;> omega
    have hcalc : ∑ u : W, (if H.degree u = 3 then (3 : ℕ) else 2) =
        2 * Fintype.card W + (Finset.univ.filter fun u : W => H.degree u = 3).card := by
      have h1 : ∀ u : W, (if H.degree u = 3 then (3 : ℕ) else 2) = 2 + (if H.degree u = 3 then 1 else 0) := by
        intro u; split_ifs <;> omega
      simp_rw [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
        Finset.sum_boole, Nat.cast_id]
      omega
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (Finset.univ.filter fun u : W => H.degree u = 3).card)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  have hNa : H.neighborFinset a = Finset.univ.erase a :=
    Finset.eq_of_subset_of_card_le
      (fun x hx => Finset.mem_erase.mpr ⟨(H.ne_of_adj ((H.mem_neighborFinset a x).mp hx)).symm, Finset.mem_univ x⟩)
      (by rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, hcard,
        SimpleGraph.card_neighborFinset_eq_degree, ha])
  have hNb : H.neighborFinset b = Finset.univ.erase b :=
    Finset.eq_of_subset_of_card_le
      (fun x hx => Finset.mem_erase.mpr ⟨(H.ne_of_adj ((H.mem_neighborFinset b x).mp hx)).symm, Finset.mem_univ x⟩)
      (by rw [Finset.card_erase_of_mem (Finset.mem_univ b), Finset.card_univ, hcard,
        SimpleGraph.card_neighborFinset_eq_degree, hb])
  have hcap : H.neighborFinset a ∩ H.neighborFinset b = (Finset.univ.erase a).erase b := by
    rw [hNa, hNb]; ext x; simp [and_comm]
  have hcap_card : (H.neighborFinset a ∩ H.neighborFinset b).card = 2 := by
    rw [hcap, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩),
      Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, hcard]
  have := hc4 a b hab
  omega

/-- Turán bound ex(5, C4) ≤ 6. -/
theorem c4_free_five_edges_le_six {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (hc4 : NoC4 H) (hcard : Fintype.card W = 5) :
    H.edgeFinset.card ≤ 6 := by
  classical
  have hreim := c4_free_sum_choose_two_le H hc4
  rw [hcard] at hreim
  have hsum : ∑ u : W, 4 * H.degree u ≤ ∑ u : W, (H.degree u * (H.degree u - 1) + 6) :=
    Finset.sum_le_sum fun u _ => quad_linear_bound (H.degree u)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hcard] at hsum
  have hhand := H.sum_degrees_eq_twice_card_edges
  simp only [smul_eq_mul] at hsum
  omega

private lemma card_edges_delete_vertex {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (v : W) :
    (H.induce {x : W | x ≠ v}).edgeFinset.card + H.degree v = H.edgeFinset.card := by
  classical
  have hsum1 := (H.induce {x : W | x ≠ v}).sum_degrees_eq_twice_card_edges
  have hsum2 := H.sum_degrees_eq_twice_card_edges
  have hdel : ∀ u : ↑({x : W | x ≠ v} : Set W),
      (H.induce {x : W | x ≠ v}).degree u + (if H.Adj u.1 v then 1 else 0) = H.degree u.1 :=
    fun u => induce_delete_degree H v u
  have htot : (∑ u : ↑({x : W | x ≠ v} : Set W), (H.induce {x : W | x ≠ v}).degree u) +
      (∑ u : ↑({x : W | x ≠ v} : Set W), if H.Adj u.1 v then 1 else 0) =
      ∑ u : ↑({x : W | x ≠ v} : Set W), H.degree u.1 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => hdel u
  have hdegv : (∑ u : ↑({x : W | x ≠ v} : Set W), if H.Adj u.1 v then 1 else 0) = H.degree v := by
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
    have e : {u : ↑({x : W | x ≠ v} : Set W) // H.Adj u.1 v} ≃ H.neighborSet v :=
      { toFun := fun u => ⟨u.1.1, u.2.symm⟩
        invFun := fun x => ⟨⟨x.1, (H.ne_of_adj x.2).symm⟩, x.2.symm⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hc := Fintype.card_congr e
    rw [Fintype.card_subtype, SimpleGraph.card_neighborSet_eq_degree] at hc
    exact hc
  have hsplit : (∑ u : ↑({x : W | x ≠ v} : Set W), H.degree u.1) + H.degree v = ∑ x : W, H.degree x := by
    have h1 : (∑ u : ↑({x : W | x ≠ v} : Set W), H.degree u.1) = ∑ x ∈ Finset.univ.erase v, H.degree x := by
      simpa using (Finset.sum_subtype (Finset.univ.erase v)
        (p := fun x : W => x ∈ ({x : W | x ≠ v} : Set W)) (by intro x; simp) (fun x => H.degree x)).symm
    rw [h1, Finset.sum_erase_add _ _ (Finset.mem_univ v)]
  omega

private lemma noC4_induce {W : Type u} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (hc4 : NoC4 H) (S : Set W) [Fintype S] [DecidableRel (H.induce S).Adj] :
    NoC4 (H.induce S) := by
  classical
  intro a b hab
  have hne : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
  have hle : ((H.induce S).neighborFinset a ∩ (H.induce S).neighborFinset b).card ≤
      (H.neighborFinset a.1 ∩ H.neighborFinset b.1).card := by
    apply Finset.card_le_card_of_injOn (fun x : S => x.1)
    · intro x hx
      have hx' := Finset.mem_inter.mp hx
      exact Finset.mem_inter.mpr
        ⟨(H.mem_neighborFinset a.1 x.1).mpr (((H.induce S).mem_neighborFinset a x).mp hx'.1),
         (H.mem_neighborFinset b.1 x.1).mpr (((H.induce S).mem_neighborFinset b x).mp hx'.2)⟩
    · intro x _ y _ hxy
      exact Subtype.ext hxy
  exact hle.trans (hc4 a.1 b.1 hne)

private lemma c4_free_five_six_has_deg_four {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (hc4 : NoC4 H)
    (hcard : Fintype.card W = 5) (he : H.edgeFinset.card = 6) :
    ∃ u : W, H.degree u = 4 := by
  classical
  by_contra hno4
  have hle3 : ∀ u : W, H.degree u ≤ 3 := fun u => by
    have hlt := H.degree_lt_card_verts u
    have hne : H.degree u ≠ 4 := fun h => hno4 ⟨u, h⟩
    omega
  have hsum := H.sum_degrees_eq_twice_card_edges
  rw [he] at hsum
  have hdeg3_card : 2 ≤ (Finset.univ.filter fun u : W => H.degree u = 3).card := by
    by_contra hlt2
    have hle1 : (Finset.univ.filter fun u : W => H.degree u = 3).card ≤ 1 := by omega
    have hbound : ∑ u : W, H.degree u ≤ ∑ u : W, (if H.degree u = 3 then 3 else 2) := by
      apply Finset.sum_le_sum
      intro u _
      have hu := hle3 u
      split_ifs <;> omega
    have hcalc : ∑ u : W, (if H.degree u = 3 then 3 else 2) =
        2 * Fintype.card W + (Finset.univ.filter fun u : W => H.degree u = 3).card := by
      have h1 : ∀ u : W, (if H.degree u = 3 then (3 : ℕ) else 2) = 2 + (if H.degree u = 3 then 1 else 0) := by
        intro u; split_ifs <;> omega
      simp_rw [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
        Finset.sum_boole, Nat.cast_id]
      omega
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (Finset.univ.filter fun u : W => H.degree u = 3).card)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  by_cases hadj : H.Adj a b
  · let R : Finset W := (Finset.univ.erase a).erase b
    have hRcard : R.card = 3 := by
      have hbmem : b ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩
      rw [Finset.card_erase_of_mem hbmem, Finset.card_erase_of_mem (Finset.mem_univ a),
        Finset.card_univ, hcard]
    let Na := (H.neighborFinset a).erase b
    let Nb := (H.neighborFinset b).erase a
    have hNa_card : Na.card = 2 := by
      rw [Finset.card_erase_of_mem ((H.mem_neighborFinset a b).mpr hadj),
        SimpleGraph.card_neighborFinset_eq_degree, ha]
    have hNb_card : Nb.card = 2 := by
      rw [Finset.card_erase_of_mem ((H.mem_neighborFinset b a).mpr hadj.symm),
        SimpleGraph.card_neighborFinset_eq_degree, hb]
    have hNaR : Na ⊆ R := by
      intro x hx
      have hxb : x ≠ b := (Finset.mem_erase.mp hx).1
      have hax : H.Adj a x := (H.mem_neighborFinset a x).mp (Finset.mem_erase.mp hx).2
      exact Finset.mem_erase.mpr ⟨hxb, Finset.mem_erase.mpr ⟨(H.ne_of_adj hax).symm, Finset.mem_univ x⟩⟩
    have hNbR : Nb ⊆ R := by
      intro x hx
      have hxa : x ≠ a := (Finset.mem_erase.mp hx).1
      have hbx : H.Adj b x := (H.mem_neighborFinset b x).mp (Finset.mem_erase.mp hx).2
      exact Finset.mem_erase.mpr ⟨(H.ne_of_adj hbx).symm, Finset.mem_erase.mpr ⟨hxa, Finset.mem_univ x⟩⟩
    have hunion : (Na ∪ Nb).card ≤ 3 := (Finset.card_le_card (Finset.union_subset hNaR hNbR)).trans hRcard.le
    have hinter_le : (Na ∩ Nb).card ≤ 1 := by
      have hsub : Na ∩ Nb ⊆ H.neighborFinset a ∩ H.neighborFinset b :=
        Finset.inter_subset_inter (Finset.erase_subset _ _) (Finset.erase_subset _ _)
      exact (Finset.card_le_card hsub).trans (hc4 a b hab)
    have hiu := Finset.card_union_add_card_inter Na Nb
    have hinter_eq : (Na ∩ Nb).card = 1 := by omega
    obtain ⟨c1, hc1⟩ := Finset.card_eq_one.mp hinter_eq
    have hc1_mem : c1 ∈ Na ∩ Nb := by rw [hc1]; exact Finset.mem_singleton_self c1
    have hc1_a : H.Adj a c1 := (H.mem_neighborFinset a c1).mp (Finset.mem_erase.mp (Finset.mem_inter.mp hc1_mem).1).2
    have hc1_b : H.Adj b c1 := (H.mem_neighborFinset b c1).mp (Finset.mem_erase.mp (Finset.mem_inter.mp hc1_mem).2).2
    have hNa_rem : (Na.erase c1).card = 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_inter.mp hc1_mem).1, hNa_card]
    obtain ⟨c2, hc2⟩ := Finset.card_eq_one.mp hNa_rem
    have hc2_mem : c2 ∈ Na.erase c1 := by rw [hc2]; exact Finset.mem_singleton_self c2
    have hc2_ne_c1 : c2 ≠ c1 := (Finset.mem_erase.mp hc2_mem).1
    have hc2_ne_b : c2 ≠ b := (Finset.mem_erase.mp (Finset.mem_erase.mp hc2_mem).2).1
    have hc2_a : H.Adj a c2 := (H.mem_neighborFinset a c2).mp (Finset.mem_erase.mp (Finset.mem_erase.mp hc2_mem).2).2
    have hc2_not_b : ¬H.Adj b c2 := by
      intro hbc2
      have hmem : c2 ∈ Na ∩ Nb := Finset.mem_inter.mpr
        ⟨(Finset.mem_erase.mp hc2_mem).2,
         Finset.mem_erase.mpr ⟨(H.ne_of_adj hc2_a).symm, (H.mem_neighborFinset b c2).mpr hbc2⟩⟩
      rw [hc1, Finset.mem_singleton] at hmem
      exact hc2_ne_c1 hmem
    have hNb_rem : (Nb.erase c1).card = 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_inter.mp hc1_mem).2, hNb_card]
    obtain ⟨c3, hc3⟩ := Finset.card_eq_one.mp hNb_rem
    have hc3_mem : c3 ∈ Nb.erase c1 := by rw [hc3]; exact Finset.mem_singleton_self c3
    have hc3_ne_c1 : c3 ≠ c1 := (Finset.mem_erase.mp hc3_mem).1
    have hc3_ne_a : c3 ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hc3_mem).2).1
    have hc3_b : H.Adj b c3 := (H.mem_neighborFinset b c3).mp (Finset.mem_erase.mp (Finset.mem_erase.mp hc3_mem).2).2
    have hc3_not_a : ¬H.Adj a c3 := by
      intro hac3
      have hmem : c3 ∈ Na ∩ Nb := Finset.mem_inter.mpr
        ⟨Finset.mem_erase.mpr ⟨(H.ne_of_adj hc3_b).symm, (H.mem_neighborFinset a c3).mpr hac3⟩,
         (Finset.mem_erase.mp hc3_mem).2⟩
      rw [hc1, Finset.mem_singleton] at hmem
      exact hc3_ne_c1 hmem
    have hc2_ne_c3 : c2 ≠ c3 := fun h => hc3_not_a (h ▸ hc2_a)
    have h12 : ¬H.Adj c1 c2 := by
      intro h
      have hsub : ({b, c2} : Finset W) ⊆ H.neighborFinset a ∩ H.neighborFinset c1 := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hxb | hxc
        · rw [hxb]; exact Finset.mem_inter.mpr ⟨(H.mem_neighborFinset a b).mpr hadj, (H.mem_neighborFinset c1 b).mpr hc1_b.symm⟩
        · rw [hxc]; exact Finset.mem_inter.mpr ⟨(H.mem_neighborFinset a c2).mpr hc2_a, (H.mem_neighborFinset c1 c2).mpr h⟩
      have hc := (Finset.card_le_card hsub).trans (hc4 a c1 (H.ne_of_adj hc1_a))
      rw [Finset.card_pair hc2_ne_b.symm] at hc
      omega
    have h13 : ¬H.Adj c1 c3 := by
      intro h
      have hsub : ({a, c3} : Finset W) ⊆ H.neighborFinset b ∩ H.neighborFinset c1 := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hxa | hxc
        · rw [hxa]; exact Finset.mem_inter.mpr ⟨(H.mem_neighborFinset b a).mpr hadj.symm, (H.mem_neighborFinset c1 a).mpr hc1_a.symm⟩
        · rw [hxc]; exact Finset.mem_inter.mpr ⟨(H.mem_neighborFinset b c3).mpr hc3_b, (H.mem_neighborFinset c1 c3).mpr h⟩
      have hc := (Finset.card_le_card hsub).trans (hc4 b c1 (H.ne_of_adj hc1_b))
      rw [Finset.card_pair hc3_ne_a.symm] at hc
      omega
    have h23 : ¬H.Adj c2 c3 := by
      intro h
      have hsub : ({b, c2} : Finset W) ⊆ H.neighborFinset a ∩ H.neighborFinset c3 := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hxb | hxc
        · rw [hxb]; exact Finset.mem_inter.mpr ⟨(H.mem_neighborFinset a b).mpr hadj, (H.mem_neighborFinset c3 b).mpr hc3_b.symm⟩
        · rw [hxc]; exact Finset.mem_inter.mpr ⟨(H.mem_neighborFinset a c2).mpr hc2_a, (H.mem_neighborFinset c3 c2).mpr h.symm⟩
      have hc := (Finset.card_le_card hsub).trans (hc4 a c3 hc3_ne_a.symm)
      rw [Finset.card_pair hc2_ne_b.symm] at hc
      omega
    have hR_eq : ({c1, c2, c3} : Finset W) = R := by
      apply Finset.eq_of_subset_of_card_le
      · intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl
        · exact hNaR (Finset.mem_inter.mp hc1_mem).1
        · exact hNaR (Finset.mem_erase.mp hc2_mem).2
        · exact hNbR (Finset.mem_erase.mp hc3_mem).2
      · rw [hRcard, Finset.card_insert_of_notMem (by simp [hc2_ne_c1.symm, hc3_ne_c1.symm]),
          Finset.card_pair hc2_ne_c3]
    have hall_v : ∀ x : W, x = a ∨ x = b ∨ x = c1 ∨ x = c2 ∨ x = c3 := by
      intro x
      by_cases hxa : x = a
      · exact Or.inl hxa
      by_cases hxb : x = b
      · exact Or.inr (Or.inl hxb)
      have hxR : x ∈ R := Finset.mem_erase.mpr ⟨hxb, Finset.mem_erase.mpr ⟨hxa, Finset.mem_univ x⟩⟩
      rw [← hR_eq] at hxR
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxR
      rcases hxR with rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    have hdc1 : H.degree c1 ≤ 2 := by
      have hsub : H.neighborFinset c1 ⊆ {a, b} := by
        intro x hx
        have hax := (H.mem_neighborFinset c1 x).mp hx
        rcases hall_v x with h | h | h | h | h
        · rw [h]; simp
        · rw [h]; simp
        · exact False.elim (H.ne_of_adj hax h.symm)
        · exact False.elim (h12 (h ▸ hax))
        · exact False.elim (h13 (h ▸ hax))
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      exact (Finset.card_le_card hsub).trans Finset.card_le_two
    have hdc2 : H.degree c2 ≤ 1 := by
      have hsub : H.neighborFinset c2 ⊆ {a} := by
        intro x hx
        have hax := (H.mem_neighborFinset c2 x).mp hx
        rcases hall_v x with h | h | h | h | h
        · rw [h]; simp
        · exact False.elim (hc2_not_b (h ▸ hax).symm)
        · exact False.elim (h12 (h ▸ hax).symm)
        · exact False.elim (H.ne_of_adj hax h.symm)
        · exact False.elim (h23 (h ▸ hax))
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      exact (Finset.card_le_card hsub).trans (by simp)
    have hdc3 : H.degree c3 ≤ 1 := by
      have hsub : H.neighborFinset c3 ⊆ {b} := by
        intro x hx
        have hax := (H.mem_neighborFinset c3 x).mp hx
        rcases hall_v x with h | h | h | h | h
        · exact False.elim (hc3_not_a (h ▸ hax).symm)
        · rw [h]; simp
        · exact False.elim (h13 (h ▸ hax).symm)
        · exact False.elim (h23 (h ▸ hax).symm)
        · exact False.elim (H.ne_of_adj hax h.symm)
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      exact (Finset.card_le_card hsub).trans (by simp)
    have huniv : (Finset.univ : Finset W) = {a, b, c1, c2, c3} := by
      ext x
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      exact hall_v x
    have ha_not : a ∉ ({b, c1, c2, c3} : Finset W) := by
      simp [hab, H.ne_of_adj hc1_a, H.ne_of_adj hc2_a, hc3_ne_a.symm]
    have hb_not : b ∉ ({c1, c2, c3} : Finset W) := by
      simp [H.ne_of_adj hc1_b, hc2_ne_b.symm, H.ne_of_adj hc3_b]
    have hc1_not : c1 ∉ ({c2, c3} : Finset W) := by
      simp [hc2_ne_c1.symm, hc3_ne_c1.symm]
    rw [huniv, Finset.sum_insert ha_not, Finset.sum_insert hb_not, Finset.sum_insert hc1_not,
      Finset.sum_pair hc2_ne_c3] at hsum
    omega
  · let R : Finset W := (Finset.univ.erase a).erase b
    have hRcard : R.card = 3 := by
      have hbmem : b ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩
      rw [Finset.card_erase_of_mem hbmem, Finset.card_erase_of_mem (Finset.mem_univ a),
        Finset.card_univ, hcard]
    have hNaR : H.neighborFinset a ⊆ R := by
      intro x hx
      have hax := (H.mem_neighborFinset a x).mp hx
      have hxb : x ≠ b := fun h => hadj (h ▸ hax)
      exact Finset.mem_erase.mpr ⟨hxb, Finset.mem_erase.mpr ⟨(H.ne_of_adj hax).symm, Finset.mem_univ x⟩⟩
    have hNbR : H.neighborFinset b ⊆ R := by
      intro x hx
      have hbx := (H.mem_neighborFinset b x).mp hx
      have hxa : x ≠ a := fun h => hadj (h ▸ hbx).symm
      exact Finset.mem_erase.mpr ⟨(H.ne_of_adj hbx).symm, Finset.mem_erase.mpr ⟨hxa, Finset.mem_univ x⟩⟩
    have hNa_eq : H.neighborFinset a = R :=
      Finset.eq_of_subset_of_card_le hNaR (by rw [SimpleGraph.card_neighborFinset_eq_degree, ha, hRcard])
    have hNb_eq : H.neighborFinset b = R :=
      Finset.eq_of_subset_of_card_le hNbR (by rw [SimpleGraph.card_neighborFinset_eq_degree, hb, hRcard])
    have hc := hc4 a b hab
    rw [hNa_eq, hNb_eq, Finset.inter_self, hRcard] at hc
    omega

/-- Turán bound ex(6, C4) ≤ 7. -/
theorem c4_free_six_edges_le_seven {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (hc4 : NoC4 H) (hcard : Fintype.card W = 6) :
    H.edgeFinset.card ≤ 7 := by
  classical
  by_contra hgt
  have hreim := c4_free_sum_choose_two_le H hc4
  rw [hcard] at hreim
  have hsum_lin : ∑ u : W, 4 * H.degree u ≤ ∑ u : W, (H.degree u * (H.degree u - 1) + 6) :=
    Finset.sum_le_sum fun u _ => quad_linear_bound (H.degree u)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hcard] at hsum_lin
  have hhand := H.sum_degrees_eq_twice_card_edges
  simp only [smul_eq_mul] at hsum_lin
  have he_eq : H.edgeFinset.card = 8 := by omega
  have hex_le2 : ∃ v : W, H.degree v ≤ 2 := by
    by_contra hall3
    have hge3 : ∀ v : W, 3 ≤ H.degree v := fun v => by
      by_contra hlt; exact hall3 ⟨v, by omega⟩
    have h18 : 18 ≤ ∑ v : W, H.degree v := by
      calc 18 = ∑ _v : W, 3 := by rw [Finset.sum_const, Finset.card_univ, hcard]; rfl
        _ ≤ ∑ v : W, H.degree v := Finset.sum_le_sum fun v _ => hge3 v
    omega
  obtain ⟨v, hv⟩ := hex_le2
  let S : Set W := {x : W | x ≠ v}
  let H' := H.induce S
  have hScard : Fintype.card S = 5 := by
    rw [Fintype.card_subtype, show (Finset.univ.filter fun x : W => x ∈ S) = Finset.univ.erase v by ext x; simp [S],
      Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, hcard]
  have hH'c4 : NoC4 H' := noC4_induce H hc4 S
  have hH'edges_le : H'.edgeFinset.card ≤ 6 := c4_free_five_edges_le_six H' hH'c4 hScard
  have hdel : H'.edgeFinset.card + H.degree v = H.edgeFinset.card := card_edges_delete_vertex H v
  have hv_eq : H.degree v = 2 := by omega
  have hH'edges : H'.edgeFinset.card = 6 := by omega
  obtain ⟨u0, hu0⟩ := c4_free_five_six_has_deg_four H' hH'c4 hScard hH'edges
  have hu0_univ : ∀ z : S, z ≠ u0 → H'.Adj u0 z := by
    intro z hz
    have hsub : H'.neighborFinset u0 ⊆ Finset.univ.erase u0 := by
      intro x hx
      exact Finset.mem_erase.mpr ⟨(H'.ne_of_adj ((H'.mem_neighborFinset u0 x).mp hx)).symm, Finset.mem_univ x⟩
    have heq : H'.neighborFinset u0 = Finset.univ.erase u0 :=
      Finset.eq_of_subset_of_card_le hsub (by
        rw [Finset.card_erase_of_mem (Finset.mem_univ u0), Finset.card_univ, hScard,
          SimpleGraph.card_neighborFinset_eq_degree, hu0])
    exact (H'.mem_neighborFinset u0 z).mp (heq ▸ Finset.mem_erase.mpr ⟨hz, Finset.mem_univ z⟩)
  have hall_le2 : ∀ z : S, z ≠ u0 → H'.degree z ≤ 2 := by
    intro z hz
    by_contra hge3
    have hcard_er : 2 ≤ ((H'.neighborFinset z).erase u0).card := by
      rw [Finset.card_erase_of_mem ((H'.mem_neighborFinset z u0).mpr (hu0_univ z hz).symm),
        SimpleGraph.card_neighborFinset_eq_degree]
      omega
    have hsub : (H'.neighborFinset z).erase u0 ⊆ H'.neighborFinset z ∩ H'.neighborFinset u0 := by
      intro t ht
      have htu : t ≠ u0 := (Finset.mem_erase.mp ht).1
      exact Finset.mem_inter.mpr ⟨(Finset.mem_erase.mp ht).2, (H'.mem_neighborFinset u0 t).mpr (hu0_univ t htu)⟩
    have hc := (Finset.card_le_card hsub).trans (hH'c4 z u0 hz)
    omega
  have hall_eq2 : ∀ z : S, z ≠ u0 → H'.degree z = 2 := by
    intro z hz
    have hsum' := H'.sum_degrees_eq_twice_card_edges
    rw [hH'edges] at hsum'
    have hadd1 := Finset.sum_erase_add (Finset.univ : Finset S) (fun t => H'.degree t) (Finset.mem_univ u0)
    have hadd2 := Finset.sum_erase_add (Finset.univ.erase u0) (fun t => H'.degree t)
      (Finset.mem_erase.mpr ⟨hz, Finset.mem_univ z⟩)
    have hrem_le : ∑ t ∈ (Finset.univ.erase u0).erase z, H'.degree t ≤ 6 := by
      calc ∑ t ∈ (Finset.univ.erase u0).erase z, H'.degree t
          ≤ ∑ _t ∈ (Finset.univ.erase u0).erase z, 2 :=
            Finset.sum_le_sum fun t ht => hall_le2 t (Finset.mem_erase.mp (Finset.mem_erase.mp ht).2).1
        _ = ((Finset.univ.erase u0).erase z).card * 2 := by rw [Finset.sum_const, smul_eq_mul]
        _ = 6 := by
            rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hz, Finset.mem_univ z⟩),
              Finset.card_erase_of_mem (Finset.mem_univ u0), Finset.card_univ, hScard]
    have hle := hall_le2 z hz
    omega
  have hnb_v : 1 < (H.neighborFinset v).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, hv_eq]; decide
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hnb_v
  have hvx : H.Adj v x := (H.mem_neighborFinset v x).mp hx
  have hvy : H.Adj v y := (H.mem_neighborFinset v y).mp hy
  let x' : S := ⟨x, (H.ne_of_adj hvx).symm⟩
  let y' : S := ⟨y, (H.ne_of_adj hvy).symm⟩
  have hxy' : x' ≠ y' := fun h => hxy (congrArg Subtype.val h)
  have hno_cn : ∀ z' : S, ¬(H'.Adj x' z' ∧ H'.Adj y' z') := by
    intro z' ⟨hxz, hyz⟩
    have hsub : ({v, z'.1} : Finset W) ⊆ H.neighborFinset x ∩ H.neighborFinset y := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with htv | htz
      · rw [htv]; exact Finset.mem_inter.mpr ⟨(H.mem_neighborFinset x v).mpr hvx.symm, (H.mem_neighborFinset y v).mpr hvy.symm⟩
      · rw [htz]; exact Finset.mem_inter.mpr ⟨(H.mem_neighborFinset x z'.1).mpr hxz, (H.mem_neighborFinset y z'.1).mpr hyz⟩
    have hc := (Finset.card_le_card hsub).trans (hc4 x y hxy)
    rw [Finset.card_pair z'.2.symm] at hc
    omega
  by_cases hx0 : x' = u0
  · have hy0 : y' ≠ u0 := fun h => hxy' (hx0.trans h.symm)
    have hdy' := hall_eq2 y' hy0
    have hpos : 0 < ((H'.neighborFinset y').erase u0).card := by
      rw [Finset.card_erase_of_mem ((H'.mem_neighborFinset y' u0).mpr (hu0_univ y' hy0).symm),
        SimpleGraph.card_neighborFinset_eq_degree, hdy']; decide
    obtain ⟨z', hz'⟩ := Finset.card_pos.mp hpos
    have hzu0 : z' ≠ u0 := (Finset.mem_erase.mp hz').1
    have hyz : H'.Adj y' z' := (H'.mem_neighborFinset y' z').mp (Finset.mem_erase.mp hz').2
    exact hno_cn z' ⟨hx0 ▸ hu0_univ z' hzu0, hyz⟩
  · by_cases hy0 : y' = u0
    · have hdx' := hall_eq2 x' hx0
      have hpos : 0 < ((H'.neighborFinset x').erase u0).card := by
        rw [Finset.card_erase_of_mem ((H'.mem_neighborFinset x' u0).mpr (hu0_univ x' hx0).symm),
          SimpleGraph.card_neighborFinset_eq_degree, hdx']; decide
      obtain ⟨z', hz'⟩ := Finset.card_pos.mp hpos
      have hzu0 : z' ≠ u0 := (Finset.mem_erase.mp hz').1
      have hxz : H'.Adj x' z' := (H'.mem_neighborFinset x' z').mp (Finset.mem_erase.mp hz').2
      exact hno_cn z' ⟨hxz, hy0 ▸ hu0_univ z' hzu0⟩
    · exact hno_cn u0 ⟨(hu0_univ x' hx0).symm, (hu0_univ y' hy0).symm⟩

private lemma exists_deg_le_two_of_noNear {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (hnn : NoNearSubgraph H)
    (hcard : 2 ≤ Fintype.card W) : ∃ v : W, H.degree v ≤ 2 := by
  classical
  by_contra hall
  have hge3 : ∀ v : W, 3 ≤ H.degree v := fun v => by
    by_contra hlt; exact hall ⟨v, by omega⟩
  obtain ⟨w⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card W)
  let H1 := H.induce (Set.univ : Set W)
  let _ : DecidableRel H1.Adj := inferInstanceAs (DecidableRel (H.induce (Set.univ : Set W)).Adj)
  have hdeg_eq : ∀ u : (Set.univ : Set W), H1.degree u = H.degree u.1 := by
    intro u
    let e : H1.neighborSet u ≃ H.neighborSet u.1 :=
      { toFun := fun x => ⟨x.1.1, x.2⟩
        invFun := fun x => ⟨⟨x.1, trivial⟩, x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hc := Fintype.card_congr e
    rwa [SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.card_neighborSet_eq_degree] at hc
  have hcard1 : 2 ≤ Fintype.card (Set.univ : Set W) := by simpa using hcard
  have hnear : Near H1 := near_of_except H1 ⟨w, trivial⟩ hcard1 (fun u _ => by rw [hdeg_eq]; exact hge3 u.1)
  exact hnn Set.univ hnear

private lemma noNear_induce {W : Type u} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (hnn : NoNearSubgraph H) (S : Set W) [Fintype S] [DecidableRel (H.induce S).Adj] :
    NoNearSubgraph (H.induce S) := by
  classical
  intro T _ _ hnear
  let T' : Set W := Subtype.val '' T
  let _ : DecidableRel (H.induce T').Adj := Classical.decRel _
  have hmemS : ∀ y : T', y.1 ∈ S := fun y => by
    obtain ⟨a, _, ha⟩ := y.2; exact ha ▸ a.2
  have hmemT : ∀ y : T', (⟨y.1, hmemS y⟩ : S) ∈ T := fun y => by
    obtain ⟨a, haT, ha⟩ := y.2
    have heq : (⟨y.1, hmemS y⟩ : S) = a := Subtype.ext ha.symm
    exact heq ▸ haT
  let e : T ≃ T' :=
    { toFun := fun x => ⟨x.1.1, ⟨x.1, x.2, rfl⟩⟩
      invFun := fun y => ⟨⟨y.1, hmemS y⟩, hmemT y⟩
      left_inv := fun _ => Subtype.ext (Subtype.ext rfl)
      right_inv := fun _ => Subtype.ext rfl }
  have hiso : ((H.induce S).induce T) ≃g (H.induce T') :=
    { toEquiv := e, map_rel_iff' := Iff.rfl }
  have hnear' : Near (H.induce T') := by
    obtain ⟨hge2, w, hw⟩ := hnear
    have hcard_eq : Fintype.card T' = Fintype.card T := (Fintype.card_congr e).symm
    apply near_of_except (H.induce T') (e w) (by omega)
    intro u hu
    have hdeg_eq : (H.induce T').degree u = ((H.induce S).induce T).degree (e.symm u) := by
      have := hiso.degree_eq (e.symm u)
      simpa using this.symm
    rw [hdeg_eq]
    have hne : e.symm u ≠ w := fun h => hu (by rw [← h, e.apply_symm_apply])
    exact hw (e.symm u) hne
  exact hnn T' hnear'

private lemma peel_edges_bound (n0 c : ℕ) (hn0 : 2 ≤ n0)
    (hbase : ∀ (W : Type u) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
      NoC4 H → NoNearSubgraph H → Fintype.card W = n0 → H.edgeFinset.card + c ≤ 2 * n0) :
    ∀ k : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
      NoC4 H → NoNearSubgraph H → Fintype.card W = n0 + k → H.edgeFinset.card + c ≤ 2 * (n0 + k) := by
  intro k
  induction k with
  | zero =>
    intro W _ _ H _ hc4 hnn hcard
    simpa using hbase W H hc4 hnn (by simpa using hcard)
  | succ k ih =>
    intro W _ _ H _ hc4 hnn hcard
    classical
    obtain ⟨v, hv⟩ := exists_deg_le_two_of_noNear H hnn (by omega)
    let S : Set W := {x : W | x ≠ v}
    let H' := H.induce S
    have hScard : Fintype.card S = n0 + k := by
      rw [Fintype.card_subtype, show (Finset.univ.filter fun x : W => x ∈ S) = Finset.univ.erase v by ext x; simp [S],
        Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, hcard]
      omega
    have hih := ih S H' (noC4_induce H hc4 S) (noNear_induce H hnn S) hScard
    have hdel : H'.edgeFinset.card + H.degree v = H.edgeFinset.card := card_edges_delete_vertex H v
    omega

/-- Every C4-free, Near-free simple graph on m ≥ 4 vertices has |E(H)| ≤ 2m - 4. -/
theorem c4_near_free_edges_le_four {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (hc4 : NoC4 H) (hnn : NoNearSubgraph H)
    (hcard : 4 ≤ Fintype.card W) : H.edgeFinset.card + 4 ≤ 2 * Fintype.card W := by
  have hk := peel_edges_bound 4 4 (by omega)
    (fun W _ _ H _ hc4 _ hc => by have := c4_free_four_edges_le_four H hc4 hc; omega)
    (Fintype.card W - 4) W H hc4 hnn (by omega)
  omega

/-- Every C4-free, Near-free simple graph on m ≥ 6 vertices has |E(H)| ≤ 2m - 5. -/
theorem c4_near_free_edges_le_five {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (hc4 : NoC4 H) (hnn : NoNearSubgraph H)
    (hcard : 6 ≤ Fintype.card W) : H.edgeFinset.card + 5 ≤ 2 * Fintype.card W := by
  have hk := peel_edges_bound 6 5 (by omega)
    (fun W _ _ H _ hc4 _ hc => by have := c4_free_six_edges_le_seven H hc4 hc; omega)
    (Fintype.card W - 6) W H hc4 hnn (by omega)
  omega

/-- Every MinimalBad graph is C4-free. -/
theorem minimal_bad_noC4 {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G) : NoC4 G := by
  classical
  intro u v huv
  by_contra hgt
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (G.neighborFinset u ∩ G.neighborFinset v).card)
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at ha hb
  have hau : a ≠ u := (G.ne_of_adj ha.1).symm
  have hav : a ≠ v := (G.ne_of_adj ha.2).symm
  have hbu : b ≠ u := (G.ne_of_adj hb.1).symm
  have hbv : b ≠ v := (G.ne_of_adj hb.2).symm
  let c : G.Walk u u :=
    Walk.cons ha.1 (Walk.cons ha.2.symm (Walk.cons hb.2 (Walk.cons hb.1.symm Walk.nil)))
  have hnd : c.support.tail.Nodup := by
    simp [c, hau, hav, hbu, hbv.symm, huv.symm, hab]
  exact hm.2.1 ⟨2, u, c, le_rfl, isCycle_of_support_tail_nodup c hnd (by simp [c]), rfl⟩

private lemma high_indep {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {x y : V} (hx : 4 ≤ G.degree x) (hy : 4 ≤ G.degree y) : ¬G.Adj x y := by
  classical
  intro hxy
  obtain ⟨_, w, hw⟩ := hm.1
  let H := G \ SimpleGraph.edge x y
  let _ : DecidableRel H.Adj := inferInstanceAs (DecidableRel (G \ SimpleGraph.edge x y).Adj)
  have hcard : 2 ≤ Fintype.card V := by have := G.degree_lt_card_verts x; omega
  have hnear : Near H := by
    apply near_of_except H w hcard
    intro v hv
    have hd := erase_edge_degree G x y hxy v
    change H.degree v + (if v = x ∨ v = y then 1 else 0) = G.degree v at hd
    by_cases hvx : v = x
    · subst hvx; simp at hd; omega
    · by_cases hvy : v = y
      · subst hvy; simp at hd; omega
      · simp [hvx, hvy] at hd; have := hw v hv; omega
  have heq := hm.2.2.2 H sdiff_le hnear
  have h1 : H.Adj x y := heq ▸ hxy
  exact ((SimpleGraph.sdiff_adj G (SimpleGraph.edge x y) x y).mp h1).2
    ((SimpleGraph.edge_adj x y x y).mpr ⟨Or.inl ⟨rfl, rfl⟩, G.ne_of_adj hxy⟩)

private lemma high_nb_cubic {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {x y : V} (hx : 4 ≤ G.degree x) (hxy : G.Adj x y) : G.degree y = 3 := by
  classical
  have hlt4 : G.degree y ≤ 3 := by
    by_contra hge4
    exact high_indep G hm hx (by omega) hxy
  obtain ⟨_, w, hw⟩ := hm.1
  by_contra hne3
  have hwy : w = y := by
    by_contra hne
    have := hw y (Ne.symm hne)
    omega
  subst hwy
  let H := G \ SimpleGraph.edge x w
  let _ : DecidableRel H.Adj := inferInstanceAs (DecidableRel (G \ SimpleGraph.edge x w).Adj)
  have hcard : 2 ≤ Fintype.card V := by have := G.degree_lt_card_verts x; omega
  have hnear : Near H := by
    apply near_of_except H w hcard
    intro v hv
    have hd := erase_edge_degree G x w hxy v
    change H.degree v + (if v = x ∨ v = w then 1 else 0) = G.degree v at hd
    by_cases hvx : v = x
    · subst hvx; simp at hd; omega
    · simp [hvx, hv] at hd; have := hw v hv; omega
  have heq := hm.2.2.2 H sdiff_le hnear
  have h1 : H.Adj x w := heq ▸ hxy
  exact ((SimpleGraph.sdiff_adj G (SimpleGraph.edge x w) x w).mp h1).2
    ((SimpleGraph.edge_adj x w x w).mpr ⟨Or.inl ⟨rfl, rfl⟩, G.ne_of_adj hxy⟩)

/-- No degree-3 vertex has all 3 neighbors in V_{≥4} in MinimalBad G. -/
theorem class_h_no_all_high_cubic {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (y : V) (hy : G.degree y = 3) :
    ((G.neighborFinset y).filter fun x => 4 ≤ G.degree x).card ≤ 2 := by
  classical
  by_contra hgt
  have hle3 : ((G.neighborFinset y).filter fun x => 4 ≤ G.degree x).card ≤ 3 := by
    have := Finset.card_filter_le (G.neighborFinset y) (fun x => 4 ≤ G.degree x)
    rwa [SimpleGraph.card_neighborFinset_eq_degree, hy] at this
  have heq : (G.neighborFinset y).filter (fun x => 4 ≤ G.degree x) = G.neighborFinset y :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by
      rw [SimpleGraph.card_neighborFinset_eq_degree, hy]; omega)
  have hall_high : ∀ x, G.Adj y x → 4 ≤ G.degree x := by
    intro x hxy
    have hmem : x ∈ (G.neighborFinset y).filter (fun x => 4 ≤ G.degree x) := by
      rw [heq]; exact (G.mem_neighborFinset y x).mpr hxy
    exact (Finset.mem_filter.mp hmem).2
  obtain ⟨_, w, hw⟩ := hm.1
  let Sy : Set V := {z : V | z ≠ y}
  let H := G.induce Sy
  let _ : DecidableRel H.Adj := inferInstanceAs (DecidableRel (G.induce Sy).Adj)
  have hVcard : 4 ≤ Fintype.card V := by
    have := G.degree_lt_card_verts y; omega
  have hScard : Fintype.card Sy + 1 = Fintype.card V := by
    rw [Fintype.card_subtype, show (Finset.univ.filter fun z : V => z ∈ Sy) = Finset.univ.erase y by ext z; simp [Sy]]
    exact Finset.card_erase_add_one (Finset.mem_univ y)
  have hnear : Near H := by
    by_cases hwy : w = y
    · obtain ⟨u0⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card Sy)
      apply near_of_except H u0 (by omega)
      intro v _
      have hd := induce_delete_degree G y v
      change H.degree v + (if G.Adj v.1 y then 1 else 0) = G.degree v.1 at hd
      by_cases hadj : G.Adj v.1 y
      · have hh := hall_high v.1 hadj.symm; simp [hadj] at hd; omega
      · simp [hadj] at hd; have := hw v.1 (hwy ▸ v.2); omega
    · apply near_of_except H ⟨w, hwy⟩ (by omega)
      intro v hv
      have hd := induce_delete_degree G y v
      change H.degree v + (if G.Adj v.1 y then 1 else 0) = G.degree v.1 at hd
      by_cases hadj : G.Adj v.1 y
      · have hh := hall_high v.1 hadj.symm; simp [hadj] at hd; omega
      · simp [hadj] at hd; have := hw v.1 (fun h => hv (Subtype.ext h)); omega
  exact hm.2.1 (power_induce G _ (hm.2.2.1 Sy H (by omega) hnear))

/-- The midpoint shadow graph on a subset S ⊆ V_{≥4}. -/
def shadowOnHigh {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : SimpleGraph S where
  Adj a b := a ≠ b ∧ ∃ y : V, G.degree y = 3 ∧ G.Adj a.1 y ∧ G.Adj b.1 y
  symm := ⟨fun _ _ ⟨hne, y, hy, ha, hb⟩ => ⟨hne.symm, y, hy, hb, ha⟩⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

private noncomputable def shadowMid {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    {a b : S} (h : (shadowOnHigh G S).Adj a b) : V :=
  Classical.choose h.2

private lemma shadowMid_spec {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    {a b : S} (h : (shadowOnHigh G S).Adj a b) :
    G.degree (shadowMid G S h) = 3 ∧ G.Adj a.1 (shadowMid G S h) ∧ G.Adj b.1 (shadowMid G S h) :=
  Classical.choose_spec h.2

private noncomputable def liftShadowWalk {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    ∀ {u v : S}, (shadowOnHigh G S).Walk u v → G.Walk u.1 v.1
  | _, _, Walk.nil => Walk.nil
  | _, _, Walk.cons h p =>
    Walk.cons (shadowMid_spec G S h).2.1
      (Walk.cons (shadowMid_spec G S h).2.2.symm (liftShadowWalk G S p))

private lemma liftShadowWalk_length {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    {u v : S} (p : (shadowOnHigh G S).Walk u v) :
    (liftShadowWalk G S p).length = 2 * p.length := by
  induction p with
  | nil => simp [liftShadowWalk]
  | cons h p ih => simp [liftShadowWalk, ih]; omega

private lemma liftShadowWalk_mem {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    {u v : S} (p : (shadowOnHigh G S).Walk u v) (z : V)
    (hz : z ∈ (liftShadowWalk G S p).support.tail) :
    (∃ x : S, x ∈ p.support.tail ∧ z = x.1) ∨
    (∃ (a b : S) (h : (shadowOnHigh G S).Adj a b), s(a, b) ∈ p.edges ∧ z = shadowMid G S h) := by
  induction p with
  | nil => simp [liftShadowWalk] at hz
  | @cons a b w h p ih =>
    simp only [liftShadowWalk, Walk.support_cons, List.tail_cons, List.mem_cons] at hz
    rcases hz with rfl | hz'
    · exact Or.inr ⟨a, b, h, by simp, rfl⟩
    · cases p with
      | nil =>
        simp only [liftShadowWalk, Walk.support_nil, List.mem_singleton] at hz'
        exact Or.inl ⟨b, by simp, hz'⟩
      | @cons _ d _ h2 p2 =>
        have hz_split : z = b.1 ∨ z ∈ (liftShadowWalk G S (Walk.cons h2 p2)).support.tail := by
          simpa [liftShadowWalk, Walk.support_cons, List.tail_cons] using hz'
        rcases hz_split with rfl | hz''
        · exact Or.inl ⟨b, by simp, rfl⟩
        · rcases ih hz'' with ⟨x, hx, rfl⟩ | ⟨a', b', h', he', rfl⟩
          · exact Or.inl ⟨x, List.mem_cons_of_mem b hx, rfl⟩
          · exact Or.inr ⟨a', b', h', List.mem_cons_of_mem s(a, b) he', rfl⟩

private lemma shadowOnHigh_hasPower_lifts {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (S : Finset V) (hS : ∀ x ∈ S, 4 ≤ G.degree x)
    (T : Set S) [Fintype T] [DecidableRel ((shadowOnHigh G S).induce T).Adj] :
    HasPower ((shadowOnHigh G S).induce T) → HasPower G := by
  classical
  rintro ⟨k, v0, c, hk, hc, hlen⟩
  let f : ((shadowOnHigh G S).induce T) →g shadowOnHigh G S := ⟨Subtype.val, fun h => h⟩
  let c' : (shadowOnHigh G S).Walk v0.1 v0.1 := c.map f
  have hc' : c'.IsCycle := (Walk.isCycle_map_iff_of_injective Subtype.val_injective).mpr hc
  have hlen' : c'.length = 2 ^ k := by simpa [c'] using hlen
  have hmid_inj : ∀ {a1 b1 a2 b2 : S} (h1 : (shadowOnHigh G S).Adj a1 b1)
      (h2 : (shadowOnHigh G S).Adj a2 b2),
      shadowMid G S h1 = shadowMid G S h2 → s(a1, b1) = s(a2, b2) := by
    intro a1 b1 a2 b2 h1 h2 heq
    set y := shadowMid G S h1
    have hs1 := shadowMid_spec G S h1
    have hs2 := shadowMid_spec G S h2
    rw [← heq] at hs2
    have hle2 := class_h_no_all_high_cubic G hm y hs1.1
    let A := (G.neighborFinset y).filter (fun x => 4 ≤ G.degree x)
    have ha1A : a1.1 ∈ A := Finset.mem_filter.mpr ⟨(G.mem_neighborFinset y a1.1).mpr hs1.2.1.symm, hS a1.1 a1.2⟩
    have hb1A : b1.1 ∈ A := Finset.mem_filter.mpr ⟨(G.mem_neighborFinset y b1.1).mpr hs1.2.2.symm, hS b1.1 b1.2⟩
    have ha2A : a2.1 ∈ A := Finset.mem_filter.mpr ⟨(G.mem_neighborFinset y a2.1).mpr hs2.2.1.symm, hS a2.1 a2.2⟩
    have hb2A : b2.1 ∈ A := Finset.mem_filter.mpr ⟨(G.mem_neighborFinset y b2.1).mpr hs2.2.2.symm, hS b2.1 b2.2⟩
    have hpair_eq : ({a1.1, b1.1} : Finset V) = A := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with h | h
        · rw [h]; exact ha1A
        · rw [h]; exact hb1A
      · rw [Finset.card_pair (fun h => h1.1 (Subtype.ext h))]; exact hle2
    have ha2_in : a2.1 = a1.1 ∨ a2.1 = b1.1 := by
      have := hpair_eq.symm ▸ ha2A; simpa using this
    have hb2_in : b2.1 = a1.1 ∨ b2.1 = b1.1 := by
      have := hpair_eq.symm ▸ hb2A; simpa using this
    have hne2 : a2.1 ≠ b2.1 := fun h => h2.1 (Subtype.ext h)
    rcases ha2_in with ha | ha <;> rcases hb2_in with hb | hb
    · exact False.elim (hne2 (ha.trans hb.symm))
    · rw [show a2 = a1 from Subtype.ext ha, show b2 = b1 from Subtype.ext hb]
    · rw [show a2 = b1 from Subtype.ext ha, show b2 = a1 from Subtype.ext hb, Sym2.eq_swap]
    · exact False.elim (hne2 (ha.trans hb.symm))
  have hmid_ne_S : ∀ {a b : S} (h : (shadowOnHigh G S).Adj a b) (x : S), shadowMid G S h ≠ x.1 := by
    intro a b h x heq
    have h3 := (shadowMid_spec G S h).1
    have h4 := hS x.1 x.2
    rw [heq] at h3
    omega
  have hlift_nodup : ∀ {u v : S} (p : (shadowOnHigh G S).Walk u v),
      p.support.tail.Nodup → p.edges.Nodup → (liftShadowWalk G S p).support.tail.Nodup := by
    intro u v p hsup hedge
    induction p with
    | nil => simp [liftShadowWalk]
    | @cons a b w h p ih =>
      simp only [Walk.support_cons, List.tail_cons] at hsup
      simp only [Walk.edges_cons, List.nodup_cons] at hedge
      have hsup_tail : p.support.tail.Nodup := by
        cases p with
        | nil => simp
        | cons _ _ => exact (List.nodup_cons.mp hsup).2
      have hih := ih hsup_tail hedge.2
      cases p with
      | nil =>
        simp only [liftShadowWalk, Walk.support_cons, Walk.support_nil, List.tail_cons, List.nodup_cons,
          List.mem_singleton, List.nodup_nil, List.not_mem_nil, not_false_eq_true, and_true]
        exact hmid_ne_S h b
      | @cons _ d _ h2 p2 =>
        have htail_eq : (liftShadowWalk G S (Walk.cons h (Walk.cons h2 p2))).support.tail =
            shadowMid G S h :: b.1 :: (liftShadowWalk G S (Walk.cons h2 p2)).support.tail := by
          simp [liftShadowWalk, Walk.support_cons, List.tail_cons]
        rw [htail_eq, List.nodup_cons, List.nodup_cons]
        refine ⟨?_, ?_, hih⟩
        · intro hmem
          simp only [List.mem_cons] at hmem
          rcases hmem with heq | hmem'
          · exact hmid_ne_S h b heq
          · rcases liftShadowWalk_mem G S (Walk.cons h2 p2) (shadowMid G S h) hmem' with ⟨x, _, heq⟩ | ⟨a', b'', h', he', heq⟩
            · exact hmid_ne_S h x heq
            · exact hedge.1 (hmid_inj h h' heq ▸ he')
        · intro hmem'
          rcases liftShadowWalk_mem G S (Walk.cons h2 p2) b.1 hmem' with ⟨x, hx, heq⟩ | ⟨a', b'', h', _, heq⟩
          · have hxb : x = b := Subtype.ext heq.symm
            subst hxb
            simp only [Walk.support_cons, List.nodup_cons] at hsup
            exact hsup.1 hx
          · exact hmid_ne_S h' b heq.symm
  let L := liftShadowWalk G S c'
  have hL_len : L.length = 2 ^ (k + 1) := by
    rw [liftShadowWalk_length, hlen', pow_succ]
    omega
  have hL_nodup : L.support.tail.Nodup := hlift_nodup c' hc'.support_nodup hc'.isTrail.edges_nodup
  have hL_ge3 : 3 ≤ L.length := by
    have hpow : 8 ≤ 2 ^ (k + 1) := by
      calc 8 = 2 ^ 3 := by decide
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  exact ⟨k + 1, v0.1.1, L, by omega, isCycle_of_support_tail_nodup L hL_nodup hL_ge3, hL_len⟩

private lemma shadowOnHigh_noC4 {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (S : Finset V) (hS : ∀ x ∈ S, 4 ≤ G.degree x)
    [DecidableRel (shadowOnHigh G S).Adj] : NoC4 (shadowOnHigh G S) := by
  classical
  intro u v huv
  by_contra hgt
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp
    (by omega : 1 < ((shadowOnHigh G S).neighborFinset u ∩ (shadowOnHigh G S).neighborFinset v).card)
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at ha hb
  have hau : a ≠ u := ((shadowOnHigh G S).ne_of_adj ha.1).symm
  have hav : a ≠ v := ((shadowOnHigh G S).ne_of_adj ha.2).symm
  have hbu : b ≠ u := ((shadowOnHigh G S).ne_of_adj hb.1).symm
  have hbv : b ≠ v := ((shadowOnHigh G S).ne_of_adj hb.2).symm
  let c : (shadowOnHigh G S).Walk u u :=
    Walk.cons ha.1 (Walk.cons ha.2.symm (Walk.cons hb.2 (Walk.cons hb.1.symm Walk.nil)))
  have hnd : c.support.tail.Nodup := by
    simp [c, hau, hav, hbu, hbv.symm, huv.symm, hab]
  have hcyc : c.IsCycle := isCycle_of_support_tail_nodup c hnd (by simp [c])
  let fU : shadowOnHigh G S →g (shadowOnHigh G S).induce Set.univ :=
    ⟨fun x => ⟨x, trivial⟩, fun h => h⟩
  let cU : ((shadowOnHigh G S).induce Set.univ).Walk ⟨u, trivial⟩ ⟨u, trivial⟩ := c.map fU
  have hcU : cU.IsCycle := (Walk.isCycle_map_iff_of_injective (fun _ _ h => congrArg Subtype.val h)).mpr hcyc
  exact hm.2.1 (shadowOnHigh_hasPower_lifts G hm S hS Set.univ ⟨2, ⟨u, trivial⟩, cU, le_rfl, hcU, by simp [cU, c]⟩)

private lemma shadowOnHigh_noNear {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (S : Finset V) (hS : ∀ x ∈ S, 4 ≤ G.degree x)
    [DecidableRel (shadowOnHigh G S).Adj] : NoNearSubgraph (shadowOnHigh G S) := by
  classical
  intro T _ _ hnear
  have hlt : Fintype.card T < Fintype.card V := by
    by_cases hSne : S.Nonempty
    · obtain ⟨x, hxS⟩ := hSne
      obtain ⟨y, hxy⟩ := (G.degree_pos_iff_exists_adj x).mp (by have := hS x hxS; omega)
      have hy3 := high_nb_cubic G hm (hS x hxS) hxy
      have hyNotS : y ∉ S := fun hy => by have := hS y hy; omega
      have hSlt : S.card < Fintype.card V := by
        have hss : S ⊂ Finset.univ := Finset.ssubset_univ_iff.mpr (fun heq => hyNotS (heq ▸ Finset.mem_univ y))
        simpa [Finset.card_univ] using Finset.card_lt_card hss
      have hTle : Fintype.card T ≤ S.card := by
        simpa [Fintype.card_coe] using Fintype.card_subtype_le (fun x : S => x ∈ T)
      omega
    · have hS0 : S.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hSne)
      have hT_le : Fintype.card T ≤ S.card := by
        simpa [Fintype.card_coe] using Fintype.card_subtype_le (fun x : S => x ∈ T)
      obtain ⟨⟨v, _⟩, _⟩ := hnear
      have hpos : 0 < Fintype.card T := Fintype.card_pos_iff.mpr ⟨v⟩
      omega
  have hpow := hm.2.2.1 T ((shadowOnHigh G S).induce T) hlt hnear
  exact hm.2.1 (shadowOnHigh_hasPower_lifts G hm S hS T hpow)

/-- F2 syndrome weight of a subset S ⊆ V_{≥4} on V_3: count of y ∈ V_3 with odd |N(y) ∩ S|. -/
def highSyndromeWeight {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  (Finset.univ.filter fun y : V => G.degree y = 3 ∧ (S.filter fun x => G.Adj x y).card % 2 = 1).card

private lemma high_syndrome_edge_identity {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (S : Finset V) (hS : ∀ x ∈ S, 4 ≤ G.degree x)
    [DecidableRel (shadowOnHigh G S).Adj] :
    ∑ x ∈ S, G.degree x = highSyndromeWeight G S + 2 * (shadowOnHigh G S).edgeFinset.card := by
  classical
  have hc4 := minimal_bad_noC4 G hm
  have hsum_deg : ∑ x ∈ S, G.degree x =
      ∑ y ∈ Finset.univ.filter (fun y : V => G.degree y = 3), (S.filter fun x => G.Adj x y).card := by
    calc ∑ x ∈ S, G.degree x
        = ∑ x ∈ S, (Finset.univ.filter fun y : V => G.degree y = 3 ∧ G.Adj x y).card := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [← SimpleGraph.card_neighborFinset_eq_degree]
          congr 1; ext y
          simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun h => ⟨high_nb_cubic G hm (hS x hx) h, h⟩, fun h => h.2⟩
      _ = ∑ x ∈ S, ∑ y ∈ Finset.univ.filter (fun y : V => G.degree y = 3), if G.Adj x y then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro y _
          by_cases h3 : G.degree y = 3 <;> by_cases ha : G.Adj x y <;> simp [h3, ha]
      _ = ∑ y ∈ Finset.univ.filter (fun y : V => G.degree y = 3), ∑ x ∈ S, if G.Adj x y then 1 else 0 :=
          Finset.sum_comm
      _ = _ := by
          apply Finset.sum_congr rfl
          intro y _
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have hle2 : ∀ y : V, G.degree y = 3 → (S.filter fun x => G.Adj x y).card ≤ 2 := by
    intro y hy
    have hsub : S.filter (fun x => G.Adj x y) ⊆ (G.neighborFinset y).filter (fun x => 4 ≤ G.degree x) := by
      intro x hx
      simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hx ⊢
      exact ⟨hx.2.symm, hS x hx.1⟩
    exact (Finset.card_le_card hsub).trans (class_h_no_all_high_cubic G hm y hy)
  let V3 := Finset.univ.filter fun y : V => G.degree y = 3
  let J1 := V3.filter fun y => (S.filter fun x => G.Adj x y).card = 1
  let J2 := V3.filter fun y => (S.filter fun x => G.Adj x y).card = 2
  have hJ1_eq : J1.card = highSyndromeWeight G S := by
    unfold highSyndromeWeight
    congr 1; ext y
    simp only [J1, V3, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h3, h1⟩; exact ⟨h3, by omega⟩
    · rintro ⟨h3, hm2⟩; have := hle2 y h3; exact ⟨h3, by omega⟩
  have hsum_part : ∑ y ∈ V3, (S.filter fun x => G.Adj x y).card = J1.card + 2 * J2.card := by
    have hterm : ∀ y ∈ V3, (S.filter fun x => G.Adj x y).card =
        (if (S.filter fun x => G.Adj x y).card = 1 then 1 else 0) +
        2 * (if (S.filter fun x => G.Adj x y).card = 2 then 1 else 0) := by
      intro y hy
      have h3 : G.degree y = 3 := (Finset.mem_filter.mp hy).2
      have hb := hle2 y h3
      split_ifs <;> omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [J1, J2, Finset.sum_boole, Nat.cast_id]
  have hJ2_eq : J2.card = (shadowOnHigh G S).edgeFinset.card := by
    have hmap_ex : ∀ y : J2, ∃ e : (shadowOnHigh G S).edgeFinset,
        ∀ a : S, a ∈ e.1 ↔ G.Adj a.1 y.1 := by
      intro ⟨y, hy⟩
      simp only [J2, V3, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      obtain ⟨a, b, hab, hpair⟩ := Finset.card_eq_two.mp hy.2
      have ha_mem : a ∈ S.filter (fun x => G.Adj x y) := by rw [hpair]; simp
      have hb_mem : b ∈ S.filter (fun x => G.Adj x y) := by rw [hpair]; simp
      have haS : a ∈ S := (Finset.mem_filter.mp ha_mem).1
      have haA : G.Adj a y := (Finset.mem_filter.mp ha_mem).2
      have hbS : b ∈ S := (Finset.mem_filter.mp hb_mem).1
      have hbA : G.Adj b y := (Finset.mem_filter.mp hb_mem).2
      have hadj : (shadowOnHigh G S).Adj ⟨a, haS⟩ ⟨b, hbS⟩ :=
        ⟨fun h => hab (congrArg Subtype.val h), y, hy.1, haA, hbA⟩
      refine ⟨⟨s(⟨a, haS⟩, ⟨b, hbS⟩), (shadowOnHigh G S).mem_edgeFinset.mpr hadj⟩, ?_⟩
      intro c
      simp only [Sym2.mem_iff, Subtype.ext_iff]
      constructor
      · rintro (h | h) <;> rw [h] <;> assumption
      · intro hcy
        have hmem : c.1 ∈ ({a, b} : Finset V) := hpair ▸ Finset.mem_filter.mpr ⟨c.2, hcy⟩
        simpa using hmem
    let f : J2 → (shadowOnHigh G S).edgeFinset := fun y => Classical.choose (hmap_ex y)
    have hf : ∀ y : J2, ∀ a : S, a ∈ (f y).1 ↔ G.Adj a.1 y.1 := fun y => Classical.choose_spec (hmap_ex y)
    have hinj : Function.Injective f := by
      intro y1 y2 heq
      by_contra hne_sub
      have hne : y1.1 ≠ y2.1 := fun h => hne_sub (Subtype.ext h)
      have hy1 := y1.2
      simp only [J2, V3, Finset.mem_filter, Finset.mem_univ, true_and] at hy1
      obtain ⟨a, b, hab, hpair⟩ := Finset.card_eq_two.mp hy1.2
      have ha_mem : a ∈ S.filter (fun x => G.Adj x y1.1) := by rw [hpair]; simp
      have hb_mem : b ∈ S.filter (fun x => G.Adj x y1.1) := by rw [hpair]; simp
      have haS : a ∈ S := (Finset.mem_filter.mp ha_mem).1
      have ha1 : G.Adj a y1.1 := (Finset.mem_filter.mp ha_mem).2
      have hbS : b ∈ S := (Finset.mem_filter.mp hb_mem).1
      have hb1 : G.Adj b y1.1 := (Finset.mem_filter.mp hb_mem).2
      have ha2 : G.Adj a y2.1 := (hf y2 ⟨a, haS⟩).mp (heq ▸ (hf y1 ⟨a, haS⟩).mpr ha1)
      have hb2 : G.Adj b y2.1 := (hf y2 ⟨b, hbS⟩).mp (heq ▸ (hf y1 ⟨b, hbS⟩).mpr hb1)
      have hsub : ({y1.1, y2.1} : Finset V) ⊆ G.neighborFinset a ∩ G.neighborFinset b := by
        intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with h | h
        · rw [h]; exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a _).mpr ha1, (G.mem_neighborFinset b _).mpr hb1⟩
        · rw [h]; exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a _).mpr ha2, (G.mem_neighborFinset b _).mpr hb2⟩
      have hc := (Finset.card_le_card hsub).trans (hc4 a b hab)
      rw [Finset.card_pair hne] at hc
      omega
    have hsurj : Function.Surjective f := by
      rintro ⟨e, he⟩
      induction e using Sym2.ind with
      | _ a b =>
        have hadj : (shadowOnHigh G S).Adj a b := (shadowOnHigh G S).mem_edgeFinset.mp he
        obtain ⟨y, hy3, hay, hby⟩ := hadj.2
        have hyJ2 : y ∈ J2 := by
          simp only [J2, V3, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨hy3, ?_⟩
          have hsub : ({a.1, b.1} : Finset V) ⊆ S.filter (fun x => G.Adj x y) := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with h | h
            · rw [h]; exact Finset.mem_filter.mpr ⟨a.2, hay⟩
            · rw [h]; exact Finset.mem_filter.mpr ⟨b.2, hby⟩
          have hge2 : 2 ≤ (S.filter (fun x => G.Adj x y)).card := by
            have := Finset.card_le_card hsub
            rwa [Finset.card_pair (fun h => hadj.1 (Subtype.ext h))] at this
          have hle := hle2 y hy3
          omega
        refine ⟨⟨y, hyJ2⟩, Subtype.ext ?_⟩
        have hfa : a ∈ (f ⟨y, hyJ2⟩).1 := (hf ⟨y, hyJ2⟩ a).mpr hay
        have hfb : b ∈ (f ⟨y, hyJ2⟩).1 := (hf ⟨y, hyJ2⟩ b).mpr hby
        exact (Sym2.mem_and_mem_iff hadj.1).mp ⟨hfa, hfb⟩
    have hbij := Fintype.card_of_bijective ⟨hinj, hsurj⟩
    simpa only [Fintype.card_coe] using hbij
  rw [hsum_deg, hsum_part, hJ1_eq, hJ2_eq]

/-- Sharp Class H F2 weight bound for |S| ≥ 2:
    wt(M 1_S) + 4|S| ≥ ∑_{x∈S} d(x) + 6. -/
theorem high_code_weight_sharp_ge_six {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (S : Finset V) (hS : ∀ x ∈ S, 4 ≤ G.degree x) (hcard : 2 ≤ S.card) :
    (∑ x ∈ S, G.degree x) + 6 ≤ highSyndromeWeight G S + 4 * S.card := by
  classical
  have hid := high_syndrome_edge_identity G hm S hS
  have hc4 := shadowOnHigh_noC4 G hm S hS
  have hnn := shadowOnHigh_noNear G hm S hS
  by_cases h4 : 4 ≤ S.card
  · have hE := c4_near_free_edges_le_four (shadowOnHigh G S) hc4 hnn (by simpa using h4)
    simp only [Fintype.card_coe] at hE
    omega
  · have hE_le : 2 * (shadowOnHigh G S).edgeFinset.card ≤ S.card * (S.card - 1) := by
      have hsum := (shadowOnHigh G S).sum_degrees_eq_twice_card_edges
      have hle : ∑ u : S, (shadowOnHigh G S).degree u ≤ ∑ _u : S, (S.card - 1) := by
        apply Finset.sum_le_sum; intro u _
        have hlt := (shadowOnHigh G S).degree_lt_card_verts u
        simp only [Fintype.card_coe] at hlt; omega
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul] at hle
      omega
    have h23 : S.card = 2 ∨ S.card = 3 := by omega
    rcases h23 with h2 | h3
    · rw [h2] at hE_le; omega
    · rw [h3] at hE_le; omega

/-- Sharp Class H F2 weight bound for |S| ≥ 4:
    wt(M 1_S) + 4|S| ≥ ∑_{x∈S} d(x) + 8. -/
theorem high_code_weight_sharp_ge_eight {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (S : Finset V) (hS : ∀ x ∈ S, 4 ≤ G.degree x) (hcard : 4 ≤ S.card) :
    (∑ x ∈ S, G.degree x) + 8 ≤ highSyndromeWeight G S + 4 * S.card := by
  classical
  have hid := high_syndrome_edge_identity G hm S hS
  have hc4 := shadowOnHigh_noC4 G hm S hS
  have hnn := shadowOnHigh_noNear G hm S hS
  have hE := c4_near_free_edges_le_four (shadowOnHigh G S) hc4 hnn (by simpa using hcard)
  simp only [Fintype.card_coe] at hE
  omega

/-- Sharp Class H F2 weight bound for |S| ≥ 6:
    wt(M 1_S) + 4|S| ≥ ∑_{x∈S} d(x) + 10. -/
theorem high_code_weight_sharp_ge_ten {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (S : Finset V) (hS : ∀ x ∈ S, 4 ≤ G.degree x) (hcard : 6 ≤ S.card) :
    (∑ x ∈ S, G.degree x) + 10 ≤ highSyndromeWeight G S + 4 * S.card := by
  classical
  have hid := high_syndrome_edge_identity G hm S hS
  have hc4 := shadowOnHigh_noC4 G hm S hS
  have hnn := shadowOnHigh_noNear G hm S hS
  have hE := c4_near_free_edges_le_five (shadowOnHigh G S) hc4 hnn (by simpa using hcard)
  simp only [Fintype.card_coe] at hE
  omega

/-- Sharp Class H cubic vertex count bound for |V_{≥4}| ≥ 6:
    |V_3| + 2|V_{≥4}| ≥ ∑_{x ∈ V_{≥4}} d(x) + 5. -/
theorem class_h_v3_sharp_bound {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (hcard : 6 ≤ (Finset.univ.filter fun x : V => 4 ≤ G.degree x).card) :
    (∑ x ∈ Finset.univ.filter (fun x : V => 4 ≤ G.degree x), G.degree x) + 5 ≤
      (Finset.univ.filter fun y : V => G.degree y = 3).card +
      2 * (Finset.univ.filter fun x : V => 4 ≤ G.degree x).card := by
  classical
  let S := Finset.univ.filter fun x : V => 4 ≤ G.degree x
  have hS : ∀ x ∈ S, 4 ≤ G.degree x := fun x hx => (Finset.mem_filter.mp hx).2
  have hid := high_syndrome_edge_identity G hm S hS
  have hc4 := shadowOnHigh_noC4 G hm S hS
  have hnn := shadowOnHigh_noNear G hm S hS
  have hE := c4_near_free_edges_le_five (shadowOnHigh G S) hc4 hnn (by simpa using hcard)
  simp only [Fintype.card_coe] at hE
  let V3 := Finset.univ.filter fun y : V => G.degree y = 3
  have hle2 : ∀ y : V, G.degree y = 3 → (S.filter fun x => G.Adj x y).card ≤ 2 := by
    intro y hy
    have hsub : S.filter (fun x => G.Adj x y) ⊆ (G.neighborFinset y).filter (fun x => 4 ≤ G.degree x) := by
      intro x hx
      simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hx ⊢
      exact ⟨hx.2.symm, hS x hx.1⟩
    exact (Finset.card_le_card hsub).trans (class_h_no_all_high_cubic G hm y hy)
  have h2v3 : (∑ x ∈ S, G.degree x) + highSyndromeWeight G S ≤ 2 * V3.card := by
    have hsum_deg : ∑ x ∈ S, G.degree x =
        ∑ y ∈ V3, (S.filter fun x => G.Adj x y).card := by
      calc ∑ x ∈ S, G.degree x
          = ∑ x ∈ S, (Finset.univ.filter fun y : V => G.degree y = 3 ∧ G.Adj x y).card := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [← SimpleGraph.card_neighborFinset_eq_degree]
            congr 1; ext y
            simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨fun h => ⟨high_nb_cubic G hm (hS x hx) h, h⟩, fun h => h.2⟩
        _ = ∑ x ∈ S, ∑ y ∈ V3, if G.Adj x y then 1 else 0 := by
            apply Finset.sum_congr rfl; intro x _
            rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_filter]
            apply Finset.sum_congr rfl; intro y _
            by_cases h3 : G.degree y = 3 <;> by_cases ha : G.Adj x y <;> simp [h3, ha]
        _ = ∑ y ∈ V3, ∑ x ∈ S, if G.Adj x y then 1 else 0 := Finset.sum_comm
        _ = _ := by
            apply Finset.sum_congr rfl; intro y _
            rw [Finset.card_eq_sum_ones]
            simp only [S, Finset.sum_filter]
    have hwt : highSyndromeWeight G S =
        ∑ y ∈ V3, if (S.filter fun x => G.Adj x y).card % 2 = 1 then 1 else 0 := by
      unfold highSyndromeWeight
      rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl; intro y _
      by_cases h3 : G.degree y = 3 <;> by_cases hm2 : (S.filter fun x => G.Adj x y).card % 2 = 1 <;>
        simp [h3, hm2]
    rw [hsum_deg, hwt, ← Finset.sum_add_distrib]
    calc ∑ y ∈ V3, ((S.filter fun x => G.Adj x y).card +
            if (S.filter fun x => G.Adj x y).card % 2 = 1 then 1 else 0)
        ≤ ∑ _y ∈ V3, 2 := by
          apply Finset.sum_le_sum
          intro y hy
          have hb := hle2 y (Finset.mem_filter.mp hy).2
          split_ifs <;> omega
      _ = 2 * V3.card := by rw [Finset.sum_const, smul_eq_mul]; omega
  change (∑ x ∈ S, G.degree x) + 5 ≤ V3.card + 2 * S.card
  omega

private lemma no_safe_prunable_v3_of_high {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (x0 : V) (hx0 : 4 ≤ G.degree x0)
    (A : Finset V) (hAne : A.Nonempty) (hAv3 : ∀ y ∈ A, G.degree y = 3)
    (hclosed : ∀ u, u ∉ A → G.degree u ≤ 3 → ∀ y ∈ A, ¬G.Adj u y)
    (hhigh : ∀ x, 4 ≤ G.degree x → (A.filter fun y => G.Adj x y).card ≤ 1) : False := by
  classical
  obtain ⟨_, w, hw⟩ := hm.1
  let SA : Set V := {z : V | z ∉ A}
  let H := G.induce SA
  let _ : DecidableRel H.Adj := inferInstanceAs (DecidableRel (G.induce SA).Adj)
  have hdeg_drop : ∀ z : SA, H.degree z + (A.filter fun y => G.Adj z.1 y).card = G.degree z.1 := by
    intro z
    have hpart : ((G.neighborFinset z.1).filter (fun y => y ∉ A)).card +
        ((G.neighborFinset z.1).filter (fun y => y ∈ A)).card = (G.neighborFinset z.1).card := by
      have := Finset.card_filter_add_card_filter_not (s := G.neighborFinset z.1) (p := fun y => y ∈ A)
      omega
    have he1 : H.degree z = ((G.neighborFinset z.1).filter (fun y => y ∉ A)).card := by
      let e : H.neighborSet z ≃ {y : V // y ∈ (G.neighborFinset z.1).filter (fun y => y ∉ A)} :=
        { toFun := fun u => ⟨u.1.1, Finset.mem_filter.mpr ⟨(G.mem_neighborFinset z.1 u.1.1).mpr u.2, u.1.2⟩⟩
          invFun := fun u => ⟨⟨u.1, (Finset.mem_filter.mp u.2).2⟩, (G.mem_neighborFinset z.1 u.1).mp (Finset.mem_filter.mp u.2).1⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      have hc := Fintype.card_congr e
      rwa [SimpleGraph.card_neighborSet_eq_degree, Fintype.card_coe] at hc
    have he2 : ((G.neighborFinset z.1).filter (fun y => y ∈ A)) = A.filter (fun y => G.Adj z.1 y) := by
      ext y; simp [SimpleGraph.mem_neighborFinset, and_comm]
    rw [SimpleGraph.card_neighborFinset_eq_degree] at hpart
    rw [he1, ← he2]; omega
  have hx0W : x0 ∉ A := fun h => by have := hAv3 x0 h; omega
  have hW_ge2 : 2 ≤ Fintype.card SA := by
    have hd := hdeg_drop ⟨x0, hx0W⟩
    dsimp only at hd
    have hh := hhigh x0 hx0
    have hlt := H.degree_lt_card_verts ⟨x0, hx0W⟩
    omega
  have hge3 : ∀ z : SA, z.1 ≠ w → 3 ≤ H.degree z := by
    intro z hzw
    have hd := hdeg_drop z
    by_cases h4 : 4 ≤ G.degree z.1
    · have hh := hhigh z.1 h4; omega
    · have h0 : (A.filter fun y => G.Adj z.1 y).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro y hy
        exact hclosed z.1 z.2 (by omega) y hy
      have := hw z.1 hzw; omega
  have hWlt : Fintype.card SA < Fintype.card V := by
    obtain ⟨y, hyA⟩ := hAne
    have hss : (Finset.univ.filter fun z : V => z ∈ SA) ⊂ Finset.univ :=
      Finset.ssubset_univ_iff.mpr (fun heq => by
        have hmem : y ∈ Finset.univ := Finset.mem_univ y
        rw [← heq] at hmem
        exact (Finset.mem_filter.mp hmem).2 hyA)
    simpa [Fintype.card_subtype] using Finset.card_lt_card hss
  have hnear : Near H := by
    by_cases hwA : w ∈ A
    · exact near_of_except H ⟨x0, hx0W⟩ hW_ge2 (fun z _ => hge3 z (fun heq => z.2 (heq ▸ hwA)))
    · exact near_of_except H ⟨w, hwA⟩ hW_ge2 (fun z hz => hge3 z (fun heq => hz (Subtype.ext heq)))
  exact hm.2.1 (power_induce G _ (hm.2.2.1 SA H hWlt hnear))

/-- First Lean 4.36.0 kernel verification of the sharp 8/11 density bound for H-N-*
    (triangle-free Class H MinimalBad graphs): 11 * |V_3| ≥ 8 * (|V| - 1). -/
theorem class_h_trifree_density_8_11 {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (htf : ∀ a b c : V, G.Adj a b → G.Adj b c → ¬G.Adj a c)
    (w : V) (hw : G.degree w = 2) (hrest : ∀ v : V, v ≠ w → 3 ≤ G.degree v)
    (x0 : V) (hx0 : 4 ≤ G.degree x0) :
    8 * (Fintype.card V - 1) ≤ 11 * (Finset.univ.filter fun y : V => G.degree y = 3).card := by
  classical
  have hc4 := minimal_bad_noC4 G hm
  let V3 := Finset.univ.filter fun y : V => G.degree y = 3
  let Vhigh := Finset.univ.filter fun x : V => 4 ≤ G.degree x
  let hdeg : V → ℕ := fun y => ((G.neighborFinset y).filter fun x => 4 ≤ G.degree x).card
  let J0 := V3.filter fun y => hdeg y = 0
  let J1 := V3.filter fun y => hdeg y = 1
  let J2 := V3.filter fun y => hdeg y = 2
  have hle2 : ∀ y ∈ V3, hdeg y ≤ 2 := fun y hy => class_h_no_all_high_cubic G hm y (Finset.mem_filter.mp hy).2
  have hV3_part : V3.card = J0.card + J1.card + J2.card := by
    have h1 : ∀ y ∈ V3, (1 : ℕ) = (if hdeg y = 0 then 1 else 0) +
        (if hdeg y = 1 then 1 else 0) + (if hdeg y = 2 then 1 else 0) := by
      intro y hy; have := hle2 y hy; split_ifs <;> omega
    calc V3.card = ∑ _y ∈ V3, 1 := by simp
      _ = ∑ y ∈ V3, ((if hdeg y = 0 then 1 else 0) +
            (if hdeg y = 1 then 1 else 0) + (if hdeg y = 2 then 1 else 0)) := Finset.sum_congr rfl h1
      _ = _ := by simp only [Finset.sum_add_distrib, J0, J1, J2, Finset.sum_boole, Nat.cast_id]
  have hV_part : Fintype.card V = 1 + V3.card + Vhigh.card := by
    have h1 : ∀ v : V, (1 : ℕ) = (if v = w then 1 else 0) +
        (if G.degree v = 3 then 1 else 0) + (if 4 ≤ G.degree v then 1 else 0) := by
      intro v
      by_cases hvw : v = w
      · subst hvw; simp [hw]
      · have := hrest v hvw; split_ifs <;> omega
    calc Fintype.card V = ∑ _v : V, 1 := by simp
      _ = ∑ v : V, ((if v = w then 1 else 0) +
            (if G.degree v = 3 then 1 else 0) + (if 4 ≤ G.degree v then 1 else 0)) :=
          Finset.sum_congr rfl fun v _ => h1 v
      _ = _ := by
          simp only [Finset.sum_add_distrib, V3, Vhigh, Finset.sum_boole, Nat.cast_id]
          have : (Finset.univ.filter fun v : V => v = w).card = 1 := by
            rw [show (Finset.univ.filter fun v : V => v = w) = {w} by ext x; simp]; simp
          omega
  have hineq1 : 4 * Vhigh.card ≤ J1.card + 2 * J2.card := by
    have h4 : 4 * Vhigh.card ≤ ∑ x ∈ Vhigh, G.degree x := by
      calc 4 * Vhigh.card = ∑ _x ∈ Vhigh, 4 := by rw [Finset.sum_const, smul_eq_mul]; omega
        _ ≤ ∑ x ∈ Vhigh, G.degree x := Finset.sum_le_sum fun x hx => (Finset.mem_filter.mp hx).2
    have hsum_eq : ∑ x ∈ Vhigh, G.degree x = ∑ y ∈ V3, hdeg y := by
      calc ∑ x ∈ Vhigh, G.degree x
          = ∑ x ∈ Vhigh, ∑ y ∈ V3, if G.Adj x y then 1 else 0 := by
            apply Finset.sum_congr rfl; intro x hx
            rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_sum_ones, ← Finset.sum_filter]
            have hsub : (V3.filter fun y => G.Adj x y) = G.neighborFinset x := by
              ext y; simp only [V3, Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset]
              exact ⟨fun h => h.2, fun h => ⟨high_nb_cubic G hm (Finset.mem_filter.mp hx).2 h, h⟩⟩
            rw [hsub]
        _ = ∑ y ∈ V3, ∑ x ∈ Vhigh, if G.Adj x y then 1 else 0 := Finset.sum_comm
        _ = ∑ y ∈ V3, hdeg y := by
            apply Finset.sum_congr rfl; intro y _
            unfold hdeg
            rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
            congr 1; ext x
            simp [Vhigh, SimpleGraph.mem_neighborFinset, SimpleGraph.adj_comm, and_comm]
    have hsum_part : ∑ y ∈ V3, hdeg y = J1.card + 2 * J2.card := by
      have h1 : ∀ y ∈ V3, hdeg y = (if hdeg y = 1 then 1 else 0) + 2 * (if hdeg y = 2 then 1 else 0) := by
        intro y hy; have := hle2 y hy; split_ifs <;> omega
      rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [J1, J2, Finset.sum_boole, Nat.cast_id]
    omega
  have hy_low_deg : ∀ y ∈ J2, ((G.neighborFinset y).filter fun u => G.degree u ≤ 3).card = 1 := by
    intro y hy
    have hy3 : G.degree y = 3 := (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).2
    have hy2 : hdeg y = 2 := (Finset.mem_filter.mp hy).2
    have hpart := Finset.card_filter_add_card_filter_not (s := G.neighborFinset y) (p := fun u => 4 ≤ G.degree u)
    have hneg : ((G.neighborFinset y).filter fun u => ¬(4 ≤ G.degree u)) =
        (G.neighborFinset y).filter (fun u => G.degree u ≤ 3) := by
      ext u; simp only [Finset.mem_filter]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h1, by omega⟩, fun ⟨h1, h2⟩ => ⟨h1, by omega⟩⟩
    rw [hneg, SimpleGraph.card_neighborFinset_eq_degree, hy3] at hpart
    change hdeg y + ((G.neighborFinset y).filter fun u => G.degree u ≤ 3).card = 3 at hpart
    omega
  have hJ2_no_w : ∀ y ∈ J2, ¬G.Adj w y := by
    intro y hy hwy
    have hy3 : G.degree y = 3 := (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).2
    have hy_other_high : ∀ u, G.Adj y u → u ≠ w → 4 ≤ G.degree u := by
      intro u hyu huw
      by_contra hle3
      have hsub : ({w, u} : Finset V) ⊆ (G.neighborFinset y).filter (fun z => G.degree z ≤ 3) := by
        intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with h | h
        · rw [h]; exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset y w).mpr hwy.symm, by omega⟩
        · rw [h]; exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset y u).mpr hyu, by omega⟩
      have hc := (Finset.card_le_card hsub).trans (hy_low_deg y hy).le
      rw [Finset.card_pair huw.symm] at hc; omega
    let A : Finset V := {w, y}
    let SA : Set V := {z : V | z ∉ A}
    let H := G.induce SA
    let _ : DecidableRel H.Adj := inferInstanceAs (DecidableRel (G.induce SA).Adj)
    have hw_ne_y : w ≠ y := G.ne_of_adj hwy
    have hpos_b2 : 0 < ((G.neighborFinset w).erase y).card := by
      rw [Finset.card_erase_of_mem ((G.mem_neighborFinset w y).mpr hwy),
        SimpleGraph.card_neighborFinset_eq_degree, hw]; decide
    obtain ⟨b2, hb2⟩ := Finset.card_pos.mp hpos_b2
    have hb2_ne_y : b2 ≠ y := (Finset.mem_erase.mp hb2).1
    have hwb2 : G.Adj w b2 := (G.mem_neighborFinset w b2).mp (Finset.mem_erase.mp hb2).2
    have hb2_not_A : b2 ∉ A := by simp [A, (G.ne_of_adj hwb2).symm, hb2_ne_y]
    have hx0_not_A : x0 ∉ A := by
      simp only [A, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => by subst h; omega, fun h => by subst h; omega⟩
    have hdeg_drop : ∀ z : SA, H.degree z + (A.filter fun t => G.Adj z.1 t).card = G.degree z.1 := by
      intro z
      have hpart : ((G.neighborFinset z.1).filter (fun t => t ∉ A)).card +
          ((G.neighborFinset z.1).filter (fun t => t ∈ A)).card = (G.neighborFinset z.1).card := by
        have := Finset.card_filter_add_card_filter_not (s := G.neighborFinset z.1) (p := fun t => t ∈ A)
        omega
      have he1 : H.degree z = ((G.neighborFinset z.1).filter (fun t => t ∉ A)).card := by
        let e : H.neighborSet z ≃ {t : V // t ∈ (G.neighborFinset z.1).filter (fun t => t ∉ A)} :=
          { toFun := fun u => ⟨u.1.1, Finset.mem_filter.mpr ⟨(G.mem_neighborFinset z.1 u.1.1).mpr u.2, u.1.2⟩⟩
            invFun := fun u => ⟨⟨u.1, (Finset.mem_filter.mp u.2).2⟩, (G.mem_neighborFinset z.1 u.1).mp (Finset.mem_filter.mp u.2).1⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
        have hc := Fintype.card_congr e
        rwa [SimpleGraph.card_neighborSet_eq_degree, Fintype.card_coe] at hc
      have he2 : ((G.neighborFinset z.1).filter (fun t => t ∈ A)) = A.filter (fun t => G.Adj z.1 t) := by
        ext t; simp [SimpleGraph.mem_neighborFinset, and_comm]
      rw [SimpleGraph.card_neighborFinset_eq_degree] at hpart
      rw [he1, ← he2]; omega
    have hno_both : ∀ z : SA, (A.filter fun t => G.Adj z.1 t).card ≤ 1 := by
      intro z
      by_contra hgt
      have hcard2 : (A.filter fun t => G.Adj z.1 t).card = 2 := by
        have hle := Finset.card_filter_le A (fun t => G.Adj z.1 t)
        rw [Finset.card_pair hw_ne_y] at hle; omega
      have heq : A.filter (fun t => G.Adj z.1 t) = A :=
        Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by rw [hcard2, Finset.card_pair hw_ne_y])
      have hwm : w ∈ A.filter (fun t => G.Adj z.1 t) := by rw [heq]; simp [A]
      have hym : y ∈ A.filter (fun t => G.Adj z.1 t) := by rw [heq]; simp [A]
      exact htf z.1 w y (Finset.mem_filter.mp hwm).2 hwy (Finset.mem_filter.mp hym).2
    have hW_ge2 : 2 ≤ Fintype.card SA := by
      have hd := hdeg_drop ⟨x0, hx0_not_A⟩
      have hb := hno_both ⟨x0, hx0_not_A⟩
      dsimp only at hd hb
      have hlt := H.degree_lt_card_verts ⟨x0, hx0_not_A⟩
      omega
    have hnear : Near H := by
      apply near_of_except H ⟨b2, hb2_not_A⟩ hW_ge2
      intro z hz
      have hd := hdeg_drop z
      have hb := hno_both z
      by_cases h4 : 4 ≤ G.degree z.1
      · omega
      · have hnw : ¬G.Adj z.1 w := by
          intro hzw
          have hmem : z.1 ∈ (G.neighborFinset w).erase y :=
            Finset.mem_erase.mpr ⟨fun heq => z.2 (by simp [A, heq]), (G.mem_neighborFinset w z.1).mpr hzw.symm⟩
          have h1 : ((G.neighborFinset w).erase y).card = 1 := by
            rw [Finset.card_erase_of_mem ((G.mem_neighborFinset w y).mpr hwy),
              SimpleGraph.card_neighborFinset_eq_degree, hw]
          have hsing : (G.neighborFinset w).erase y = {b2} :=
            (Finset.eq_of_subset_of_card_le (by intro t ht; rw [Finset.mem_singleton] at ht; exact ht ▸ hb2)
              (by rw [h1]; simp)).symm
          rw [hsing, Finset.mem_singleton] at hmem
          exact hz (Subtype.ext hmem)
        have hny : ¬G.Adj z.1 y := fun hzy => h4 (hy_other_high z.1 hzy.symm (fun heq => z.2 (by simp [A, heq])))
        have h0 : (A.filter fun t => G.Adj z.1 t).card = 0 := by
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro t ht; simp only [A, Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with h | h
          · exact h ▸ hnw
          · exact h ▸ hny
        have hzw' : z.1 ≠ w := fun heq => z.2 (by simp [A, heq])
        have := hrest z.1 hzw'
        omega
    have hWlt : Fintype.card SA < Fintype.card V := by
      have hss : (Finset.univ.filter fun z : V => z ∈ SA) ⊂ Finset.univ :=
        Finset.ssubset_univ_iff.mpr (fun heq => by
          have hmem : w ∈ Finset.univ := Finset.mem_univ w
          rw [← heq] at hmem
          exact (Finset.mem_filter.mp hmem).2 (by simp [A]))
      simpa [Fintype.card_subtype] using Finset.card_lt_card hss
    exact hm.2.1 (power_induce G _ (hm.2.2.1 SA H hWlt hnear))
  have hJ2_indep : ∀ y1 ∈ J2, ∀ y2 ∈ J2, ¬G.Adj y1 y2 := by
    intro y1 hy1 y2 hy2 hadj
    have hne : y1 ≠ y2 := G.ne_of_adj hadj
    apply no_safe_prunable_v3_of_high G hm x0 hx0 {y1, y2} ⟨y1, by simp⟩
    · intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hy1).1).2
      · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hy2).1).2
    · intro u hu hule3 y hy huy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy hu
      push Not at hu
      rcases hy with h | h
      · have hsub : ({u, y2} : Finset V) ⊆ (G.neighborFinset y1).filter (fun z => G.degree z ≤ 3) := by
          intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with htu | hty
          · rw [htu]; exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset y1 u).mpr (h ▸ huy).symm, hule3⟩
          · rw [hty]; exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset y1 y2).mpr hadj,
              by have := (Finset.mem_filter.mp (Finset.mem_filter.mp hy2).1).2; omega⟩
        have hc := (Finset.card_le_card hsub).trans (hy_low_deg y1 hy1).le
        rw [Finset.card_pair hu.2] at hc; omega
      · have hsub : ({u, y1} : Finset V) ⊆ (G.neighborFinset y2).filter (fun z => G.degree z ≤ 3) := by
          intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with htu | hty
          · rw [htu]; exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset y2 u).mpr (h ▸ huy).symm, hule3⟩
          · rw [hty]; exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset y2 y1).mpr hadj.symm,
              by have := (Finset.mem_filter.mp (Finset.mem_filter.mp hy1).1).2; omega⟩
        have hc := (Finset.card_le_card hsub).trans (hy_low_deg y2 hy2).le
        rw [Finset.card_pair hu.1] at hc; omega
    · intro x _
      by_contra hgt
      have hcard2 : (({y1, y2} : Finset V).filter fun y => G.Adj x y).card = 2 := by
        have hle := Finset.card_filter_le ({y1, y2} : Finset V) (fun y => G.Adj x y)
        rw [Finset.card_pair hne] at hle; omega
      have heq : ({y1, y2} : Finset V).filter (fun y => G.Adj x y) = {y1, y2} :=
        Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by rw [hcard2, Finset.card_pair hne])
      have hm1 : y1 ∈ ({y1, y2} : Finset V).filter (fun y => G.Adj x y) := by rw [heq]; simp
      have hm2 : y2 ∈ ({y1, y2} : Finset V).filter (fun y => G.Adj x y) := by rw [heq]; simp
      exact htf x y1 y2 (Finset.mem_filter.mp hm1).2 hadj (Finset.mem_filter.mp hm2).2
  have hJ1_deg : ∀ z ∈ J1, (J2.filter fun y => G.Adj z y).card ≤ 1 := by
    intro z hz
    by_contra hgt
    obtain ⟨y1, hy1, y2, hy2, h12⟩ := Finset.one_lt_card.mp (by omega : 1 < (J2.filter fun y => G.Adj z y).card)
    simp only [Finset.mem_filter] at hy1 hy2
    have hz3 : G.degree z = 3 := (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2
    have hz1 : hdeg z = 1 := (Finset.mem_filter.mp hz).2
    apply no_safe_prunable_v3_of_high G hm x0 hx0 {z, y1, y2} ⟨z, by simp⟩
    · intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact hz3
      · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hy1.1).1).2
      · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hy2.1).1).2
    · intro u hu hule3 y hy huy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy hu
      push Not at hu
      rcases hy with h | h | h
      · have hpart := Finset.card_filter_add_card_filter_not (s := G.neighborFinset z) (p := fun t => 4 ≤ G.degree t)
        have hneg : ((G.neighborFinset z).filter fun t => ¬(4 ≤ G.degree t)) =
            (G.neighborFinset z).filter (fun t => G.degree t ≤ 3) := by
          ext t; simp only [Finset.mem_filter]
          exact ⟨fun ⟨h1, h2⟩ => ⟨h1, by omega⟩, fun ⟨h1, h2⟩ => ⟨h1, by omega⟩⟩
        rw [hneg, SimpleGraph.card_neighborFinset_eq_degree, hz3] at hpart
        have hlow2 : ((G.neighborFinset z).filter fun t => G.degree t ≤ 3).card = 2 := by
          change hdeg z + _ = 3 at hpart; omega
        have hsub : ({u, y1, y2} : Finset V) ⊆ (G.neighborFinset z).filter (fun t => G.degree t ≤ 3) := by
          intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with ht0 | ht1 | ht2
          · rw [ht0]; exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset z u).mpr (h ▸ huy).symm, hule3⟩
          · rw [ht1]; exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset z y1).mpr hy1.2,
              by have := (Finset.mem_filter.mp (Finset.mem_filter.mp hy1.1).1).2; omega⟩
          · rw [ht2]; exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset z y2).mpr hy2.2,
              by have := (Finset.mem_filter.mp (Finset.mem_filter.mp hy2.1).1).2; omega⟩
        have hc := (Finset.card_le_card hsub).trans hlow2.le
        rw [Finset.card_insert_of_notMem (by simp [hu.2.1, hu.2.2]), Finset.card_pair h12] at hc; omega
      · have hsub : ({u, z} : Finset V) ⊆ (G.neighborFinset y1).filter (fun t => G.degree t ≤ 3) := by
          intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with ht0 | ht1
          · rw [ht0]; exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset y1 u).mpr (h ▸ huy).symm, hule3⟩
          · rw [ht1]; exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset y1 z).mpr hy1.2.symm, by omega⟩
        have hc := (Finset.card_le_card hsub).trans (hy_low_deg y1 hy1.1).le
        rw [Finset.card_pair hu.1] at hc; omega
      · have hsub : ({u, z} : Finset V) ⊆ (G.neighborFinset y2).filter (fun t => G.degree t ≤ 3) := by
          intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with ht0 | ht1
          · rw [ht0]; exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset y2 u).mpr (h ▸ huy).symm, hule3⟩
          · rw [ht1]; exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset y2 z).mpr hy2.2.symm, by omega⟩
        have hc := (Finset.card_le_card hsub).trans (hy_low_deg y2 hy2.1).le
        rw [Finset.card_pair hu.1] at hc; omega
    · intro x hx4
      by_contra hgt2
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (({z, y1, y2} : Finset V).filter fun y => G.Adj x y).card)
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at ha hb
      have hxz : x ≠ z := fun heq => by subst heq; omega
      rcases ha.1 with ha1 | ha1 | ha1 <;> rcases hb.1 with hb1 | hb1 | hb1
      · exact hab (ha1.trans hb1.symm)
      · exact htf x z y1 (ha1 ▸ ha.2) hy1.2 (hb1 ▸ hb.2)
      · exact htf x z y2 (ha1 ▸ ha.2) hy2.2 (hb1 ▸ hb.2)
      · exact htf x z y1 (hb1 ▸ hb.2) hy1.2 (ha1 ▸ ha.2)
      · exact hab (ha1.trans hb1.symm)
      · have hsub : ({y1, y2} : Finset V) ⊆ G.neighborFinset x ∩ G.neighborFinset z := by
          intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with ht1 | ht2
          · rw [ht1]; exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x y1).mpr (ha1 ▸ ha.2), (G.mem_neighborFinset z y1).mpr hy1.2⟩
          · rw [ht2]; exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x y2).mpr (hb1 ▸ hb.2), (G.mem_neighborFinset z y2).mpr hy2.2⟩
        have hc := (Finset.card_le_card hsub).trans (hc4 x z hxz)
        rw [Finset.card_pair h12] at hc; omega
      · exact htf x z y2 (hb1 ▸ hb.2) hy2.2 (ha1 ▸ ha.2)
      · have hsub : ({y1, y2} : Finset V) ⊆ G.neighborFinset x ∩ G.neighborFinset z := by
          intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with ht1 | ht2
          · rw [ht1]; exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x y1).mpr (hb1 ▸ hb.2), (G.mem_neighborFinset z y1).mpr hy1.2⟩
          · rw [ht2]; exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x y2).mpr (ha1 ▸ ha.2), (G.mem_neighborFinset z y2).mpr hy2.2⟩
        have hc := (Finset.card_le_card hsub).trans (hc4 x z hxz)
        rw [Finset.card_pair h12] at hc; omega
      · exact hab (ha1.trans hb1.symm)
  have hJ0_deg : ∀ z ∈ J0, (J2.filter fun y => G.Adj z y).card ≤ 2 := by
    intro z hz
    by_contra hgt
    have hz3 : G.degree z = 3 := (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2
    have hsub_nb : J2.filter (fun y => G.Adj z y) ⊆ G.neighborFinset z := fun y hy =>
      (G.mem_neighborFinset z y).mpr (Finset.mem_filter.mp hy).2
    have heq_nb : J2.filter (fun y => G.Adj z y) = G.neighborFinset z :=
      Finset.eq_of_subset_of_card_le hsub_nb (by rw [SimpleGraph.card_neighborFinset_eq_degree, hz3]; omega)
    let A := insert z (G.neighborFinset z)
    apply no_safe_prunable_v3_of_high G hm x0 hx0 A ⟨z, Finset.mem_insert_self z _⟩
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy'
      · exact hz3
      · rw [← heq_nb] at hy'
        exact (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hy').1).1).2
    · intro u hu hule3 y hy huy
      rcases Finset.mem_insert.mp hy with hyz_eq | hy'
      · exact hu (Finset.mem_insert_of_mem ((G.mem_neighborFinset z u).mpr (hyz_eq ▸ huy).symm))
      · have hyJ2 : y ∈ J2 := (Finset.mem_filter.mp (heq_nb.symm ▸ hy')).1
        have hyz : G.Adj z y := (G.mem_neighborFinset z y).mp hy'
        have huz : u ≠ z := fun h => hu (h ▸ Finset.mem_insert_self z _)
        have hsub : ({u, z} : Finset V) ⊆ (G.neighborFinset y).filter (fun t => G.degree t ≤ 3) := by
          intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with htu | htz
          · rw [htu]; exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset y u).mpr huy.symm, hule3⟩
          · rw [htz]; exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset y z).mpr hyz.symm, by omega⟩
        have hc := (Finset.card_le_card hsub).trans (hy_low_deg y hyJ2).le
        rw [Finset.card_pair huz] at hc; omega
    · intro x hx4
      by_contra hgt2
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (A.filter fun y => G.Adj x y).card)
      simp only [Finset.mem_filter, A, Finset.mem_insert] at ha hb
      have hxz : x ≠ z := fun heq => by subst heq; omega
      rcases ha.1 with ha1 | ha' <;> rcases hb.1 with hb1 | hb'
      · exact hab (ha1.trans hb1.symm)
      · exact htf x z b (ha1 ▸ ha.2) ((G.mem_neighborFinset z b).mp hb') hb.2
      · exact htf x z a (hb1 ▸ hb.2) ((G.mem_neighborFinset z a).mp ha') ha.2
      · have hsub : ({a, b} : Finset V) ⊆ G.neighborFinset x ∩ G.neighborFinset z := by
          intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with hta | htb
          · rw [hta]; exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x a).mpr ha.2, ha'⟩
          · rw [htb]; exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x b).mpr hb.2, hb'⟩
        have hc := (Finset.card_le_card hsub).trans (hc4 x z hxz)
        rw [Finset.card_pair hab] at hc; omega
  have hineq2 : J2.card ≤ J1.card + 2 * J0.card := by
    have hleft : J2.card = ∑ y ∈ J2, ((J0 ∪ J1).filter fun z => G.Adj y z).card := by
      calc J2.card = ∑ _y ∈ J2, 1 := by simp
        _ = ∑ y ∈ J2, ((J0 ∪ J1).filter fun z => G.Adj y z).card := by
          apply Finset.sum_congr rfl; intro y hy
          have h1 := hy_low_deg y hy
          have hsub : ((G.neighborFinset y).filter fun u => G.degree u ≤ 3) =
              ((J0 ∪ J1).filter fun z => G.Adj y z) := by
            ext u
            simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset, Finset.mem_union, J0, J1, V3,
              Finset.mem_univ, true_and]
            constructor
            · rintro ⟨hyu, hle3⟩
              have huw : u ≠ w := fun h => hJ2_no_w y hy (h ▸ hyu).symm
              have hu3 : G.degree u = 3 := by have := hrest u huw; omega
              have hle2u : hdeg u ≤ 2 := hle2 u (Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu3⟩)
              have hne2 : hdeg u ≠ 2 := fun h2 =>
                hJ2_indep y hy u (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu3⟩, h2⟩) hyu
              exact ⟨by omega, hyu⟩
            · rintro ⟨⟨⟨hu3, _⟩ | ⟨hu3, _⟩⟩, hyu⟩ <;> exact ⟨hyu, by omega⟩
          omega
    have hswap : (∑ y ∈ J2, ((J0 ∪ J1).filter fun z => G.Adj y z).card) =
        ∑ z ∈ J0 ∪ J1, (J2.filter fun y => G.Adj z y).card := by
      calc ∑ y ∈ J2, ((J0 ∪ J1).filter fun z => G.Adj y z).card
          = ∑ y ∈ J2, ∑ z ∈ J0 ∪ J1, if G.Adj y z then 1 else 0 := by
            apply Finset.sum_congr rfl; intro y _; rw [Finset.card_eq_sum_ones, Finset.sum_filter]
        _ = ∑ z ∈ J0 ∪ J1, ∑ y ∈ J2, if G.Adj z y then 1 else 0 := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro z _
            apply Finset.sum_congr rfl; intro y _
            simp only [SimpleGraph.adj_comm]
        _ = _ := by
            apply Finset.sum_congr rfl; intro z _; rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    have hdisj : Disjoint J0 J1 := by
      rw [Finset.disjoint_left]; intro z hz0 hz1
      have h0 : hdeg z = 0 := (Finset.mem_filter.mp hz0).2
      have h1 : hdeg z = 1 := (Finset.mem_filter.mp hz1).2
      omega
    rw [Finset.sum_union hdisj] at hswap
    have h0_le : ∑ z ∈ J0, (J2.filter fun y => G.Adj z y).card ≤ 2 * J0.card := by
      calc ∑ z ∈ J0, (J2.filter fun y => G.Adj z y).card
          ≤ ∑ _z ∈ J0, 2 := Finset.sum_le_sum fun z hz => hJ0_deg z hz
        _ = 2 * J0.card := by rw [Finset.sum_const, smul_eq_mul]; omega
    have h1_le : ∑ z ∈ J1, (J2.filter fun y => G.Adj z y).card ≤ J1.card := by
      calc ∑ z ∈ J1, (J2.filter fun y => G.Adj z y).card
          ≤ ∑ _z ∈ J1, 1 := Finset.sum_le_sum fun z hz => hJ1_deg z hz
        _ = J1.card := by simp
    omega
  change 8 * (Fintype.card V - 1) ≤ 11 * V3.card
  omega

#print axioms c4_free_sum_choose_two_le
#print axioms c4_free_four_edges_le_four
#print axioms c4_free_five_edges_le_six
#print axioms c4_free_six_edges_le_seven
#print axioms c4_near_free_edges_le_four
#print axioms c4_near_free_edges_le_five
#print axioms class_h_no_all_high_cubic
#print axioms high_code_weight_sharp_ge_six
#print axioms high_code_weight_sharp_ge_eight
#print axioms high_code_weight_sharp_ge_ten
#print axioms class_h_v3_sharp_bound
#print axioms class_h_trifree_density_8_11

end E64Wave3ClassH
