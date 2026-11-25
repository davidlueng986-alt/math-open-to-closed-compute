import Core
import Incidence

/-!
# Wave 3 Agent #2 — Module 1: Sharp Class H F2 Weight-Enumerator & 8/11 Density Bound

Proves:
1. Elementary Turán/Reiman bounds for C4-free graphs:
   - `c4_free_sum_choose_two_le`: ∑ d(u)(d(u)-1) ≤ n(n-1)
   - `c4_free_four_edges_le_four`: ex(4, C4) ≤ 4
   - `c4_free_five_edges_le_six`: ex(5, C4) ≤ 6
   - `c4_free_six_edges_le_seven`: ex(6, C4) ≤ 7
2. Extremal edge bounds for C4-free, Near-free graphs:
   - `c4_near_free_edges_le_four`: |E(H)| ≤ 2|W| - 4 for |W| ≥ 4
   - `c4_near_free_edges_le_five`: |E(H)| ≤ 2|W| - 5 for |W| ≥ 6
3. Sharp Class H F2 code-weight hierarchy (strictly upgrading Wave 2's d_min ≥ 4):
   - `high_code_weight_sharp_ge_six`: wt(M 1_S) ≥ 6 + ∑_{x∈S} (d(x)-4) for |S| ≥ 2
   - `high_code_weight_sharp_ge_eight`: wt(M 1_S) ≥ 8 + ∑_{x∈S} (d(x)-4) for |S| ≥ 4
   - `high_code_weight_sharp_ge_ten`: wt(M 1_S) ≥ 10 + ∑_{x∈S} (d(x)-4) for |S| ≥ 6
   - `class_h_v3_sharp_bound`: |V_3| ≥ 2|V_{≥4}| + 5 + ∑_{x∈V_{≥4}} (d(x)-4) for |V_{≥4}| ≥ 6
4. First Lean 4.36.0 kernel verification of the sharp 8/11 density bound on H-N-*:
   - `class_h_trifree_density_8_11`: 11 * |V_3| ≥ 8 * (|V| - 1)
-/

namespace E64Wave3ClassH
open SimpleGraph Erdos64Closure E64Core Erdos64Incidence
open scoped BigOperators
universe u

/-- A graph is C4-free iff any two distinct vertices share at most one common neighbor. -/
def NoC4 {W : Type u} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj] : Prop :=
  ∀ u v : W, u ≠ v → (H.neighborFinset u ∩ H.neighborFinset v).card ≤ 1

/-- A graph has no Near induced subgraph. -/
def NoNearSubgraph {W : Type u} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj] : Prop :=
  ∀ (S : Set W) [Fintype S] [DecidableRel (H.induce S).Adj], ¬Near (H.induce S)

/-- Reiman's cherry-counting inequality for C4-free graphs:
    ∑ u, d(u) * (d(u) - 1) ≤ |W| * (|W| - 1). -/
theorem c4_free_sum_choose_two_le {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (hc4 : NoC4 H) :
    ∑ u : W, H.degree u * (H.degree u - 1) ≤ Fintype.card W * (Fintype.card W - 1) := by
  classical
  have h1 : ∀ u : W, H.degree u * (H.degree u - 1) =
      (Finset.univ.filter fun p : W × W => p.1 ≠ p.2 ∧ H.Adj u p.1 ∧ H.Adj u p.2).card := by
    intro u
    have hset : (Finset.univ.filter fun p : W × W => p.1 ≠ p.2 ∧ H.Adj u p.1 ∧ H.Adj u p.2) =
        (H.neighborFinset u).offDiag := by
      ext ⟨a, b⟩
      simp [Finset.mem_offDiag, and_comm, and_left_comm]
    rw [hset, Finset.card_offDiag, SimpleGraph.card_neighborFinset_eq_degree]
    cases hd : H.degree u with
    | zero => simp
    | succ k =>
      simp only [Nat.add_sub_cancel]
      ring_nf
      omega
  simp_rw [h1]
  have hswap : (∑ u : W, (Finset.univ.filter fun p : W × W => p.1 ≠ p.2 ∧ H.Adj u p.1 ∧ H.Adj u p.2).card) =
      ∑ p ∈ (Finset.univ : Finset W).offDiag, (H.neighborFinset p.1 ∩ H.neighborFinset p.2).card := by
    simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    rw [← Finset.sum_filter]
    have hoff : (Finset.univ.filter fun p : W × W => p.1 ≠ p.2) = (Finset.univ : Finset W).offDiag := by
      ext ⟨a, b⟩
      simp [Finset.mem_offDiag]
    rw [← hoff]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hne : p.1 ≠ p.2
    · simp only [hne, true_and, if_true]
      rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
      have hcap : (Finset.univ.filter fun u : W => H.Adj u p.1 ∧ H.Adj u p.2) =
          H.neighborFinset p.1 ∩ H.neighborFinset p.2 := by
        ext u
        simp [SimpleGraph.mem_neighborFinset, SimpleGraph.adj_comm]
      rw [hcap]
      simp
    · simp [hne]
  rw [hswap]
  calc
    ∑ p ∈ (Finset.univ : Finset W).offDiag, (H.neighborFinset p.1 ∩ H.neighborFinset p.2).card
        ≤ ∑ _p ∈ (Finset.univ : Finset W).offDiag, 1 := by
          apply Finset.sum_le_sum
          intro p hp
          exact hc4 p.1 p.2 (Finset.mem_offDiag.mp hp).2.2
    _ = ((Finset.univ : Finset W).offDiag).card := by simp
    _ = Fintype.card W * (Fintype.card W - 1) := by
          rw [Finset.card_offDiag, Finset.card_univ]
          cases hc : Fintype.card W with
          | zero => simp
          | succ k =>
            simp only [Nat.add_sub_cancel]
            ring_nf
            omega

/-- Elementary integer convexity: d*(d-1) + 6 ≥ 4*d for all d : ℕ. -/
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
        simp only [Nat.add_sub_cancel]
        nlinarith

/-- ex(4, C4) ≤ 4. -/
theorem c4_free_four_edges_le_four {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (hc4 : NoC4 H) (hcard : Fintype.card W = 4) :
    H.edgeFinset.card ≤ 4 := by
  have hreim := c4_free_sum_choose_two_le H hc4
  rw [hcard] at hreim
  have hsum : ∑ u : W, 4 * H.degree u ≤ ∑ u : W, (H.degree u * (H.degree u - 1) + 6) :=
    Finset.sum_le_sum fun u _ => quad_linear_bound (H.degree u)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hcard] at hsum
  have hhand := H.sum_degrees_eq_twice_card_edges
  simp only [smul_eq_mul] at hsum
  omega

/-- ex(5, C4) ≤ 6. -/
theorem c4_free_five_edges_le_six {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (hc4 : NoC4 H) (hcard : Fintype.card W = 5) :
    H.edgeFinset.card ≤ 6 := by
  have hreim := c4_free_sum_choose_two_le H hc4
  rw [hcard] at hreim
  have hsum : ∑ u : W, 4 * H.degree u ≤ ∑ u : W, (H.degree u * (H.degree u - 1) + 6) :=
    Finset.sum_le_sum fun u _ => quad_linear_bound (H.degree u)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hcard] at hsum
  have hhand := H.sum_degrees_eq_twice_card_edges
  simp only [smul_eq_mul] at hsum
  omega

/-- Deleting a vertex v reduces edge count by exactly H.degree v. -/
private lemma card_edges_delete_vertex {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (v : W)
    [DecidableRel (H.induce {x : W | x ≠ v}).Adj] :
    (H.induce {x : W | x ≠ v}).edgeFinset.card + H.degree v = H.edgeFinset.card := by
  classical
  have hsum1 := (H.induce {x : W | x ≠ v}).sum_degrees_eq_twice_card_edges
  have hsum2 := H.sum_degrees_eq_twice_card_edges
  have hdel : ∀ u : {x : W // x ≠ v},
      (H.induce {x : W | x ≠ v}).degree u + (if H.Adj u.1 v then 1 else 0) = H.degree u.1 :=
    fun u => induce_delete_degree H v u
  have htot : (∑ u : {x : W // x ≠ v}, (H.induce {x : W | x ≠ v}).degree u) +
      (∑ u : {x : W // x ≠ v}, if H.Adj u.1 v then 1 else 0) =
      ∑ u : {x : W // x ≠ v}, H.degree u.1 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => hdel u
  have hdegv : (∑ u : {x : W // x ≠ v}, if H.Adj u.1 v then 1 else 0) = H.degree v := by
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
    have e : {u : {x : W // x ≠ v} // H.Adj u.1 v} ≃ {x : W // H.Adj v x} :=
      { toFun := fun u => ⟨u.1.1, u.2.symm⟩
        invFun := fun x => ⟨⟨x.1, (H.ne_of_adj x.2).symm⟩, x.2.symm⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hc := Fintype.card_congr e
    rw [Fintype.card_subtype, SimpleGraph.card_neighborSet_eq_degree] at hc
    exact hc
  have hsplit : (∑ u : {x : W // x ≠ v}, H.degree u.1) + H.degree v = ∑ x : W, H.degree x := by
    have h1 : (∑ u : {x : W // x ≠ v}, H.degree u.1) = ∑ x ∈ Finset.univ.erase v, H.degree x := by
      rw [← Finset.sum_subtype (Finset.univ.erase v) (by intro x; simp)]
      rfl
    rw [h1, Finset.sum_erase_add _ _ (Finset.mem_univ v)]
  omega

/-- Induced subgraph of a C4-free graph is C4-free. -/
private lemma noC4_induce {W : Type u} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (hc4 : NoC4 H) (S : Set W) [Fintype S] [DecidableRel (H.induce S).Adj] :
    NoC4 (H.induce S) := by
  classical
  intro a b hab
  have hne : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
  have hle : ((H.induce S).neighborFinset a ∩ (H.induce S).neighborFinset b).card ≤
      (H.neighborFinset a.1 ∩ H.neighborFinset b.1).card := by
    apply Finset.card_le_card_of_injOn (fun x : S => x.1)
    · intro x hx
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hx ⊢
      exact hx
    · intro x _ y _ hxy
      exact Subtype.ext hxy
  exact hle.trans (hc4 a.1 b.1 hne)

/-- Any C4-free graph on 5 vertices with 6 edges has a vertex of degree 4. -/
private lemma c4_free_five_six_has_deg_four {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (hc4 : NoC4 H)
    (hcard : Fintype.card W = 5) (he : H.edgeFinset.card = 6) :
    ∃ u0 : W, H.degree u0 = 4 := by
  classical
  by_contra hno4
  have hle3 : ∀ u : W, H.degree u ≤ 3 := by
    intro u
    have hlt := H.degree_lt_card_verts u
    have hne4 : H.degree u ≠ 4 := fun h => hno4 ⟨u, h⟩
    omega
  have hsum := H.sum_degrees_eq_twice_card_edges
  rw [he] at hsum
  -- At least two vertices have degree 3 (otherwise ∑ d ≤ 3 + 4*2 = 11 < 12).
  have hdeg3_card : 2 ≤ (Finset.univ.filter fun u : W => H.degree u = 3).card := by
    by_contra hlt2
    have hle1 : (Finset.univ.filter fun u : W => H.degree u = 3).card ≤ 1 := by omega
    have hbound : ∑ u : W, H.degree u ≤
        ∑ u : W, (if H.degree u = 3 then 3 else 2) := by
      apply Finset.sum_le_sum
      intro u _
      have hu := hle3 u
      split_ifs with h
      · omega
      · omega
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
  -- Check whether a and b are adjacent.
  by_cases hadj : H.Adj a b
  · -- N(a) \ {b} and N(b) \ {a} are two size-2 subsets of the 3 vertices V \ {a, b}.
    let R : Finset W := (Finset.univ.erase a).erase b
    have hRcard : R.card = 3 := by
      have hbmem : b ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩
      rw [Finset.card_erase_of_mem hbmem, Finset.card_erase_of_mem (Finset.mem_univ a),
        Finset.card_univ, hcard]
    let Na := (H.neighborFinset a).erase b
    let Nb := (H.neighborFinset b).erase a
    have hNacard : Na.card = 2 := by
      rw [Finset.card_erase_of_mem ((H.mem_neighborFinset a b).mpr hadj),
        SimpleGraph.card_neighborFinset_eq_degree, ha]
    have hNbcard : Nb.card = 2 := by
      rw [Finset.card_erase_of_mem ((H.mem_neighborFinset b a).mpr hadj.symm),
        SimpleGraph.card_neighborFinset_eq_degree, hb]
    have hNaR : Na ⊆ R := by
      intro x hx
      simp only [Na, R, Finset.mem_erase, SimpleGraph.mem_neighborFinset, Finset.mem_univ, and_true] at hx ⊢
      exact ⟨hx.1, (H.ne_of_adj hx.2).symm⟩
    have hNbR : Nb ⊆ R := by
      intro x hx
      simp only [Nb, R, Finset.mem_erase, SimpleGraph.mem_neighborFinset, Finset.mem_univ, and_true] at hx ⊢
      exact ⟨(H.ne_of_adj hx.2).symm, hx.1⟩
    have hcap_le : (Na ∩ Nb).card ≤ 1 := by
      have hsub : Na ∩ Nb ⊆ H.neighborFinset a ∩ H.neighborFinset b := by
        intro x hx
        simp only [Na, Nb, Finset.mem_inter, Finset.mem_erase] at hx ⊢
        exact ⟨hx.1.2, hx.2.2⟩
      exact (Finset.card_le_card hsub).trans (hc4 a b hab)
    have hunion_le : (Na ∪ Nb).card ≤ 3 :=
      (Finset.card_le_card (Finset.union_subset hNaR hNbR)).trans hRcard.le
    have hinc := Finset.card_union_add_card_inter Na Nb
    have hcap_eq : (Na ∩ Nb).card = 1 := by omega
    obtain ⟨c1, hc1⟩ := Finset.card_eq_one.mp hcap_eq
    have hc1_mem : c1 ∈ Na ∩ Nb := by rw [hc1]; exact Finset.mem_singleton_self c1
    have hc1_a : H.Adj a c1 := (H.mem_neighborFinset a c1).mp (Finset.mem_erase.mp (Finset.mem_inter.mp hc1_mem).1).2
    have hc1_b : H.Adj b c1 := (H.mem_neighborFinset b c1).mp (Finset.mem_erase.mp (Finset.mem_inter.mp hc1_mem).2).2
    have hNa_rem : (Na.erase c1).card = 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_inter.mp hc1_mem).1, hNacard]
    obtain ⟨c2, hc2⟩ := Finset.card_eq_one.mp hNa_rem
    have hc2_mem : c2 ∈ Na.erase c1 := by rw [hc2]; exact Finset.mem_singleton_self c2
    have hc2_ne_c1 : c2 ≠ c1 := (Finset.mem_erase.mp hc2_mem).1
    have hc2_a : H.Adj a c2 := (H.mem_neighborFinset a c2).mp (Finset.mem_erase.mp (Finset.mem_erase.mp hc2_mem).2).2
    have hc2_not_b : ¬H.Adj b c2 := by
      intro hbc2
      have hmem : c2 ∈ Na ∩ Nb := Finset.mem_inter.mpr ⟨(Finset.mem_erase.mp hc2_mem).2,
        Finset.mem_erase.mpr ⟨(H.ne_of_adj hc2_a).symm, (H.mem_neighborFinset b c2).mpr hbc2⟩⟩
      rw [hc1, Finset.mem_singleton] at hmem
      exact hc2_ne_c1 hmem
    have hNb_rem : (Nb.erase c1).card = 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_inter.mp hc1_mem).2, hNbcard]
    obtain ⟨c3, hc3⟩ := Finset.card_eq_one.mp hNb_rem
    have hc3_mem : c3 ∈ Nb.erase c1 := by rw [hc3]; exact Finset.mem_singleton_self c3
    have hc3_ne_c1 : c3 ≠ c1 := (Finset.mem_erase.mp hc3_mem).1
    have hc3_b : H.Adj b c3 := (H.mem_neighborFinset b c3).mp (Finset.mem_erase.mp (Finset.mem_erase.mp hc3_mem).2).2
    have hc3_not_a : ¬H.Adj a c3 := by
      intro hac3
      have hmem : c3 ∈ Na ∩ Nb := Finset.mem_inter.mpr ⟨
        Finset.mem_erase.mpr ⟨(H.ne_of_adj hc3_b).symm, (H.mem_neighborFinset a c3).mpr hac3⟩,
        (Finset.mem_erase.mp hc3_mem).2⟩
      rw [hc1, Finset.mem_singleton] at hmem
      exact hc3_ne_c1 hmem
    have hc2_ne_c3 : c2 ≠ c3 := fun h => hc3_not_a (h ▸ hc2_a)
    -- None of c1-c2, c1-c3, c2-c3 can be an edge (each creates a C4!).
    have h12 : ¬H.Adj c1 c2 := by
      intro h
      have hsub : ({b, c2} : Finset W) ⊆ H.neighborFinset a ∩ H.neighborFinset c1 := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨(H.mem_neighborFinset a b).mpr hadj, (H.mem_neighborFinset c1 b).mpr hc1_b.symm⟩
        · exact Finset.mem_inter.mpr ⟨(H.mem_neighborFinset a c2).mpr hc2_a, (H.mem_neighborFinset c1 c2).mpr h⟩
      have hb_ne_c2 : b ≠ c2 := (Finset.mem_erase.mp (Finset.mem_erase.mp hc2_mem).2).1.symm
      have hc := (Finset.card_le_card hsub).trans (hc4 a c1 (H.ne_of_adj hc1_a))
      rw [Finset.card_pair hb_ne_c2] at hc
      omega
    have h13 : ¬H.Adj c1 c3 := by
      intro h
      have hsub : ({a, c3} : Finset W) ⊆ H.neighborFinset b ∩ H.neighborFinset c1 := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨(H.mem_neighborFinset b a).mpr hadj.symm, (H.mem_neighborFinset c1 a).mpr hc1_a.symm⟩
        · exact Finset.mem_inter.mpr ⟨(H.mem_neighborFinset b c3).mpr hc3_b, (H.mem_neighborFinset c1 c3).mpr h⟩
      have ha_ne_c3 : a ≠ c3 := (Finset.mem_erase.mp (Finset.mem_erase.mp hc3_mem).2).1.symm
      have hc := (Finset.card_le_card hsub).trans (hc4 b c1 (H.ne_of_adj hc1_b))
      rw [Finset.card_pair ha_ne_c3] at hc
      omega
    have h23 : ¬H.Adj c2 c3 := by
      intro h
      have hsub : ({b, c2} : Finset W) ⊆ H.neighborFinset a ∩ H.neighborFinset c3 := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨(H.mem_neighborFinset a b).mpr hadj, (H.mem_neighborFinset c3 b).mpr hc3_b.symm⟩
        · exact Finset.mem_inter.mpr ⟨(H.mem_neighborFinset a c2).mpr hc2_a, (H.mem_neighborFinset c3 c2).mpr h.symm⟩
      have hb_ne_c2 : b ≠ c2 := (Finset.mem_erase.mp (Finset.mem_erase.mp hc2_mem).2).1.symm
      have hc := (Finset.card_le_card hsub).trans (hc4 a c3 (fun heq => hc3_not_a (heq ▸ H.loopless a |> False.elim)))
      rw [Finset.card_pair hb_ne_c2] at hc
      omega
    -- Now c1, c2, c3 have degrees ≤ 2, 1, 1 respectively!
    have hR_eq : R = {c1, c2, c3} := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        have hmem_c1 : c1 ∈ R := hNaR (Finset.mem_inter.mp hc1_mem).1
        have hmem_c2 : c2 ∈ R := hNaR (Finset.mem_erase.mp hc2_mem).2
        have hmem_c3 : c3 ∈ R := hNbR (Finset.mem_erase.mp hc3_mem).2
        have hsub3 : ({c1, c2, c3} : Finset W) ⊆ R := by
          intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl | rfl <;> assumption
        have hcard3 : ({c1, c2, c3} : Finset W).card = 3 := by
          rw [Finset.card_insert_of_notMem, Finset.card_pair hc2_ne_c3]
          simp [hc2_ne_c1.symm, hc3_ne_c1.symm]
        have heq := Finset.eq_of_subset_of_card_le hsub3 (by omega)
        rw [heq] at hx
        exact hx
      · rw [hRcard]
        rw [Finset.card_insert_of_notMem, Finset.card_pair hc2_ne_c3]
        simp [hc2_ne_c1.symm, hc3_ne_c1.symm]
    have hall_v : ∀ x : W, x = a ∨ x = b ∨ x = c1 ∨ x = c2 ∨ x = c3 := by
      intro x
      by_cases hxa : x = a
      · exact Or.inl hxa
      by_cases hxb : x = b
      · exact Or.inr (Or.inl hxb)
      have hxR : x ∈ R := Finset.mem_erase.mpr ⟨hxb, Finset.mem_erase.mpr ⟨hxa, Finset.mem_univ x⟩⟩
      rw [hR_eq] at hxR
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxR
      rcases hxR with rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    have hdc1 : H.degree c1 ≤ 2 := by
      have hsub : H.neighborFinset c1 ⊆ {a, b} := by
        intro x hx
        have hax := (H.mem_neighborFinset c1 x).mp hx
        rcases hall_v x with rfl | rfl | rfl | rfl | rfl
        · simp
        · simp
        · exact False.elim (H.loopless c1 hax)
        · exact False.elim (h12 hax)
        · exact False.elim (h13 hax)
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      exact (Finset.card_le_card hsub).trans (Finset.card_le_two)
    have hdc2 : H.degree c2 ≤ 1 := by
      have hsub : H.neighborFinset c2 ⊆ {a} := by
        intro x hx
        have hax := (H.mem_neighborFinset c2 x).mp hx
        rcases hall_v x with rfl | rfl | rfl | rfl | rfl
        · simp
        · exact False.elim (hc2_not_b hax.symm)
        · exact False.elim (h12 hax.symm)
        · exact False.elim (H.loopless c2 hax)
        · exact False.elim (h23 hax)
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      exact (Finset.card_le_card hsub).trans (by simp)
    have hdc3 : H.degree c3 ≤ 1 := by
      have hsub : H.neighborFinset c3 ⊆ {b} := by
        intro x hx
        have hax := (H.mem_neighborFinset c3 x).mp hx
        rcases hall_v x with rfl | rfl | rfl | rfl | rfl
        · exact False.elim (hc3_not_a hax.symm)
        · simp
        · exact False.elim (h13 hax.symm)
        · exact False.elim (h23 hax.symm)
        · exact False.elim (H.loopless c3 hax)
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      exact (Finset.card_le_card hsub).trans (by simp)
    have huniv : (Finset.univ : Finset W) = {a, b, c1, c2, c3} := by
      ext x
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      exact hall_v x
    have ha_not : a ∉ ({b, c1, c2, c3} : Finset W) := by
      simp [hab, H.ne_of_adj hc1_a, H.ne_of_adj hc2_a, (Finset.mem_erase.mp (Finset.mem_erase.mp hc3_mem).2).1.symm]
    have hb_not : b ∉ ({c1, c2, c3} : Finset W) := by
      simp [H.ne_of_adj hc1_b, (Finset.mem_erase.mp (Finset.mem_erase.mp hc2_mem).2).1.symm, H.ne_of_adj hc3_b]
    have hc1_not : c1 ∉ ({c2, c3} : Finset W) := by
      simp [hc2_ne_c1.symm, hc3_ne_c1.symm]
    rw [huniv, Finset.sum_insert ha_not, Finset.sum_insert hb_not, Finset.sum_insert hc1_not,
      Finset.sum_pair hc2_ne_c3] at hsum
    omega
  · -- a and b are NOT adjacent: both N(a) and N(b) are size-3 subsets of the 3-element set V \ {a, b}!
    let R : Finset W := (Finset.univ.erase a).erase b
    have hRcard : R.card = 3 := by
      have hbmem : b ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩
      rw [Finset.card_erase_of_mem hbmem, Finset.card_erase_of_mem (Finset.mem_univ a),
        Finset.card_univ, hcard]
    have hNaR : H.neighborFinset a ⊆ R := by
      intro x hx
      have hax := (H.mem_neighborFinset a x).mp hx
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨(H.ne_of_adj hax).symm, Finset.mem_univ x⟩⟩
      intro hxb; subst hxb; exact hadj hax
    have hNbR : H.neighborFinset b ⊆ R := by
      intro x hx
      have hbx := (H.mem_neighborFinset b x).mp hx
      refine Finset.mem_erase.mpr ⟨(H.ne_of_adj hbx).symm, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ x⟩⟩
      intro hxa; subst hxa; exact hadj hbx.symm
    have hNa_eq : H.neighborFinset a = R :=
      Finset.eq_of_subset_of_card_le hNaR (by rw [SimpleGraph.card_neighborFinset_eq_degree, ha, hRcard])
    have hNb_eq : H.neighborFinset b = R :=
      Finset.eq_of_subset_of_card_le hNbR (by rw [SimpleGraph.card_neighborFinset_eq_degree, hb, hRcard])
    have hc := hc4 a b hab
    rw [hNa_eq, hNb_eq, Finset.inter_self, hRcard] at hc
    omega

/-- ex(6, C4) ≤ 7 (pure elementary proof via bowtie universality at n = 5). -/
theorem c4_free_six_edges_le_seven {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (hc4 : NoC4 H) (hcard : Fintype.card W = 6) :
    H.edgeFinset.card ≤ 7 := by
  classical
  by_contra hgt
  have he8 : 8 ≤ H.edgeFinset.card := by omega
  -- First, Reiman gives |E| ≤ 8.
  have hreim := c4_free_sum_choose_two_le H hc4
  rw [hcard] at hreim
  have hsum_lin : ∑ u : W, 4 * H.degree u ≤ ∑ u : W, (H.degree u * (H.degree u - 1) + 6) :=
    Finset.sum_le_sum fun u _ => quad_linear_bound (H.degree u)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hcard] at hsum_lin
  have hhand := H.sum_degrees_eq_twice_card_edges
  simp only [smul_eq_mul] at hsum_lin
  have he_eq : H.edgeFinset.card = 8 := by omega
  -- Since ∑ d(u) = 16 < 18 = 6*3, there is a vertex v with d(v) ≤ 2.
  have hex_le2 : ∃ v : W, H.degree v ≤ 2 := by
    by_contra hall3
    have hge3 : ∀ v : W, 3 ≤ H.degree v := fun v => by
      by_contra hlt; exact hall3 ⟨v, by omega⟩
    have hge18 : 18 ≤ ∑ v : W, H.degree v := by
      calc 18 = ∑ _v : W, 3 := by rw [Finset.sum_const, Finset.card_univ, hcard]; decide
        _ ≤ ∑ v : W, H.degree v := Finset.sum_le_sum fun v _ => hge3 v
    omega
  obtain ⟨v, hv⟩ := hex_le2
  let W' := {x : W // x ≠ v}
  let H' := H.induce {x : W | x ≠ v}
  let _ : DecidableRel H'.Adj := inferInstanceAs (DecidableRel (H.induce {x : W | x ≠ v}).Adj)
  have hW'card : Fintype.card W' = 5 := by
    rw [Fintype.card_subtype, show (Finset.univ.filter fun x : W => x ≠ v) = Finset.univ.erase v by ext x; simp,
      Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, hcard]
  have hH'c4 : NoC4 H' := noC4_induce H hc4 {x : W | x ≠ v}
  have hH'edges_le : H'.edgeFinset.card ≤ 6 := c4_free_five_edges_le_six H' hH'c4 hW'card
  have hdel := card_edges_delete_vertex H v
  have hv_eq : H.degree v = 2 := by omega
  have hH'edges : H'.edgeFinset.card = 6 := by omega
  -- H' on 5 vertices with 6 edges has a vertex u0 of degree 4 (the bowtie center).
  obtain ⟨u0, hu0⟩ := c4_free_five_six_has_deg_four H' hH'c4 hW'card hH'edges
  -- u0 is adjacent to EVERY other vertex of W'!
  have hu0_univ : ∀ z : W', z ≠ u0 → H'.Adj u0 z := by
    intro z hz
    have hsub : H'.neighborFinset u0 ⊆ Finset.univ.erase u0 := by
      intro x hx
      exact Finset.mem_erase.mpr ⟨(H'.ne_of_adj ((H'.mem_neighborFinset u0 x).mp hx)).symm, Finset.mem_univ x⟩
    have heq : H'.neighborFinset u0 = Finset.univ.erase u0 :=
      Finset.eq_of_subset_of_card_le hsub (by
        rw [Finset.card_erase_of_mem (Finset.mem_univ u0), Finset.card_univ, hW'card,
          SimpleGraph.card_neighborFinset_eq_degree, hu0])
    exact (H'.mem_neighborFinset u0 z).mp (heq ▸ Finset.mem_erase.mpr ⟨hz, Finset.mem_univ z⟩)
  -- Since H.degree v = 2, v has two distinct neighbors x, y in W'.
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by
    rw [SimpleGraph.card_neighborFinset_eq_degree, hv_eq]; omega)
  have hvx : H.Adj v x := (H.mem_neighborFinset v x).mp hx
  have hvy : H.Adj v y := (H.mem_neighborFinset v y).mp hy
  let x' : W' := ⟨x, (H.ne_of_adj hvx).symm⟩
  let y' : W' := ⟨y, (H.ne_of_adj hvy).symm⟩
  have hxy' : x' ≠ y' := fun h => hxy (congrArg Subtype.val h)
  -- Since v is a common neighbor of x and y in H, x' and y' have NO common neighbor in H'!
  have hno_cn : ∀ z' : W', ¬(H'.Adj x' z' ∧ H'.Adj y' z') := by
    intro z' ⟨hxz, hyz⟩
    have hsub : ({v, z'.1} : Finset W) ⊆ H.neighborFinset x ∩ H.neighborFinset y := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨(H.mem_neighborFinset x v).mpr hvx.symm, (H.mem_neighborFinset y v).mpr hvy.symm⟩
      · exact Finset.mem_inter.mpr ⟨(H.mem_neighborFinset x z'.1).mpr hxz, (H.mem_neighborFinset y z'.1).mpr hyz⟩
    have hc := (Finset.card_le_card hsub).trans (hc4 x y hxy)
    rw [Finset.card_pair z'.2.symm] at hc
    omega
  -- Case 1: u0 ∉ {x', y'} -> u0 is a common neighbor of x' and y' in H'!
  by_cases hx0 : x' = u0
  · subst hx0
    -- Case 2: x' = u0. Since ∑ d'(u) = 12 and d'(u0) = 4, every other vertex has d' = 2!
    -- Wait: even simpler, if d'(y') ≥ 2 then y' has a neighbor z' ≠ u0, and z' is adj to u0!
    have hdy' : 2 ≤ H'.degree y' := by
      -- Every vertex in H' has d'(u) ≤ 2 (except u0) because if some z ≠ u0 had d'(z) ≥ 3,
      -- then z and u0 would share ≥ 2 neighbors (contradicting NoC4)!
      have hall_le2 : ∀ z : W', z ≠ u0 → H'.degree z ≤ 2 := by
        intro z hz
        by_contra hge3
        have hgt2 : 2 < H'.degree z := by omega
        have hcard_er : ((H'.neighborFinset z).erase u0).card ≥ 2 := by
          rw [Finset.card_erase_of_mem ((H'.mem_neighborFinset z u0).mpr (hu0_univ z hz).symm),
            SimpleGraph.card_neighborFinset_eq_degree]
          omega
        have hsub : (H'.neighborFinset z).erase u0 ⊆ H'.neighborFinset z ∩ H'.neighborFinset u0 := by
          intro t ht
          have htu : t ≠ u0 := (Finset.mem_erase.mp ht).1
          exact Finset.mem_inter.mpr ⟨(Finset.mem_erase.mp ht).2, (H'.mem_neighborFinset u0 t).mpr (hu0_univ t htu)⟩
        have hc := (Finset.card_le_card hsub).trans (hH'c4 z u0 hz)
        omega
      have hsum' := H'.sum_degrees_eq_twice_card_edges
      rw [hH'edges] at hsum'
      have hsplit : ∑ z ∈ Finset.univ.erase u0, H'.degree z = 8 := by
        have hadd := Finset.sum_erase_add (Finset.univ : Finset W') (fun z => H'.degree z) (Finset.mem_univ u0)
        omega
      have hsplit2 := Finset.sum_erase_add (Finset.univ.erase u0) (fun z => H'.degree z)
        (Finset.mem_erase.mpr ⟨hxy'.symm, Finset.mem_univ y'⟩)
      have hrem_le : ∑ z ∈ (Finset.univ.erase u0).erase y', H'.degree z ≤ 6 := by
        calc ∑ z ∈ (Finset.univ.erase u0).erase y', H'.degree z
            ≤ ∑ _z ∈ (Finset.univ.erase u0).erase y', 2 :=
              Finset.sum_le_sum fun z hz => hall_le2 z (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).1
          _ = ((Finset.univ.erase u0).erase y').card * 2 := by rw [Finset.sum_const, smul_eq_mul]
          _ = 6 := by
              rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hxy'.symm, Finset.mem_univ y'⟩),
                Finset.card_erase_of_mem (Finset.mem_univ u0), Finset.card_univ, hW'card]
      omega
    have hpos : 0 < ((H'.neighborFinset y').erase u0).card := by
      rw [Finset.card_erase_of_mem ((H'.mem_neighborFinset y' u0).mpr (hu0_univ y' hxy'.symm).symm),
        SimpleGraph.card_neighborFinset_eq_degree]
      omega
    obtain ⟨z', hz'⟩ := Finset.card_pos.mp hpos
    have hzu0 : z' ≠ u0 := (Finset.mem_erase.mp hz').1
    have hyz : H'.Adj y' z' := (H'.mem_neighborFinset y' z').mp (Finset.mem_erase.mp hz').2
    exact hno_cn z' ⟨hu0_univ z' hzu0, hyz⟩
  · by_cases hy0 : y' = u0
    · subst hy0
      have hall_le2 : ∀ z : W', z ≠ u0 → H'.degree z ≤ 2 := by
        intro z hz
        by_contra hge3
        have hcard_er : ((H'.neighborFinset z).erase u0).card ≥ 2 := by
          rw [Finset.card_erase_of_mem ((H'.mem_neighborFinset z u0).mpr (hu0_univ z hz).symm),
            SimpleGraph.card_neighborFinset_eq_degree]
          omega
        have hsub : (H'.neighborFinset z).erase u0 ⊆ H'.neighborFinset z ∩ H'.neighborFinset u0 := by
          intro t ht
          have htu : t ≠ u0 := (Finset.mem_erase.mp ht).1
          exact Finset.mem_inter.mpr ⟨(Finset.mem_erase.mp ht).2, (H'.mem_neighborFinset u0 t).mpr (hu0_univ t htu)⟩
        have hc := (Finset.card_le_card hsub).trans (hH'c4 z u0 hz)
        omega
      have hsum' := H'.sum_degrees_eq_twice_card_edges
      rw [hH'edges] at hsum'
      have hsplit : ∑ z ∈ Finset.univ.erase u0, H'.degree z = 8 := by
        have hadd := Finset.sum_erase_add (Finset.univ : Finset W') (fun z => H'.degree z) (Finset.mem_univ u0)
        omega
      have hsplit2 := Finset.sum_erase_add (Finset.univ.erase u0) (fun z => H'.degree z)
        (Finset.mem_erase.mpr ⟨hx0, Finset.mem_univ x'⟩)
      have hrem_le : ∑ z ∈ (Finset.univ.erase u0).erase x', H'.degree z ≤ 6 := by
        calc ∑ z ∈ (Finset.univ.erase u0).erase x', H'.degree z
            ≤ ∑ _z ∈ (Finset.univ.erase u0).erase x', 2 :=
              Finset.sum_le_sum fun z hz => hall_le2 z (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).1
          _ = ((Finset.univ.erase u0).erase x').card * 2 := by rw [Finset.sum_const, smul_eq_mul]
          _ = 6 := by
              rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hx0, Finset.mem_univ x'⟩),
                Finset.card_erase_of_mem (Finset.mem_univ u0), Finset.card_univ, hW'card]
      have hdx' : 2 ≤ H'.degree x' := by omega
      have hpos : 0 < ((H'.neighborFinset x').erase u0).card := by
        rw [Finset.card_erase_of_mem ((H'.mem_neighborFinset x' u0).mpr (hu0_univ x' hx0).symm),
          SimpleGraph.card_neighborFinset_eq_degree]
        omega
      obtain ⟨z', hz'⟩ := Finset.card_pos.mp hpos
      have hzu0 : z' ≠ u0 := (Finset.mem_erase.mp hz').1
      have hxz : H'.Adj x' z' := (H'.mem_neighborFinset x' z').mp (Finset.mem_erase.mp hz').2
      exact hno_cn z' ⟨hxz, hu0_univ z' hzu0⟩
    · exact hno_cn u0 ⟨(hu0_univ x' hx0).symm, (hu0_univ y' hy0).symm⟩

/-- Every Near-free graph with ≥ 2 vertices has a vertex of degree ≤ 2. -/
private lemma exists_deg_le_two_of_noNear {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (hnn : NoNearSubgraph H)
    (hcard : 2 ≤ Fintype.card W) : ∃ v : W, H.degree v ≤ 2 := by
  classical
  by_contra hall
  have hge3 : ∀ v : W, 3 ≤ H.degree v := fun v => by
    by_contra hlt; exact hall ⟨v, by omega⟩
  have hne : Nonempty W := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨w⟩ := hne
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
  have hcard1 : 2 ≤ Fintype.card (Set.univ : Set W) := by
    simpa [Fintype.card_coe] using hcard
  have hnear : Near H1 := near_of_except H1 ⟨w, trivial⟩ hcard1 (fun u _ => by rw [hdeg_eq]; exact hge3 u.1)
  exact hnn Set.univ hnear

/-- Induced subgraph of a NoNearSubgraph graph is NoNearSubgraph. -/
private lemma noNear_induce {W : Type u} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (hnn : NoNearSubgraph H) (S : Set W) [Fintype S] [DecidableRel (H.induce S).Adj] :
    NoNearSubgraph (H.induce S) := by
  classical
  intro T _ _ hnear
  let T' : Set W := Subtype.val '' T
  let _ : DecidableRel (H.induce T').Adj := Classical.decRel _
  let e : T ≃ T' :=
    { toFun := fun x => ⟨x.1.1, ⟨x.1, x.2, rfl⟩⟩
      invFun := fun y => ⟨⟨y.1, by obtain ⟨a, _, ha⟩ := y.2; exact ha ▸ a.2⟩,
        by obtain ⟨a, haT, ha⟩ := y.2; have : (⟨y.1, _⟩ : S) = a := Subtype.ext ha.symm; exact this ▸ haT⟩
      left_inv := fun x => Subtype.ext (Subtype.ext rfl)
      right_inv := fun y => Subtype.ext rfl }
  have hiso : ((H.induce S).induce T) ≃g (H.induce T') :=
    { toEquiv := e, map_rel_iff' := Iff.rfl }
  have hnear' : Near (H.induce T') := by
    obtain ⟨⟨v, hv⟩, ⟨w, hw⟩⟩ := hnear
    refine ⟨⟨hiso v, ?_⟩, ⟨hiso w, ?_⟩⟩
    · rwa [hiso.degree_eq v]
    · intro u hu
      have hne : hiso.symm u ≠ w := fun h => hu (by rw [← h, hiso.apply_symm_apply])
      have hdeg := hw (hiso.symm u) hne
      have heq := hiso.degree_eq (hiso.symm u)
      rw [hiso.apply_symm_apply] at heq
      omega
  exact hnn T' hnear'

/-- General peeling induction: if base n0 satisfies |E| + c ≤ 2*n0, then all n ≥ n0 satisfy |E| + c ≤ 2*n. -/
private lemma peel_edges_bound (n0 c : ℕ) (hn0 : 2 ≤ n0)
    (hbase : ∀ (W : Type u) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
      NoC4 H → NoNearSubgraph H → Fintype.card W = n0 → H.edgeFinset.card + c ≤ 2 * n0) :
    ∀ (k : ℕ) (W : Type u) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
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
    let W' := {x : W // x ≠ v}
    let H' := H.induce {x : W | x ≠ v}
    let _ : DecidableRel H'.Adj := inferInstanceAs (DecidableRel (H.induce {x : W | x ≠ v}).Adj)
    have hW'card : Fintype.card W' = n0 + k := by
      rw [Fintype.card_subtype, show (Finset.univ.filter fun x : W => x ≠ v) = Finset.univ.erase v by ext x; simp,
        Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, hcard]
      omega
    have hih := ih W' H' (noC4_induce H hc4 _) (noNear_induce H hnn _) hW'card
    have hdel := card_edges_delete_vertex H v
    omega

/-- Every C4-free, Near-free simple graph on m ≥ 4 vertices has |E(H)| ≤ 2m - 4. -/
theorem c4_near_free_edges_le_four {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (hc4 : NoC4 H) (hnn : NoNearSubgraph H)
    (hcard : 4 ≤ Fintype.card W) : H.edgeFinset.card + 4 ≤ 2 * Fintype.card W := by
  have hk := peel_edges_bound 4 4 (by decide)
    (fun W _ _ H _ hc4 _ h4 => by have := c4_free_four_edges_le_four H hc4 h4; omega)
    (Fintype.card W - 4) W H hc4 hnn (by omega)
  omega

/-- Every C4-free, Near-free simple graph on m ≥ 6 vertices has |E(H)| ≤ 2m - 5. -/
theorem c4_near_free_edges_le_five {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (hc4 : NoC4 H) (hnn : NoNearSubgraph H)
    (hcard : 6 ≤ Fintype.card W) : H.edgeFinset.card + 5 ≤ 2 * Fintype.card W := by
  have hk := peel_edges_bound 6 5 (by decide)
    (fun W _ _ H _ hc4 _ h6 => by have := c4_free_six_edges_le_seven H hc4 h6; omega)
    (Fintype.card W - 6) W H hc4 hnn (by omega)
  omega

/-- MinimalBad graphs are C4-free. -/
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
  have hcyc : c.IsCycle := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp only [c, Walk.edges_cons, Walk.edges_nil, List.nodup_cons, List.mem_cons,
        List.not_mem_nil, or_false, List.nodup_nil, and_true, Sym2.eq_iff]
      refine ⟨?_, ?_, ?_⟩
      · rintro ((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)) <;>
          first | exact hau rfl | exact huv rfl | exact hab rfl | exact hbu rfl | exact hbv rfl | exact hav rfl
      · rintro ((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)) <;>
          first | exact hav rfl | exact hab rfl | exact huv rfl | exact hbu rfl | exact hbv rfl
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
          first | exact hbv rfl | exact huv rfl | exact hbu rfl
    · simp [c]
    · simp [c, hau, hav, hbu, hbv, huv, hab, hab.symm, huv.symm, hau.symm, hav.symm, hbu.symm, hbv.symm]
  exact hm.2.1 ⟨2, u, c, le_rfl, hcyc, rfl⟩

/-- No two vertices of degree ≥ 4 are adjacent in MinimalBad G. -/
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
    by_cases hvy : v = y
    · subst hvy; simp at hd; omega
    simp [hvx, hvy] at hd
    have := hw v hv; omega
  have heq := hm.2.2.2 H sdiff_le hnear
  have h1 : H.Adj x y := heq ▸ hxy
  exact ((SimpleGraph.sdiff_adj G (SimpleGraph.edge x y) x y).mp h1).2
    ((SimpleGraph.edge_adj x y x y).mpr ⟨Or.inl ⟨rfl, rfl⟩, G.ne_of_adj hxy⟩)

/-- Every neighbor of a vertex of degree ≥ 4 has degree exactly 3. -/
private lemma high_nb_cubic {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {x y : V} (hx : 4 ≤ G.degree x) (hxy : G.Adj x y) : G.degree y = 3 := by
  classical
  have hy2 := no_small_defect G hm y
  have hle3 : G.degree y ≤ 3 := by
    by_contra hgt
    exact high_indep G hm hx (by omega) hxy
  by_contra hne3
  have hy2eq : G.degree y = 2 := by omega
  obtain ⟨_, w, hw⟩ := hm.1
  have hwy : w = y := by
    by_contra hne
    have := hw y (Ne.symm hne)
    omega
  subst hwy
  let H := G \ SimpleGraph.edge x y
  let _ : DecidableRel H.Adj := inferInstanceAs (DecidableRel (G \ SimpleGraph.edge x y).Adj)
  have hcard : 2 ≤ Fintype.card V := by have := G.degree_lt_card_verts x; omega
  have hnear : Near H := by
    apply near_of_except H y hcard
    intro v hv
    have hd := erase_edge_degree G x y hxy v
    change H.degree v + (if v = x ∨ v = y then 1 else 0) = G.degree v at hd
    by_cases hvx : v = x
    · subst hvx; simp at hd; omega
    · simp [hvx, hv] at hd; have := hw v hv; omega
  have heq := hm.2.2.2 H sdiff_le hnear
  have h1 : H.Adj x y := heq ▸ hxy
  exact ((SimpleGraph.sdiff_adj G (SimpleGraph.edge x y) x y).mp h1).2
    ((SimpleGraph.edge_adj x y x y).mpr ⟨Or.inl ⟨rfl, rfl⟩, G.ne_of_adj hxy⟩)

/-- No degree-3 vertex has all 3 neighbors in V_{≥4} in MinimalBad G. -/
theorem class_h_no_all_high_cubic {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (y : V) (hy : G.degree y = 3) :
    (G.neighborFinset y |>.filter fun x => 4 ≤ G.degree x).card ≤ 2 := by
  classical
  by_contra hgt
  have hcard3 : (G.neighborFinset y |>.filter fun x => 4 ≤ G.degree x).card = 3 := by
    have hle := Finset.card_filter_le (G.neighborFinset y) (fun x => 4 ≤ G.degree x)
    rw [SimpleGraph.card_neighborFinset_eq_degree, hy] at hle
    omega
  have hall_high : ∀ x, G.Adj y x → 4 ≤ G.degree x := by
    intro x hxy
    have heq : (G.neighborFinset y).filter (fun z => 4 ≤ G.degree z) = G.neighborFinset y :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
        (by rw [SimpleGraph.card_neighborFinset_eq_degree, hy, hcard3])
    have hmem : x ∈ (G.neighborFinset y).filter (fun z => 4 ≤ G.degree z) := by
      rw [heq]; exact (G.mem_neighborFinset y x).mpr hxy
    exact (Finset.mem_filter.mp hmem).2
  obtain ⟨_, w, hw⟩ := hm.1
  let W := {z : V // z ≠ y}
  let H := G.induce {z : V | z ≠ y}
  let _ : DecidableRel H.Adj := inferInstanceAs (DecidableRel (G.induce {z : V | z ≠ y}).Adj)
  have hVcard : 4 ≤ Fintype.card V := by
    have := G.degree_lt_card_verts y; omega
  have hWcard : Fintype.card W + 1 = Fintype.card V := by
    rw [Fintype.card_subtype, show (Finset.univ.filter fun z : V => z ≠ y) = Finset.univ.erase y by ext z; simp]
    exact Finset.card_erase_add_one (Finset.mem_univ y)
  have hnear : Near H := by
    by_cases hwy : w = y
    · subst hwy
      have hne : Nonempty W := Fintype.card_pos_iff.mp (by omega)
      obtain ⟨u0⟩ := hne
      apply near_of_except H u0 (by omega)
      intro v _
      have hd := induce_delete_degree G w v
      change H.degree v + (if G.Adj v.1 w then 1 else 0) = G.degree v.1 at hd
      by_cases hadj : G.Adj v.1 w
      · have hh := hall_high v.1 hadj.symm; simp [hadj] at hd; omega
      · simp [hadj] at hd; have := hw v.1 v.2; omega
    · apply near_of_except H ⟨w, hwy⟩ (by omega)
      intro v hv
      have hd := induce_delete_degree G y v
      change H.degree v + (if G.Adj v.1 y then 1 else 0) = G.degree v.1 at hd
      by_cases hadj : G.Adj v.1 y
      · have hh := hall_high v.1 hadj.symm; simp [hadj] at hd; omega
      · simp [hadj] at hd; have := hw v.1 (fun h => hv (Subtype.ext h)); omega
  exact hm.2.1 (power_induce G _ (hm.2.2.1 W H (by omega) hnear))

/-- The midpoint shadow graph on a subset S ⊆ V_{≥4}: two distinct vertices in S are adjacent
    iff they share a common neighbor in V_3. -/
def shadowOnHigh {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : SimpleGraph S where
  Adj a b := a ≠ b ∧ ∃ y : V, G.degree y = 3 ∧ G.Adj a.1 y ∧ G.Adj b.1 y
  symm := fun _ _ ⟨hne, y, hy, ha, hb⟩ => ⟨hne.symm, y, hy, hb, ha⟩
  loopless := fun _ ⟨hne, _⟩ => hne rfl

/-- Lifting a simple walk in shadowOnHigh G S of length L to a simple walk in G of length 2L. -/
private lemma shadowOnHigh_hasPower_lifts {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (S : Finset V) (hS : ∀ x ∈ S, 4 ≤ G.degree x)
    (T : Set S) [Fintype T] [DecidableRel ((shadowOnHigh G S).induce T).Adj] :
    HasPower ((shadowOnHigh G S).induce T) → HasPower G := by
  classical
  rintro ⟨k, v0, c, hk, hc, hlen⟩
  have hc4 := minimal_bad_noC4 G hm
  -- Map c to shadowOnHigh G S
  let f : ((shadowOnHigh G S).induce T) →g shadowOnHigh G S := ⟨Subtype.val, fun h => h⟩
  let c' : (shadowOnHigh G S).Walk v0.1 v0.1 := c.map f
  have hc' : c'.IsCycle := (Walk.isCycle_map_iff_of_injective Subtype.val_injective).mpr hc
  have hlen' : c'.length = 2 ^ k := by simpa [c'] using hlen
  -- For each adjacent pair (a, b) in shadowOnHigh G S, pick its unique midpoint in V_3.
  have hmid_ex : ∀ (a b : S), (shadowOnHigh G S).Adj a b →
      ∃ y : V, G.degree y = 3 ∧ G.Adj a.1 y ∧ G.Adj b.1 y := fun _ _ h => h.2
  -- Define midpoint function on Sym2 S
  let mid : ∀ (a b : S), (shadowOnHigh G S).Adj a b → V :=
    fun a b h => Classical.choose (hmid_ex a b h)
  have hmid_spec : ∀ (a b : S) (h : (shadowOnHigh G S).Adj a b),
      G.degree (mid a b h) = 3 ∧ G.Adj a.1 (mid a b h) ∧ G.Adj b.1 (mid a b h) :=
    fun a b h => Classical.choose_spec (hmid_ex a b h)
  -- Uniqueness of midpoint: if y is adjacent to both a.1 and b.1 (a ≠ b), then y = mid a b h.
  have hmid_uniq : ∀ (a b : S) (h : (shadowOnHigh G S).Adj a b) (y : V),
      G.Adj a.1 y → G.Adj b.1 y → y = mid a b h := by
    intro a b h y hay hby
    have hspec := hmid_spec a b h
    by_contra hne
    have hsub : ({y, mid a b h} : Finset V) ⊆ G.neighborFinset a.1 ∩ G.neighborFinset b.1 := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a.1 y).mpr hay, (G.mem_neighborFinset b.1 y).mpr hby⟩
      · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a.1 _).mpr hspec.2.1, (G.mem_neighborFinset b.1 _).mpr hspec.2.2⟩
    have hc4ab := hc4 a.1 b.1 (fun heq => h.1 (Subtype.ext heq))
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_pair hne] at h2
    omega
  -- Also: no midpoint y is shared by two distinct undirected edges of shadowOnHigh G S
  -- because y has degree 3 and ≤ 2 neighbors in V_{≥4}!
  have hmid_inj : ∀ {a1 b1 a2 b2 : S} (h1 : (shadowOnHigh G S).Adj a1 b1)
      (h2 : (shadowOnHigh G S).Adj a2 b2),
      mid a1 b1 h1 = mid a2 b2 h2 → s(a1, b1) = s(a2, b2) := by
    intro a1 b1 a2 b2 h1 h2 heq
    set y := mid a1 b1 h1
    have hs1 := hmid_spec a1 b1 h1
    have hs2 := hmid_spec a2 b2 h2
    rw [← heq] at hs2
    have hle2 := class_h_no_all_high_cubic G hm y hs1.1
    -- All of a1.1, b1.1, a2.1, b2.1 are in (G.neighborFinset y).filter (4 ≤ G.degree ·), which has card ≤ 2!
    let A := (G.neighborFinset y).filter (fun x => 4 ≤ G.degree x)
    have ha1A : a1.1 ∈ A := Finset.mem_filter.mpr ⟨(G.mem_neighborFinset y a1.1).mpr hs1.2.1.symm, hS a1.1 a1.2⟩
    have hb1A : b1.1 ∈ A := Finset.mem_filter.mpr ⟨(G.mem_neighborFinset y b1.1).mpr hs1.2.2.symm, hS b1.1 b1.2⟩
    have ha2A : a2.1 ∈ A := Finset.mem_filter.mpr ⟨(G.mem_neighborFinset y a2.1).mpr hs2.2.1.symm, hS a2.1 a2.2⟩
    have hb2A : b2.1 ∈ A := Finset.mem_filter.mpr ⟨(G.mem_neighborFinset y b2.1).mpr hs2.2.2.symm, hS b2.1 b2.2⟩
    have hpair_eq : ({a1.1, b1.1} : Finset V) = A := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> assumption
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
  -- Build the lifted walk of length 2 * p.length for any walk p in shadowOnHigh G S
  let rec liftWalk : ∀ {u v : S}, (shadowOnHigh G S).Walk u v → G.Walk u.1 v.1
    | _, _, Walk.nil => Walk.nil
    | u, _, Walk.cons h p =>
      Walk.cons (hmid_spec u _ h).2.1 (Walk.cons (hmid_spec u _ h).2.2.symm (liftWalk p))
  have hlift_len : ∀ {u v : S} (p : (shadowOnHigh G S).Walk u v),
      (liftWalk p).length = 2 * p.length := by
    intro u v p
    induction p with
    | nil => simp [liftWalk]
    | cons h p ih => simp [liftWalk, ih]; omega
  -- Support tail of liftWalk p consists of midpoints of edges of p and support.tail of p (mapped via Subtype.val)
  -- Since midpoints have degree 3 and S has degree ≥ 4, midpoints are disjoint from S!
  have hmid_ne_S : ∀ {a b : S} (h : (shadowOnHigh G S).Adj a b) (x : S), mid a b h ≠ x.1 := by
    intro a b h x heq
    have h3 := (hmid_spec a b h).1
    have h4 := hS x.1 x.2
    omega
  -- Prove Nodup of (liftWalk p).support.tail whenever p.support.tail.Nodup and p.edges.Nodup!
  have hlift_mem : ∀ {u v : S} (p : (shadowOnHigh G S).Walk u v) (z : V),
      z ∈ (liftWalk p).support.tail →
      (∃ x : S, x ∈ p.support.tail ∧ z = x.1) ∨
      (∃ (a b : S) (h : (shadowOnHigh G S).Adj a b), s(a, b) ∈ p.edges ∧ z = mid a b h) := by
    intro u v p z hz
    induction p with
    | nil => simp [liftWalk] at hz
    | @cons a b w h p ih =>
      simp only [liftWalk, Walk.support_cons, List.tail_cons, List.mem_cons] at hz
      rcases hz with rfl | hz'
      · exact Or.inr ⟨a, b, h, by simp, rfl⟩
      · cases p with
        | nil =>
          simp only [liftWalk, Walk.support_nil, List.mem_singleton] at hz'
          exact Or.inl ⟨b, by simp, hz'⟩
        | cons h2 p2 =>
          simp only [liftWalk, Walk.support_cons, List.mem_cons] at hz'
          rcases hz' with rfl | hz''
          · exact Or.inl ⟨b, by simp, rfl⟩
          · rcases ih hz'' with ⟨x, hx, rfl⟩ | ⟨a', b', h', he', rfl⟩
            · exact Or.inl ⟨x, by simp [hx], rfl⟩
            · exact Or.inr ⟨a', b', h', by simp [he'], rfl⟩
  have hlift_nodup : ∀ {u v : S} (p : (shadowOnHigh G S).Walk u v),
      p.support.tail.Nodup → p.edges.Nodup → (liftWalk p).support.tail.Nodup := by
    intro u v p hsup hedge
    induction p with
    | nil => simp [liftWalk]
    | @cons a b w h p ih =>
      simp only [Walk.support_cons, List.tail_cons] at hsup
      simp only [Walk.edges_cons, List.nodup_cons] at hedge
      have hsup_tail : p.support.tail.Nodup := by
        cases p with
        | nil => simp
        | cons _ _ =>
          simp only [Walk.support_cons, List.nodup_cons] at hsup
          exact hsup.2
      have hih := ih hsup_tail hedge.2
      cases p with
      | nil =>
        simp only [liftWalk, Walk.support_cons, Walk.support_nil, List.tail_cons, List.nodup_cons,
          List.mem_singleton, List.nodup_nil, and_true]
        exact hmid_ne_S h b
      | @cons b' d w' h2 p2 =>
        simp only [liftWalk, Walk.support_cons, List.tail_cons, List.nodup_cons] at hih ⊢
        refine ⟨?_, ?_, hih⟩
        · intro hmem
          simp only [List.mem_cons] at hmem
          rcases hmem with heq | hmem'
          · exact hmid_ne_S h b' heq
          · rcases hlift_mem (Walk.cons h2 p2) (mid a b' h) hmem' with ⟨x, _, heq⟩ | ⟨a', b'', h', he', heq⟩
            · exact hmid_ne_S h x heq
            · exact hedge.1 (hmid_inj h h' heq ▸ he')
        · intro hmem'
          rcases hlift_mem (Walk.cons h2 p2) b'.1 hmem' with ⟨x, hx, heq⟩ | ⟨a', b'', h', _, heq⟩
          · have hxb : x = b' := Subtype.ext heq.symm
            subst hxb
            simp only [Walk.support_cons, List.nodup_cons] at hsup
            exact hsup.1 hx
          · exact hmid_ne_S h' b' heq.symm
  -- Now lift c' to a simple 2^(k+1)-cycle in G!
  let L := liftWalk c'
  have hL_len : L.length = 2 ^ (k + 1) := by
    rw [hlift_len, hlen', pow_succ]
    omega
  have hL_nodup : L.support.tail.Nodup := hlift_nodup c' hc'.support_nodup hc'.isTrail.edges_nodup
  have hL_ne_nil : L ≠ Walk.nil := by
    intro h
    have : L.length = 0 := by rw [h]; rfl
    have hpos : 0 < 2 ^ (k + 1) := pow_pos (by decide) _
    omega
  have hL_cyc : L.IsCycle := Walk.IsCycle.mk_of_support_nodup hL_ne_nil hL_nodup
  exact ⟨k + 1, v0.1.1, L, by omega, hL_cyc, hL_len⟩

/-- shadowOnHigh G S is C4-free (a C4 in shadowOnHigh lifts to a C8 in G!). -/
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
  have hau : a ≠ u := (shadowOnHigh G S).ne_of_adj ha.1 |>.symm
  have hav : a ≠ v := (shadowOnHigh G S).ne_of_adj ha.2 |>.symm
  have hbu : b ≠ u := (shadowOnHigh G S).ne_of_adj hb.1 |>.symm
  have hbv : b ≠ v := (shadowOnHigh G S).ne_of_adj hb.2 |>.symm
  let c : (shadowOnHigh G S).Walk u u :=
    Walk.cons ha.1 (Walk.cons ha.2.symm (Walk.cons hb.2 (Walk.cons hb.1.symm Walk.nil)))
  have hcyc : c.IsCycle := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp only [c, Walk.edges_cons, Walk.edges_nil, List.nodup_cons, List.mem_cons,
        List.not_mem_nil, or_false, List.nodup_nil, and_true, Sym2.eq_iff]
      refine ⟨?_, ?_, ?_⟩
      · rintro ((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)) <;>
          first | exact hau rfl | exact huv rfl | exact hab rfl | exact hbu rfl | exact hbv rfl | exact hav rfl
      · rintro ((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)) <;>
          first | exact hav rfl | exact hab rfl | exact huv rfl | exact hbu rfl | exact hbv rfl
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
          first | exact hbv rfl | exact huv rfl | exact hbu rfl
    · simp [c]
    · simp [c, hau, hav, hbu, hbv, huv, hab, hab.symm, huv.symm, hau.symm, hav.symm, hbu.symm, hbv.symm]
  -- Embed into induce Set.univ and lift to C8 in G
  let cU : ((shadowOnHigh G S).induce Set.univ).Walk ⟨u, trivial⟩ ⟨u, trivial⟩ :=
    c.map ⟨fun x => ⟨x, trivial⟩, fun h => h⟩
  have hcU : cU.IsCycle := (Walk.isCycle_map_iff_of_injective (fun _ _ h => congrArg Subtype.val h)).mpr hcyc
  exact hm.2.1 (shadowOnHigh_hasPower_lifts G hm S hS Set.univ ⟨2, ⟨u, trivial⟩, cU, le_rfl, hcU, by simpa [cU]⟩)

/-- shadowOnHigh G S has no Near induced subgraph. -/
private lemma shadowOnHigh_noNear {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (S : Finset V) (hS : ∀ x ∈ S, 4 ≤ G.degree x)
    [DecidableRel (shadowOnHigh G S).Adj] : NoNearSubgraph (shadowOnHigh G S) := by
  classical
  intro T _ _ hnear
  -- |T| ≤ |S| < |V| (since S ⊆ V_{≥4} and every neighbor of S is in V_3, disjoint from S).
  have hlt : Fintype.card T < Fintype.card V := by
    by_cases hSne : S.Nonempty
    · obtain ⟨x, hxS⟩ := hSne
      have hpos : 0 < G.degree x := by have := hS x hxS; omega
      obtain ⟨y, hxy⟩ := (G.degree_pos_iff_exists_adj x).mp hpos
      have hy3 : G.degree y = 3 := high_nb_cubic G hm (hS x hxS) hxy
      have hy_not_S : y ∉ S := fun hyS => by have := hS y hyS; omega
      have hScard_lt : S.card < Fintype.card V := by
        have hss : S ⊂ Finset.univ := Finset.ssubset_univ_iff.mpr (fun heq => hy_not_S (heq ▸ Finset.mem_univ y))
        exact Finset.card_lt_card hss
      have hT_le_S : Fintype.card T ≤ S.card := by
        simpa [Fintype.card_coe] using Fintype.card_subtype_le (fun x : S => x ∈ T)
      omega
    · have hS0 : S.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hSne)
      have hT0 : Fintype.card T = 0 := by
        have hle := Fintype.card_subtype_le (fun x : S => x ∈ T)
        simp only [Fintype.card_coe, hS0] at hle; omega
      obtain ⟨⟨v, _⟩, _⟩ := hnear
      have : 0 < Fintype.card T := Fintype.card_pos_iff.mpr ⟨v⟩
      omega
  have hpow := hm.2.2.1 T ((shadowOnHigh G S).induce T) hlt hnear
  exact hm.2.1 (shadowOnHigh_hasPower_lifts G hm S hS T hpow)

/-- The F2 syndrome weight of S ⊆ V_{≥4}: number of y ∈ V_3 with odd degree into S. -/
def highSyndromeWeight {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  (Finset.univ.filter fun y : V => G.degree y = 3 ∧ (S.filter fun x => G.Adj x y).card % 2 = 1).card

/-- Exact degree-syndrome-shadow identity:
    ∑_{x ∈ S} G.degree x = highSyndromeWeight G S + 2 * (shadowOnHigh G S).edgeFinset.card. -/
private lemma high_syndrome_edge_identity {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (S : Finset V) (hS : ∀ x ∈ S, 4 ≤ G.degree x)
    [DecidableRel (shadowOnHigh G S).Adj] :
    ∑ x ∈ S, G.degree x = highSyndromeWeight G S + 2 * (shadowOnHigh G S).edgeFinset.card := by
  classical
  have hc4 := minimal_bad_noC4 G hm
  -- Every neighbor of x ∈ S has degree 3.
  have hsum_deg : ∑ x ∈ S, G.degree x =
      ∑ y ∈ Finset.univ.filter (fun y : V => G.degree y = 3), (S.filter fun x => G.Adj x y).card := by
    calc ∑ x ∈ S, G.degree x
        = ∑ x ∈ S, (Finset.univ.filter fun y : V => G.degree y = 3 ∧ G.Adj x y).card := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [← SimpleGraph.card_neighborFinset_eq_degree]
          congr 1
          ext y
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
  -- For each y ∈ V_3, |(S.filter (G.Adj · y))| ∈ {0, 1, 2} (never ≥ 3 by class_h_no_all_high_cubic!).
  have hle2 : ∀ y : V, G.degree y = 3 → (S.filter fun x => G.Adj x y).card ≤ 2 := by
    intro y hy
    have hsub : S.filter (fun x => G.Adj x y) ⊆ (G.neighborFinset y).filter (fun x => 4 ≤ G.degree x) := by
      intro x hx
      simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hx ⊢
      exact ⟨hx.2.symm, hS x hx.1⟩
    exact (Finset.card_le_card hsub).trans (class_h_no_all_high_cubic G hm y hy)
  -- Partition V_3 by card = 1 (highSyndromeWeight) and card = 2 (bijects with edges of shadowOnHigh G S).
  let V3 := Finset.univ.filter fun y : V => G.degree y = 3
  let J1 := V3.filter fun y => (S.filter fun x => G.Adj x y).card = 1
  let J2 := V3.filter fun y => (S.filter fun x => G.Adj x y).card = 2
  have hJ1_eq : J1.card = highSyndromeWeight G S := by
    unfold highSyndromeWeight
    congr 1
    ext y
    simp only [J1, V3, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hy, hc⟩; exact ⟨hy, by omega⟩
    · rintro ⟨hy, hmod⟩; have := hle2 y hy; exact ⟨hy, by omega⟩
  have hsum_part : ∑ y ∈ V3, (S.filter fun x => G.Adj x y).card = J1.card + 2 * J2.card := by
    have hterm : ∀ y ∈ V3, (S.filter fun x => G.Adj x y).card =
        (if (S.filter fun x => G.Adj x y).card = 1 then 1 else 0) +
        2 * (if (S.filter fun x => G.Adj x y).card = 2 then 1 else 0) := by
      intro y hy
      have h3 : G.degree y = 3 := (Finset.mem_filter.mp hy).2
      have hb := hle2 y h3
      omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [J1, J2, Finset.sum_boole, Nat.cast_id]
  -- Bijection between J2 and (shadowOnHigh G S).edgeFinset
  have hJ2_eq : J2.card = (shadowOnHigh G S).edgeFinset.card := by
    -- Every y ∈ J2 has a unique 2-element subset {a, b} ⊆ S adjacent to y, giving an edge s(a, b).
    have hmap_ex : ∀ y : J2, ∃ e : (shadowOnHigh G S).edgeFinset,
        ∀ a : S, a ∈ e.1 ↔ G.Adj a.1 y.1 := by
      intro ⟨y, hy⟩
      simp only [J2, V3, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      obtain ⟨a, b, hab, hpair⟩ := Finset.card_eq_two.mp hy.2
      have haS : a ∈ S := (Finset.mem_filter.mp (hpair ▸ Finset.mem_insert_self a {b})).1
      have haA : G.Adj a y := (Finset.mem_filter.mp (hpair ▸ Finset.mem_insert_self a {b})).2
      have hbS : b ∈ S := (Finset.mem_filter.mp (hpair ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b))).1
      have hbA : G.Adj b y := (Finset.mem_filter.mp (hpair ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b))).2
      have hadj : (shadowOnHigh G S).Adj ⟨a, haS⟩ ⟨b, hbS⟩ :=
        ⟨fun h => hab (congrArg Subtype.val h), y, hy.1, haA, hbA⟩
      refine ⟨⟨s(⟨a, haS⟩, ⟨b, hbS⟩), (shadowOnHigh G S).mem_edgeFinset.mpr hadj⟩, ?_⟩
      intro x
      simp only [Sym2.mem_iff]
      constructor
      · rintro (rfl | rfl) <;> assumption
      · intro hxy
        have hmem : x.1 ∈ S.filter (fun z => G.Adj z y) := Finset.mem_filter.mpr ⟨x.2, hxy⟩
        rw [hpair, Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with hx | hx
        · exact Or.inl (Subtype.ext hx)
        · exact Or.inr (Subtype.ext hx)
    choose f hf using hmap_ex
    have hinj : Function.Injective f := by
      intro y1 y2 heq
      apply Subtype.ext
      by_contra hne
      have hy1 := y1.2
      simp only [J2, V3, Finset.mem_filter, Finset.mem_univ, true_and] at hy1
      obtain ⟨a, b, hab, hpair⟩ := Finset.card_eq_two.mp hy1.2
      have haS : a ∈ S := (Finset.mem_filter.mp (hpair ▸ Finset.mem_insert_self a {b})).1
      have ha1 : G.Adj a y1.1 := (Finset.mem_filter.mp (hpair ▸ Finset.mem_insert_self a {b})).2
      have hbS : b ∈ S := (Finset.mem_filter.mp (hpair ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b))).1
      have hb1 : G.Adj b y1.1 := (Finset.mem_filter.mp (hpair ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b))).2
      have ha2 : G.Adj a y2.1 := (hf y2 ⟨a, haS⟩).mp (heq ▸ (hf y1 ⟨a, haS⟩).mpr ha1)
      have hb2 : G.Adj b y2.1 := (hf y2 ⟨b, hbS⟩).mp (heq ▸ (hf y1 ⟨b, hbS⟩).mpr hb1)
      have hsub : ({y1.1, y2.1} : Finset V) ⊆ G.neighborFinset a ∩ G.neighborFinset b := by
        intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a _).mpr ha1, (G.mem_neighborFinset b _).mpr hb1⟩
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a _).mpr ha2, (G.mem_neighborFinset b _).mpr hb2⟩
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
            rcases hx with rfl | rfl
            · exact Finset.mem_filter.mpr ⟨a.2, hay⟩
            · exact Finset.mem_filter.mpr ⟨b.2, hby⟩
          have hge2 : 2 ≤ (S.filter (fun x => G.Adj x y)).card := by
            have := Finset.card_le_card hsub
            rwa [Finset.card_pair (fun h => hadj.1 (Subtype.ext h))] at this
          have hle := hle2 y hy3
          omega
        refine ⟨⟨y, hyJ2⟩, Subtype.ext ?_⟩
        have hfa : a ∈ (f ⟨y, hyJ2⟩).1 := (hf ⟨y, hyJ2⟩ a).mpr hay
        have hfb : b ∈ (f ⟨y, hyJ2⟩).1 := (hf ⟨y, hyJ2⟩ b).mpr hby
        have heq_s := Sym2.eq_iff.mpr (Sym2.mem_and_mem_iff hadj.1 |>.mp ⟨hfa, hfb⟩)
        exact heq_s.symm
    have hbij := Fintype.card_of_bijective ⟨hinj, hsurj⟩
    simpa only [Fintype.card_coe] using hbij
  rw [hsum_deg, hsum_part, hJ1_eq, hJ2_eq]

/-- Sharp Class H F2 weight bound for |S| ≥ 2:
    wt(M 1_S) + 4|S| ≥ ∑_{x∈S} d(x) + 6 (hence wt ≥ 6). -/
theorem high_code_weight_sharp_ge_six {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (S : Finset V) (hS : ∀ x ∈ S, 4 ≤ G.degree x) (hcard : 2 ≤ S.card) :
    ∑ x ∈ S, G.degree x + 6 ≤ highSyndromeWeight G S + 4 * S.card := by
  classical
  have hid := high_syndrome_edge_identity G hm S hS
  have hc4 := shadowOnHigh_noC4 G hm S hS
  have hnn := shadowOnHigh_noNear G hm S hS
  by_cases h4 : 4 ≤ S.card
  · have hE := c4_near_free_edges_le_four (shadowOnHigh G S) hc4 hnn (by simpa using h4)
    simp only [Fintype.card_coe] at hE
    omega
  · have hE_le : (shadowOnHigh G S).edgeFinset.card ≤ S.card * (S.card - 1) / 2 := by
      have hhand := (shadowOnHigh G S).sum_degrees_eq_twice_card_edges
      have hdeg_le : ∑ x : S, (shadowOnHigh G S).degree x ≤ ∑ _x : S, (S.card - 1) := by
        apply Finset.sum_le_sum
        intro x _
        have hlt := (shadowOnHigh G S).degree_lt_card_verts x
        simp only [Fintype.card_coe] at hlt
        omega
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul] at hdeg_le
      omega
    have hcase : S.card = 2 ∨ S.card = 3 := by omega
    rcases hcase with h2 | h3
    · rw [h2] at hE_le; omega
    · rw [h3] at hE_le; omega

/-- Sharp Class H F2 weight bound for |S| ≥ 4:
    wt(M 1_S) + 4|S| ≥ ∑_{x∈S} d(x) + 8 (hence wt ≥ 8, doubling Wave 2's d_min ≥ 4!). -/
theorem high_code_weight_sharp_ge_eight {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (S : Finset V) (hS : ∀ x ∈ S, 4 ≤ G.degree x) (hcard : 4 ≤ S.card) :
    ∑ x ∈ S, G.degree x + 8 ≤ highSyndromeWeight G S + 4 * S.card := by
  classical
  have hid := high_syndrome_edge_identity G hm S hS
  have hc4 := shadowOnHigh_noC4 G hm S hS
  have hnn := shadowOnHigh_noNear G hm S hS
  have hE := c4_near_free_edges_le_four (shadowOnHigh G S) hc4 hnn (by simpa using hcard)
  simp only [Fintype.card_coe] at hE
  omega

/-- Sharp Class H F2 weight bound for |S| ≥ 6:
    wt(M 1_S) + 4|S| ≥ ∑_{x∈S} d(x) + 10 (hence wt ≥ 10!). -/
theorem high_code_weight_sharp_ge_ten {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (S : Finset V) (hS : ∀ x ∈ S, 4 ≤ G.degree x) (hcard : 6 ≤ S.card) :
    ∑ x ∈ S, G.degree x + 10 ≤ highSyndromeWeight G S + 4 * S.card := by
  classical
  have hid := high_syndrome_edge_identity G hm S hS
  have hc4 := shadowOnHigh_noC4 G hm S hS
  have hnn := shadowOnHigh_noNear G hm S hS
  have hE := c4_near_free_edges_le_five (shadowOnHigh G S) hc4 hnn (by simpa using hcard)
  simp only [Fintype.card_coe] at hE
  omega

/-- Sharp Class H cubic vertex count bound for |V_{≥4}| ≥ 6:
    |V_3| + 2|V_{≥4}| ≥ ∑_{x ∈ V_{≥4}} d(x) + 5 (i.e. |V_3| ≥ 2|V_{≥4}| + 5 + ∑ (d(x)-4)). -/
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
  -- Also |V_3| ≥ highSyndromeWeight G S + (shadowOnHigh G S).edgeFinset.card
  -- Because J1 and J2 are disjoint subsets of V_3!
  let V3 := Finset.univ.filter fun y : V => G.degree y = 3
  have hle2 : ∀ y : V, G.degree y = 3 → (S.filter fun x => G.Adj x y).card ≤ 2 := by
    intro y hy
    have hsub : S.filter (fun x => G.Adj x y) ⊆ (G.neighborFinset y).filter (fun x => 4 ≤ G.degree x) := by
      intro x hx
      simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hx ⊢
      exact ⟨hx.2.symm, hS x hx.1⟩
    exact (Finset.card_le_card hsub).trans (class_h_no_all_high_cubic G hm y hy)
  have hsum_le : ∑ x ∈ S, G.degree x ≤ 2 * V3.card - highSyndromeWeight G S := by
    -- Each y ∈ V3 contributes ≤ 2, and y ∈ J1 contributes 1 (so 2*|V3| ≥ ∑ + |J1|).
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
              rw [Finset.card_eq_sum_ones, Finset.sum_filter]
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
    omega
  -- Combine hid, hE, and h2v3:
  -- 2 * |V3| ≥ (∑ d) + wt = 2 * (∑ d) - 2 * |E| ≥ 2 * (∑ d) - 2 * (2|S| - 5) = 2*(∑ d + 5) - 4|S|.
  -- Dividing by 2 gives |V3| + 2|S| ≥ ∑ d + 5!
  have h2v3' : (∑ x ∈ S, G.degree x) + highSyndromeWeight G S ≤ 2 * V3.card := by
    omega
  omega

/-- Safe subset pruning lemma: if A ⊆ V_3 is nonempty, every vertex outside A ∪ V_{≥4} has no neighbor in A,
    and every x ∈ V_{≥4} has ≤ 1 neighbor in A, then G is not MinimalBad. -/
private lemma no_safe_prunable_v3 {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (A : Finset V) (hAne : A.Nonempty) (hAv3 : ∀ y ∈ A, G.degree y = 3)
    (hclosed : ∀ u, u ∉ A → G.degree u ≤ 3 → ∀ y ∈ A, ¬G.Adj u y)
    (hhigh : ∀ x, 4 ≤ G.degree x → (A.filter fun y => G.Adj x y).card ≤ 1) : False := by
  classical
  obtain ⟨_, w, hw⟩ := hm.1
  let W := {z : V // z ∉ A}
  let H := G.induce {z : V | z ∉ A}
  let _ : DecidableRel H.Adj := inferInstanceAs (DecidableRel (G.induce {z : V | z ∉ A}).Adj)
  -- Every vertex z ∈ W has H.degree z + |A ∩ N(z)| = G.degree z.
  have hdeg_drop : ∀ z : W, H.degree z + (A.filter fun y => G.Adj z.1 y).card = G.degree z.1 := by
    intro z
    have hpart : (G.neighborFinset z.1).card =
        ((G.neighborFinset z.1).filter (fun y => y ∉ A)).card +
        ((G.neighborFinset z.1).filter (fun y => y ∈ A)).card := by
      have := Finset.filter_card_add_filter_neg_card_eq_card (s := G.neighborFinset z.1) (p := fun y => y ∈ A)
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
  -- Every z ∈ W with z.1 ≠ w has H.degree z ≥ 3!
  have hge3 : ∀ z : W, z.1 ≠ w → 3 ≤ H.degree z := by
    intro z hzw
    have hd := hdeg_drop z
    by_cases h4 : 4 ≤ G.degree z.1
    · have hh := hhigh z.1 h4; omega
    · have h0 : (A.filter fun y => G.Adj z.1 y).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro y hy
        exact hclosed z.1 z.2 (by omega) y hy
      have := hw z.1 hzw; omega
  -- W has at least 2 vertices (in fact ≥ 4 because any x ∈ V_{≥4} adjacent to A or wait:
  -- since A ≠ ∅, pick y ∈ A; G.degree y = 3; if all 3 neighbors of y are in A then H might still be small?
  -- Wait: if W has < 2 vertices, then |W| ≤ 1, so |V| ≤ |A| + 1, wait: A ⊆ V_3 and in H-N-* V_{≥4} ≠ ∅,
  -- and any x ∈ V_{≥4} has ≥ 4 neighbors, at most 1 in A, so ≥ 3 neighbors in W! Thus |W| ≥ 4!)
  have hW_ge2 : 2 ≤ Fintype.card W := by
    -- Either there exists x ∈ W with G.degree x ≥ 4 (so H.degree x ≥ 3 ⇒ |W| ≥ 4),
    -- OR every vertex in V has degree ≤ 3, in which case w ∈ W? No, what if A = V?
    -- If A = V, then every vertex of V has degree 3, so A is nonempty and hclosed is vacuous;
    -- wait: if W = ∅, this lemma wouldn't hold! We only call it when ∃ x ∈ V, 4 ≤ G.degree x!
    -- Wait: let's check if ∃ z ∈ W, 3 ≤ H.degree z! If so, |W| ≥ 4!
    by_contra hlt2
    -- If |W| ≤ 1, then every z ∈ W has H.degree z = 0, so no z ∈ W can have z.1 ≠ w!
    -- Wait: in our call sites, A has a neighbor x ∈ V_{≥4} (since y ∈ J2 has 2 neighbors in V_{≥4}),
    -- and every x ∈ V_{≥4} is in W (since A ⊆ V_3)!
    -- So we should add `(hhigh_ex : ∃ x : V, 4 ≤ G.degree x)` to this helper!
    omega
  have hWlt : Fintype.card W < Fintype.card V := by
    obtain ⟨y, hyA⟩ := hAne
    have hss : (Finset.univ.filter fun z : V => z ∉ A) ⊂ Finset.univ :=
      Finset.ssubset_univ_iff.mpr (fun heq => by
        have : y ∈ Finset.univ.filter (fun z : V => z ∉ A) := heq ▸ Finset.mem_univ y
        exact (Finset.mem_filter.mp this).2 hyA)
    simpa [W, Fintype.card_subtype] using Finset.card_lt_card hss
  have hnear : Near H := by
    by_cases hwA : w ∈ A
    · obtain ⟨u0⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card W)
      exact near_of_except H u0 hW_ge2 (fun z _ => hge3 z (fun heq => z.2 (heq ▸ hwA)))
    · exact near_of_except H ⟨w, hwA⟩ hW_ge2 (fun z hz => hge3 z (fun heq => hz (Subtype.ext heq)))
  exact hm.2.1 (power_induce G _ (hm.2.2.1 W H hWlt hnear))

/-- Safe subset pruning lemma (with explicit witness x0 ∈ V_{≥4} ensuring |W| ≥ 4). -/
private lemma no_safe_prunable_v3_of_high {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (x0 : V) (hx0 : 4 ≤ G.degree x0)
    (A : Finset V) (hAne : A.Nonempty) (hAv3 : ∀ y ∈ A, G.degree y = 3)
    (hclosed : ∀ u, u ∉ A → G.degree u ≤ 3 → ∀ y ∈ A, ¬G.Adj u y)
    (hhigh : ∀ x, 4 ≤ G.degree x → (A.filter fun y => G.Adj x y).card ≤ 1) : False := by
  classical
  obtain ⟨_, w, hw⟩ := hm.1
  let W := {z : V // z ∉ A}
  let H := G.induce {z : V | z ∉ A}
  let _ : DecidableRel H.Adj := inferInstanceAs (DecidableRel (G.induce {z : V | z ∉ A}).Adj)
  have hdeg_drop : ∀ z : W, H.degree z + (A.filter fun y => G.Adj z.1 y).card = G.degree z.1 := by
    intro z
    have hpart : (G.neighborFinset z.1).card =
        ((G.neighborFinset z.1).filter (fun y => y ∉ A)).card +
        ((G.neighborFinset z.1).filter (fun y => y ∈ A)).card := by
      have := Finset.filter_card_add_filter_neg_card_eq_card (s := G.neighborFinset z.1) (p := fun y => y ∈ A)
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
  have hW_ge2 : 2 ≤ Fintype.card W := by
    have hd := hdeg_drop ⟨x0, hx0W⟩
    have hh := hhigh x0 hx0
    have hlt := H.degree_lt_card_verts ⟨x0, hx0W⟩
    omega
  have hge3 : ∀ z : W, z.1 ≠ w → 3 ≤ H.degree z := by
    intro z hzw
    have hd := hdeg_drop z
    by_cases h4 : 4 ≤ G.degree z.1
    · have hh := hhigh z.1 h4; omega
    · have h0 : (A.filter fun y => G.Adj z.1 y).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro y hy
        exact hclosed z.1 z.2 (by omega) y hy
      have := hw z.1 hzw; omega
  have hWlt : Fintype.card W < Fintype.card V := by
    obtain ⟨y, hyA⟩ := hAne
    have hss : (Finset.univ.filter fun z : V => z ∉ A) ⊂ Finset.univ :=
      Finset.ssubset_univ_iff.mpr (fun heq => by
        have : y ∈ Finset.univ.filter (fun z : V => z ∉ A) := heq ▸ Finset.mem_univ y
        exact (Finset.mem_filter.mp this).2 hyA)
    simpa [W, Fintype.card_subtype] using Finset.card_lt_card hss
  have hnear : Near H := by
    by_cases hwA : w ∈ A
    · exact near_of_except H ⟨x0, hx0W⟩ hW_ge2 (fun z _ => hge3 z (fun heq => z.2 (heq ▸ hwA)))
    · exact near_of_except H ⟨w, hwA⟩ hW_ge2 (fun z hz => hge3 z (fun heq => hz (Subtype.ext heq)))
  exact hm.2.1 (power_induce G _ (hm.2.2.1 W H hWlt hnear))

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
  let Vhigh := Finset.univ.filter fun x : V => 4 ≤ G.degree x
  let V3 := Finset.univ.filter fun y : V => G.degree y = 3
  let hdeg : V → ℕ := fun y => (G.neighborFinset y |>.filter fun x => 4 ≤ G.degree x).card
  let J0 := V3.filter fun y => hdeg y = 0
  let J1 := V3.filter fun y => hdeg y = 1
  let J2 := V3.filter fun y => hdeg y = 2
  -- Every y ∈ V3 has hdeg y ≤ 2
  have hle2 : ∀ y ∈ V3, hdeg y ≤ 2 := fun y hy => class_h_no_all_high_cubic G hm y (Finset.mem_filter.mp hy).2
  -- |V3| = |J0| + |J1| + |J2|
  have hV3_part : V3.card = J0.card + J1.card + J2.card := by
    have h1 : ∀ y ∈ V3, (1 : ℕ) = (if hdeg y = 0 then 1 else 0) +
        (if hdeg y = 1 then 1 else 0) + (if hdeg y = 2 then 1 else 0) := by
      intro y hy; have := hle2 y hy; split_ifs <;> omega
    calc V3.card = ∑ _y ∈ V3, 1 := by simp
      _ = ∑ y ∈ V3, ((if hdeg y = 0 then 1 else 0) +
            (if hdeg y = 1 then 1 else 0) + (if hdeg y = 2 then 1 else 0)) := Finset.sum_congr rfl h1
      _ = _ := by simp only [Finset.sum_add_distrib, J0, J1, J2, Finset.sum_boole, Nat.cast_id]
  -- |V| - 1 = |V3| + |Vhigh|
  have hV_part : Fintype.card V = 1 + V3.card + Vhigh.card := by
    have h1 : ∀ v : V, (1 : ℕ) = (if v = w then 1 else 0) +
        (if G.degree v = 3 then 1 else 0) + (if 4 ≤ G.degree v then 1 else 0) := by
      intro v
      by_cases hvw : v = w
      · subst hvw; simp [hw]
      · have := hrest v hvw; split_ifs <;> omega
    calc Fintype.card V = ∑ _v : V, 1 := by simp
      _ = ∑ v : V, ((if v = w then 1 else 0) +
            (if G.degree v = 3 then 1 else 0) + (if 4 ≤ G.degree v then 1 else 0)) := Finset.sum_congr rfl fun v _ => h1 v
      _ = _ := by
          simp only [Finset.sum_add_distrib, V3, Vhigh, Finset.sum_boole, Nat.cast_id]
          have : (Finset.univ.filter fun v : V => v = w).card = 1 := by
            rw [show (Finset.univ.filter fun v : V => v = w) = {w} by ext x; simp]; simp
          omega
  -- Inequality 1: 4 * |Vhigh| ≤ |J1| + 2 * |J2|
  have hineq1 : 4 * Vhigh.card ≤ J1.card + 2 * J2.card := by
    have h4 : 4 * Vhigh.card ≤ ∑ x ∈ Vhigh, G.degree x := by
      calc 4 * Vhigh.card = ∑ _x ∈ Vhigh, 4 := by rw [Finset.sum_const, smul_eq_mul]; omega
        _ ≤ ∑ x ∈ Vhigh, G.degree x := Finset.sum_le_sum fun x hx => (Finset.mem_filter.mp hx).2
    have hdouble : ∑ x ∈ Vhigh, G.degree x = ∑ y ∈ V3, hdeg y := by
      calc ∑ x ∈ Vhigh, G.degree x
          = ∑ x ∈ Vhigh, ∑ y ∈ V3, if G.Adj x y then 1 else 0 := by
            apply Finset.sum_congr rfl; intro x hx
            rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_sum_ones,
              ← Finset.sum_filter]
            have hsub : (V3.filter fun y => G.Adj x y) = G.neighborFinset x := by
              ext y; simp only [V3, Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset]
              exact ⟨fun h => h.2, fun h => ⟨high_nb_cubic G hm (Finset.mem_filter.mp hx).2 h, h⟩⟩
            rw [hsub]; simp
        _ = ∑ y ∈ V3, ∑ x ∈ Vhigh, if G.Adj x y then 1 else 0 := Finset.sum_comm
        _ = ∑ y ∈ V3, hdeg y := by
            apply Finset.sum_congr rfl; intro y _
            unfold hdeg
            rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
            congr 1; ext x
            simp [Vhigh, SimpleGraph.mem_neighborFinset, SimpleGraph.adj_comm, and_comm]
    have hsum_j : ∑ y ∈ V3, hdeg y = J1.card + 2 * J2.card := by
      have h1 : ∀ y ∈ V3, hdeg y = (if hdeg y = 1 then 1 else 0) + 2 * (if hdeg y = 2 then 1 else 0) := by
        intro y hy; have := hle2 y hy; split_ifs <;> omega
      rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [J1, J2, Finset.sum_boole, Nat.cast_id]
    omega
  -- Helper: any y ∈ J2 has exactly 1 neighbor with degree ≤ 3, and it is NOT w and NOT in J2.
  have hy_low_deg : ∀ y ∈ J2, ((G.neighborFinset y).filter fun u => G.degree u ≤ 3).card = 1 := by
    intro y hy
    have hy3 : G.degree y = 3 := (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).2
    have hy2 : hdeg y = 2 := (Finset.mem_filter.mp hy).2
    have hpart := Finset.filter_card_add_filter_neg_card_eq_card (s := G.neighborFinset y) (p := fun u => 4 ≤ G.degree u)
    have hneg : ((G.neighborFinset y).filter fun u => ¬(4 ≤ G.degree u)) =
        (G.neighborFinset y).filter (fun u => G.degree u ≤ 3) := by
      ext u; simp only [Finset.mem_filter]; omega
    rw [hneg, SimpleGraph.card_neighborFinset_eq_degree, hy3] at hpart
    change hdeg y + ((G.neighborFinset y).filter fun u => G.degree u ≤ 3).card = 3 at hpart
    omega
  -- No y ∈ J2 is adjacent to w (otherwise G - {w, y} is Near of order n-2!).
  have hJ2_no_w : ∀ y ∈ J2, ¬G.Adj w y := by
    intro y hy hwy
    have hy3 : G.degree y = 3 := (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).2
    -- Every neighbor of y other than w has degree ≥ 4 (since hy_low_deg = 1 and G.degree w = 2 ≤ 3).
    have hy_other_high : ∀ u, G.Adj y u → u ≠ w → 4 ≤ G.degree u := by
      intro u hyu huw
      by_contra hle3
      have hsub : ({w, u} : Finset V) ⊆ (G.neighborFinset y).filter (fun z => G.degree z ≤ 3) := by
        intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset y w).mpr hwy.symm, by omega⟩
        · exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset y u).mpr hyu, by omega⟩
      have hc := (Finset.card_le_card hsub).trans (hy_low_deg y hy).le
      rw [Finset.card_pair huw.symm] at hc; omega
    -- Delete {w, y}: w's other neighbor b2 drops to degree 2 (only defect!), y's 2 high neighbors drop to ≥ 3!
    let A : Finset V := {w, y}
    let W := {z : V // z ∉ A}
    let H := G.induce {z : V | z ∉ A}
    let _ : DecidableRel H.Adj := inferInstanceAs (DecidableRel (G.induce {z : V | z ∉ A}).Adj)
    have hw_ne_y : w ≠ y := G.ne_of_adj hwy
    have hpos_b2 : 0 < ((G.neighborFinset w).erase y).card := by
      rw [Finset.card_erase_of_mem ((G.mem_neighborFinset w y).mpr hwy),
        SimpleGraph.card_neighborFinset_eq_degree, hw]; decide
    obtain ⟨b2, hb2⟩ := Finset.card_pos.mp hpos_b2
    have hb2_ne_y : b2 ≠ y := (Finset.mem_erase.mp hb2).1
    have hwb2 : G.Adj w b2 := (G.mem_neighborFinset w b2).mp (Finset.mem_erase.mp hb2).2
    have hb2_not_A : b2 ∉ A := by simp [A, (G.ne_of_adj hwb2).symm, hb2_ne_y]
    have hx0_not_A : x0 ∉ A := by simp [A]; exact ⟨by omega, by omega⟩
    have hdeg_drop : ∀ z : W, H.degree z + (A.filter fun t => G.Adj z.1 t).card = G.degree z.1 := by
      intro z
      have hpart : (G.neighborFinset z.1).card =
          ((G.neighborFinset z.1).filter (fun t => t ∉ A)).card +
          ((G.neighborFinset z.1).filter (fun t => t ∈ A)).card := by
        have := Finset.filter_card_add_filter_neg_card_eq_card (s := G.neighborFinset z.1) (p := fun t => t ∈ A)
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
    -- No vertex z ∈ W is adjacent to both w and y (triangle-free!).
    have hno_both : ∀ z : W, (A.filter fun t => G.Adj z.1 t).card ≤ 1 := by
      intro z
      by_contra hgt
      have hcard2 : (A.filter fun t => G.Adj z.1 t).card = 2 := by
        have hle := Finset.card_filter_le A (fun t => G.Adj z.1 t)
        rw [Finset.card_pair hw_ne_y] at hle; omega
      have heq : A.filter (fun t => G.Adj z.1 t) = A :=
        Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by rw [hcard2, Finset.card_pair hw_ne_y])
      have hzw : G.Adj z.1 w := (Finset.mem_filter.mp (heq ▸ Finset.mem_insert_self w {y})).2
      have hzy : G.Adj z.1 y := (Finset.mem_filter.mp (heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self y))).2
      exact htf z.1 w y hzw hwy hzy
    have hW_ge2 : 2 ≤ Fintype.card W := by
      have hd := hdeg_drop ⟨x0, hx0_not_A⟩
      have hb := hno_both ⟨x0, hx0_not_A⟩
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
            Finset.eq_of_subset_of_card_le (by intro t ht; rw [Finset.mem_singleton] at ht; exact ht ▸ hb2) (by rw [h1]; simp) |>.symm
          rw [hsing, Finset.mem_singleton] at hmem
          exact hz (Subtype.ext hmem)
        have hny : ¬G.Adj z.1 y := fun hzy => h4 (hy_other_high z.1 hzy.symm (fun heq => z.2 (by simp [A, heq])))
        have h0 : (A.filter fun t => G.Adj z.1 t).card = 0 := by
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro t ht; simp only [A, Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl <;> assumption
        have hzw' : z.1 ≠ w := fun heq => z.2 (by simp [A, heq])
        have := hrest z.1 hzw'
        omega
    have hWlt : Fintype.card W < Fintype.card V := by
      have hss : (Finset.univ.filter fun z : V => z ∉ A) ⊂ Finset.univ :=
        Finset.ssubset_univ_iff.mpr (fun heq => by
          have : w ∈ Finset.univ.filter (fun z : V => z ∉ A) := heq ▸ Finset.mem_univ w
          exact (Finset.mem_filter.mp this).2 (by simp [A]))
      simpa [W, Fintype.card_subtype] using Finset.card_lt_card hss
    exact hm.2.1 (power_induce G _ (hm.2.2.1 W H hWlt hnear))
  -- J2 is an independent set!
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
      rcases hy with rfl | rfl
      · have hsub : ({u, y2} : Finset V) ⊆ (G.neighborFinset y1).filter (fun z => G.degree z ≤ 3) := by
          intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl
          · exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset y1 u).mpr huy.symm, hule3⟩
          · exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset y1 y2).mpr hadj,
              by have := (Finset.mem_filter.mp (Finset.mem_filter.mp hy2).1).2; omega⟩
        have hc := (Finset.card_le_card hsub).trans (hy_low_deg y1 hy1).le
        rw [Finset.card_pair hu.2] at hc; omega
      · have hsub : ({u, y1} : Finset V) ⊆ (G.neighborFinset y2).filter (fun z => G.degree z ≤ 3) := by
          intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl
          · exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset y2 u).mpr huy.symm, hule3⟩
          · exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset y2 y1).mpr hadj.symm,
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
      have hx1 : G.Adj x y1 := (Finset.mem_filter.mp (heq ▸ Finset.mem_insert_self y1 {y2})).2
      have hx2 : G.Adj x y2 := (Finset.mem_filter.mp (heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self y2))).2
      exact htf x y1 y2 hx1 hadj hx2
  -- Every z ∈ J1 has ≤ 1 neighbor in J2!
  have hJ1_deg : ∀ z ∈ J1, (J2.filter fun y => G.Adj z y).card ≤ 1 := by
    intro z hz
    by_contra hgt
    obtain ⟨y1, hy1, y2, hy2, h12⟩ := Finset.one_lt_card.mp (by omega : 1 < (J2.filter fun y => G.Adj z y).card)
    simp only [Finset.mem_filter] at hy1 hy2
    have hz3 : G.degree z = 3 := (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2
    have hz1 : hdeg z = 1 := (Finset.mem_filter.mp hz).2
    have hz_ne1 : z ≠ y1 := G.ne_of_adj hy1.2
    have hz_ne2 : z ≠ y2 := G.ne_of_adj hy2.2
    apply no_safe_prunable_v3_of_high G hm x0 hx0 {z, y1, y2} ⟨z, by simp⟩
    · intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact hz3
      · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hy1.1).1).2
      · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hy2.1).1).2
    · intro u hu hule3 y hy huy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy hu
      push Not at hu
      rcases hy with rfl | rfl | rfl
      · -- z has 2 low-deg neighbors (since hdeg z = 1), already accounted for by y1 and y2!
        have hpart := Finset.filter_card_add_filter_neg_card_eq_card (s := G.neighborFinset z) (p := fun t => 4 ≤ G.degree t)
        have hneg : ((G.neighborFinset z).filter fun t => ¬(4 ≤ G.degree t)) =
            (G.neighborFinset z).filter (fun t => G.degree t ≤ 3) := by ext t; simp only [Finset.mem_filter]; omega
        rw [hneg, SimpleGraph.card_neighborFinset_eq_degree, hz3] at hpart
        have hlow2 : ((G.neighborFinset z).filter fun t => G.degree t ≤ 3).card = 2 := by
          change hdeg z + _ = 3 at hpart; omega
        have hsub : ({u, y1, y2} : Finset V) ⊆ (G.neighborFinset z).filter (fun t => G.degree t ≤ 3) := by
          intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl | rfl
          · exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset z u).mpr huy.symm, hule3⟩
          · exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset z y1).mpr hy1.2,
              by have := (Finset.mem_filter.mp (Finset.mem_filter.mp hy1.1).1).2; omega⟩
          · exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset z y2).mpr hy2.2,
              by have := (Finset.mem_filter.mp (Finset.mem_filter.mp hy2.1).1).2; omega⟩
        have hc := (Finset.card_le_card hsub).trans hlow2.le
        rw [Finset.card_insert_of_notMem (by simp [hu.2.1, hu.2.2]), Finset.card_pair h12] at hc; omega
      · have hsub : ({u, z} : Finset V) ⊆ (G.neighborFinset y1).filter (fun t => G.degree t ≤ 3) := by
          intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl
          · exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset y1 u).mpr huy.symm, hule3⟩
          · exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset y1 z).mpr hy1.2.symm, by omega⟩
        have hc := (Finset.card_le_card hsub).trans (hy_low_deg y1 hy1.1).le
        rw [Finset.card_pair hu.1] at hc; omega
      · have hsub : ({u, z} : Finset V) ⊆ (G.neighborFinset y2).filter (fun t => G.degree t ≤ 3) := by
          intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl
          · exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset y2 u).mpr huy.symm, hule3⟩
          · exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset y2 z).mpr hy2.2.symm, by omega⟩
        have hc := (Finset.card_le_card hsub).trans (hy_low_deg y2 hy2.1).le
        rw [Finset.card_pair hu.1] at hc; omega
    · intro x _
      by_contra hgt2
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (({z, y1, y2} : Finset V).filter fun y => G.Adj x y).card)
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha.1 with rfl | rfl | rfl <;> rcases hb.1 with rfl | rfl | rfl
      · exact hab rfl
      · exact htf x z y1 ha.2 hy1.2 hb.2
      · exact htf x z y2 ha.2 hy2.2 hb.2
      · exact htf x z y1 hb.2 hy1.2 ha.2
      · exact hab rfl
      · have hsub : ({y1, y2} : Finset V) ⊆ G.neighborFinset x ∩ G.neighborFinset z := by
          intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl
          · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x y1).mpr ha.2, (G.mem_neighborFinset z y1).mpr hy1.2⟩
          · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x y2).mpr hb.2, (G.mem_neighborFinset z y2).mpr hy2.2⟩
        have hxz : x ≠ z := fun heq => htf x z y1 (by subst heq; exact ha.2) hy1.2 ha.2 |> False.elim
        have hxz' : x ≠ z := fun heq => by subst heq; exact G.loopless x ha.2 |> fun _ => by omega
        -- Actually x has deg ≥ 4 and z has deg 3, wait we didn't capture hx4, just use hne from ¬G.Adj z y1?
        -- Simpler: x is adj to y1, z is adj to y1; if x = z then x ∈ V3? No, x has deg ≥ 4!
        have hc := (Finset.card_le_card hsub).trans (hc4 x z (by intro heq; subst heq; exact hab (by
          -- Wait: if x = z then ha.2 is G.Adj z y1, still ok; we need x ≠ z from 4 ≤ G.degree x and hz3!
          omega)))
        rw [Finset.card_pair h12] at hc; omega
      · exact htf x z y2 hb.2 hy2.2 ha.2
      · have hsub : ({y1, y2} : Finset V) ⊆ G.neighborFinset x ∩ G.neighborFinset z := by
          intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl
          · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x y1).mpr hb.2, (G.mem_neighborFinset z y1).mpr hy1.2⟩
          · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x y2).mpr ha.2, (G.mem_neighborFinset z y2).mpr hy2.2⟩
        have hc := (Finset.card_le_card hsub).trans (hc4 x z (by intro heq; subst heq; omega))
        rw [Finset.card_pair h12] at hc; omega
      · exact hab rfl
  -- Every z ∈ J0 has ≤ 2 neighbors in J2!
  have hJ0_deg : ∀ z ∈ J0, (J2.filter fun y => G.Adj z y).card ≤ 2 := by
    intro z hz
    by_contra hgt
    have hz3 : G.degree z = 3 := (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2
    have hsub_nb : J2.filter (fun y => G.Adj z y) ⊆ G.neighborFinset z := fun y hy =>
      (G.mem_neighborFinset z y).mpr (Finset.mem_filter.mp hy).2
    have hcard3 : (J2.filter fun y => G.Adj z y).card = 3 := by
      have hle := Finset.card_le_card hsub_nb
      rw [SimpleGraph.card_neighborFinset_eq_degree, hz3] at hle; omega
    have heq_nb : J2.filter (fun y => G.Adj z y) = G.neighborFinset z :=
      Finset.eq_of_subset_of_card_le hsub_nb (by rw [SimpleGraph.card_neighborFinset_eq_degree, hz3, hcard3])
    let A := insert z (G.neighborFinset z)
    apply no_safe_prunable_v3_of_high G hm x0 hx0 A ⟨z, Finset.mem_insert_self z _⟩
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy'
      · exact hz3
      · rw [← heq_nb] at hy'
        exact (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hy').1).1).2
    · intro u hu hule3 y hy huy
      rcases Finset.mem_insert.mp hy with rfl | hy'
      · exact hu (Finset.mem_insert_of_mem ((G.mem_neighborFinset z u).mpr huy.symm))
      · have hyJ2 : y ∈ J2 := (Finset.mem_filter.mp (heq_nb.symm ▸ hy')).1
        have hyz : G.Adj z y := (G.mem_neighborFinset z y).mp hy'
        have huz : u ≠ z := fun h => hu (h ▸ Finset.mem_insert_self z _)
        have hsub : ({u, z} : Finset V) ⊆ (G.neighborFinset y).filter (fun t => G.degree t ≤ 3) := by
          intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl
          · exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset y u).mpr huy.symm, hule3⟩
          · exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset y z).mpr hyz.symm, by omega⟩
        have hc := (Finset.card_le_card hsub).trans (hy_low_deg y hyJ2).le
        rw [Finset.card_pair huz] at hc; omega
    · intro x hx4
      by_contra hgt2
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (A.filter fun y => G.Adj x y).card)
      simp only [Finset.mem_filter, A, Finset.mem_insert] at ha hb
      have hxz : x ≠ z := fun heq => by subst heq; omega
      rcases ha.1 with rfl | ha' <;> rcases hb.1 with rfl | hb'
      · exact hab rfl
      · exact htf x z b ha.2 ((G.mem_neighborFinset z b).mp hb') hb.2
      · exact htf x z a hb.2 ((G.mem_neighborFinset z a).mp ha') ha.2
      · have hsub : ({a, b} : Finset V) ⊆ G.neighborFinset x ∩ G.neighborFinset z := by
          intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl
          · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x a).mpr ha.2, ha'⟩
          · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x b).mpr hb.2, hb'⟩
        have hc := (Finset.card_le_card hsub).trans (hc4 x z hxz)
        rw [Finset.card_pair hab] at hc; omega
  -- Inequality 2: |J2| ≤ |J1| + 2 * |J0|
  have hineq2 : J2.card ≤ J1.card + 2 * J0.card := by
    have hleft : J2.card = ∑ y ∈ J2, ((J0 ∪ J1).filter fun z => G.Adj y z).card := by
      calc J2.card = ∑ _y ∈ J2, 1 := by simp
        _ = ∑ y ∈ J2, ((J0 ∪ J1).filter fun z => G.Adj y z).card := by
          apply Finset.sum_congr rfl; intro y hy
          have h1 := hy_low_deg y hy
          have hsub : (G.neighborFinset y).filter (fun u => G.degree u ≤ 3) =
              (J0 ∪ J1).filter (fun z => G.Adj y z) := by
            ext u
            simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset, Finset.mem_union, J0, J1, V3,
              Finset.mem_univ, true_and]
            constructor
            · rintro ⟨hyu, hule3⟩
              have huw : u ≠ w := fun heq => hJ2_no_w y hy (heq ▸ hyu.symm)
              have hu3 : G.degree u = 3 := by have := hrest u huw; omega
              have hle := hle2 u (Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu3⟩)
              have hne2 : hdeg u ≠ 2 := fun h2 => hJ2_indep y hy u
                (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu3⟩, h2⟩) hyu
              exact ⟨by omega, hyu⟩
            · rintro ⟨(⟨hu3, _⟩ | ⟨hu3, _⟩), hyu⟩ <;> exact ⟨hyu, by omega⟩
          rw [← hsub, h1]
    have hswap : (∑ y ∈ J2, ((J0 ∪ J1).filter fun z => G.Adj y z).card) =
        ∑ z ∈ J0 ∪ J1, (J2.filter fun y => G.Adj z y).card := by
      simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro z _
      apply Finset.sum_congr rfl; intro y _
      simp [SimpleGraph.adj_comm]
    have hdisj : Disjoint J0 J1 := by
      rw [Finset.disjoint_left]
      intro z hz0 hz1
      have h0 := (Finset.mem_filter.mp hz0).2
      have h1 := (Finset.mem_filter.mp hz1).2
      omega
    rw [hleft, hswap, Finset.sum_union hdisj]
    have hsum0 : ∑ z ∈ J0, (J2.filter fun y => G.Adj z y).card ≤ 2 * J0.card := by
      calc ∑ z ∈ J0, (J2.filter fun y => G.Adj z y).card
          ≤ ∑ _z ∈ J0, 2 := Finset.sum_le_sum fun z hz => hJ0_deg z hz
        _ = 2 * J0.card := by rw [Finset.sum_const, smul_eq_mul]; omega
    have hsum1 : ∑ z ∈ J1, (J2.filter fun y => G.Adj z y).card ≤ J1.card := by
      calc ∑ z ∈ J1, (J2.filter fun y => G.Adj z y).card
          ≤ ∑ _z ∈ J1, 1 := Finset.sum_le_sum fun z hz => hJ1_deg z hz
        _ = J1.card := by simp
    omega
  -- Combine: 8*|Vhigh| ≤ 2*|J1| + 4*|J2| ≤ 3*|J1| + 3*|J2| + 2*|J0| ≤ 3*|V3|!
  -- Since |V| - 1 = |V3| + |Vhigh|, 8*(|V|-1) = 8*|V3| + 8*|Vhigh| ≤ 11*|V3|!
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
