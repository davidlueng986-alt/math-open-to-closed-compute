import Mathlib

open Classical
open SimpleGraph

namespace E64Wave7Agent3P3

/-!
# Wave 7 Agent #3 — Pillar 3: F₂ Cycle-Space Parity, Theta & Chordal-Shortcut Exclusions
-/

def IsPowerOfTwo (L : ℕ) : Prop := ∃ k : ℕ, 2 ≤ k ∧ L = 2 ^ k

def HasPowerCycle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ IsPowerOfTwo p.length

def PowerFree {V : Type*} (G : SimpleGraph V) : Prop := ¬ HasPowerCycle G

def MinDegGe {V : Type*} [Fintype V] (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∀ v : V, d ≤ G.degree v

def Defects {V : Type*} [Fintype V] (G : SimpleGraph V) : Finset V :=
  Finset.univ.filter (fun v => G.degree v = 2)

def Bad2 {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  PowerFree G ∧ MinDegGe G 2 ∧ (Defects G).card ≤ 2

def MinimalBad2 {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  Bad2 G ∧
  (∀ (m : ℕ) (H : SimpleGraph (Fin m)), Bad2 H → Fintype.card V ≤ m) ∧
  (∀ (H : SimpleGraph V), Bad2 H → G.edgeFinset.card ≤ H.edgeFinset.card)

lemma mem_support_of_edge {V : Type*} {G : SimpleGraph V} {u v w : V} {e : Sym2 V}
    (p : G.Walk u v) (he : e ∈ p.edges) (hw : w ∈ e) : w ∈ p.support := by
  induction p with
  | nil => simp at he
  | @cons a b c hab rest ih =>
    simp only [Walk.edges_cons, List.mem_cons] at he
    rcases he with rfl | h'
    · simp only [Sym2.mem_iff] at hw
      rcases hw with rfl | rfl
      · exact Walk.start_mem_support _
      · exact List.mem_cons_of_mem _ (Walk.start_mem_support _)
    · exact List.mem_cons_of_mem _ (ih h')

lemma walk_adj_of_mem_edges {V : Type*} {G : SimpleGraph V} {u v x y : V}
    (p : G.Walk u v) (h : s(x, y) ∈ p.edges) : G.Adj x y := by
  induction p with
  | nil => simp at h
  | @cons a b c hab rest ih =>
    simp only [Walk.edges_cons, List.mem_cons] at h
    rcases h with heq | h'
    · rw [Sym2.eq_iff] at heq
      rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hab
      · exact hab.symm
    · exact ih h'

lemma isPath_mem_edges_endpoints_length_one {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hp : p.IsPath) (hmem : s(u, v) ∈ p.edges) : p.length = 1 := by
  cases p with
  | nil => simp at hmem
  | @cons _ w _ huw q =>
    simp only [Walk.edges_cons, List.mem_cons] at hmem
    rcases hmem with heq | hmem'
    · rw [Sym2.eq_iff] at heq
      rcases heq with ⟨_, rfl⟩ | ⟨hvu, rfl⟩
      · cases q with
        | nil => rfl
        | @cons _ z _ hvz q' =>
          have hnd := List.nodup_cons.mp (List.nodup_cons.mp hp.support_nodup).2
          exact False.elim (hnd.1 (Walk.end_mem_support q'))
      · exact False.elim (G.ne_of_adj huw hvu.symm)
    · have hu_in : u ∈ q.support := mem_support_of_edge q hmem' (by simp)
      exact False.elim ((List.nodup_cons.mp hp.support_nodup).1 hu_in)

lemma two_internally_disjoint_paths_cycle {V : Type*} {G : SimpleGraph V} {u v : V}
    (p q : G.Walk u v) (hp : p.IsPath) (hq : q.IsPath)
    (hp1 : 1 ≤ p.length) (hq1 : 1 ≤ q.length) (hsum3 : 3 ≤ p.length + q.length)
    (hdisj : ∀ w, w ∈ p.support → w ∈ q.support → w = u ∨ w = v) :
    (p.append q.reverse).IsCycle ∧ (p.append q.reverse).length = p.length + q.length := by
  let c : G.Walk u u := p.append q.reverse
  have hlen : c.length = p.length + q.length := by
    simp [c, Walk.length_append, Walk.length_reverse]
  have hqr_len : 1 ≤ q.reverse.length := by rw [Walk.length_reverse]; exact hq1
  have hqr_path : q.reverse.IsPath := hq.reverse
  refine ⟨?_, hlen⟩
  rw [Walk.isCycle_def]
  refine ⟨?_, ?_, ?_⟩
  · rw [Walk.isTrail_def]
    simp only [Walk.edges_append]
    rw [List.nodup_append]
    refine ⟨hp.isTrail.edges_nodup, hqr_path.isTrail.edges_nodup, ?_⟩
    intro e he1 e' he2 heq
    subst heq
    have he2q : e ∈ q.edges := by simpa [Walk.edges_reverse] using he2
    refine Sym2.ind (fun x y => ?_) e he1 he2q
    intro hxy1 hxy2
    have hx_p : x ∈ p.support := mem_support_of_edge p hxy1 (by simp)
    have hy_p : y ∈ p.support := mem_support_of_edge p hxy1 (by simp)
    have hx_q : x ∈ q.support := mem_support_of_edge q hxy2 (by simp)
    have hy_q : y ∈ q.support := mem_support_of_edge q hxy2 (by simp)
    have hxy_ne : x ≠ y := G.ne_of_adj (walk_adj_of_mem_edges p hxy1)
    have hxe : x = u ∨ x = v := hdisj x hx_p hx_q
    have hye : y = u ∨ y = v := hdisj y hy_p hy_q
    have hsuv_p : s(u, v) ∈ p.edges := by
      rcases hxe with rfl | rfl <;> rcases hye with rfl | rfl
      · exact False.elim (hxy_ne rfl)
      · exact hxy1
      · rwa [Sym2.eq_swap] at hxy1
      · exact False.elim (hxy_ne rfl)
    have hsuv_q : s(u, v) ∈ q.edges := by
      rcases hxe with rfl | rfl <;> rcases hye with rfl | rfl
      · exact False.elim (hxy_ne rfl)
      · exact hxy2
      · rwa [Sym2.eq_swap] at hxy2
      · exact False.elim (hxy_ne rfl)
    have hp_one := isPath_mem_edges_endpoints_length_one p hp hsuv_p
    have hq_one := isPath_mem_edges_endpoints_length_one q hq hsuv_q
    omega
  · intro hnil
    have h0 : (p.append q.reverse).length = 0 := by rw [hnil]; rfl
    rw [Walk.length_append, Walk.length_reverse] at h0
    omega
  · have hsupp : c.support = p.support ++ q.reverse.support.tail := Walk.support_append p q.reverse
    have htail : c.support.tail = p.support.tail ++ q.reverse.support.tail := by
      rw [hsupp]
      cases p with
      | nil => simp at hp1
      | cons _ _ => simp [Walk.support_cons]
    rw [htail, List.nodup_append]
    have hp_tail_nd : p.support.tail.Nodup := by
      cases p with
      | nil => simp at hp1
      | cons _ _ => exact (List.nodup_cons.mp hp.support_nodup).2
    have hqr_tail_nd : q.reverse.support.tail.Nodup := by
      cases hqr : q.reverse with
      | nil => rw [hqr] at hqr_len; simp at hqr_len
      | cons _ _ =>
        have hnd := hqr_path.support_nodup
        rw [hqr] at hnd
        exact (List.nodup_cons.mp hnd).2
    refine ⟨hp_tail_nd, hqr_tail_nd, ?_⟩
    intro w hw1 w' hw2 heq
    subst heq
    have hw_p : w ∈ p.support := by
      cases p with
      | nil => simp at hp1
      | cons _ _ => exact List.mem_cons_of_mem _ hw1
    have hw_qr : w ∈ q.reverse.support := by
      cases hqr : q.reverse with
      | nil => rw [hqr] at hqr_len; simp at hqr_len
      | cons _ _ => rw [hqr] at hw2; exact List.mem_cons_of_mem _ hw2
    have hw_q : w ∈ q.support := by simpa [Walk.support_reverse] using hw_qr
    rcases hdisj w hw_p hw_q with rfl | rfl
    · cases p with
      | nil => simp at hp1
      | cons _ _ => exact (List.nodup_cons.mp hp.support_nodup).1 hw1
    · cases hqr : q.reverse with
      | nil => rw [hqr] at hqr_len; simp at hqr_len
      | cons _ _ =>
        have hnd := hqr_path.support_nodup
        rw [hqr] at hnd
        rw [hqr] at hw2
        exact (List.nodup_cons.mp hnd).1 hw2

/-- PILLAR 3.1: Theta-Graph `Θ(p, q, r)` Dyadic-Sum Exclusion. -/
theorem powerfree_theta_dyadic_sum_exclusion {V : Type*} {G : SimpleGraph V}
    (hpf : PowerFree G) {u v : V}
    (p q r : G.Walk u v) (hp : p.IsPath) (hq : q.IsPath) (hr : r.IsPath)
    (hp1 : 1 ≤ p.length) (hq1 : 1 ≤ q.length) (hr1 : 1 ≤ r.length)
    (hpq : ∀ w, w ∈ p.support → w ∈ q.support → w = u ∨ w = v)
    (hqr : ∀ w, w ∈ q.support → w ∈ r.support → w = u ∨ w = v)
    (hrp : ∀ w, w ∈ r.support → w ∈ p.support → w = u ∨ w = v) :
    ¬ IsPowerOfTwo (p.length + q.length) ∧
    ¬ IsPowerOfTwo (q.length + r.length) ∧
    ¬ IsPowerOfTwo (r.length + p.length) := by
  have kill : ∀ (a b : G.Walk u v), a.IsPath → b.IsPath → 1 ≤ a.length → 1 ≤ b.length →
      (∀ w, w ∈ a.support → w ∈ b.support → w = u ∨ w = v) →
      ¬ IsPowerOfTwo (a.length + b.length) := by
    intro a b ha hb ha1 hb1 hdisj ⟨k, hk, hlen⟩
    have hge4 : 4 ≤ 2 ^ k := calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    rcases two_internally_disjoint_paths_cycle a b ha hb ha1 hb1 (by omega) hdisj with ⟨hc, hcl⟩
    exact hpf ⟨u, a.append b.reverse, hc, k, hk, hcl.trans hlen⟩
  exact ⟨kill p q hp hq hp1 hq1 hpq, kill q r hq hr hq1 hr1 hqr, kill r p hr hp hr1 hp1 hrp⟩

/-- PILLAR 3.2: F₂ Cycle-Space Same-Scale Path-Overlap Exclusion. -/
theorem powerfree_f2_same_scale_cycle_overlap_exclusion {V : Type*} {G : SimpleGraph V}
    (hpf : PowerFree G) {u v : V} {k : ℕ} (hk : 2 ≤ k)
    (p1 p2 : G.Walk u v) (hp1 : p1.IsPath) (hp2 : p2.IsPath)
    (hlen1 : p1.length = 2 ^ k) (hlen2 : p2.length = 2 ^ k)
    (hdisj : ∀ w, w ∈ p1.support → w ∈ p2.support → w = u ∨ w = v) :
    False := by
  have hge4 : 4 ≤ 2 ^ k := calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  rcases two_internally_disjoint_paths_cycle p1 p2 hp1 hp2 (by omega) (by omega) (by omega) hdisj
    with ⟨hc, hcl⟩
  apply hpf
  refine ⟨u, p1.append p2.reverse, hc, k + 1, by omega, ?_⟩
  rw [hcl, hlen1, hlen2, pow_succ]; omega

/-- PILLAR 3.3: F₂ Chordal-Shortcut Arc Exclusion. -/
theorem powerfree_chord_arc_exclusion {V : Type*} {G : SimpleGraph V}
    (hpf : PowerFree G) {u v : V} (huv : G.Adj u v)
    (a1 a2 : G.Walk u v) (ha1 : a1.IsPath) (ha2 : a2.IsPath)
    (hl1 : 2 ≤ a1.length) (hl2 : 2 ≤ a2.length) :
    ¬ IsPowerOfTwo (a1.length + 1) ∧ ¬ IsPowerOfTwo (a2.length + 1) := by
  let e : G.Walk u v := Walk.cons huv Walk.nil
  have he_path : e.IsPath := Walk.IsPath.mk' (by
    simp only [e, Walk.support_cons, Walk.support_nil, List.nodup_cons, List.mem_singleton,
      List.nodup_nil, and_true]
    exact G.ne_of_adj huv)
  have kill : ∀ (p : G.Walk u v), p.IsPath → 2 ≤ p.length → ¬ IsPowerOfTwo (p.length + 1) := by
    intro p hp hpl ⟨k, hk, hlen⟩
    have hdisj : ∀ w, w ∈ p.support → w ∈ e.support → w = u ∨ w = v := by
      intro w _ hwe
      simpa [e] using hwe
    rcases two_internally_disjoint_paths_cycle p e hp he_path (by omega) (by simp [e])
        (by simp [e]; omega) hdisj with ⟨hc, hcl⟩
    exact hpf ⟨u, p.append e.reverse, hc, k, hk, by simpa [e] using hcl.trans hlen⟩
  exact ⟨kill a1 ha1 hl1, kill a2 ha2 hl2⟩

/-- PILLAR 3.4: Triangle Fermat-Edge Bypass Exclusion. -/
theorem powerfree_triangle_fermat_edge_exclusion {V : Type*} {G : SimpleGraph V}
    (hpf : PowerFree G) {u v w : V}
    (huw : G.Adj u w) (hwv : G.Adj w v) (huv_ne : u ≠ v)
    (p : G.Walk u v) (hp : p.IsPath) (hw_not : w ∉ p.support)
    {k : ℕ} (hk : 2 ≤ k) (hplen : p.length = 2 ^ k - 2) :
    False := by
  have hge4 : 4 ≤ 2 ^ k := calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  let q : G.Walk u v := Walk.cons huw (Walk.cons hwv Walk.nil)
  have hq_path : q.IsPath := Walk.IsPath.mk' (by
    simp only [q, Walk.support_cons, Walk.support_nil, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
    exact ⟨⟨G.ne_of_adj huw, huv_ne⟩, G.ne_of_adj hwv⟩)
  have hdisj : ∀ z, z ∈ p.support → z ∈ q.support → z = u ∨ z = v := by
    intro z hzp hzq
    simp only [q, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hzq
    rcases hzq with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact False.elim (hw_not hzp)
    · exact Or.inr rfl
  rcases two_internally_disjoint_paths_cycle p q hp hq_path (by omega) (by simp [q])
      (by simp [q]; omega) hdisj with ⟨hc, hcl⟩
  apply hpf
  refine ⟨u, p.append q.reverse, hc, k, hk, ?_⟩
  rw [hcl, hplen]; simp only [q, Walk.length_cons, Walk.length_nil]; omega

/-- PILLAR 3.5: Triangle `(2^k + 1)`-Cycle Two-Edge Shortcut Exclusion. -/
theorem powerfree_triangle_dyadic_plus_one_two_edge_exclusion {V : Type*} {G : SimpleGraph V}
    (hpf : PowerFree G) {u v : V} (huv : G.Adj u v)
    (p : G.Walk u v) (hp : p.IsPath)
    {k : ℕ} (hk : 2 ≤ k) (hplen : p.length = 2 ^ k - 1) :
    False := by
  have hge4 : 4 ≤ 2 ^ k := calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hnot := (powerfree_chord_arc_exclusion hpf huv p p hp hp (by omega) (by omega)).1
  exact hnot ⟨k, hk, by omega⟩

/-- PILLAR 3.6: F₂ Cycle-Space Dimension Lower Bound on `MinimalBad2`. -/
theorem minimal_bad2_f2_cycle_space_dim_lower_bound {V : Type} [Fintype V]
    {G : SimpleGraph V} (hG : MinimalBad2 G) :
    3 * Fintype.card V ≤ 2 * G.edgeFinset.card + 2 := by
  have hhand := SimpleGraph.sum_degrees_eq_twice_card_edges G
  have hsplit : ∑ v : V, G.degree v =
      (∑ v ∈ Defects G, G.degree v) + (∑ v ∈ (Defects G)ᶜ, G.degree v) := by
    rw [Finset.sum_add_sum_compl]
  have hdef_sum : 2 * (Defects G).card ≤ ∑ v ∈ Defects G, G.degree v := by
    calc 2 * (Defects G).card = ∑ _v ∈ Defects G, 2 := by simp
      _ ≤ ∑ v ∈ Defects G, G.degree v :=
          Finset.sum_le_sum (fun v hv => by have := (Finset.mem_filter.mp hv).2; omega)
  have hrest_sum : 3 * (Defects G)ᶜ.card ≤ ∑ v ∈ (Defects G)ᶜ, G.degree v := by
    calc 3 * (Defects G)ᶜ.card = ∑ _v ∈ (Defects G)ᶜ, 3 := by simp
      _ ≤ ∑ v ∈ (Defects G)ᶜ, G.degree v := Finset.sum_le_sum (fun v hv => by
          have h2 := hG.1.2.1 v
          have hne2 : G.degree v ≠ 2 := fun h =>
            (Finset.mem_compl.mp hv) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
          omega)
  have hcard : (Defects G).card + (Defects G)ᶜ.card = Fintype.card V :=
    Finset.card_add_card_compl (Defects G)
  have hdef_le2 : (Defects G).card ≤ 2 := hG.1.2.2
  omega

end E64Wave7Agent3P3
