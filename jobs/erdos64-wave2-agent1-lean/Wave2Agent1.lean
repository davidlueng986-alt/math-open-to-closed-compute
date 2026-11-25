import Leaves
import ClosedDefectCore

/-!
Erdős Problem #64 (Wave 2 — Agent #1):
Lean 4.36.0 formalization of new and core structural theorems on `MinimalBad(G)`:
1. `high_degree_independent`: V_{>=4} is an independent set in every MinimalBad(G).
2. `no_all_high_neighbors`: No vertex has all neighbors of degree >= 4 (so every v in V_3 has <= 2 neighbors in V_{>=4}).
3. `defect_neighbor_at_most_one_high_neighbor`: (NEW Wave 2) Every neighbor of the degree-2 defect w has <= 1 neighbor in V_{>=4}.
4. `no_c4_of_power_free`: No two distinct vertices share two distinct common neighbors when ¬HasPower G.
5. `identify_pair_dyadic_path`: Master vertex-identification dyadic-path theorem.
6. `dist_ge3_dyadic_path`: Universal Dyadic Path Theorem for all MinimalBad(G) (dist >= 3).
7. `cubic_all_pairs_dyadic_path`: (NEW Wave 2) Universal All-Pairs Dyadic Path Theorem for every cubic MinimalBad(G) (dist = 1, 2, >= 3).
8. `cubic_every_edge_on_dyadic_plus_one_cycle`: (NEW Wave 2) Every edge of cubic MinimalBad(G) lies on a (2^k + 1)-cycle.
9. `tri_free_edge_on_dyadic_plus_one_cycle`: (NEW Wave 2) Every triangle-free edge of ANY MinimalBad(G) (C, S, H) lies on a (2^k + 1)-cycle.
-/

namespace E64Wave2Agent1
open SimpleGraph Erdos64Closure E64Core E64Leaves E64DefectCore
universe u

/-! ### Part 1: Class H High-Degree & Defect-Neighborhood Structure -/

/-- In any MinimalBad graph, no two vertices of degree >= 4 are adjacent. -/
theorem high_degree_independent {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {u v : V} (hu : 4 ≤ G.degree u) (hv : 4 ≤ G.degree v) :
    ¬G.Adj u v := by
  classical
  intro huv
  obtain ⟨_, r, hr⟩ := hm.1
  let H := G \ SimpleGraph.edge u v
  let _ : DecidableRel H.Adj := inferInstanceAs (DecidableRel (G \ SimpleGraph.edge u v).Adj)
  have hcard : 2 ≤ Fintype.card V := by
    have := G.degree_lt_card_verts u
    omega
  have hn : Near H := by
    apply near_of_except H r hcard
    intro x hxr
    have hd := erase_edge_degree G u v huv x
    change H.degree x + (if x = u ∨ x = v then 1 else 0) = G.degree x at hd
    by_cases hxu : x = u
    · subst x
      simp only [true_or, ite_true] at hd
      omega
    · by_cases hxv : x = v
      · subst x
        simp only [or_true, ite_true] at hd
        omega
      · simp only [hxu, hxv, or_self, ite_false, add_zero] at hd
        rw [hd]
        exact hr x hxr
  have hEq : H = G := hm.2.2.2 H sdiff_le hn
  have he : H.Adj u v := hEq ▸ huv
  have hno : ¬H.Adj u v := by
    intro h
    have hs := (SimpleGraph.sdiff_adj G (SimpleGraph.edge u v) u v).mp h
    exact hs.2 ((SimpleGraph.edge_adj u v u v).mpr ⟨Or.inl ⟨rfl, rfl⟩, G.ne_of_adj huv⟩)
  exact hno he

/-- In any MinimalBad graph, no vertex can have all its neighbors of degree >= 4.
    In particular, every cubic vertex has at most 2 neighbors in V_{>=4}. -/
theorem no_all_high_neighbors {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (v : V) (hall : ∀ u, G.Adj v u → 4 ≤ G.degree u) : False := by
  classical
  obtain ⟨⟨a, ha⟩, r, hr⟩ := hm.1
  let W := {x : V // x ≠ v}
  let H := G.induce {x | x ≠ v}
  let _ : DecidableRel H.Adj := inferInstanceAs (DecidableRel (G.induce {x | x ≠ v}).Adj)
  have hV : 4 ≤ Fintype.card V := by
    have := G.degree_lt_card_verts a
    omega
  have hW : Fintype.card W + 1 = Fintype.card V := by
    rw [Fintype.card_subtype,
      show (Finset.univ.filter (fun x : V => x ≠ v)) = Finset.univ.erase v by ext x; simp]
    exact Finset.card_erase_add_one (Finset.mem_univ v)
  have hW2 : 2 ≤ Fintype.card ↑({x : V | x ≠ v} : Set V) := by
    have he : Fintype.card ↑({x : V | x ≠ v} : Set V) = Fintype.card W :=
      Fintype.card_congr (Equiv.refl _)
    omega
  have hdegW (x : W) (hxr : x.val ≠ r) : 3 ≤ H.degree x := by
    have hd := induce_delete_degree G v x
    change H.degree x + (if G.Adj x.val v then 1 else 0) = G.degree x.val at hd
    by_cases hxv : G.Adj x.val v
    · rw [ite_eq_left hxv] at hd
      have h4 := hall x.val hxv.symm
      omega
    · rw [ite_eq_right hxv, add_zero] at hd
      have h3 := hr x.val hxr
      omega
  have hnear : Near H := by
    by_cases hrv : r = v
    · subst hrv
      have hne : Nonempty W := by
        have hpos : 0 < Fintype.card W := by omega
        exact Fintype.card_pos_iff.mp hpos
      obtain ⟨w0⟩ := hne
      apply near_of_except H w0 hW2
      intro x _
      exact hdegW x x.property
    · apply near_of_except H ⟨r, hrv⟩ hW2
      intro x hxr
      exact hdegW x (fun h => hxr (Subtype.ext h))
  have hpow : HasPower H := hm.2.2.1 W H (by omega) hnear
  exact hm.2.1 (power_induce G _ hpow)

/-- NEW Wave 2 Theorem: In any MinimalBad graph with degree-2 defect w,
    every neighbor b of w has at most one neighbor of degree >= 4. -/
theorem defect_neighbor_at_most_one_high_neighbor {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {w b x1 x2 : V} (hw : G.degree w = 2) (hwb : G.Adj w b)
    (hx1 : G.Adj b x1) (hx2 : G.Adj b x2)
    (h1w : x1 ≠ w) (h2w : x2 ≠ w) (h12 : x1 ≠ x2) :
    ¬(4 ≤ G.degree x1 ∧ 4 ≤ G.degree x2) := by
  classical
  rintro ⟨hd1, hd2⟩
  obtain ⟨_, r, hr⟩ := hm.1
  have hrw : r = w := by
    by_contra hne
    have := hr w (Ne.symm hne)
    omega
  subst r
  have hb3 : G.degree b = 3 := defect_neighbor_cubic G hm hw hwb
  have hbw : b ≠ w := (G.ne_of_adj hwb).symm
  have hncard : (G.neighborFinset w).card = 2 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, hw]
  obtain ⟨u1, u2, hu12, hNw⟩ := Finset.card_eq_two.mp hncard
  have hmem_b : b ∈ ({u1, u2} : Finset V) := by
    rw [← hNw, G.mem_neighborFinset]
    exact hwb
  have hex_b' : ∃ b' : V, b' ≠ b ∧ G.Adj w b' ∧ ∀ z, G.Adj w z → z = b ∨ z = b' := by
    rcases Finset.mem_insert.mp hmem_b with rfl | hmem2
    · refine ⟨u2, hu12.symm, ?_, ?_⟩
      · exact (G.mem_neighborFinset w u2).mp (hNw ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self u2))
      · intro z hz
        have hzm : z ∈ ({b, u2} : Finset V) := hNw ▸ (G.mem_neighborFinset w z).mpr hz
        simpa using hzm
    · have hu2b : b = u2 := Finset.mem_singleton.mp hmem2
      subst hu2b
      refine ⟨u1, hu12, ?_, ?_⟩
      · exact (G.mem_neighborFinset w u1).mp (hNw ▸ Finset.mem_insert_self u1 {b})
      · intro z hz
        have hzm : z ∈ ({u1, b} : Finset V) := hNw ▸ (G.mem_neighborFinset w z).mpr hz
        rcases Finset.mem_insert.mp hzm with rfl | h2
        · exact Or.inr rfl
        · exact Or.inl (Finset.mem_singleton.mp h2)
  obtain ⟨b', hb'b, hwb', hw_all⟩ := hex_b'
  have hb'w : b' ≠ w := (G.ne_of_adj hwb').symm
  have hNb : G.neighborFinset b = {w, x1, x2} := by
    apply (Finset.eq_of_subset_of_card_le (s := ({w, x1, x2} : Finset V)) (t := G.neighborFinset b) ?_ ?_).symm
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rw [G.mem_neighborFinset]
      rcases hz with rfl | rfl | rfl
      · exact hwb.symm
      · exact hx1
      · exact hx2
    · rw [SimpleGraph.card_neighborFinset_eq_degree, hb3]
      have hnot1 : x1 ∉ ({x2} : Finset V) := by
        intro h; exact h12 (Finset.mem_singleton.mp h)
      have hnot2 : w ∉ ({x1, x2} : Finset V) := by
        intro h
        rcases Finset.mem_insert.mp h with h1 | h2
        · exact h1w h1.symm
        · exact h2w (Finset.mem_singleton.mp h2).symm
      rw [Finset.card_insert_of_notMem hnot2, Finset.card_insert_of_notMem hnot1, Finset.card_singleton]
  let S : Set V := {z | z ≠ w ∧ z ≠ b}
  let W := {z : V // z ≠ w ∧ z ≠ b}
  let H := G.induce S
  let _ : DecidableRel H.Adj := inferInstanceAs (DecidableRel (G.induce S).Adj)
  have hV : 5 ≤ Fintype.card V := by
    have := G.degree_lt_card_verts x1
    omega
  have hW : Fintype.card W + 2 = Fintype.card V := by
    rw [Fintype.card_subtype]
    have hfilt : (Finset.univ.filter (fun z : V => z ≠ w ∧ z ≠ b)) = (Finset.univ.erase w).erase b := by
      ext z; simp [and_comm]
    rw [hfilt]
    have h1 : ((Finset.univ.erase w).erase b).card + 1 = (Finset.univ.erase w).card :=
      Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨hbw, Finset.mem_univ b⟩)
    have h2 : (Finset.univ.erase w).card + 1 = (Finset.univ : Finset V).card :=
      Finset.card_erase_add_one (Finset.mem_univ w)
    have h3 : (Finset.univ : Finset V).card = Fintype.card V := Finset.card_univ
    omega
  have hS2 : 2 ≤ Fintype.card ↑S := by
    have he : Fintype.card ↑S = Fintype.card W := Fintype.card_congr (Equiv.refl _)
    omega
  have hnear : Near H := by
    apply near_of_except H ⟨b', hb'w, hb'b⟩ hS2
    intro z hzb'
    have hz_neb' : z.val ≠ b' := fun h => hzb' (Subtype.ext h)
    have hznw : ¬G.Adj z.val w := by
      intro hzw
      rcases hw_all z.val hzw.symm with h | h
      · exact z.property.2 h
      · exact hz_neb' h
    let e : H.neighborSet z ≃ {y : V // G.Adj z.val y ∧ y ≠ w ∧ y ≠ b} :=
      { toFun := fun y => ⟨y.1.1, y.2, y.1.2.1, y.1.2.2⟩
        invFun := fun y => ⟨⟨y.1, y.2.2.1, y.2.2.2⟩, y.2.1⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hc := Fintype.card_congr e
    rw [SimpleGraph.card_neighborSet_eq_degree, Fintype.card_subtype] at hc
    have hfilt : (Finset.univ.filter (fun y : V => G.Adj z.val y ∧ y ≠ w ∧ y ≠ b)) =
        (G.neighborFinset z.val).erase b := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
        G.mem_neighborFinset]
      constructor
      · rintro ⟨hy1, _, hyb⟩; exact ⟨hyb, hy1⟩
      · rintro ⟨hyb, hy1⟩
        refine ⟨hy1, ?_, hyb⟩
        rintro rfl
        exact hznw hy1
    rw [hfilt] at hc
    by_cases hzb : G.Adj z.val b
    · have hzmem : z.val ∈ G.neighborFinset b := (G.mem_neighborFinset b z.val).mpr hzb.symm
      rw [hNb] at hzmem
      have h4 : 4 ≤ G.degree z.val := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hzmem
        rcases hzmem with hzw | hzx1 | hzx2
        · exact absurd hzw z.property.1
        · rw [hzx1]; exact hd1
        · rw [hzx2]; exact hd2
      have hce := Finset.card_erase_add_one ((G.mem_neighborFinset z.val b).mpr hzb)
      rw [SimpleGraph.card_neighborFinset_eq_degree] at hce
      omega
    · have hce : ((G.neighborFinset z.val).erase b).card = (G.neighborFinset z.val).card :=
        congrArg Finset.card (Finset.erase_eq_of_notMem (fun hm => hzb ((G.mem_neighborFinset z.val b).mp hm)))
      rw [SimpleGraph.card_neighborFinset_eq_degree] at hce
      have h3 := hr z.val z.property.1
      omega
  have hpow : HasPower H := hm.2.2.1 W H (by omega) hnear
  exact hm.2.1 (power_induce G S hpow)

/-! ### Part 2: C4-Freeness and Master Vertex-Identification Dyadic Path Theorem -/

/-- Helper: closing a simple path `p : G.Walk u a` of length ≥ 2 with edge `G.Adj a u`
    produces a simple cycle `Walk.cons h1 p : G.Walk a a`. -/
theorem cons_path_isCycle {V : Type u} {G : SimpleGraph V} {a u : V}
    (h1 : G.Adj a u) (p : G.Walk u a) (hp : p.IsPath) (hlen : 2 ≤ p.length) :
    (Walk.cons h1 p).IsCycle := by
  rw [Walk.isCycle_def]
  refine ⟨?_, ?_, ?_⟩
  · rw [Walk.isTrail_def, Walk.edges_cons, List.nodup_cons]
    refine ⟨?_, hp.isTrail.edges_nodup⟩
    cases hp_eq : p with
    | nil => rw [hp_eq] at hlen; simp at hlen
    | @cons _ b _ h2 rest =>
      rw [Walk.edges_cons, List.mem_cons]
      rintro (heq | hmem)
      · have hba : b = a := by
          rw [Sym2.eq_iff] at heq
          rcases heq with ⟨h_au, _⟩ | ⟨h_ab, _⟩
          · exact absurd h_au (G.ne_of_adj h1)
          · exact h_ab.symm
        subst b
        have hnod := hp.support_nodup
        rw [hp_eq, Walk.support_cons, List.nodup_cons] at hnod
        cases hrest_eq : rest with
        | nil => rw [hp_eq, hrest_eq] at hlen; simp at hlen
        | @cons _ c _ hc rest2 =>
          have hmem_end : a ∈ rest2.support := Walk.end_mem_support rest2
          have hnod_r := hnod.2
          rw [hrest_eq, Walk.support_cons, List.nodup_cons] at hnod_r
          exact hnod_r.1 hmem_end
      · have hu_mem : u ∈ rest.support := Walk.snd_mem_support_of_mem_edges rest hmem
        have hnod := hp.support_nodup
        rw [hp_eq, Walk.support_cons, List.nodup_cons] at hnod
        exact hnod.1 hu_mem
  · simp
  · simpa [Walk.support_cons] using hp.support_nodup

/-- In any power-free graph, no two distinct vertices have two distinct common neighbors. -/
theorem no_c4_of_power_free {V : Type u} (G : SimpleGraph V) (hf : ¬HasPower G)
    {x y c1 c2 : V} (hxy : x ≠ y) (hc12 : c1 ≠ c2)
    (hx1 : G.Adj x c1) (hy1 : G.Adj y c1) (hx2 : G.Adj x c2) (hy2 : G.Adj y c2) :
    False := by
  have hxc1 : x ≠ c1 := G.ne_of_adj hx1
  have hyc1 : y ≠ c1 := G.ne_of_adj hy1
  have hxc2 : x ≠ c2 := G.ne_of_adj hx2
  have hyc2 : y ≠ c2 := G.ne_of_adj hy2
  let p : G.Walk c1 x :=
    Walk.cons hy1.symm (Walk.cons hy2 (Walk.cons hx2.symm Walk.nil))
  have hp : p.IsPath := by
    rw [Walk.isPath_def]
    simp [p, hyc1.symm, hc12, hxc1.symm, hyc2, hxy.symm, hxc2.symm]
  have hcyc : (Walk.cons hx1 p).IsCycle := cons_path_isCycle hx1 p hp (by simp [p])
  exact hf ⟨2, x, Walk.cons hx1 p, le_rfl, hcyc, rfl⟩

/-- Merged graph G/(x=y) realized directly on the subtype W = {v : V // v ≠ y},
    where z = ⟨x, hxy⟩ represents the identified pair {x, y}. -/
def mergeGraph {V : Type u} (G : SimpleGraph V) (x y : V) (_hxy : x ≠ y) :
    SimpleGraph {v : V // v ≠ y} where
  Adj u v :=
    u ≠ v ∧
      ((u.val = x ∧ (G.Adj x v.val ∨ G.Adj y v.val)) ∨
       (v.val = x ∧ (G.Adj x u.val ∨ G.Adj y u.val)) ∨
       (u.val ≠ x ∧ v.val ≠ x ∧ G.Adj u.val v.val))
  symm := ⟨fun _ _ ⟨hne, hadj⟩ =>
    ⟨hne.symm, match hadj with
      | Or.inl h1 => Or.inr (Or.inl h1)
      | Or.inr (Or.inl h2) => Or.inl h2
      | Or.inr (Or.inr ⟨hux, hvx, huv⟩) => Or.inr (Or.inr ⟨hvx, hux, huv.symm⟩)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Lift a walk in `mergeGraph G x y hxy` whose support avoids `⟨x, hxy⟩`
    directly to a walk in `G \ edge x y` with identical support values, edges, and length. -/
def liftAvoidWalk {V : Type u} {G : SimpleGraph V} {x y : V} {hxy : x ≠ y}
    {u v : {w : V // w ≠ y}} :
    ∀ (p : (mergeGraph G x y hxy).Walk u v),
      (⟨x, hxy⟩ : {w : V // w ≠ y}) ∉ p.support →
      { q : (G \ SimpleGraph.edge x y).Walk u.val v.val //
          q.length = p.length ∧
          q.support = p.support.map Subtype.val ∧
          q.edges = p.edges.map (Sym2.map Subtype.val) }
  | Walk.nil, _ => ⟨Walk.nil, rfl, rfl, rfl⟩
  | Walk.cons (u := a) (v := b) hab rest, hnot =>
    let ha : a.val ≠ x := fun h => hnot (by
      have ha_eq : a = ⟨x, hxy⟩ := Subtype.ext h
      rw [Walk.support_cons, ha_eq]
      exact List.mem_cons_self)
    let hb : b.val ≠ x := fun h => hnot (by
      have hb_eq : b = ⟨x, hxy⟩ := Subtype.ext h
      rw [Walk.support_cons, ← hb_eq]
      exact List.mem_cons_of_mem _ (Walk.start_mem_support rest))
    let hrest : (⟨x, hxy⟩ : {w : V // w ≠ y}) ∉ rest.support := fun hm =>
      hnot (by rw [Walk.support_cons]; exact List.mem_cons_of_mem _ hm)
    let hadjG : G.Adj a.val b.val := by
      rcases hab.2 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h⟩
      · exact absurd h ha
      · exact absurd h hb
      · exact h
    let hadjDiff : (G \ SimpleGraph.edge x y).Adj a.val b.val := by
      rw [SimpleGraph.sdiff_adj]
      refine ⟨hadjG, ?_⟩
      rw [SimpleGraph.edge_adj]
      rintro ⟨⟨h1, _⟩ | ⟨h1, _⟩, _⟩
      · exact ha h1
      · exact a.property h1
    let ⟨q, hlen, hsup, hedg⟩ := liftAvoidWalk rest hrest
    ⟨Walk.cons hadjDiff q, by simp [hlen], by simp [hsup], by simp [hedg]⟩

/-- Helper: lift a closed cycle in `mergeGraph` avoiding `z = ⟨x, hxy⟩` to a cycle in `G`. -/
theorem power_of_avoid_cycle {V : Type u} {G : SimpleGraph V} {x y : V} {hxy : x ≠ y}
    {k : ℕ} {v : {w : V // w ≠ y}} {c : (mergeGraph G x y hxy).Walk v v}
    (hk : 2 ≤ k) (hc : c.IsCycle) (hl : c.length = 2 ^ k)
    (hnot : (⟨x, hxy⟩ : {w : V // w ≠ y}) ∉ c.support) :
    HasPower G := by
  obtain ⟨q, hlen, hsup, hedg⟩ := liftAvoidWalk c hnot
  have htail_map : ∀ (l : List {w : V // w ≠ y}), (l.map Subtype.val).tail = l.tail.map Subtype.val := by
    intro l; cases l <;> rfl
  have hcyc_diff : q.IsCycle := by
    rw [Walk.isCycle_def]
    refine ⟨?_, ?_, ?_⟩
    · rw [Walk.isTrail_def, hedg]
      exact hc.edges_nodup.map (Sym2.map.injective Subtype.val_injective)
    · intro hnil
      subst hnil
      have h4 : 4 ≤ 2 ^ k := by
        have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hk
        simpa using this
      simp at hlen
      omega
    · rw [hsup, htail_map]
      exact hc.support_nodup.map Subtype.val_injective
  exact power_mono sdiff_le ⟨k, v.val, q, hk, hcyc_diff, hlen.trans hl⟩

/-- Helper: close a simple path `mid` in `G` (avoiding `a`) with two edges to `a`
    to get a simple cycle of length `mid.length + 2` in `G`. -/
theorem cycle_from_mid_and_vertex {V : Type u} {G : SimpleGraph V}
    {a u1 u2 : V} (mid : G.Walk u1 u2)
    (hpath : mid.IsPath) (ha : a ∉ mid.support)
    (h1 : G.Adj a u1) (h2 : G.Adj a u2) (hlen : 1 ≤ mid.length) :
    ∃ c : G.Walk a a, c.IsCycle ∧ c.length = mid.length + 2 := by
  let p : G.Walk u1 a := mid.concat h2.symm
  have hp : p.IsPath := by
    rw [Walk.isPath_def]
    have hsup : p.support = mid.support ++ [a] := by simp [p, Walk.support_concat]
    rw [hsup, List.nodup_append]
    refine ⟨hpath.support_nodup, List.nodup_singleton a, ?_⟩
    intro z hz1 w hw2
    rw [List.mem_singleton] at hw2
    subst hw2
    intro heq
    subst heq
    exact ha hz1
  have hplen : p.length = mid.length + 1 := by simp [p, Walk.length_concat]
  exact ⟨Walk.cons h1 p, cons_path_isCycle h1 p hp (by omega), by simp [hplen]⟩

/-- Master Vertex-Identification Dyadic Path Theorem:
    In any `MinimalBad G`, if identifying distinct `x ≠ y` preserves `Near`,
    then `G \ edge x y` contains a simple `x`–`y` path of length `2^k` (`k ≥ 2`). -/
theorem identify_pair_dyadic_path {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {x y : V} (hxy : x ≠ y)
    (hnear : @Near {v : V // v ≠ y} (mergeGraph G x y hxy) _ (Classical.decRel _)) :
    ∃ (k : ℕ) (p : (G \ SimpleGraph.edge x y).Walk x y),
      2 ≤ k ∧ p.IsPath ∧ p.length = 2 ^ k := by
  classical
  let W := {v : V // v ≠ y}
  let H := mergeGraph G x y hxy
  let _ : DecidableRel H.Adj := Classical.decRel _
  let z : W := ⟨x, hxy⟩
  have hW : Fintype.card W + 1 = Fintype.card V := by
    rw [Fintype.card_subtype,
      show (Finset.univ.filter (fun v : V => v ≠ y)) = Finset.univ.erase y by ext v; simp]
    exact Finset.card_erase_add_one (Finset.mem_univ y)
  obtain ⟨k, v0, c0, hk, hc0, hl0⟩ := hm.2.2.1 W H (by omega) hnear
  have hz_mem : z ∈ c0.support := by
    by_contra hnot
    exact hm.2.1 (power_of_avoid_cycle hk hc0 hl0 hnot)
  let c : H.Walk z z := c0.rotate z hz_mem
  have hc : c.IsCycle := hc0.rotate hz_mem
  have hl : c.length = 2 ^ k := by
    change (c0.rotate z hz_mem).length = 2 ^ k
    rw [Walk.length_rotate]
    exact hl0
  have h4 : 4 ≤ 2 ^ k := by
    have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hk
    simpa using this
  cases hc_eq : c with
  | nil =>
    rw [hc_eq] at hl; simp at hl; omega
  | @cons _ u1 _ h1 rest =>
    have hrest_nodup : rest.support.Nodup := by
      have h := hc.support_nodup
      rw [hc_eq] at h
      simpa using h
    have hrest_len : rest.length = 2 ^ k - 1 := by
      rw [hc_eq] at hl; simp at hl; omega
    cases hrev_eq : rest.reverse with
    | nil =>
      have hlr : rest.reverse.length = rest.length := Walk.length_reverse rest
      rw [hrev_eq] at hlr
      simp at hlr
      omega
    | @cons _ u2 _ h2 mid_rev =>
      let mid : H.Walk u1 u2 := mid_rev.reverse
      have hmid_len : mid.length = 2 ^ k - 2 := by
        have hlen_rev : rest.reverse.length = rest.length := Walk.length_reverse rest
        rw [hrev_eq] at hlen_rev
        simp only [Walk.length_cons] at hlen_rev
        have : mid.length = mid_rev.length := Walk.length_reverse mid_rev
        omega
      have hmid_sup : rest.support = mid.support ++ [z] := by
        have h1s : rest.reverse.support = z :: mid_rev.support := by rw [hrev_eq]; rfl
        have h2s : rest.support = rest.reverse.support.reverse := by
          rw [Walk.support_reverse, List.reverse_reverse]
        rw [h2s, h1s, List.reverse_cons]
        simp [mid, Walk.support_reverse]
      have hmid_nodup : mid.support.Nodup := by
        rw [hmid_sup, List.nodup_append] at hrest_nodup
        exact hrest_nodup.1
      have hz_not_mid : z ∉ mid.support := by
        rw [hmid_sup, List.nodup_append] at hrest_nodup
        intro hm_z
        exact hrest_nodup.2.2 z hm_z z (List.mem_singleton_self z) rfl
      obtain ⟨midD, hmidD_len, hmidD_sup, _⟩ := liftAvoidWalk mid hz_not_mid
      have hmidD_path : midD.IsPath := by
        rw [Walk.isPath_def, hmidD_sup]
        exact hmid_nodup.map Subtype.val_injective
      have hx_not_midD : x ∉ midD.support := by
        rw [hmidD_sup, List.mem_map]
        rintro ⟨w, hw, hwx⟩
        have hwz : w = z := Subtype.ext hwx
        exact hz_not_mid (hwz ▸ hw)
      have hy_not_midD : y ∉ midD.support := by
        rw [hmidD_sup, List.mem_map]
        rintro ⟨w, _, hwy⟩
        exact w.property hwy
      have h1_or : G.Adj x u1.val ∨ G.Adj y u1.val := by
        rcases h1.2 with ⟨_, h⟩ | ⟨hu1x, _⟩ | ⟨hzx, _, _⟩
        · exact h
        · exact absurd (Subtype.ext hu1x.symm) h1.1
        · exact absurd rfl hzx
      have h2_or : G.Adj x u2.val ∨ G.Adj y u2.val := by
        rcases h2.2 with ⟨_, h⟩ | ⟨hu2x, _⟩ | ⟨hzx, _, _⟩
        · exact h
        · exact absurd (Subtype.ext hu2x.symm) h2.1
        · exact absurd rfl hzx
      let midG : G.Walk u1.val u2.val := midD.mapLe sdiff_le
      have hmidG_path : midG.IsPath := (Walk.isPath_mapLe sdiff_le).mpr hmidD_path
      have hmidG_sup : midG.support = midD.support := by simp [midG]
      have hmidG_len : midG.length = 2 ^ k - 2 := by simp [midG, hmidD_len, hmid_len]
      have hnot_both_x : ¬(G.Adj x u1.val ∧ G.Adj x u2.val) := by
        rintro ⟨hx1, hx2⟩
        obtain ⟨cG, hcG, hlG⟩ := cycle_from_mid_and_vertex midG hmidG_path
          (hmidG_sup ▸ hx_not_midD) hx1 hx2 (by omega)
        exact hm.2.1 ⟨k, x, cG, hk, hcG, by omega⟩
      have hnot_both_y : ¬(G.Adj y u1.val ∧ G.Adj y u2.val) := by
        rintro ⟨hy1, hy2⟩
        obtain ⟨cG, hcG, hlG⟩ := cycle_from_mid_and_vertex midG hmidG_path
          (hmidG_sup ▸ hy_not_midD) hy1 hy2 (by omega)
        exact hm.2.1 ⟨k, y, cG, hk, hcG, by omega⟩
      have mkDiffX : ∀ (w : W), w.val ≠ x → G.Adj x w.val → (G \ SimpleGraph.edge x y).Adj x w.val := by
        intro w _ hadj
        rw [SimpleGraph.sdiff_adj]
        refine ⟨hadj, ?_⟩
        rw [SimpleGraph.edge_adj]
        rintro ⟨⟨_, h2⟩ | ⟨h1, _⟩, _⟩
        · exact w.property h2
        · exact hxy h1
      have mkDiffY : ∀ (w : W), w.val ≠ x → G.Adj y w.val → (G \ SimpleGraph.edge x y).Adj w.val y := by
        intro w hwx hadj
        rw [SimpleGraph.sdiff_adj]
        refine ⟨hadj.symm, ?_⟩
        rw [SimpleGraph.edge_adj]
        rintro ⟨⟨h1, _⟩ | ⟨h1, _⟩, _⟩
        · exact hwx h1
        · exact w.property h1
      have hu1_nx : u1.val ≠ x := fun h => h1.1 (Subtype.ext h.symm)
      have hu2_nx : u2.val ≠ x := fun h => h2.1 (Subtype.ext h.symm)
      rcases h1_or with hx1 | hy1
      · rcases h2_or with hx2 | hy2
        · exact absurd ⟨hx1, hx2⟩ hnot_both_x
        · let p : (G \ SimpleGraph.edge x y).Walk x y :=
            Walk.cons (mkDiffX u1 hu1_nx hx1) (midD.concat (mkDiffY u2 hu2_nx hy2))
          have hp_path : p.IsPath := by
            rw [Walk.isPath_def]
            have hps : p.support = x :: (midD.support ++ [y]) := by
              simp [p, Walk.support_concat]
            rw [hps, List.nodup_cons]
            refine ⟨?_, ?_⟩
            · simp [hx_not_midD, hxy]
            · rw [List.nodup_append]
              refine ⟨hmidD_path.support_nodup, List.nodup_singleton y, ?_⟩
              intro a ha1 b hb2
              rw [List.mem_singleton] at hb2
              subst hb2
              intro heq; subst heq
              exact hy_not_midD ha1
          refine ⟨k, p, hk, hp_path, ?_⟩
          simp [p, Walk.length_concat, hmidD_len, hmid_len]
          omega
      · rcases h2_or with hx2 | hy2
        · let p0 : (G \ SimpleGraph.edge x y).Walk y x :=
            Walk.cons (mkDiffY u1 hu1_nx hy1).symm (midD.concat (mkDiffX u2 hu2_nx hx2).symm)
          let p : (G \ SimpleGraph.edge x y).Walk x y := p0.reverse
          have hp0_path : p0.IsPath := by
            rw [Walk.isPath_def]
            have hps : p0.support = y :: (midD.support ++ [x]) := by
              simp [p0, Walk.support_concat]
            rw [hps, List.nodup_cons]
            refine ⟨?_, ?_⟩
            · simp [hy_not_midD, hxy.symm]
            · rw [List.nodup_append]
              refine ⟨hmidD_path.support_nodup, List.nodup_singleton x, ?_⟩
              intro a ha1 b hb2
              rw [List.mem_singleton] at hb2
              subst hb2
              intro heq; subst heq
              exact hx_not_midD ha1
          refine ⟨k, p, hk, hp0_path.reverse, ?_⟩
          simp [p, p0, Walk.length_reverse, hmidD_len, hmid_len]
          omega
        · exact absurd ⟨hy1, hy2⟩ hnot_both_y

/-! ### Part 3: Degree Formulas for `mergeGraph` and Unconditional Applications -/

/-- Exact degree of any vertex `u ≠ z` in `mergeGraph G x y hxy`. -/
theorem mergeGraph_degree_ne {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y : V) (hxy : x ≠ y)
    [DecidableRel (mergeGraph G x y hxy).Adj]
    (u : {v : V // v ≠ y}) (hux : u.val ≠ x) :
    (mergeGraph G x y hxy).degree u + (if G.Adj u.val x ∧ G.Adj u.val y then 1 else 0) =
      G.degree u.val := by
  classical
  let H := mergeGraph G x y hxy
  change H.degree u + (if G.Adj u.val x ∧ G.Adj u.val y then 1 else 0) = G.degree u.val
  let S_other := (G.neighborFinset u.val).filter (fun w => w ≠ x ∧ w ≠ y)
  have hH_card : H.degree u = S_other.card + (if G.Adj x u.val ∨ G.Adj y u.val then 1 else 0) := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    let z : {v : V // v ≠ y} := ⟨x, hxy⟩
    have hsplit : H.neighborFinset u =
        (H.neighborFinset u).erase z ∪ (if H.Adj u z then {z} else ∅) := by
      ext w
      by_cases h : H.Adj u z
      · rw [ite_eq_left h]
        simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton,
          H.mem_neighborFinset]
        by_cases hwz : w = z
        · subst hwz; simp [h]
        · simp [hwz]
      · rw [ite_eq_right h]
        simp only [Finset.union_empty, Finset.mem_erase, H.mem_neighborFinset]
        constructor
        · intro hw
          refine ⟨?_, hw⟩
          rintro rfl
          exact h hw
        · exact fun hw => hw.2
    have hdisj : Disjoint ((H.neighborFinset u).erase z) (if H.Adj u z then {z} else ∅) := by
      by_cases h : H.Adj u z
      · rw [ite_eq_left h]; simp
      · rw [ite_eq_right h]; simp
    rw [hsplit, Finset.card_union_of_disjoint hdisj]
    have h1 : ((H.neighborFinset u).erase z).card = S_other.card := by
      apply Finset.card_bij (fun w _ => w.val)
      · intro w hw
        simp only [Finset.mem_erase, H.mem_neighborFinset] at hw
        have hwx : w.val ≠ x := fun he => hw.1 (Subtype.ext he)
        have hadjG : G.Adj u.val w.val := by
          rcases hw.2.2 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h⟩
          · exact absurd h hux
          · exact absurd h hwx
          · exact h
        simp only [S_other, Finset.mem_filter, G.mem_neighborFinset]
        exact ⟨hadjG, hwx, w.property⟩
      · intro w1 _ w2 _ he; exact Subtype.ext he
      · intro w hw
        simp only [S_other, Finset.mem_filter, G.mem_neighborFinset] at hw
        refine ⟨⟨w, hw.2.2⟩, ?_, rfl⟩
        simp only [Finset.mem_erase, H.mem_neighborFinset]
        refine ⟨fun he => hw.2.1 (congrArg Subtype.val he), ?_, Or.inr (Or.inr ⟨hux, hw.2.1, hw.1⟩)⟩
        intro he
        exact G.ne_of_adj hw.1 (congrArg Subtype.val he)
    have h2 : (if H.Adj u z then ({z} : Finset _) else ∅).card =
        if G.Adj x u.val ∨ G.Adj y u.val then 1 else 0 := by
      have heq : H.Adj u z ↔ G.Adj x u.val ∨ G.Adj y u.val := by
        have huz : u ≠ z := fun he => hux (congrArg Subtype.val he)
        constructor
        · intro h
          rcases h.2 with ⟨h1, _⟩ | ⟨_, h2⟩ | ⟨_, h3, _⟩
          · exact absurd h1 hux
          · exact h2
          · exact absurd rfl h3
        · intro h
          exact ⟨huz, Or.inr (Or.inl ⟨rfl, h⟩)⟩
      by_cases h : H.Adj u z
      · rw [ite_eq_left h, ite_eq_left (heq.mp h), Finset.card_singleton]
      · rw [ite_eq_right h, ite_eq_right (mt heq.mpr h), Finset.card_empty]
    rw [h1, h2]
  have hG_card : G.degree u.val =
      S_other.card + (if G.Adj u.val x then 1 else 0) + (if G.Adj u.val y then 1 else 0) := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have hfilt : S_other = ((G.neighborFinset u.val).erase x).erase y := by
      ext w
      simp only [S_other, Finset.mem_filter, Finset.mem_erase, G.mem_neighborFinset]
      tauto
    rw [hfilt]
    by_cases hy : G.Adj u.val y
    · have hym : y ∈ (G.neighborFinset u.val).erase x :=
        Finset.mem_erase.mpr ⟨hxy.symm, (G.mem_neighborFinset u.val y).mpr hy⟩
      have hcy := Finset.card_erase_add_one hym
      rw [ite_eq_left hy]
      by_cases hx : G.Adj u.val x
      · have hxm : x ∈ G.neighborFinset u.val := (G.mem_neighborFinset u.val x).mpr hx
        have hcx := Finset.card_erase_add_one hxm
        rw [ite_eq_left hx]; omega
      · have hcx : ((G.neighborFinset u.val).erase x).card = (G.neighborFinset u.val).card :=
          congrArg Finset.card (Finset.erase_eq_of_notMem (fun hm => hx ((G.mem_neighborFinset u.val x).mp hm)))
        rw [ite_eq_right hx]; omega
    · have hcy : (((G.neighborFinset u.val).erase x).erase y).card = ((G.neighborFinset u.val).erase x).card :=
        congrArg Finset.card (Finset.erase_eq_of_notMem (fun hm =>
          hy ((G.mem_neighborFinset u.val y).mp (Finset.mem_of_mem_erase hm))))
      rw [ite_eq_right hy]
      by_cases hx : G.Adj u.val x
      · have hxm : x ∈ G.neighborFinset u.val := (G.mem_neighborFinset u.val x).mpr hx
        have hcx := Finset.card_erase_add_one hxm
        rw [ite_eq_left hx]; omega
      · have hcx : ((G.neighborFinset u.val).erase x).card = (G.neighborFinset u.val).card :=
          congrArg Finset.card (Finset.erase_eq_of_notMem (fun hm => hx ((G.mem_neighborFinset u.val x).mp hm)))
        rw [ite_eq_right hx]; omega
  rw [hH_card, hG_card]
  by_cases hx : G.Adj u.val x <;> by_cases hy : G.Adj u.val y
  · have hx' : G.Adj x u.val := hx.symm
    have hy' : G.Adj y u.val := hy.symm
    simp [hx, hy, hx', hy']
  · have hx' : G.Adj x u.val := hx.symm
    have hy' : ¬G.Adj y u.val := fun h => hy h.symm
    simp [hx, hy, hx', hy']
  · have hx' : ¬G.Adj x u.val := fun h => hx h.symm
    have hy' : G.Adj y u.val := hy.symm
    simp [hx, hy, hx', hy']
  · have hx' : ¬G.Adj x u.val := fun h => hx h.symm
    have hy' : ¬G.Adj y u.val := fun h => hy h.symm
    simp [hx, hy, hx', hy']

/-- Degree of the merged vertex `z = ⟨x, hxy⟩` in `mergeGraph G x y hxy`. -/
theorem mergeGraph_degree_z {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y : V) (hxy : x ≠ y)
    [DecidableRel (mergeGraph G x y hxy).Adj] :
    (mergeGraph G x y hxy).degree ⟨x, hxy⟩ =
      (((G.neighborFinset x).erase y) ∪ ((G.neighborFinset y).erase x)).card := by
  classical
  let H := mergeGraph G x y hxy
  change H.degree ⟨x, hxy⟩ = _
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun w _ => w.val)
  · intro w hw
    rw [H.mem_neighborFinset] at hw
    have hwx : w.val ≠ x := fun he => hw.1 (Subtype.ext he.symm)
    have hor : G.Adj x w.val ∨ G.Adj y w.val := by
      rcases hw.2 with ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _, _⟩
      · exact h
      · exact absurd h hwx
      · exact absurd rfl h
    simp only [Finset.mem_union, Finset.mem_erase, G.mem_neighborFinset]
    rcases hor with h | h
    · exact Or.inl ⟨w.property, h⟩
    · exact Or.inr ⟨hwx, h⟩
  · intro w1 _ w2 _ he; exact Subtype.ext he
  · intro w hw
    simp only [Finset.mem_union, Finset.mem_erase, G.mem_neighborFinset] at hw
    have hwy : w ≠ y := by
      rcases hw with ⟨h, _⟩ | ⟨_, h⟩
      · exact h
      · exact (G.ne_of_adj h).symm
    have hwx : w ≠ x := by
      rcases hw with ⟨_, h⟩ | ⟨h, _⟩
      · exact (G.ne_of_adj h).symm
      · exact h
    refine ⟨⟨w, hwy⟩, ?_, rfl⟩
    rw [H.mem_neighborFinset]
    refine ⟨fun he => hwx (congrArg Subtype.val he).symm, Or.inl ⟨rfl, ?_⟩⟩
    rcases hw with ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inr h

/-- Wave 1 Universal Dyadic Path Theorem (dist >= 3) — First Lean 4.36.0 Verification!
    Applies to EVERY MinimalBad graph (C, S, or H). -/
theorem dist_ge3_dyadic_path {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {x y : V} (hxy : x ≠ y) (hnadj : ¬G.Adj x y)
    (hdisj : ∀ c, ¬(G.Adj x c ∧ G.Adj y c)) :
    ∃ (k : ℕ) (p : G.Walk x y), 2 ≤ k ∧ p.IsPath ∧ p.length = 2 ^ k := by
  classical
  let W := {v : V // v ≠ y}
  let H := mergeGraph G x y hxy
  let _ : DecidableRel H.Adj := Classical.decRel _
  obtain ⟨⟨a, ha⟩, r, hr⟩ := hm.1
  have hV : 4 ≤ Fintype.card V := by have := G.degree_lt_card_verts a; omega
  have hW : Fintype.card W + 1 = Fintype.card V := by
    rw [Fintype.card_subtype,
      show (Finset.univ.filter (fun v : V => v ≠ y)) = Finset.univ.erase y by ext v; simp]
    exact Finset.card_erase_add_one (Finset.mem_univ y)
  have hW2 : 2 ≤ Fintype.card {v : V // v ≠ y} := by
    change 2 ≤ Fintype.card W; omega
  have hdz : 3 ≤ H.degree ⟨x, hxy⟩ := by
    rw [mergeGraph_degree_z G x y hxy]
    have hdisjF : Disjoint ((G.neighborFinset x).erase y) ((G.neighborFinset y).erase x) := by
      rw [Finset.disjoint_left]
      intro c hc1 hc2
      exact hdisj c ⟨(G.mem_neighborFinset x c).mp (Finset.mem_of_mem_erase hc1),
                     (G.mem_neighborFinset y c).mp (Finset.mem_of_mem_erase hc2)⟩
    rw [Finset.card_union_of_disjoint hdisjF]
    have hex : ((G.neighborFinset x).erase y).card = G.degree x := by
      rw [Finset.erase_eq_of_notMem (fun hm => hnadj ((G.mem_neighborFinset x y).mp hm)),
          SimpleGraph.card_neighborFinset_eq_degree]
    have hey : ((G.neighborFinset y).erase x).card = G.degree y := by
      rw [Finset.erase_eq_of_notMem (fun hm => hnadj ((G.mem_neighborFinset y x).mp hm).symm),
          SimpleGraph.card_neighborFinset_eq_degree]
    have hx2 := no_small_defect G hm x
    have hy2 := no_small_defect G hm y
    omega
  have hdeg_other (u : W) (hux : u.val ≠ x) : H.degree u = G.degree u.val := by
    have hd := mergeGraph_degree_ne G x y hxy u hux
    have hno : ¬(G.Adj u.val x ∧ G.Adj u.val y) := fun h => hdisj u.val ⟨h.1.symm, h.2.symm⟩
    rw [ite_eq_right hno, add_zero] at hd
    exact hd
  have hnear : Near H := by
    by_cases hry : r = y
    · subst hry
      apply near_of_except H ⟨x, hxy⟩ hW2
      intro u hux
      rw [hdeg_other u (fun h => hux (Subtype.ext h))]
      exact hr u.val u.property
    · apply near_of_except H ⟨r, hry⟩ hW2
      intro u hur
      by_cases hux : u.val = x
      · have : u = ⟨x, hxy⟩ := Subtype.ext hux
        rw [this]; exact hdz
      · rw [hdeg_other u hux]
        exact hr u.val (fun h => hur (Subtype.ext h))
  obtain ⟨k, p, hk, hp, hl⟩ := identify_pair_dyadic_path G hm hxy hnear
  exact ⟨k, p.mapLe sdiff_le, hk, (Walk.isPath_mapLe sdiff_le).mpr hp, by simpa using hl⟩

/-- NEW Wave 2 Theorem: Universal All-Pairs Dyadic Path Theorem for ALL cubic MinimalBad graphs
    (covering C-N-R, C-N-2, C-N-3, C-T-2, C-T-3; works for dist = 1, 2, AND >= 3!). -/
theorem cubic_all_pairs_dyadic_path {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (hcubic : ∀ v, G.degree v = 3)
    {x y : V} (hxy : x ≠ y) :
    ∃ (k : ℕ) (p : (G \ SimpleGraph.edge x y).Walk x y),
      2 ≤ k ∧ p.IsPath ∧ p.length = 2 ^ k := by
  classical
  let W := {v : V // v ≠ y}
  let H := mergeGraph G x y hxy
  let _ : DecidableRel H.Adj := Classical.decRel _
  have hV : 4 ≤ Fintype.card V := by have := G.degree_lt_card_verts x; have := hcubic x; omega
  have hW : Fintype.card W + 1 = Fintype.card V := by
    rw [Fintype.card_subtype,
      show (Finset.univ.filter (fun v : V => v ≠ y)) = Finset.univ.erase y by ext v; simp]
    exact Finset.card_erase_add_one (Finset.mem_univ y)
  have hW2 : 2 ≤ Fintype.card {v : V // v ≠ y} := by
    change 2 ≤ Fintype.card W; omega
  have huniq : ∀ c1 c2, (G.Adj x c1 ∧ G.Adj y c1) → (G.Adj x c2 ∧ G.Adj y c2) → c1 = c2 := by
    intro c1 c2 h1 h2
    by_contra hne
    exact no_c4_of_power_free G hm.2.1 hxy hne h1.1 h1.2 h2.1 h2.2
  have hdz : 3 ≤ H.degree ⟨x, hxy⟩ := by
    rw [mergeGraph_degree_z G x y hxy]
    have hAB_inter : (((G.neighborFinset x).erase y) ∩ ((G.neighborFinset y).erase x)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro c1 hc1 c2 hc2
      simp only [Finset.mem_inter, Finset.mem_erase, G.mem_neighborFinset] at hc1 hc2
      exact huniq c1 c2 ⟨hc1.1.2, hc1.2.2⟩ ⟨hc2.1.2, hc2.2.2⟩
    have hA : 2 ≤ ((G.neighborFinset x).erase y).card := by
      by_cases h : G.Adj x y
      · have hc := Finset.card_erase_add_one ((G.mem_neighborFinset x y).mpr h)
        rw [SimpleGraph.card_neighborFinset_eq_degree, hcubic x] at hc; omega
      · have heq : (G.neighborFinset x).erase y = G.neighborFinset x :=
          Finset.erase_eq_of_notMem (fun hm => h ((G.mem_neighborFinset x y).mp hm))
        rw [heq, SimpleGraph.card_neighborFinset_eq_degree, hcubic x]; omega
    have hB : 2 ≤ ((G.neighborFinset y).erase x).card := by
      by_cases h : G.Adj y x
      · have hc := Finset.card_erase_add_one ((G.mem_neighborFinset y x).mpr h)
        rw [SimpleGraph.card_neighborFinset_eq_degree, hcubic y] at hc; omega
      · have heq : (G.neighborFinset y).erase x = G.neighborFinset y :=
          Finset.erase_eq_of_notMem (fun hm => h ((G.mem_neighborFinset y x).mp hm))
        rw [heq, SimpleGraph.card_neighborFinset_eq_degree, hcubic y]; omega
    have hu := Finset.card_union_add_card_inter ((G.neighborFinset x).erase y) ((G.neighborFinset y).erase x)
    omega
  have hnear : Near H := by
    by_cases hcomm : ∃ c : V, G.Adj x c ∧ G.Adj y c
    · obtain ⟨c, hxc, hyc⟩ := hcomm
      have hcy : c ≠ y := (G.ne_of_adj hyc).symm
      apply near_of_except H ⟨c, hcy⟩ hW2
      intro u huc
      by_cases hux : u.val = x
      · have : u = ⟨x, hxy⟩ := Subtype.ext hux
        rw [this]; exact hdz
      · have hd := mergeGraph_degree_ne G x y hxy u hux
        have hno : ¬(G.Adj u.val x ∧ G.Adj u.val y) := by
          rintro ⟨h1, h2⟩
          exact huc (Subtype.ext (huniq u.val c ⟨h1.symm, h2.symm⟩ ⟨hxc, hyc⟩))
        rw [ite_eq_right hno, add_zero] at hd
        rw [hd, hcubic u.val]
    · push Not at hcomm
      apply near_of_except H ⟨x, hxy⟩ hW2
      intro u hux
      have hd := mergeGraph_degree_ne G x y hxy u (fun h => hux (Subtype.ext h))
      have hno : ¬(G.Adj u.val x ∧ G.Adj u.val y) := fun h => hcomm u.val h.1.symm h.2.symm
      rw [ite_eq_right hno, add_zero] at hd
      rw [hd, hcubic u.val]
  exact identify_pair_dyadic_path G hm hxy hnear

/-- Helper: close a simple `x`–`y` path `p` in `G \ edge x y` with edge `G.Adj x y`
    to get a simple cycle of length `p.length + 1` in `G`. -/
theorem close_path_with_edge {V : Type u} {G : SimpleGraph V} {x y : V}
    (hadj : G.Adj x y) (p : (G \ SimpleGraph.edge x y).Walk x y)
    (hp : p.IsPath) (hlen : 2 ≤ p.length) :
    ∃ c : G.Walk x x, c.IsCycle ∧ c.length = p.length + 1 := by
  let pG : G.Walk y x := (p.mapLe sdiff_le).reverse
  have hpG : pG.IsPath := ((Walk.isPath_mapLe sdiff_le).mpr hp).reverse
  have hpG_len : pG.length = p.length := by simp [pG, Walk.length_reverse]
  exact ⟨Walk.cons hadj pG, cons_path_isCycle hadj pG hpG (by omega), by simp [hpG_len]⟩

/-- NEW Wave 2 Corollary: Every edge in ANY cubic MinimalBad graph lies on a simple
    odd cycle of length 2^k + 1 (k >= 2). -/
theorem cubic_every_edge_on_dyadic_plus_one_cycle {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (hcubic : ∀ v, G.degree v = 3)
    {x y : V} (hadj : G.Adj x y) :
    ∃ (k : ℕ) (c : G.Walk x x), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k + 1 := by
  obtain ⟨k, p, hk, hp, hl⟩ := cubic_all_pairs_dyadic_path G hm hcubic (G.ne_of_adj hadj)
  have h4 : 4 ≤ 2 ^ k := by
    have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hk
    simpa using this
  obtain ⟨c, hc, hcl⟩ := close_path_with_edge hadj p hp (by omega)
  exact ⟨k, c, hk, hc, by omega⟩

/-- NEW Wave 2 Theorem: In ANY MinimalBad graph (C, S, or H), every triangle-free edge
    lies on a simple odd cycle of length 2^k + 1 (k >= 2). -/
theorem tri_free_edge_on_dyadic_plus_one_cycle {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {x y : V} (hadj : G.Adj x y)
    (hnotri : ∀ c, ¬(G.Adj x c ∧ G.Adj y c)) :
    ∃ (k : ℕ) (c : G.Walk x x), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k + 1 := by
  classical
  have hxy : x ≠ y := G.ne_of_adj hadj
  let W := {v : V // v ≠ y}
  let H := mergeGraph G x y hxy
  let _ : DecidableRel H.Adj := Classical.decRel _
  obtain ⟨⟨a, ha⟩, r, hr⟩ := hm.1
  have hV : 4 ≤ Fintype.card V := by have := G.degree_lt_card_verts a; omega
  have hW : Fintype.card W + 1 = Fintype.card V := by
    rw [Fintype.card_subtype,
      show (Finset.univ.filter (fun v : V => v ≠ y)) = Finset.univ.erase y by ext v; simp]
    exact Finset.card_erase_add_one (Finset.mem_univ y)
  have hW2 : 2 ≤ Fintype.card {v : V // v ≠ y} := by
    change 2 ≤ Fintype.card W; omega
  have hdz : 3 ≤ H.degree ⟨x, hxy⟩ := by
    rw [mergeGraph_degree_z G x y hxy]
    have hdisjF : Disjoint ((G.neighborFinset x).erase y) ((G.neighborFinset y).erase x) := by
      rw [Finset.disjoint_left]
      intro c hc1 hc2
      exact hnotri c ⟨(G.mem_neighborFinset x c).mp (Finset.mem_of_mem_erase hc1),
                      (G.mem_neighborFinset y c).mp (Finset.mem_of_mem_erase hc2)⟩
    rw [Finset.card_union_of_disjoint hdisjF]
    have hcx := Finset.card_erase_add_one ((G.mem_neighborFinset x y).mpr hadj)
    have hcy := Finset.card_erase_add_one ((G.mem_neighborFinset y x).mpr hadj.symm)
    rw [SimpleGraph.card_neighborFinset_eq_degree] at hcx hcy
    have hx2 := no_small_defect G hm x
    have hy2 := no_small_defect G hm y
    have hsum : 5 ≤ G.degree x + G.degree y := by
      by_cases hxr : x = r
      · subst hxr
        have := hr y (Ne.symm hxy)
        omega
      · have := hr x hxr
        omega
    omega
  have hdeg_other (u : W) (hux : u.val ≠ x) : H.degree u = G.degree u.val := by
    have hd := mergeGraph_degree_ne G x y hxy u hux
    have hno : ¬(G.Adj u.val x ∧ G.Adj u.val y) := fun h => hnotri u.val ⟨h.1.symm, h.2.symm⟩
    rw [ite_eq_right hno, add_zero] at hd
    exact hd
  have hnear : Near H := by
    by_cases hry : r = y
    · subst hry
      apply near_of_except H ⟨x, hxy⟩ hW2
      intro u hux
      rw [hdeg_other u (fun h => hux (Subtype.ext h))]
      exact hr u.val u.property
    · apply near_of_except H ⟨r, hry⟩ hW2
      intro u hur
      by_cases hux : u.val = x
      · have : u = ⟨x, hxy⟩ := Subtype.ext hux
        rw [this]; exact hdz
      · rw [hdeg_other u hux]
        exact hr u.val (fun h => hur (Subtype.ext h))
  obtain ⟨k, p, hk, hp, hl⟩ := identify_pair_dyadic_path G hm hxy hnear
  have h4 : 4 ≤ 2 ^ k := by
    have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hk
    simpa using this
  obtain ⟨c, hc, hcl⟩ := close_path_with_edge hadj p hp (by omega)
  exact ⟨k, c, hk, hc, by omega⟩

#print axioms high_degree_independent
#print axioms no_all_high_neighbors
#print axioms defect_neighbor_at_most_one_high_neighbor
#print axioms no_c4_of_power_free
#print axioms identify_pair_dyadic_path
#print axioms dist_ge3_dyadic_path
#print axioms cubic_all_pairs_dyadic_path
#print axioms cubic_every_edge_on_dyadic_plus_one_cycle
#print axioms tri_free_edge_on_dyadic_plus_one_cycle
end E64Wave2Agent1
