import Mathlib

open Classical
open SimpleGraph

namespace E64Wave7Agent3P1

/-!
# Wave 7 Agent #3 — Pillar 1: 3-Connected Menger & 2-Cut Splitting on `G = H - ab`
-/

def IsPowerOfTwo (L : ℕ) : Prop := ∃ k : ℕ, 2 ≤ k ∧ L = 2 ^ k

def HasPowerCycle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ IsPowerOfTwo p.length

def PowerFree {V : Type*} (G : SimpleGraph V) : Prop := ¬ HasPowerCycle G

def addEdge {V : Type*} (G : SimpleGraph V) (a b : V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ (G.Adj u v ∨ (u = a ∧ v = b) ∨ (u = b ∧ v = a))
  symm := by
    intro u v ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    rcases h with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  loopless := fun _ ⟨hne, _⟩ => hne rfl

def IsThreeConnected {V : Type*} [Fintype V] (H : SimpleGraph V) : Prop :=
  4 ≤ Fintype.card V ∧
  ∀ S : Finset V, S.card ≤ 2 → (H.induce (Sᶜ : Set V)).Connected

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
    · have hu_in : u ∈ q.support := Walk.mem_support_of_mem_edges q hmem' (by simp)
      exact False.elim ((List.nodup_cons.mp hp.support_nodup).1 hu_in)

lemma two_internally_disjoint_paths_cycle {V : Type*} {G : SimpleGraph V} {u v : V}
    (p q : G.Walk u v) (hp : p.IsPath) (hq : q.IsPath)
    (hp1 : 1 ≤ p.length) (hq1 : 1 ≤ q.length) (hsum3 : 3 ≤ p.length + q.length)
    (hdisj : ∀ w, w ∈ p.support → w ∈ q.support → w = u ∨ w = v) :
    (p.append q.reverse).IsCycle ∧ (p.append q.reverse).length = p.length + q.length := by
  let c : G.Walk u u := p.append q.reverse
  have hlen : c.length = p.length + q.length := by
    simp [c, Walk.length_append, Walk.length_reverse]
  have hp_ne : ¬ p.Nil := fun h => by have := Walk.length_eq_zero_iff.mpr h; omega
  have hqr_ne : ¬ q.reverse.Nil := fun h => by
    have : q.reverse.length = 0 := Walk.length_eq_zero_iff.mpr h
    rw [Walk.length_reverse] at this; omega
  have hqr_path : q.reverse.IsPath := hq.reverse
  refine ⟨?_, hlen⟩
  rw [Walk.isCycle_def]
  refine ⟨?_, ?_, ?_⟩
  · rw [Walk.isTrail_def]
    simp only [c, Walk.edges_append]
    rw [List.nodup_append]
    refine ⟨hp.isTrail.edges_nodup, hqr_path.isTrail.edges_nodup, ?_⟩
    intro e he1 e' he2 heq
    subst heq
    have he2q : e ∈ q.edges := by simpa [Walk.edges_reverse] using he2
    refine Sym2.ind (fun x y => ?_) e he1 he2q
    intro hxy1 hxy2
    have hx_p : x ∈ p.support := Walk.mem_support_of_mem_edges p hxy1 (by simp)
    have hy_p : y ∈ p.support := Walk.mem_support_of_mem_edges p hxy1 (by simp)
    have hx_q : x ∈ q.support := Walk.mem_support_of_mem_edges q hxy2 (by simp)
    have hy_q : y ∈ q.support := Walk.mem_support_of_mem_edges q hxy2 (by simp)
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
    have : c.length = 0 := Walk.length_eq_zero_iff.mpr hnil
    omega
  · have hsupp : c.support = p.support ++ q.reverse.support.tail := Walk.support_append p q.reverse
    have htail : c.support.tail = p.support.tail ++ q.reverse.support.tail := by
      rw [hsupp]
      cases p with
      | nil => exact False.elim (hp_ne rfl)
      | cons _ _ => simp [Walk.support_cons]
    rw [htail, List.nodup_append]
    have hp_tail_nd : p.support.tail.Nodup := by
      cases p with
      | nil => exact False.elim (hp_ne rfl)
      | cons _ _ => exact (List.nodup_cons.mp hp.support_nodup).2
    have hqr_tail_nd : q.reverse.support.tail.Nodup := by
      cases hqr : q.reverse with
      | nil => exact False.elim (hqr_ne hqr)
      | cons _ _ =>
        have hnd := hqr_path.support_nodup
        rw [hqr] at hnd
        exact (List.nodup_cons.mp hnd).2
    refine ⟨hp_tail_nd, hqr_tail_nd, ?_⟩
    intro w hw1 w' hw2 heq
    subst heq
    have hw_p : w ∈ p.support := by
      cases p with
      | nil => exact False.elim (hp_ne rfl)
      | cons _ _ => exact List.mem_cons_of_mem _ hw1
    have hw_qr : w ∈ q.reverse.support := by
      cases hqr : q.reverse with
      | nil => exact False.elim (hqr_ne hqr)
      | cons _ _ => rw [hqr] at hw2; exact List.mem_cons_of_mem _ hw2
    have hw_q : w ∈ q.support := by simpa [Walk.support_reverse] using hw_qr
    rcases hdisj w hw_p hw_q with rfl | rfl
    · cases p with
      | nil => exact False.elim (hp_ne rfl)
      | cons _ _ => exact (List.nodup_cons.mp hp.support_nodup).1 hw1
    · cases hqr : q.reverse with
      | nil => exact False.elim (hqr_ne hqr)
      | cons _ _ =>
        have hnd := hqr_path.support_nodup
        rw [hqr] at hnd
        rw [hqr] at hw2
        exact (List.nodup_cons.mp hnd).1 hw2

/-- PILLAR 1.1: If `H = G + ab` is 3-vertex-connected, then NO 2-vertex cut `{x, y}` of `G`
    can contain either defect `a` or `b`. -/
theorem minimal_bad2_two_cut_avoids_defects {V : Type*} [Fintype V]
    {G : SimpleGraph V} {a b x y : V}
    (h3c : IsThreeConnected (addEdge G a b))
    (hcut : ¬ (G.induce (({x, y} : Finset V)ᶜ : Set V)).Connected) :
    a ≠ x ∧ a ≠ y ∧ b ≠ x ∧ b ≠ y := by
  have heq_sub : ∀ (hmem : a ∈ ({x, y} : Finset V) ∨ b ∈ ({x, y} : Finset V)),
      G.induce (({x, y} : Finset V)ᶜ : Set V) =
      (addEdge G a b).induce (({x, y} : Finset V)ᶜ : Set V) := by
    intro hmem
    ext u v
    simp only [SimpleGraph.induce_adj, addEdge]
    constructor
    · intro huv
      exact ⟨G.ne_of_adj huv, Or.inl huv⟩
    · rintro ⟨_, huv | ⟨hua, hvb⟩ | ⟨hub, hva⟩⟩
      · exact huv
      · rcases hmem with ha | hb
        · exact False.elim ((Finset.mem_compl.mp u.2) (hua ▸ ha))
        · exact False.elim ((Finset.mem_compl.mp v.2) (hvb ▸ hb))
      · rcases hmem with ha | hb
        · exact False.elim ((Finset.mem_compl.mp v.2) (hva ▸ ha))
        · exact False.elim ((Finset.mem_compl.mp u.2) (hub ▸ hb))
  have hH_conn : ((addEdge G a b).induce (({x, y} : Finset V)ᶜ : Set V)).Connected :=
    h3c.2 {x, y} Finset.card_le_two
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h; apply hcut; rw [heq_sub (Or.inl (by simp [h]))]; exact hH_conn
  · intro h; apply hcut; rw [heq_sub (Or.inl (by simp [h]))]; exact hH_conn
  · intro h; apply hcut; rw [heq_sub (Or.inr (by simp [h]))]; exact hH_conn
  · intro h; apply hcut; rw [heq_sub (Or.inr (by simp [h]))]; exact hH_conn

lemma addEdge_walk_reachable_or_hits_ab {V : Type*} {G : SimpleGraph V} {a b : V} {S : Finset V}
    {u v : {w : V // w ∈ (Sᶜ : Set V)}}
    (p : ((addEdge G a b).induce (Sᶜ : Set V)).Walk u v) :
    (G.induce (Sᶜ : Set V)).Reachable u v ∨
    (∃ ha : a ∈ (Sᶜ : Set V), (G.induce (Sᶜ : Set V)).Reachable u ⟨a, ha⟩) ∨
    (∃ hb : b ∈ (Sᶜ : Set V), (G.induce (Sᶜ : Set V)).Reachable u ⟨b, hb⟩) := by
  induction p with
  | nil => exact Or.inl Reachable.refl
  | @cons x y z hxy q ih =>
    rcases hxy.2 with hG | ⟨hxa, _⟩ | ⟨hxb, _⟩
    · rcases ih with hreach | ⟨ha, hreach⟩ | ⟨hb, hreach⟩
      · exact Or.inl (Reachable.trans (Adj.reachable hG) hreach)
      · exact Or.inr (Or.inl ⟨ha, Reachable.trans (Adj.reachable hG) hreach⟩)
      · exact Or.inr (Or.inr ⟨hb, Reachable.trans (Adj.reachable hG) hreach⟩)
    · have ha : a ∈ (Sᶜ : Set V) := hxa ▸ x.2
      have hxeq : x = ⟨a, ha⟩ := Subtype.ext hxa
      exact Or.inr (Or.inl ⟨ha, hxeq ▸ Reachable.refl⟩)
    · have hb : b ∈ (Sᶜ : Set V) := hxb ▸ x.2
      have hxeq : x = ⟨b, hb⟩ := Subtype.ext hxb
      exact Or.inr (Or.inr ⟨hb, hxeq ▸ Reachable.refl⟩)

/-- PILLAR 1.2: Every 2-vertex cut `{x, y}` of `G = H - ab` splits `G - {x, y}` into
    EXACTLY TWO components: every vertex `w ∉ {x, y}` is reachable from either `a` or `b`. -/
theorem minimal_bad2_two_cut_exact_two_components {V : Type*} [Fintype V]
    {G : SimpleGraph V} {a b x y : V}
    (h3c : IsThreeConnected (addEdge G a b))
    (hcut : ¬ (G.induce (({x, y} : Finset V)ᶜ : Set V)).Connected) :
    ∃ (ha : a ∈ (({x, y} : Finset V)ᶜ : Set V)) (hb : b ∈ (({x, y} : Finset V)ᶜ : Set V)),
      ¬ (G.induce (({x, y} : Finset V)ᶜ : Set V)).Reachable ⟨a, ha⟩ ⟨b, hb⟩ ∧
      ∀ (w : {z : V // z ∈ (({x, y} : Finset V)ᶜ : Set V)}),
        (G.induce (({x, y} : Finset V)ᶜ : Set V)).Reachable w ⟨a, ha⟩ ∨
        (G.induce (({x, y} : Finset V)ᶜ : Set V)).Reachable w ⟨b, hb⟩ := by
  have hav := minimal_bad2_two_cut_avoids_defects h3c hcut
  have ha : a ∈ (({x, y} : Finset V)ᶜ : Set V) := by
    simp only [Finset.mem_coe, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hav.1, hav.2.1⟩
  have hb : b ∈ (({x, y} : Finset V)ᶜ : Set V) := by
    simp only [Finset.mem_coe, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hav.2.2.1, hav.2.2.2⟩
  have hH_conn := h3c.2 {x, y} Finset.card_le_two
  have hall : ∀ w : {z : V // z ∈ (({x, y} : Finset V)ᶜ : Set V)},
      (G.induce (({x, y} : Finset V)ᶜ : Set V)).Reachable w ⟨a, ha⟩ ∨
      (G.induce (({x, y} : Finset V)ᶜ : Set V)).Reachable w ⟨b, hb⟩ := by
    intro w
    rcases hH_conn.preconnected w ⟨a, ha⟩ with ⟨p⟩
    rcases addEdge_walk_reachable_or_hits_ab p with h | ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inl h
    · exact Or.inr h
  refine ⟨ha, hb, ?_, hall⟩
  intro hab_reach
  apply hcut
  refine ⟨?_, ⟨⟨a, ha⟩⟩⟩
  intro u v
  rcases hall u with hua | hub <;> rcases hall v with hva | hvb
  · exact hua.trans hva.symm
  · exact hua.trans (hab_reach.trans hvb.symm)
  · exact hub.trans (hab_reach.symm.trans hva.symm)
  · exact hub.trans hvb.symm

/-- PILLAR 1.3: Menger Separator Theorem on `G = H - ab`:
    Any vertex separator `S` of size ≤ 2 separating `u` and `v` in `G` must avoid `a` and `b`
    and separate `a` from `b` in `G - S`. -/
theorem minimal_bad2_menger_separator_forces_defect_split {V : Type*} [Fintype V]
    {G : SimpleGraph V} {a b : V} (S : Finset V)
    (h3c : IsThreeConnected (addEdge G a b))
    (hScard : S.card ≤ 2)
    {u v : {z : V // z ∈ (Sᶜ : Set V)}}
    (hsep : ¬ (G.induce (Sᶜ : Set V)).Reachable u v) :
    ∃ (ha : a ∈ (Sᶜ : Set V)) (hb : b ∈ (Sᶜ : Set V)),
      ¬ (G.induce (Sᶜ : Set V)).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
  have hH_conn := h3c.2 S hScard
  have ha_in : a ∈ (Sᶜ : Set V) := by
    by_contra hna
    have hsame : G.induce (Sᶜ : Set V) = (addEdge G a b).induce (Sᶜ : Set V) := by
      ext w1 w2
      simp only [SimpleGraph.induce_adj, addEdge]
      constructor
      · intro h; exact ⟨G.ne_of_adj h, Or.inl h⟩
      · rintro ⟨_, h | ⟨rfl, _⟩ | ⟨_, rfl⟩⟩
        · exact h
        · exact False.elim (hna w1.2)
        · exact False.elim (hna w2.2)
    apply hsep
    rw [hsame]
    exact hH_conn.preconnected u v
  have hb_in : b ∈ (Sᶜ : Set V) := by
    by_contra hnb
    have hsame : G.induce (Sᶜ : Set V) = (addEdge G a b).induce (Sᶜ : Set V) := by
      ext w1 w2
      simp only [SimpleGraph.induce_adj, addEdge]
      constructor
      · intro h; exact ⟨G.ne_of_adj h, Or.inl h⟩
      · rintro ⟨_, h | ⟨_, rfl⟩ | ⟨rfl, _⟩⟩
        · exact h
        · exact False.elim (hnb w2.2)
        · exact False.elim (hnb w1.2)
    apply hsep
    rw [hsame]
    exact hH_conn.preconnected u v
  refine ⟨ha_in, hb_in, ?_⟩
  intro hab_reach
  apply hsep
  rcases hH_conn.preconnected u ⟨a, ha_in⟩ with ⟨pu⟩
  rcases hH_conn.preconnected v ⟨a, ha_in⟩ with ⟨pv⟩
  have hu : (G.induce (Sᶜ : Set V)).Reachable u ⟨a, ha_in⟩ ∨
      (G.induce (Sᶜ : Set V)).Reachable u ⟨b, hb_in⟩ := by
    rcases addEdge_walk_reachable_or_hits_ab pu with h | ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inl h
    · exact Or.inr h
  have hv : (G.induce (Sᶜ : Set V)).Reachable v ⟨a, ha_in⟩ ∨
      (G.induce (Sᶜ : Set V)).Reachable v ⟨b, hb_in⟩ := by
    rcases addEdge_walk_reachable_or_hits_ab pv with h | ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inl h
    · exact Or.inr h
  rcases hu with hua | hub <;> rcases hv with hva | hvb
  · exact hua.trans hva.symm
  · exact hua.trans (hab_reach.trans hvb.symm)
  · exact hub.trans (hab_reach.symm.trans hva.symm)
  · exact hub.trans hvb.symm

/-- PILLAR 1.4: Across any 2-vertex cut `{x, y}` separating `Ca` and `Cb`, no power of 2
    `2^k` (k ≥ 2) can occur as a simple `x`-`y` path length in BOTH `Ca ∪ {x, y}` and `Cb ∪ {x, y}`. -/
theorem minimal_bad2_two_cut_dyadic_path_disjoint {V : Type*}
    {G : SimpleGraph V} (hpf : PowerFree G) {x y : V} {Ca Cb : Finset V}
    (hdisj : Disjoint Ca Cb)
    (p : G.Walk x y) (hp : p.IsPath)
    (hp_in : ∀ w ∈ p.support, w ∈ Ca ∨ w = x ∨ w = y)
    (q : G.Walk x y) (hq : q.IsPath)
    (hq_in : ∀ w ∈ q.support, w ∈ Cb ∨ w = x ∨ w = y)
    {k : ℕ} (hk : 2 ≤ k) (hplen : p.length = 2 ^ k) (hqlen : q.length = 2 ^ k) :
    False := by
  have hge4 : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hdisj_supp : ∀ w, w ∈ p.support → w ∈ q.support → w = x ∨ w = y := by
    intro w hwp hwq
    rcases hp_in w hwp with hwCa | hxy
    · rcases hq_in w hwq with hwCb | hxy
      · exact False.elim (Finset.disjoint_left.mp hdisj hwCa hwCb)
      · exact hxy
    · exact hxy
  rcases two_internally_disjoint_paths_cycle p q hp hq (by omega) (by omega) (by omega) hdisj_supp
    with ⟨hcyc, hclen⟩
  apply hpf
  refine ⟨x, p.append q.reverse, hcyc, k + 1, by omega, ?_⟩
  rw [hclen, hplen, hqlen, pow_succ]
  omega

end E64Wave7Agent3P1
