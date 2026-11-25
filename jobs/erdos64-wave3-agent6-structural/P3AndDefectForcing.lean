import Core
import Leaves
import Descent
import PairedShadow

/-!
Erdos 64 (Wave 3, Agent #6): Induced-P3 Fermat Cycle & Defect Edge-Deletion Forcing.
Proves (unconditionally, all finite orders, standard axioms only):
1. `cubic_p3_fermat_cycle`: In EVERY cubic MinimalBad(G) (C-N-R, C-N-2, C-N-3, C-T-2, C-T-3),
   EVERY induced P3 (u1 - v - u2 with ¬G.Adj u1 u2) lies on a simple (2^k + 1)-cycle (k ≥ 2).
   (Strictly new: complements Wave 2's (2^m + 2)-cycle through every induced P3.)
2. `defect_fermat_cycle`: In ANY MinimalBad(G) with defect w (deg w = 2, N(w) = {b1, b2},
   ¬G.Adj b1 b2), b1 - w - b2 lies on a simple (2^k + 1)-cycle (k ≥ 2).
3. `defect_edge_del_mersenne_path`: In ANY MinimalBad(G) with defect w (N(w) = {b1, b2},
   ¬G.Adj b1 b2) and ANY edge xy with 4 ≤ deg x and x, y ≠ w, the graph G - w - xy
   contains a simple b1-b2 path of length 2^k - 1 (k ≥ 2).
-/

namespace E64P3Defect
open SimpleGraph Erdos64Closure E64Core E64Leaves Erdos64Paired
universe u

variable {V : Type u}

/-- Generic lifting lemma: if `H = (G.induce {x | x ≠ v}) ⊔ edge a b` (or a subgraph of it)
    has a power-of-2 cycle and `G` is power-free, then `G.induce {x | x ≠ v}` contains a
    simple `a`-`b` path of length `2^k - 1` (k ≥ 2) avoiding `v`. -/
theorem mersenne_path_of_add_edge {G : SimpleGraph V} {v : V}
    {a b : {x : V // x ≠ v}} (hab : a ≠ b)
    {H : SimpleGraph {x : V // x ≠ v}}
    (hsub : H ≤ (G.induce {x | x ≠ v}) ⊔ SimpleGraph.edge a b)
    (hfree : ¬ HasPower G) (hpow : HasPower H) :
    ∃ (k : ℕ) (p : (H \ SimpleGraph.edge a b).Walk a b),
      2 ≤ k ∧ p.IsPath ∧ p.length + 1 = 2 ^ k := by
  classical
  obtain ⟨k, u₀, c, hk, hc, hlen⟩ := hpow
  have hge4 : 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide : 0 < 2) hk
  by_cases hmem : s(a, b) ∈ c.edges
  · have hmemA : a ∈ c.support := Walk.fst_mem_support_of_mem_edges c hmem
    let c' := c.rotate a hmemA
    have hc' : c'.IsCycle := hc.rotate hmemA
    have hlen' : c'.length = 2 ^ k := by rw [Walk.length_rotate, hlen]
    have hmem' : s(a, b) ∈ c'.edges := by
      have hspec : ((c.takeUntil a hmemA).append (c.dropUntil a hmemA)).edges = c.edges :=
        congrArg Walk.edges (c.take_spec hmemA)
      rw [Walk.edges_append] at hspec
      have hmem_or : s(a, b) ∈ (c.takeUntil a hmemA).edges ∨ s(a, b) ∈ (c.dropUntil a hmemA).edges :=
        List.mem_append.mp (hspec.symm ▸ hmem)
      show s(a, b) ∈ ((c.dropUntil a hmemA).append (c.takeUntil a hmemA)).edges
      rw [Walk.edges_append, List.mem_append]
      exact hmem_or.symm
    have hstart : ∃ q : H.Walk b a, q.IsPath ∧ q.length + 1 = 2 ^ k ∧ s(a, b) ∉ q.edges := by
      cases hce : c' with
      | nil => rw [hce] at hlen'; simp at hlen'; omega
      | @cons _ x _ hax q =>
        by_cases hxb : x = b
        · subst hxb
          have hqpath : q.IsPath := by
            apply Walk.IsPath.mk'
            have hsn := hc'.support_nodup
            rw [hce, Walk.support_cons, List.tail_cons] at hsn
            exact hsn
          have hqlen : q.length + 1 = 2 ^ k := by
            have := congrArg Walk.length hce; simp at this; omega
          have hqno : s(a, x) ∉ q.edges := by
            have hnd := hc'.isTrail.edges_nodup
            rw [hce, Walk.edges_cons, List.nodup_cons] at hnd
            exact hnd.1
          exact ⟨q, hqpath, hqlen, hqno⟩
        · have hrev_cyc : c'.reverse.IsCycle := hc'.reverse
          have hrev_len : c'.reverse.length = 2 ^ k := by rw [Walk.length_reverse, hlen']
          cases hre : c'.reverse with
          | nil => rw [hre] at hrev_len; simp at hrev_len; omega
          | @cons _ y _ hay r =>
            have hyb : y = b := by
              have hmem_rev : s(a, b) ∈ c'.reverse.edges := by
                rw [Walk.edges_reverse, List.mem_reverse]; exact hmem'
              rw [hre, Walk.edges_cons, List.mem_cons] at hmem_rev
              rcases hmem_rev with heq | _
              · rcases Sym2.eq_iff.mp heq with ⟨_, rfl⟩ | ⟨_, h2⟩
                · rfl
                · exact False.elim (hab h2.symm)
              · have hmem_c : s(a, b) ∈ q.edges := by
                  rw [hce, Walk.edges_cons, List.mem_cons] at hmem'
                  rcases hmem' with heq | hq
                  · rcases Sym2.eq_iff.mp heq with ⟨_, hbx⟩ | ⟨_, h2⟩
                    · exact False.elim (hxb hbx.symm)
                    · exact False.elim (hab h2.symm)
                  · exact hq
                have hq_edges : c'.reverse.edges = q.reverse.edges ++ [s(x, a)] := by
                  rw [hce, Walk.reverse_cons, Walk.edges_append]
                  simp
                have hmem_qrev : s(a, b) ∈ q.reverse.edges := by
                  rw [Walk.edges_reverse, List.mem_reverse]; exact hmem_c
                have hqrev_hd : q.reverse.edges.head? = some s(a, y) := by
                  rw [hre, Walk.edges_cons] at hq_edges
                  cases hqr : q.reverse.edges with
                  | nil =>
                    rw [hqr, List.nil_append] at hq_edges
                    have := congrArg List.head? hq_edges
                    simp at this
                    have hql : q.reverse.length = 0 := by
                      have := Walk.length_edges q.reverse; rw [hqr] at this; exact this.symm
                    have hcl : c'.length = 1 := by
                      rw [hce, Walk.length_cons]; rw [Walk.length_reverse] at hql; omega
                    omega
                  | cons e es =>
                    rw [hqr, List.cons_append] at hq_edges
                    have := congrArg List.head? hq_edges
                    simp at this
                    rw [this]; rfl
                have hqpath : q.IsPath := by
                  apply Walk.IsPath.mk'
                  have hsn := hc'.support_nodup
                  rw [hce, Walk.support_cons, List.tail_cons] at hsn
                  exact hsn
                have hqrp : q.reverse.IsPath := hqpath.reverse
                cases hqrv : q.reverse with
                | nil =>
                  rw [hqrv] at hmem_qrev; simp at hmem_qrev
                | @cons _ z _ haz rest =>
                  rw [hqrv, Walk.edges_cons] at hqrev_hd hmem_qrev
                  simp only [List.head?_cons, Option.some.injEq] at hqrev_hd
                  rcases List.mem_cons.mp hmem_qrev with heq1 | hmem_rest
                  · rw [← hqrev_hd] at heq1
                    rcases Sym2.eq_iff.mp heq1 with ⟨_, hby⟩ | ⟨_, h2⟩
                    · exact hby.symm
                    · exact False.elim (hab h2.symm)
                  · have ha_rest : a ∈ rest.support := Walk.fst_mem_support_of_mem_edges rest hmem_rest
                    have hnd := hqrp.support_nodup
                    rw [hqrv, Walk.support_cons, List.nodup_cons] at hnd
                    exact False.elim (hnd.1 ha_rest)
            subst hyb
            have hrpath : r.IsPath := by
              apply Walk.IsPath.mk'
              have hsn := hrev_cyc.support_nodup
              rw [hre, Walk.support_cons, List.tail_cons] at hsn
              exact hsn
            have hrlen : r.length + 1 = 2 ^ k := by
              have := congrArg Walk.length hre; simp at this; omega
            have hrno : s(a, y) ∉ r.edges := by
              have hnd := hrev_cyc.isTrail.edges_nodup
              rw [hre, Walk.edges_cons, List.nodup_cons] at hnd
              exact hnd.1
            exact ⟨r, hrpath, hrlen, hrno⟩
    obtain ⟨q, hqpath, hqlen, hqno⟩ := hstart
    have htrans : ∀ e ∈ q.reverse.edges, e ∈ (H \ SimpleGraph.edge a b).edgeSet := by
      intro e he
      rw [Walk.edges_reverse, List.mem_reverse] at he
      rw [SimpleGraph.edgeSet_sdiff, Set.mem_sdiff]
      refine ⟨q.edges_subset_edgeSet he, ?_⟩
      rw [SimpleGraph.edgeSet_edge_of_ne hab, Set.mem_singleton_iff]
      exact fun heq => hqno (heq ▸ he)
    let p := q.reverse.transfer (H \ SimpleGraph.edge a b) htrans
    exact ⟨k, p, hk, hqpath.reverse.transfer htrans, by simp [p, Walk.length_reverse, hqlen]⟩
  · have htrans : ∀ e ∈ c.edges, e ∈ (G.induce {x | x ≠ v}).edgeSet := by
      intro e he
      have hH := c.edges_subset_edgeSet he
      have hle := (SimpleGraph.edgeSet_mono hsub) hH
      rw [SimpleGraph.edgeSet_sup] at hle
      rcases hle with hg | hadd
      · exact hg
      · rw [SimpleGraph.edgeSet_edge_of_ne hab, Set.mem_singleton_iff] at hadd
        exact False.elim (hmem (hadd ▸ he))
    let cG := c.transfer (G.induce {x | x ≠ v}) htrans
    have hpowInd : HasPower (G.induce {x | x ≠ v}) :=
      ⟨k, u₀, cG, hk, hc.transfer htrans, by simp [cG, hlen]⟩
    exact False.elim (hfree (power_induce G _ hpowInd))

/-- Close a simple `a`-`b` path in `G - v` of length `2^k - 1` via `a - v - b`
    to obtain a simple `(2^k + 1)`-cycle in `G` containing both edges `s(a, v)` and `s(v, b)`. -/
theorem fermat_cycle_of_p3_and_mersenne {G : SimpleGraph V} {v : V}
    {a b : {x : V // x ≠ v}} (hav : G.Adj a.1 v) (hvb : G.Adj v b.1)
    {k : ℕ} (hk : 2 ≤ k) (p : (G.induce {x | x ≠ v}).Walk a b)
    (hp : p.IsPath) (hlen : p.length + 1 = 2 ^ k) :
    ∃ c : G.Walk v v, c.IsCycle ∧ c.length = 2 ^ k + 1 ∧
      s(v, a.1) ∈ c.edges ∧ s(v, b.1) ∈ c.edges := by
  let f : G.induce {x | x ≠ v} →g G := ⟨Subtype.val, fun h => h⟩
  let pG : G.Walk a.1 b.1 := p.map f
  have hpG : pG.IsPath := by
    apply Walk.IsPath.mk'
    rw [Walk.support_map]
    exact (List.nodup_map_iff Subtype.val_injective).mpr hp.support_nodup
  have hpGlen : pG.length = p.length := Walk.length_map f p
  have hvnot : v ∉ pG.support := by
    rw [Walk.support_map]
    intro hm
    obtain ⟨x, _, hxv⟩ := List.mem_map.mp hm
    exact x.2 hxv
  have hge4 : 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide : 0 < 2) hk
  let c : G.Walk v v := .cons hav.symm (pG.append (.cons hvb.symm .nil))
  have hclen : c.length = 2 ^ k + 1 := by
    simp [c, Walk.length_append, hpGlen]; omega
  have hsupp : c.support = v :: (pG.support ++ [v]) := by
    simp [c, Walk.support_cons, Walk.support_append]
  have htail : c.support.tail = pG.support ++ [v] := by
    rw [hsupp, List.tail_cons]
  have hnodup : c.support.tail.Nodup := by
    rw [htail]
    exact List.nodup_append'.mpr ⟨hpG.support_nodup, List.nodup_singleton v,
      fun z hz1 hz2 => hvnot ((List.mem_singleton.mp hz2) ▸ hz1)⟩
  have hnil : ¬ c.Nil := by
    intro h; have := Walk.length_eq_zero_iff.mpr h; omega
  have hc : c.IsCycle := by
    apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    refine ⟨Walk.IsPath.mk' ?_, by omega⟩
    rwa [Walk.support_tail_of_not_nil _ hnil]
  have hmem1 : s(v, a.1) ∈ c.edges := by simp [c]
  have hmem2 : s(v, b.1) ∈ c.edges := by
    simp only [c, Walk.edges_cons, Walk.edges_append, Walk.edges_nil, List.mem_cons,
      List.mem_append]
    exact Or.inr (Or.inr (Or.inl Sym2.eq_swap))
  exact ⟨c, hc, hclen, hmem1, hmem2⟩

/-- NEW (Wave 3, Agent #6): Cubic Induced-P3 Simultaneous (2^k + 1)-Cycle Forcing.
    In EVERY cubic MinimalBad(G), EVERY induced P3 (u1 - v - u2 with ¬G.Adj u1 u2)
    lies on a simple cycle of length 2^k + 1 (k ≥ 2). -/
theorem cubic_p3_fermat_cycle [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G) (hC : Cubic G)
    {v u₁ u₂ : V} (h1 : G.Adj u₁ v) (h2 : G.Adj v u₂) (h12 : u₁ ≠ u₂)
    (hnadj : ¬ G.Adj u₁ u₂) :
    ∃ (k : ℕ) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k + 1 ∧
      s(v, u₁) ∈ c.edges ∧ s(v, u₂) ∈ c.edges := by
  classical
  let W := {x : V // x ≠ v}
  have hu₁ : u₁ ≠ v := G.ne_of_adj h1
  have hu₂ : u₂ ≠ v := (G.ne_of_adj h2).symm
  let a : W := ⟨u₁, hu₁⟩
  let b : W := ⟨u₂, hu₂⟩
  have hab : a ≠ b := fun h => h12 (congrArg Subtype.val h)
  let Gv := G.induce {x | x ≠ v}
  let _ : DecidableRel Gv.Adj := inferInstanceAs (DecidableRel (G.induce {x | x ≠ v}).Adj)
  let H := Gv ⊔ SimpleGraph.edge a b
  let _ : DecidableRel H.Adj := inferInstanceAs (DecidableRel (Gv ⊔ SimpleGraph.edge a b).Adj)
  have hex3 : ∃ u₃ : V, G.Adj v u₃ ∧ u₃ ≠ u₁ ∧ u₃ ≠ u₂ := by
    by_contra h
    push Not at h
    have hs : G.neighborFinset v ⊆ ({u₁, u₂} : Finset V) := by
      intro x hx
      have hadj := (G.mem_neighborFinset v x).mp hx
      by_cases hx1 : x = u₁
      · simp [hx1]
      · simp [h x hadj hx1]
    have hc := Finset.card_le_card hs
    rw [G.card_neighborFinset_eq_degree, hC v] at hc
    have h2c : ({u₁, u₂} : Finset V).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨u₃, hv3, h31, h32⟩ := hex3
  let c3 : W := ⟨u₃, (G.ne_of_adj hv3).symm⟩
  have huniq_nbr : ∀ x : V, G.Adj v x → x = u₁ ∨ x = u₂ ∨ x = u₃ := by
    intro x hvx
    by_contra hnot
    push Not at hnot
    have hs : ({u₁, u₂, u₃, x} : Finset V) ⊆ G.neighborFinset v := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact (G.mem_neighborFinset v _).mpr h1.symm
      · exact (G.mem_neighborFinset v _).mpr h2
      · exact (G.mem_neighborFinset v _).mpr hv3
      · exact (G.mem_neighborFinset v _).mpr hvx
    have hc := Finset.card_le_card hs
    have h4 : ({u₁, u₂, u₃, x} : Finset V).card = 4 := by
      simp [h12, h31.symm, h32.symm, Ne.symm hnot.1, Ne.symm hnot.2.1, Ne.symm hnot.2.2]
    rw [h4, G.card_neighborFinset_eq_degree, hC v] at hc
    omega
  have hcardW_eq : Fintype.card W + 1 = Fintype.card V := by
    rw [Fintype.card_subtype,
      show (Finset.univ.filter (fun x : V => x ≠ v)) = Finset.univ.erase v by ext z; simp]
    exact Finset.card_erase_add_one (Finset.mem_univ v)
  have hV4 : 4 ≤ Fintype.card V := by
    have := G.degree_lt_card_verts v; rw [hC v] at this; omega
  have hW2 : 2 ≤ Fintype.card W := by omega
  have hna_Gv : ¬ Gv.Adj a b := hnadj
  have hnear : Near H := by
    apply near_of_except H c3 hW2
    intro x hxc3
    by_cases hxa : x = a
    · subst hxa
      have hd1 := Erdos64Descent.degree_add_new_edge_left Gv a b hab hna_Gv
      have hd2 := induce_delete_degree G v a
      change Gv.degree a + (if G.Adj u₁ v then 1 else 0) = G.degree u₁ at hd2
      simp [h1, hC u₁] at hd2
      change H.degree a = Gv.degree a + 1 at hd1
      omega
    · by_cases hxb : x = b
      · subst hxb
        have hd1 := Erdos64Descent.degree_add_new_edge_right Gv a b hab hna_Gv
        have hd2 := induce_delete_degree G v b
        change Gv.degree b + (if G.Adj u₂ v then 1 else 0) = G.degree u₂ at hd2
        simp [h2.symm, hC u₂] at hd2
        change H.degree b = Gv.degree b + 1 at hd1
        omega
      · have hnotv : ¬ G.Adj x.1 v := by
          intro hxv
          rcases huniq_nbr x.1 hxv.symm with h | h | h
          · exact hxa (Subtype.ext h)
          · exact hxb (Subtype.ext h)
          · exact hxc3 (Subtype.ext h)
        have hd2 := induce_delete_degree G v x
        change Gv.degree x + (if G.Adj x.1 v then 1 else 0) = G.degree x.1 at hd2
        simp [hnotv, hC x.1] at hd2
        have hle : Gv.degree x ≤ H.degree x :=
          Gv.degree_le_of_le (v := x) (H := H) le_sup_left
        omega
  have hpow : HasPower H := hm.2.2.1 W H (by omega) hnear
  obtain ⟨k, p, hk, hp, hplen⟩ := mersenne_path_of_add_edge hab le_rfl hm.2.1 hpow
  have hle_ind : H \ SimpleGraph.edge a b ≤ Gv := by
    intro x y hxy
    rcases (SimpleGraph.sdiff_adj H (SimpleGraph.edge a b) x y).mp hxy with ⟨h1', h2'⟩
    rcases (SimpleGraph.sup_adj Gv (SimpleGraph.edge a b) x y).mp h1' with hg | he
    · exact hg
    · exact False.elim (h2' he)
  let pInd := p.mapLe hle_ind
  obtain ⟨c, hc, hclen, hm1, hm2⟩ := fermat_cycle_of_p3_and_mersenne h1 h2 hk pInd
    ((Walk.isPath_mapLe hle_ind).mpr hp) (by simpa [pInd] using hplen)
  exact ⟨k, c, hk, hc, hclen, hm1, hm2⟩

/-- NEW (Wave 3, Agent #6): Class S / H High-Degree Edge-Deletion Mersenne Path Theorem.
    In ANY MinimalBad(G) with defect w (deg w = 2, N(w) = {b1, b2}, ¬G.Adj b1 b2) and
    ANY edge xy with 4 ≤ deg x and x, y ≠ w, deleting w and edge xy still leaves a simple
    b1-b2 path of length 2^k - 1 (k ≥ 2). -/
theorem defect_edge_del_mersenne_path [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    {w b₁ b₂ x y : V} (hw : G.degree w = 2)
    (hb1 : G.Adj w b₁) (hb2 : G.Adj w b₂) (hb12 : b₁ ≠ b₂) (hnb : ¬ G.Adj b₁ b₂)
    (hxy : G.Adj x y) (hx4 : 4 ≤ G.degree x) (hxw : x ≠ w) (hyw : y ≠ w) :
    let W := {z : V // z ≠ w}
    let G0 := (G.induce {z | z ≠ w}) \ SimpleGraph.edge (⟨x, hxw⟩ : W) ⟨y, hyw⟩
    ∃ (k : ℕ) (p : G0.Walk ⟨b₁, (G.ne_of_adj hb1).symm⟩ ⟨b₂, (G.ne_of_adj hb2).symm⟩),
      2 ≤ k ∧ p.IsPath ∧ p.length + 1 = 2 ^ k := by
  classical
  intro W G0
  have hb1w : b₁ ≠ w := (G.ne_of_adj hb1).symm
  have hb2w : b₂ ≠ w := (G.ne_of_adj hb2).symm
  let a : W := ⟨b₁, hb1w⟩
  let b : W := ⟨b₂, hb2w⟩
  let xW : W := ⟨x, hxw⟩
  let yW : W := ⟨y, hyw⟩
  have hab : a ≠ b := fun h => hb12 (congrArg Subtype.val h)
  let Gv := G.induce {z | z ≠ w}
  let _ : DecidableRel Gv.Adj := inferInstanceAs (DecidableRel (G.induce {z | z ≠ w}).Adj)
  let _ : DecidableRel G0.Adj := inferInstanceAs (DecidableRel (Gv \ SimpleGraph.edge xW yW).Adj)
  let H := G0 ⊔ SimpleGraph.edge a b
  let _ : DecidableRel H.Adj := inferInstanceAs (DecidableRel (G0 ⊔ SimpleGraph.edge a b).Adj)
  obtain ⟨_, r, hr⟩ := hm.1
  have hrw : r = w := by
    by_contra hne; have := hr w (Ne.symm hne); omega
  subst r
  have huniq_w : ∀ z : V, G.Adj w z → z = b₁ ∨ z = b₂ := by
    intro z hwz
    by_contra hnot
    push Not at hnot
    have hs : ({b₁, b₂, z} : Finset V) ⊆ G.neighborFinset w := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · exact (G.mem_neighborFinset w _).mpr hb1
      · exact (G.mem_neighborFinset w _).mpr hb2
      · exact (G.mem_neighborFinset w _).mpr hwz
    have hc := Finset.card_le_card hs
    have h3 : ({b₁, b₂, z} : Finset V).card = 3 := by
      simp [hb12, Ne.symm hnot.1, Ne.symm hnot.2]
    rw [h3, G.card_neighborFinset_eq_degree, hw] at hc
    omega
  have hcardW_eq : Fintype.card W + 1 = Fintype.card V := by
    rw [Fintype.card_subtype,
      show (Finset.univ.filter (fun z : V => z ≠ w)) = Finset.univ.erase w by ext z; simp]
    exact Finset.card_erase_add_one (Finset.mem_univ w)
  have hV4 : 4 ≤ Fintype.card V := by
    have := G.degree_lt_card_verts x; omega
  have hW2 : 2 ≤ Fintype.card W := by omega
  have hxy_Gv : Gv.Adj xW yW := hxy
  have hna_G0 : ¬ G0.Adj a b := fun h => hnb ((SimpleGraph.sdiff_adj Gv _ a b).mp h).1
  have hnear : Near H := by
    apply near_of_except H yW hW2
    intro z hzy
    have hdeg_sdiff := erase_edge_degree Gv xW yW hxy_Gv z
    change G0.degree z + (if z = xW ∨ z = yW then 1 else 0) = Gv.degree z at hdeg_sdiff
    have hdeg_ind := induce_delete_degree G w z
    change Gv.degree z + (if G.Adj z.1 w then 1 else 0) = G.degree z.1 at hdeg_ind
    by_cases hza : z = a
    · subst hza
      have hd_add := Erdos64Descent.degree_add_new_edge_left G0 a b hab hna_G0
      change H.degree a = G0.degree a + 1 at hd_add
      change Gv.degree a + (if G.Adj b₁ w then 1 else 0) = G.degree b₁ at hdeg_ind
      simp [hb1.symm] at hdeg_ind
      have hda3 := hr b₁ hb1w
      by_cases hax : a = xW
      · have : b₁ = x := congrArg Subtype.val hax
        rw [this] at hdeg_ind; simp [hax] at hdeg_sdiff; omega
      · simp [hax, hzy] at hdeg_sdiff; omega
    · by_cases hzb : z = b
      · subst hzb
        have hd_add := Erdos64Descent.degree_add_new_edge_right G0 a b hab hna_G0
        change H.degree b = G0.degree b + 1 at hd_add
        change Gv.degree b + (if G.Adj b₂ w then 1 else 0) = G.degree b₂ at hdeg_ind
        simp [hb2.symm] at hdeg_ind
        have hdb3 := hr b₂ hb2w
        by_cases hbx : b = xW
        · have : b₂ = x := congrArg Subtype.val hbx
          rw [this] at hdeg_ind; simp [hbx] at hdeg_sdiff; omega
        · simp [hbx, hzy] at hdeg_sdiff; omega
      · have hnotw : ¬ G.Adj z.1 w := by
          intro hzw
          rcases huniq_w z.1 hzw.symm with h | h
          · exact hza (Subtype.ext h)
          · exact hzb (Subtype.ext h)
        simp [hnotw] at hdeg_ind
        have hle : G0.degree z ≤ H.degree z :=
          G0.degree_le_of_le (v := z) (H := H) le_sup_left
        by_cases hzx : z = xW
        · have : z.1 = x := congrArg Subtype.val hzx
          rw [this] at hdeg_ind; simp [hzx] at hdeg_sdiff; omega
        · simp [hzx, hzy] at hdeg_sdiff
          have hdz3 := hr z.1 z.2
          omega
  have hpow : HasPower H := hm.2.2.1 W H (by omega) hnear
  have hsub : H ≤ Gv ⊔ SimpleGraph.edge a b := sup_le_sup_right sdiff_le _
  obtain ⟨k, p, hk, hp, hplen⟩ := mersenne_path_of_add_edge hab hsub hm.2.1 hpow
  have hle_G0 : H \ SimpleGraph.edge a b ≤ G0 := by
    intro u1 u2 hu
    rcases (SimpleGraph.sdiff_adj H (SimpleGraph.edge a b) u1 u2).mp hu with ⟨h1', h2'⟩
    rcases (SimpleGraph.sup_adj G0 (SimpleGraph.edge a b) u1 u2).mp h1' with hg | he
    · exact hg
    · exact False.elim (h2' he)
  exact ⟨k, p.mapLe hle_G0, hk, (Walk.isPath_mapLe hle_G0).mpr hp, by simpa using hplen⟩

#print axioms mersenne_path_of_add_edge
#print axioms fermat_cycle_of_p3_and_mersenne
#print axioms cubic_p3_fermat_cycle
#print axioms defect_edge_del_mersenne_path

end E64P3Defect
