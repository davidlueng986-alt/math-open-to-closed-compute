import Core
import Leaves
import Descent
import Identification

/-!
Erdos 64 (Wave 3, Agent #6): No Bipartite Small-Cut Side & Odd-Cycle Transversal ≥ 2.
First Lean 4.36.0 formalization of Wave 1's flagship CUT obstructions (all finite orders,
standard axioms only):
1. `no_bipartite_small_cut_side`: In ANY MinimalBad(G), for EVERY subset S ⊆ V with
   2 ≤ |S| < |V|, ∀ v ∈ S, 3 ≤ deg_G(v), and |∂_G(S)| ≤ 3, the induced subgraph G[S]
   is NONBIPARTITE.
2. `cubic_odd_cycle_transversal_ge_two`: In EVERY cubic MinimalBad(G), for EVERY vertex v,
   the vertex-deleted graph G - v is NONBIPARTITE (τ_odd^v(G) ≥ 2).
-/

namespace E64CutObstructions
open SimpleGraph Erdos64Closure E64Core E64Leaves E64Identification
open scoped BigOperators
universe u

variable {V : Type u}

/-- Boundary edge count of a Finset `S : Finset V` in `G`. -/
def cutCount [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : ℕ :=
  ∑ v ∈ S, ((G.neighborFinset v) \ S).card

/-- Exact degree split: internal degree in `G.induce S` plus external neighbors equals `G.degree`. -/
theorem induce_finset_degree_add_ext [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : {x : V // x ∈ (S : Set V)}) :
    let H := G.induce (S : Set V)
    letI : DecidableRel H.Adj := inferInstanceAs (DecidableRel (G.induce (S : Set V)).Adj)
    H.degree v + ((G.neighborFinset v.1) \ S).card = G.degree v.1 := by
  classical
  intro H _
  let e : H.neighborSet v ≃ {x : V // x ∈ G.neighborFinset v.1 ∩ S} :=
    { toFun := fun u => ⟨u.1.1, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset v.1 u.1.1).mpr u.2, u.1.2⟩⟩
      invFun := fun u => ⟨⟨u.1, (Finset.mem_inter.mp u.2).2⟩, (G.mem_neighborFinset v.1 u.1).mp (Finset.mem_inter.mp u.2).1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc := Fintype.card_congr e
  rw [SimpleGraph.card_neighborSet_eq_degree, Fintype.card_coe] at hc
  rw [hc, ← G.card_neighborFinset_eq_degree]
  exact Finset.card_inter_add_card_sdiff (G.neighborFinset v.1) S

/-- Deleting a vertex `a ∈ S` changes `cutCount` by `- d_ext(a) + d_int(a)`. -/
theorem cutCount_erase [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) {a : V} (ha : a ∈ S) :
    cutCount G (S.erase a) + ((G.neighborFinset a) \ S).card =
      cutCount G S + ((G.neighborFinset a) ∩ S).card := by
  classical
  unfold cutCount
  have hsplit : ∑ v ∈ S, ((G.neighborFinset v) \ S).card =
      ((G.neighborFinset a) \ S).card + ∑ v ∈ S.erase a, ((G.neighborFinset v) \ S).card :=
    (Finset.add_sum_erase S (fun v => ((G.neighborFinset v) \ S).card) ha).symm
  rw [hsplit]
  have hstep : ∀ v ∈ S.erase a,
      ((G.neighborFinset v) \ (S.erase a)).card =
        ((G.neighborFinset v) \ S).card + (if G.Adj a v then 1 else 0) := by
    intro v hv
    by_cases hadj : G.Adj a v
    · have hmem : a ∈ G.neighborFinset v := (G.mem_neighborFinset v a).mpr hadj.symm
      have hnot : a ∉ (G.neighborFinset v) \ S := by simp [ha]
      have heq : (G.neighborFinset v) \ (S.erase a) = insert a ((G.neighborFinset v) \ S) := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
        by_cases hxa : x = a
        · subst hxa; simp [hmem, ha]
        · simp [hxa]
      rw [heq, Finset.card_insert_of_notMem hnot, if_pos hadj]
    · have hnot : a ∉ G.neighborFinset v := fun hm => hadj ((G.mem_neighborFinset v a).mp hm).symm
      have heq : (G.neighborFinset v) \ (S.erase a) = (G.neighborFinset v) \ S := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_erase]
        by_cases hxa : x = a
        · subst hxa; simp [hnot]
        · simp [hxa]
      rw [heq, if_neg hadj, add_zero]
  rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib]
  have hcount : (∑ v ∈ S.erase a, if G.Adj a v then (1 : ℕ) else 0) =
      ((G.neighborFinset a) ∩ S).card := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, smul_eq_mul, mul_one]
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨⟨_, hvS⟩, hadj⟩; exact ⟨hadj, hvS⟩
    · rintro ⟨hadj, hvS⟩; exact ⟨⟨(G.ne_of_adj hadj).symm, hvS⟩, hadj⟩
  rw [hcount]
  omega

/-- Parity of walks in a bipartite graph with coloring `color : W → Fin 2`. -/
theorem bip_walk_even_same_color {W : Type*} {H : SimpleGraph W} (color : W → Fin 2)
    (hc : ∀ u v, H.Adj u v → color u ≠ color v) {a b : W} (p : H.Walk a b)
    (heven : p.length % 2 = 0) : color a = color b := by
  have haux : ∀ {x y : W} (q : H.Walk x y),
      (q.length % 2 = 0 → color x = color y) ∧ (q.length % 2 = 1 → color x ≠ color y) := by
    intro x y q
    induction q with
    | nil => simp
    | @cons u v w huv r ih =>
      have hne := hc u v huv
      constructor <;> intro h
      · have h1 : r.length % 2 = 1 := by simp at h; omega
        have h2 := ih.2 h1
        have hu := (color u).isLt; have hv := (color v).isLt; have hw := (color w).isLt
        have hne' : (color u).val ≠ (color v).val := fun e => hne (Fin.ext e)
        have h2' : (color v).val ≠ (color w).val := fun e => h2 (Fin.ext e)
        exact Fin.ext (by omega)
      · have h0 : r.length % 2 = 0 := by simp at h; omega
        have h2 := ih.1 h0
        rw [← h2]; exact hne
  exact (haux p).1 heven

/-- Helper: `PowerFree` is equivalent to `¬HasPower`. -/
theorem powerFree_of_not_hasPower {W : Type*} {H : SimpleGraph W}
    (h : ¬ HasPower H) : Erdos64Descent.PowerFree H := by
  intro k v c hk hc hlen
  exact h ⟨k, v, c, hk, hc, hlen⟩

/-- NEW (Wave 3, Agent #6): No Bipartite Small-Cut Side Theorem.
    In ANY MinimalBad(G), for EVERY subset S ⊆ V with 2 ≤ |S| < |V|,
    every vertex in S having degree ≥ 3 in G, and cut size |∂(S)| ≤ 3,
    the induced subgraph G[S] is NONBIPARTITE. -/
theorem no_bipartite_small_cut_side [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (S : Finset V) (hS2 : 2 ≤ S.card) (hSlt : S.card < Fintype.card V)
    (hdeg3 : ∀ v ∈ S, 3 ≤ G.degree v) (hcut : cutCount G S ≤ 3)
    (color : {x : V // x ∈ (S : Set V)} → Fin 2)
    (hproper : ∀ a b : {x : V // x ∈ (S : Set V)},
      (G.induce (S : Set V)).Adj a b → color a ≠ color b) : False := by
  classical
  suffices hmain : ∀ m : ℕ, ∀ (T : Finset V), T.card = m →
      2 ≤ T.card → T.card < Fintype.card V →
      (∀ v ∈ T, 3 ≤ G.degree v) → cutCount G T ≤ 3 →
      ∀ (col : {x : V // x ∈ (T : Set V)} → Fin 2),
      (∀ a b, (G.induce (T : Set V)).Adj a b → col a ≠ col b) → False by
    exact hmain S.card S rfl hS2 hSlt hdeg3 hcut color hproper
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro T hTm hT2 hTlt hTdeg hTcut col hcol
    let W := {x : V // x ∈ (T : Set V)}
    let H := G.induce (T : Set V)
    letI : DecidableRel H.Adj := inferInstanceAs (DecidableRel (G.induce (T : Set V)).Adj)
    have hcardW : Fintype.card W = T.card := Fintype.card_coe T
    have hHfree : ¬ HasPower H := fun hp => hm.2.1 (power_induce G (T : Set V) hp)
    by_cases hlow : ∃ a : W, H.degree a ≤ 1
    · obtain ⟨a, ha1⟩ := hlow
      have haT : a.1 ∈ T := a.2
      have hsplit := induce_finset_degree_add_ext G T a
      change H.degree a + ((G.neighborFinset a.1) \ T).card = G.degree a.1 at hsplit
      have ha3 := hTdeg a.1 haT
      have hext2 : 2 ≤ ((G.neighborFinset a.1) \ T).card := by omega
      have hint1 : ((G.neighborFinset a.1) ∩ T).card ≤ 1 := by
        have := Finset.card_inter_add_card_sdiff (G.neighborFinset a.1) T
        rw [G.card_neighborFinset_eq_degree] at this
        omega
      let T' := T.erase a.1
      have hT'card : T'.card + 1 = T.card := Finset.card_erase_add_one haT
      have hT'cut : cutCount G T' ≤ 3 := by
        have hce := cutCount_erase G T haT
        omega
      have hT'2 : 2 ≤ T'.card := by
        by_contra hlt2
        have h1 : T'.card = 1 := by omega
        obtain ⟨b, hb⟩ := Finset.card_eq_one.mp h1
        have hbT : b ∈ T := Finset.mem_of_mem_erase (by rw [hb]; simp)
        have hba : b ≠ a.1 := (Finset.mem_erase.mp (by rw [hb]; simp)).1
        have hTeq : T = {a.1, b} := by
          ext x
          by_cases hxa : x = a.1
          · subst hxa; simp [haT]
          · have : x ∈ T' ↔ x ∈ T := by simp [T', hxa]
            rw [← this, hb]; simp [hxa]
        have hbdeg := hTdeg b hbT
        have hbint : ((G.neighborFinset b) ∩ T).card ≤ 1 := by
          have hsub : (G.neighborFinset b) ∩ T ⊆ {a.1} := by
            intro x hx
            rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, hTeq] at hx
            rcases Finset.mem_insert.mp hx.2 with rfl | hxb
            · simp
            · exact False.elim ((G.ne_of_adj hx.1) (Finset.mem_singleton.mp hxb).symm)
          exact (Finset.card_le_card hsub).trans (by simp)
        have hbext : 2 ≤ ((G.neighborFinset b) \ T).card := by
          have := Finset.card_inter_add_card_sdiff (G.neighborFinset b) T
          rw [G.card_neighborFinset_eq_degree] at this
          omega
        have hcut_ge4 : 4 ≤ cutCount G T := by
          unfold cutCount
          rw [hTeq, Finset.sum_pair hba.symm]
          omega
        omega
      exact ih T'.card (by omega) T' rfl hT'2 (by omega)
        (fun v hv => hTdeg v (Finset.mem_of_mem_erase hv)) hT'cut
        (fun x => col ⟨x.1, Finset.mem_of_mem_erase x.2⟩)
        (fun x y hxy => hcol ⟨x.1, Finset.mem_of_mem_erase x.2⟩
          ⟨y.1, Finset.mem_of_mem_erase y.2⟩ hxy)
    · push Not at hlow
      have hge2 : ∀ v : W, 2 ≤ H.degree v := fun v => by have := hlow v; omega
      let D : Finset W := Finset.univ.filter (fun v : W => H.degree v = 2)
      have hD_le3 : D.card ≤ 3 := by
        have hsum_ge : D.card ≤ ∑ v ∈ D, ((G.neighborFinset v.1) \ T).card := by
          have : D.card = ∑ _v ∈ D, (1 : ℕ) := by simp
          rw [this]
          apply Finset.sum_le_sum
          intro v hv
          have hv2 : H.degree v = 2 := (Finset.mem_filter.mp hv).2
          have hsp := induce_finset_degree_add_ext G T v
          change H.degree v + ((G.neighborFinset v.1) \ T).card = G.degree v.1 at hsp
          have hv3 := hTdeg v.1 v.2
          omega
        have hsum_le : ∑ v ∈ D, ((G.neighborFinset v.1) \ T).card ≤ cutCount G T := by
          have hle1 : ∑ v ∈ D, ((G.neighborFinset v.1) \ T).card ≤
              ∑ v : W, ((G.neighborFinset v.1) \ T).card :=
            Finset.sum_le_sum_of_subset (Finset.subset_univ D)
          have heq : ∑ v : W, ((G.neighborFinset v.1) \ T).card = cutCount G T := by
            unfold cutCount
            exact Finset.sum_coe_sort T (fun x => ((G.neighborFinset x) \ T).card)
          omega
        omega
      by_cases hD1 : D.card ≤ 1
      · have hnear : Near H := by
          by_cases hD0 : D = ∅
          · obtain ⟨w₀⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card W)
            apply near_of_except H w₀ (by omega)
            intro v _
            have hvnot : v ∉ D := by simp [hD0]
            have : H.degree v ≠ 2 := by simpa [D] using hvnot
            have := hge2 v; omega
          · obtain ⟨w₀, hw₀⟩ := Finset.nonempty_iff_ne_empty.mpr hD0
            apply near_of_except H w₀ (by omega)
            intro v hvw
            have hvnot : v ∉ D := by
              intro hvD
              have h2 : ({v, w₀} : Finset W).card ≤ D.card := by
                apply Finset.card_le_card
                intro z hz
                simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                rcases hz with rfl | rfl <;> assumption
              rw [Finset.card_pair hvw] at h2
              omega
            have : H.degree v ≠ 2 := by simpa [D] using hvnot
            have := hge2 v; omega
        exact hHfree (hm.2.2.1 W H (by omega) hnear)
      · by_cases hsame : ∃ a ∈ D, ∃ b ∈ D, a ≠ b ∧ col a = col b
        · obtain ⟨a, haD, b, hbD, hab, hcol_ab⟩ := hsame
          have hw_ex : ∃ w : W, ∀ x : W, x ≠ a → x ≠ b → x ≠ w → 3 ≤ H.degree x := by
            by_cases hrem : ∃ w ∈ D, w ≠ a ∧ w ≠ b
            · obtain ⟨w, hwD, hwa, hwb⟩ := hrem
              refine ⟨w, fun x hxa hxb hxw => ?_⟩
              have hxnot : x ∉ D := by
                intro hxD
                have h4 : ({a, b, w, x} : Finset W).card ≤ D.card := by
                  apply Finset.card_le_card
                  intro z hz
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                  rcases hz with rfl | rfl | rfl | rfl <;> assumption
                have hcard4 : ({a, b, w, x} : Finset W).card = 4 := by
                  simp [hab, hwa.symm, hwb.symm, hxa.symm, hxb.symm, hxw.symm]
                omega
              have : H.degree x ≠ 2 := by simpa [D] using hxnot
              have := hge2 x; omega
            · push Not at hrem
              refine ⟨a, fun x hxa hxb _ => ?_⟩
              have hxnot : x ∉ D := fun hxD => hrem x hxD hxa hxb
              have : H.degree x ≠ 2 := by simpa [D] using hxnot
              have := hge2 x; omega
          obtain ⟨w, hwrest⟩ := hw_ex
          have ha2 : H.degree a = 2 := (Finset.mem_filter.mp haD).2
          have hb2 : H.degree b = 2 := (Finset.mem_filter.mp hbD).2
          obtain ⟨hpf, hdeg_rep⟩ := Erdos64Descent.repair_two_same_color_ports
            H col hcol a b w hab hcol_ab ha2 hb2 hwrest (powerFree_of_not_hasPower hHfree)
          let H' := H ⊔ SimpleGraph.edge a b
          letI : DecidableRel H'.Adj := inferInstanceAs (DecidableRel (H ⊔ SimpleGraph.edge a b).Adj)
          have hnear' : Near H' := near_of_except H' w (by omega) hdeg_rep
          obtain ⟨k, v₀, c, hk, hc, hlen⟩ := hm.2.2.1 W H' (by omega) hnear'
          exact hpf k v₀ c hk hc hlen
        · push Not at hsame
          have hD2 : D.card = 2 := by
            have hle2 : D.card ≤ 2 := by
              have hinj : Set.InjOn col (D : Set W) := by
                intro x hx y hy hxy
                by_contra hne
                exact hsame x hx y hy hne hxy
              have hc := Finset.card_le_card_of_injOn col (fun x _ => Finset.mem_univ (col x)) hinj
              simpa using hc
            omega
          obtain ⟨a, b, hab, hDeq⟩ := Finset.card_eq_two.mp hD2
          have haD : a ∈ D := by rw [hDeq]; simp
          have hbD : b ∈ D := by rw [hDeq]; simp
          have hcol_ne : col a ≠ col b := hsame a haD b hbD hab
          let H' := identify H a b
          letI : DecidableRel H'.Adj := fun _ _ => Classical.dec _
          let X : {z : W // z ≠ b} := ⟨a, hab⟩
          have hnocom : ∀ u : W, ¬ (H.Adj a u ∧ H.Adj b u) := by
            rintro u ⟨hau, hbu⟩
            have h1 := hcol a u hau
            have h2 := hcol b u hbu
            have ha' := (col a).isLt; have hb' := (col b).isLt; have hu' := (col u).isLt
            have h1' : (col a).val ≠ (col u).val := fun e => h1 (Fin.ext e)
            have h2' : (col b).val ≠ (col u).val := fun e => h2 (Fin.ext e)
            exact hcol_ne (Fin.ext (by omega))
          have hcardH' : Fintype.card {z : W // z ≠ b} + 1 = Fintype.card W := by
            rw [Fintype.card_subtype,
              show (Finset.univ.filter (fun z : W => z ≠ b)) = Finset.univ.erase b by ext z; simp]
            exact Finset.card_erase_add_one (Finset.mem_univ b)
          have hW3 : 3 ≤ Fintype.card W := by
            have ha2 : H.degree a = 2 := (Finset.mem_filter.mp haD).2
            have := H.degree_lt_card_verts a
            omega
          have hnear' : Near H' := by
            apply near_of_except H' X (by omega)
            intro v hvX
            have hva : v.1 ≠ a := fun h => hvX (Subtype.ext h)
            have hvb : v.1 ≠ b := v.2
            have hvnotD : v.1 ∉ D := by rw [hDeq]; simp [hva, hvb]
            have hv3 : 3 ≤ H.degree v.1 := by
              have : H.degree v.1 ≠ 2 := by simpa [D] using hvnotD
              have := hge2 v.1; omega
            rw [identify_degree_other_of_not_common H hab v hva (hnocom v.1)]
            exact hv3
          have hpow' : HasPower H' := hm.2.2.1 _ H' (by omega) hnear'
          obtain ⟨k, p, hk, _, hplen⟩ := dyadic_path_of_identify hab hHfree hpow'
          have heven : p.length % 2 = 0 := by
            rw [hplen]
            cases k with
            | zero => omega
            | succ k => rw [pow_succ]; omega
          exact hcol_ne (bip_walk_even_same_color col hcol p heven)

/-- Corollary (Wave 3, Agent #6): Cubic Odd-Cycle Transversal ≥ 2 (τ_odd^v(G) ≥ 2).
    In EVERY cubic MinimalBad(G) and for EVERY vertex v, G - v is NONBIPARTITE. -/
theorem cubic_odd_cycle_transversal_ge_two [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G) (hC : Cubic G) (v : V)
    (color : {x : V // x ∈ ((Finset.univ.erase v : Finset V) : Set V)} → Fin 2)
    (hproper : ∀ a b, (G.induce ((Finset.univ.erase v : Finset V) : Set V)).Adj a b →
      color a ≠ color b) : False := by
  classical
  let S := Finset.univ.erase v
  have hV4 : 4 ≤ Fintype.card V := by
    have := G.degree_lt_card_verts v; rw [hC v] at this; omega
  have hScard : S.card + 1 = Fintype.card V := Finset.card_erase_add_one (Finset.mem_univ v)
  have hcut : cutCount G S ≤ 3 := by
    unfold cutCount
    have hstep : ∀ x ∈ S, ((G.neighborFinset x) \ S).card = if G.Adj v x then 1 else 0 := by
      intro x _
      by_cases h : G.Adj v x
      · have heq : (G.neighborFinset x) \ S = {v} := by
          ext y
          simp only [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset, Finset.mem_erase,
            Finset.mem_univ, and_true, Finset.mem_singleton, S]
          constructor
          · rintro ⟨_, hy⟩; by_contra hne; exact hy hne
          · rintro rfl; exact ⟨h.symm, fun hn => hn rfl⟩
        rw [heq, Finset.card_singleton, if_pos h]
      · have heq : (G.neighborFinset x) \ S = ∅ := by
          ext y
          simp only [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset, Finset.mem_erase,
            Finset.mem_univ, and_true, Finset.notMem_empty, iff_false, S]
          rintro ⟨hxy, hy⟩
          have hyv : y = v := by by_contra hne; exact hy hne
          exact h (hyv ▸ hxy.symm)
        rw [heq, Finset.card_empty, if_neg h]
    rw [Finset.sum_congr rfl hstep, ← Finset.sum_filter]
    simp only [Finset.sum_const, smul_eq_mul, mul_one]
    have hsub : S.filter (fun x => G.Adj v x) ⊆ G.neighborFinset v := by
      intro x hx
      exact (G.mem_neighborFinset v x).mpr (Finset.mem_filter.mp hx).2
    have hc := Finset.card_le_card hsub
    rw [G.card_neighborFinset_eq_degree, hC v] at hc
    exact hc
  exact no_bipartite_small_cut_side G hm S (by omega) (by omega)
    (fun x _ => by rw [hC x]) hcut color hproper

#print axioms cutCount_erase
#print axioms no_bipartite_small_cut_side
#print axioms cubic_odd_cycle_transversal_ge_two

end E64CutObstructions
