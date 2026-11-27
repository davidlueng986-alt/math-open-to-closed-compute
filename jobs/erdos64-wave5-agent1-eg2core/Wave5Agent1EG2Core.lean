import Mathlib

open SimpleGraph Finset

namespace E64Wave5Agent1EG2Core

/-!
# Wave 5 Agent #1 — All-Order Siege on `EG2-CORE` / `MinimalBad2` (Erdős Problem #64)

Self-contained Lean 4.36.0 formalization of 15 all-order structural reductions on `MinimalBad2` / `EG2-CORE`:
- Pillar I: Connectedness, bridgelessness (2-edge-connectivity), 2-vertex-connectivity (no cut vertex),
  and exact normal form of defect-separating 2-edge cuts (matching with 4 cubic endpoints).
- Pillar II: Local and global `V_3`–`V_{≥4}` exclusions (`v3_component_high_bottleneck`,
  `no_v3_all_high_neighbors`, `no_adjacent_two_high_disjoint`, `defect_neighbor_at_most_one_high`,
  `c4_free`, and global cubic density `6 |V_3| ≥ 4n - 5`).
- Pillar III: Universal defect-anchored dyadic paths (`∀ y ∉ {u} ∪ N(u)`),
  defect-pair contraction `Q = G / {u = v}` edge-robustness & neighbor-deletion robustness.
- Pillar IV: Nonbipartiteness of `G - u` (all cases: `dist(u,v) = 2` and `dist(u,v) ≥ 3`)
  and exact single-edge odd-transversal constraints.
-/

def IsPowerOfTwo (m : ℕ) : Prop :=
  ∃ k : ℕ, 2 ≤ k ∧ m = 2 ^ k

def HasPowerCycle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ IsPowerOfTwo p.length

def Near2 {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  (∀ x : V, 2 ≤ G.degree x) ∧ (Finset.univ.filter (fun x : V => G.degree x < 3)).card ≤ 2

def MinimalBad2 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  Near2 G ∧ ¬HasPowerCycle G ∧
    (∀ (m : ℕ), m < n → ∀ (H : SimpleGraph (Fin m)) [DecidableRel H.Adj],
      Near2 H → HasPowerCycle H) ∧
    (∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
      Near2 H → H.edgeFinset.card < G.edgeFinset.card → HasPowerCycle H)

/-- Directed cut edges leaving `S`. -/
def cutEdges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n)) :
    Finset (Fin n × Fin n) :=
  S.biUnion (fun x => ((G.neighborFinset x).filter (fun y => y ∉ S)).image (fun y => (x, y)))

def EG2Core {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) : Prop :=
  MinimalBad2 G ∧
  u ≠ v ∧
  ¬G.Adj u v ∧
  G.degree u = 2 ∧
  G.degree v = 2 ∧
  (∀ x : Fin n, x ≠ u → x ≠ v → 3 ≤ G.degree x) ∧
  (∀ x : Fin n, G.Adj u x ∨ G.Adj v x → G.degree x = 3) ∧
  (∀ x y : Fin n, 4 ≤ G.degree x → 4 ≤ G.degree y → ¬G.Adj x y) ∧
  (¬∃ c : Fin n → Bool, ∀ x y : Fin n, G.Adj x y → c x ≠ c y) ∧
  (∀ S : Finset (Fin n), 2 ≤ S.card → u ∉ S → v ∉ S → 3 ≤ (cutEdges G S).card)

lemma mem_cutEdges {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {S : Finset (Fin n)} {p : Fin n × Fin n} :
    p ∈ cutEdges G S ↔ p.1 ∈ S ∧ p.2 ∉ S ∧ G.Adj p.1 p.2 := by
  simp only [cutEdges, mem_biUnion, mem_image, mem_filter, mem_neighborFinset]
  constructor
  · rintro ⟨x, hx, y, ⟨hxy, hyS⟩, rfl⟩
    exact ⟨hx, hyS, hxy⟩
  · rintro ⟨hx, hy, hxy⟩
    exact ⟨p.1, hx, p.2, ⟨hxy, hy⟩, by cases p; rfl⟩

lemma cutEdges_symm_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) :
    (cutEdges G (Finset.univ \ S)).card = (cutEdges G S).card := by
  apply Finset.card_bij (fun p _ => (p.2, p.1))
  · intro p hp
    rw [mem_cutEdges] at hp ⊢
    rcases hp with ⟨h1, h2, hadj⟩
    simp only [mem_sdiff, mem_univ, true_and] at h1 h2
    exact ⟨by tauto, h1, hadj.symm⟩
  · intro p1 _ p2 _ h
    cases p1; cases p2; simp only [Prod.mk.injEq] at h; ext <;> [exact h.2; exact h.1]
  · intro p hp
    rw [mem_cutEdges] at hp
    refine ⟨(p.2, p.1), ?_, by cases p; rfl⟩
    rw [mem_cutEdges]
    simp only [mem_sdiff, mem_univ, true_and]
    exact ⟨hp.2.1, by simp [hp.1], hp.2.2.symm⟩

/-! ### Graph Homomorphism & Transfer Helpers -/

lemma walk_isCycle_map_inj {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hf : Function.Injective f) {v : V} {p : G.Walk v v} (hp : p.IsCycle) :
    (p.map f).IsCycle := by
  refine ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
  · rw [Walk.edges_map]
    exact hp.edges_nodup.map (Sym2.map.injective hf)
  · intro hnil
    exact hp.ne_nil (by cases p <;> simp_all)
  · rw [Walk.support_map]
    cases hsup : p.support with
    | nil => exact absurd hsup (Walk.support_ne_nil p)
    | cons a l =>
      have hnd : l.Nodup := by
        have := hp.support_nodup
        rw [hsup] at this
        exact this
      simpa using hnd.map hf

lemma hasPowerCycle_of_inj_hom {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hf : Function.Injective f) (hG : HasPowerCycle G) : HasPowerCycle H := by
  rcases hG with ⟨v, p, hp, hlen⟩
  refine ⟨f v, p.map f, walk_isCycle_map_inj f hf hp, ?_⟩
  simpa [Walk.length_map] using hlen

lemma comap_degree_equiv {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : W ≃ V) (w : W) :
    (G.comap e).degree w = G.degree (e w) := by
  simp only [← card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun x _ => e x)
  · intro x hx
    simp only [mem_neighborFinset, comap_adj] at hx ⊢
    exact hx
  · intro x _ y _ h; exact e.injective h
  · intro y hy
    simp only [mem_neighborFinset] at hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    simp only [mem_neighborFinset, comap_adj, e.apply_symm_apply]
    exact hy

lemma minimal_bad2_smaller_type {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hmin : MinimalBad2 G) {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : Fintype.card V < n) (hnear : Near2 H) : HasPowerCycle H := by
  let m := Fintype.card V
  let e : Fin m ≃ V := (Fintype.equivFin V).symm
  let H' : SimpleGraph (Fin m) := H.comap e
  have hnear' : Near2 H' := by
    refine ⟨fun i => ?_, ?_⟩
    · rw [comap_degree_equiv]; exact hnear.1 (e i)
    · have hbij : (Finset.univ.filter (fun i : Fin m => H'.degree i < 3)).card =
          (Finset.univ.filter (fun x : V => H.degree x < 3)).card := by
        apply Finset.card_bij (fun i _ => e i)
        · intro i hi
          simp only [mem_filter, mem_univ, true_and, comap_degree_equiv] at hi ⊢
          exact hi
        · intro i _ j _ h; exact e.injective h
        · intro x hx
          simp only [mem_filter, mem_univ, true_and] at hx
          refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
          simp only [mem_filter, mem_univ, true_and, comap_degree_equiv, e.apply_symm_apply]
          exact hx
      rw [hbij]
      exact hnear.2
  have hpow' : HasPowerCycle H' := hmin.2.2.1 m hcard H' hnear'
  exact hasPowerCycle_of_inj_hom ⟨e, fun h => h⟩ e.injective hpow'

lemma induced_no_power_cycle {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hnp : ¬HasPowerCycle G) (S : Finset (Fin n)) :
    ¬HasPowerCycle (G.induce (S : Set (Fin n))) := by
  intro hpow
  exact hnp (hasPowerCycle_of_inj_hom (SimpleGraph.Embedding.induce (S : Set (Fin n))).toHom
    Subtype.val_injective hpow)

lemma induce_degree_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (x : {a : Fin n // a ∈ (S : Set (Fin n))}) :
    (G.induce (S : Set (Fin n))).degree x = ((G.neighborFinset x.1).filter (· ∈ S)).card := by
  simp only [← card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun y _ => y.1)
  · intro y hy
    simp only [mem_neighborFinset, induce_adj, mem_filter] at hy ⊢
    exact ⟨hy, y.2⟩
  · intro y1 _ y2 _ h; exact Subtype.ext h
  · intro y hy
    simp only [mem_filter, mem_neighborFinset] at hy
    exact ⟨⟨y, hy.2⟩, by simp [mem_neighborFinset, induce_adj, hy.1], rfl⟩

lemma induce_card_lt {n : ℕ} (S : Finset (Fin n)) (hne : S ≠ Finset.univ) :
    Fintype.card {a : Fin n // a ∈ (S : Set (Fin n))} < n := by
  rw [Fintype.card_coe]
  have hlt : S.card < (Finset.univ : Finset (Fin n)).card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ S, hne⟩)
  simpa using hlt

lemma degree_split_cut {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (x : Fin n) :
    G.degree x = ((G.neighborFinset x).filter (· ∈ S)).card +
      ((G.neighborFinset x).filter (· ∉ S)).card := by
  rw [← card_neighborFinset_eq_degree]
  exact (Finset.filter_card_add_filter_neg_card_eq_card (s := G.neighborFinset x) (p := (· ∈ S))).symm

lemma card_out_neighbors_le_cutEdges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) {x : Fin n} (hx : x ∈ S) :
    ((G.neighborFinset x).filter (· ∉ S)).card ≤ (cutEdges G S).card := by
  calc ((G.neighborFinset x).filter (· ∉ S)).card
      = (((G.neighborFinset x).filter (· ∉ S)).image (fun y => (x, y))).card := by
        symm; exact Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2)
    _ ≤ (cutEdges G S).card := by
        apply Finset.card_le_card
        intro p hp
        simp only [mem_image, mem_filter, mem_neighborFinset] at hp
        rcases hp with ⟨y, ⟨hxy, hyS⟩, rfl⟩
        exact mem_cutEdges.mpr ⟨hx, hyS, hxy⟩

/-! ### Pillar I: Global Connectivity, Bridgelessness, 2-Connectivity, & 2-Cut Normal Form -/

/-- Theorem 1.1: Every `MinimalBad2` graph has no nontrivial 0-edge cut (connected). -/
theorem minimal_bad2_connected {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hmin : MinimalBad2 G) (S : Finset (Fin n)) (_hne : S.Nonempty) (hnu : S ≠ Finset.univ) :
    1 ≤ (cutEdges G S).card := by
  by_contra h0
  have hzero : (cutEdges G S).card = 0 := by omega
  have hdeg : ∀ x : {a : Fin n // a ∈ (S : Set (Fin n))},
      (G.induce (S : Set (Fin n))).degree x = G.degree x.1 := by
    intro x
    rw [induce_degree_eq]
    have hout : ((G.neighborFinset x.1).filter (· ∉ S)).card = 0 := by
      have := card_out_neighbors_le_cutEdges G S x.2
      omega
    have := degree_split_cut G S x.1
    omega
  have hnear : Near2 (G.induce (S : Set (Fin n))) := by
    refine ⟨fun x => by rw [hdeg x]; exact hmin.1.1 x.1, ?_⟩
    calc (Finset.univ.filter (fun x : {a : Fin n // a ∈ (S : Set (Fin n))} =>
            (G.induce (S : Set (Fin n))).degree x < 3)).card
        ≤ (Finset.univ.filter (fun x : Fin n => G.degree x < 3)).card := by
          apply Finset.card_le_card_of_injOn Subtype.val
          · intro x hx
            simp only [mem_coe, mem_filter, mem_univ, true_and] at hx ⊢
            rwa [← hdeg x]
          · intro x _ y _ h; exact Subtype.ext h
      _ ≤ 2 := hmin.1.2
  have hpow := minimal_bad2_smaller_type hmin (G.induce (S : Set (Fin n)))
    (induce_card_lt S hnu) hnear
  exact induced_no_power_cycle hmin.2.1 S hpow

/-- Theorem 1.2: Every `EG2Core` graph is 2-edge-connected (bridgeless). -/
theorem minimal_bad2_two_edge_connected {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u v : Fin n} (hcore : EG2Core G u v)
    (S : Finset (Fin n)) (hne : S.Nonempty) (hnu : S ≠ Finset.univ) :
    2 ≤ (cutEdges G S).card := by
  have hmin := hcore.1
  have hge1 := minimal_bad2_connected hmin S hne hnu
  by_contra hlt
  have h1 : (cutEdges G S).card = 1 := by omega
  rcases Finset.card_eq_one.mp h1 with ⟨⟨x, y⟩, hcut⟩
  have hxy_mem : (x, y) ∈ cutEdges G S := by rw [hcut]; simp
  rcases mem_cutEdges.mp hxy_mem with ⟨hxS, hyS, hxy⟩
  have honly : ∀ a ∈ S, ∀ b ∉ S, G.Adj a b → a = x ∧ b = y := by
    intro a ha b hb hab
    have hmem : (a, b) ∈ cutEdges G S := mem_cutEdges.mpr ⟨ha, hb, hab⟩
    rw [hcut, Finset.mem_singleton] at hmem
    exact Prod.mk.inj hmem
  have side_contra : ∀ (A : Finset (Fin n)) (z : Fin n),
      A ≠ Finset.univ → z ∈ A →
      (∀ a ∈ A, a ≠ z → ((G.neighborFinset a).filter (· ∉ A)).card = 0) →
      ((G.neighborFinset z).filter (· ∉ A)).card ≤ 1 →
      (u ∉ A ∨ v ∉ A) →
      (z ≠ u ∧ z ≠ v) → False := by
    intro A z hAnu _ hother hout huv hzn
    have hnearA : Near2 (G.induce (A : Set (Fin n))) := by
      refine ⟨fun a => ?_, ?_⟩
      · rw [induce_degree_eq]
        have hsp := degree_split_cut G A a.1
        by_cases haz : a.1 = z
        · subst haz
          have hdz : 3 ≤ G.degree a.1 := hcore.2.2.2.2.2.1 a.1 hzn.1 hzn.2
          omega
        · have := hother a.1 a.2 haz
          have := hmin.1.1 a.1
          omega
      · have hsub : Finset.univ.filter (fun a : {a : Fin n // a ∈ (A : Set (Fin n))} =>
            (G.induce (A : Set (Fin n))).degree a < 3) ⊆
            (Finset.univ.filter (fun a : {a : Fin n // a ∈ (A : Set (Fin n))} =>
              a.1 = u ∨ a.1 = v ∨ a.1 = z)) := by
          intro a ha
          simp only [mem_filter, mem_univ, true_and] at ha ⊢
          by_contra hnone
          push Not at hnone
          rw [induce_degree_eq] at ha
          have hsp := degree_split_cut G A a.1
          have ho := hother a.1 a.2 hnone.2.2
          have hd := hcore.2.2.2.2.2.1 a.1 hnone.1 hnone.2.1
          omega
        calc (Finset.univ.filter (fun a : {a : Fin n // a ∈ (A : Set (Fin n))} =>
                (G.induce (A : Set (Fin n))).degree a < 3)).card
            ≤ (Finset.univ.filter (fun a : {a : Fin n // a ∈ (A : Set (Fin n))} =>
                a.1 = u ∨ a.1 = v ∨ a.1 = z)).card := Finset.card_le_card hsub
          _ ≤ 2 := by
              rcases huv with huA | hvA
              · have hsub2 : Finset.univ.filter (fun a : {a : Fin n // a ∈ (A : Set (Fin n))} =>
                    a.1 = u ∨ a.1 = v ∨ a.1 = z) ⊆
                    (Finset.univ.filter (fun a : {a : Fin n // a ∈ (A : Set (Fin n))} =>
                      a.1 = v ∨ a.1 = z)) := by
                  intro a ha
                  simp only [mem_filter, mem_univ, true_and] at ha ⊢
                  rcases ha with h | h | h
                  · exact absurd (h ▸ a.2) huA
                  · exact Or.inl h
                  · exact Or.inr h
                calc _ ≤ (Finset.univ.filter (fun a : {a : Fin n // a ∈ (A : Set (Fin n))} =>
                          a.1 = v ∨ a.1 = z)).card := Finset.card_le_card hsub2
                  _ ≤ ({v, z} : Finset (Fin n)).card := by
                        apply Finset.card_le_card_of_injOn Subtype.val
                        · intro a ha; simp only [mem_coe, mem_filter, mem_univ, true_and] at ha
                          simp [ha]
                        · intro a _ b _ h; exact Subtype.ext h
                  _ ≤ 2 := Finset.card_le_two
              · have hsub2 : Finset.univ.filter (fun a : {a : Fin n // a ∈ (A : Set (Fin n))} =>
                    a.1 = u ∨ a.1 = v ∨ a.1 = z) ⊆
                    (Finset.univ.filter (fun a : {a : Fin n // a ∈ (A : Set (Fin n))} =>
                      a.1 = u ∨ a.1 = z)) := by
                  intro a ha
                  simp only [mem_filter, mem_univ, true_and] at ha ⊢
                  rcases ha with h | h | h
                  · exact Or.inl h
                  · exact absurd (h ▸ a.2) hvA
                  · exact Or.inr h
                calc _ ≤ (Finset.univ.filter (fun a : {a : Fin n // a ∈ (A : Set (Fin n))} =>
                          a.1 = u ∨ a.1 = z)).card := Finset.card_le_card hsub2
                  _ ≤ ({u, z} : Finset (Fin n)).card := by
                        apply Finset.card_le_card_of_injOn Subtype.val
                        · intro a ha; simp only [mem_coe, mem_filter, mem_univ, true_and] at ha
                          simp [ha]
                        · intro a _ b _ h; exact Subtype.ext h
                  _ ≤ 2 := Finset.card_le_two
    exact induced_no_power_cycle hmin.2.1 A
      (minimal_bad2_smaller_type hmin (G.induce (A : Set (Fin n))) (induce_card_lt A hAnu) hnearA)
  have delete_defect_side : ∀ (A : Finset (Fin n)) (w : Fin n),
      w ∈ A → G.degree w = 2 →
      (∀ a ∈ A, a ≠ w → ((G.neighborFinset a).filter (· ∉ A)).card = 0) →
      ((G.neighborFinset w).filter (· ∉ A)).card = 1 →
      (∀ a ∈ A, a ≠ w → 3 ≤ G.degree a) → False := by
    intro A w _ hdw hother hout hall3
    let A' := A.erase w
    have hA'nu : A' ≠ Finset.univ := by
      intro h; have : w ∈ A' := by rw [h]; simp
      exact Finset.notMem_erase w A this
    have hspw := degree_split_cut G A w
    have hin_card : ((G.neighborFinset w).filter (· ∈ A)).card = 1 := by omega
    rcases Finset.card_eq_one.mp hin_card with ⟨a0, ha0⟩
    have ha0_mem : a0 ∈ (G.neighborFinset w).filter (· ∈ A) := by rw [ha0]; simp
    simp only [mem_filter, mem_neighborFinset] at ha0_mem
    have hnearA' : Near2 (G.induce (A' : Set (Fin n))) := by
      refine ⟨fun a => ?_, ?_⟩
      · rw [induce_degree_eq]
        have haA : a.1 ∈ A := Finset.mem_of_mem_erase a.2
        have haw : a.1 ≠ w := Finset.ne_of_mem_erase a.2
        have hoA := hother a.1 haA haw
        have hsp := degree_split_cut G A a.1
        have hda : 3 ≤ G.degree a.1 := hall3 a.1 haA haw
        have hcard_er : ((G.neighborFinset a.1).filter (· ∈ A)).card ≤
            ((G.neighborFinset a.1).filter (· ∈ A')).card + 1 := by
          have hsub : (G.neighborFinset a.1).filter (· ∈ A) ⊆
              insert w ((G.neighborFinset a.1).filter (· ∈ A')) := by
            intro z hz
            simp only [mem_filter, mem_neighborFinset] at hz
            by_cases hzw : z = w
            · simp [hzw]
            · exact Finset.mem_insert_of_mem (by simp [A', hz.1, hz.2, hzw])
          calc ((G.neighborFinset a.1).filter (· ∈ A)).card
              ≤ (insert w ((G.neighborFinset a.1).filter (· ∈ A'))).card := Finset.card_le_card hsub
            _ ≤ ((G.neighborFinset a.1).filter (· ∈ A')).card + 1 := Finset.card_insert_le _ _
        omega
      · have hsub : Finset.univ.filter (fun a : {a : Fin n // a ∈ (A' : Set (Fin n))} =>
            (G.induce (A' : Set (Fin n))).degree a < 3) ⊆
            (Finset.univ.filter (fun a : {a : Fin n // a ∈ (A' : Set (Fin n))} => a.1 = a0)) := by
          intro a ha
          simp only [mem_filter, mem_univ, true_and] at ha ⊢
          by_contra hna0
          rw [induce_degree_eq] at ha
          have haA : a.1 ∈ A := Finset.mem_of_mem_erase a.2
          have haw : a.1 ≠ w := Finset.ne_of_mem_erase a.2
          have hnotadj : ¬G.Adj w a.1 := by
            intro hadj
            have hmem : a.1 ∈ (G.neighborFinset w).filter (· ∈ A) := by
              simp [mem_filter, mem_neighborFinset, hadj, haA]
            rw [ha0, Finset.mem_singleton] at hmem
            exact hna0 hmem
          have heq : (G.neighborFinset a.1).filter (· ∈ A') = (G.neighborFinset a.1).filter (· ∈ A) := by
            ext z; simp only [mem_filter, mem_neighborFinset, A', mem_erase]
            constructor
            · rintro ⟨h1, _, h2⟩; exact ⟨h1, h2⟩
            · rintro ⟨h1, h2⟩
              exact ⟨h1, fun hzw => hnotadj (hzw ▸ h1.symm), h2⟩
          rw [heq] at ha
          have hoA := hother a.1 haA haw
          have hsp := degree_split_cut G A a.1
          have hda : 3 ≤ G.degree a.1 := hall3 a.1 haA haw
          omega
        calc (Finset.univ.filter (fun a : {a : Fin n // a ∈ (A' : Set (Fin n))} =>
                (G.induce (A' : Set (Fin n))).degree a < 3)).card
            ≤ (Finset.univ.filter (fun a : {a : Fin n // a ∈ (A' : Set (Fin n))} => a.1 = a0)).card :=
              Finset.card_le_card hsub
          _ ≤ ({a0} : Finset (Fin n)).card := by
              apply Finset.card_le_card_of_injOn Subtype.val
              · intro a ha; simp only [mem_coe, mem_filter, mem_univ, true_and] at ha; simp [ha]
              · intro a _ b _ h; exact Subtype.ext h
          _ ≤ 2 := by simp
    exact induced_no_power_cycle hmin.2.1 A'
      (minimal_bad2_smaller_type hmin (G.induce (A' : Set (Fin n))) (induce_card_lt A' hA'nu) hnearA')
  let T := Finset.univ \ S
  have hTnu : T ≠ Finset.univ := by
    intro h; rcases hne with ⟨a, ha⟩
    have : a ∈ T := by rw [h]; simp
    simp [T, ha] at this
  have hyT : y ∈ T := by simp [T, hyS]
  have hotherS : ∀ a ∈ S, a ≠ x → ((G.neighborFinset a).filter (· ∉ S)).card = 0 := by
    intro a ha hax
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro b hb hbnS
    rw [mem_neighborFinset] at hb
    exact hax (honly a ha b hbnS hb).1
  have houtS : ((G.neighborFinset x).filter (· ∉ S)).card = 1 := by
    have hle := card_out_neighbors_le_cutEdges G S hxS
    have hpos : 1 ≤ ((G.neighborFinset x).filter (· ∉ S)).card :=
      Finset.card_pos.mpr ⟨y, by simp [mem_filter, mem_neighborFinset, hxy, hyS]⟩
    omega
  have hotherT : ∀ b ∈ T, b ≠ y → ((G.neighborFinset b).filter (· ∉ T)).card = 0 := by
    intro b hb hby
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro a ha hanT
    rw [mem_neighborFinset] at ha
    simp only [T, mem_sdiff, mem_univ, true_and, not_not] at hb hanT
    exact hby (honly a hanT b hb ha.symm).2
  have houtT : ((G.neighborFinset y).filter (· ∉ T)).card = 1 := by
    have hct : (cutEdges G T).card = 1 := by rw [cutEdges_symm_card, h1]
    have hle := card_out_neighbors_le_cutEdges G T hyT
    have hpos : 1 ≤ ((G.neighborFinset y).filter (· ∉ T)).card :=
      Finset.card_pos.mpr ⟨x, by simp [T, mem_filter, mem_neighborFinset, hxy.symm, hxS]⟩
    omega
  by_cases huS : u ∈ S <;> by_cases hvS : v ∈ S
  · have hyn : y ≠ u ∧ y ≠ v := ⟨fun h => hyS (h ▸ huS), fun h => hyS (h ▸ hvS)⟩
    exact side_contra T y hTnu hyT hotherT (by omega) (Or.inl (by simp [T, huS])) hyn
  · by_cases hxu : x = u
    · subst hxu
      exact delete_defect_side S x hxS hcore.2.2.2.1 hotherS houtS
        (fun a ha hax => hcore.2.2.2.2.2.1 a hax (fun h => hvS (h ▸ ha)))
    · have hxn : x ≠ u ∧ x ≠ v := ⟨hxu, fun h => hvS (h ▸ hxS)⟩
      exact side_contra S x hnu hxS hotherS (by omega) (Or.inr hvS) hxn
  · by_cases hxv : x = v
    · subst hxv
      exact delete_defect_side S x hxS hcore.2.2.2.2.1 hotherS houtS
        (fun a ha hax => hcore.2.2.2.2.2.1 a (fun h => huS (h ▸ ha)) hax)
    · have hxn : x ≠ u ∧ x ≠ v := ⟨fun h => huS (h ▸ hxS), hxv⟩
      exact side_contra S x hnu hxS hotherS (by omega) (Or.inl huS) hxn
  · have hxn : x ≠ u ∧ x ≠ v := ⟨fun h => huS (h ▸ hxS), fun h => hvS (h ▸ hxS)⟩
    exact side_contra S x hnu hxS hotherS (by omega) (Or.inl huS) hxn

/-- Theorem 1.3: Every `EG2Core` graph is 2-vertex-connected (no cut vertex). -/
theorem minimal_bad2_two_connected {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u v : Fin n} (hcore : EG2Core G u v)
    (c : Fin n) (A B : Finset (Fin n))
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hdisj : Disjoint A B) (hcA : c ∉ A) (hcB : c ∉ B)
    (hcov : A ∪ B = Finset.univ.erase c) :
    ∃ a ∈ A, ∃ b ∈ B, G.Adj a b := by
  by_contra hno
  push Not at hno
  have hmin := hcore.1
  have hA_to_c : ∀ a ∈ A, ∀ z ∉ A, G.Adj a z → z = c := by
    intro a ha z hzA haz
    by_contra hzc
    have hz_er : z ∈ Finset.univ.erase c := Finset.mem_erase.mpr ⟨hzc, Finset.mem_univ z⟩
    rw [← hcov, Finset.mem_union] at hz_er
    rcases hz_er with h | h
    · exact hzA h
    · exact hno a ha z h haz
  have hB_to_c : ∀ b ∈ B, ∀ z ∉ B, G.Adj b z → z = c := by
    intro b hb z hzB hbz
    by_contra hzc
    have hz_er : z ∈ Finset.univ.erase c := Finset.mem_erase.mpr ⟨hzc, Finset.mem_univ z⟩
    rw [← hcov, Finset.mem_union] at hz_er
    rcases hz_er with h | h
    · exact hno z h b hb hbz.symm
    · exact hzB h
  have hAnu : A ≠ Finset.univ := fun h => hcA (by rw [h]; simp)
  have hBnu : B ≠ Finset.univ := fun h => hcB (by rw [h]; simp)
  have hcutA : 2 ≤ (cutEdges G A).card := minimal_bad2_two_edge_connected hcore A hAne hAnu
  have hcutB : 2 ≤ (cutEdges G B).card := minimal_bad2_two_edge_connected hcore B hBne hBnu
  have hcA_deg : 2 ≤ ((G.neighborFinset c).filter (· ∈ A)).card := by
    calc 2 ≤ (cutEdges G A).card := hcutA
      _ ≤ ((G.neighborFinset c).filter (· ∈ A)).card := by
        apply Finset.card_le_card_of_injOn Prod.fst
        · intro p hp
          rw [mem_coe, mem_cutEdges] at hp
          have hp2 : p.2 = c := hA_to_c p.1 hp.1 p.2 hp.2.1 hp.2.2
          simp [mem_filter, mem_neighborFinset, hp2 ▸ hp.2.2.symm, hp.1]
        · intro p1 hp1 p2 hp2 hfst
          rw [mem_coe, mem_cutEdges] at hp1 hp2
          have h1 := hA_to_c p1.1 hp1.1 p1.2 hp1.2.1 hp1.2.2
          have h2 := hA_to_c p2.1 hp2.1 p2.2 hp2.2.1 hp2.2.2
          exact Prod.ext hfst (h1.trans h2.symm)
  have hcB_deg : 2 ≤ ((G.neighborFinset c).filter (· ∈ B)).card := by
    calc 2 ≤ (cutEdges G B).card := hcutB
      _ ≤ ((G.neighborFinset c).filter (· ∈ B)).card := by
        apply Finset.card_le_card_of_injOn Prod.fst
        · intro p hp
          rw [mem_coe, mem_cutEdges] at hp
          have hp2 : p.2 = c := hB_to_c p.1 hp.1 p.2 hp.2.1 hp.2.2
          simp [mem_filter, mem_neighborFinset, hp2 ▸ hp.2.2.symm, hp.1]
        · intro p1 hp1 p2 hp2 hfst
          rw [mem_coe, mem_cutEdges] at hp1 hp2
          have h1 := hB_to_c p1.1 hp1.1 p1.2 hp1.2.1 hp1.2.2
          have h2 := hB_to_c p2.1 hp2.1 p2.2 hp2.2.1 hp2.2.2
          exact Prod.ext hfst (h1.trans h2.symm)
  have hc_deg4 : 4 ≤ G.degree c := by
    have hdisj_nb : Disjoint ((G.neighborFinset c).filter (· ∈ A))
        ((G.neighborFinset c).filter (· ∈ B)) := Finset.disjoint_filter_filter hdisj
    have hsub : ((G.neighborFinset c).filter (· ∈ A)) ∪ ((G.neighborFinset c).filter (· ∈ B)) ⊆
        G.neighborFinset c :=
      Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj_nb, card_neighborFinset_eq_degree] at hcard
    omega
  have hcu : c ≠ u := fun h => by have := hcore.2.2.2.1; subst h; omega
  have hcv : c ≠ v := fun h => by have := hcore.2.2.2.2.1; subst h; omega
  have kill_side : ∀ (S : Finset (Fin n)),
      (insert c S) ≠ Finset.univ →
      (∀ s ∈ S, ∀ z ∉ S, G.Adj s z → z = c) →
      2 ≤ ((G.neighborFinset c).filter (· ∈ S)).card →
      (u ∉ S ∨ v ∉ S) → False := by
    intro S hSnu hSto hcd huv
    let Sc := insert c S
    have hnearS : Near2 (G.induce (Sc : Set (Fin n))) := by
      refine ⟨fun x => ?_, ?_⟩
      · rw [induce_degree_eq]
        by_cases hxc : x.1 = c
        · subst hxc
          have hsub : (G.neighborFinset x.1).filter (· ∈ S) ⊆ (G.neighborFinset x.1).filter (· ∈ Sc) :=
            Finset.filter_subset_filter _ (Finset.subset_insert _ _)
          exact le_trans hcd (Finset.card_le_card hsub)
        · have hxS : x.1 ∈ S := (Finset.mem_insert.mp x.2).resolve_left hxc
          have heq : (G.neighborFinset x.1).filter (· ∈ Sc) = G.neighborFinset x.1 := by
            ext z; simp only [mem_filter, mem_neighborFinset, Sc, mem_insert, and_iff_left_iff_imp]
            intro hxz
            by_cases hzS : z ∈ S
            · exact Or.inr hzS
            · exact Or.inl (hSto x.1 hxS z hzS hxz)
          rw [heq, card_neighborFinset_eq_degree]
          exact hmin.1.1 x.1
      · have hsub : Finset.univ.filter (fun x : {a : Fin n // a ∈ (Sc : Set (Fin n))} =>
            (G.induce (Sc : Set (Fin n))).degree x < 3) ⊆
            (Finset.univ.filter (fun x : {a : Fin n // a ∈ (Sc : Set (Fin n))} =>
              x.1 = u ∨ x.1 = v ∨ x.1 = c)) := by
          intro x hx
          simp only [mem_filter, mem_univ, true_and] at hx ⊢
          by_contra hnone; push Not at hnone
          rw [induce_degree_eq] at hx
          have hxS : x.1 ∈ S := (Finset.mem_insert.mp x.2).resolve_left hnone.2.2
          have heq : (G.neighborFinset x.1).filter (· ∈ Sc) = G.neighborFinset x.1 := by
            ext z; simp only [mem_filter, mem_neighborFinset, Sc, mem_insert, and_iff_left_iff_imp]
            intro hxz
            by_cases hzS : z ∈ S
            · exact Or.inr hzS
            · exact Or.inl (hSto x.1 hxS z hzS hxz)
          rw [heq, card_neighborFinset_eq_degree] at hx
          have := hcore.2.2.2.2.2.1 x.1 hnone.1 hnone.2.1
          omega
        calc _ ≤ (Finset.univ.filter (fun x : {a : Fin n // a ∈ (Sc : Set (Fin n))} =>
                  x.1 = u ∨ x.1 = v ∨ x.1 = c)).card := Finset.card_le_card hsub
          _ ≤ 2 := by
              rcases huv with huS | hvS
              · have huSc : u ∉ Sc := fun h => by
                  rcases Finset.mem_insert.mp h with h1 | h2
                  · exact hcu h1.symm
                  · exact huS h2
                have hsub2 : Finset.univ.filter (fun x : {a : Fin n // a ∈ (Sc : Set (Fin n))} =>
                    x.1 = u ∨ x.1 = v ∨ x.1 = c) ⊆
                    (Finset.univ.filter (fun x : {a : Fin n // a ∈ (Sc : Set (Fin n))} =>
                      x.1 = v ∨ x.1 = c)) := by
                  intro x hx; simp only [mem_filter, mem_univ, true_and] at hx ⊢
                  rcases hx with h | h | h
                  · exact absurd (h ▸ x.2) huSc
                  · exact Or.inl h
                  · exact Or.inr h
                calc _ ≤ (Finset.univ.filter (fun x : {a : Fin n // a ∈ (Sc : Set (Fin n))} =>
                          x.1 = v ∨ x.1 = c)).card := Finset.card_le_card hsub2
                  _ ≤ ({v, c} : Finset (Fin n)).card := by
                        apply Finset.card_le_card_of_injOn Subtype.val
                        · intro x hx; simp only [mem_coe, mem_filter, mem_univ, true_and] at hx; simp [hx]
                        · intro x _ y _ h; exact Subtype.ext h
                  _ ≤ 2 := Finset.card_le_two
              · have hvSc : v ∉ Sc := fun h => by
                  rcases Finset.mem_insert.mp h with h1 | h2
                  · exact hcv h1.symm
                  · exact hvS h2
                have hsub2 : Finset.univ.filter (fun x : {a : Fin n // a ∈ (Sc : Set (Fin n))} =>
                    x.1 = u ∨ x.1 = v ∨ x.1 = c) ⊆
                    (Finset.univ.filter (fun x : {a : Fin n // a ∈ (Sc : Set (Fin n))} =>
                      x.1 = u ∨ x.1 = c)) := by
                  intro x hx; simp only [mem_filter, mem_univ, true_and] at hx ⊢
                  rcases hx with h | h | h
                  · exact Or.inl h
                  · exact absurd (h ▸ x.2) hvSc
                  · exact Or.inr h
                calc _ ≤ (Finset.univ.filter (fun x : {a : Fin n // a ∈ (Sc : Set (Fin n))} =>
                          x.1 = u ∨ x.1 = c)).card := Finset.card_le_card hsub2
                  _ ≤ ({u, c} : Finset (Fin n)).card := by
                        apply Finset.card_le_card_of_injOn Subtype.val
                        · intro x hx; simp only [mem_coe, mem_filter, mem_univ, true_and] at hx; simp [hx]
                        · intro x _ y _ h; exact Subtype.ext h
                  _ ≤ 2 := Finset.card_le_two
    exact induced_no_power_cycle hmin.2.1 Sc
      (minimal_bad2_smaller_type hmin (G.induce (Sc : Set (Fin n))) (induce_card_lt Sc hSnu) hnearS)
  have hAc_nu : insert c A ≠ Finset.univ := by
    intro h; rcases hBne with ⟨b, hb⟩
    have hb_in : b ∈ insert c A := by rw [h]; simp
    rcases Finset.mem_insert.mp hb_in with hbc | hbA
    · exact hcB (hbc ▸ hb)
    · exact Finset.disjoint_left.mp hdisj hbA hb
  have hBc_nu : insert c B ≠ Finset.univ := by
    intro h; rcases hAne with ⟨a, ha⟩
    have ha_in : a ∈ insert c B := by rw [h]; simp
    rcases Finset.mem_insert.mp ha_in with hac | haB
    · exact hcA (hac ▸ ha)
    · exact Finset.disjoint_left.mp hdisj ha haB
  by_cases huA : u ∈ A
  · have huB : u ∉ B := Finset.disjoint_left.mp hdisj huA
    exact kill_side B hBc_nu hB_to_c hcB_deg (Or.inl huB)
  · exact kill_side A hAc_nu hA_to_c hcA_deg (Or.inl huA)

/-- Theorem 1.4: Defect-separating 2-edge cut normal form in `EG2Core`.
Every nontrivial 2-edge cut separates `u` and `v`, avoids `u, v`, is a matching,
and has all four endpoints of degree exactly 3. -/
theorem minimal_bad2_two_cut_normal_form {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u v : Fin n} (hcore : EG2Core G u v)
    (S : Finset (Fin n)) (hS2 : 2 ≤ S.card) (hT2 : 2 ≤ (Finset.univ \ S).card)
    (hcut2 : (cutEdges G S).card = 2) :
    ((u ∈ S ∧ v ∉ S) ∨ (v ∈ S ∧ u ∉ S)) ∧
    ∀ p ∈ cutEdges G S,
      p.1 ≠ u ∧ p.1 ≠ v ∧ p.2 ≠ u ∧ p.2 ≠ v ∧
      G.degree p.1 = 3 ∧ G.degree p.2 = 3 ∧
      (∀ q ∈ cutEdges G S, q ≠ p → q.1 ≠ p.1 ∧ q.2 ≠ p.2) := by
  have hmin := hcore.1
  have hsep : (u ∈ S ∧ v ∉ S) ∨ (v ∈ S ∧ u ∉ S) := by
    by_contra hns; push Not at hns
    by_cases huS : u ∈ S
    · have hvS : v ∈ S := hns.1 huS
      have hge3 := hcore.2.2.2.2.2.2.2.2.2 (Finset.univ \ S) hT2 (by simp [huS]) (by simp [hvS])
      have hsym := cutEdges_symm_card G S
      omega
    · have hvS : v ∉ S := fun hv => (hns.2 hv) huS
      have hge3 := hcore.2.2.2.2.2.2.2.2.2 S hS2 huS hvS
      omega
  refine ⟨hsep, ?_⟩
  have side_props : ∀ (A : Finset (Fin n)) (w w' : Fin n),
      2 ≤ A.card → A ≠ Finset.univ →
      w ∈ A → w' ∉ A →
      ({w, w'} : Finset (Fin n)) = {u, v} →
      (cutEdges G A).card = 2 →
      ∀ p ∈ cutEdges G A,
        p.1 ≠ u ∧ p.1 ≠ v ∧ G.degree p.1 = 3 ∧
        (∀ q ∈ cutEdges G A, q ≠ p → q.1 ≠ p.1) := by
    intro A w w' hA2 hAnu hwA hw'A hww' hcutA
    have hw_deg2 : G.degree w = 2 := by
      have : w ∈ ({u, v} : Finset (Fin n)) := hww' ▸ (by simp)
      rcases Finset.mem_insert.mp this with rfl | h
      · exact hcore.2.2.2.1
      · rw [Finset.mem_singleton.mp h]; exact hcore.2.2.2.2.1
    have hother_deg3 : ∀ z ∈ A, z ≠ w → 3 ≤ G.degree z := by
      intro z hzA hzw
      have hz_ne_w' : z ≠ w' := fun h => hw'A (h ▸ hzA)
      have hz_not : z ∉ ({u, v} : Finset (Fin n)) := by rw [← hww']; simp [hzw, hz_ne_w']
      exact hcore.2.2.2.2.2.1 z (fun h => hz_not (by simp [h])) (fun h => hz_not (by simp [h]))
    have hall_ne_w : ∀ r ∈ cutEdges G A, r.1 ≠ w := by
      intro r hr hrw
      rcases mem_cutEdges.mp hr with ⟨_, hr2nA, hr_adj⟩
      let A' := A.erase w
      have hA'card : A'.card = A.card - 1 := Finset.card_erase_of_mem hwA
      have hw_out_le : ((G.neighborFinset w).filter (· ∉ A)).card ≤ 2 := by
        have := card_out_neighbors_le_cutEdges G A hwA; omega
      have hw_out_ge : 1 ≤ ((G.neighborFinset w).filter (· ∉ A)).card :=
        Finset.card_pos.mpr ⟨r.2, by simp [mem_filter, mem_neighborFinset, hrw ▸ hr_adj, hr2nA]⟩
      have hspw := degree_split_cut G A w
      by_cases hwout2 : ((G.neighborFinset w).filter (· ∉ A)).card = 2
      · have hwin0 : ((G.neighborFinset w).filter (· ∈ A)).card = 0 := by omega
        have hA'ne : A'.Nonempty := Finset.card_pos.mp (by omega)
        have hA'nu : A' ≠ Finset.univ := fun h => Finset.notMem_erase w A (by rw [h]; simp)
        have hcutA'0 : (cutEdges G A').card = 0 := by
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro q hq
          rcases mem_cutEdges.mp hq with ⟨hq1, hq2, hqadj⟩
          have hq1A : q.1 ∈ A := Finset.mem_of_mem_erase hq1
          have hq1w : q.1 ≠ w := Finset.ne_of_mem_erase hq1
          by_cases hq2w : q.2 = w
          · have : q.1 ∈ (G.neighborFinset w).filter (· ∈ A) := by
              simp [mem_filter, mem_neighborFinset, hq2w ▸ hqadj.symm, hq1A]
            have hpos := Finset.card_pos.mpr ⟨q.1, this⟩
            omega
          · have hq2nA : q.2 ∉ A := fun h => hq2 (Finset.mem_erase.mpr ⟨hq2w, h⟩)
            have hq_mem : q ∈ cutEdges G A := mem_cutEdges.mpr ⟨hq1A, hq2nA, hqadj⟩
            have hw_cut : ((G.neighborFinset w).filter (· ∉ A)).image (fun y => (w, y)) ⊆ cutEdges G A := by
              intro s hs
              simp only [mem_image, mem_filter, mem_neighborFinset] at hs
              rcases hs with ⟨y, ⟨hwy, hynA⟩, rfl⟩
              exact mem_cutEdges.mpr ⟨hwA, hynA, hwy⟩
            have hcard_eq : (((G.neighborFinset w).filter (· ∉ A)).image (fun y => (w, y))).card =
                (cutEdges G A).card := by
              rw [Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2), hwout2, hcutA]
            have heq := Finset.eq_of_subset_of_card_le hw_cut (le_of_eq hcard_eq.symm)
            rw [← heq] at hq_mem
            simp only [mem_image] at hq_mem
            rcases hq_mem with ⟨y, _, hyq⟩
            exact hq1w (congrArg Prod.fst hyq).symm
        have := minimal_bad2_connected hmin A' hA'ne hA'nu
        omega
      · have hwout1 : ((G.neighborFinset w).filter (· ∉ A)).card = 1 := by omega
        have hwin1 : ((G.neighborFinset w).filter (· ∈ A)).card = 1 := by omega
        rcases Finset.card_eq_one.mp hwin1 with ⟨a0, ha0⟩
        have ha0_mem : a0 ∈ (G.neighborFinset w).filter (· ∈ A) := by rw [ha0]; simp
        simp only [mem_filter, mem_neighborFinset] at ha0_mem
        have hsubA' : cutEdges G A' ⊆ insert (a0, w) ((cutEdges G A).erase r) := by
          intro q hq
          rcases mem_cutEdges.mp hq with ⟨hq1, hq2, hqadj⟩
          have hq1A : q.1 ∈ A := Finset.mem_of_mem_erase hq1
          have hq1w : q.1 ≠ w := Finset.ne_of_mem_erase hq1
          by_cases hq2w : q.2 = w
          · have hq1a0 : q.1 = a0 := by
              have hmem : q.1 ∈ (G.neighborFinset w).filter (· ∈ A) := by
                simp [mem_filter, mem_neighborFinset, hq2w ▸ hqadj.symm, hq1A]
              rw [ha0, Finset.mem_singleton] at hmem; exact hmem
            exact Finset.mem_insert.mpr (Or.inl (Prod.ext hq1a0 hq2w))
          · have hq2nA : q.2 ∉ A := fun h => hq2 (Finset.mem_erase.mpr ⟨hq2w, h⟩)
            have hqA : q ∈ cutEdges G A := mem_cutEdges.mpr ⟨hq1A, hq2nA, hqadj⟩
            have hqr : q ≠ r := fun h => hq1w (h ▸ hrw)
            exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hqr, hqA⟩)
        have hcutA'le2 : (cutEdges G A').card ≤ 2 := by
          calc (cutEdges G A').card
              ≤ (insert (a0, w) ((cutEdges G A).erase r)).card := Finset.card_le_card hsubA'
            _ ≤ ((cutEdges G A).erase r).card + 1 := Finset.card_insert_le _ _
            _ = 2 := by rw [Finset.card_erase_of_mem hr, hcutA]
        by_cases hA'2 : 2 ≤ A'.card
        · have huA' : u ∉ A' := by
            intro h
            have : u ∈ ({w, w'} : Finset (Fin n)) := by rw [hww']; simp
            rcases Finset.mem_insert.mp this with rfl | h1
            · exact Finset.notMem_erase u A h
            · rw [Finset.mem_singleton.mp h1] at h; exact hw'A (Finset.mem_of_mem_erase h)
          have hvA' : v ∉ A' := by
            intro h
            have : v ∈ ({w, w'} : Finset (Fin n)) := by rw [hww']; simp
            rcases Finset.mem_insert.mp this with rfl | h1
            · exact Finset.notMem_erase v A h
            · rw [Finset.mem_singleton.mp h1] at h; exact hw'A (Finset.mem_of_mem_erase h)
          have hge3 := hcore.2.2.2.2.2.2.2.2.2 A' hA'2 huA' hvA'
          omega
        · have hA'1 : A'.card = 1 := by omega
          have ha0A' : a0 ∈ A' := Finset.mem_erase.mpr ⟨(G.ne_of_adj ha0_mem.1).symm, ha0_mem.2⟩
          have hA'eq : A' = {a0} := Finset.eq_singleton_iff_unique_mem.mpr
            ⟨ha0A', fun z hz => by
              rcases Finset.card_eq_one.mp hA'1 with ⟨b, hb⟩
              rw [hb, Finset.mem_singleton] at hz ha0A'; exact hz.trans ha0A'.symm⟩
          have hda0 : G.degree a0 ≤ 2 := by
            have hsp := degree_split_cut G A' a0
            have hin0 : ((G.neighborFinset a0).filter (· ∈ A')).card = 0 := by
              rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
              intro z hz hzA'
              rw [hA'eq, Finset.mem_singleton] at hzA'
              rw [mem_neighborFinset] at hz
              exact G.ne_of_adj hz hzA'.symm
            have hout := card_out_neighbors_le_cutEdges G A' ha0A'
            omega
          have hda0_ge3 := hother_deg3 a0 ha0_mem.2 (G.ne_of_adj ha0_mem.1).symm
          omega
    intro p hp
    rcases mem_cutEdges.mp hp with ⟨hp1A, hp2nA, hp_adj⟩
    have hp1_ne_w : p.1 ≠ w := hall_ne_w p hp
    have hp1_ne_w' : p.1 ≠ w' := fun h => hw'A (h ▸ hp1A)
    have hp1_uniq : ∀ q ∈ cutEdges G A, q ≠ p → q.1 ≠ p.1 := by
      intro q hq hqp hq1
      have hp1_out2 : ((G.neighborFinset p.1).filter (· ∉ A)).card = 2 := by
        have hle := card_out_neighbors_le_cutEdges G A hp1A
        have hq2_ne : q.2 ≠ p.2 := fun h => hqp (Prod.ext hq1 h)
        rcases mem_cutEdges.mp hq with ⟨_, hq2nA, hq_adj⟩
        have hsub : ({p.2, q.2} : Finset (Fin n)) ⊆ (G.neighborFinset p.1).filter (· ∉ A) := by
          intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hz'
          · simp [mem_filter, mem_neighborFinset, hp_adj, hp2nA]
          · rw [Finset.mem_singleton.mp hz']
            simp [mem_filter, mem_neighborFinset, hq1 ▸ hq_adj, hq2nA]
        have hge := Finset.card_le_card hsub
        rw [Finset.card_pair hq2_ne.symm] at hge
        omega
      have hp1_deg3 : 3 ≤ G.degree p.1 := hother_deg3 p.1 hp1A hp1_ne_w
      have hpair : cutEdges G A = {p, q} := by
        symm; apply Finset.eq_of_subset_of_card_le
        · intro r hr; rcases Finset.mem_insert.mp hr with rfl | hr'
          · exact hp
          · rw [Finset.mem_singleton.mp hr']; exact hq
        · rw [hcutA, Finset.card_pair hqp.symm]
      by_cases hp1_deg4 : 4 ≤ G.degree p.1
      · have hother0 : ∀ a ∈ A, a ≠ p.1 → ((G.neighborFinset a).filter (· ∉ A)).card = 0 := by
          intro a ha hap1
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro b hb hbnA; rw [mem_neighborFinset] at hb
          have hab_mem : (a, b) ∈ cutEdges G A := mem_cutEdges.mpr ⟨ha, hbnA, hb⟩
          rw [hpair] at hab_mem
          rcases Finset.mem_insert.mp hab_mem with h1 | h2
          · exact hap1 (congrArg Prod.fst h1)
          · rw [Finset.mem_singleton] at h2; exact hap1 ((congrArg Prod.fst h2).trans hq1)
        have hnearA : Near2 (G.induce (A : Set (Fin n))) := by
          refine ⟨fun a => ?_, ?_⟩
          · rw [induce_degree_eq]
            have hsp := degree_split_cut G A a.1
            by_cases ha : a.1 = p.1
            · rw [ha] at hsp ⊢; omega
            · have := hother0 a.1 a.2 ha; have := hmin.1.1 a.1; omega
          · have hsub : Finset.univ.filter (fun a : {a : Fin n // a ∈ (A : Set (Fin n))} =>
                (G.induce (A : Set (Fin n))).degree a < 3) ⊆
                Finset.univ.filter (fun a : {a : Fin n // a ∈ (A : Set (Fin n))} =>
                  a.1 = w ∨ a.1 = p.1) := by
              intro a ha; simp only [mem_filter, mem_univ, true_and] at ha ⊢
              by_contra hnone; push Not at hnone
              rw [induce_degree_eq] at ha
              have hsp := degree_split_cut G A a.1
              have := hother0 a.1 a.2 hnone.2
              have := hother_deg3 a.1 a.2 hnone.1
              omega
            calc _ ≤ (Finset.univ.filter (fun a : {a : Fin n // a ∈ (A : Set (Fin n))} =>
                      a.1 = w ∨ a.1 = p.1)).card := Finset.card_le_card hsub
              _ ≤ ({w, p.1} : Finset (Fin n)).card := by
                    apply Finset.card_le_card_of_injOn Subtype.val
                    · intro a ha; simp only [mem_coe, mem_filter, mem_univ, true_and] at ha; simp [ha]
                    · intro a _ b _ h; exact Subtype.ext h
              _ ≤ 2 := Finset.card_le_two
        exact induced_no_power_cycle hmin.2.1 A
          (minimal_bad2_smaller_type hmin (G.induce (A : Set (Fin n))) (induce_card_lt A hAnu) hnearA)
      · have hsp := degree_split_cut G A p.1
        have hp1_in1 : ((G.neighborFinset p.1).filter (· ∈ A)).card = 1 := by omega
        let A' := A.erase p.1
        have hA'ne : A'.Nonempty := ⟨w, Finset.mem_erase.mpr ⟨hp1_ne_w.symm, hwA⟩⟩
        have hA'nu : A' ≠ Finset.univ := fun h => Finset.notMem_erase p.1 A (by rw [h]; simp)
        have hcutA'le1 : (cutEdges G A').card ≤ 1 := by
          rcases Finset.card_eq_one.mp hp1_in1 with ⟨b0, hb0⟩
          have hsub : cutEdges G A' ⊆ {(b0, p.1)} := by
            intro r hr
            rcases mem_cutEdges.mp hr with ⟨hr1, hr2, hradj⟩
            have hr1A : r.1 ∈ A := Finset.mem_of_mem_erase hr1
            have hr1p : r.1 ≠ p.1 := Finset.ne_of_mem_erase hr1
            by_cases hr2p : r.2 = p.1
            · have hr1b0 : r.1 = b0 := by
                have hmem : r.1 ∈ (G.neighborFinset p.1).filter (· ∈ A) := by
                  simp [mem_filter, mem_neighborFinset, hr2p ▸ hradj.symm, hr1A]
                rw [hb0, Finset.mem_singleton] at hmem; exact hmem
              exact Finset.mem_singleton.mpr (Prod.ext hr1b0 hr2p)
            · have hr2nA : r.2 ∉ A := fun h => hr2 (Finset.mem_erase.mpr ⟨hr2p, h⟩)
              have hrA : r ∈ cutEdges G A := mem_cutEdges.mpr ⟨hr1A, hr2nA, hradj⟩
              rw [hpair] at hrA
              rcases Finset.mem_insert.mp hrA with h1 | h2
              · exact absurd (congrArg Prod.fst h1) hr1p
              · rw [Finset.mem_singleton] at h2
                exact absurd ((congrArg Prod.fst h2).trans hq1) hr1p
          calc (cutEdges G A').card ≤ ({(b0, p.1)} : Finset _).card := Finset.card_le_card hsub
            _ = 1 := by simp
        have := minimal_bad2_two_edge_connected hcore A' hA'ne hA'nu
        omega
    have hp1_deg3 : G.degree p.1 = 3 := by
      have hge3 := hother_deg3 p.1 hp1A hp1_ne_w
      by_contra hne3
      have hge4 : 4 ≤ G.degree p.1 := by omega
      have hrem_card : ((cutEdges G A).erase p).card = 1 := by
        rw [Finset.card_erase_of_mem hp, hcutA]
      rcases Finset.card_eq_one.mp hrem_card with ⟨q, hqeq⟩
      have hq_mem : q ∈ (cutEdges G A).erase p := by rw [hqeq]; simp
      have hqp : q ≠ p := Finset.ne_of_mem_erase hq_mem
      have hqA : q ∈ cutEdges G A := Finset.mem_of_mem_erase hq_mem
      have hpair : cutEdges G A = {p, q} := by
        symm; apply Finset.eq_of_subset_of_card_le
        · intro r hr; rcases Finset.mem_insert.mp hr with rfl | hr'
          · exact hp
          · rw [Finset.mem_singleton.mp hr']; exact hqA
        · rw [hcutA, Finset.card_pair hqp.symm]
      have hout_le1 : ∀ a ∈ A, ((G.neighborFinset a).filter (· ∉ A)).card ≤ 1 := by
        intro a ha
        by_contra hgt
        rcases Finset.one_lt_card.mp (by omega : 1 < ((G.neighborFinset a).filter (· ∉ A)).card) with
          ⟨b1, hb1, b2, hb2, hb12⟩
        simp only [mem_filter, mem_neighborFinset] at hb1 hb2
        have h1 : (a, b1) ∈ cutEdges G A := mem_cutEdges.mpr ⟨ha, hb1.2, hb1.1⟩
        have h2 : (a, b2) ∈ cutEdges G A := mem_cutEdges.mpr ⟨ha, hb2.2, hb2.1⟩
        rw [hpair] at h1 h2
        rcases Finset.mem_insert.mp h1 with h1p | h1q <;>
          rcases Finset.mem_insert.mp h2 with h2p | h2q
        · exact hb12 (congrArg Prod.snd (h1p.trans h2p.symm))
        · rw [Finset.mem_singleton] at h2q
          exact hp1_uniq q hqA hqp ((congrArg Prod.fst h2q).symm.trans (congrArg Prod.fst h1p))
        · rw [Finset.mem_singleton] at h1q
          exact hp1_uniq q hqA hqp ((congrArg Prod.fst h1q).symm.trans (congrArg Prod.fst h2p))
        · rw [Finset.mem_singleton] at h1q h2q
          exact hb12 (congrArg Prod.snd (h1q.trans h2q.symm))
      have hw_out0 : ((G.neighborFinset w).filter (· ∉ A)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro b hb hbnA; rw [mem_neighborFinset] at hb
        exact hall_ne_w (w, b) (mem_cutEdges.mpr ⟨hwA, hbnA, hb⟩) rfl
      have hnearA : Near2 (G.induce (A : Set (Fin n))) := by
        refine ⟨fun a => ?_, ?_⟩
        · rw [induce_degree_eq]
          have hsp := degree_split_cut G A a.1
          by_cases haw : a.1 = w
          · rw [haw] at hsp ⊢; omega
          · have := hout_le1 a.1 a.2; have := hother_deg3 a.1 a.2 haw; omega
        · have hsub : Finset.univ.filter (fun a : {a : Fin n // a ∈ (A : Set (Fin n))} =>
              (G.induce (A : Set (Fin n))).degree a < 3) ⊆
              Finset.univ.filter (fun a : {a : Fin n // a ∈ (A : Set (Fin n))} =>
                a.1 = w ∨ a.1 = q.1) := by
            intro a ha; simp only [mem_filter, mem_univ, true_and] at ha ⊢
            by_contra hnone; push Not at hnone
            rw [induce_degree_eq] at ha
            have hsp := degree_split_cut G A a.1
            by_cases hap : a.1 = p.1
            · have hle := hout_le1 a.1 a.2
              rw [hap] at hsp hle ha
              omega
            · have ha_out0 : ((G.neighborFinset a.1).filter (· ∉ A)).card = 0 := by
                rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
                intro b hb hbnA; rw [mem_neighborFinset] at hb
                have hmem : (a.1, b) ∈ cutEdges G A := mem_cutEdges.mpr ⟨a.2, hbnA, hb⟩
                rw [hpair] at hmem
                rcases Finset.mem_insert.mp hmem with h1 | h2
                · exact hap (congrArg Prod.fst h1)
                · rw [Finset.mem_singleton] at h2; exact hnone.2 (congrArg Prod.fst h2)
              have := hother_deg3 a.1 a.2 hnone.1
              omega
          calc _ ≤ (Finset.univ.filter (fun a : {a : Fin n // a ∈ (A : Set (Fin n))} =>
                    a.1 = w ∨ a.1 = q.1)).card := Finset.card_le_card hsub
            _ ≤ ({w, q.1} : Finset (Fin n)).card := by
                  apply Finset.card_le_card_of_injOn Subtype.val
                  · intro a ha; simp only [mem_coe, mem_filter, mem_univ, true_and] at ha; simp [ha]
                  · intro a _ b _ h; exact Subtype.ext h
            _ ≤ 2 := Finset.card_le_two
      exact induced_no_power_cycle hmin.2.1 A
        (minimal_bad2_smaller_type hmin (G.induce (A : Set (Fin n))) (induce_card_lt A hAnu) hnearA)
    have hp1_not : p.1 ∉ ({u, v} : Finset (Fin n)) := by rw [← hww']; simp [hp1_ne_w, hp1_ne_w']
    exact ⟨fun h => hp1_not (by simp [h]), fun h => hp1_not (by simp [h]), hp1_deg3, hp1_uniq⟩
  let T := Finset.univ \ S
  have hSnu : S ≠ Finset.univ := by
    intro h; rw [h, Finset.sdiff_self] at hT2; simp at hT2
  have hTnu : T ≠ Finset.univ := by
    intro h; have hScard : S.card = 0 := by
      have : S = ∅ := by
        ext x; simp only [Finset.notMem_empty, iff_false]
        intro hx; have : x ∈ T := by rw [h]; simp
        simp [T, hx] at this
      simp [this]
    omega
  have hcutT : (cutEdges G T).card = 2 := by rw [cutEdges_symm_card, hcut2]
  intro p hp
  have hp_rev : (p.2, p.1) ∈ cutEdges G T := by
    rcases mem_cutEdges.mp hp with ⟨h1, h2, hadj⟩
    exact mem_cutEdges.mpr ⟨by simp [T, h2], by simp [T, h1], hadj.symm⟩
  rcases hsep with ⟨huS, hvS⟩ | ⟨hvS, huS⟩
  · have h1 := side_props S u v hS2 hSnu huS hvS rfl hcut2 p hp
    have h2 := side_props T v u hT2 hTnu (by simp [T, hvS]) (by simp [T, huS])
      (by ext x; simp [or_comm]) hcutT (p.2, p.1) hp_rev
    refine ⟨h1.1, h1.2.1, h2.1, h2.2.1, h1.2.2.1, h2.2.2.1, fun q hq hqp => ⟨h1.2.2.2 q hq hqp, ?_⟩⟩
    have hq_rev : (q.2, q.1) ∈ cutEdges G T := by
      rcases mem_cutEdges.mp hq with ⟨ha, hb, hadj⟩
      exact mem_cutEdges.mpr ⟨by simp [T, hb], by simp [T, ha], hadj.symm⟩
    have hne_rev : (q.2, q.1) ≠ (p.2, p.1) := fun h => hqp (Prod.ext (Prod.mk.inj h).2 (Prod.mk.inj h).1)
    exact h2.2.2.2 (q.2, q.1) hq_rev hne_rev
  · have h1 := side_props S v u hS2 hSnu hvS huS (by ext x; simp [or_comm]) hcut2 p hp
    have h2 := side_props T u v hT2 hTnu (by simp [T, huS]) (by simp [T, hvS]) rfl hcutT (p.2, p.1) hp_rev
    refine ⟨h1.1, h1.2.1, h2.1, h2.2.1, h1.2.2.1, h2.2.2.1, fun q hq hqp => ⟨h1.2.2.2 q hq hqp, ?_⟩⟩
    have hq_rev : (q.2, q.1) ∈ cutEdges G T := by
      rcases mem_cutEdges.mp hq with ⟨ha, hb, hadj⟩
      exact mem_cutEdges.mpr ⟨by simp [T, hb], by simp [T, ha], hadj.symm⟩
    have hne_rev : (q.2, q.1) ≠ (p.2, p.1) := fun h => hqp (Prod.ext (Prod.mk.inj h).2 (Prod.mk.inj h).1)
    exact h2.2.2.2 (q.2, q.1) hq_rev hne_rev

/-! ### Pillar II: Local and Global `V_3`–`V_{≥4}` Discharging & Density Bounds -/

/-- Theorem 2.1: Every nonempty subset `S ⊆ V \ {u, v}` whose outgoing edges all land in `V_{≥4}`
must force some `h ∈ V_{≥4}` to drop below degree 3 when `S` is deleted. -/
theorem minimal_bad2_v3_component_high_bottleneck {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u v : Fin n} (hcore : EG2Core G u v)
    (S : Finset (Fin n)) (hne : S.Nonempty) (huS : u ∉ S) (hvS : v ∉ S)
    (hout : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → 4 ≤ G.degree y) :
    ∃ h ∉ S, 4 ≤ G.degree h ∧ G.degree h - ((G.neighborFinset h).filter (· ∈ S)).card < 3 := by
  by_contra hno
  push Not at hno
  have hmin := hcore.1
  let T := Finset.univ \ S
  have hTnu : T ≠ Finset.univ := by
    intro h; rcases hne with ⟨s, hs⟩
    have : s ∈ T := by rw [h]; simp
    simp [T, hs] at this
  have hnearT : Near2 (G.induce (T : Set (Fin n))) := by
    refine ⟨fun a => ?_, ?_⟩
    · rw [induce_degree_eq]
      have haS : a.1 ∉ S := (Finset.mem_sdiff.mp a.2).2
      have hsp := degree_split_cut G T a.1
      have hfilt : (G.neighborFinset a.1).filter (· ∉ T) = (G.neighborFinset a.1).filter (· ∈ S) := by
        ext z; simp [T]
      rw [hfilt] at hsp
      by_cases hhigh : 4 ≤ G.degree a.1
      · have := hno a.1 haS hhigh; omega
      · have h0 : ((G.neighborFinset a.1).filter (· ∈ S)).card = 0 := by
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro z hz hzS; rw [mem_neighborFinset] at hz
          exact hhigh (hout z hzS a.1 haS hz.symm)
        have := hmin.1.1 a.1
        omega
    · have hsub : Finset.univ.filter (fun a : {a : Fin n // a ∈ (T : Set (Fin n))} =>
          (G.induce (T : Set (Fin n))).degree a < 3) ⊆
          Finset.univ.filter (fun a : {a : Fin n // a ∈ (T : Set (Fin n))} =>
            a.1 = u ∨ a.1 = v) := by
        intro a ha; simp only [mem_filter, mem_univ, true_and] at ha ⊢
        by_contra hnone; push Not at hnone
        rw [induce_degree_eq] at ha
        have haS : a.1 ∉ S := (Finset.mem_sdiff.mp a.2).2
        have hsp := degree_split_cut G T a.1
        have hfilt : (G.neighborFinset a.1).filter (· ∉ T) = (G.neighborFinset a.1).filter (· ∈ S) := by
          ext z; simp [T]
        rw [hfilt] at hsp
        by_cases hhigh : 4 ≤ G.degree a.1
        · have := hno a.1 haS hhigh; omega
        · have h0 : ((G.neighborFinset a.1).filter (· ∈ S)).card = 0 := by
            rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro z hz hzS; rw [mem_neighborFinset] at hz
            exact hhigh (hout z hzS a.1 haS hz.symm)
          have := hcore.2.2.2.2.2.1 a.1 hnone.1 hnone.2
          omega
      calc _ ≤ (Finset.univ.filter (fun a : {a : Fin n // a ∈ (T : Set (Fin n))} =>
                a.1 = u ∨ a.1 = v)).card := Finset.card_le_card hsub
        _ ≤ ({u, v} : Finset (Fin n)).card := by
              apply Finset.card_le_card_of_injOn Subtype.val
              · intro a ha; simp only [mem_coe, mem_filter, mem_univ, true_and] at ha; simp [ha]
              · intro a _ b _ h; exact Subtype.ext h
        _ ≤ 2 := Finset.card_le_two
  exact induced_no_power_cycle hmin.2.1 T
    (minimal_bad2_smaller_type hmin (G.induce (T : Set (Fin n))) (induce_card_lt T hTnu) hnearT)

/-- Theorem 2.2: No vertex of degree 3 in `EG2Core` has all its neighbors in `V_{≥4}`. -/
theorem minimal_bad2_no_v3_all_high_neighbors {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u v : Fin n} (hcore : EG2Core G u v) (x : Fin n) (hx3 : G.degree x = 3) :
    ∃ y : Fin n, G.Adj x y ∧ G.degree y ≤ 3 := by
  by_contra hno
  push Not at hno
  have hxu : x ≠ u := fun h => by have := hcore.2.2.2.1; subst h; omega
  have hxv : x ≠ v := fun h => by have := hcore.2.2.2.2.1; subst h; omega
  have hbot := minimal_bad2_v3_component_high_bottleneck hcore {x} (Finset.singleton_nonempty x)
    (by simp [hxu.symm]) (by simp [hxv.symm])
    (fun a ha y _ hay => by rw [Finset.mem_singleton.mp ha] at hay; exact hno y hay)
  rcases hbot with ⟨h, _, hh4, hlt⟩
  have hle1 : ((G.neighborFinset h).filter (· ∈ ({x} : Finset (Fin n)))).card ≤ 1 := by
    calc _ ≤ ({x} : Finset (Fin n)).card := Finset.card_le_card (fun z hz => (Finset.mem_filter.mp hz).2)
      _ = 1 := by simp
  omega

/-- Theorem 2.3: No two adjacent vertices `x, y ∈ V_3` can each have 2 neighbors in `V_{≥4}`
unless they share a common neighbor of degree 4. -/
theorem minimal_bad2_no_adjacent_two_high_disjoint {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u v : Fin n} (hcore : EG2Core G u v)
    (x y : Fin n) (hxy : G.Adj x y)
    (hx_out : ∀ z, G.Adj x z → z ≠ y → 4 ≤ G.degree z)
    (hy_out : ∀ z, G.Adj y z → z ≠ x → 4 ≤ G.degree z)
    (hno4 : ∀ h, G.Adj x h → G.Adj y h → 5 ≤ G.degree h) : False := by
  have not_defect : ∀ (w t : Fin n), G.Adj w t →
      (∀ z, G.Adj w z → z ≠ t → 4 ≤ G.degree z) → w ≠ u ∧ w ≠ v := by
    intro w t hwt hw_out
    constructor
    · intro h; subst h
      have hsp : (G.neighborFinset w).card = 2 := by rw [card_neighborFinset_eq_degree]; exact hcore.2.2.2.1
      rcases Finset.card_eq_two.mp hsp with ⟨a, b, hab, hpair⟩
      have ht_in : t ∈ ({a, b} : Finset (Fin n)) := by rw [← hpair, mem_neighborFinset]; exact hwt
      rcases Finset.mem_insert.mp ht_in with hta | htb
      · have hwb : G.Adj w b := by rw [← mem_neighborFinset, hpair]; simp
        have hb3 := hcore.2.2.2.2.2.2.1 b (Or.inl hwb)
        have hb4 := hw_out b hwb (hta ▸ hab.symm); omega
      · have htb' : t = b := Finset.mem_singleton.mp htb
        have hwa : G.Adj w a := by rw [← mem_neighborFinset, hpair]; simp
        have ha3 := hcore.2.2.2.2.2.2.1 a (Or.inl hwa)
        have ha4 := hw_out a hwa (htb' ▸ hab); omega
    · intro h; subst h
      have hsp : (G.neighborFinset w).card = 2 := by rw [card_neighborFinset_eq_degree]; exact hcore.2.2.2.2.1
      rcases Finset.card_eq_two.mp hsp with ⟨a, b, hab, hpair⟩
      have ht_in : t ∈ ({a, b} : Finset (Fin n)) := by rw [← hpair, mem_neighborFinset]; exact hwt
      rcases Finset.mem_insert.mp ht_in with hta | htb
      · have hwb : G.Adj w b := by rw [← mem_neighborFinset, hpair]; simp
        have hb3 := hcore.2.2.2.2.2.2.1 b (Or.inr hwb)
        have hb4 := hw_out b hwb (hta ▸ hab.symm); omega
      · have htb' : t = b := Finset.mem_singleton.mp htb
        have hwa : G.Adj w a := by rw [← mem_neighborFinset, hpair]; simp
        have ha3 := hcore.2.2.2.2.2.2.1 a (Or.inr hwa)
        have ha4 := hw_out a hwa (htb' ▸ hab); omega
  have hxn := not_defect x y hxy hx_out
  have hyn := not_defect y x hxy.symm hy_out
  have hbot := minimal_bad2_v3_component_high_bottleneck hcore {x, y}
    ⟨x, by simp⟩ (by simp [hxn.1.symm, hyn.1.symm]) (by simp [hxn.2.symm, hyn.2.symm])
    (fun a ha z hz haz => by
      simp only [mem_insert, mem_singleton] at ha hz
      push Not at hz
      rcases ha with rfl | rfl
      · exact hx_out z haz hz.2
      · exact hy_out z haz hz.1)
  rcases hbot with ⟨h, _, hh4, hlt⟩
  have hsub : (G.neighborFinset h).filter (· ∈ ({x, y} : Finset (Fin n))) ⊆ {x, y} :=
    fun z hz => (Finset.mem_filter.mp hz).2
  have hle2 : ((G.neighborFinset h).filter (· ∈ ({x, y} : Finset (Fin n)))).card ≤ 2 :=
    le_trans (Finset.card_le_card hsub) Finset.card_le_two
  by_cases hcard2 : ((G.neighborFinset h).filter (· ∈ ({x, y} : Finset (Fin n)))).card = 2
  · have hxy_ne : x ≠ y := G.ne_of_adj hxy
    have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard2, Finset.card_pair hxy_ne])
    have hx_in : x ∈ (G.neighborFinset h).filter (· ∈ ({x, y} : Finset (Fin n))) := by rw [heq]; simp
    have hy_in : y ∈ (G.neighborFinset h).filter (· ∈ ({x, y} : Finset (Fin n))) := by rw [heq]; simp
    simp only [mem_filter, mem_neighborFinset] at hx_in hy_in
    have hh5 := hno4 h hx_in.1.symm hy_in.1.symm
    omega
  · omega

/-- Theorem 2.4: Every neighbor of a degree-2 defect `u` (or `v`) has at most 1 neighbor in `V_{≥4}`. -/
theorem minimal_bad2_defect_neighbor_at_most_one_high {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u v : Fin n} (hcore : EG2Core G u v) (x : Fin n) (hux : G.Adj u x) :
    ((G.neighborFinset x).filter (fun z => 4 ≤ G.degree z)).card ≤ 1 := by
  by_contra hgt
  have hge2 : 2 ≤ ((G.neighborFinset x).filter (fun z => 4 ≤ G.degree z)).card := by omega
  have hdx3 : G.degree x = 3 := hcore.2.2.2.2.2.2.1 x (Or.inl hux)
  have hx_other_high : ∀ z, G.Adj x z → z ≠ u → 4 ≤ G.degree z := by
    intro z hxz hzu
    by_contra hlt4
    have hsub : insert u (insert z ((G.neighborFinset x).filter (fun w => 4 ≤ G.degree w))) ⊆
        G.neighborFinset x := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw1
      · simp [mem_neighborFinset, hux.symm]
      · rcases Finset.mem_insert.mp hw1 with rfl | hw2
        · simp [mem_neighborFinset, hxz]
        · exact (Finset.mem_filter.mp hw2).1
    have hu_not : u ∉ insert z ((G.neighborFinset x).filter (fun w => 4 ≤ G.degree w)) := by
      intro h; rcases Finset.mem_insert.mp h with h1 | h2
      · exact hzu h1.symm
      · have := (Finset.mem_filter.mp h2).2; have := hcore.2.2.2.1; omega
    have hz_not : z ∉ (G.neighborFinset x).filter (fun w => 4 ≤ G.degree w) := by
      intro h; exact hlt4 (Finset.mem_filter.mp h).2
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hu_not, Finset.card_insert_of_notMem hz_not,
        card_neighborFinset_eq_degree, hdx3] at hcard
    omega
  have hmin := hcore.1
  let T := Finset.univ \ {u, x}
  have hTnu : T ≠ Finset.univ := by
    intro h; have : u ∈ T := by rw [h]; simp
    simp [T] at this
  have hdu2 : (G.neighborFinset u).card = 2 := by rw [card_neighborFinset_eq_degree]; exact hcore.2.2.2.1
  rcases Finset.card_eq_two.mp hdu2 with ⟨a1, a2, _, hupair⟩
  have hx_in_u : x ∈ ({a1, a2} : Finset (Fin n)) := by rw [← hupair, mem_neighborFinset]; exact hux
  have hex_other : ∃ a0, ∀ z, G.Adj u z → z ≠ x → z = a0 := by
    rcases Finset.mem_insert.mp hx_in_u with hxa1 | hxa2
    · exact ⟨a2, fun z huz hzx => by
        have hz_in : z ∈ ({a1, a2} : Finset (Fin n)) := by rw [← hupair, mem_neighborFinset]; exact huz
        exact (Finset.mem_insert.mp hz_in).resolve_left (hxa1 ▸ hzx)⟩
    · have hxa2' : x = a2 := Finset.mem_singleton.mp hxa2
      exact ⟨a1, fun z huz hzx => by
        have hz_in : z ∈ ({a1, a2} : Finset (Fin n)) := by rw [← hupair, mem_neighborFinset]; exact huz
        rcases Finset.mem_insert.mp hz_in with rfl | h2
        · rfl
        · exact absurd ((Finset.mem_singleton.mp h2).trans hxa2'.symm) hzx⟩
  rcases hex_other with ⟨a0, ha0⟩
  have hnearT : Near2 (G.induce (T : Set (Fin n))) := by
    refine ⟨fun a => ?_, ?_⟩
    · rw [induce_degree_eq]
      have ha_not : a.1 ≠ u ∧ a.1 ≠ x := by
        have := (Finset.mem_sdiff.mp a.2).2; simp only [mem_insert, mem_singleton, not_or] at this; exact this
      have hsp := degree_split_cut G T a.1
      have hfilt : (G.neighborFinset a.1).filter (· ∉ T) = (G.neighborFinset a.1).filter (· ∈ ({u, x} : Finset (Fin n))) := by
        ext z; simp only [mem_filter, mem_neighborFinset, T, mem_sdiff, mem_univ, true_and, not_not]
      rw [hfilt] at hsp
      by_cases hax : G.Adj x a.1
      · have hda4 : 4 ≤ G.degree a.1 := hx_other_high a.1 hax ha_not.1
        have hnotu : ¬G.Adj u a.1 := fun hua => by
          have := hcore.2.2.2.2.2.2.1 a.1 (Or.inl hua); omega
        have hle1 : ((G.neighborFinset a.1).filter (· ∈ ({u, x} : Finset (Fin n)))).card ≤ 1 := by
          have hsub : (G.neighborFinset a.1).filter (· ∈ ({u, x} : Finset (Fin n))) ⊆ {x} := by
            intro z hz; simp only [mem_filter, mem_neighborFinset, mem_insert, mem_singleton] at hz ⊢
            rcases hz.2 with rfl | rfl
            · exact absurd hz.1.symm hnotu
            · rfl
          exact le_trans (Finset.card_le_card hsub) (by simp)
        omega
      · by_cases hau : G.Adj u a.1
        · have hda3 : G.degree a.1 = 3 := hcore.2.2.2.2.2.2.1 a.1 (Or.inl hau)
          have hle1 : ((G.neighborFinset a.1).filter (· ∈ ({u, x} : Finset (Fin n)))).card ≤ 1 := by
            have hsub : (G.neighborFinset a.1).filter (· ∈ ({u, x} : Finset (Fin n))) ⊆ {u} := by
              intro z hz; simp only [mem_filter, mem_neighborFinset, mem_insert, mem_singleton] at hz ⊢
              rcases hz.2 with rfl | rfl
              · rfl
              · exact absurd hz.1.symm hax
            exact le_trans (Finset.card_le_card hsub) (by simp)
          omega
        · have h0 : ((G.neighborFinset a.1).filter (· ∈ ({u, x} : Finset (Fin n)))).card = 0 := by
            rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro z hz hzx; rw [mem_neighborFinset] at hz
            rcases Finset.mem_insert.mp hzx with rfl | h1
            · exact hau hz.symm
            · rw [Finset.mem_singleton.mp h1] at hz; exact hax hz.symm
          have := hmin.1.1 a.1
          omega
    · have hsub : Finset.univ.filter (fun a : {a : Fin n // a ∈ (T : Set (Fin n))} =>
          (G.induce (T : Set (Fin n))).degree a < 3) ⊆
          Finset.univ.filter (fun a : {a : Fin n // a ∈ (T : Set (Fin n))} =>
            a.1 = a0 ∨ a.1 = v) := by
        intro a ha; simp only [mem_filter, mem_univ, true_and] at ha ⊢
        by_contra hnone; push Not at hnone
        rw [induce_degree_eq] at ha
        have ha_not : a.1 ≠ u ∧ a.1 ≠ x := by
          have := (Finset.mem_sdiff.mp a.2).2; simp only [mem_insert, mem_singleton, not_or] at this; exact this
        have hsp := degree_split_cut G T a.1
        have hfilt : (G.neighborFinset a.1).filter (· ∉ T) = (G.neighborFinset a.1).filter (· ∈ ({u, x} : Finset (Fin n))) := by
          ext z; simp only [mem_filter, mem_neighborFinset, T, mem_sdiff, mem_univ, true_and, not_not]
        rw [hfilt] at hsp
        have hnotu : ¬G.Adj u a.1 := fun hua => hnone.1 (ha0 a.1 hua ha_not.2)
        by_cases hax : G.Adj x a.1
        · have hda4 : 4 ≤ G.degree a.1 := hx_other_high a.1 hax ha_not.1
          have hle1 : ((G.neighborFinset a.1).filter (· ∈ ({u, x} : Finset (Fin n)))).card ≤ 1 := by
            have hsub1 : (G.neighborFinset a.1).filter (· ∈ ({u, x} : Finset (Fin n))) ⊆ {x} := by
              intro z hz; simp only [mem_filter, mem_neighborFinset, mem_insert, mem_singleton] at hz ⊢
              rcases hz.2 with rfl | rfl
              · exact absurd hz.1.symm hnotu
              · rfl
            exact le_trans (Finset.card_le_card hsub1) (by simp)
          omega
        · have h0 : ((G.neighborFinset a.1).filter (· ∈ ({u, x} : Finset (Fin n)))).card = 0 := by
            rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro z hz hzx; rw [mem_neighborFinset] at hz
            rcases Finset.mem_insert.mp hzx with rfl | h1
            · exact hnotu hz.symm
            · rw [Finset.mem_singleton.mp h1] at hz; exact hax hz.symm
          have := hcore.2.2.2.2.2.1 a.1 ha_not.1 hnone.2
          omega
      calc _ ≤ (Finset.univ.filter (fun a : {a : Fin n // a ∈ (T : Set (Fin n))} =>
                a.1 = a0 ∨ a.1 = v)).card := Finset.card_le_card hsub
        _ ≤ ({a0, v} : Finset (Fin n)).card := by
              apply Finset.card_le_card_of_injOn Subtype.val
              · intro a ha; simp only [mem_coe, mem_filter, mem_univ, true_and] at ha; simp [ha]
              · intro a _ b _ h; exact Subtype.ext h
        _ ≤ 2 := Finset.card_le_two
  exact induced_no_power_cycle hmin.2.1 T
    (minimal_bad2_smaller_type hmin (G.induce (T : Set (Fin n))) (induce_card_lt T hTnu) hnearT)

/-- Theorem 2.5 (C4-freeness): `MinimalBad2 G` has no 4-cycle. -/
theorem minimal_bad2_c4_free {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hmin : MinimalBad2 G) (x y : Fin n) (hxy : x ≠ y) :
    ((G.neighborFinset x) ∩ (G.neighborFinset y)).card ≤ 1 := by
  by_contra hgt
  rcases Finset.one_lt_card.mp (by omega : 1 < ((G.neighborFinset x) ∩ (G.neighborFinset y)).card) with
    ⟨a, ha, b, hb, hab⟩
  simp only [mem_inter, mem_neighborFinset] at ha hb
  have hxa : x ≠ a := G.ne_of_adj ha.1
  have hxb : x ≠ b := G.ne_of_adj hb.1
  have hya : y ≠ a := G.ne_of_adj ha.2
  have hyb : y ≠ b := G.ne_of_adj hb.2
  let p : G.Walk x x :=
    Walk.cons ha.1 (Walk.cons ha.2.symm (Walk.cons hb.2 (Walk.cons hb.1.symm Walk.nil)))
  have hcyc : p.IsCycle := by
    refine ⟨⟨⟨?_⟩, by simp [p]⟩, ?_⟩
    · simp only [p, Walk.edges_cons, Walk.edges_nil, List.nodup_cons, List.mem_cons,
        List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true, Sym2.eq_iff]
      refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> tauto
    · simp only [p, Walk.support_cons, Walk.support_nil, List.tail_cons, List.nodup_cons,
        List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
      refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> tauto
  exact hmin.2.1 ⟨x, p, hcyc, ⟨2, le_rfl, rfl⟩⟩

/-- Theorem 2.6 (Global Cubic Density Bound in `EG2Core`):
`4 * |V_{≥4}| ≤ 2 * |V_3| - 3` and `6 * |V_3| ≥ 4 * n - 5`. -/
theorem minimal_bad2_v3_density_two_thirds {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u v : Fin n} (hcore : EG2Core G u v) :
    let V3 := Finset.univ.filter (fun x : Fin n => G.degree x = 3)
    let V4 := Finset.univ.filter (fun x : Fin n => 4 ≤ G.degree x)
    4 * V4.card ≤ 2 * V3.card - 3 ∧ 4 * n ≤ 6 * V3.card + 5 := by
  intro V3 V4
  have hmin := hcore.1
  have huv := hcore.2.1
  have hpart : n = 2 + V3.card + V4.card := by
    have hdisj1 : Disjoint ({u, v} : Finset (Fin n)) V3 := by
      rw [Finset.disjoint_left]
      intro x hx hx3; simp only [V3, mem_filter, mem_univ, true_and] at hx3
      rcases Finset.mem_insert.mp hx with rfl | h1
      · have := hcore.2.2.2.1; omega
      · rw [Finset.mem_singleton.mp h1] at hx3; have := hcore.2.2.2.2.1; omega
    have hdisj2 : Disjoint (({u, v} : Finset (Fin n)) ∪ V3) V4 := by
      rw [Finset.disjoint_left]
      intro x hx hx4; simp only [V4, mem_filter, mem_univ, true_and] at hx4
      rcases Finset.mem_union.mp hx with h | h
      · rcases Finset.mem_insert.mp h with rfl | h1
        · have := hcore.2.2.2.1; omega
        · rw [Finset.mem_singleton.mp h1] at hx4; have := hcore.2.2.2.2.1; omega
      · simp only [V3, mem_filter, mem_univ, true_and] at h; omega
    have hunion : ({u, v} : Finset (Fin n)) ∪ V3 ∪ V4 = Finset.univ := by
      ext x; simp only [mem_union, mem_insert, mem_singleton, V3, V4, mem_filter, mem_univ, true_and, iff_true]
      by_cases hxu : x = u
      · exact Or.inl (Or.inl (Or.inl hxu))
      · by_cases hxv : x = v
        · exact Or.inl (Or.inl (Or.inr hxv))
        · have hd3 := hcore.2.2.2.2.2.1 x hxu hxv
          by_cases hd4 : 4 ≤ G.degree x
          · exact Or.inr hd4
          · exact Or.inl (Or.inr (by omega))
    have hcard := congrArg Finset.card hunion
    rw [Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1,
        Finset.card_pair huv, Finset.card_univ, Fintype.card_fin] at hcard
    omega
  let Nuv := G.neighborFinset u ∪ G.neighborFinset v
  have hNuv_sub : Nuv ⊆ V3 := by
    intro x hx; simp only [Nuv, mem_union, mem_neighborFinset, V3, mem_filter, mem_univ, true_and] at hx ⊢
    exact hcore.2.2.2.2.2.2.1 x hx
  have hNuv_card : 3 ≤ Nuv.card := by
    have hc4 := minimal_bad2_c4_free hmin u v huv
    have hcu := Finset.card_union_add_card_inter (G.neighborFinset u) (G.neighborFinset v)
    rw [card_neighborFinset_eq_degree, card_neighborFinset_eq_degree, hcore.2.2.2.1, hcore.2.2.2.2.1] at hcu
    dsimp [Nuv]; omega
  have hV4_nb : ∀ h ∈ V4, G.neighborFinset h ⊆ V3 := by
    intro h hh x hx
    simp only [V4, V3, mem_filter, mem_univ, true_and, mem_neighborFinset] at hh hx ⊢
    have hnot4 : ¬4 ≤ G.degree x := fun hx4 => hcore.2.2.2.2.2.2.2.1 h x hh hx4 hx
    have hxu : x ≠ u := fun h1 => by subst h1; have := hcore.2.2.2.2.2.2.1 h (Or.inl hx.symm); omega
    have hxv : x ≠ v := fun h1 => by subst h1; have := hcore.2.2.2.2.2.2.1 h (Or.inr hx.symm); omega
    have hd3 := hcore.2.2.2.2.2.1 x hxu hxv
    omega
  have hdouble : ∑ h ∈ V4, G.degree h = ∑ x ∈ V3, ((G.neighborFinset x).filter (· ∈ V4)).card := by
    have h1 : ∑ h ∈ V4, G.degree h = ∑ h ∈ V4, (V3.filter (fun x => G.Adj h x)).card := by
      apply Finset.sum_congr rfl; intro h hh
      rw [← card_neighborFinset_eq_degree]
      congr 1; ext x; simp only [mem_neighborFinset, mem_filter]
      exact ⟨fun hx => ⟨hV4_nb h hh (by simp [mem_neighborFinset, hx]), hx⟩, fun hx => hx.2⟩
    have h2 : ∑ x ∈ V3, ((G.neighborFinset x).filter (· ∈ V4)).card =
        ∑ x ∈ V3, (V4.filter (fun h => G.Adj h x)).card := by
      apply Finset.sum_congr rfl; intro x _
      congr 1; ext h; simp [mem_filter, mem_neighborFinset, adj_comm]
    rw [h1, h2]
    simp_rw [Finset.card_filter]
    exact Finset.sum_comm
  have hlow : 4 * V4.card ≤ ∑ h ∈ V4, G.degree h := by
    calc 4 * V4.card = ∑ _h ∈ V4, 4 := by simp [mul_comm]
      _ ≤ ∑ h ∈ V4, G.degree h := Finset.sum_le_sum (fun h hh => (Finset.mem_filter.mp hh).2)
  have hhigh_x : ∀ x ∈ V3, ((G.neighborFinset x).filter (· ∈ V4)).card ≤ if x ∈ Nuv then 1 else 2 := by
    intro x hx
    have hx3 : G.degree x = 3 := (Finset.mem_filter.mp hx).2
    by_cases hxN : x ∈ Nuv
    · simp only [hxN, ↓reduceIte]
      simp only [Nuv, mem_union, mem_neighborFinset] at hxN
      rcases hxN with hux | hvx
      · simpa [V4] using minimal_bad2_defect_neighbor_at_most_one_high hcore x hux
      · have hcore_sw : EG2Core G v u :=
          ⟨hcore.1, hcore.2.1.symm, fun h => hcore.2.2.1 h.symm, hcore.2.2.2.2.1, hcore.2.2.2.1,
           fun z hzv hzu => hcore.2.2.2.2.2.1 z hzu hzv,
           fun z hz => hcore.2.2.2.2.2.2.1 z hz.symm,
           hcore.2.2.2.2.2.2.2.1, hcore.2.2.2.2.2.2.2.2.1,
           fun S hS hvS huS => hcore.2.2.2.2.2.2.2.2.2 S hS huS hvS⟩
        simpa [V4] using minimal_bad2_defect_neighbor_at_most_one_high hcore_sw x hvx
    · simp only [hxN, ↓reduceIte]
      rcases minimal_bad2_no_v3_all_high_neighbors hcore x hx3 with ⟨y, hxy, hy3⟩
      have hy_not : y ∉ (G.neighborFinset x).filter (· ∈ V4) := by
        intro h; have := (Finset.mem_filter.mp h).2; simp only [V4, mem_filter, mem_univ, true_and] at this; omega
      have hsub : insert y ((G.neighborFinset x).filter (· ∈ V4)) ⊆ G.neighborFinset x := by
        intro z hz; rcases Finset.mem_insert.mp hz with rfl | h1
        · simp [mem_neighborFinset, hxy]
        · exact (Finset.mem_filter.mp h1).1
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hy_not, card_neighborFinset_eq_degree, hx3] at hcard
      omega
  have hup : ∑ x ∈ V3, ((G.neighborFinset x).filter (· ∈ V4)).card + Nuv.card ≤ 2 * V3.card := by
    have hsum := Finset.sum_le_sum hhigh_x
    have hsplit : ∑ x ∈ V3, (if x ∈ Nuv then 1 else 2) + Nuv.card = 2 * V3.card := by
      have hite : ∀ x ∈ V3, (if x ∈ Nuv then 1 else 2) + (if x ∈ Nuv then 1 else 0) = 2 := by
        intro x _; split_ifs <;> rfl
      have hs : ∑ x ∈ V3, ((if x ∈ Nuv then 1 else 2) + (if x ∈ Nuv then 1 else 0)) = 2 * V3.card := by
        rw [Finset.sum_congr rfl hite]; simp [mul_comm]
      rw [Finset.sum_add_distrib] at hs
      have hN : ∑ x ∈ V3, (if x ∈ Nuv then 1 else 0) = Nuv.card := by
        rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hNuv_sub]
      rw [hN] at hs; exact hs
    omega
  have hbound : 4 * V4.card ≤ 2 * V3.card - 3 := by omega
  exact ⟨hbound, by omega⟩

/-! ### Pillar III: Defect-Anchored Dyadic Paths & Defect-Pair Contraction `Q = G / {u = v}` -/

/-- Simple quotient graph identifying `u` and `y` (`u ≠ y`), realized on `{x : Fin n // x ≠ u}`
where `y` plays the role of the merged vertex `z*`. -/
def mergeGraph {n : ℕ} (G : SimpleGraph (Fin n)) (u y : Fin n) : SimpleGraph {x : Fin n // x ≠ u} where
  Adj a b := a ≠ b ∧ (G.Adj a.1 b.1 ∨ (a.1 = y ∧ G.Adj u b.1) ∨ (b.1 = y ∧ G.Adj u a.1))
  symm := ⟨fun _ _ h => ⟨h.1.symm, by
    rcases h.2 with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl h1.symm
    · exact Or.inr (Or.inr ⟨h1, h2⟩)
    · exact Or.inr (Or.inl ⟨h1, h2⟩)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u y : Fin n) :
    DecidableRel (mergeGraph G u y).Adj :=
  fun a b => inferInstanceAs (Decidable (a ≠ b ∧ (G.Adj a.1 b.1 ∨ (a.1 = y ∧ G.Adj u b.1) ∨ (b.1 = y ∧ G.Adj u a.1))))

/-- Lifting lemma: any `2^k`-cycle in `mergeGraph G u y` (when `G` is power-free) lifts to a
simple `u`–`y` path of length `2^k` in `G`. -/
lemma mergeGraph_cycle_lifts_to_path {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u y : Fin n} (huy : u ≠ y) (hnp : ¬HasPowerCycle G)
    (hpow : HasPowerCycle (mergeGraph G u y)) :
    ∃ p : G.Walk u y, p.IsPath ∧ IsPowerOfTwo p.length := by
  let Q := mergeGraph G u y
  let y' : {x : Fin n // x ≠ u} := ⟨y, huy.symm⟩
  have lift_avoid : ∀ {a b : {x : Fin n // x ≠ u}} (w : Q.Walk a b),
      y' ∉ w.support → ∃ wG : G.Walk a.1 b.1, wG.support = w.support.map Subtype.val ∧ wG.length = w.length := by
    intro a b w
    induction w with
    | nil => intro _; exact ⟨Walk.nil, rfl, rfl⟩
    | @cons a c b hadj w ih =>
      intro hny
      have ha_ny : a ≠ y' := fun h => hny (by simp [h])
      have hc_ny : c ≠ y' := fun h => hny (by
        rw [Walk.support_cons]; exact List.mem_cons_of_mem a (h ▸ Walk.start_mem_support w))
      have hw_ny : y' ∉ w.support := fun h => hny (List.mem_cons_of_mem a h)
      have hadjG : G.Adj a.1 c.1 := by
        rcases hadj.2 with h1 | ⟨h1, _⟩ | ⟨h1, _⟩
        · exact h1
        · exact absurd (Subtype.ext h1) ha_ny
        · exact absurd (Subtype.ext h1) hc_ny
      rcases ih hw_ny with ⟨wG, hsup, hlen⟩
      exact ⟨Walk.cons hadjG wG, by simp [hsup], by simp [hlen]⟩
  rcases hpow with ⟨v0, c, hc, hlen⟩
  by_cases hy_mem : y' ∈ c.support
  · let p := c.rotate y' hy_mem
    have hp : p.IsCycle := hc.rotate hy_mem
    have hplen : IsPowerOfTwo p.length := by rwa [Walk.length_rotate]
    have hp_ge4 : 4 ≤ p.length := by
      rcases hplen with ⟨k, hk, heq⟩
      have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      omega
    cases p with
    | nil => exact absurd rfl hp.ne_nil
    | @cons _ a _ h1 q =>
      cases hqr : q.reverse with
      | nil =>
        have : q = Walk.nil := by simpa using congrArg Walk.reverse hqr
        subst this; simp at hp_ge4
      | @cons _ b _ h2 r_rev =>
        let r := r_rev.reverse
        have hq_eq : q = r.concat h2.symm := by
          have := congrArg Walk.reverse hqr
          simpa [r] using this
        have hsup_p : (Walk.cons h1 q).support = y' :: (r.support ++ [y']) := by
          rw [hq_eq, Walk.support_cons, Walk.support_concat]
        have hnd_tail : (r.support ++ [y']).Nodup := by
          have := hp.support_nodup; rw [hsup_p] at this; simpa using this
        have hr_nd : r.support.Nodup := (List.nodup_append.mp hnd_tail).1
        have hy_not_r : y' ∉ r.support := fun h => (List.nodup_append.mp hnd_tail).2.2 y' h y' (by simp) rfl
        rcases lift_avoid r hy_not_r with ⟨rG, hrG_sup, hrG_len⟩
        have hrG_nd : rG.support.Nodup := by rw [hrG_sup]; exact hr_nd.map Subtype.val_injective
        have hu_not_rG : u ∉ rG.support := by
          rw [hrG_sup]; simp only [List.mem_map, not_exists, not_and]
          intro z _ hz; exact z.2 hz
        have hy_not_rG : y ∉ rG.support := by
          rw [hrG_sup]; simp only [List.mem_map, not_exists, not_and]
          intro z hz hzy; exact hy_not_r (Subtype.ext hzy ▸ hz)
        have hlen_rG : rG.length + 2 = (Walk.cons h1 q).length := by
          rw [hrG_len, hq_eq]; simp [Walk.length_concat]; omega
        have hab_ne : a ≠ b := by
          intro hab; subst hab
          have hr_len_ge2 : 2 ≤ r.length := by omega
          have hhead : r.support.head (Walk.support_ne_nil r) = a := Walk.head_support r
          have hlast : r.support.getLast (Walk.support_ne_nil r) = a := Walk.getLast_support r
          have hlen_sup : 2 ≤ r.support.length := by rw [Walk.length_support]; omega
          cases hs : r.support with
          | nil => exact absurd hs (Walk.support_ne_nil r)
          | cons hd tl =>
            cases tl with
            | nil => simp [hs] at hlen_sup
            | cons x xs =>
              rw [hs] at hr_nd hhead hlast
              simp only [List.head_cons] at hhead
              subst hhead
              have hlast_mem : a ∈ x :: xs := hlast ▸ List.getLast_mem (List.cons_ne_nil x xs)
              exact (List.nodup_cons.mp hr_nd).1 hlast_mem
        have h1_disj : G.Adj y a.1 ∨ G.Adj u a.1 := by
          rcases h1.2 with h | ⟨_, h⟩ | ⟨h, _⟩
          · exact Or.inl h
          · exact Or.inr h
          · exact absurd (Subtype.ext h) h1.1.symm
        have h2_disj : G.Adj y b.1 ∨ G.Adj u b.1 := by
          rcases h2.2 with h | ⟨_, h⟩ | ⟨h, _⟩
          · exact Or.inl h
          · exact Or.inr h
          · exact absurd (Subtype.ext h) h2.1.symm
        have mk_cycle : ∀ (z : Fin n), z ∉ rG.support → G.Adj z a.1 → G.Adj b.1 z → False := by
          intro z hz hza hbz
          let cyc : G.Walk z z := Walk.cons hza (rG.concat hbz)
          have hcyc_len : cyc.length = (Walk.cons h1 q).length := by
            simp [cyc, Walk.length_concat]; omega
          have hcyc_nd : cyc.support.tail.Nodup := by
            simp only [cyc, Walk.support_cons, Walk.support_concat, List.tail_cons]
            exact List.nodup_append.mpr ⟨hrG_nd, List.nodup_singleton z,
              fun w hw w' hw' heq => by rw [List.mem_singleton.mp hw'] at heq; exact hz (heq ▸ hw)⟩
          have hcyc_edges : cyc.edges.Nodup := by
            have hrG_path : rG.IsPath := Walk.IsPath.mk' hrG_nd
            have hrG_edges_nd : rG.edges.Nodup := hrG_path.isTrail.edges_nodup
            have hza_not : s(z, a.1) ∉ (rG.concat hbz).edges := by
              rw [Walk.edges_concat, List.mem_append, List.mem_singleton]
              rintro (hm | heq)
              · exact hz (Walk.fst_mem_support_of_mem_edges rG hm)
              · rw [Sym2.eq_iff] at heq
                rcases heq with ⟨hza', _⟩ | ⟨_, hab'⟩
                · exact hz (hza' ▸ Walk.end_mem_support rG)
                · exact hab_ne (Subtype.ext hab'.symm)
            have hbz_not : s(b.1, z) ∉ rG.edges := by
              intro hm; exact hz (Walk.snd_mem_support_of_mem_edges rG hm)
            simp only [cyc, Walk.edges_cons, Walk.edges_concat, List.nodup_cons]
            refine ⟨hza_not, List.nodup_append.mpr ⟨hrG_edges_nd, List.nodup_singleton _, ?_⟩⟩
            intro e he e' he' hEq; rw [List.mem_singleton.mp he'] at hEq; exact hbz_not (hEq ▸ he)
          exact hnp ⟨z, cyc, ⟨⟨⟨hcyc_edges⟩, by simp [cyc]⟩, hcyc_nd⟩, hcyc_len ▸ hplen⟩
        rcases h1_disj with hya | hua <;> rcases h2_disj with hyb | hub
        · exact absurd (mk_cycle y hy_not_rG hya hyb.symm) id
        · let pathG : G.Walk u y := Walk.cons hub (rG.reverse.concat hya.symm)
          refine ⟨pathG, Walk.IsPath.mk' ?_, ?_⟩
          · simp only [pathG, Walk.support_cons, Walk.support_concat, Walk.support_reverse]
            rw [List.nodup_cons]
            refine ⟨?_, List.nodup_append.mpr ⟨List.nodup_reverse.mpr hrG_nd, List.nodup_singleton y, ?_⟩⟩
            · rw [List.mem_append, List.mem_reverse, List.mem_singleton]
              rintro (h | h); exact hu_not_rG h; exact huy h
            · intro w hw w' hw' heq; rw [List.mem_singleton.mp hw'] at heq
              exact hy_not_rG (heq ▸ List.mem_reverse.mp hw)
          · have : pathG.length = (Walk.cons h1 q).length := by
              simp [pathG, Walk.length_concat, Walk.length_reverse]; omega
            rwa [this]
        · let pathG : G.Walk u y := Walk.cons hua (rG.concat hyb.symm)
          refine ⟨pathG, Walk.IsPath.mk' ?_, ?_⟩
          · simp only [pathG, Walk.support_cons, Walk.support_concat]
            rw [List.nodup_cons]
            refine ⟨?_, List.nodup_append.mpr ⟨hrG_nd, List.nodup_singleton y, ?_⟩⟩
            · rw [List.mem_append, List.mem_singleton]
              rintro (h | h); exact hu_not_rG h; exact huy h
            · intro w hw w' hw' heq; rw [List.mem_singleton.mp hw'] at heq
              exact hy_not_rG (heq ▸ hw)
          · have : pathG.length = (Walk.cons h1 q).length := by
              simp [pathG, Walk.length_concat]; omega
            rwa [this]
        · exact absurd (mk_cycle u hu_not_rG hua hub.symm) id
  · rcases lift_avoid c hy_mem with ⟨cG, hcG_sup, hcG_len⟩
    have hcG_edges : cG.edges = c.edges.map (Sym2.map Subtype.val) := by
      have aux : ∀ {a b : {x : Fin n // x ≠ u}} (w : Q.Walk a b) (wG : G.Walk a.1 b.1),
          wG.support = w.support.map Subtype.val → wG.length = w.length →
          wG.edges = w.edges.map (Sym2.map Subtype.val) := by
        intro a b w
        induction w with
        | nil =>
          intro wG _ hlen'
          cases wG with
          | nil => rfl
          | cons _ _ => simp at hlen'
        | @cons a d b h w ih =>
          intro wG hsup' hlen'
          cases wG with
          | nil => simp at hlen'
          | @cons _ d' _ h' w' =>
            have hd : d' = d.1 := by
              have := congrArg (fun l => l[1]?) hsup'
              simpa using this
            subst hd
            have hw'_sup : w'.support = w.support.map Subtype.val := by
              have := congrArg List.tail hsup'
              simpa using this
            have hw'_len : w'.length = w.length := by simpa using hlen'
            simp [Walk.edges_cons, ih w' hw'_sup hw'_len]
      exact aux c cG hcG_sup hcG_len
    have hcG_cyc : cG.IsCycle := by
      refine ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
      · rw [hcG_edges]
        exact hc.edges_nodup.map (Sym2.map.injective Subtype.val_injective)
      · intro hnil; subst hnil; simp at hcG_len
        exact hc.ne_nil (Walk.nil_iff_length_eq.mpr hcG_len.symm)
      · rw [hcG_sup]
        cases hs : c.support with
        | nil => exact absurd hs (Walk.support_ne_nil c)
        | cons hd tl =>
          have hnd : tl.Nodup := by have := hc.support_nodup; rw [hs] at this; exact this
          simpa using hnd.map Subtype.val_injective
    exact absurd ⟨v0.1, cG, hcG_cyc, hcG_len ▸ hlen⟩ hnp

/-- Helper for `mergeGraph` degree when `u` and `y` have NO common neighbors in `G`. -/
lemma mergeGraph_degree_disjoint {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {u y : Fin n} (huy : u ≠ y) (hnotadj : ¬G.Adj u y)
    (hdisj : ∀ z : Fin n, ¬(G.Adj u z ∧ G.Adj y z)) :
    (mergeGraph G u y).degree ⟨y, huy.symm⟩ = G.degree u + G.degree y ∧
    ∀ z : {x : Fin n // x ≠ u}, z ≠ ⟨y, huy.symm⟩ → (mergeGraph G u y).degree z = G.degree z.1 := by
  let Q := mergeGraph G u y
  let y' : {x : Fin n // x ≠ u} := ⟨y, huy.symm⟩
  constructor
  · simp only [← card_neighborFinset_eq_degree]
    have hbij : (Q.neighborFinset y').card = (G.neighborFinset u ∪ G.neighborFinset y).card := by
      apply Finset.card_bij (fun z _ => z.1)
      · intro z hz
        simp only [mem_neighborFinset, Q, mergeGraph, mem_union] at hz ⊢
        rcases hz.2 with h1 | ⟨_, h2⟩ | ⟨h1, _⟩
        · exact Or.inr h1
        · exact Or.inl h2
        · exact absurd (Subtype.ext h1) hz.1.symm
      · intro z1 _ z2 _ h; exact Subtype.ext h
      · intro z hz
        simp only [mem_union, mem_neighborFinset] at hz
        have hzu : z ≠ u := by rintro rfl; rcases hz with h | h; exact G.ne_of_adj h rfl; exact hnotadj h.symm
        have hzy : z ≠ y := by rintro rfl; rcases hz with h | h; exact hnotadj h; exact G.ne_of_adj h rfl
        refine ⟨⟨z, hzu⟩, ?_, rfl⟩
        rw [SimpleGraph.mem_neighborFinset]
        refine ⟨fun h => hzy (congrArg Subtype.val h).symm, ?_⟩
        rcases hz with h | h
        · exact Or.inr (Or.inl ⟨rfl, h⟩)
        · exact Or.inl h
    rw [hbij, Finset.card_union_of_disjoint]
    rw [Finset.disjoint_left]; intro z hzu hzy
    simp only [mem_neighborFinset] at hzu hzy
    exact hdisj z ⟨hzu, hzy⟩
  · intro z hzy'
    have hzy : z.1 ≠ y := fun h => hzy' (Subtype.ext h)
    simp only [← card_neighborFinset_eq_degree]
    by_cases huz : G.Adj u z.1
    · have hnyz : ¬G.Adj y z.1 := fun h => hdisj z.1 ⟨huz, h⟩
      apply Finset.card_bij (fun w _ => if w = y' then u else w.1)
      · intro w hw
        simp only [mem_neighborFinset, Q, mergeGraph] at hw ⊢
        split_ifs with hwy
        · exact huz.symm
        · rcases hw.2 with h1 | ⟨h1, _⟩ | ⟨h1, _⟩
          · exact h1
          · exact absurd h1 hzy
          · exact absurd (Subtype.ext h1) hwy
      · intro w1 _ w2 _ heq
        split_ifs at heq with h1 h2
        · exact h1.trans h2.symm
        · exact absurd heq.symm w2.2
        · exact absurd heq w1.2
        · exact Subtype.ext heq
      · intro x hx; rw [mem_neighborFinset] at hx
        by_cases hxu : x = u
        · subst hxu; refine ⟨y', ?_, by simp⟩
          rw [SimpleGraph.mem_neighborFinset]
          exact ⟨hzy', Or.inr (Or.inr ⟨rfl, hx.symm⟩)⟩
        · have hxy : x ≠ y := fun h => hnyz (h ▸ hx.symm)
          refine ⟨⟨x, hxu⟩, ?_, by simp [y', hxy]⟩
          rw [SimpleGraph.mem_neighborFinset]
          exact ⟨fun h => G.ne_of_adj hx (congrArg Subtype.val h), Or.inl hx⟩
    · apply Finset.card_bij (fun w _ => w.1)
      · intro w hw
        simp only [mem_neighborFinset, Q, mergeGraph] at hw ⊢
        rcases hw.2 with h1 | ⟨h1, _⟩ | ⟨_, h2⟩
        · exact h1
        · exact absurd h1 hzy
        · exact absurd h2 huz
      · intro w1 _ w2 _ h; exact Subtype.ext h
      · intro x hx; rw [mem_neighborFinset] at hx
        have hxu : x ≠ u := fun h => huz (h ▸ hx.symm)
        refine ⟨⟨x, hxu⟩, ?_, rfl⟩
        rw [SimpleGraph.mem_neighborFinset]
        exact ⟨fun h => G.ne_of_adj hx (congrArg Subtype.val h), Or.inl hx⟩

/-- Theorem 3.1 (Universal Defect-Anchored Dyadic Path Theorem):
In `EG2Core G u v`, for EVERY vertex `y ≠ u` nonadjacent to `u` (at ANY distance ≥ 2, including `y = v`!),
there exists a simple `u`–`y` path of length `2^k` (`k ≥ 2`) in `G`. -/
theorem minimal_bad2_defect_dyadic_path {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u v : Fin n} (hcore : EG2Core G u v) (y : Fin n) (huy : u ≠ y) (hnotadj : ¬G.Adj u y) :
    ∃ p : G.Walk u y, p.IsPath ∧ IsPowerOfTwo p.length := by
  have hmin := hcore.1
  let Q := mergeGraph G u y
  let y' : {x : Fin n // x ≠ u} := ⟨y, huy.symm⟩
  have hcard : Fintype.card {x : Fin n // x ≠ u} < n := by
    rw [Fintype.card_subtype_compl, Fintype.card_unique, Fintype.card_fin]
    have := Fin.pos u; omega
  have hcomm_le1 : ((G.neighborFinset u) ∩ (G.neighborFinset y)).card ≤ 1 :=
    minimal_bad2_c4_free hmin u y huy
  have hy'_deg : 3 ≤ Q.degree y' := by
    rw [← card_neighborFinset_eq_degree]
    have hbij : (Q.neighborFinset y').card = (G.neighborFinset u ∪ G.neighborFinset y).card := by
      apply Finset.card_bij (fun z _ => z.1)
      · intro z hz
        simp only [mem_neighborFinset, Q, mergeGraph, mem_union] at hz ⊢
        rcases hz.2 with h1 | ⟨_, h2⟩ | ⟨h1, _⟩
        · exact Or.inr h1
        · exact Or.inl h2
        · exact absurd (Subtype.ext h1) hz.1.symm
      · intro z1 _ z2 _ h; exact Subtype.ext h
      · intro z hz
        simp only [mem_union, mem_neighborFinset] at hz
        have hzu : z ≠ u := by rintro rfl; rcases hz with h | h; exact G.ne_of_adj h rfl; exact hnotadj h.symm
        have hzy : z ≠ y := by rintro rfl; rcases hz with h | h; exact hnotadj h; exact G.ne_of_adj h rfl
        refine ⟨⟨z, hzu⟩, ?_, rfl⟩
        rw [SimpleGraph.mem_neighborFinset]
        refine ⟨fun h => hzy (congrArg Subtype.val h).symm, ?_⟩
        rcases hz with h | h
        · exact Or.inr (Or.inl ⟨rfl, h⟩)
        · exact Or.inl h
    rw [hbij]
    have hcu := Finset.card_union_add_card_inter (G.neighborFinset u) (G.neighborFinset y)
    rw [card_neighborFinset_eq_degree, card_neighborFinset_eq_degree, hcore.2.2.2.1] at hcu
    have hdy := hmin.1.1 y
    omega
  have hz_deg : ∀ z : {x : Fin n // x ≠ u}, z ≠ y' →
      ((¬(G.Adj u z.1 ∧ G.Adj y z.1)) → Q.degree z = G.degree z.1) ∧
      ((G.Adj u z.1 ∧ G.Adj y z.1) → Q.degree z = 2) := by
    intro z hzy'
    have hzy : z.1 ≠ y := fun h => hzy' (Subtype.ext h)
    constructor
    · intro hnotc
      simp only [← card_neighborFinset_eq_degree]
      by_cases huz : G.Adj u z.1
      · have hnyz : ¬G.Adj y z.1 := fun h => hnotc ⟨huz, h⟩
        apply Finset.card_bij (fun w _ => if w = y' then u else w.1)
        · intro w hw
          simp only [mem_neighborFinset, Q, mergeGraph] at hw ⊢
          split_ifs with hwy
          · exact huz.symm
          · rcases hw.2 with h1 | ⟨h1, _⟩ | ⟨h1, _⟩
            · exact h1
            · exact absurd h1 hzy
            · exact absurd (Subtype.ext h1) hwy
        · intro w1 _ w2 _ heq
          split_ifs at heq with h1 h2
          · exact h1.trans h2.symm
          · exact absurd heq.symm w2.2
          · exact absurd heq w1.2
          · exact Subtype.ext heq
        · intro x hx; rw [mem_neighborFinset] at hx
          by_cases hxu : x = u
          · subst hxu; refine ⟨y', ?_, by simp⟩
            rw [SimpleGraph.mem_neighborFinset]
            exact ⟨hzy', Or.inr (Or.inr ⟨rfl, hx.symm⟩)⟩
          · have hxy : x ≠ y := fun h => hnyz (h ▸ hx.symm)
            refine ⟨⟨x, hxu⟩, ?_, by simp [y', hxy]⟩
            rw [SimpleGraph.mem_neighborFinset]
            exact ⟨fun h => G.ne_of_adj hx (congrArg Subtype.val h), Or.inl hx⟩
      · apply Finset.card_bij (fun w _ => w.1)
        · intro w hw
          simp only [mem_neighborFinset, Q, mergeGraph] at hw ⊢
          rcases hw.2 with h1 | ⟨h1, _⟩ | ⟨_, h2⟩
          · exact h1
          · exact absurd h1 hzy
          · exact absurd h2 huz
        · intro w1 _ w2 _ h; exact Subtype.ext h
        · intro x hx; rw [mem_neighborFinset] at hx
          have hxu : x ≠ u := fun h => huz (h ▸ hx.symm)
          refine ⟨⟨x, hxu⟩, ?_, rfl⟩
          rw [SimpleGraph.mem_neighborFinset]
          exact ⟨fun h => G.ne_of_adj hx (congrArg Subtype.val h), Or.inl hx⟩
    · intro ⟨huz, hyz⟩
      have hdz3 : G.degree z.1 = 3 := hcore.2.2.2.2.2.2.1 z.1 (Or.inl huz)
      simp only [← card_neighborFinset_eq_degree]
      have hbij : (Q.neighborFinset z).card = ((G.neighborFinset z.1).erase u).card := by
        apply Finset.card_bij (fun w _ => w.1)
        · intro w hw
          simp only [mem_neighborFinset, Q, mergeGraph, mem_erase] at hw ⊢
          refine ⟨w.2, ?_⟩
          rcases hw.2 with h1 | ⟨h1, _⟩ | ⟨h1, _⟩
          · exact h1
          · exact absurd h1 hzy
          · exact h1 ▸ hyz.symm
        · intro w1 _ w2 _ h; exact Subtype.ext h
        · intro x hx; simp only [mem_erase, mem_neighborFinset] at hx
          refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
          rw [SimpleGraph.mem_neighborFinset]
          exact ⟨fun h => G.ne_of_adj hx.2 (congrArg Subtype.val h), Or.inl hx.2⟩
      rw [hbij, Finset.card_erase_of_mem (by simp [mem_neighborFinset, huz.symm]),
          card_neighborFinset_eq_degree, hdz3]
  have hnearQ : Near2 Q := by
    refine ⟨fun z => ?_, ?_⟩
    · by_cases hzy : z = y'
      · subst hzy; omega
      · by_cases hc : G.Adj u z.1 ∧ G.Adj y z.1
        · rw [(hz_deg z hzy).2 hc]
        · rw [(hz_deg z hzy).1 hc]; exact hmin.1.1 z.1
    · have hsub : Finset.univ.filter (fun z : {x : Fin n // x ≠ u} => Q.degree z < 3) ⊆
          (Finset.univ.filter (fun z : {x : Fin n // x ≠ u} => z.1 = v)) ∪
          (Finset.univ.filter (fun z : {x : Fin n // x ≠ u} => G.Adj u z.1 ∧ G.Adj y z.1)) := by
        intro z hz; simp only [mem_filter, mem_univ, true_and, mem_union] at hz ⊢
        by_cases hzy : z = y'
        · subst hzy; omega
        · by_cases hc : G.Adj u z.1 ∧ G.Adj y z.1
          · exact Or.inr hc
          · rw [(hz_deg z hzy).1 hc] at hz
            by_contra hnv
            have := hcore.2.2.2.2.2.1 z.1 z.2 (by tauto)
            omega
      have hc1 : (Finset.univ.filter (fun z : {x : Fin n // x ≠ u} => z.1 = v)).card ≤ 1 := by
        calc _ ≤ ({v} : Finset (Fin n)).card := by
              apply Finset.card_le_card_of_injOn Subtype.val
              · intro z hz; simp only [mem_coe, mem_filter, mem_univ, true_and] at hz; simp [hz]
              · intro z1 _ z2 _ h; exact Subtype.ext h
          _ = 1 := by simp
      have hc2 : (Finset.univ.filter (fun z : {x : Fin n // x ≠ u} => G.Adj u z.1 ∧ G.Adj y z.1)).card ≤ 1 := by
        calc _ ≤ ((G.neighborFinset u) ∩ (G.neighborFinset y)).card := by
              apply Finset.card_le_card_of_injOn Subtype.val
              · intro z hz; simp only [mem_coe, mem_filter, mem_univ, true_and] at hz
                simp [mem_inter, mem_neighborFinset, hz]
              · intro z1 _ z2 _ h; exact Subtype.ext h
          _ ≤ 1 := hcomm_le1
      calc _ ≤ _ := Finset.card_le_card hsub
        _ ≤ _ := Finset.card_union_le _ _
        _ ≤ 2 := by omega
  exact mergeGraph_cycle_lifts_to_path huy hmin.2.1 (minimal_bad2_smaller_type hmin Q hcard hnearQ)

/-- Theorem 3.2 (Edge-Robustness of Defect-Pair Contraction `Q = G / {u = v}`):
When `N(u) ∩ N(v) = ∅`, for EVERY edge `a b` of `G`, `G.deleteEdges {s(a, b)}` still contains
a simple `u`–`v` path of length `2^k` (`k ≥ 2`). -/
theorem minimal_bad2_defect_pair_contraction_edge_robust {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u v : Fin n} (hcore : EG2Core G u v)
    (hdisj : ∀ z : Fin n, ¬(G.Adj u z ∧ G.Adj v z))
    (a b : Fin n) (hab : G.Adj a b) :
    ∃ p : (G.deleteEdges {s(a, b)}).Walk u v, p.IsPath ∧ IsPowerOfTwo p.length := by
  have hmin := hcore.1
  have huv := hcore.2.1
  have hnotuv := hcore.2.2.1
  let G' := G.deleteEdges {s(a, b)}
  have hnp' : ¬HasPowerCycle G' := by
    intro hpow
    exact hmin.2.1 (hasPowerCycle_of_inj_hom (SimpleGraph.Hom.ofLE (SimpleGraph.deleteEdges_le _ _))
      Function.injective_id hpow)
  let Q := mergeGraph G' u v
  let v' : {x : Fin n // x ≠ u} := ⟨v, huv.symm⟩
  have hcard : Fintype.card {x : Fin n // x ≠ u} < n := by
    rw [Fintype.card_subtype_compl, Fintype.card_unique, Fintype.card_fin]
    have := Fin.pos u; omega
  have hdegG' : ∀ x : Fin n,
      (x ≠ a → x ≠ b → G'.degree x = G.degree x) ∧
      ((x = a ∨ x = b) → G'.degree x = G.degree x - 1) := by
    intro x; constructor
    · intro hxa hxb; simp only [← card_neighborFinset_eq_degree]
      congr 1; ext z; simp only [mem_neighborFinset, G', deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff]
      constructor
      · exact fun h => h.1
      · intro hxz; refine ⟨hxz, ?_⟩; rintro (⟨rfl, _⟩ | ⟨rfl, _⟩) <;> [exact hxa rfl; exact hxb rfl]
    · intro hxab; simp only [← card_neighborFinset_eq_degree]
      rcases hxab with rfl | rfl
      · have heq : G'.neighborFinset a = (G.neighborFinset a).erase b := by
          ext z; simp only [mem_neighborFinset, mem_erase, G', deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff]
          constructor
          · rintro ⟨haz, hne⟩; exact ⟨fun hzb => hne (Or.inl ⟨rfl, hzb⟩), haz⟩
          · rintro ⟨hzb, haz⟩; refine ⟨haz, ?_⟩
            rintro (⟨_, rfl⟩ | ⟨h1, _⟩); exact hzb rfl; exact G.ne_of_adj hab h1
        rw [heq, Finset.card_erase_of_mem (by simp [mem_neighborFinset, hab])]
      · have heq : G'.neighborFinset b = (G.neighborFinset b).erase a := by
          ext z; simp only [mem_neighborFinset, mem_erase, G', deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff]
          constructor
          · rintro ⟨hbz, hne⟩; exact ⟨fun hza => hne (Or.inr ⟨rfl, hza⟩), hbz⟩
          · rintro ⟨hza, hbz⟩; refine ⟨hbz, ?_⟩
            rintro (⟨h1, _⟩ | ⟨_, rfl⟩); exact G.ne_of_adj hab h1.symm; exact hza rfl
        rw [heq, Finset.card_erase_of_mem (by simp [mem_neighborFinset, hab.symm])]
  have hQdeg := mergeGraph_degree_disjoint G' huv (fun h => hnotuv h.1) (fun z ⟨h1, h2⟩ => hdisj z ⟨h1.1, h2.1⟩)
  have hv'_deg : 3 ≤ Q.degree v' := by
    rw [hQdeg.1]
    by_cases huab : u = a ∨ u = b
    · have hvab : v ≠ a ∧ v ≠ b := by
        rcases huab with rfl | rfl
        · exact ⟨huv.symm, fun h => hnotuv (h ▸ hab)⟩
        · exact ⟨fun h => hnotuv (h ▸ hab.symm), huv.symm⟩
      rw [(hdegG' u).2 huab, (hdegG' v).1 hvab.1 hvab.2, hcore.2.2.2.1, hcore.2.2.2.2.1]
    · push Not at huab
      rw [(hdegG' u).1 huab.1 huab.2, hcore.2.2.2.1]
      by_cases hvab : v = a ∨ v = b
      · rw [(hdegG' v).2 hvab, hcore.2.2.2.2.1]
      · push Not at hvab; rw [(hdegG' v).1 hvab.1 hvab.2, hcore.2.2.2.2.1]
  have hnearQ : Near2 Q := by
    refine ⟨fun z => ?_, ?_⟩
    · by_cases hzv : z = v'
      · subst hzv; omega
      · rw [hQdeg.2 z hzv]
        have hzv1 : z.1 ≠ v := fun h => hzv (Subtype.ext h)
        have hd3 := hcore.2.2.2.2.2.1 z.1 z.2 hzv1
        by_cases hzab : z.1 = a ∨ z.1 = b
        · rw [(hdegG' z.1).2 hzab]; omega
        · push Not at hzab; rw [(hdegG' z.1).1 hzab.1 hzab.2]; omega
    · have hsub : Finset.univ.filter (fun z : {x : Fin n // x ≠ u} => Q.degree z < 3) ⊆
          Finset.univ.filter (fun z : {x : Fin n // x ≠ u} => z.1 = a ∨ z.1 = b) := by
        intro z hz; simp only [mem_filter, mem_univ, true_and] at hz ⊢
        by_cases hzv : z = v'
        · subst hzv; omega
        · rw [hQdeg.2 z hzv] at hz
          have hzv1 : z.1 ≠ v := fun h => hzv (Subtype.ext h)
          have hd3 := hcore.2.2.2.2.2.1 z.1 z.2 hzv1
          by_contra hnab; push Not at hnab
          rw [(hdegG' z.1).1 hnab.1 hnab.2] at hz; omega
      calc _ ≤ (Finset.univ.filter (fun z : {x : Fin n // x ≠ u} => z.1 = a ∨ z.1 = b)).card :=
            Finset.card_le_card hsub
        _ ≤ ({a, b} : Finset (Fin n)).card := by
              apply Finset.card_le_card_of_injOn Subtype.val
              · intro z hz; simp only [mem_coe, mem_filter, mem_univ, true_and] at hz; simp [hz]
              · intro z1 _ z2 _ h; exact Subtype.ext h
        _ ≤ 2 := Finset.card_le_two
  exact mergeGraph_cycle_lifts_to_path huv hnp' (minimal_bad2_smaller_type hmin Q hcard hnearQ)

/-- Theorem 3.3 (Neighbor-Deletion Robustness of Defect-Pair Contraction `Q = G / {u = v}`):
For any `x ∈ N(u) ∪ N(v)` such that `u` and `v` share no common neighbor other than possibly `x`
(which holds for ALL `x ∈ N(u) ∪ N(v)` when `dist(u,v) ≥ 3`, AND for the unique common neighbor
`x ∈ N(u) ∩ N(v)` when `dist(u,v) = 2`!), `G - x` still contains a simple `u`–`v` path of length `2^k` (`k ≥ 2`). -/
theorem minimal_bad2_defect_pair_contraction_neighbor_robust {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u v : Fin n} (hcore : EG2Core G u v)
    (x : Fin n) (hx_nb : G.Adj u x ∨ G.Adj v x)
    (hdisj_other : ∀ z : Fin n, z ≠ x → ¬(G.Adj u z ∧ G.Adj v z)) :
    ∃ p : G.Walk u v, p.IsPath ∧ x ∉ p.support ∧ IsPowerOfTwo p.length := by
  have hmin := hcore.1
  have huv := hcore.2.1
  have hnotuv := hcore.2.2.1
  have hdx3 : G.degree x = 3 := hcore.2.2.2.2.2.2.1 x hx_nb
  have hxu : x ≠ u := by rcases hx_nb with h | h; exact (G.ne_of_adj h).symm; exact fun h1 => hnotuv (h1 ▸ h).symm
  have hxv : x ≠ v := by rcases hx_nb with h | h; exact fun h1 => hnotuv (h1 ▸ h); exact (G.ne_of_adj h).symm
  let Sx : Finset (Fin n) := Finset.univ.erase x
  let m := Sx.card
  have hm_lt : m < n := by
    have := induce_card_lt Sx (fun h => Finset.notMem_erase x Finset.univ (by rw [h]; simp))
    simpa [m] using this
  let e : Fin m ≃ {z : Fin n // z ∈ (Sx : Set (Fin n))} := (Fintype.equivFin _).symm
  let H : SimpleGraph (Fin m) := (G.induce (Sx : Set (Fin n))).comap e
  have huSx : u ∈ (Sx : Set (Fin n)) := Finset.mem_erase.mpr ⟨hxu.symm, Finset.mem_univ u⟩
  have hvSx : v ∈ (Sx : Set (Fin n)) := Finset.mem_erase.mpr ⟨hxv.symm, Finset.mem_univ v⟩
  let uH : Fin m := e.symm ⟨u, huSx⟩
  let vH : Fin m := e.symm ⟨v, hvSx⟩
  have huH_val : (e uH).1 = u := by simp [uH]
  have hvH_val : (e vH).1 = v := by simp [vH]
  have huvH : uH ≠ vH := fun h => huv (by rw [← huH_val, ← hvH_val, h])
  have hnotuvH : ¬H.Adj uH vH := fun h => hnotuv (by simpa [H, huH_val, hvH_val] using h)
  have hnpH : ¬HasPowerCycle H := by
    intro hpow
    exact induced_no_power_cycle hmin.2.1 Sx (hasPowerCycle_of_inj_hom ⟨e, fun h => h⟩ e.injective hpow)
  have hdisjH : ∀ z : Fin m, ¬(H.Adj uH z ∧ H.Adj vH z) := by
    intro z ⟨huz, hvz⟩
    have huzG : G.Adj u (e z).1 := by simpa [H, huH_val] using huz
    have hvzG : G.Adj v (e z).1 := by simpa [H, hvH_val] using hvz
    exact hdisj_other (e z).1 (Finset.ne_of_mem_erase (e z).2) ⟨huzG, hvzG⟩
  have hdegH : ∀ i : Fin m,
      (¬G.Adj x (e i).1 → H.degree i = G.degree (e i).1) ∧
      (G.Adj x (e i).1 → H.degree i = G.degree (e i).1 - 1) := by
    intro i
    have h1 : H.degree i = ((G.neighborFinset (e i).1).filter (· ∈ Sx)).card := by
      rw [comap_degree_equiv, induce_degree_eq]
    have hsp := degree_split_cut G Sx (e i).1
    have hfilt : (G.neighborFinset (e i).1).filter (· ∉ Sx) = (G.neighborFinset (e i).1).filter (· = x) := by
      ext z; simp [Sx]
    rw [hfilt] at hsp
    constructor
    · intro hnx
      have h0 : ((G.neighborFinset (e i).1).filter (· = x)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro z hz hzx; rw [mem_neighborFinset] at hz; exact hnx (hzx ▸ hz.symm)
      omega
    · intro hax
      have h1' : ((G.neighborFinset (e i).1).filter (· = x)).card = 1 := by
        have heq : (G.neighborFinset (e i).1).filter (· = x) = {x} := by
          ext z; simp [mem_filter, mem_neighborFinset, hax.symm]
        rw [heq]; simp
      omega
  let Q := mergeGraph H uH vH
  let v' : {i : Fin m // i ≠ uH} := ⟨vH, huvH.symm⟩
  have hQcard : Fintype.card {i : Fin m // i ≠ uH} < n := by
    rw [Fintype.card_subtype_compl, Fintype.card_unique, Fintype.card_fin]
    have := Fin.pos uH; omega
  have hQdeg := mergeGraph_degree_disjoint H huvH hnotuvH hdisjH
  have hnearQ : Near2 Q := by
    by_cases hboth : G.Adj u x ∧ G.Adj v x
    · have hv'2 : Q.degree v' = 2 := by
        rw [hQdeg.1, (hdegH uH).2 (huH_val ▸ hboth.1.symm), (hdegH vH).2 (hvH_val ▸ hboth.2.symm),
            huH_val, hvH_val, hcore.2.2.2.1, hcore.2.2.2.2.1]
      refine ⟨fun i => ?_, ?_⟩
      · by_cases hi : i = v'
        · subst hi; omega
        · rw [hQdeg.2 i hi]
          have hne_u : (e i.1).1 ≠ u := fun h => i.2 (e.injective (Subtype.ext (h.trans huH_val.symm)))
          have hne_v : (e i.1).1 ≠ v := fun h => hi (Subtype.ext (e.injective (Subtype.ext (h.trans hvH_val.symm))))
          have hd3 := hcore.2.2.2.2.2.1 (e i.1).1 hne_u hne_v
          by_cases hax : G.Adj x (e i.1).1
          · rw [(hdegH i.1).2 hax]; omega
          · rw [(hdegH i.1).1 hax]; omega
      · have hsub : Finset.univ.filter (fun i : {i : Fin m // i ≠ uH} => Q.degree i < 3) ⊆
            insert v' (Finset.univ.filter (fun i : {i : Fin m // i ≠ uH} =>
              G.Adj x (e i.1).1 ∧ i ≠ v')) := by
          intro i hi; simp only [mem_filter, mem_univ, true_and, mem_insert] at hi ⊢
          by_cases hiv : i = v'
          · exact Or.inl hiv
          · right; refine ⟨?_, hiv⟩
            rw [hQdeg.2 i hiv] at hi
            have hne_u : (e i.1).1 ≠ u := fun h => i.2 (e.injective (Subtype.ext (h.trans huH_val.symm)))
            have hne_v : (e i.1).1 ≠ v := fun h => hiv (Subtype.ext (e.injective (Subtype.ext (h.trans hvH_val.symm))))
            have hd3 := hcore.2.2.2.2.2.1 (e i.1).1 hne_u hne_v
            by_contra hnx
            rw [(hdegH i.1).1 hnx] at hi; omega
        have hother_le1 : (Finset.univ.filter (fun i : {i : Fin m // i ≠ uH} =>
            G.Adj x (e i.1).1 ∧ i ≠ v')).card ≤ 1 := by
          calc _ ≤ ((G.neighborFinset x) \ {u, v}).card := by
                apply Finset.card_le_card_of_injOn (fun i => (e i.1).1)
                · intro i hi; simp only [mem_coe, mem_filter, mem_univ, true_and, mem_sdiff,
                    mem_neighborFinset, mem_insert, mem_singleton, not_or] at hi ⊢
                  refine ⟨hi.1, fun h => i.2 (e.injective (Subtype.ext (h.trans huH_val.symm))),
                    fun h => hi.2 (Subtype.ext (e.injective (Subtype.ext (h.trans hvH_val.symm))))⟩
                · intro i1 _ i2 _ h; exact Subtype.ext (e.injective (Subtype.ext h))
            _ = 1 := by
                have hsubuv : ({u, v} : Finset (Fin n)) ⊆ G.neighborFinset x := by
                  intro z hz; rcases Finset.mem_insert.mp hz with rfl | h1
                  · simp [mem_neighborFinset, hboth.1.symm]
                  · rw [Finset.mem_singleton.mp h1]; simp [mem_neighborFinset, hboth.2.symm]
                rw [Finset.card_sdiff hsubuv, card_neighborFinset_eq_degree, hdx3, Finset.card_pair huv]
        calc _ ≤ (insert v' _).card := Finset.card_le_card hsub
          _ ≤ _ + 1 := Finset.card_insert_le _ _
          _ ≤ 2 := by omega
    · have hv'3 : Q.degree v' = 3 := by
        rw [hQdeg.1]
        rcases hx_nb with hux | hvx
        · have hnvx : ¬G.Adj v x := fun h => hboth ⟨hux, h⟩
          rw [(hdegH uH).2 (huH_val ▸ hux.symm), (hdegH vH).1 (fun h => hnvx (hvH_val ▸ h.symm)),
              huH_val, hvH_val, hcore.2.2.2.1, hcore.2.2.2.2.1]
        · have hnux : ¬G.Adj u x := fun h => hboth ⟨h, hvx⟩
          rw [(hdegH uH).1 (fun h => hnux (huH_val ▸ h.symm)), (hdegH vH).2 (hvH_val ▸ hvx.symm),
              huH_val, hvH_val, hcore.2.2.2.1, hcore.2.2.2.2.1]
      refine ⟨fun i => ?_, ?_⟩
      · by_cases hi : i = v'
        · subst hi; omega
        · rw [hQdeg.2 i hi]
          have hne_u : (e i.1).1 ≠ u := fun h => i.2 (e.injective (Subtype.ext (h.trans huH_val.symm)))
          have hne_v : (e i.1).1 ≠ v := fun h => hi (Subtype.ext (e.injective (Subtype.ext (h.trans hvH_val.symm))))
          have hd3 := hcore.2.2.2.2.2.1 (e i.1).1 hne_u hne_v
          by_cases hax : G.Adj x (e i.1).1
          · rw [(hdegH i.1).2 hax]; omega
          · rw [(hdegH i.1).1 hax]; omega
      · have hsub : Finset.univ.filter (fun i : {i : Fin m // i ≠ uH} => Q.degree i < 3) ⊆
            Finset.univ.filter (fun i : {i : Fin m // i ≠ uH} => G.Adj x (e i.1).1 ∧ i ≠ v') := by
          intro i hi; simp only [mem_filter, mem_univ, true_and] at hi ⊢
          by_cases hiv : i = v'
          · subst hiv; omega
          · refine ⟨?_, hiv⟩
            rw [hQdeg.2 i hiv] at hi
            have hne_u : (e i.1).1 ≠ u := fun h => i.2 (e.injective (Subtype.ext (h.trans huH_val.symm)))
            have hne_v : (e i.1).1 ≠ v := fun h => hiv (Subtype.ext (e.injective (Subtype.ext (h.trans hvH_val.symm))))
            have hd3 := hcore.2.2.2.2.2.1 (e i.1).1 hne_u hne_v
            by_contra hnx
            rw [(hdegH i.1).1 hnx] at hi; omega
        calc _ ≤ (Finset.univ.filter (fun i : {i : Fin m // i ≠ uH} => G.Adj x (e i.1).1 ∧ i ≠ v')).card :=
              Finset.card_le_card hsub
          _ ≤ ((G.neighborFinset x) \ {u, v}).card := by
                apply Finset.card_le_card_of_injOn (fun i => (e i.1).1)
                · intro i hi; simp only [mem_coe, mem_filter, mem_univ, true_and, mem_sdiff,
                    mem_neighborFinset, mem_insert, mem_singleton, not_or] at hi ⊢
                  refine ⟨hi.1, fun h => i.2 (e.injective (Subtype.ext (h.trans huH_val.symm))),
                    fun h => hi.2 (Subtype.ext (e.injective (Subtype.ext (h.trans hvH_val.symm))))⟩
                · intro i1 _ i2 _ h; exact Subtype.ext (e.injective (Subtype.ext h))
          _ ≤ 2 := by
                rcases hx_nb with hux | hvx
                · have hsub1 : (G.neighborFinset x) \ {u, v} ⊆ (G.neighborFinset x).erase u := by
                    intro z hz; simp only [mem_sdiff, mem_insert, mem_singleton, not_or, mem_erase] at hz ⊢
                    exact ⟨hz.2.1, hz.1⟩
                  calc _ ≤ ((G.neighborFinset x).erase u).card := Finset.card_le_card hsub1
                    _ = 2 := by rw [Finset.card_erase_of_mem (by simp [mem_neighborFinset, hux.symm]),
                                    card_neighborFinset_eq_degree, hdx3]
                · have hsub1 : (G.neighborFinset x) \ {u, v} ⊆ (G.neighborFinset x).erase v := by
                    intro z hz; simp only [mem_sdiff, mem_insert, mem_singleton, not_or, mem_erase] at hz ⊢
                    exact ⟨hz.2.2, hz.1⟩
                  calc _ ≤ ((G.neighborFinset x).erase v).card := Finset.card_le_card hsub1
                    _ = 2 := by rw [Finset.card_erase_of_mem (by simp [mem_neighborFinset, hvx.symm]),
                                    card_neighborFinset_eq_degree, hdx3]
  rcases mergeGraph_cycle_lifts_to_path huvH hnpH (minimal_bad2_smaller_type hmin Q hQcard hnearQ) with
    ⟨pH, hpH_path, hpH_len⟩
  let f : H →g G := ⟨fun i => (e i).1, fun h => h⟩
  have hf_inj : Function.Injective f := fun i1 i2 h => e.injective (Subtype.ext h)
  let pG : G.Walk u v := (pH.map f).copy huH_val hvH_val
  refine ⟨pG, ?_, ?_, ?_⟩
  · refine Walk.IsPath.mk' ?_
    rw [Walk.support_copy, Walk.support_map]
    exact hpH_path.support_nodup.map hf_inj
  · rw [Walk.support_copy, Walk.support_map]
    simp only [List.mem_map, not_exists, not_and]
    intro i _ hi
    exact Finset.ne_of_mem_erase (e i).2 hi
  · simpa [pG, Walk.length_copy, Walk.length_map] using hpH_len

/-! ### Pillar IV: Nonbipartiteness of `G - u` & Single-Edge Odd-Transversal Constraints -/

lemma walk_bipartite_parity {V : Type*} {G : SimpleGraph V}
    (c : V → Bool) (hc : ∀ x y, G.Adj x y → c x ≠ c y)
    {a b : V} (p : G.Walk a b) :
    (Even p.length → c a = c b) ∧ (Odd p.length → c a ≠ c b) := by
  induction p with
  | nil =>
    exact ⟨fun _ => rfl, fun h => by simp at h⟩
  | @cons x y z hxy w ih =>
    have hcxy : c x ≠ c y := hc x y hxy
    constructor
    · intro hev
      have hodd : Odd w.length := by
        rw [Walk.length_cons] at hev; exact Nat.even_add_one.mp hev
      have hcyz := ih.2 hodd
      cases hcx : c x <;> cases hcy : c y <;> cases hcz : c z <;> simp_all
    · intro hodd
      have hev : Even w.length := by
        rw [Walk.length_cons] at hodd; exact Nat.odd_add_one.mp hodd
      have hcyz := ih.1 hev
      rw [← hcyz]; exact hcxy

lemma power_of_two_even {m : ℕ} (hm : IsPowerOfTwo m) : Even m := by
  rcases hm with ⟨k, hk, rfl⟩
  have hk1 : k ≠ 0 := by omega
  exact (Nat.even_pow' hk1).mpr (by decide)

/-- Theorem 4.1: In `EG2Core G u v`, `G - u` is NONBIPARTITE (for ALL distances `dist(u,v) ≥ 2`). -/
theorem minimal_bad2_delete_defect_nonbipartite {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u v : Fin n} (hcore : EG2Core G u v) :
    ¬∃ c : Fin n → Bool, ∀ x y : Fin n, x ≠ u → y ≠ u → G.Adj x y → c x ≠ c y := by
  rintro ⟨c, hc⟩
  have hmin := hcore.1
  have huv := hcore.2.1
  have hdu2 : (G.neighborFinset u).card = 2 := by rw [card_neighborFinset_eq_degree]; exact hcore.2.2.2.1
  rcases Finset.card_eq_two.mp hdu2 with ⟨a1, a2, _, hupair⟩
  have hua1 : G.Adj u a1 := by rw [← mem_neighborFinset, hupair]; simp
  have hua2 : G.Adj u a2 := by rw [← mem_neighborFinset, hupair]; simp
  have ha1u : a1 ≠ u := (G.ne_of_adj hua1).symm
  have ha2u : a2 ≠ u := (G.ne_of_adj hua2).symm
  have hca12 : c a1 ≠ c a2 := by
    intro heq
    apply hcore.2.2.2.2.2.2.2.2.1
    refine ⟨fun x => if x = u then !(c a1) else c x, fun x y hxy => ?_⟩
    by_cases hxu : x = u
    · subst hxu
      have hyu : y ≠ x := (G.ne_of_adj hxy).symm
      have hy_in : y ∈ ({a1, a2} : Finset (Fin n)) := by rw [← hupair, mem_neighborFinset]; exact hxy
      simp only [↓reduceIte, hyu]
      rcases Finset.mem_insert.mp hy_in with rfl | h1
      · simp
      · rw [Finset.mem_singleton.mp h1, ← heq]; simp
    · by_cases hyu : y = u
      · subst hyu
        have hx_in : x ∈ ({a1, a2} : Finset (Fin n)) := by rw [← hupair, mem_neighborFinset]; exact hxy.symm
        simp only [hxu, ↓reduceIte]
        rcases Finset.mem_insert.mp hx_in with rfl | h1
        · simp
        · rw [Finset.mem_singleton.mp h1, ← heq]; simp
      · simp only [hxu, hyu, ↓reduceIte]; exact hc x y hxu hyu hxy
  have path_forces_color : ∀ (ai aj : Fin n),
      ({ai, aj} : Finset (Fin n)) = G.neighborFinset u →
      (∃ p : G.Walk u v, p.IsPath ∧ ai ∉ p.support ∧ IsPowerOfTwo p.length) →
      c v ≠ c aj := by
    intro ai aj hset ⟨p, hp_path, hai_not, hplen⟩
    cases p with
    | nil => exact absurd rfl huv
    | @cons _ w _ huw q =>
      have hw_in : w ∈ ({ai, aj} : Finset (Fin n)) := by rw [hset, mem_neighborFinset]; exact huw
      have hw_ne_ai : w ≠ ai := fun h => hai_not (by simp [h])
      have hw_eq_aj : w = aj := by
        rcases Finset.mem_insert.mp hw_in with h1 | h2
        · exact absurd h1 hw_ne_ai
        · exact Finset.mem_singleton.mp h2
      subst hw_eq_aj
      have hu_not_q : u ∉ q.support := (List.nodup_cons.mp hp_path.support_nodup).1
      let Gu := G.induce {z : Fin n | z ≠ u}
      have lift_q : ∀ {x y : Fin n} (r : G.Walk x y), u ∉ r.support →
          ∃ (hx : x ≠ u) (hy : y ≠ u) (r' : Gu.Walk ⟨x, hx⟩ ⟨y, hy⟩), r'.length = r.length := by
        intro x y r
        induction r with
        | nil =>
          intro hnu; have hx : x ≠ u := fun h => hnu (by simp [h])
          exact ⟨hx, hx, Walk.nil, rfl⟩
        | @cons a b d hab r ih =>
          intro hnu
          have ha : a ≠ u := fun h => hnu (by simp [h])
          have hr : u ∉ r.support := fun h => hnu (List.mem_cons_of_mem a h)
          rcases ih hr with ⟨hb, hd, r', hlen⟩
          exact ⟨ha, hd, Walk.cons hab r', by simp [hlen]⟩
      rcases lift_q q hu_not_q with ⟨_, _, q', hq'len⟩
      have hodd_q' : Odd q'.length := by
        have hev := power_of_two_even hplen
        rw [Walk.length_cons] at hev
        rw [hq'len]; exact Nat.even_add_one.mp hev
      have hbip := walk_bipartite_parity (G := Gu) (fun z => c z.1)
        (fun x y hxy => hc x.1 y.1 x.2 y.2 hxy) q'
      exact (hbip.2 hodd_q').symm
  by_cases hcomm : ∃ z : Fin n, G.Adj u z ∧ G.Adj v z
  · rcases hcomm with ⟨z, huz, hvz⟩
    have hz_uniq : ∀ w : Fin n, w ≠ z → ¬(G.Adj u w ∧ G.Adj v w) := by
      intro w hwz ⟨huw, hvw⟩
      have hc4 := minimal_bad2_c4_free hmin u v huv
      have hsub : ({z, w} : Finset (Fin n)) ⊆ G.neighborFinset u ∩ G.neighborFinset v := by
        intro t ht; rcases Finset.mem_insert.mp ht with rfl | h1
        · simp [mem_inter, mem_neighborFinset, huz, hvz]
        · rw [Finset.mem_singleton.mp h1]; simp [mem_inter, mem_neighborFinset, huw, hvw]
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_pair hwz.symm] at hcard; omega
    have hpath := minimal_bad2_defect_pair_contraction_neighbor_robust hcore z (Or.inl huz) hz_uniq
    have hz_in : z ∈ ({a1, a2} : Finset (Fin n)) := by rw [← hupair, mem_neighborFinset]; exact huz
    rcases Finset.mem_insert.mp hz_in with hza1 | hza2
    · subst hza1
      have hcv_ne_a2 := path_forces_color z a2 hupair.symm hpath
      have hcv_ne_a1 : c v ≠ c z := hc v z huv.symm ha1u hvz
      cases h1 : c z <;> cases h2 : c a2 <;> cases h3 : c v <;> simp_all
    · have hza2' : z = a2 := Finset.mem_singleton.mp hza2
      subst hza2'
      have hcv_ne_a1 := path_forces_color z a1 (by rw [← hupair]; ext t; simp [or_comm]) hpath
      have hcv_ne_a2 : c v ≠ c z := hc v z huv.symm ha2u hvz
      cases h1 : c a1 <;> cases h2 : c z <;> cases h3 : c v <;> simp_all
  · push Not at hcomm
    have hpath1 := minimal_bad2_defect_pair_contraction_neighbor_robust hcore a1 (Or.inl hua1)
      (fun z _ ⟨h1, h2⟩ => hcomm z h1 h2)
    have hpath2 := minimal_bad2_defect_pair_contraction_neighbor_robust hcore a2 (Or.inl hua2)
      (fun z _ ⟨h1, h2⟩ => hcomm z h1 h2)
    have hcv_ne_a2 := path_forces_color a1 a2 hupair.symm hpath1
    have hcv_ne_a1 := path_forces_color a2 a1 (by rw [← hupair]; ext t; simp [or_comm]) hpath2
    cases h1 : c a1 <;> cases h2 : c a2 <;> cases h3 : c v <;> simp_all

/-- Theorem 4.2 (Single-Edge Odd-Transversal Constraints in `EG2Core`):
If deleting a single edge `e = a b` makes `G` bipartite with 2-coloring `c`, then:
(1) `e` is not incident to `u` or `v`;
(2) BOTH `u` and `v` lie in the SAME color class as `a` and `b` (`c u = c a ∧ c v = c a`);
(3) BOTH endpoints `a` and `b` have degree EXACTLY 3 (`G.degree a = 3 ∧ G.degree b = 3`). -/
theorem minimal_bad2_odd_edge_transversal_constraints {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u v : Fin n} (hcore : EG2Core G u v)
    (a b : Fin n) (hab : G.Adj a b)
    (c : Fin n → Bool) (hc : ∀ x y : Fin n, (G.deleteEdges {s(a, b)}).Adj x y → c x ≠ c y) :
    a ≠ u ∧ b ≠ u ∧ a ≠ v ∧ b ≠ v ∧
    c u = c a ∧ c v = c a ∧
    G.degree a = 3 ∧ G.degree b = 3 := by
  have hmin := hcore.1
  have huv := hcore.2.1
  let G' := G.deleteEdges {s(a, b)}
  have hnp' : ¬HasPowerCycle G' := by
    intro hpow
    exact hmin.2.1 (hasPowerCycle_of_inj_hom (SimpleGraph.Hom.ofLE (SimpleGraph.deleteEdges_le _ _))
      Function.injective_id hpow)
  have hcab : c a = c b := by
    by_contra hne
    apply hcore.2.2.2.2.2.2.2.2.1
    refine ⟨c, fun x y hxy => ?_⟩
    by_cases hse : s(x, y) = s(a, b)
    · rw [Sym2.eq_iff] at hse
      rcases hse with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hne
      · exact hne.symm
    · exact hc x y ⟨hxy, hse⟩
  have hau : a ≠ u := by
    intro h; subst h
    apply minimal_bad2_delete_defect_nonbipartite hcore
    refine ⟨c, fun x y hxu hyu hxy => hc x y ⟨hxy, ?_⟩⟩
    intro hse; rw [Set.mem_singleton_iff, Sym2.eq_iff] at hse
    rcases hse with ⟨rfl, _⟩ | ⟨_, rfl⟩
    · exact hxu rfl
    · exact hyu rfl
  have hbu : b ≠ u := by
    intro h; subst h
    apply minimal_bad2_delete_defect_nonbipartite hcore
    refine ⟨c, fun x y hxu hyu hxy => hc x y ⟨hxy, ?_⟩⟩
    intro hse; rw [Set.mem_singleton_iff, Sym2.eq_iff] at hse
    rcases hse with ⟨_, rfl⟩ | ⟨rfl, _⟩
    · exact hyu rfl
    · exact hxu rfl
  have hcore_sw : EG2Core G v u :=
    ⟨hcore.1, hcore.2.1.symm, fun h => hcore.2.2.1 h.symm, hcore.2.2.2.2.1, hcore.2.2.2.1,
     fun z hzv hzu => hcore.2.2.2.2.2.1 z hzu hzv,
     fun z hz => hcore.2.2.2.2.2.2.1 z hz.symm,
     hcore.2.2.2.2.2.2.2.1, hcore.2.2.2.2.2.2.2.2.1,
     fun S hS hvS huS => hcore.2.2.2.2.2.2.2.2.2 S hS huS hvS⟩
  have hav : a ≠ v := by
    intro h; subst h
    apply minimal_bad2_delete_defect_nonbipartite hcore_sw
    refine ⟨c, fun x y hxv hyv hxy => hc x y ⟨hxy, ?_⟩⟩
    intro hse; rw [Set.mem_singleton_iff, Sym2.eq_iff] at hse
    rcases hse with ⟨rfl, _⟩ | ⟨_, rfl⟩
    · exact hxv rfl
    · exact hyv rfl
  have hbv : b ≠ v := by
    intro h; subst h
    apply minimal_bad2_delete_defect_nonbipartite hcore_sw
    refine ⟨c, fun x y hxv hyv hxy => hc x y ⟨hxy, ?_⟩⟩
    intro hse; rw [Set.mem_singleton_iff, Sym2.eq_iff] at hse
    rcases hse with ⟨_, rfl⟩ | ⟨rfl, _⟩
    · exact hyv rfl
    · exact hxv rfl
  have hdegG' : ∀ x : Fin n,
      (x ≠ a → x ≠ b → G'.degree x = G.degree x) ∧
      ((x = a ∨ x = b) → G'.degree x = G.degree x - 1) := by
    intro x; constructor
    · intro hxa hxb; simp only [← card_neighborFinset_eq_degree]
      congr 1; ext z; simp only [mem_neighborFinset, G', deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff]
      constructor
      · exact fun h => h.1
      · intro hxz; refine ⟨hxz, ?_⟩; rintro (⟨rfl, _⟩ | ⟨rfl, _⟩) <;> [exact hxa rfl; exact hxb rfl]
    · intro hxab; simp only [← card_neighborFinset_eq_degree]
      rcases hxab with rfl | rfl
      · have heq : G'.neighborFinset a = (G.neighborFinset a).erase b := by
          ext z; simp only [mem_neighborFinset, mem_erase, G', deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff]
          constructor
          · rintro ⟨haz, hne⟩; exact ⟨fun hzb => hne (Or.inl ⟨rfl, hzb⟩), haz⟩
          · rintro ⟨hzb, haz⟩; refine ⟨haz, ?_⟩
            rintro (⟨_, rfl⟩ | ⟨h1, _⟩); exact hzb rfl; exact G.ne_of_adj hab h1
        rw [heq, Finset.card_erase_of_mem (by simp [mem_neighborFinset, hab])]
      · have heq : G'.neighborFinset b = (G.neighborFinset b).erase a := by
          ext z; simp only [mem_neighborFinset, mem_erase, G', deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff]
          constructor
          · rintro ⟨hbz, hne⟩; exact ⟨fun hza => hne (Or.inr ⟨rfl, hza⟩), hbz⟩
          · rintro ⟨hza, hbz⟩; refine ⟨hbz, ?_⟩
            rintro (⟨h1, _⟩ | ⟨_, rfl⟩); exact G.ne_of_adj hab h1.symm; exact hza rfl
        rw [heq, Finset.card_erase_of_mem (by simp [mem_neighborFinset, hab.symm])]
  have opp_color_forces_adj : ∀ (w w' z z' : Fin n),
      ({w, w'} : Finset (Fin n)) = {u, v} →
      ({z, z'} : Finset (Fin n)) = {a, b} →
      w ≠ w' → z ≠ z' →
      c w ≠ c z → G.Adj w z := by
    intro w w' z z' hww' hzz' _ _ hcwz
    by_contra hnotadj
    have hwu : w = u ∨ w = v := by
      have : w ∈ ({u, v} : Finset (Fin n)) := hww' ▸ (by simp)
      simpa using this
    have hza : z = a ∨ z = b := by
      have : z ∈ ({a, b} : Finset (Fin n)) := hzz' ▸ (by simp)
      simpa using this
    have hwz : w ≠ z := fun h => hcwz (by rw [h])
    have hnotadj' : ¬G'.Adj w z := fun h => hnotadj h.1
    have hdisj_wz : ∀ t : Fin n, ¬(G'.Adj w t ∧ G'.Adj z t) := by
      intro t ⟨hwt, hzt⟩
      have h1 := hc w t hwt
      have h2 := hc z t hzt
      cases hcw : c w <;> cases hcz : c z <;> cases hct : c t <;> simp_all
    let Q := mergeGraph G' w z
    let z_sub : {x : Fin n // x ≠ w} := ⟨z, hwz.symm⟩
    have hcard : Fintype.card {x : Fin n // x ≠ w} < n := by
      rw [Fintype.card_subtype_compl, Fintype.card_unique, Fintype.card_fin]
      have := Fin.pos w; omega
    have hQdeg := mergeGraph_degree_disjoint G' hwz hnotadj' hdisj_wz
    have hw_not_ab : w ≠ a ∧ w ≠ b := by
      rcases hwu with rfl | rfl <;> [exact ⟨hau.symm, hbu.symm⟩; exact ⟨hav.symm, hbv.symm⟩]
    have hdw2 : G'.degree w = 2 := by
      rw [(hdegG' w).1 hw_not_ab.1 hw_not_ab.2]
      rcases hwu with rfl | rfl; exact hcore.2.2.2.1; exact hcore.2.2.2.2.1
    have hdz_ge2 : 2 ≤ G'.degree z := by
      rw [(hdegG' z).2 hza]
      have hzu : z ≠ u := by rcases hza with rfl | rfl; exact hau; exact hbu
      have hzv : z ≠ v := by rcases hza with rfl | rfl; exact hav; exact hbv
      have := hcore.2.2.2.2.2.1 z hzu hzv; omega
    have hnearQ : Near2 Q := by
      refine ⟨fun t => ?_, ?_⟩
      · by_cases htz : t = z_sub
        · subst htz; rw [hQdeg.1]; omega
        · rw [hQdeg.2 t htz]
          by_cases htab : t.1 = a ∨ t.1 = b
          · rw [(hdegG' t.1).2 htab]
            have htu : t.1 ≠ u := by rcases htab with h | h <;> rw [h]; exact hau; exact hbu
            have htv : t.1 ≠ v := by rcases htab with h | h <;> rw [h]; exact hav; exact hbv
            have := hcore.2.2.2.2.2.1 t.1 htu htv; omega
          · push Not at htab; rw [(hdegG' t.1).1 htab.1 htab.2]; exact hmin.1.1 t.1
      · have hsub : Finset.univ.filter (fun t : {x : Fin n // x ≠ w} => Q.degree t < 3) ⊆
            Finset.univ.filter (fun t : {x : Fin n // x ≠ w} => t.1 = w' ∨ t.1 = z') := by
          intro t ht; simp only [mem_filter, mem_univ, true_and] at ht ⊢
          by_cases htz : t = z_sub
          · subst htz; rw [hQdeg.1] at ht; omega
          · rw [hQdeg.2 t htz] at ht
            by_contra hnone; push Not at hnone
            have htz1 : t.1 ≠ z := fun h => htz (Subtype.ext h)
            have htab : t.1 ≠ a ∧ t.1 ≠ b := by
              have hnot : t.1 ∉ ({a, b} : Finset (Fin n)) := by rw [← hzz']; simp [htz1, hnone.2]
              exact ⟨fun h => hnot (by simp [h]), fun h => hnot (by simp [h])⟩
            have htuv : t.1 ≠ u ∧ t.1 ≠ v := by
              have hnot : t.1 ∉ ({u, v} : Finset (Fin n)) := by rw [← hww']; simp [t.2, hnone.1]
              exact ⟨fun h => hnot (by simp [h]), fun h => hnot (by simp [h])⟩
            rw [(hdegG' t.1).1 htab.1 htab.2] at ht
            have := hcore.2.2.2.2.2.1 t.1 htuv.1 htuv.2; omega
        calc _ ≤ (Finset.univ.filter (fun t : {x : Fin n // x ≠ w} => t.1 = w' ∨ t.1 = z')).card :=
              Finset.card_le_card hsub
          _ ≤ ({w', z'} : Finset (Fin n)).card := by
                apply Finset.card_le_card_of_injOn Subtype.val
                · intro t ht; simp only [mem_coe, mem_filter, mem_univ, true_and] at ht; simp [ht]
                · intro t1 _ t2 _ h; exact Subtype.ext h
          _ ≤ 2 := Finset.card_le_two
    rcases mergeGraph_cycle_lifts_to_path hwz hnp' (minimal_bad2_smaller_type hmin Q hcard hnearQ) with
      ⟨p, _, hplen⟩
    exact hcwz ((walk_bipartite_parity c hc p).1 (power_of_two_even hplen))
  have hab_ne : a ≠ b := G.ne_of_adj hab
  have hcua : c u = c a := by
    by_contra hne_u
    have hua : G.Adj u a := opp_color_forces_adj u v a b rfl rfl huv hab_ne hne_u
    have hub : G.Adj u b := opp_color_forces_adj u v b a rfl (by ext x; simp [or_comm]) huv hab_ne.symm (hcab ▸ hne_u)
    by_cases hne_v : c v ≠ c a
    · have hva : G.Adj v a := opp_color_forces_adj v u a b (by ext x; simp [or_comm]) rfl huv.symm hab_ne hne_v
      have hvb : G.Adj v b := opp_color_forces_adj v u b a (by ext x; simp [or_comm]) (by ext x; simp [or_comm]) huv.symm hab_ne.symm (hcab ▸ hne_v)
      have hc4 := minimal_bad2_c4_free hmin u v huv
      have hsub : ({a, b} : Finset (Fin n)) ⊆ G.neighborFinset u ∩ G.neighborFinset v := by
        intro z hz; rcases Finset.mem_insert.mp hz with rfl | h1
        · simp [mem_inter, mem_neighborFinset, hua, hva]
        · rw [Finset.mem_singleton.mp h1]; simp [mem_inter, mem_neighborFinset, hub, hvb]
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_pair hab_ne] at hcard; omega
    · push Not at hne_v
      have hdisj_uv : ∀ z : Fin n, ¬(G.Adj u z ∧ G.Adj v z) := by
        intro z ⟨huz, hvz⟩
        have huz' : G'.Adj u z := ⟨huz, fun hse => by
          rw [Set.mem_singleton_iff, Sym2.eq_iff] at hse
          rcases hse with ⟨h1, _⟩ | ⟨h1, _⟩ <;> [exact hau h1.symm; exact hbu h1.symm]⟩
        have hvz' : G'.Adj v z := ⟨hvz, fun hse => by
          rw [Set.mem_singleton_iff, Sym2.eq_iff] at hse
          rcases hse with ⟨h1, _⟩ | ⟨h1, _⟩ <;> [exact hav h1.symm; exact hbv h1.symm]⟩
        have h1 := hc u z huz'
        have h2 := hc v z hvz'
        cases hcu : c u <;> cases hcv : c v <;> cases hcz : c z <;> simp_all
      rcases minimal_bad2_defect_pair_contraction_edge_robust hcore hdisj_uv a b hab with ⟨p, _, hplen⟩
      have hcu_eq_cv := (walk_bipartite_parity c hc p).1 (power_of_two_even hplen)
      exact hne_u (hcu_eq_cv.trans hne_v)
  have hcva : c v = c a := by
    by_contra hne_v
    have hdisj_uv : ∀ z : Fin n, ¬(G.Adj u z ∧ G.Adj v z) := by
      intro z ⟨huz, hvz⟩
      have huz' : G'.Adj u z := ⟨huz, fun hse => by
        rw [Set.mem_singleton_iff, Sym2.eq_iff] at hse
        rcases hse with ⟨h1, _⟩ | ⟨h1, _⟩ <;> [exact hau h1.symm; exact hbu h1.symm]⟩
      have hvz' : G'.Adj v z := ⟨hvz, fun hse => by
        rw [Set.mem_singleton_iff, Sym2.eq_iff] at hse
        rcases hse with ⟨h1, _⟩ | ⟨h1, _⟩ <;> [exact hav h1.symm; exact hbv h1.symm]⟩
      have h1 := hc u z huz'
      have h2 := hc v z hvz'
      cases hcu : c u <;> cases hcv : c v <;> cases hcz : c z <;> simp_all
    rcases minimal_bad2_defect_pair_contraction_edge_robust hcore hdisj_uv a b hab with ⟨p, _, hplen⟩
    have hcu_eq_cv := (walk_bipartite_parity c hc p).1 (power_of_two_even hplen)
    exact hne_v (hcu_eq_cv.symm.trans hcua)
  have deg_eq3 : ∀ (z z' : Fin n), ({z, z'} : Finset (Fin n)) = {a, b} → z ≠ z' →
      c z = c a → z ≠ u → z ≠ v → G.degree z = 3 := by
    intro z z' hzz' _ hcz hzu hzv
    have hd3 := hcore.2.2.2.2.2.1 z hzu hzv
    by_contra hne3
    have hd4 : 4 ≤ G.degree z := by omega
    have hza : z = a ∨ z = b := by
      have : z ∈ ({a, b} : Finset (Fin n)) := hzz' ▸ (by simp)
      simpa using this
    have hdz'3 : 3 ≤ G'.degree z := by rw [(hdegG' z).2 hza]; omega
    have hex_w : ∃ w ∈ G'.neighborFinset z, w ∉ G.neighborFinset u := by
      by_contra hall
      push Not at hall
      have hle := Finset.card_le_card hall
      rw [card_neighborFinset_eq_degree, card_neighborFinset_eq_degree, hcore.2.2.2.1] at hle
      omega
    rcases hex_w with ⟨w, hwz, hwu_not⟩
    rw [mem_neighborFinset] at hwz hwu_not
    have hcw_ne : c w ≠ c u := by
      have := hc z w hwz; rw [hcz, ← hcua] at this; exact this.symm
    have huw : u ≠ w := fun h => hcw_ne (by rw [h])
    have hnotadj' : ¬G'.Adj u w := fun h => hwu_not h.1
    have hdisj_uw : ∀ t : Fin n, ¬(G'.Adj u t ∧ G'.Adj w t) := by
      intro t ⟨hut, hwt⟩
      have h1 := hc u t hut; have h2 := hc w t hwt
      cases h1' : c u <;> cases h2' : c w <;> cases h3' : c t <;> simp_all
    let Q := mergeGraph G' u w
    let w' : {x : Fin n // x ≠ u} := ⟨w, huw.symm⟩
    have hcard : Fintype.card {x : Fin n // x ≠ u} < n := by
      rw [Fintype.card_subtype_compl, Fintype.card_unique, Fintype.card_fin]
      have := Fin.pos u; omega
    have hQdeg := mergeGraph_degree_disjoint G' huw hnotadj' hdisj_uw
    have hdu' : G'.degree u = 2 := by rw [(hdegG' u).1 hau.symm hbu.symm, hcore.2.2.2.1]
    have hdw'_ge2 : 2 ≤ G'.degree w := by
      by_cases hwab : w = a ∨ w = b
      · rw [(hdegG' w).2 hwab]
        have hwu' : w ≠ u := huw.symm
        have hwv' : w ≠ v := by rcases hwab with rfl | rfl; exact hav; exact hbv
        have := hcore.2.2.2.2.2.1 w hwu' hwv'; omega
      · push Not at hwab; rw [(hdegG' w).1 hwab.1 hwab.2]; exact hmin.1.1 w
    have hnearQ : Near2 Q := by
      refine ⟨fun t => ?_, ?_⟩
      · by_cases htw : t = w'
        · subst htw; rw [hQdeg.1]; omega
        · rw [hQdeg.2 t htw]
          by_cases htab : t.1 = a ∨ t.1 = b
          · rw [(hdegG' t.1).2 htab]
            have htu : t.1 ≠ u := by rcases htab with h | h <;> rw [h]; exact hau; exact hbu
            have htv : t.1 ≠ v := by rcases htab with h | h <;> rw [h]; exact hav; exact hbv
            have := hcore.2.2.2.2.2.1 t.1 htu htv; omega
          · push Not at htab; rw [(hdegG' t.1).1 htab.1 htab.2]; exact hmin.1.1 t.1
      · have hsub : Finset.univ.filter (fun t : {x : Fin n // x ≠ u} => Q.degree t < 3) ⊆
            Finset.univ.filter (fun t : {x : Fin n // x ≠ u} => t.1 = v ∨ t.1 = z') := by
          intro t ht; simp only [mem_filter, mem_univ, true_and] at ht ⊢
          by_cases htw : t = w'
          · subst htw; rw [hQdeg.1] at ht; omega
          · rw [hQdeg.2 t htw] at ht
            by_contra hnone; push Not at hnone
            by_cases htz : t.1 = z
            · rw [htz] at ht; omega
            · have htab : t.1 ≠ a ∧ t.1 ≠ b := by
                have hnot : t.1 ∉ ({a, b} : Finset (Fin n)) := by rw [← hzz']; simp [htz, hnone.2]
                exact ⟨fun h => hnot (by simp [h]), fun h => hnot (by simp [h])⟩
              rw [(hdegG' t.1).1 htab.1 htab.2] at ht
              have := hcore.2.2.2.2.2.1 t.1 t.2 hnone.1; omega
        calc _ ≤ (Finset.univ.filter (fun t : {x : Fin n // x ≠ u} => t.1 = v ∨ t.1 = z')).card :=
              Finset.card_le_card hsub
          _ ≤ ({v, z'} : Finset (Fin n)).card := by
                apply Finset.card_le_card_of_injOn Subtype.val
                · intro t ht; simp only [mem_coe, mem_filter, mem_univ, true_and] at ht; simp [ht]
                · intro t1 _ t2 _ h; exact Subtype.ext h
          _ ≤ 2 := Finset.card_le_two
    rcases mergeGraph_cycle_lifts_to_path huw hnp' (minimal_bad2_smaller_type hmin Q hcard hnearQ) with
      ⟨p, _, hplen⟩
    exact hcw_ne ((walk_bipartite_parity c hc p).1 (power_of_two_even hplen)).symm
  exact ⟨hau, hbu, hav, hbv, hcua, hcva,
    deg_eq3 a b rfl hab_ne rfl hau hav,
    deg_eq3 b a (by ext x; simp [or_comm]) hab_ne.symm hcab.symm hbu hbv⟩

end E64Wave5Agent1EG2Core
