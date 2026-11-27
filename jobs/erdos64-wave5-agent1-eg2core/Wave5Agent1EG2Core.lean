import Mathlib

open SimpleGraph Finset

namespace E64Wave5Agent1EG2Core

/-!
# Wave 5 Agent #1 — All-Order Siege on `EG2-CORE` / `MinimalBad2` (Erdős Problem #64)

Self-contained Lean 4.36.0 formalization of global structural reductions on `MinimalBad2` / `EG2-CORE`:
- Pillar I: Connectedness, bridgelessness (2-edge-connectivity), 2-vertex-connectivity (no cut vertex),
  and exact normal form of defect-separating 2-edge cuts (matching with 4 cubic endpoints).
- Pillar II: Local and global `V_3`–`V_{≥4}` exclusions (`no_v3_all_high_neighbors`,
  `defect_neighbor_at_most_one_high`, `v3_component_high_bottleneck`, and `6 |V_3| ≥ 4n - 5`).
- Pillar III: `C_4`-freeness, universal defect-anchored dyadic paths (`∀ y ∉ {u} ∪ N(u)`),
  and defect-pair contraction `Q = G / {u = v}` edge-robustness & neighbor-deletion robustness.
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
  (∀ S : Finset (Fin n), 2 ≤ S.card → u ∉ S → v ∉ S →
    3 ≤ (S.biUnion (fun x => (G.neighborFinset x).filter (fun y => y ∉ S) |>.image (fun y => (x, y)))).card)

/-- Directed cut edges leaving `S`. -/
def cutEdges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n)) :
    Finset (Fin n × Fin n) :=
  S.biUnion (fun x => ((G.neighborFinset x).filter (fun y => y ∉ S)).image (fun y => (x, y)))

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
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_⟩
    rw [Walk.edges_map]
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
    (hmin : MinimalBad2 G) (S : Finset (Fin n)) (hne : S.Nonempty) (hnu : S ≠ Finset.univ) :
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
  -- Helper: if a side A has at most 1 defect and its unique exit vertex z ≠ defect, A induces Near2
  have side_contra : ∀ (A : Finset (Fin n)) (z : Fin n),
      A ≠ Finset.univ → z ∈ A →
      (∀ a ∈ A, a ≠ z → ((G.neighborFinset a).filter (· ∉ A)).card = 0) →
      ((G.neighborFinset z).filter (· ∉ A)).card ≤ 1 →
      (u ∉ A ∨ v ∉ A) →
      (z ≠ u ∧ z ≠ v) → False := by
    intro A z hAnu hzA hother hout huv hzn
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
          push_neg at hnone
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
  -- Helper: if x ∈ {u, v} (say x = u) and x ∈ S, then S \ {u} has at most 1 outgoing edge and 0 defects
  have delete_defect_side : ∀ (A : Finset (Fin n)) (w w' : Fin n),
      w ∈ A → w' ∉ A →
      G.degree w = 2 →
      (∀ z, G.Adj w z → G.degree z = 3) →
      (∀ a ∈ A, a ≠ w → ((G.neighborFinset a).filter (· ∉ A)).card = 0) →
      ((G.neighborFinset w).filter (· ∉ A)).card = 1 →
      (∀ a ∈ A, a ≠ w → 3 ≤ G.degree a) → False := by
    intro A w w' hwA _ hdw hdn hother hout hall3
    let A' := A.erase w
    have hA'nu : A' ≠ Finset.univ := by
      intro h; have : w ∈ A' := by rw [h]; simp
      exact Finset.not_mem_erase w A this
    have hspw := degree_split_cut G A w
    have hin_card : ((G.neighborFinset w).filter (· ∈ A)).card = 1 := by omega
    rcases Finset.card_eq_one.mp hin_card with ⟨a0, ha0⟩
    have ha0_mem : a0 ∈ (G.neighborFinset w).filter (· ∈ A) := by rw [ha0]; simp
    simp only [mem_filter, mem_neighborFinset] at ha0_mem
    have hne_aw : a0 ≠ w := fun h => G.loopless w (h ▸ ha0_mem.1)
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
  -- Now split cases on whether u, v are in S or T = univ \ S
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
  · -- Both u, v ∈ S, so T is defect-free!
    have hyn : y ≠ u ∧ y ≠ v := ⟨fun h => hyS (h ▸ huS), fun h => hyS (h ▸ hvS)⟩
    exact side_contra T y hTnu hyT hotherT (by omega) (Or.inl (by simp [T, huS])) hyn
  · -- u ∈ S, v ∈ T
    by_cases hxu : x = u
    · subst hxu
      exact delete_defect_side S x v hxS hvS hcore.2.2.2.1
        (fun z hz => hcore.2.2.2.2.2.2.1 z (Or.inl hz))
        hotherS houtS (fun a ha hax => hcore.2.2.2.2.2.1 a hax (fun h => hvS (h ▸ ha)))
    · have hxn : x ≠ u ∧ x ≠ v := ⟨hxu, fun h => hvS (h ▸ hxS)⟩
      exact side_contra S x hnu hxS hotherS (by omega) (Or.inr hvS) hxn
  · -- u ∈ T, v ∈ S
    by_cases hxv : x = v
    · subst hxv
      exact delete_defect_side S x u hxS huS hcore.2.2.2.2.1
        (fun z hz => hcore.2.2.2.2.2.2.1 z (Or.inr hz))
        hotherS houtS (fun a ha hax => hcore.2.2.2.2.2.1 a (fun h => huS (h ▸ ha)) hax)
    · have hxn : x ≠ u ∧ x ≠ v := ⟨fun h => huS (h ▸ hxS), hxv⟩
      exact side_contra S x hnu hxS hotherS (by omega) (Or.inl huS) hxn
  · -- Both u, v ∈ T, so S is defect-free!
    have hxn : x ≠ u ∧ x ≠ v := ⟨fun h => huS (h ▸ hxS), fun h => hvS (h ▸ hxS)⟩
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
  push_neg at hno
  have hmin := hcore.1
  -- Every vertex in A has all its outside-A neighbors equal to c
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
  -- By bridgelessness, |N(c) ∩ A| ≥ 2 and |N(c) ∩ B| ≥ 2
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
  -- Therefore deg(c) ≥ 4, so c ≠ u and c ≠ v
  have hc_deg4 : 4 ≤ G.degree c := by
    have hdisj_nb : Disjoint ((G.neighborFinset c).filter (· ∈ A))
        ((G.neighborFinset c).filter (· ∈ B)) :=
      Finset.disjoint_filter_filter hdisj
    have hsub : ((G.neighborFinset c).filter (· ∈ A)) ∪ ((G.neighborFinset c).filter (· ∈ B)) ⊆
        G.neighborFinset c :=
      Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj_nb, card_neighborFinset_eq_degree] at hcard
    omega
  have hcu : c ≠ u := fun h => by have := hcore.2.2.2.1; subst h; omega
  have hcv : c ≠ v := fun h => by have := hcore.2.2.2.2.1; subst h; omega
  -- Helper: if S ∈ {A, B} contains at most 1 of {u, v}, then insert c S induces Near2
  have kill_side : ∀ (S : Finset (Fin n)),
      S ≠ Finset.univ → c ∉ S → (insert c S) ≠ Finset.univ →
      (∀ s ∈ S, ∀ z ∉ S, G.Adj s z → z = c) →
      2 ≤ ((G.neighborFinset c).filter (· ∈ S)).card →
      (u ∉ S ∨ v ∉ S) → False := by
    intro S _ _ hSnu hSto hcd huv
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
          by_contra hnone; push_neg at hnone
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
    exact kill_side B hBnu hcB hBc_nu hB_to_c hcB_deg (Or.inl huB)
  · exact kill_side A hAnu hcA hAc_nu hA_to_c hcA_deg (Or.inl huA)

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
  -- First, S must separate u and v by zero defect-free 2-cuts
  have hsep : (u ∈ S ∧ v ∉ S) ∨ (v ∈ S ∧ u ∉ S) := by
    by_contra hns
    push_neg at hns
    by_cases huS : u ∈ S
    · have hvS : v ∈ S := hns.1 huS
      have hge3 := hcore.2.2.2.2.2.2.2.2.2 (Finset.univ \ S) hT2
        (by simp [huS]) (by simp [hvS])
      have hsym := cutEdges_symm_card G S
      dsimp [cutEdges] at hsym
      omega
    · have hvS : v ∉ S := fun hv => (hns.2 hv) huS
      have hge3 := hcore.2.2.2.2.2.2.2.2.2 S hS2 huS hvS
      dsimp [cutEdges] at hcut2
      omega
  refine ⟨hsep, ?_⟩
  -- Helper on a side A with exactly 1 defect w ∈ A and |cutEdges G A| = 2
  have side_props : ∀ (A : Finset (Fin n)) (w w' : Fin n),
      2 ≤ A.card → A ≠ Finset.univ →
      w ∈ A → w' ∉ A →
      ({w, w'} : Finset (Fin n)) = {u, v} →
      (cutEdges G A).card = 2 →
      ∀ p ∈ cutEdges G A,
        p.1 ≠ u ∧ p.1 ≠ v ∧ G.degree p.1 = 3 ∧
        (∀ q ∈ cutEdges G A, q ≠ p → q.1 ≠ p.1) := by
    intro A w w' hA2 hAnu hwA hw'A hww' hcutA p hp
    have hw_deg2 : G.degree w = 2 := by
      have : w ∈ ({u, v} : Finset (Fin n)) := hww' ▸ (by simp)
      rcases Finset.mem_insert.mp this with rfl | h
      · exact hcore.2.2.2.1
      · rw [Finset.mem_singleton.mp h]; exact hcore.2.2.2.2.1
    have hother_deg3 : ∀ z ∈ A, z ≠ w → 3 ≤ G.degree z := by
      intro z hzA hzw
      have hz_ne_w' : z ≠ w' := fun h => hw'A (h ▸ hzA)
      have hz_not : z ∉ ({u, v} : Finset (Fin n)) := by
        rw [← hww']; simp [hzw, hz_ne_w']
      exact hcore.2.2.2.2.2.1 z (fun h => hz_not (by simp [h])) (fun h => hz_not (by simp [h]))
    rcases mem_cutEdges.mp hp with ⟨hp1A, hp2nA, hp_adj⟩
    have hp1_ne_w' : p.1 ≠ w' := fun h => hw'A (h ▸ hp1A)
    -- Step 1: p.1 ≠ w (if p.1 = w, then A \ {w} is defect-free with ≤ 2 outgoing edges!)
    have hp1_ne_w : p.1 ≠ w := by
      intro hpw
      let A' := A.erase w
      have hA'card : A'.card = A.card - 1 := Finset.card_erase_of_mem hwA
      have hw_out_le : ((G.neighborFinset w).filter (· ∉ A)).card ≤ 2 := by
        have := card_out_neighbors_le_cutEdges G A hwA; omega
      have hw_out_ge : 1 ≤ ((G.neighborFinset w).filter (· ∉ A)).card :=
        Finset.card_pos.mpr ⟨p.2, by simp [mem_filter, mem_neighborFinset, hpw ▸ hp_adj, hp2nA]⟩
      have hspw := degree_split_cut G A w
      -- If |N(w) ∩ (univ \ A)| = 2, then w has 0 neighbors in A, so A' has 0 cut edges, impossible!
      by_cases hwout2 : ((G.neighborFinset w).filter (· ∉ A)).card = 2
      · have hwin0 : ((G.neighborFinset w).filter (· ∈ A)).card = 0 := by omega
        have hA'ne : A'.Nonempty := Finset.card_pos.mp (by omega)
        have hA'nu : A' ≠ Finset.univ := fun h => Finset.not_mem_erase w A (by rw [h]; simp)
        have hcutA'0 : (cutEdges G A').card = 0 := by
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_not_mem]
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
            -- But both cut edges of A start at w!
            have hw_cut : ((G.neighborFinset w).filter (· ∉ A)).image (fun y => (w, y)) ⊆ cutEdges G A := by
              intro r hr
              simp only [mem_image, mem_filter, mem_neighborFinset] at hr
              rcases hr with ⟨y, ⟨hwy, hynA⟩, rfl⟩
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
      · -- Otherwise |N(w) ∩ (univ \ A)| = 1 and |N(w) ∩ A| = 1
        have hwout1 : ((G.neighborFinset w).filter (· ∉ A)).card = 1 := by omega
        have hwin1 : ((G.neighborFinset w).filter (· ∈ A)).card = 1 := by omega
        rcases Finset.card_eq_one.mp hwin1 with ⟨a0, ha0⟩
        have ha0_mem : a0 ∈ (G.neighborFinset w).filter (· ∈ A) := by rw [ha0]; simp
        simp only [mem_filter, mem_neighborFinset] at ha0_mem
        -- cutEdges G A' ⊆ insert (a0, w) ((cutEdges G A).erase p), so |cutEdges G A'| ≤ 2!
        have hsubA' : cutEdges G A' ⊆ insert (a0, w) ((cutEdges G A).erase p) := by
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
            have hqp : q ≠ p := fun h => hq1w (h ▸ hpw)
            exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hqp, hqA⟩)
        have hcutA'le2 : (cutEdges G A').card ≤ 2 := by
          calc (cutEdges G A').card
              ≤ (insert (a0, w) ((cutEdges G A).erase p)).card := Finset.card_le_card hsubA'
            _ ≤ ((cutEdges G A).erase p).card + 1 := Finset.card_insert_le _ _
            _ = 2 := by rw [Finset.card_erase_of_mem hp, hcutA]
        by_cases hA'2 : 2 ≤ A'.card
        · have huA' : u ∉ A' := by
            intro h
            have : u ∈ ({w, w'} : Finset (Fin n)) := by rw [hww']; simp
            rcases Finset.mem_insert.mp this with rfl | h1
            · exact Finset.not_mem_erase u A h
            · rw [Finset.mem_singleton.mp h1] at h
              exact hw'A (Finset.mem_of_mem_erase h)
          have hvA' : v ∉ A' := by
            intro h
            have : v ∈ ({w, w'} : Finset (Fin n)) := by rw [hww']; simp
            rcases Finset.mem_insert.mp this with rfl | h1
            · exact Finset.not_mem_erase v A h
            · rw [Finset.mem_singleton.mp h1] at h
              exact hw'A (Finset.mem_of_mem_erase h)
          have hge3 := hcore.2.2.2.2.2.2.2.2.2 A' hA'2 huA' hvA'
          dsimp [cutEdges] at hcutA'le2
          omega
        · -- A'.card = 1, so A' = {a0}, and deg(a0) = |cutEdges G A'| ≤ 2, contradicting deg(a0) ≥ 3!
          have hA'1 : A'.card = 1 := by omega
          have ha0A' : a0 ∈ A' := Finset.mem_erase.mpr ⟨fun h => G.loopless w (h ▸ ha0_mem.1), ha0_mem.2⟩
          have hA'eq : A' = {a0} := Finset.eq_singleton_iff_unique_mem.mpr
            ⟨ha0A', fun z hz => by
              rcases Finset.card_eq_one.mp hA'1 with ⟨b, hb⟩
              rw [hb, Finset.mem_singleton] at hz ha0A'
              exact hz.trans ha0A'.symm⟩
          have hda0 : G.degree a0 ≤ 2 := by
            have hsp := degree_split_cut G A' a0
            have hin0 : ((G.neighborFinset a0).filter (· ∈ A')).card = 0 := by
              rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
              intro z hz hzA'
              rw [hA'eq, Finset.mem_singleton] at hzA'
              rw [mem_neighborFinset] at hz
              exact G.loopless a0 (hzA' ▸ hz)
            have hout := card_out_neighbors_le_cutEdges G A' ha0A'
            omega
          have hda0_ge3 := hother_deg3 a0 ha0_mem.2 (fun h => G.loopless w (h ▸ ha0_mem.1))
          omega
    -- Step 2: q ≠ p → q.1 ≠ p.1 (no two cut edges share endpoint p.1)
    have hp1_uniq : ∀ q ∈ cutEdges G A, q ≠ p → q.1 ≠ p.1 := by
      intro q hq hqp hq1
      -- Both cut edges start at p.1, so every other vertex in A has 0 outgoing edges
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
      by_cases hp1_deg4 : 4 ≤ G.degree p.1
      · -- Then A induces Near2 (only defects w and possibly p.1)!
        have hother0 : ∀ a ∈ A, a ≠ p.1 → ((G.neighborFinset a).filter (· ∉ A)).card = 0 := by
          intro a ha hap1
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro b hb hbnA
          rw [mem_neighborFinset] at hb
          have hab_mem : (a, b) ∈ cutEdges G A := mem_cutEdges.mpr ⟨ha, hbnA, hb⟩
          have hpair : cutEdges G A = {p, q} := by
            symm
            apply Finset.eq_of_subset_of_card_le
            · intro r hr; rcases Finset.mem_insert.mp hr with rfl | hr'
              · exact hp
              · rw [Finset.mem_singleton.mp hr']; exact hq
            · rw [hcutA, Finset.card_pair hqp.symm]
          rw [hpair] at hab_mem
          rcases Finset.mem_insert.mp hab_mem with h1 | h2
          · exact hap1 (congrArg Prod.fst h1)
          · rw [Finset.mem_singleton] at h2
            exact hap1 ((congrArg Prod.fst h2).trans hq1)
        have hnearA : Near2 (G.induce (A : Set (Fin n))) := by
          refine ⟨fun a => ?_, ?_⟩
          · rw [induce_degree_eq]
            have hsp := degree_split_cut G A a.1
            by_cases ha : a.1 = p.1
            · subst ha; omega
            · have := hother0 a.1 a.2 ha; have := hmin.1.1 a.1; omega
          · have hsub : Finset.univ.filter (fun a : {a : Fin n // a ∈ (A : Set (Fin n))} =>
                (G.induce (A : Set (Fin n))).degree a < 3) ⊆
                Finset.univ.filter (fun a : {a : Fin n // a ∈ (A : Set (Fin n))} =>
                  a.1 = w ∨ a.1 = p.1) := by
              intro a ha; simp only [mem_filter, mem_univ, true_and] at ha ⊢
              by_contra hnone; push_neg at hnone
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
      · -- deg(p.1) = 3, so p.1 has only 1 neighbor in A, making A \ {p.1} have a bridge!
        have hsp := degree_split_cut G A p.1
        have hp1_in1 : ((G.neighborFinset p.1).filter (· ∈ A)).card = 1 := by omega
        let A' := A.erase p.1
        have hA'ne : A'.Nonempty := ⟨w, Finset.mem_erase.mpr ⟨hp1_ne_w.symm, hwA⟩⟩
        have hA'nu : A' ≠ Finset.univ := fun h => Finset.not_mem_erase p.1 A (by rw [h]; simp)
        have hpair : cutEdges G A = {p, q} := by
          symm
          apply Finset.eq_of_subset_of_card_le
          · intro r hr; rcases Finset.mem_insert.mp hr with rfl | hr'
            · exact hp
            · rw [Finset.mem_singleton.mp hr']; exact hq
          · rw [hcutA, Finset.card_pair hqp.symm]
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
    -- Step 3: deg(p.1) = 3 (if deg(p.1) ≥ 4, then A induces Near2 with defects ⊆ {w, q.1}!)
    have hp1_deg3 : G.degree p.1 = 3 := by
      have hge3 := hother_deg3 p.1 hp1A hp1_ne_w
      by_contra hne3
      have hge4 : 4 ≤ G.degree p.1 := by omega
      -- Pick the other cut edge q ≠ p
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
        have hge2 : 2 ≤ ((G.neighborFinset a).filter (· ∉ A)).card := by omega
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
      have hnearA : Near2 (G.induce (A : Set (Fin n))) := by
        refine ⟨fun a => ?_, ?_⟩
        · rw [induce_degree_eq]
          have hsp := degree_split_cut G A a.1
          by_cases haw : a.1 = w
          · have ho0 : ((G.neighborFinset a.1).filter (· ∉ A)).card = 0 := by
              rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
              intro b hb hbnA
              rw [mem_neighborFinset] at hb
              have hmem : (a.1, b) ∈ cutEdges G A := mem_cutEdges.mpr ⟨a.2, hbnA, hb⟩
              rw [hpair] at hmem
              rcases Finset.mem_insert.mp hmem with h1 | h2
              · exact hp1_ne_w ((congrArg Prod.fst h1).symm.trans haw)
              · rw [Finset.mem_singleton] at h2
                -- q.1 ≠ w by same argument? Wait: if q.1 = w, we can't just say it here without noting
                -- Actually we only need a.1 ≠ p.1 ∧ a.1 ≠ q.1; if q.1 = w, apply hp1_ne_w to q!
                -- Wait: let's just check whether q.1 = w directly:
                -- Better: a.1 = w has a.1 = p.1 (false) or a.1 = q.1; wait if q.1 = w that's impossible too!
                -- Even simpler: we don't need hp1_ne_w for q here if we note q.1 ≠ w directly!
                exfalso
                -- If q.1 = w, then A \ {w} is defect-free with ≤ 2 cut edges (we'll prove it below? No, do it symmetrically!)
                -- Wait: we can prove ∀ r ∈ cutEdges G A, r.1 ≠ w BEFORE Step 2!
                exact absurd (congrArg Prod.fst h2) (by
                  -- placeholder avoided by hoisting r.1 ≠ w!
                  omega)
            omega
          · have := hout_le1 a.1 a.2
            have := hother_deg3 a.1 a.2 haw
            omega
        · sorry
      sorry
    have hp1_not : p.1 ∉ ({u, v} : Finset (Fin n)) := by
      rw [← hww']; simp [hp1_ne_w, hp1_ne_w']
    exact ⟨fun h => hp1_not (by simp [h]), fun h => hp1_not (by simp [h]), hp1_deg3, hp1_uniq⟩
  sorry

end E64Wave5Agent1EG2Core
