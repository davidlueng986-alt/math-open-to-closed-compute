import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace E64Wave5Agent2EGRob

open SimpleGraph Finset

/-- Power-of-two cycle length `2^k` with `k ≥ 2` (`4, 8, 16, ...`). -/
def IsPowerTwo (len : ℕ) : Prop :=
  ∃ k : ℕ, 2 ≤ k ∧ len = 2 ^ k

/-- A simple graph has a `2^k`-cycle (`k ≥ 2`). -/
def HasPower {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ IsPowerTwo p.length

/-- Minimum degree at least 3 on a nonempty finite graph. -/
def MinDeg3 {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  Nonempty V ∧ ∀ v : V, 3 ≤ G.degree v

/-- Original Erdős–Gyárfás Conjecture (Erdős #64). -/
def Erdos64 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], MinDeg3 G → HasPower G

/-- Two-defect near-cubic class `Near2`: `δ(G) ≥ 2`, `≤ 2` degree-2 vertices, `∃ v, deg(v) ≥ 3`. -/
def Near2 {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  (∀ v : V, 2 ≤ G.degree v) ∧
  (Finset.univ.filter (fun v => G.degree v = 2)).card ≤ 2 ∧
  ∃ v : V, 3 ≤ G.degree v

/-- Two-defect Erdős–Gyárfás Conjecture (`EG2`). -/
def EG2 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], Near2 G → HasPower G

/-- Edge deletion `G - ab`. -/
def delEdge {V : Type*} (G : SimpleGraph V) (a b : V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ ¬((x = a ∧ y = b) ∨ (x = b ∧ y = a))
  symm _ _ h := ⟨G.symm h.1, fun h' => h.2 (h'.elim (fun ⟨h1, h2⟩ => Or.inr ⟨h2, h1⟩)
    (fun ⟨h1, h2⟩ => Or.inl ⟨h2, h1⟩))⟩
  loopless x h := G.loopless x h.1

instance instDecidableRelDelEdge {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (a b : V) : DecidableRel (delEdge G a b).Adj := by
  intro x y; unfold delEdge; infer_instance

/-- Edge addition `G + ab` (for `a ≠ b`). -/
def addEdge {V : Type*} (G : SimpleGraph V) (a b : V) (hab : a ≠ b) : SimpleGraph V where
  Adj x y := G.Adj x y ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a)
  symm _ _ h := by
    rcases h with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl (G.symm h)
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  loopless x h := by
    rcases h with h | ⟨rfl, h2⟩ | ⟨rfl, h2⟩
    · exact G.loopless x h
    · exact hab h2
    · exact hab h2.symm

instance instDecidableRelAddEdge {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (a b : V) (hab : a ≠ b) : DecidableRel (addEdge G a b hab).Adj := by
  intro x y; unfold addEdge; infer_instance

/-- Cut size `|∂_G(S)|` as ordered crossing pairs `(x, y)` with `x ∈ S, y ∉ S, G.Adj x y`. -/
def cutSize {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : ℕ :=
  (Finset.univ.filter (fun p : V × V => p.1 ∈ S ∧ p.2 ∉ S ∧ G.Adj p.1 p.2)).card

/-- 2-edge-connectivity. -/
def TwoEdgeConnected {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop :=
  ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → 2 ≤ cutSize G S

/-- 3-edge-connectivity. -/
def ThreeEdgeConnected {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop :=
  ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → 3 ≤ cutSize G S

/-- Vertex separator predicate. -/
def Separates {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (C A B : Finset V) : Prop :=
  A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧ Disjoint A C ∧ Disjoint B C ∧
  A ∪ B ∪ C = Finset.univ ∧ ∀ x ∈ A, ∀ y ∈ B, ¬G.Adj x y

/-- 2-vertex-connectivity. -/
def TwoConnected {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Prop :=
  3 ≤ Fintype.card V ∧ ∀ (v : V) (A B : Finset V), ¬Separates G {v} A B

/-- 3-vertex-connectivity. -/
def ThreeConnected {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Prop :=
  4 ≤ Fintype.card V ∧ ∀ (u v : V) (A B : Finset V), ¬Separates G {u, v} A B

/-- Bipartiteness via 2-coloring. -/
def IsBipartite {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ f : V → Bool, ∀ x y, G.Adj x y → f x ≠ f y

/-- High-degree vertices (`deg ≥ 4`) form an independent set. -/
def HighIndependent {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ x y : V, G.Adj x y → 4 ≤ G.degree x → G.degree y ≤ 3

/-- Edge-avoiding power cycle property (`EdgeAvoidingPower`): no single edge hits all `2^k`-cycles. -/
def EdgeAvoidingPower {V : Type*} [DecidableEq V] (H : SimpleGraph V) : Prop :=
  ∀ a b : V, H.Adj a b → HasPower (delEdge H a b)

/-- General Edge-Robust Erdős–Gyárfás (`EGRob`). -/
def EGRob : Prop :=
  ∀ (n : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj], MinDeg3 H → EdgeAvoidingPower H

/-- 3-edge-connected `EGRob` (`EGRob3EC`). -/
def EGRob3EC : Prop :=
  ∀ (n : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
    MinDeg3 H → ThreeEdgeConnected H → EdgeAvoidingPower H

/-- 3-vertex-connected `EGRob` (`EGRob3Conn`). -/
def EGRob3Conn : Prop :=
  ∀ (n : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
    MinDeg3 H → ThreeConnected H → EdgeAvoidingPower H

/-- Core `EGRob` (`EGRob3ConnCore`): 3-vertex-connected, 3-edge-connected, nonbipartite,
    `V_{≥4}`-independent, and edge `ab` has cubic closed neighborhood `N_H[a] ∪ N_H[b]`. -/
def EGRob3ConnCore : Prop :=
  ∀ (n : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
    MinDeg3 H → ThreeConnected H → ThreeEdgeConnected H →
    ¬IsBipartite H → HighIndependent H →
    ∀ a b : Fin n, H.Adj a b →
      (∀ x : Fin n, (x = a ∨ x = b ∨ H.Adj a x ∨ H.Adj b x) → H.degree x = 3) →
      HasPower (delEdge H a b)

/-- Minimal counterexample to `EG2`: minimum order `n`, then edge-inclusion minimal on `Fin n`. -/
def MinimalBad2 (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  Near2 G ∧ ¬HasPower G ∧
  (∀ m < n, ∀ (G' : SimpleGraph (Fin m)) [DecidableRel G'.Adj], Near2 G' → HasPower G') ∧
  (∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj],
    Near2 G' → (∀ x y, G'.Adj x y → G.Adj x y) → (∃ x y, G.Adj x y ∧ ¬G'.Adj x y) → HasPower G')

/-! ### Section 1: Compact Helpers -/

theorem hasPower_of_inj_hom {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hf : Function.Injective f) (h : HasPower G) : HasPower H := by
  rcases h with ⟨u, p, hcyc, hpow⟩
  exact ⟨f u, p.map f, hcyc.map hf, by simpa using hpow⟩

theorem hasPower_of_le {V : Type*} {G' G : SimpleGraph V}
    (hle : ∀ x y, G'.Adj x y → G.Adj x y) (h : HasPower G') : HasPower G :=
  hasPower_of_inj_hom ⟨id, fun hab => hle _ _ hab⟩ Function.injective_id h

def induceFin {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : SimpleGraph (Fin S.card) :=
  SimpleGraph.comap (fun i => (S.equivFin.symm i).1) G

instance instDecidableRelInduceFin {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) : DecidableRel (induceFin G S).Adj := by
  intro i j; unfold induceFin SimpleGraph.comap; infer_instance

theorem hasPower_of_induceFin {n : ℕ} {G : SimpleGraph (Fin n)} {S : Finset (Fin n)}
    (h : HasPower (induceFin G S)) : HasPower G :=
  hasPower_of_inj_hom ⟨fun i => (S.equivFin.symm i).1, fun hab => hab⟩
    (Subtype.val_injective.comp S.equivFin.symm.injective) h

theorem induceFin_degree {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (i : Fin S.card) :
    (induceFin G S).degree i = (G.neighborFinset (S.equivFin.symm i).1 ∩ S).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  refine Finset.card_bij (fun j _ => (S.equivFin.symm j).1) ?_ ?_ ?_
  · intro j hj
    rw [SimpleGraph.mem_neighborFinset] at hj
    exact Finset.mem_inter.mpr ⟨SimpleGraph.mem_neighborFinset.mpr hj, (S.equivFin.symm j).2⟩
  · intro _ _ _ _ h; exact S.equivFin.symm.injective (Subtype.ext h)
  · intro y hy
    rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hy
    refine ⟨S.equivFin ⟨y, hy.2⟩, ?_, by simp⟩
    rw [SimpleGraph.mem_neighborFinset]
    change G.Adj (S.equivFin.symm i).1 (S.equivFin.symm (S.equivFin ⟨y, hy.2⟩)).1
    simpa using hy.1

theorem inter_card_ge_of_sdiff_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : V) (k : ℕ)
    (h : (G.neighborFinset v \ S).card ≤ k) :
    G.degree v - k ≤ (G.neighborFinset v ∩ S).card := by
  have hsum := Finset.card_inter_add_card_sdiff (G.neighborFinset v) S
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hsum; omega

theorem delEdge_degree_left {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {a b : V} (hab : G.Adj a b) :
    (delEdge G a b).degree a = G.degree a - 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  have heq : (delEdge G a b).neighborFinset a = (G.neighborFinset a).erase b := by
    ext y; simp only [SimpleGraph.mem_neighborFinset, Finset.mem_erase, delEdge]
    exact ⟨fun ⟨h1, h2⟩ => ⟨fun hy => h2 (Or.inl ⟨rfl, hy⟩), h1⟩,
           fun ⟨hne, h1⟩ => ⟨h1, fun h => h.elim (fun ⟨_, hy⟩ => hne hy) (fun ⟨h', _⟩ => G.loopless a (h' ▸ h1))⟩⟩
  rw [heq, Finset.card_erase_of_mem (SimpleGraph.mem_neighborFinset.mpr hab)]

theorem delEdge_degree_right {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {a b : V} (hab : G.Adj a b) :
    (delEdge G a b).degree b = G.degree b - 1 := by
  have hcomm : delEdge G a b = delEdge G b a := by
    ext x y; simp only [delEdge]; tauto
  rw [hcomm]; exact delEdge_degree_left G (G.symm hab)

theorem delEdge_degree_other {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {a b x : V} (hxa : x ≠ a) (hxb : x ≠ b) :
    (delEdge G a b).degree x = G.degree x := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  congr 1; ext y; simp only [SimpleGraph.mem_neighborFinset, delEdge]
  exact ⟨fun h => h.1, fun h => ⟨h, fun h' => h'.elim (fun ⟨h1, _⟩ => hxa h1) (fun ⟨h1, _⟩ => hxb h1)⟩⟩

theorem addEdge_degree_left {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {a b : V} (hab : a ≠ b) (hn : ¬G.Adj a b) :
    (addEdge G a b hab).degree a = G.degree a + 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  have heq : (addEdge G a b hab).neighborFinset a = insert b (G.neighborFinset a) := by
    ext y; simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, addEdge]
    exact ⟨fun h => h.elim Or.inr (fun h' => h'.elim (fun ⟨_, hy⟩ => Or.inl hy) (fun ⟨h1, _⟩ => absurd h1 hab)),
           fun h => h.elim (fun hy => Or.inr (Or.inl ⟨rfl, hy⟩)) Or.inl⟩
  rw [heq, Finset.card_insert_of_not_mem (by simp [SimpleGraph.mem_neighborFinset, hn])]

theorem addEdge_degree_right {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {a b : V} (hab : a ≠ b) (hn : ¬G.Adj a b) :
    (addEdge G a b hab).degree b = G.degree b + 1 := by
  have hcomm : addEdge G a b hab = addEdge G b a hab.symm := by
    ext x y; simp only [addEdge]; tauto
  rw [hcomm]; exact addEdge_degree_left G hab.symm (mt G.symm hn)

theorem addEdge_degree_other {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {a b x : V} (hab : a ≠ b)
    (hxa : x ≠ a) (hxb : x ≠ b) :
    (addEdge G a b hab).degree x = G.degree x := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  congr 1; ext y; simp only [SimpleGraph.mem_neighborFinset, addEdge]
  exact ⟨fun h => h.elim id (fun h' => h'.elim (fun ⟨h1, _⟩ => absurd h1 hxa) (fun ⟨h1, _⟩ => absurd h1 hxb)), Or.inl⟩

theorem delEdge_addEdge {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {a b : V} (hab : a ≠ b) (hn : ¬G.Adj a b) :
    delEdge (addEdge G a b hab) a b = G := by
  ext x y; simp only [delEdge, addEdge]
  exact ⟨fun ⟨h, hnot⟩ => h.elim id (fun h' => absurd h' hnot),
         fun hxy => ⟨Or.inl hxy, fun h => h.elim (fun ⟨h1, h2⟩ => hn (h1 ▸ h2 ▸ hxy))
           (fun ⟨h1, h2⟩ => hn (G.symm (h1 ▸ h2 ▸ hxy)))⟩⟩

theorem minimal_bad2_no_near2_proper_subset {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hmb : MinimalBad2 n G) {S : Finset (Fin n)} (hS : S.card < n)
    (hnear : Near2 (induceFin G S)) : False :=
  hmb.2.1 (hasPower_of_induceFin (hmb.2.2.1 S.card hS (induceFin G S) hnear))

theorem near2_induceFin_of_defects {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (S D : Finset (Fin n)) (hD : D.card ≤ 2)
    (hmin : ∀ v ∈ S, 2 ≤ (G.neighborFinset v ∩ S).card)
    (hge3 : ∀ v ∈ S, v ∉ D → 3 ≤ (G.neighborFinset v ∩ S).card)
    (hex : ∃ v ∈ S, 3 ≤ (G.neighborFinset v ∩ S).card) :
    Near2 (induceFin G S) := by
  refine ⟨fun i => by rw [induceFin_degree]; exact hmin _ (S.equivFin.symm i).2, ?_, ?_⟩
  · have hsub : (Finset.univ.filter (fun i : Fin S.card => (induceFin G S).degree i = 2)).card ≤ D.card := by
      refine Finset.card_le_card_of_injOn (fun i => (S.equivFin.symm i).1) ?_
        (fun _ _ _ _ h => S.equivFin.symm.injective (Subtype.ext h))
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [induceFin_degree] at hi
      by_contra hnotD; have := hge3 _ (S.equivFin.symm i).2 hnotD; omega
    omega
  · rcases hex with ⟨v, hvS, hv3⟩
    exact ⟨S.equivFin ⟨v, hvS⟩, by rw [induceFin_degree]; simpa using hv3⟩

theorem no_c4_of_not_hasPower {V : Type*} {G : SimpleGraph V} (h : ¬HasPower G)
    {a b c d : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) : False := by
  have hab_ne := G.ne_of_adj hab; have hbc_ne := G.ne_of_adj hbc
  have hcd_ne := G.ne_of_adj hcd; have hda_ne := G.ne_of_adj hda
  let p : G.Walk a a := Walk.cons hab (Walk.cons hbc (Walk.cons hcd (Walk.cons hda Walk.nil)))
  apply h; refine ⟨a, p, ⟨⟨?_⟩, ?_, ?_⟩, ⟨2, le_rfl, rfl⟩⟩
  · simp [p, SimpleGraph.Walk.edges, Sym2.eq_iff, hab_ne, hab_ne.symm, hbc_ne, hbc_ne.symm,
      hcd_ne, hcd_ne.symm, hda_ne, hda_ne.symm, hac, hac.symm, hbd, hbd.symm]
  · simp [p]
  · simp [p, List.nodup_cons, hab_ne, hab_ne.symm, hbc_ne, hbc_ne.symm,
      hcd_ne, hcd_ne.symm, hda_ne, hda_ne.symm, hac, hac.symm, hbd, hbd.symm]

theorem card_ge_five_of_near2_not_hasPower {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hnear : Near2 G) (hnp : ¬HasPower G) : 5 ≤ n := by
  rcases hnear with ⟨hmin, _, v, hv3⟩
  have h4 : 4 ≤ n := by
    have hsub : G.neighborFinset v ⊆ Finset.univ.erase v := fun x hx =>
      Finset.mem_erase.mpr ⟨G.ne_of_adj (G.symm (SimpleGraph.mem_neighborFinset.mp hx)), Finset.mem_univ _⟩
    have hc := Finset.card_le_card hsub
    rw [SimpleGraph.card_neighborFinset_eq_degree, Finset.card_erase_of_mem (Finset.mem_univ v),
      Finset.card_univ, Fintype.card_fin] at hc; omega
  by_contra hlt5
  have hn4 : n = 4 := by omega
  subst hn4
  have hall : ∀ x : Fin 4, x ≠ v → G.Adj v x := by
    have heq : G.neighborFinset v = Finset.univ.erase v :=
      Finset.eq_of_subset_of_card_le
        (fun x hx => Finset.mem_erase.mpr ⟨G.ne_of_adj (G.symm (SimpleGraph.mem_neighborFinset.mp hx)), Finset.mem_univ _⟩)
        (by rw [SimpleGraph.card_neighborFinset_eq_degree, Finset.card_erase_of_mem (Finset.mem_univ v),
              Finset.card_univ, Fintype.card_fin]; omega)
    intro x hxv; exact SimpleGraph.mem_neighborFinset.mp (heq ▸ Finset.mem_erase.mpr ⟨hxv, Finset.mem_univ _⟩)
  rcases Finset.card_pos.mp (by simp : 0 < (Finset.univ.erase v).card) with ⟨u1, hu1⟩
  have hu1v : u1 ≠ v := (Finset.mem_erase.mp hu1).1
  have hex_u2 : ((G.neighborFinset u1).erase v).Nonempty := by
    have h2 : 2 ≤ (G.neighborFinset u1).card := by rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hmin u1
    have hle : ((G.neighborFinset u1).erase v).card + 1 ≥ (G.neighborFinset u1).card := by
      by_cases hmem : v ∈ G.neighborFinset u1
      · rw [Finset.card_erase_of_mem hmem]; omega
      · rw [Finset.erase_eq_of_not_mem hmem]; omega
    exact Finset.card_pos.mp (by omega)
  rcases hex_u2 with ⟨u2, hu2⟩
  have hu2v : u2 ≠ v := (Finset.mem_erase.mp hu2).1
  have hu12 : G.Adj u1 u2 := SimpleGraph.mem_neighborFinset.mp (Finset.mem_erase.mp hu2).2
  have hu12_ne : u1 ≠ u2 := G.ne_of_adj hu12
  have hex_u3 : (((Finset.univ.erase v).erase u1).erase u2).Nonempty := by
    have hc : (((Finset.univ.erase v).erase u1).erase u2).card = 1 := by
      rw [Finset.card_erase_of_mem, Finset.card_erase_of_mem, Finset.card_erase_of_mem]
      · simp
      · simp
      · exact Finset.mem_erase.mpr ⟨hu1v, Finset.mem_univ _⟩
      · exact Finset.mem_erase.mpr ⟨hu12_ne.symm, Finset.mem_erase.mpr ⟨hu2v, Finset.mem_univ _⟩⟩
    exact Finset.card_pos.mp (by omega)
  rcases hex_u3 with ⟨u3, hu3⟩
  have hu3_u2 : u3 ≠ u2 := (Finset.mem_erase.mp hu3).1
  have hu3_u1 : u3 ≠ u1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hu3).2).1
  have hu3_v : u3 ≠ v := (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hu3).2).2).1
  have hex_w : ((G.neighborFinset u3).erase v).Nonempty := by
    have h2 : 2 ≤ (G.neighborFinset u3).card := by rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hmin u3
    have hle : ((G.neighborFinset u3).erase v).card + 1 ≥ (G.neighborFinset u3).card := by
      by_cases hmem : v ∈ G.neighborFinset u3
      · rw [Finset.card_erase_of_mem hmem]; omega
      · rw [Finset.erase_eq_of_not_mem hmem]; omega
    exact Finset.card_pos.mp (by omega)
  rcases hex_w with ⟨w, hw⟩
  have hwv : w ≠ v := (Finset.mem_erase.mp hw).1
  have hu3w : G.Adj u3 w := SimpleGraph.mem_neighborFinset.mp (Finset.mem_erase.mp hw).2
  have hwu3 : w ≠ u3 := (G.ne_of_adj hu3w).symm
  have hw_cases : w = u1 ∨ w = u2 := by
    by_contra hnot; push_neg at hnot
    have hmem : w ∈ ((((Finset.univ.erase v).erase u1).erase u2).erase u3) := by
      simp [hwv, hnot.1, hnot.2, hwu3]
    have hc : ((((Finset.univ.erase v).erase u1).erase u2).erase u3).card = 0 := by
      rw [Finset.card_erase_of_mem hu3]
      have : (((Finset.univ.erase v).erase u1).erase u2).card = 1 := by
        rw [Finset.card_erase_of_mem, Finset.card_erase_of_mem, Finset.card_erase_of_mem]
        · simp
        · simp
        · exact Finset.mem_erase.mpr ⟨hu1v, Finset.mem_univ _⟩
        · exact Finset.mem_erase.mpr ⟨hu12_ne.symm, Finset.mem_erase.mpr ⟨hu2v, Finset.mem_univ _⟩⟩
      omega
    exact Finset.not_mem_empty w (Finset.card_eq_zero.mp hc ▸ hmem)
  rcases hw_cases with rfl | rfl
  · exact no_c4_of_not_hasPower hnp (hall u3 hu3_v) hu3w hu12 (G.symm (hall u2 hu2v)) hu1v.symm hu3_u2
  · exact no_c4_of_not_hasPower hnp (hall u3 hu3_v) hu3w (G.symm hu12) (G.symm (hall u1 hu1v)) hu2v.symm hu3_u1

/-! ### Section 2: MinimalBad2 Existence & EG2-CORE Collapse -/

theorem minimal_bad2_exists (h : ¬EG2) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj), MinimalBad2 n G := by
  have hex : ∃ n : ℕ, ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj), Near2 G ∧ ¬HasPower G := by
    by_contra hno; apply h; intro n G inst hnear; by_contra hnp; exact hno ⟨n, G, inst, hnear, hnp⟩
  classical
  let n := Nat.find hex
  have hmin_n : ∀ m < n, ∀ (G' : SimpleGraph (Fin m)) [DecidableRel G'.Adj], Near2 G' → HasPower G' := by
    intro m hm G' inst' hnear'; by_contra hnp'; exact Nat.find_min hex hm ⟨G', inst', hnear', hnp'⟩
  have hex_e : ∃ k : ℕ, ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      Near2 G ∧ ¬HasPower G ∧ (Finset.univ.filter (fun p : Fin n × Fin n => G.Adj p.1 p.2)).card = k := by
    rcases Nat.find_spec hex with ⟨G, inst, h1, h2⟩; exact ⟨_, G, inst, h1, h2, rfl⟩
  let k := Nat.find hex_e
  rcases Nat.find_spec hex_e with ⟨G, inst, hnear, hnp, hcard⟩
  refine ⟨n, G, inst, hnear, hnp, hmin_n, fun G' inst' hnear' hsub hstrict => ?_⟩
  by_contra hnp'
  have hlt : (Finset.univ.filter (fun p : Fin n × Fin n => G'.Adj p.1 p.2)).card < k := by
    rw [← hcard]; apply Finset.card_lt_card; rw [Finset.ssubset_iff_subset_ne]
    refine ⟨fun p hp => by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢; exact hsub p.1 p.2 hp,
            fun heq => by rcases hstrict with ⟨x, y, hxy, hnot⟩
                          have hmem : (x, y) ∈ Finset.univ.filter (fun p : Fin n × Fin n => G.Adj p.1 p.2) := by simp [hxy]
                          rw [← heq] at hmem; simp [hnot] at hmem⟩
  exact Nat.find_min hex_e hlt ⟨G', inst', hnear', hnp', rfl⟩

theorem minimal_bad2_exact_two_defects {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hmb : MinimalBad2 n G) :
    ∃ a b : Fin n, a ≠ b ∧ G.degree a = 2 ∧ G.degree b = 2 ∧
      ∀ x : Fin n, x ≠ a → x ≠ b → 3 ≤ G.degree x := by
  have hn5 := card_ge_five_of_near2_not_hasPower hmb.1 hmb.2.1
  have hne0 : (Finset.univ.filter (fun v => G.degree v = 2)).card ≠ 0 := by
    intro h0
    have hall3 : ∀ v : Fin n, 3 ≤ G.degree v := fun v => by
      have h2 := hmb.1.1 v
      have hne : G.degree v ≠ 2 := fun heq => Finset.not_mem_empty v (Finset.card_eq_zero.mp h0 ▸ (by simp [heq]))
      omega
    let a : Fin n := ⟨0, by omega⟩
    rcases Finset.card_pos.mp (by rw [SimpleGraph.card_neighborFinset_eq_degree]; have := hall3 a; omega) with ⟨b, hb⟩
    have hab := SimpleGraph.mem_neighborFinset.mp hb
    let G' := delEdge G a b
    have hnear' : Near2 G' := by
      refine ⟨fun x => ?_, ?_, ?_⟩
      · by_cases hxa : x = a
        · subst hxa; rw [delEdge_degree_left G hab]; have := hall3 x; omega
        · by_cases hxb : x = b
          · subst hxb; rw [delEdge_degree_right G hab]; have := hall3 x; omega
          · rw [delEdge_degree_other G hxa hxb]; have := hall3 x; omega
      · refine (Finset.card_le_card (t := ({a, b} : Finset (Fin n))) ?_).trans Finset.card_le_two
        intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        by_contra hnot
        have hxa : x ≠ a := fun h => hnot (by simp [h])
        have hxb : x ≠ b := fun h => hnot (by simp [h])
        rw [delEdge_degree_other G hxa hxb] at hx; have := hall3 x; omega
      · have hex : (Finset.univ \ ({a, b} : Finset (Fin n))).Nonempty := by
          have hsum := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (Fin n)) {a, b}
          have hinter : ((Finset.univ : Finset (Fin n)) ∩ {a, b}).card ≤ 2 :=
            (Finset.card_le_card Finset.inter_subset_right).trans Finset.card_le_two
          simp at hsum; exact Finset.card_pos.mp (by omega)
        rcases hex with ⟨z, hz⟩
        refine ⟨z, ?_⟩
        rw [delEdge_degree_other G (fun h => by simp [h] at hz) (fun h => by simp [h] at hz)]
        exact hall3 z
    exact hmb.2.1 (hasPower_of_le (fun _ _ h => h.1)
      (hmb.2.2.2 G' hnear' (fun _ _ h => h.1) ⟨a, b, hab, fun h => h.2 (Or.inl ⟨rfl, rfl⟩)⟩))
  have hne1 : (Finset.univ.filter (fun v => G.degree v = 2)).card ≠ 1 := by
    intro h1
    rcases Finset.card_eq_one.mp h1 with ⟨a, ha⟩
    have hda : G.degree a = 2 := (Finset.mem_filter.mp (by rw [ha]; simp)).2
    have hother3 : ∀ v : Fin n, v ≠ a → 3 ≤ G.degree v := fun v hva => by
      have h2 := hmb.1.1 v
      have hne : G.degree v ≠ 2 := fun heq => hva (Finset.mem_singleton.mp (ha ▸ (by simp [heq])))
      omega
    let S := Finset.univ.erase a
    have hScard : S.card < n := by rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; simp; omega
    have hnearS : Near2 (induceFin G S) := by
      refine near2_induceFin_of_defects S (G.neighborFinset a)
        (by rw [SimpleGraph.card_neighborFinset_eq_degree, hda]) ?_ ?_ ?_
      · intro v hvS
        have h1' : (G.neighborFinset v \ S).card ≤ 1 :=
          (Finset.card_le_card (t := {a}) (fun x hx => by
            rw [Finset.mem_sdiff] at hx; by_contra hxa; exact hx.2 (Finset.mem_erase.mpr ⟨hxa, Finset.mem_univ _⟩))).trans (by simp)
        have := inter_card_ge_of_sdiff_le G S v 1 h1'
        have := hother3 v (Finset.mem_erase.mp hvS).1; omega
      · intro v hvS hvnot
        have hsub : G.neighborFinset v ⊆ S := fun x hx =>
          Finset.mem_erase.mpr ⟨fun hxa => hvnot (SimpleGraph.mem_neighborFinset.mpr
            (G.symm (hxa ▸ SimpleGraph.mem_neighborFinset.mp hx))), Finset.mem_univ _⟩
        rw [Finset.inter_eq_left.mpr hsub, SimpleGraph.card_neighborFinset_eq_degree]
        exact hother3 v (Finset.mem_erase.mp hvS).1
      · have hex : (S \ G.neighborFinset a).Nonempty := by
          have hS : S.card = n - 1 := by simp [S]
          have hsum := Finset.card_sdiff_add_card_inter S (G.neighborFinset a)
          have hinter : (S ∩ G.neighborFinset a).card ≤ 2 :=
            (Finset.card_le_card Finset.inter_subset_right).trans
              (by rw [SimpleGraph.card_neighborFinset_eq_degree, hda])
          exact Finset.card_pos.mp (by omega)
        rcases hex with ⟨z, hz⟩; rw [Finset.mem_sdiff] at hz
        have hsub : G.neighborFinset z ⊆ S := fun x hx =>
          Finset.mem_erase.mpr ⟨fun hxa => hz.2 (SimpleGraph.mem_neighborFinset.mpr
            (G.symm (hxa ▸ SimpleGraph.mem_neighborFinset.mp hx))), Finset.mem_univ _⟩
        exact ⟨z, hz.1, by rw [Finset.inter_eq_left.mpr hsub, SimpleGraph.card_neighborFinset_eq_degree]; exact hother3 z (Finset.mem_erase.mp hz.1).1⟩
    exact minimal_bad2_no_near2_proper_subset hmb hScard hnearS
  have hc2 : (Finset.univ.filter (fun v => G.degree v = 2)).card = 2 := by have := hmb.1.2.1; omega
  rcases Finset.card_eq_two.mp hc2 with ⟨a, b, hab, heq⟩
  refine ⟨a, b, hab, (Finset.mem_filter.mp (by rw [heq]; simp)).2,
    (Finset.mem_filter.mp (by rw [heq]; simp)).2, fun x hxa hxb => ?_⟩
  have h2 := hmb.1.1 x
  have hne : G.degree x ≠ 2 := fun hx2 => by
    have : x ∈ ({a, b} : Finset (Fin n)) := heq ▸ (by simp [hx2])
    simp [hxa, hxb] at this
  omega

theorem minimal_bad2_defects_nonadjacent {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hmb : MinimalBad2 n G) {a b : Fin n} (hab : a ≠ b)
    (hda : G.degree a = 2) (hdb : G.degree b = 2)
    (hother : ∀ x : Fin n, x ≠ a → x ≠ b → 3 ≤ G.degree x) :
    ¬G.Adj a b := by
  intro hadj
  have hn5 := card_ge_five_of_near2_not_hasPower hmb.1 hmb.2.1
  rcases Finset.card_eq_one.mp (by rw [Finset.card_erase_of_mem (SimpleGraph.mem_neighborFinset.mpr hadj),
    SimpleGraph.card_neighborFinset_eq_degree, hda]) with ⟨a1, ha1eq⟩
  have ha1_mem : a1 ∈ (G.neighborFinset a).erase b := by rw [ha1eq]; simp
  have ha1b : a1 ≠ b := (Finset.mem_erase.mp ha1_mem).1
  have haa1 : G.Adj a a1 := SimpleGraph.mem_neighborFinset.mp (Finset.mem_erase.mp ha1_mem).2
  have ha1a : a1 ≠ a := (G.ne_of_adj haa1).symm
  rcases Finset.card_eq_one.mp (by rw [Finset.card_erase_of_mem (SimpleGraph.mem_neighborFinset.mpr (G.symm hadj)),
    SimpleGraph.card_neighborFinset_eq_degree, hdb]) with ⟨b1, hb1eq⟩
  have hb1_mem : b1 ∈ (G.neighborFinset b).erase a := by rw [hb1eq]; simp
  have hb1a : b1 ≠ a := (Finset.mem_erase.mp hb1_mem).1
  have hbb1 : G.Adj b b1 := SimpleGraph.mem_neighborFinset.mp (Finset.mem_erase.mp hb1_mem).2
  have hb1b : b1 ≠ b := (G.ne_of_adj hbb1).symm
  let S := (Finset.univ.erase a).erase b
  have hScard_eq : S.card = n - 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hScard : S.card < n := by omega
  have hsub_of_ne : ∀ v ∈ S, v ≠ a1 → v ≠ b1 → G.neighborFinset v ⊆ S := by
    intro v hvS hva1 hvb1 x hx
    have hvb : v ≠ b := (Finset.mem_erase.mp hvS).1
    have hva : v ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hvS).2).1
    have hvx := SimpleGraph.mem_neighborFinset.mp hx
    refine Finset.mem_erase.mpr ⟨fun hxb => hvb1 (Finset.mem_singleton.mp (hb1eq ▸
      Finset.mem_erase.mpr ⟨hva, SimpleGraph.mem_neighborFinset.mpr (G.symm (hxb ▸ hvx))⟩)),
      Finset.mem_erase.mpr ⟨fun hxa => hva1 (Finset.mem_singleton.mp (ha1eq ▸
      Finset.mem_erase.mpr ⟨hvb, SimpleGraph.mem_neighborFinset.mpr (G.symm (hxa ▸ hvx))⟩)), Finset.mem_univ _⟩⟩
  by_cases heq1 : a1 = b1
  · subst heq1
    by_cases h4 : 4 ≤ G.degree a1
    · refine minimal_bad2_no_near2_proper_subset hmb hScard
        (near2_induceFin_of_defects S {a1} (by simp) ?_ ?_ ?_)
      · intro v hvS
        by_cases hva1 : v = a1
        · subst hva1
          have h2 : (G.neighborFinset v \ S).card ≤ 2 :=
            (Finset.card_le_card (t := ({a, b} : Finset (Fin n))) (fun x hx => by
              rw [Finset.mem_sdiff] at hx; by_contra hnot
              exact hx.2 (Finset.mem_erase.mpr ⟨fun h => hnot (by simp [h]),
                Finset.mem_erase.mpr ⟨fun h => hnot (by simp [h]), Finset.mem_univ _⟩⟩))).trans Finset.card_le_two
          have := inter_card_ge_of_sdiff_le G S v 2 h2; omega
        · rw [Finset.inter_eq_left.mpr (hsub_of_ne v hvS hva1 hva1), SimpleGraph.card_neighborFinset_eq_degree]
          have := hother v (Finset.mem_erase.mp (Finset.mem_erase.mp hvS).2).1 (Finset.mem_erase.mp hvS).1; omega
      · intro v hvS hva1; simp only [Finset.mem_singleton] at hva1
        rw [Finset.inter_eq_left.mpr (hsub_of_ne v hvS hva1 hva1), SimpleGraph.card_neighborFinset_eq_degree]
        exact hother v (Finset.mem_erase.mp (Finset.mem_erase.mp hvS).2).1 (Finset.mem_erase.mp hvS).1
      · have hex : (S.erase a1).Nonempty := by
          have hmem : a1 ∈ S := Finset.mem_erase.mpr ⟨ha1b, Finset.mem_erase.mpr ⟨ha1a, Finset.mem_univ _⟩⟩
          exact Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hmem]; omega)
        rcases hex with ⟨z, hz⟩
        have hza1 := (Finset.mem_erase.mp hz).1; have hzS := (Finset.mem_erase.mp hz).2
        exact ⟨z, hzS, by rw [Finset.inter_eq_left.mpr (hsub_of_ne z hzS hza1 hza1), SimpleGraph.card_neighborFinset_eq_degree]
                          exact hother z (Finset.mem_erase.mp (Finset.mem_erase.mp hzS).2).1 (Finset.mem_erase.mp hzS).1⟩
    · have hda1 : G.degree a1 = 3 := by have := hother a1 ha1a ha1b; omega
      rcases Finset.card_eq_one.mp (by
        rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hab.symm, SimpleGraph.mem_neighborFinset.mpr (G.symm hbb1)⟩),
          Finset.card_erase_of_mem (SimpleGraph.mem_neighborFinset.mpr (G.symm haa1)),
          SimpleGraph.card_neighborFinset_eq_degree, hda1]) with ⟨z, hzeq⟩
      have hz_mem : z ∈ ((G.neighborFinset a1).erase a).erase b := by rw [hzeq]; simp
      have hzb := (Finset.mem_erase.mp hz_mem).1
      have hza := (Finset.mem_erase.mp (Finset.mem_erase.mp hz_mem).2).1
      have ha1z := SimpleGraph.mem_neighborFinset.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hz_mem).2).2
      have hza1 : z ≠ a1 := (G.ne_of_adj ha1z).symm
      let S3 := S.erase a1
      have hS3card : S3.card < n := (Finset.card_erase_lt_of_mem
        (Finset.mem_erase.mpr ⟨ha1b, Finset.mem_erase.mpr ⟨ha1a, Finset.mem_univ _⟩⟩)).trans hScard
      have hsub3 : ∀ v ∈ S3, v ≠ z → G.neighborFinset v ⊆ S3 := by
        intro v hvS3 hvz x hx
        have hva1 := (Finset.mem_erase.mp hvS3).1; have hvS := (Finset.mem_erase.mp hvS3).2
        refine Finset.mem_erase.mpr ⟨fun hxa1 => hvz (Finset.mem_singleton.mp (hzeq ▸
          Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hvS).1, Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp (Finset.mem_erase.mp hvS).2).1,
            SimpleGraph.mem_neighborFinset.mpr (G.symm (hxa1 ▸ SimpleGraph.mem_neighborFinset.mp hx))⟩⟩)),
          hsub_of_ne v hvS hva1 hva1 hx⟩
      have hdiff3 : ∀ v ∈ S3, (G.neighborFinset v \ S3).card ≤ 1 := fun v hvS3 =>
        (Finset.card_le_card (t := {a1}) (fun x hx => by
          rw [Finset.mem_sdiff] at hx; by_contra hxa1
          exact hx.2 (Finset.mem_erase.mpr ⟨hxa1,
            hsub_of_ne v (Finset.mem_erase.mp hvS3).2 (Finset.mem_erase.mp hvS3).1 (Finset.mem_erase.mp hvS3).1 hx.1⟩))).trans (by simp)
      refine minimal_bad2_no_near2_proper_subset hmb hS3card (near2_induceFin_of_defects S3 {z} (by simp) ?_ ?_ ?_)
      · intro v hvS3
        have hvS := (Finset.mem_erase.mp hvS3).2
        have := inter_card_ge_of_sdiff_le G S3 v 1 (hdiff3 v hvS3)
        have := hother v (Finset.mem_erase.mp (Finset.mem_erase.mp hvS).2).1 (Finset.mem_erase.mp hvS).1; omega
      · intro v hvS3 hvz; simp only [Finset.mem_singleton] at hvz
        have hvS := (Finset.mem_erase.mp hvS3).2
        rw [Finset.inter_eq_left.mpr (hsub3 v hvS3 hvz), SimpleGraph.card_neighborFinset_eq_degree]
        exact hother v (Finset.mem_erase.mp (Finset.mem_erase.mp hvS).2).1 (Finset.mem_erase.mp hvS).1
      · have hzS3 : z ∈ S3 := Finset.mem_erase.mpr ⟨hza1, Finset.mem_erase.mpr ⟨hzb, Finset.mem_erase.mpr ⟨hza, Finset.mem_univ _⟩⟩⟩
        have hpos : 0 < (G.neighborFinset z ∩ S3).card := by
          have := inter_card_ge_of_sdiff_le G S3 z 1 (hdiff3 z hzS3); have := hother z hza hzb; omega
        rcases Finset.card_pos.mp hpos with ⟨w, hw⟩
        rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hw
        have hwz : w ≠ z := (G.ne_of_adj hw.1).symm
        have hwS := (Finset.mem_erase.mp hw.2).2
        exact ⟨w, hw.2, by rw [Finset.inter_eq_left.mpr (hsub3 w hw.2 hwz), SimpleGraph.card_neighborFinset_eq_degree]
                           exact hother w (Finset.mem_erase.mp (Finset.mem_erase.mp hwS).2).1 (Finset.mem_erase.mp hwS).1⟩
  · refine minimal_bad2_no_near2_proper_subset hmb hScard
      (near2_induceFin_of_defects S {a1, b1} Finset.card_le_two ?_ ?_ ?_)
    · intro v hvS
      have hvb := (Finset.mem_erase.mp hvS).1
      have hva := (Finset.mem_erase.mp (Finset.mem_erase.mp hvS).2).1
      have h1 : (G.neighborFinset v \ S).card ≤ 1 := by
        by_cases hva1 : v = a1
        · subst hva1
          exact (Finset.card_le_card (t := {a}) (fun x hx => by
            rw [Finset.mem_sdiff] at hx; by_contra hxa
            refine hx.2 (Finset.mem_erase.mpr ⟨fun hxb => heq1 (Finset.mem_singleton.mp (hb1eq ▸
              Finset.mem_erase.mpr ⟨hva, SimpleGraph.mem_neighborFinset.mpr (G.symm (hxb ▸ SimpleGraph.mem_neighborFinset.mp hx.1))⟩)),
              Finset.mem_erase.mpr ⟨hxa, Finset.mem_univ _⟩⟩))).trans (by simp)
        · exact (Finset.card_le_card (t := {b}) (fun x hx => by
            rw [Finset.mem_sdiff] at hx; by_contra hxb
            refine hx.2 (Finset.mem_erase.mpr ⟨hxb, Finset.mem_erase.mpr ⟨fun hxa => hva1 (Finset.mem_singleton.mp (ha1eq ▸
              Finset.mem_erase.mpr ⟨hvb, SimpleGraph.mem_neighborFinset.mpr (G.symm (hxa ▸ SimpleGraph.mem_neighborFinset.mp hx.1))⟩)),
              Finset.mem_univ _⟩⟩))).trans (by simp)
      have := inter_card_ge_of_sdiff_le G S v 1 h1; have := hother v hva hvb; omega
    · intro v hvS hvnot
      rw [Finset.inter_eq_left.mpr (hsub_of_ne v hvS (fun h => hvnot (by simp [h])) (fun h => hvnot (by simp [h]))),
        SimpleGraph.card_neighborFinset_eq_degree]
      exact hother v (Finset.mem_erase.mp (Finset.mem_erase.mp hvS).2).1 (Finset.mem_erase.mp hvS).1
    · have hex : (S \ ({a1, b1} : Finset (Fin n))).Nonempty := by
        have hsum := Finset.card_sdiff_add_card_inter S ({a1, b1} : Finset (Fin n))
        have hinter : (S ∩ ({a1, b1} : Finset (Fin n))).card ≤ 2 :=
          (Finset.card_le_card Finset.inter_subset_right).trans Finset.card_le_two
        exact Finset.card_pos.mp (by omega)
      rcases hex with ⟨z, hz⟩; rw [Finset.mem_sdiff] at hz
      exact ⟨z, hz.1, by rw [Finset.inter_eq_left.mpr (hsub_of_ne z hz.1 (fun h => hz.2 (by simp [h])) (fun h => hz.2 (by simp [h]))),
        SimpleGraph.card_neighborFinset_eq_degree]; exact hother z (Finset.mem_erase.mp (Finset.mem_erase.mp hz.1).2).1 (Finset.mem_erase.mp hz.1).1⟩

theorem minimal_bad2_defect_neighbors_cubic {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hmb : MinimalBad2 n G) {a b u : Fin n} (hab : a ≠ b)
    (hda : G.degree a = 2) (hdb : G.degree b = 2)
    (hother : ∀ x : Fin n, x ≠ a → x ≠ b → 3 ≤ G.degree x) (hau : G.Adj a u) : G.degree u = 3 := by
  have hnonadj := minimal_bad2_defects_nonadjacent hmb hab hda hdb hother
  have hua : u ≠ a := (G.ne_of_adj hau).symm
  have hub : u ≠ b := fun h => hnonadj (h ▸ hau)
  have hu3 := hother u hua hub
  by_contra hne3; have hu4 : 4 ≤ G.degree u := by omega
  rcases Finset.card_eq_one.mp (by rw [Finset.card_erase_of_mem (SimpleGraph.mem_neighborFinset.mpr hau),
    SimpleGraph.card_neighborFinset_eq_degree, hda]) with ⟨v, hveq⟩
  let S := Finset.univ.erase a
  have hScard : S.card < n := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    have := card_ge_five_of_near2_not_hasPower hmb.1 hmb.2.1; omega
  have hdiff1 : ∀ x ∈ S, (G.neighborFinset x \ S).card ≤ 1 := fun x _ =>
    (Finset.card_le_card (t := {a}) (fun y hy => by
      rw [Finset.mem_sdiff] at hy; by_contra hya; exact hy.2 (Finset.mem_erase.mpr ⟨hya, Finset.mem_univ _⟩))).trans (by simp)
  refine minimal_bad2_no_near2_proper_subset hmb hScard
    (near2_induceFin_of_defects S {b, v} Finset.card_le_two ?_ ?_ ?_)
  · intro x hxS
    by_cases hxb : x = b
    · subst hxb
      have hsub : G.neighborFinset x ⊆ S := fun y hy =>
        Finset.mem_erase.mpr ⟨fun hya => hnonadj (G.symm (hya ▸ SimpleGraph.mem_neighborFinset.mp hy)), Finset.mem_univ _⟩
      rw [Finset.inter_eq_left.mpr hsub, SimpleGraph.card_neighborFinset_eq_degree, hdb]
    · have := inter_card_ge_of_sdiff_le G S x 1 (hdiff1 x hxS)
      have := hother x (Finset.mem_erase.mp hxS).1 hxb; omega
  · intro x hxS hxnot
    have hxb : x ≠ b := fun h => hxnot (by simp [h])
    have hxv : x ≠ v := fun h => hxnot (by simp [h])
    by_cases hxu : x = u
    · subst hxu; have := inter_card_ge_of_sdiff_le G S x 1 (hdiff1 x hxS); omega
    · have hsub : G.neighborFinset x ⊆ S := fun y hy =>
        Finset.mem_erase.mpr ⟨fun hya => hxv (Finset.mem_singleton.mp (hveq ▸
          Finset.mem_erase.mpr ⟨hxu, SimpleGraph.mem_neighborFinset.mpr (G.symm (hya ▸ SimpleGraph.mem_neighborFinset.mp hy))⟩)), Finset.mem_univ _⟩
      rw [Finset.inter_eq_left.mpr hsub, SimpleGraph.card_neighborFinset_eq_degree]
      exact hother x (Finset.mem_erase.mp hxS).1 hxb
  · refine ⟨u, Finset.mem_erase.mpr ⟨hua, Finset.mem_univ _⟩, ?_⟩
    have := inter_card_ge_of_sdiff_le G S u 1 (hdiff1 u (Finset.mem_erase.mpr ⟨hua, Finset.mem_univ _⟩)); omega

theorem minimal_bad2_high_independent {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hmb : MinimalBad2 n G) : HighIndependent G := by
  intro x y hxy hx4; by_contra hy4; push_neg at hy4
  let G' := delEdge G x y
  have hnear' : Near2 G' := by
    refine ⟨fun z => ?_, ?_, ⟨x, by rw [delEdge_degree_left G hxy]; omega⟩⟩
    · by_cases hzx : z = x
      · subst hzx; rw [delEdge_degree_left G hxy]; omega
      · by_cases hzy : z = y
        · subst hzy; rw [delEdge_degree_right G hxy]; omega
        · rw [delEdge_degree_other G hzx hzy]; exact hmb.1.1 z
    · refine (Finset.card_le_card (t := Finset.univ.filter (fun z => G.degree z = 2)) ?_).trans hmb.1.2.1
      intro z hz; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      by_cases hzx : z = x
      · subst hzx; rw [delEdge_degree_left G hxy] at hz; omega
      · by_cases hzy : z = y
        · subst hzy; rw [delEdge_degree_right G hxy] at hz; omega
        · rw [delEdge_degree_other G hzx hzy] at hz; exact hz
  exact hmb.2.1 (hasPower_of_le (fun _ _ h => h.1)
    (hmb.2.2.2 G' hnear' (fun _ _ h => h.1) ⟨x, y, hxy, fun h => h.2 (Or.inl ⟨rfl, rfl⟩)⟩))

theorem minimal_bad2_nonbipartite {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hmb : MinimalBad2 n G) : ¬IsBipartite G := by
  rintro ⟨f, hf⟩
  rcases minimal_bad2_exact_two_defects hmb with ⟨a, b, hab, hda, hdb, hother⟩
  have hnonadj := minimal_bad2_defects_nonadjacent hmb hab hda hdb hother
  rcases Finset.card_eq_two.mp (by rw [SimpleGraph.card_neighborFinset_eq_degree, hda]) with ⟨u, v, huv, heqa⟩
  have hau : G.Adj a u := SimpleGraph.mem_neighborFinset.mp (by rw [heqa]; simp)
  have hav : G.Adj a v := SimpleGraph.mem_neighborFinset.mp (by rw [heqa]; simp)
  have hua := (G.ne_of_adj hau).symm; have hva := (G.ne_of_adj hav).symm
  have hub : u ≠ b := fun h => hnonadj (h ▸ hau)
  have hvb : v ≠ b := fun h => hnonadj (h ▸ hav)
  have hfuv : f u = f v := by
    have h1 := hf a u hau; have h2 := hf a v hav
    cases hfa : f a <;> cases hfu : f u <;> cases hfv : f v <;> simp_all
  have hnotuv : ¬G.Adj u v := fun h => hf u v h hfuv
  let S := Finset.univ.erase a
  let ui : Fin S.card := S.equivFin ⟨u, Finset.mem_erase.mpr ⟨hua, Finset.mem_univ _⟩⟩
  let vi : Fin S.card := S.equivFin ⟨v, Finset.mem_erase.mpr ⟨hva, Finset.mem_univ _⟩⟩
  have huvi : ui ≠ vi := fun h => huv (congrArg Subtype.val (S.equivFin.injective h))
  let G0 := induceFin G S
  have hnotuv0 : ¬G0.Adj ui vi := by
    change ¬G.Adj (S.equivFin.symm ui).1 (S.equivFin.symm vi).1; simpa [ui, vi] using hnotuv
  let G' := addEdge G0 ui vi huvi
  have hScard : S.card < n := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    have := card_ge_five_of_near2_not_hasPower hmb.1 hmb.2.1; omega
  have hdiff1 : ∀ x ∈ S, (G.neighborFinset x \ S).card ≤ 1 := fun x _ =>
    (Finset.card_le_card (t := {a}) (fun y hy => by
      rw [Finset.mem_sdiff] at hy; by_contra hya; exact hy.2 (Finset.mem_erase.mpr ⟨hya, Finset.mem_univ _⟩))).trans (by simp)
  have hdeg_ui : 3 ≤ G'.degree ui := by
    rw [addEdge_degree_left G0 huvi hnotuv0, induceFin_degree]
    have := inter_card_ge_of_sdiff_le G S u 1 (hdiff1 u (Finset.mem_erase.mpr ⟨hua, Finset.mem_univ _⟩))
    have := hother u hua hub; simpa [ui] using (by omega : 3 ≤ (G.neighborFinset u ∩ S).card + 1)
  have hdeg_vi : 3 ≤ G'.degree vi := by
    rw [addEdge_degree_right G0 huvi hnotuv0, induceFin_degree]
    have := inter_card_ge_of_sdiff_le G S v 1 (hdiff1 v (Finset.mem_erase.mpr ⟨hva, Finset.mem_univ _⟩))
    have := hother v hva hvb; simpa [vi] using (by omega : 3 ≤ (G.neighborFinset v ∩ S).card + 1)
  have hdeg_other : ∀ i : Fin S.card, i ≠ ui → i ≠ vi → G'.degree i = G.degree (S.equivFin.symm i).1 := by
    intro i hi1 hi2
    rw [addEdge_degree_other G0 huvi hi1 hi2, induceFin_degree]
    let x := (S.equivFin.symm i).1
    have hxu : x ≠ u := fun h => hi1 (S.equivFin.symm.injective (Subtype.ext (by simpa [ui] using h)))
    have hxv : x ≠ v := fun h => hi2 (S.equivFin.symm.injective (Subtype.ext (by simpa [vi] using h)))
    have hsub : G.neighborFinset x ⊆ S := fun y hy =>
      Finset.mem_erase.mpr ⟨fun hya => by
        have hmem : x ∈ ({u, v} : Finset (Fin n)) :=
          heqa ▸ SimpleGraph.mem_neighborFinset.mpr (G.symm (hya ▸ SimpleGraph.mem_neighborFinset.mp hy))
        simp [hxu, hxv] at hmem, Finset.mem_univ _⟩
    rw [Finset.inter_eq_left.mpr hsub, SimpleGraph.card_neighborFinset_eq_degree]
  let bi : Fin S.card := S.equivFin ⟨b, Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ _⟩⟩
  have hnear' : Near2 G' := by
    refine ⟨fun i => ?_, ?_, ⟨ui, hdeg_ui⟩⟩
    · by_cases h1 : i = ui
      · subst h1; omega
      · by_cases h2 : i = vi
        · subst h2; omega
        · rw [hdeg_other i h1 h2]; exact hmb.1.1 _
    · refine (Finset.card_le_card (t := {bi}) ?_).trans (by simp)
      intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [Finset.mem_singleton]; by_contra hibi
      by_cases h1 : i = ui
      · subst h1; omega
      · by_cases h2 : i = vi
        · subst h2; omega
        · rw [hdeg_other i h1 h2] at hi
          have hxa := (Finset.mem_erase.mp (S.equivFin.symm i).2).1
          have hxb : (S.equivFin.symm i).1 ≠ b := fun h => hibi (S.equivFin.symm.injective (Subtype.ext (by simpa [bi] using h)))
          have := hother _ hxa hxb; omega
  rcases hmb.2.2.1 S.card hScard G' hnear' with ⟨w, p, hcyc, k, hk2, hlen⟩
  by_cases huses : s(ui, vi) ∈ p.edges
  · let f0 : Fin S.card → Bool := fun i => f (S.equivFin.symm i).1
    have hflips : ∀ {x y : Fin S.card} (q : G'.Walk x y),
        (q.edges.filter (fun e => e = s(ui, vi))).length % 2 =
          (q.length + if f0 x = f0 y then 0 else 1) % 2 := by
      intro x y q
      induction q with
      | nil => simp
      | @cons x y z hxy q ih =>
        simp only [SimpleGraph.Walk.edges_cons, List.filter_cons, SimpleGraph.Walk.length_cons]
        by_cases he : s(x, y) = s(ui, vi)
        · have hfxy : f0 x = f0 y := by
            rw [Sym2.eq_iff] at he
            rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · simpa [f0, ui, vi] using hfuv
            · simpa [f0, ui, vi] using hfuv.symm
          simp only [he, decide_true, ↓reduceIte, List.length_cons]
          cases hfx : f0 x <;> cases hfy : f0 y <;> cases hfz : f0 z <;> simp_all <;> omega
        · have hG0 : G0.Adj x y := by
            rcases hxy with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact h
            · exact absurd rfl he
            · exact absurd Sym2.eq_swap he
          have hfxy : f0 x ≠ f0 y := hf _ _ hG0
          simp only [he, decide_false, Bool.false_eq_true, ↓reduceIte]
          cases hfx : f0 x <;> cases hfy : f0 y <;> cases hfz : f0 z <;> simp_all <;> omega
    have hp_flips := hflips p; simp only [↓reduceIte, add_zero] at hp_flips
    have hcount1 : (p.edges.filter (fun e => e = s(ui, vi))).length = 1 := by
      have hnd := hcyc.isTrail.edges_nodup.filter (fun e => e = s(ui, vi))
      have hmem : s(ui, vi) ∈ p.edges.filter (fun e => e = s(ui, vi)) := by simp [huses]
      cases hL : p.edges.filter (fun e => e = s(ui, vi)) with
      | nil => rw [hL] at hmem; simp at hmem
      | cons e rest =>
        cases rest with
        | nil => simp
        | cons e2 rest2 =>
          rw [hL, List.nodup_cons] at hnd
          have h1 : e = s(ui, vi) := (List.mem_filter.mp (by rw [hL]; simp)).2 |> of_decide_eq_true
          have h2 : e2 = s(ui, vi) := (List.mem_filter.mp (by rw [hL]; simp)).2 |> of_decide_eq_true
          exact absurd (by simp [h1, h2]) hnd.1
    rw [hcount1, hlen] at hp_flips
    have heven : 2 ^ k % 2 = 0 := by
      have : 2 ^ k = 2 * 2 ^ (k - 1) := by conv_lhs => rw [← Nat.sub_add_cancel (by omega : 0 < k), pow_succ, mul_comm]
      omega
    omega
  · have hsubG0 : ∀ e ∈ p.edges, e ≠ s(ui, vi) := fun e he heq => huses (heq ▸ he)
    let inc : G0 →g G' := ⟨id, fun h => Or.inl h⟩
    have htransfer : ∀ {x y : Fin S.card} (q : G'.Walk x y), (∀ e ∈ q.edges, e ≠ s(ui, vi)) →
        ∃ q0 : G0.Walk x y, q0.map inc = q := by
      intro x y q
      induction q with
      | nil => intro _; exact ⟨Walk.nil, rfl⟩
      | @cons x y z hxy q ih =>
        intro hq
        have hne : s(x, y) ≠ s(ui, vi) := hq _ (by simp)
        have hG0 : G0.Adj x y := by
          rcases hxy with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact h
          · exact absurd rfl hne
          · exact absurd Sym2.eq_swap hne
        rcases ih (fun e he => hq e (by simp [he])) with ⟨q0, hq0⟩
        exact ⟨Walk.cons hG0 q0, by simp [hq0]⟩
    rcases htransfer p hsubG0 with ⟨p0, hp0⟩
    have hcyc0 : p0.IsCycle := by
      refine ⟨⟨?_⟩, ?_, ?_⟩
      · have hnd : (p0.map inc).edges.Nodup := hp0 ▸ hcyc.isTrail.edges_nodup
        simpa [SimpleGraph.Walk.edges_map, inc] using hnd
      · intro hnil; exact hcyc.ne_nil (hp0 ▸ (by simpa [hnil] : (p0.map inc).Nil))
      · have hnd : (p0.map inc).support.tail.Nodup := hp0 ▸ hcyc.support_nodup
        simpa [SimpleGraph.Walk.support_map, inc] using hnd
    have hlen0 : p0.length = 2 ^ k := by
      have := congrArg SimpleGraph.Walk.length hp0; simpa using this.trans hlen
    exact hmb.2.1 (hasPower_of_induceFin ⟨w, p0, hcyc0, ⟨k, hk2, hlen0⟩⟩)

/-! ### Section 3: Pillar 1 — 2-Edge-Connectivity, 2-Connectivity, and 3-Connected Completion -/

theorem cutSize_eq_sum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    cutSize G S = ∑ v ∈ S, (G.neighborFinset v \ S).card := by
  unfold cutSize; rw [← Finset.card_sigma]
  refine Finset.card_bij (fun p _ => ⟨p.1, p.2⟩) ?_ ?_ ?_
  · intro p hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [Finset.mem_sigma, Finset.mem_sdiff, SimpleGraph.mem_neighborFinset]; exact ⟨hp.1, hp.2.2, hp.2.1⟩
  · intro p1 _ p2 _ h; cases p1; cases p2; simp only [Sigma.mk.inj_iff, heq_eq_eq] at h; exact Prod.ext h.1 h.2
  · intro q hq; simp only [Finset.mem_sigma, Finset.mem_sdiff, SimpleGraph.mem_neighborFinset] at hq
    exact ⟨(q.1, q.2), by simp [hq.1, hq.2.1, hq.2.2], rfl⟩

theorem cutSize_compl {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    cutSize G Sᶜ = cutSize G S := by
  unfold cutSize
  refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
  · intro p hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl] at hp ⊢
    exact ⟨not_not.mp hp.2.1, hp.1, G.symm hp.2.2⟩
  · intro p1 _ p2 _ h; cases p1; cases p2; simp only [Prod.mk.injEq] at h; exact Prod.ext h.2 h.1
  · intro p hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact ⟨(p.2, p.1), by simp [hp.1, hp.2.1, G.symm hp.2.2], rfl⟩

theorem minimal_bad2_two_edge_connected {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hmb : MinimalBad2 n G) : TwoEdgeConnected G := by
  rcases minimal_bad2_exact_two_defects hmb with ⟨a, b, hab, hda, hdb, hother⟩
  have hside : ∀ (T : Finset (Fin n)), T.Nonempty → T ≠ Finset.univ → cutSize G T ≤ 1 →
      ¬(a ∈ T ∧ b ∈ T) → False := by
    intro T hTne hTuniv hTcut hnotboth
    have hTcard : T.card < n := by
      simpa using Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hTuniv⟩)
    rw [cutSize_eq_sum] at hTcut
    by_cases h0 : ∑ v ∈ T, (G.neighborFinset v \ T).card = 0
    · have hdegT : ∀ v ∈ T, (G.neighborFinset v ∩ T).card = G.degree v := fun v hv => by
        have hz : (G.neighborFinset v \ T).card = 0 :=
          Nat.eq_zero_of_le_zero ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) hv).trans (by omega))
        have hsum := Finset.card_inter_add_card_sdiff (G.neighborFinset v) T
        rw [SimpleGraph.card_neighborFinset_eq_degree, hz] at hsum; omega
      have hT3 : 3 ≤ T.card := by
        rcases hTne with ⟨x, hx⟩
        have hx2 := hmb.1.1 x; rw [← hdegT x hx] at hx2
        have hsub : G.neighborFinset x ∩ T ⊆ T.erase x := fun y hy => by
          rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hy
          exact Finset.mem_erase.mpr ⟨(G.ne_of_adj hy.1).symm, hy.2⟩
        have hc := Finset.card_le_card hsub; rw [Finset.card_erase_of_mem hx] at hc; omega
      have hex3 : ∃ v ∈ T, 3 ≤ (G.neighborFinset v ∩ T).card := by
        have hne : (T \ ({a, b} : Finset (Fin n))).Nonempty := by
          have hsum := Finset.card_sdiff_add_card_inter T ({a, b} : Finset (Fin n))
          have hinter : (T ∩ ({a, b} : Finset (Fin n))).card ≤ 2 :=
            (Finset.card_le_card Finset.inter_subset_right).trans Finset.card_le_two
          exact Finset.card_pos.mp (by omega)
        rcases hne with ⟨v, hv⟩; rw [Finset.mem_sdiff] at hv
        exact ⟨v, hv.1, by rw [hdegT v hv.1]; exact hother v (fun h => hv.2 (by simp [h])) (fun h => hv.2 (by simp [h]))⟩
      exact minimal_bad2_no_near2_proper_subset hmb hTcard
        (near2_induceFin_of_defects T {a, b} Finset.card_le_two
          (fun v hv => by rw [hdegT v hv]; exact hmb.1.1 v)
          (fun v hv hvnot => by rw [hdegT v hv]; exact hother v (fun h => hvnot (by simp [h])) (fun h => hvnot (by simp [h])))
          hex3)
    · have hsum1 : ∑ v ∈ T, (G.neighborFinset v \ T).card = 1 := by omega
      have hexu : ∃ u ∈ T, (G.neighborFinset u \ T).card = 1 ∧
          ∀ v ∈ T, v ≠ u → (G.neighborFinset v \ T).card = 0 := by
        by_contra hno; push_neg at hno
        have hall0 : ∀ v ∈ T, (G.neighborFinset v \ T).card = 0 := fun v hv => by
          by_contra hv0
          have hvle := (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hv).trans (by omega : _ ≤ 1)
          rcases hno v hv (by omega) with ⟨w, hwT, hwv, hw0⟩
          have h2 := Finset.sum_le_sum_of_subset_of_nonneg (s := {v, w}) (t := T)
            (f := fun x => (G.neighborFinset x \ T).card)
            (fun x hx => by simp at hx; rcases hx with rfl | rfl <;> assumption) (fun _ _ _ => Nat.zero_le _)
          rw [Finset.sum_pair hwv.symm] at h2; omega
        rw [Finset.sum_eq_zero hall0] at hsum1; omega
      rcases hexu with ⟨u, huT, hu1, hrest0⟩
      have hdeg_other : ∀ v ∈ T, v ≠ u → (G.neighborFinset v ∩ T).card = G.degree v := fun v hv hvu => by
        have hsum := Finset.card_inter_add_card_sdiff (G.neighborFinset v) T
        rw [SimpleGraph.card_neighborFinset_eq_degree, hrest0 v hv hvu] at hsum; omega
      have hdeg_u : (G.neighborFinset u ∩ T).card = G.degree u - 1 := by
        have hsum := Finset.card_inter_add_card_sdiff (G.neighborFinset u) T
        rw [SimpleGraph.card_neighborFinset_eq_degree, hu1] at hsum; omega
      by_cases hu_def : u = a ∨ u = b
      · have hu2 : G.degree u = 2 := hu_def.elim (fun h => h ▸ hda) (fun h => h ▸ hdb)
        have hotherT : ∀ v ∈ T, v ≠ u → 3 ≤ G.degree v := fun v hv hvu =>
          hother v (fun hva => hu_def.elim (fun h => hvu (hva.trans h.symm)) (fun h => hnotboth ⟨hva ▸ hv, h ▸ huT⟩))
            (fun hvb => hu_def.elim (fun h => hnotboth ⟨h ▸ huT, hvb ▸ hv⟩) (fun h => hvu (hvb.trans h.symm)))
        rcases Finset.card_eq_one.mp (by rw [hdeg_u, hu2] : (G.neighborFinset u ∩ T).card = 1) with ⟨w, hweq⟩
        have hw_mem : w ∈ G.neighborFinset u ∩ T := by rw [hweq]; simp
        have hwT := (Finset.mem_inter.mp hw_mem).2
        have hwu := (G.ne_of_adj (SimpleGraph.mem_neighborFinset.mp (Finset.mem_inter.mp hw_mem).1)).symm
        let T' := T.erase u
        have hT'card : T'.card < n := (Finset.card_erase_lt_of_mem huT).trans hTcard
        have hdiff1 : ∀ v ∈ T', (G.neighborFinset v \ T').card ≤ 1 := fun v hvT' =>
          (Finset.card_le_card (t := {u}) (fun x hx => by
            rw [Finset.mem_sdiff] at hx; by_contra hxu
            have hxT : x ∈ T := by
              by_contra hnotT
              exact Finset.not_mem_empty x (Finset.card_eq_zero.mp (hrest0 v (Finset.mem_erase.mp hvT').2
                (Finset.mem_erase.mp hvT').1) ▸ Finset.mem_sdiff.mpr ⟨hx.1, hnotT⟩)
            exact hx.2 (Finset.mem_erase.mpr ⟨hxu, hxT⟩))).trans (by simp)
        have hsubT' : ∀ v ∈ T', v ≠ w → G.neighborFinset v ⊆ T' := fun v hvT' hvw x hx => by
          have hxT : x ∈ T := by
            by_contra hnotT
            exact Finset.not_mem_empty x (Finset.card_eq_zero.mp (hrest0 v (Finset.mem_erase.mp hvT').2
              (Finset.mem_erase.mp hvT').1) ▸ Finset.mem_sdiff.mpr ⟨hx, hnotT⟩)
          exact Finset.mem_erase.mpr ⟨fun hxu => hvw (Finset.mem_singleton.mp (hweq ▸
            Finset.mem_inter.mpr ⟨SimpleGraph.mem_neighborFinset.mpr (G.symm (hxu ▸ SimpleGraph.mem_neighborFinset.mp hx)),
              (Finset.mem_erase.mp hvT').2⟩)), hxT⟩
        refine minimal_bad2_no_near2_proper_subset hmb hT'card (near2_induceFin_of_defects T' {w} (by simp) ?_ ?_ ?_)
        · intro v hvT'
          have := inter_card_ge_of_sdiff_le G T' v 1 (hdiff1 v hvT')
          have := hotherT v (Finset.mem_erase.mp hvT').2 (Finset.mem_erase.mp hvT').1; omega
        · intro v hvT' hvw; simp only [Finset.mem_singleton] at hvw
          rw [Finset.inter_eq_left.mpr (hsubT' v hvT' hvw), SimpleGraph.card_neighborFinset_eq_degree]
          exact hotherT v (Finset.mem_erase.mp hvT').2 (Finset.mem_erase.mp hvT').1
        · have hwT' : w ∈ T' := Finset.mem_erase.mpr ⟨hwu, hwT⟩
          have hwpos : 0 < (G.neighborFinset w ∩ T').card := by
            have := inter_card_ge_of_sdiff_le G T' w 1 (hdiff1 w hwT'); have := hotherT w hwT hwu; omega
          rcases Finset.card_pos.mp hwpos with ⟨z, hz⟩
          rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hz
          have hzw := (G.ne_of_adj hz.1).symm
          exact ⟨z, hz.2, by rw [Finset.inter_eq_left.mpr (hsubT' z hz.2 hzw), SimpleGraph.card_neighborFinset_eq_degree]
                             exact hotherT z (Finset.mem_erase.mp hz.2).2 (Finset.mem_erase.mp hz.2).1⟩
      · push_neg at hu_def
        have hu2in : 2 ≤ (G.neighborFinset u ∩ T).card := by rw [hdeg_u]; have := hother u hu_def.1 hu_def.2; omega
        let D : Finset (Fin n) := if a ∈ T then {u, a} else {u, b}
        have hDcard : D.card ≤ 2 := by dsimp [D]; split_ifs <;> exact Finset.card_le_two
        have hTge3 : ∀ v ∈ T, v ∉ D → 3 ≤ (G.neighborFinset v ∩ T).card := fun v hv hvD => by
          have hvu : v ≠ u := fun h => hvD (by dsimp [D]; split_ifs <;> simp [h])
          rw [hdeg_other v hv hvu]
          exact hother v (fun hva => hvD (by dsimp [D]; simp [hva ▸ hv, hva]))
            (fun hvb => hvD (by dsimp [D]; split_ifs with haT
                                · exact absurd ⟨haT, hvb ▸ hv⟩ hnotboth
                                · simp [hvb]))
        have hT3 : 3 ≤ T.card := by
          have hsub : G.neighborFinset u ∩ T ⊆ T.erase u := fun y hy => by
            rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hy
            exact Finset.mem_erase.mpr ⟨(G.ne_of_adj hy.1).symm, hy.2⟩
          have hc := hu2in.trans (Finset.card_le_card hsub); rw [Finset.card_erase_of_mem huT] at hc; omega
        have hex3 : ∃ v ∈ T, 3 ≤ (G.neighborFinset v ∩ T).card := by
          have hne : (T \ D).Nonempty := by
            have hsum := Finset.card_sdiff_add_card_inter T D
            have hinter : (T ∩ D).card ≤ 2 := (Finset.card_le_card Finset.inter_subset_right).trans hDcard
            exact Finset.card_pos.mp (by omega)
          rcases hne with ⟨v, hv⟩; rw [Finset.mem_sdiff] at hv; exact ⟨v, hv.1, hTge3 v hv.1 hv.2⟩
        exact minimal_bad2_no_near2_proper_subset hmb hTcard
          (near2_induceFin_of_defects T D hDcard
            (fun v hv => by by_cases hvu : v = u
                            · exact hvu ▸ hu2in
                            · rw [hdeg_other v hv hvu]; exact hmb.1.1 v)
            hTge3 hex3)
  intro S hSne hSuniv; by_contra hlt2
  by_cases hboth : a ∈ S ∧ b ∈ S
  · exact hside Sᶜ (Finset.nonempty_compl.mpr hSuniv)
      (fun h => hSne.ne_empty (by simpa using congrArg Compl.compl h))
      (by rw [cutSize_compl]; omega) (fun ⟨ha, _⟩ => Finset.mem_compl.mp ha hboth.1)
  · exact hside S hSne hSuniv (by omega) hboth

theorem minimal_bad2_no_cut_vertex {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hmb : MinimalBad2 n G) : TwoConnected G := by
  have hn5 := card_ge_five_of_near2_not_hasPower hmb.1 hmb.2.1
  refine ⟨by rw [Fintype.card_fin]; omega, ?_⟩
  rcases minimal_bad2_exact_two_defects hmb with ⟨a, b, hab, hda, hdb, hother⟩
  have h2ec := minimal_bad2_two_edge_connected hmb
  intro v A B ⟨hAne, hBne, hAB, hAv, hBv, hunion, hnoedge⟩
  have hside : ∀ (X Y : Finset (Fin n)), X.Nonempty → Y.Nonempty →
      Disjoint X Y → Disjoint X {v} → Disjoint Y {v} → X ∪ Y ∪ {v} = Finset.univ →
      (∀ x ∈ X, ∀ y ∈ Y, ¬G.Adj x y) → ¬(a ∈ X ∧ b ∈ X) → False := by
    intro X Y hXne hYne hXY hXv hYv hXYv hnoXY hnotboth
    let S := X ∪ {v}
    have hScard : S.card < n := by
      rcases hYne with ⟨y, hy⟩
      have hyS : y ∉ S := fun hmem => (Finset.mem_union.mp hmem).elim
        (fun h => Finset.disjoint_left.mp hXY h hy) (fun h => Finset.disjoint_left.mp hYv hy h)
      simpa using Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
        ⟨Finset.subset_univ _, fun h => hyS (h ▸ Finset.mem_univ y)⟩)
    have hX_nb : ∀ x ∈ X, G.neighborFinset x ⊆ S := fun x hx y hy => by
      have hyU : y ∈ X ∪ Y ∪ {v} := hXYv ▸ Finset.mem_univ y
      rcases Finset.mem_union.mp hyU with hyXY | hyv
      · rcases Finset.mem_union.mp hyXY with hyX | hyY
        · exact Finset.mem_union_left _ hyX
        · exact absurd (SimpleGraph.mem_neighborFinset.mp hy) (hnoXY x hx y hyY)
      · exact Finset.mem_union_right _ hyv
    have hvX2 : 2 ≤ (G.neighborFinset v ∩ S).card := by
      have hXuniv : X ≠ Finset.univ := fun h => by
        rcases hYne with ⟨y, hy⟩; exact Finset.disjoint_left.mp hXY (h ▸ Finset.mem_univ y) hy
      have hcut2 := h2ec X hXne hXuniv
      have hle : cutSize G X ≤ (G.neighborFinset v ∩ S).card := by
        unfold cutSize
        refine Finset.card_le_card_of_injOn (fun p => p.1) ?_ ?_
        · intro p hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
          have hp2v : p.2 = v := Finset.mem_singleton.mp
            ((Finset.mem_union.mp (hX_nb p.1 hp.1 (SimpleGraph.mem_neighborFinset.mpr hp.2.2))).resolve_left hp.2.1)
          exact Finset.mem_inter.mpr ⟨SimpleGraph.mem_neighborFinset.mpr (G.symm (hp2v ▸ hp.2.2)),
            Finset.mem_union_left _ hp.1⟩
        · intro p1 hp1 p2 hp2 heq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
          have h1v : p1.2 = v := Finset.mem_singleton.mp
            ((Finset.mem_union.mp (hX_nb p1.1 hp1.1 (SimpleGraph.mem_neighborFinset.mpr hp1.2.2))).resolve_left hp1.2.1)
          have h2v : p2.2 = v := Finset.mem_singleton.mp
            ((Finset.mem_union.mp (hX_nb p2.1 hp2.1 (SimpleGraph.mem_neighborFinset.mpr hp2.2.2))).resolve_left hp2.2.1)
          exact Prod.ext heq (h1v.trans h2v.symm)
      omega
    let D : Finset (Fin n) := if a ∈ X then {v, a} else {v, b}
    have hDcard : D.card ≤ 2 := by dsimp [D]; split_ifs <;> exact Finset.card_le_two
    have hSge3 : ∀ x ∈ S, x ∉ D → 3 ≤ (G.neighborFinset x ∩ S).card := fun x hxS hxD => by
      have hxv : x ≠ v := fun h => hxD (by dsimp [D]; split_ifs <;> simp [h])
      have hxX : x ∈ X := (Finset.mem_union.mp hxS).resolve_right (by simp [hxv])
      rw [Finset.inter_eq_left.mpr (hX_nb x hxX), SimpleGraph.card_neighborFinset_eq_degree]
      exact hother x (fun hxa => hxD (by dsimp [D]; simp [hxa ▸ hxX, hxa]))
        (fun hxb => hxD (by dsimp [D]; split_ifs with haX
                            · exact absurd ⟨haX, hxb ▸ hxX⟩ hnotboth
                            · simp [hxb]))
    have hS3 : 3 ≤ S.card := by
      have hsub : G.neighborFinset v ∩ S ⊆ X := fun y hy => by
        rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hy
        exact (Finset.mem_union.mp hy.2).resolve_right (by simp [(G.ne_of_adj hy.1).symm])
      have hX2 := hvX2.trans (Finset.card_le_card hsub)
      rw [Finset.card_union_of_disjoint hXv, Finset.card_singleton]; omega
    have hex3 : ∃ x ∈ S, 3 ≤ (G.neighborFinset x ∩ S).card := by
      have hne : (S \ D).Nonempty := by
        have hsum := Finset.card_sdiff_add_card_inter S D
        have hinter : (S ∩ D).card ≤ 2 := (Finset.card_le_card Finset.inter_subset_right).trans hDcard
        exact Finset.card_pos.mp (by omega)
      rcases hne with ⟨x, hx⟩; rw [Finset.mem_sdiff] at hx; exact ⟨x, hx.1, hSge3 x hx.1 hx.2⟩
    exact minimal_bad2_no_near2_proper_subset hmb hScard
      (near2_induceFin_of_defects S D hDcard
        (fun x hxS => by
          by_cases hxv : x = v
          · exact hxv ▸ hvX2
          · have hxX := (Finset.mem_union.mp hxS).resolve_right (by simp [hxv])
            rw [Finset.inter_eq_left.mpr (hX_nb x hxX), SimpleGraph.card_neighborFinset_eq_degree]; exact hmb.1.1 x)
        hSge3 hex3)
  by_cases hbothA : a ∈ A ∧ b ∈ A
  · exact hside B A hBne hAne hAB.symm hBv hAv (by rw [Finset.union_comm B A]; exact hunion)
      (fun x hx y hy h => hnoedge y hy x hx (G.symm h)) (fun ⟨haB, _⟩ => Finset.disjoint_left.mp hAB hbothA.1 haB)
  · exact hside A B hAne hBne hAB hAv hBv hunion hnoedge hbothA

theorem minimal_bad2_no_defect_free_two_cut {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hmb : MinimalBad2 n G) {a b : Fin n} (hab : a ≠ b)
    (hda : G.degree a = 2) (hdb : G.degree b = 2)
    (hother : ∀ x : Fin n, x ≠ a → x ≠ b → 3 ≤ G.degree x)
    {S : Finset (Fin n)} (hS2 : 2 ≤ S.card) (hSuniv : S ≠ Finset.univ)
    (haS : a ∉ S) (hbS : b ∉ S) : 3 ≤ cutSize G S := by
  by_contra hlt3
  have hScard : S.card < n := by
    simpa using Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hSuniv⟩)
  have h2conn := minimal_bad2_no_cut_vertex hmb
  have hS3 : ∀ v ∈ S, 3 ≤ G.degree v := fun v hv =>
    hother v (fun h => haS (h ▸ hv)) (fun h => hbS (h ▸ hv))
  have hcut2 : ∑ v ∈ S, (G.neighborFinset v \ S).card ≤ 2 := by rw [← cutSize_eq_sum]; omega
  by_cases hex2 : ∃ u ∈ S, 2 ≤ (G.neighborFinset u \ S).card
  · rcases hex2 with ⟨u, huS, hu2⟩
    have hrest0 : ∀ v ∈ S, v ≠ u → (G.neighborFinset v \ S).card = 0 := fun v hv hvu => by
      by_contra hv0
      have h2 := Finset.sum_le_sum_of_subset_of_nonneg (s := {u, v}) (t := S)
        (f := fun x => (G.neighborFinset x \ S).card)
        (fun x hx => by simp at hx; rcases hx with rfl | rfl <;> assumption) (fun _ _ _ => Nat.zero_le _)
      rw [Finset.sum_pair hvu.symm] at h2; omega
    exact h2conn.2 u (S.erase u) Sᶜ
      ⟨Finset.card_pos.mp (by rw [Finset.card_erase_of_mem huS]; omega),
       Finset.nonempty_compl.mpr hSuniv,
       Finset.disjoint_left.mpr (fun x hx => by simp [(Finset.mem_erase.mp hx).2]),
       Finset.disjoint_singleton_right.mpr (Finset.not_mem_erase u S),
       Finset.disjoint_singleton_right.mpr (by simp [huS]),
       by ext x; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_compl, Finset.mem_singleton,
            Finset.mem_univ, iff_true]; by_cases hxu : x = u <;> by_cases hxS : x ∈ S <;> tauto,
       fun x hx y hy hxy => Finset.not_mem_empty y
         (Finset.card_eq_zero.mp (hrest0 x (Finset.mem_erase.mp hx).2 (Finset.mem_erase.mp hx).1) ▸
           Finset.mem_sdiff.mpr ⟨SimpleGraph.mem_neighborFinset.mpr hxy, Finset.mem_compl.mp hy⟩)⟩
  · push_neg at hex2
    let D := S.filter (fun v => 1 ≤ (G.neighborFinset v \ S).card)
    have hDcard : D.card ≤ 2 := by
      have h1 : D.card ≤ ∑ v ∈ D, (G.neighborFinset v \ S).card := by
        calc D.card = ∑ _v ∈ D, 1 := by simp
        _ ≤ ∑ v ∈ D, (G.neighborFinset v \ S).card := Finset.sum_le_sum (fun v hv => (Finset.mem_filter.mp hv).2)
      have h2 := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ S) (fun _ _ _ => Nat.zero_le _)
      omega
    have hminS : ∀ v ∈ S, 2 ≤ (G.neighborFinset v ∩ S).card := fun v hv => by
      have := inter_card_ge_of_sdiff_le G S v 1 (by have := hex2 v hv; omega); have := hS3 v hv; omega
    have hge3S : ∀ v ∈ S, v ∉ D → 3 ≤ (G.neighborFinset v ∩ S).card := fun v hv hvD => by
      have h0 : (G.neighborFinset v \ S).card = 0 := by
        by_contra hne; exact hvD (Finset.mem_filter.mpr ⟨hv, by omega⟩)
      have := inter_card_ge_of_sdiff_le G S v 0 (by omega); have := hS3 v hv; omega
    have hScard3 : 3 ≤ S.card := by
      rcases Finset.card_pos.mp (by omega : 0 < S.card) with ⟨x, hx⟩
      have hsub : G.neighborFinset x ∩ S ⊆ S.erase x := fun y hy => by
        rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hy
        exact Finset.mem_erase.mpr ⟨(G.ne_of_adj hy.1).symm, hy.2⟩
      have hc := (hminS x hx).trans (Finset.card_le_card hsub); rw [Finset.card_erase_of_mem hx] at hc; omega
    have hex3 : ∃ v ∈ S, 3 ≤ (G.neighborFinset v ∩ S).card := by
      have hne : (S \ D).Nonempty := by
        have hsum := Finset.card_sdiff_add_card_inter S D
        have hinter : (S ∩ D).card ≤ 2 := (Finset.card_le_card Finset.inter_subset_right).trans hDcard
        exact Finset.card_pos.mp (by omega)
      rcases hne with ⟨v, hv⟩; rw [Finset.mem_sdiff] at hv; exact ⟨v, hv.1, hge3S v hv.1 hv.2⟩
    exact minimal_bad2_no_near2_proper_subset hmb hScard
      (near2_induceFin_of_defects S D hDcard hminS hge3S hex3)

theorem minimal_bad2_no_defect_free_two_vertex_cut {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hmb : MinimalBad2 n G) {a b : Fin n} (hab : a ≠ b)
    (hda : G.degree a = 2) (hdb : G.degree b = 2)
    (hother : ∀ x : Fin n, x ≠ a → x ≠ b → 3 ≤ G.degree x)
    {u v : Fin n} {A B : Finset (Fin n)}
    (hsep : Separates G {u, v} A B) (haB : a ∉ B) (hbB : b ∉ B) : False := by
  rcases hsep with ⟨hAne, hBne, hAB, hAC, hBC, hunion, hnoedge⟩
  have h2conn := minimal_bad2_no_cut_vertex hmb
  have hB3 : ∀ w ∈ B, 3 ≤ G.degree w := fun w hw =>
    hother w (fun h => haB (h ▸ hw)) (fun h => hbB (h ▸ hw))
  have hB_nb : ∀ w ∈ B, G.neighborFinset w ⊆ B ∪ {u, v} := fun w hw y hy => by
    have hyU : y ∈ A ∪ B ∪ {u, v} := hunion ▸ Finset.mem_univ y
    rcases Finset.mem_union.mp hyU with hyAB | hyC
    · rcases Finset.mem_union.mp hyAB with hyA | hyB
      · exact absurd (G.symm (SimpleGraph.mem_neighborFinset.mp hy)) (hnoedge y hyA w hw)
      · exact Finset.mem_union_left _ hyB
    · exact Finset.mem_union_right _ hyC
  have huv : u ≠ v := fun heq => by
    subst heq; have hC : ({u, u} : Finset (Fin n)) = {u} := by simp
    exact h2conn.2 u A B ⟨hAne, hBne, hAB, hC ▸ hAC, hC ▸ hBC, hC ▸ hunion, hnoedge⟩
  -- Helper: if w ∈ {u, v} has 0 neighbors in B, the other separates A ∪ {w} from B.
  have hdeg_pos : ∀ (p q : Fin n), ({p, q} : Finset (Fin n)) = {u, v} → p ≠ q →
      1 ≤ (G.neighborFinset p ∩ B).card := by
    intro p q hpq hpq_ne; by_contra h0
    have h0' : (G.neighborFinset p ∩ B).card = 0 := by omega
    refine h2conn.2 q (A ∪ {p}) B ⟨Finset.Nonempty.inl hAne, hBne,
      Finset.disjoint_union_left.mpr ⟨hAB, Finset.disjoint_singleton_left.mpr
        (fun hpB => Finset.disjoint_left.mp hBC hpB (hpq ▸ by simp))⟩,
      Finset.disjoint_union_left.mpr ⟨Finset.disjoint_singleton_right.mpr
        (fun hqA => Finset.disjoint_left.mp hAC hqA (hpq ▸ by simp)),
        Finset.disjoint_singleton.mpr hpq_ne⟩,
      Finset.disjoint_singleton_right.mpr (fun hqB => Finset.disjoint_left.mp hBC hqB (hpq ▸ by simp)),
      ?_, fun x hx y hy hxy => (Finset.mem_union.mp hx).elim (fun hxA => hnoedge x hxA y hy hxy)
        (fun hxp => Finset.not_mem_empty y (Finset.card_eq_zero.mp h0' ▸
          Finset.mem_inter.mpr ⟨SimpleGraph.mem_neighborFinset.mpr (Finset.mem_singleton.mp hxp ▸ hxy), hy⟩))⟩
    ext x; have hx : x ∈ A ∪ B ∪ {p, q} := by rw [hpq, hunion]; exact Finset.mem_univ x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_univ, iff_true] at hx ⊢; tauto
  have hdu1 := hdeg_pos u v rfl huv
  have hdv1 := hdeg_pos v u (Finset.pair_comm v u) huv.symm
  -- Helper for Case 2/3: one of {p, q} has ≥ 2 neighbors in B and the other has = 1.
  have hcase_asym : ∀ (p q : Fin n), ({p, q} : Finset (Fin n)) = {u, v} → p ≠ q →
      2 ≤ (G.neighborFinset p ∩ B).card → (G.neighborFinset q ∩ B).card = 1 → False := by
    intro p q hpq hpq_ne hdp2 hdq1
    rcases Finset.card_eq_one.mp hdq1 with ⟨z, hzeq⟩
    have hzB : z ∈ B := (Finset.mem_inter.mp (by rw [hzeq]; simp)).2
    let S := B ∪ {p}
    have hScard : S.card < n := by
      have hqS : q ∉ S := fun hmem => (Finset.mem_union.mp hmem).elim
        (fun hqB => Finset.disjoint_left.mp hBC hqB (hpq ▸ by simp))
        (fun hqp => hpq_ne (Finset.mem_singleton.mp hqp).symm)
      simpa using Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
        ⟨Finset.subset_univ _, fun h => hqS (h ▸ Finset.mem_univ q)⟩)
    have hB_nb' : ∀ w ∈ B, G.neighborFinset w ⊆ B ∪ {p, q} := fun w hw => hpq.symm ▸ hB_nb w hw
    have hsub_of_nez : ∀ x ∈ B, x ≠ z → G.neighborFinset x ⊆ S := fun x hxB hxz y hy => by
      rcases Finset.mem_union.mp (hB_nb' x hxB hy) with hyB | hyPQ
      · exact Finset.mem_union_left _ hyB
      · rcases Finset.mem_insert.mp hyPQ with rfl | hyq
        · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
        · exact absurd (Finset.mem_singleton.mp (hzeq ▸ Finset.mem_inter.mpr
            ⟨SimpleGraph.mem_neighborFinset.mpr (G.symm (Finset.mem_singleton.mp hyq ▸ SimpleGraph.mem_neighborFinset.mp hy)), hxB⟩)) hxz
    refine minimal_bad2_no_near2_proper_subset hmb hScard (near2_induceFin_of_defects S {p, z} Finset.card_le_two ?_ ?_ ?_)
    · intro x hxS
      rcases Finset.mem_union.mp hxS with hxB | hxp
      · have h1 : (G.neighborFinset x \ S).card ≤ 1 :=
          (Finset.card_le_card (t := {q}) (fun y hy => by
            rw [Finset.mem_sdiff] at hy
            rcases Finset.mem_union.mp (hB_nb' x hxB hy.1) with hyB | hyPQ
            · exact absurd (Finset.mem_union_left _ hyB) hy.2
            · rcases Finset.mem_insert.mp hyPQ with rfl | hyq
              · exact absurd (Finset.mem_union_right _ (Finset.mem_singleton_self _)) hy.2
              · exact hyq)).trans (by simp)
        have := inter_card_ge_of_sdiff_le G S x 1 h1; have := hB3 x hxB; omega
      · rw [Finset.mem_singleton.mp hxp]
        exact hdp2.trans (Finset.card_le_card (Finset.inter_subset_inter_left Finset.subset_union_left))
    · intro x hxS hxnot
      have hxB := (Finset.mem_union.mp hxS).resolve_right (by simp [fun h => hxnot (by simp [h])])
      rw [Finset.inter_eq_left.mpr (hsub_of_nez x hxB (fun h => hxnot (by simp [h]))), SimpleGraph.card_neighborFinset_eq_degree]
      exact hB3 x hxB
    · have hB2 : 2 ≤ B.card := hdp2.trans (Finset.card_le_card Finset.inter_subset_right)
      rcases Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hzB]; omega : 0 < (B.erase z).card) with ⟨w, hw⟩
      have hwz := (Finset.mem_erase.mp hw).1; have hwB := (Finset.mem_erase.mp hw).2
      exact ⟨w, Finset.mem_union_left _ hwB, by rw [Finset.inter_eq_left.mpr (hsub_of_nez w hwB hwz), SimpleGraph.card_neighborFinset_eq_degree]; exact hB3 w hwB⟩
  by_cases hdu2 : 2 ≤ (G.neighborFinset u ∩ B).card
  · by_cases hdv2 : 2 ≤ (G.neighborFinset v ∩ B).card
    · let S := B ∪ {u, v}
      have hScard : S.card < n := by
        rcases hAne with ⟨x, hx⟩
        have hxS : x ∉ S := fun hmem => (Finset.mem_union.mp hmem).elim
          (fun h => Finset.disjoint_left.mp hAB hx h) (fun h => Finset.disjoint_left.mp hAC hx h)
        simpa using Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
          ⟨Finset.subset_univ _, fun h => hxS (h ▸ Finset.mem_univ x)⟩)
      refine minimal_bad2_no_near2_proper_subset hmb hScard (near2_induceFin_of_defects S {u, v} Finset.card_le_two ?_ ?_ ?_)
      · intro x hxS
        rcases Finset.mem_union.mp hxS with hxB | hxC
        · rw [Finset.inter_eq_left.mpr (hB_nb x hxB), SimpleGraph.card_neighborFinset_eq_degree]; have := hB3 x hxB; omega
        · rcases Finset.mem_insert.mp hxC with rfl | hxv
          · exact hdu2.trans (Finset.card_le_card (Finset.inter_subset_inter_left Finset.subset_union_left))
          · rw [Finset.mem_singleton.mp hxv]
            exact hdv2.trans (Finset.card_le_card (Finset.inter_subset_inter_left Finset.subset_union_left))
      · intro x hxS hxC
        have hxB := (Finset.mem_union.mp hxS).resolve_right hxC
        rw [Finset.inter_eq_left.mpr (hB_nb x hxB), SimpleGraph.card_neighborFinset_eq_degree]; exact hB3 x hxB
      · rcases hBne with ⟨w, hwB⟩
        exact ⟨w, Finset.mem_union_left _ hwB, by rw [Finset.inter_eq_left.mpr (hB_nb w hwB), SimpleGraph.card_neighborFinset_eq_degree]; exact hB3 w hwB⟩
    · exact hcase_asym u v rfl huv hdu2 (by omega)
  · by_cases hdv2 : 2 ≤ (G.neighborFinset v ∩ B).card
    · exact hcase_asym v u (Finset.pair_comm v u) huv.symm hdv2 (by omega)
    · -- du = 1 and dv = 1 -> cutSize G B ≤ 2
      have hcutB : cutSize G B ≤ 2 := by
        let Su := (G.neighborFinset u ∩ B).image (fun w => (u, w))
        let Sv := (G.neighborFinset v ∩ B).image (fun w => (v, w))
        have hdisj : Disjoint Su Sv := Finset.disjoint_left.mpr fun q hq1 hq2 => by
          rcases Finset.mem_image.mp hq1 with ⟨_, _, rfl⟩
          rcases Finset.mem_image.mp hq2 with ⟨_, _, h⟩; exact huv (Prod.mk.inj h).1.symm
        have h1 : cutSize G B = (Su ∪ Sv).card := by
          unfold cutSize
          refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
          · intro p hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
            have hp2UV := (Finset.mem_union.mp (hB_nb p.1 hp.1 (SimpleGraph.mem_neighborFinset.mpr hp.2.2))).resolve_left hp.2.1
            rcases Finset.mem_insert.mp hp2UV with h2u | h2v
            · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p.1,
                Finset.mem_inter.mpr ⟨SimpleGraph.mem_neighborFinset.mpr (h2u ▸ G.symm hp.2.2), hp.1⟩, by simp [h2u]⟩)
            · rw [Finset.mem_singleton.mp h2v] at hp ⊢
              exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p.1,
                Finset.mem_inter.mpr ⟨SimpleGraph.mem_neighborFinset.mpr (G.symm hp.2.2), hp.1⟩, rfl⟩)
          · intro p1 _ p2 _ h; cases p1; cases p2; simp only [Prod.mk.injEq] at h; exact Prod.ext h.2 h.1
          · intro q hq
            rcases Finset.mem_union.mp hq with hq1 | hq2
            · rcases Finset.mem_image.mp hq1 with ⟨w, hw, rfl⟩
              rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hw
              exact ⟨(w, u), by simp [hw.2, fun huB => Finset.disjoint_left.mp hBC huB (by simp), G.symm hw.1], rfl⟩
            · rcases Finset.mem_image.mp hq2 with ⟨w, hw, rfl⟩
              rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hw
              exact ⟨(w, v), by simp [hw.2, fun hvB => Finset.disjoint_left.mp hBC hvB (by simp), G.symm hw.1], rfl⟩
        rw [h1, Finset.card_union_of_disjoint hdisj,
          Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2),
          Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)]; omega
      have hBuniv : B ≠ Finset.univ := fun h => by
        rcases hAne with ⟨x, hx⟩; exact Finset.disjoint_left.mp hAB hx (h ▸ Finset.mem_univ x)
      by_cases hB2 : 2 ≤ B.card
      · have := minimal_bad2_no_defect_free_two_cut hmb hab hda hdb hother hB2 hBuniv haB hbB; omega
      · rcases Finset.card_eq_one.mp (by have := Finset.card_pos.mpr hBne; omega : B.card = 1) with ⟨w, rfl⟩
        have hdegw : G.degree w = cutSize G {w} := by
          rw [cutSize_eq_sum, Finset.sum_singleton, ← SimpleGraph.card_neighborFinset_eq_degree]
          congr 1; ext y; simp only [Finset.mem_sdiff, Finset.mem_singleton, and_iff_left_iff_imp]
          exact fun hy => (G.ne_of_adj (SimpleGraph.mem_neighborFinset.mp hy)).symm
        have := hB3 w (Finset.mem_singleton_self w); omega

theorem eg2_core_completion_three_edge_connected {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hmb : MinimalBad2 n G) {a b : Fin n} (hab : a ≠ b)
    (hda : G.degree a = 2) (hdb : G.degree b = 2)
    (hother : ∀ x : Fin n, x ≠ a → x ≠ b → 3 ≤ G.degree x) :
    ThreeEdgeConnected (addEdge G a b hab) := by
  have hnonadj := minimal_bad2_defects_nonadjacent hmb hab hda hdb hother
  have h2ec := minimal_bad2_two_edge_connected hmb
  let H := addEdge G a b hab
  have hH_deg3 : ∀ x : Fin n, 3 ≤ H.degree x := fun x => by
    by_cases hxa : x = a
    · subst hxa; rw [addEdge_degree_left G hab hnonadj, hda]
    · by_cases hxb : x = b
      · subst hxb; rw [addEdge_degree_right G hab hnonadj, hdb]
      · rw [addEdge_degree_other G hab hxa hxb]; exact hother x hxa hxb
  intro S hSne hSuniv
  have hH_ge_G : cutSize G S ≤ cutSize H S :=
    Finset.card_le_card (fun p hp => by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢; exact ⟨hp.1, hp.2.1, Or.inl hp.2.2⟩)
  by_cases hsep_ab : (a ∈ S ∧ b ∉ S) ∨ (b ∈ S ∧ a ∉ S)
  · have h2 := h2ec S hSne hSuniv
    have hlt : cutSize G S < cutSize H S := by
      unfold cutSize; apply Finset.card_lt_card; rw [Finset.ssubset_iff_subset_ne]
      refine ⟨fun p hp => by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢; exact ⟨hp.1, hp.2.1, Or.inl hp.2.2⟩,
              fun heq => ?_⟩
      rcases hsep_ab with ⟨haS, hbS⟩ | ⟨hbS, haS⟩
      · have hmem : (a, b) ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 ∈ S ∧ p.2 ∉ S ∧ H.Adj p.1 p.2) := by simp [haS, hbS, H, addEdge]
        rw [← heq] at hmem; simp [hnonadj] at hmem
      · have hmem : (b, a) ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 ∈ S ∧ p.2 ∉ S ∧ H.Adj p.1 p.2) := by simp [hbS, haS, H, addEdge]
        rw [← heq] at hmem; simp [mt G.symm hnonadj] at hmem
    omega
  · by_cases hS1 : S.card = 1
    · rcases Finset.card_eq_one.mp hS1 with ⟨x, rfl⟩
      have hdegx : cutSize H {x} = H.degree x := by
        rw [cutSize_eq_sum, Finset.sum_singleton, ← SimpleGraph.card_neighborFinset_eq_degree]
        congr 1; ext y; simp only [Finset.mem_sdiff, Finset.mem_singleton, and_iff_left_iff_imp]
        exact fun hy => (H.ne_of_adj (SimpleGraph.mem_neighborFinset.mp hy)).symm
      rw [hdegx]; exact hH_deg3 x
    · by_cases hSc1 : Sᶜ.card = 1
      · rw [← cutSize_compl]; rcases Finset.card_eq_one.mp hSc1 with ⟨x, hx⟩; rw [hx]
        have hdegx : cutSize H {x} = H.degree x := by
          rw [cutSize_eq_sum, Finset.sum_singleton, ← SimpleGraph.card_neighborFinset_eq_degree]
          congr 1; ext y; simp only [Finset.mem_sdiff, Finset.mem_singleton, and_iff_left_iff_imp]
          exact fun hy => (H.ne_of_adj (SimpleGraph.mem_neighborFinset.mp hy)).symm
        rw [hdegx]; exact hH_deg3 x
      · have hS2 : 2 ≤ S.card := by have := Finset.card_pos.mpr hSne; omega
        have hSc2 : 2 ≤ Sᶜ.card := by have := Finset.card_pos.mpr (Finset.nonempty_compl.mpr hSuniv); omega
        by_cases haS : a ∈ S
        · have hbS : b ∈ S := by by_contra h; exact hsep_ab (Or.inl ⟨haS, h⟩)
          have h3 := minimal_bad2_no_defect_free_two_cut hmb hab hda hdb hother hSc2
            (fun h => hSne.ne_empty (by simpa using congrArg Compl.compl h)) (by simp [haS]) (by simp [hbS])
          rw [cutSize_compl] at h3; exact h3.trans hH_ge_G
        · have hbS : b ∉ S := fun hb => hsep_ab (Or.inr ⟨hb, haS⟩)
          exact (minimal_bad2_no_defect_free_two_cut hmb hab hda hdb hother hS2 hSuniv haS hbS).trans hH_ge_G

theorem eg2_core_completion_three_connected {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hmb : MinimalBad2 n G) {a b : Fin n} (hab : a ≠ b)
    (hda : G.degree a = 2) (hdb : G.degree b = 2)
    (hother : ∀ x : Fin n, x ≠ a → x ≠ b → 3 ≤ G.degree x) :
    ThreeConnected (addEdge G a b hab) := by
  have hn5 := card_ge_five_of_near2_not_hasPower hmb.1 hmb.2.1
  refine ⟨by rw [Fintype.card_fin]; omega, fun u v A B hsepH => ?_⟩
  have hsepG : Separates G {u, v} A B :=
    ⟨hsepH.1, hsepH.2.1, hsepH.2.2.1, hsepH.2.2.2.1, hsepH.2.2.2.2.1, hsepH.2.2.2.2.2.1,
      fun x hx y hy hxy => hsepH.2.2.2.2.2.2 x hx y hy (Or.inl hxy)⟩
  have hsepG_swap : Separates G {u, v} B A :=
    ⟨hsepG.2.1, hsepG.1, hsepG.2.2.1.symm, hsepG.2.2.2.2.1, hsepG.2.2.2.1,
      by rw [Finset.union_comm B A]; exact hsepG.2.2.2.2.2.1,
      fun x hx y hy hxy => hsepG.2.2.2.2.2.2 y hy x hx (G.symm hxy)⟩
  by_cases haB : a ∈ B
  · exact minimal_bad2_no_defect_free_two_vertex_cut hmb hab hda hdb hother hsepG_swap
      (fun haA => Finset.disjoint_left.mp hsepH.2.2.1 haA haB)
      (fun hbA => hsepH.2.2.2.2.2.2 b hbA a haB (Or.inr (Or.inr ⟨rfl, rfl⟩)))
  · by_cases hbB : b ∈ B
    · exact minimal_bad2_no_defect_free_two_vertex_cut hmb hab hda hdb hother hsepG_swap
        (fun haA => hsepH.2.2.2.2.2.2 a haA b hbB (Or.inr (Or.inl ⟨rfl, rfl⟩)))
        (fun hbA => Finset.disjoint_left.mp hsepH.2.2.1 hbA hbB)
    · exact minimal_bad2_no_defect_free_two_vertex_cut hmb hab hda hdb hother hsepG haB hbB

/-! ### Section 4: Whole-Problem Closure Equivalences (`EGRob3ConnCore ↔ EG2 ⟹ Erdos64`) -/

theorem eg_rob_3conn_core_implies_eg2 (h : EGRob3ConnCore) : EG2 := by
  by_contra hneg
  rcases minimal_bad2_exists hneg with ⟨n, G, inst, hmb⟩
  rcases minimal_bad2_exact_two_defects hmb with ⟨a, b, hab, hda, hdb, hother⟩
  have hnonadj := minimal_bad2_defects_nonadjacent hmb hab hda hdb hother
  let H := addEdge G a b hab
  have hmin3 : MinDeg3 H := ⟨⟨a⟩, fun x => by
    by_cases hxa : x = a
    · subst hxa; rw [addEdge_degree_left G hab hnonadj, hda]
    · by_cases hxb : x = b
      · subst hxb; rw [addEdge_degree_right G hab hnonadj, hdb]
      · rw [addEdge_degree_other G hab hxa hxb]; exact hother x hxa hxb⟩
  have hhigh : HighIndependent H := fun x y hxy hx4 => by
    have hxa : x ≠ a := fun hx => by subst hx; rw [addEdge_degree_left G hab hnonadj, hda] at hx4; omega
    have hxb : x ≠ b := fun hx => by subst hx; rw [addEdge_degree_right G hab hnonadj, hdb] at hx4; omega
    rw [addEdge_degree_other G hab hxa hxb] at hx4
    have hGxy : G.Adj x y := hxy.elim id (fun h' => h'.elim (fun ⟨h1, _⟩ => absurd h1 hxa) (fun ⟨h1, _⟩ => absurd h1 hxb))
    by_cases hya : y = a
    · subst hya; rw [addEdge_degree_left G hab hnonadj, hda]
    · by_cases hyb : y = b
      · subst hyb; rw [addEdge_degree_right G hab hnonadj, hdb]
      · rw [addEdge_degree_other G hab hya hyb]; exact minimal_bad2_high_independent hmb x y hGxy hx4
  have hcub_nb : ∀ x : Fin n, (x = a ∨ x = b ∨ H.Adj a x ∨ H.Adj b x) → H.degree x = 3 := fun x hx => by
    by_cases hxa : x = a
    · subst hxa; rw [addEdge_degree_left G hab hnonadj, hda]
    · by_cases hxb : x = b
      · subst hxb; rw [addEdge_degree_right G hab hnonadj, hdb]
      · rw [addEdge_degree_other G hab hxa hxb]
        rcases hx with rfl | rfl | hax | hbx
        · exact absurd rfl hxa
        · exact absurd rfl hxb
        · exact minimal_bad2_defect_neighbors_cubic hmb hab hda hdb hother
            (hax.elim id (fun h' => h'.elim (fun ⟨_, h2⟩ => absurd h2 hxb) (fun ⟨h1, _⟩ => absurd h1 hab)))
        · exact minimal_bad2_defect_neighbors_cubic hmb hab.symm hdb hda (fun z hzb hza => hother z hza hzb)
            (hbx.elim id (fun h' => h'.elim (fun ⟨h1, _⟩ => absurd h1 hab.symm) (fun ⟨_, h2⟩ => absurd h2 hxa)))
  have hpow := h n H hmin3 (eg2_core_completion_three_connected hmb hab hda hdb hother)
    (eg2_core_completion_three_edge_connected hmb hab hda hdb hother)
    (fun ⟨f, hf⟩ => minimal_bad2_nonbipartite hmb ⟨f, fun x y hxy => hf x y (Or.inl hxy)⟩)
    hhigh a b (Or.inr (Or.inl ⟨rfl, rfl⟩)) hcub_nb
  rw [delEdge_addEdge G hab hnonadj] at hpow; exact hmb.2.1 hpow

theorem eg2_implies_eg_rob (h : EG2) : EGRob := by
  intro n H inst hmin3 a b hab
  have hn4 : 4 ≤ n := by
    have hsub : H.neighborFinset a ⊆ Finset.univ.erase a := fun x hx =>
      Finset.mem_erase.mpr ⟨H.ne_of_adj (H.symm (SimpleGraph.mem_neighborFinset.mp hx)), Finset.mem_univ _⟩
    have hc := Finset.card_le_card hsub
    rw [SimpleGraph.card_neighborFinset_eq_degree, Finset.card_erase_of_mem (Finset.mem_univ a),
      Finset.card_univ, Fintype.card_fin] at hc; have := hmin3.2 a; omega
  refine h n (delEdge H a b) ⟨fun x => ?_, ?_, ?_⟩
  · by_cases hxa : x = a
    · subst hxa; rw [delEdge_degree_left H hab]; have := hmin3.2 x; omega
    · by_cases hxb : x = b
      · subst hxb; rw [delEdge_degree_right H hab]; have := hmin3.2 x; omega
      · rw [delEdge_degree_other H hxa hxb]; have := hmin3.2 x; omega
  · refine (Finset.card_le_card (t := ({a, b} : Finset (Fin n))) ?_).trans Finset.card_le_two
    intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    by_contra hnot
    rw [delEdge_degree_other H (fun h => hnot (by simp [h])) (fun h => hnot (by simp [h]))] at hx
    have := hmin3.2 x; omega
  · have hex : (Finset.univ \ ({a, b} : Finset (Fin n))).Nonempty := by
      have hsum := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (Fin n)) {a, b}
      have hinter : ((Finset.univ : Finset (Fin n)) ∩ {a, b}).card ≤ 2 :=
        (Finset.card_le_card Finset.inter_subset_right).trans Finset.card_le_two
      simp at hsum; exact Finset.card_pos.mp (by omega)
    rcases hex with ⟨z, hz⟩
    exact ⟨z, by rw [delEdge_degree_other H (fun h => by simp [h] at hz) (fun h => by simp [h] at hz)]; exact hmin3.2 z⟩

theorem eg2_iff_eg_rob_3conn_core : EG2 ↔ EGRob3ConnCore :=
  ⟨fun h n H _ hmin3 _ _ _ _ a b hab _ => eg2_implies_eg_rob h n H hmin3 a b hab, eg_rob_3conn_core_implies_eg2⟩

theorem eg2_iff_eg_rob_3conn : EG2 ↔ EGRob3Conn :=
  ⟨fun h n H _ hmin3 _ a b hab => eg2_implies_eg_rob h n H hmin3 a b hab,
   fun h => eg_rob_3conn_core_implies_eg2 (fun n H _ hmin3 h3c _ _ _ a b hab _ => h n H hmin3 h3c a b hab)⟩

theorem eg2_iff_eg_rob_3ec : EG2 ↔ EGRob3EC :=
  ⟨fun h n H _ hmin3 _ a b hab => eg2_implies_eg_rob h n H hmin3 a b hab,
   fun h => eg_rob_3conn_core_implies_eg2 (fun n H _ hmin3 _ h3e _ _ a b hab _ => h n H hmin3 h3e a b hab)⟩

theorem eg_rob_3conn_core_implies_erdos64 (h : EGRob3ConnCore) : Erdos64 := by
  have heg2 := eg_rob_3conn_core_implies_eg2 h
  intro n G inst ⟨⟨v0⟩, hdeg⟩
  refine heg2 n G ⟨fun v => by have := hdeg v; omega, ?_, ⟨v0, hdeg v0⟩⟩
  have hemp : Finset.univ.filter (fun v => G.degree v = 2) = ∅ := by
    ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.not_mem_empty, iff_false]
    have := hdeg v; omega
  rw [hemp, Finset.card_empty]; omega

/-! ### Section 5: Pillar 2 — Cubic Density `> 2/3` & High-Degree Neighborhood Bounds on `EG2-CORE` -/

theorem minimal_bad2_cubic_at_most_two_high_neighbors {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hmb : MinimalBad2 n G) {u : Fin n} (hdu : G.degree u = 3) :
    ((G.neighborFinset u).filter (fun v => 4 ≤ G.degree v)).card ≤ 2 := by
  by_contra hgt2
  have hall4 : ∀ v ∈ G.neighborFinset u, 4 ≤ G.degree v := by
    have heq := Finset.eq_of_subset_of_card_le (Finset.filter_subset (fun v => 4 ≤ G.degree v) (G.neighborFinset u))
      (by rw [SimpleGraph.card_neighborFinset_eq_degree, hdu]; omega)
    intro v hv; exact (Finset.mem_filter.mp (heq ▸ hv)).2
  rcases minimal_bad2_exact_two_defects hmb with ⟨a, b, hab, hda, hdb, hother⟩
  let S := Finset.univ.erase u
  have hScard : S.card < n := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    have := card_ge_five_of_near2_not_hasPower hmb.1 hmb.2.1; omega
  have hdiff1 : ∀ v ∈ S, (G.neighborFinset v \ S).card ≤ 1 := fun v _ =>
    (Finset.card_le_card (t := {u}) (fun z hz => by
      rw [Finset.mem_sdiff] at hz; by_contra hzu; exact hz.2 (Finset.mem_erase.mpr ⟨hzu, Finset.mem_univ _⟩))).trans (by simp)
  refine minimal_bad2_no_near2_proper_subset hmb hScard (near2_induceFin_of_defects S {a, b} Finset.card_le_two ?_ ?_ ?_)
  · intro v hvS
    by_cases hvu : v ∈ G.neighborFinset u
    · have := inter_card_ge_of_sdiff_le G S v 1 (hdiff1 v hvS); have := hall4 v hvu; omega
    · have hsub : G.neighborFinset v ⊆ S := fun z hz =>
        Finset.mem_erase.mpr ⟨fun hzu => hvu (SimpleGraph.mem_neighborFinset.mpr (G.symm (hzu ▸ SimpleGraph.mem_neighborFinset.mp hz))), Finset.mem_univ _⟩
      rw [Finset.inter_eq_left.mpr hsub, SimpleGraph.card_neighborFinset_eq_degree]; exact hmb.1.1 v
  · intro v hvS hvnot
    by_cases hvu : v ∈ G.neighborFinset u
    · have := inter_card_ge_of_sdiff_le G S v 1 (hdiff1 v hvS); have := hall4 v hvu; omega
    · have hsub : G.neighborFinset v ⊆ S := fun z hz =>
        Finset.mem_erase.mpr ⟨fun hzu => hvu (SimpleGraph.mem_neighborFinset.mpr (G.symm (hzu ▸ SimpleGraph.mem_neighborFinset.mp hz))), Finset.mem_univ _⟩
      rw [Finset.inter_eq_left.mpr hsub, SimpleGraph.card_neighborFinset_eq_degree]
      exact hother v (fun h => hvnot (by simp [h])) (fun h => hvnot (by simp [h]))
  · rcases Finset.card_pos.mp (by rw [SimpleGraph.card_neighborFinset_eq_degree, hdu]; omega) with ⟨v, hv⟩
    have hvS : v ∈ S := Finset.mem_erase.mpr ⟨(G.ne_of_adj (SimpleGraph.mem_neighborFinset.mp hv)).symm, Finset.mem_univ _⟩
    exact ⟨v, hvS, by have := inter_card_ge_of_sdiff_le G S v 1 (hdiff1 v hvS); have := hall4 v hv; omega⟩

theorem minimal_bad2_defect_neighbor_at_most_one_high_neighbor {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hmb : MinimalBad2 n G) {a b u : Fin n} (hab : a ≠ b)
    (hda : G.degree a = 2) (hdb : G.degree b = 2)
    (hother : ∀ x : Fin n, x ≠ a → x ≠ b → 3 ≤ G.degree x) (hau : G.Adj a u) :
    ((G.neighborFinset u).filter (fun v => 4 ≤ G.degree v)).card ≤ 1 := by
  have hnonadj := minimal_bad2_defects_nonadjacent hmb hab hda hdb hother
  have hdu3 := minimal_bad2_defect_neighbors_cubic hmb hab hda hdb hother hau
  by_contra hgt1
  have hall4 : ∀ v ∈ (G.neighborFinset u).erase a, 4 ≤ G.degree v := by
    have hsub : (G.neighborFinset u).filter (fun v => 4 ≤ G.degree v) ⊆ (G.neighborFinset u).erase a := fun v hv => by
      rw [Finset.mem_filter] at hv; exact Finset.mem_erase.mpr ⟨fun hva => by subst hva; omega, hv.1⟩
    have hcard_er : ((G.neighborFinset u).erase a).card = 2 := by
      rw [Finset.card_erase_of_mem (SimpleGraph.mem_neighborFinset.mpr (G.symm hau)),
        SimpleGraph.card_neighborFinset_eq_degree, hdu3]
    have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
    intro v hv; exact (Finset.mem_filter.mp (heq ▸ hv)).2
  rcases Finset.card_eq_one.mp (by rw [Finset.card_erase_of_mem (SimpleGraph.mem_neighborFinset.mpr hau),
    SimpleGraph.card_neighborFinset_eq_degree, hda]) with ⟨a2, ha2eq⟩
  let S := (Finset.univ.erase a).erase u
  have hScard : S.card < n := by
    simpa using Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ _, fun h => by have : a ∈ S := h ▸ Finset.mem_univ a; simp [S] at this⟩)
  refine minimal_bad2_no_near2_proper_subset hmb hScard (near2_induceFin_of_defects S {b, a2} Finset.card_le_two ?_ ?_ ?_)
  · intro v hvS
    have hvu := (Finset.mem_erase.mp hvS).1; have hva := (Finset.mem_erase.mp (Finset.mem_erase.mp hvS).2).1
    by_cases hvb : v = b
    · subst hvb
      have hsub : G.neighborFinset v ⊆ S := fun z hz => by
        have hvz := SimpleGraph.mem_neighborFinset.mp hz
        exact Finset.mem_erase.mpr ⟨fun hzu => by
          have := hall4 v (Finset.mem_erase.mpr ⟨hab.symm, SimpleGraph.mem_neighborFinset.mpr (G.symm (hzu ▸ hvz))⟩); omega,
          Finset.mem_erase.mpr ⟨fun hza => hnonadj (G.symm (hza ▸ hvz)), Finset.mem_univ _⟩⟩
      rw [Finset.inter_eq_left.mpr hsub, SimpleGraph.card_neighborFinset_eq_degree, hdb]
    · by_cases hmemu : v ∈ (G.neighborFinset u).erase a
      · have h2 : (G.neighborFinset v \ S).card ≤ 2 :=
          (Finset.card_le_card (t := ({a, u} : Finset (Fin n))) (fun z hz => by
            rw [Finset.mem_sdiff] at hz; by_contra hnot
            exact hz.2 (Finset.mem_erase.mpr ⟨fun h => hnot (by simp [h]),
              Finset.mem_erase.mpr ⟨fun h => hnot (by simp [h]), Finset.mem_univ _⟩⟩))).trans Finset.card_le_two
        have := inter_card_ge_of_sdiff_le G S v 2 h2; have := hall4 v hmemu; omega
      · have h1 : (G.neighborFinset v \ S).card ≤ 1 :=
          (Finset.card_le_card (t := {a}) (fun z hz => by
            rw [Finset.mem_sdiff] at hz; by_contra hza
            exact hz.2 (Finset.mem_erase.mpr ⟨fun hzu => hmemu (Finset.mem_erase.mpr ⟨hva,
              SimpleGraph.mem_neighborFinset.mpr (G.symm (hzu ▸ SimpleGraph.mem_neighborFinset.mp hz.1))⟩),
              Finset.mem_erase.mpr ⟨hza, Finset.mem_univ _⟩⟩))).trans (by simp)
        have := inter_card_ge_of_sdiff_le G S v 1 h1; have := hother v hva hvb; omega
  · intro v hvS hvnot
    have hvb : v ≠ b := fun h => hvnot (by simp [h])
    have hva2 : v ≠ a2 := fun h => hvnot (by simp [h])
    have hvu := (Finset.mem_erase.mp hvS).1; have hva := (Finset.mem_erase.mp (Finset.mem_erase.mp hvS).2).1
    have hnot_a : ¬G.Adj v a := fun hGva => hva2 (Finset.mem_singleton.mp (ha2eq ▸
      Finset.mem_erase.mpr ⟨hvu, SimpleGraph.mem_neighborFinset.mpr (G.symm hGva)⟩))
    by_cases hmemu : v ∈ (G.neighborFinset u).erase a
    · have h1 : (G.neighborFinset v \ S).card ≤ 1 :=
        (Finset.card_le_card (t := {u}) (fun z hz => by
          rw [Finset.mem_sdiff] at hz; by_contra hzu
          exact hz.2 (Finset.mem_erase.mpr ⟨hzu, Finset.mem_erase.mpr ⟨fun hza => hnot_a (hza ▸ SimpleGraph.mem_neighborFinset.mp hz.1), Finset.mem_univ _⟩⟩))).trans (by simp)
      have := inter_card_ge_of_sdiff_le G S v 1 h1; have := hall4 v hmemu; omega
    · have hsub : G.neighborFinset v ⊆ S := fun z hz =>
        Finset.mem_erase.mpr ⟨fun hzu => hmemu (Finset.mem_erase.mpr ⟨hva,
          SimpleGraph.mem_neighborFinset.mpr (G.symm (hzu ▸ SimpleGraph.mem_neighborFinset.mp hz))⟩),
          Finset.mem_erase.mpr ⟨fun hza => hnot_a (hza ▸ SimpleGraph.mem_neighborFinset.mp hz), Finset.mem_univ _⟩⟩
      rw [Finset.inter_eq_left.mpr hsub, SimpleGraph.card_neighborFinset_eq_degree]; exact hother v hva hvb
  · have hcard_er : ((G.neighborFinset u).erase a).card = 2 := by
      rw [Finset.card_erase_of_mem (SimpleGraph.mem_neighborFinset.mpr (G.symm hau)),
        SimpleGraph.card_neighborFinset_eq_degree, hdu3]
    rcases Finset.card_pos.mp (by omega : 0 < ((G.neighborFinset u).erase a).card) with ⟨v, hv⟩
    have hva := (Finset.mem_erase.mp hv).1
    have hvu := (G.ne_of_adj (SimpleGraph.mem_neighborFinset.mp (Finset.mem_erase.mp hv).2)).symm
    have hv4 := hall4 v hv
    have hnot_a : ¬G.Adj v a := fun hGva => by
      have := minimal_bad2_defect_neighbors_cubic hmb hab hda hdb hother (G.symm hGva); omega
    have h1 : (G.neighborFinset v \ S).card ≤ 1 :=
      (Finset.card_le_card (t := {u}) (fun z hz => by
        rw [Finset.mem_sdiff] at hz; by_contra hzu
        exact hz.2 (Finset.mem_erase.mpr ⟨hzu, Finset.mem_erase.mpr ⟨fun hza => hnot_a (hza ▸ SimpleGraph.mem_neighborFinset.mp hz.1), Finset.mem_univ _⟩⟩))).trans (by simp)
    exact ⟨v, Finset.mem_erase.mpr ⟨hvu, Finset.mem_erase.mpr ⟨hva, Finset.mem_univ _⟩⟩,
      by have := inter_card_ge_of_sdiff_le G S v 1 h1; omega⟩

theorem minimal_bad2_cubic_density_bound {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hmb : MinimalBad2 n G) :
    4 * n - 5 ≤ 6 * (Finset.univ.filter (fun v => G.degree v = 3)).card := by
  rcases minimal_bad2_exact_two_defects hmb with ⟨a, b, hab, hda, hdb, hother⟩
  let V3 := Finset.univ.filter (fun v => G.degree v = 3)
  let V4 := Finset.univ.filter (fun v => 4 ≤ G.degree v)
  let Ndef := G.neighborFinset a ∪ G.neighborFinset b
  have hNdef_sub : Ndef ⊆ V3 := fun u hu => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    (Finset.mem_union.mp hu).elim
      (fun hua => minimal_bad2_defect_neighbors_cubic hmb hab hda hdb hother (SimpleGraph.mem_neighborFinset.mp hua))
      (fun hub => minimal_bad2_defect_neighbors_cubic hmb hab.symm hdb hda (fun z hzb hza => hother z hza hzb) (SimpleGraph.mem_neighborFinset.mp hub))⟩
  have hNdef_card : 3 ≤ Ndef.card := by
    have hinter : (G.neighborFinset a ∩ G.neighborFinset b).card ≤ 1 := by
      by_contra hgt1
      rcases Finset.one_lt_card.mp (by omega : 1 < (G.neighborFinset a ∩ G.neighborFinset b).card) with ⟨x, hx, y, hy, hxy⟩
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset] at hx hy
      exact no_c4_of_not_hasPower hmb.2.1 hx.1 (G.symm hx.2) hy.2 (G.symm hy.1) hab hxy
    have hsum := Finset.card_union_add_card_inter (G.neighborFinset a) (G.neighborFinset b)
    rw [SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.card_neighborFinset_eq_degree, hda, hdb] at hsum; omega
  have hhigh := minimal_bad2_high_independent hmb
  have hV4_nb : ∀ v ∈ V4, G.neighborFinset v ⊆ V3 := fun v hv u hu => by
    have hv4 := (Finset.mem_filter.mp hv).2; have hvu := SimpleGraph.mem_neighborFinset.mp hu
    have hu3 := hhigh v u hvu hv4; have hu2 := hmb.1.1 u
    have hune2 : G.degree u ≠ 2 := fun hu2eq => by
      have hor : u = a ∨ u = b := by by_contra hnot; push_neg at hnot; have := hother u hnot.1 hnot.2; omega
      rcases hor with rfl | rfl
      · have := minimal_bad2_defect_neighbors_cubic hmb hab hda hdb hother (G.symm hvu); omega
      · have := minimal_bad2_defect_neighbors_cubic hmb hab.symm hdb hda (fun z hzb hza => hother z hza hzb) (G.symm hvu); omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
  have h4V4 : 4 * V4.card ≤ ∑ v ∈ V4, G.degree v := by
    calc 4 * V4.card = ∑ _v ∈ V4, 4 := by simp [mul_comm]
    _ ≤ ∑ v ∈ V4, G.degree v := Finset.sum_le_sum (fun v hv => (Finset.mem_filter.mp hv).2)
  have hdouble : ∑ v ∈ V4, G.degree v = ∑ u ∈ V3, ((G.neighborFinset u).filter (fun v => 4 ≤ G.degree v)).card := by
    have hlhs : ∑ v ∈ V4, G.degree v = (Finset.univ.filter (fun p : Fin n × Fin n => p.1 ∈ V4 ∧ G.Adj p.1 p.2)).card := by
      rw [Finset.sum_congr rfl (fun v _ => (SimpleGraph.card_neighborFinset_eq_degree).symm), ← Finset.card_sigma]
      refine Finset.card_bij (fun q _ => (q.1, q.2))
        (fun q hq => by simp only [Finset.mem_sigma, SimpleGraph.mem_neighborFinset] at hq; simp [hq.1, hq.2])
        (fun q1 _ q2 _ h => by cases q1; cases q2; simp at h; rcases h with ⟨rfl, rfl⟩; rfl)
        (fun p hp => by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp; exact ⟨⟨p.1, p.2⟩, by simp [hp.1, SimpleGraph.mem_neighborFinset, hp.2], rfl⟩)
    have hrhs : ∑ u ∈ V3, ((G.neighborFinset u).filter (fun v => 4 ≤ G.degree v)).card =
        (Finset.univ.filter (fun p : Fin n × Fin n => p.1 ∈ V4 ∧ G.Adj p.1 p.2)).card := by
      rw [← Finset.card_sigma]
      refine Finset.card_bij (fun q _ => (q.2, q.1))
        (fun q hq => by simp only [Finset.mem_sigma, Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hq
                        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq.2.2⟩, G.symm hq.2.1⟩)
        (fun q1 _ q2 _ h => by cases q1; cases q2; simp at h; rcases h with ⟨rfl, rfl⟩; rfl)
        (fun p hp => by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
                        exact ⟨⟨p.2, p.1⟩, by simp only [Finset.mem_sigma, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
                                             exact ⟨hV4_nb p.1 hp.1 (SimpleGraph.mem_neighborFinset.mpr hp.2), G.symm hp.2, (Finset.mem_filter.mp hp.1).2⟩, rfl⟩)
    rw [hlhs, hrhs]
  have hupper : ∑ u ∈ V3, ((G.neighborFinset u).filter (fun v => 4 ≤ G.degree v)).card ≤ 2 * V3.card - Ndef.card := by
    have hsplit := (Finset.sum_sdiff hNdef_sub (f := fun u => ((G.neighborFinset u).filter (fun v => 4 ≤ G.degree v)).card)).symm
    have h1 : ∑ u ∈ Ndef, ((G.neighborFinset u).filter (fun v => 4 ≤ G.degree v)).card ≤ Ndef.card :=
      (Finset.sum_le_sum fun u hu => (Finset.mem_union.mp hu).elim
        (fun hua => minimal_bad2_defect_neighbor_at_most_one_high_neighbor hmb hab hda hdb hother (SimpleGraph.mem_neighborFinset.mp hua))
        (fun hub => minimal_bad2_defect_neighbor_at_most_one_high_neighbor hmb hab.symm hdb hda (fun z hzb hza => hother z hza hzb) (SimpleGraph.mem_neighborFinset.mp hub))).trans (by simp)
    have h2 : ∑ u ∈ V3 \ Ndef, ((G.neighborFinset u).filter (fun v => 4 ≤ G.degree v)).card ≤ 2 * (V3 \ Ndef).card :=
      (Finset.sum_le_sum fun u hu => minimal_bad2_cubic_at_most_two_high_neighbors hmb (Finset.mem_filter.mp (Finset.mem_sdiff.mp hu).1).2).trans (by simp [mul_comm])
    have hcard_sdiff : (V3 \ Ndef).card + Ndef.card = V3.card := by
      rw [Finset.card_sdiff hNdef_sub, Nat.sub_add_cancel (Finset.card_le_card hNdef_sub)]
    omega
  have hpart : V3.card + V4.card + 2 = n := by
    have hdisj : Disjoint V3 V4 := Finset.disjoint_left.mpr fun x h3 h4 => by
      have := (Finset.mem_filter.mp h3).2; have := (Finset.mem_filter.mp h4).2; omega
    have hdisj2 : Disjoint (V3 ∪ V4) ({a, b} : Finset (Fin n)) := Finset.disjoint_left.mpr fun x hx hab' => by
      simp at hab'; rcases Finset.mem_union.mp hx with h3 | h4
      · have := (Finset.mem_filter.mp h3).2; rcases hab' with rfl | rfl <;> omega
      · have := (Finset.mem_filter.mp h4).2; rcases hab' with rfl | rfl <;> omega
    have hunion : (V3 ∪ V4) ∪ ({a, b} : Finset (Fin n)) = Finset.univ := by
      ext x; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, iff_true]
      by_cases hxa : x = a
      · exact Or.inr (Or.inl hxa)
      · by_cases hxb : x = b
        · exact Or.inr (Or.inr hxb)
        · have := hother x hxa hxb; by_cases hx4 : 4 ≤ G.degree x
          · exact Or.inl (Or.inr hx4)
          · exact Or.inl (Or.inl (by omega))
    have hc := congrArg Finset.card hunion
    rw [Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj,
      Finset.card_pair hab, Finset.card_univ, Fintype.card_fin] at hc; exact hc
  omega

end E64Wave5Agent2EGRob
