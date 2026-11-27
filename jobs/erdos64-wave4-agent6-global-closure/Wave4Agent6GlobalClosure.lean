import Remaining
import MinimalCutCompletion
import CutCompletionApplication
import ConnectivityAndCuts
import CutBoundaryWeapons
import Descent

/-!
Erdős Problem #64 (Erdős–Gyárfás Conjecture) — Wave 4 Agent #6 Global Closure Architecture.

All theorems in this module are all-order (no bound on |V|), zero-`sorry`, zero-`native_decide`,
and depend only on standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).

Three Whole-Problem-Closing Pillars directly tied to `Erdos64Closure.Original`:
1. **Universal Max-Cut Frustration-Matching Decomposition (ALL 13 Open Leaves)**:
   Every `MinimalBad G` admits a Max-Cut `f : V → Bool` whose frustrated edge set is nonempty,
   satisfies `2 * frustDeg G f v ≤ G.degree v` everywhere, forms a matching on `V_3 ∪ {w}`,
   and leaves a power-free bipartite spanning subgraph `bipSubgraph G f` with `δ ≥ 2` on `V_{≥3}`.
   Whole-Problem Closure Gate #1: `original_of_max_cut_bipartite_power`.
2. **Universal `w`-Free Minimal 2-Cut Completion (ALL 6 `*-2` Leaves: `C/S/H-*-2`)**:
   Generalizes the 2026-11-27 cubic-only minimal 2-cut completion (`CutCompletionApplication.lean`)
   to EVERY `MinimalBad G` with `SmallCut G 2` (cubic, subcubic-defect, and high-defect).
   Produces a strictly smaller 3-edge-connected simple graph `H` with `δ(H) ≥ 3` (zero defect!)
   and an edge `ab` such that `HasPower H ∧ ¬ HasPower (H \ edge a b)`.
   Whole-Problem Closure Gate #2: `EdgeAvoidingPower` unconditionally closes all 6 `*-2` leaves
   AND `C-N-R` (7 of the 13 remaining leaves), reducing `Original` to the 6 `*-3` leaves alone
   (`original_of_edge_avoiding_and_low3`).
3. **Universal Perfect-Matching Contraction (`C-N-R`, `C-N-2`, `C-N-3`)**:
   For any cubic, triangle-free `MinimalBad G` with a perfect matching `m` (fixed-point-free
   involution along edges), contracting every matching edge produces a strictly smaller
   **simple 4-regular** graph `MContract G m` satisfying `HasPower (MContract G m)`.
-/

namespace E64Wave4Agent6
open SimpleGraph Erdos64Closure E64Core E64Leaves Erdos64Descent E64MinimalCut
universe u

/-! ## Pillar 1: Universal Max-Cut Frustration-Matching Decomposition -/

/-- Every `MinimalBad` graph is nonbipartite (immediate from the 13 Lean-closed leaves). -/
theorem minimal_bad_not_bip {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G) : ¬ Bip G := by
  obtain ⟨l, hl⟩ := cover G hm
  cases l with
  | cb => exact False.elim (E64Remaining.exclude_closed .cb rfl V G hm hl)
  | sb => exact False.elim (E64Remaining.exclude_closed .sb rfl V G hm hl)
  | ct s => exact hl.2.1
  | cn s => exact hl.2.1
  | st s => exact hl.2.1
  | sn s => exact hl.2.1
  | hb s => exact False.elim (E64Remaining.exclude_closed (.hb s) rfl V G hm hl)
  | ht s => exact hl.2.1
  | hn s => exact hl.2.1

/-- Number of oriented crossing edges of a bipartition `f : V → Bool`. -/
noncomputable def cutCard {V : Type u} [Fintype V] (G : SimpleGraph V) (f : V → Bool) : ℕ := by
  classical
  exact ((Finset.univ : Finset (V × V)).filter (fun e => G.Adj e.1 e.2 ∧ f e.1 ≠ f e.2)).card

/-- Number of opposite-color (bipartite) neighbors of `v` under `f`. -/
noncomputable def bipDeg {V : Type u} [Fintype V] (G : SimpleGraph V) (f : V → Bool) (v : V) : ℕ := by
  classical
  exact ((G.neighborFinset v).filter (fun u => f u ≠ f v)).card

/-- Number of same-color (frustrated) neighbors of `v` under `f`. -/
noncomputable def frustDeg {V : Type u} [Fintype V] (G : SimpleGraph V) (f : V → Bool) (v : V) : ℕ := by
  classical
  exact ((G.neighborFinset v).filter (fun u => f u = f v)).card

/-- The bipartite spanning subgraph induced by a bipartition `f : V → Bool`. -/
def bipSubgraph {V : Type u} (G : SimpleGraph V) (f : V → Bool) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ f u ≠ f v
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun v h => G.loopless.irrefl v h.1⟩

theorem bipSubgraph_le {V : Type u} (G : SimpleGraph V) (f : V → Bool) :
    bipSubgraph G f ≤ G := fun _ _ h => h.1

theorem bipSubgraph_bip {V : Type u} (G : SimpleGraph V) (f : V → Bool) :
    Bip (bipSubgraph G f) := ⟨f, fun _ _ h => h.2⟩

theorem bipDeg_add_frustDeg {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : V → Bool) (v : V) : bipDeg G f v + frustDeg G f v = G.degree v := by
  classical
  let e : G.neighborSet v ≃
      {u : V // u ∈ (Finset.univ.filter (fun u => G.Adj v u ∧ f u ≠ f v))} ⊕
      {u : V // u ∈ (Finset.univ.filter (fun u => G.Adj v u ∧ f u = f v))} :=
    { toFun := fun u =>
        if h : f u.1 = f v then
          Sum.inr ⟨u.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, u.2, h⟩⟩
        else
          Sum.inl ⟨u.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, u.2, h⟩⟩
      invFun := Sum.elim
        (fun u => ⟨u.1, (Finset.mem_filter.mp u.2).2.1⟩)
        (fun u => ⟨u.1, (Finset.mem_filter.mp u.2).2.1⟩)
      left_inv := by intro u; by_cases h : f u.1 = f v <;> simp [h]
      right_inv := by
        rintro (u | u)
        · have hne : f u.1 ≠ f v := (Finset.mem_filter.mp u.2).2.2
          simp [hne]
        · have heq : f u.1 = f v := (Finset.mem_filter.mp u.2).2.2
          simp [heq] }
  have hc := Fintype.card_congr e
  rw [SimpleGraph.card_neighborSet_eq_degree, Fintype.card_sum,
    Fintype.card_coe, Fintype.card_coe] at hc
  have hb : bipDeg G f v = (Finset.univ.filter (fun u => G.Adj v u ∧ f u ≠ f v)).card := by
    unfold bipDeg
    congr 1
    ext u
    simp [SimpleGraph.mem_neighborFinset]
  have hf : frustDeg G f v = (Finset.univ.filter (fun u => G.Adj v u ∧ f u = f v)).card := by
    unfold frustDeg
    congr 1
    ext u
    simp [SimpleGraph.mem_neighborFinset]
  rw [hb, hf]
  exact hc.symm

/-- Every finite graph admits a Max-Cut bipartition maximizing `cutCard G f`. -/
theorem exists_max_cut {V : Type u} [Fintype V] (G : SimpleGraph V) :
    ∃ f : V → Bool, ∀ g : V → Bool, cutCard G g ≤ cutCard G f := by
  classical
  have hne : (Finset.univ : Finset (V → Bool)).Nonempty := ⟨fun _ => false, Finset.mem_univ _⟩
  obtain ⟨f, _, hf⟩ := Finset.exists_max_image (Finset.univ : Finset (V → Bool)) (cutCard G) hne
  exact ⟨f, fun g => hf g (Finset.mem_univ g)⟩

/-- Flipping vertex `v` in `f` changes `cutCard` by `2 * (frustDeg - bipDeg)`. -/
private theorem cutCard_flip {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (f : V → Bool) (v : V) :
    cutCard G (Function.update f v (!f v)) + 2 * bipDeg G f v =
      cutCard G f + 2 * frustDeg G f v := by
  classical
  let f' := Function.update f v (!f v)
  let S (g : V → Bool) : Finset (V × V) :=
    (Finset.univ : Finset (V × V)).filter (fun e => G.Adj e.1 e.2 ∧ g e.1 ≠ g e.2)
  let A (g : V → Bool) := (S g).filter (fun e => e.1 ≠ v ∧ e.2 ≠ v)
  let B1 (g : V → Bool) := (S g).filter (fun e => e.1 = v)
  let B2 (g : V → Bool) := (S g).filter (fun e => e.2 = v)
  have hpart : ∀ g : V → Bool, (S g).card = (A g).card + (B1 g).card + (B2 g).card := by
    intro g
    have hd1 : Disjoint (A g) (B1 g) := by
      rw [Finset.disjoint_filter]; intro e _ h1 h2; exact h1.1 h2
    have hd2 : Disjoint (A g ∪ B1 g) (B2 g) := by
      rw [Finset.disjoint_left]
      intro e he h2
      have h2' := (Finset.mem_filter.mp h2).2
      rcases Finset.mem_union.mp he with hA | hB1
      · exact (Finset.mem_filter.mp hA).2.2 h2'
      · have h1' := (Finset.mem_filter.mp hB1).2
        have hadj := (Finset.mem_filter.mp (Finset.mem_filter.mp hB1).1).2.1
        rw [h1', h2'] at hadj
        exact G.loopless.irrefl v hadj
    have hu : (A g ∪ B1 g) ∪ B2 g = S g := by
      ext e
      simp only [Finset.mem_union, A, B1, B2, Finset.mem_filter]
      constructor
      · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
      · intro h
        by_cases h1 : e.1 = v
        · exact Or.inl (Or.inr ⟨h, h1⟩)
        · by_cases h2 : e.2 = v
          · exact Or.inr ⟨h, h2⟩
          · exact Or.inl (Or.inl ⟨h, h1, h2⟩)
    rw [← hu, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]
  have hAeq : A f' = A f := by
    ext e
    simp only [A, S, Finset.mem_filter, Finset.mem_univ, true_and, f']
    constructor
    · rintro ⟨⟨hadj, hne⟩, h1, h2⟩
      rw [Function.update_of_ne h1, Function.update_of_ne h2] at hne
      exact ⟨⟨hadj, hne⟩, h1, h2⟩
    · rintro ⟨⟨hadj, hne⟩, h1, h2⟩
      refine ⟨⟨hadj, ?_⟩, h1, h2⟩
      rw [Function.update_of_ne h1, Function.update_of_ne h2]
      exact hne
  have hB1_f : (B1 f).card = bipDeg G f v := by
    unfold bipDeg
    refine Finset.card_bij (fun e _ => e.2) ?_ ?_ ?_
    · intro e he
      have h1 := (Finset.mem_filter.mp he).2
      have hS := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
      rw [h1] at hS
      exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset v e.2).mpr hS.1, hS.2.symm⟩
    · intro e1 he1 e2 he2 heq
      have h1 := (Finset.mem_filter.mp he1).2
      have h2 := (Finset.mem_filter.mp he2).2
      exact Prod.ext (h1.trans h2.symm) heq
    · intro u hu
      have hmem := Finset.mem_filter.mp hu
      refine ⟨(v, u), ?_, rfl⟩
      simp only [B1, S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨⟨(G.mem_neighborFinset v u).mp hmem.1, hmem.2.symm⟩, trivial⟩
  have hB2_f : (B2 f).card = bipDeg G f v := by
    unfold bipDeg
    refine Finset.card_bij (fun e _ => e.1) ?_ ?_ ?_
    · intro e he
      have h2 := (Finset.mem_filter.mp he).2
      have hS := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
      rw [h2] at hS
      exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset v e.1).mpr hS.1.symm, hS.2⟩
    · intro e1 he1 e2 he2 heq
      have h1 := (Finset.mem_filter.mp he1).2
      have h2 := (Finset.mem_filter.mp he2).2
      exact Prod.ext heq (h1.trans h2.symm)
    · intro u hu
      have hmem := Finset.mem_filter.mp hu
      refine ⟨(u, v), ?_, rfl⟩
      simp only [B2, S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨⟨((G.mem_neighborFinset v u).mp hmem.1).symm, hmem.2⟩, trivial⟩
  have hflip_iff : ∀ u : V, u ≠ v → (f' v ≠ f' u ↔ f u = f v) := by
    intro u huv
    simp only [f', Function.update_self, Function.update_of_ne huv]
    cases f v <;> cases f u <;> decide
  have hB1_f' : (B1 f').card = frustDeg G f v := by
    unfold frustDeg
    refine Finset.card_bij (fun e _ => e.2) ?_ ?_ ?_
    · intro e he
      have h1 := (Finset.mem_filter.mp he).2
      have hS := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
      rw [h1] at hS
      have huv : e.2 ≠ v := (G.ne_of_adj hS.1).symm
      exact Finset.mem_filter.mpr
        ⟨(G.mem_neighborFinset v e.2).mpr hS.1, (hflip_iff e.2 huv).mp hS.2⟩
    · intro e1 he1 e2 he2 heq
      have h1 := (Finset.mem_filter.mp he1).2
      have h2 := (Finset.mem_filter.mp he2).2
      exact Prod.ext (h1.trans h2.symm) heq
    · intro u hu
      have hmem := Finset.mem_filter.mp hu
      have hadj : G.Adj v u := (G.mem_neighborFinset v u).mp hmem.1
      have huv : u ≠ v := (G.ne_of_adj hadj).symm
      refine ⟨(v, u), ?_, rfl⟩
      simp only [B1, S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨⟨hadj, (hflip_iff u huv).mpr hmem.2⟩, trivial⟩
  have hB2_f' : (B2 f').card = frustDeg G f v := by
    unfold frustDeg
    refine Finset.card_bij (fun e _ => e.1) ?_ ?_ ?_
    · intro e he
      have h2 := (Finset.mem_filter.mp he).2
      have hS := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
      rw [h2] at hS
      have huv : e.1 ≠ v := G.ne_of_adj hS.1
      exact Finset.mem_filter.mpr
        ⟨(G.mem_neighborFinset v e.1).mpr hS.1.symm, (hflip_iff e.1 huv).mp hS.2.symm⟩
    · intro e1 he1 e2 he2 heq
      have h1 := (Finset.mem_filter.mp he1).2
      have h2 := (Finset.mem_filter.mp he2).2
      exact Prod.ext heq (h1.trans h2.symm)
    · intro u hu
      have hmem := Finset.mem_filter.mp hu
      have hadj : G.Adj v u := (G.mem_neighborFinset v u).mp hmem.1
      have huv : u ≠ v := (G.ne_of_adj hadj).symm
      refine ⟨(u, v), ?_, rfl⟩
      simp only [B2, S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨⟨hadj.symm, ((hflip_iff u huv).mpr hmem.2).symm⟩, trivial⟩
  change (S f').card + 2 * bipDeg G f v = (S f).card + 2 * frustDeg G f v
  rw [hpart f', hpart f, hAeq, hB1_f, hB2_f, hB1_f', hB2_f']
  omega

/-- At any Max-Cut `f`, every vertex has at most as many frustrated neighbors as bipartite neighbors. -/
theorem max_cut_frustDeg_le_bipDeg {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (f : V → Bool) (hmax : ∀ g : V → Bool, cutCard G g ≤ cutCard G f)
    (v : V) : frustDeg G f v ≤ bipDeg G f v := by
  have hflip := cutCard_flip G f v
  have hle := hmax (Function.update f v (!f v))
  omega

/-- Universal Max-Cut Frustration-Matching Decomposition for ALL `MinimalBad` graphs
    (uniformly covering all 13 open leaves: `C-*`, `S-*`, `H-*`, both `CUT` and `C-N-R`). -/
theorem minimal_bad_max_cut_frustrated_matching {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G) :
    ∃ f : V → Bool,
      (∀ g : V → Bool, cutCard G g ≤ cutCard G f) ∧
      (∃ u v : V, G.Adj u v ∧ f u = f v) ∧
      (∀ v : V, 2 * frustDeg G f v ≤ G.degree v ∧ G.degree v ≤ 2 * bipDeg G f v) ∧
      (∀ v : V, G.degree v ≤ 3 → frustDeg G f v ≤ 1) ∧
      (∀ v : V, 3 ≤ G.degree v → 2 ≤ bipDeg G f v) ∧
      Bip (bipSubgraph G f) ∧ ¬ HasPower (bipSubgraph G f) := by
  obtain ⟨f, hmax⟩ := exists_max_cut G
  have hnotbip := minimal_bad_not_bip G hm
  have hfrust : ∃ u v : V, G.Adj u v ∧ f u = f v := by
    by_contra h
    exact hnotbip ⟨f, fun u v huv heq => h ⟨u, v, huv, heq⟩⟩
  refine ⟨f, hmax, hfrust, ?_, ?_, ?_, bipSubgraph_bip G f,
    fun hp => hm.2.1 (power_mono (bipSubgraph_le G f) hp)⟩
  · intro v
    have hsum := bipDeg_add_frustDeg G f v
    have hle := max_cut_frustDeg_le_bipDeg G f hmax v
    omega
  · intro v hv
    have hsum := bipDeg_add_frustDeg G f v
    have hle := max_cut_frustDeg_le_bipDeg G f hmax v
    omega
  · intro v hv
    have hsum := bipDeg_add_frustDeg G f v
    have hle := max_cut_frustDeg_le_bipDeg G f hmax v
    omega

/-- Whole-Problem Closure Gate #1: If every `MinimalBad` graph has a Max-Cut whose
    bipartite spanning subgraph contains a power-of-2 cycle, then full Erdős #64 is CLOSED. -/
theorem original_of_max_cut_bipartite_power
    (h : ∀ (V : Type u) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
      MinimalBad G → ∃ f : V → Bool,
        (∀ g : V → Bool, cutCard G g ≤ cutCard G f) ∧ HasPower (bipSubgraph G f)) :
    ∀ (V : Type u) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
      G.minDegree ≥ 3 → ∃ (k : ℕ) (v : V) (c : G.Walk v v),
        k ≥ 2 ∧ c.IsCycle ∧ c.length = 2 ^ k := by
  apply erdos64_of_global_descent
  intro V G _ _ hn hnp
  obtain ⟨W, fW, H, dH, hm⟩ := minimal_bad_exists ⟨V, inferInstance, G, inferInstance, hn, hnp⟩
  let _ : Fintype W := fW
  let _ : DecidableRel H.Adj := dH
  obtain ⟨f, _, hpow⟩ := h W H hm
  exact False.elim (hm.2.1 (power_mono (bipSubgraph_le H f) hpow))

/-! ## Pillar 2: Universal `w`-Free Minimal 2-Cut Completion (ALL 6 `*-2` Leaves) -/

private theorem boundary_compl_card' {V : Type u} (G : SimpleGraph V) (S : Set V) :
    Nat.card (Boundary G Sᶜ) = Nat.card (Boundary G S) := by
  classical
  let e : Boundary G Sᶜ ≃ Boundary G S :=
    { toFun := fun p => ⟨(p.1.2, p.1.1), by
        exact ⟨by simpa using p.2.2.1, p.2.1, p.2.2.2.symm⟩⟩
      invFun := fun p => ⟨(p.1.2, p.1.1), by
        exact ⟨p.2.2.1, by simpa using p.2.1, p.2.2.2.symm⟩⟩
      left_inv := by intro p; apply Subtype.ext; rfl
      right_inv := by intro p; apply Subtype.ext; rfl }
  exact Nat.card_congr e

/-- In ANY `MinimalBad` graph with `SmallCut G 2` (all 6 `*-2` leaves: `C/S/H-*-2`),
    there exists an inclusion-minimal `w`-free 2-cut side `A` satisfying `SideMinimal G A`. -/
theorem select_wfree_minimal_two_cut {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G) (hcut : SmallCut G 2) :
    ∃ A : Set V, 2 ≤ Nat.card A ∧ 2 ≤ Nat.card (Aᶜ : Set V) ∧
      Nat.card (Boundary G A) ≤ 2 ∧
      (∀ z : A, 3 ≤ G.degree z.1) ∧ SideMinimal G A := by
  classical
  obtain ⟨w, hw⟩ := hm.1.2
  let P : ℕ → Prop := fun n => ∃ A : Set V,
    2 ≤ Nat.card A ∧ 2 ≤ Nat.card (Aᶜ : Set V) ∧
    Nat.card (Boundary G A) ≤ 2 ∧ (∀ z : A, 3 ≤ G.degree z.1) ∧ Nat.card A = n
  have hex : ∃ n, P n := by
    obtain ⟨S, hS, hSc, hB⟩ := hcut
    by_cases hwS : w ∈ S
    · refine ⟨Nat.card (Sᶜ : Set V), Sᶜ, hSc, ?_, ?_, ?_, rfl⟩
      · simpa only [compl_compl] using hS
      · rwa [boundary_compl_card']
      · intro z
        apply hw z.1
        intro hz
        exact z.2 (hz ▸ hwS)
    · refine ⟨Nat.card S, S, hS, hSc, hB, ?_, rfl⟩
      intro z
      apply hw z.1
      intro hz
      exact hwS (hz ▸ z.2)
  obtain ⟨A, hA, hAc, hB, hwfree, hN⟩ := Nat.find_spec hex
  refine ⟨A, hA, hAc, hB, hwfree, ?_⟩
  intro T hTA hT hne
  by_contra hn
  have hc : Nat.card (Boundary G T) ≤ 2 := by omega
  have hTc : 2 ≤ Nat.card (Tᶜ : Set V) := by
    let f : (Aᶜ : Set V) → (Tᶜ : Set V) := fun z => ⟨z.1, fun hz => z.2 (hTA hz)⟩
    have hf : Function.Injective f := fun p q h =>
      Subtype.ext (congrArg (fun z : (Tᶜ : Set V) => z.1) h)
    exact hAc.trans (Nat.card_le_card_of_injective f hf)
  by_cases hT2 : 2 ≤ Nat.card T
  · have hp : P (Nat.card T) := ⟨T, hT2, hTc, hc, fun z => hwfree ⟨z.1, hTA z.2⟩, rfl⟩
    have hmin := Nat.find_min' hex hp
    have hlt : Nat.card T < Nat.card A := by
      let f : T → A := fun z => ⟨z.1, hTA z.2⟩
      have hf : Function.Injective f := fun p q h =>
        Subtype.ext (congrArg (fun z : A => z.1) h)
      have hns : ¬ Function.Surjective f := by
        intro hs
        apply hne
        apply Set.Subset.antisymm hTA
        intro z hz
        obtain ⟨t, ht⟩ := hs ⟨z, hz⟩
        have hv : t.1 = z := congrArg (fun q : A => q.1) ht
        exact hv ▸ t.2
      simpa only [Nat.card_eq_fintype_card] using
        Fintype.card_lt_of_injective_not_surjective f hf hns
    omega
  · obtain ⟨z, hz⟩ := hT
    have huniq : ∀ v ∈ T, v = z := by
      intro v hv
      by_contra hvz
      let f : Bool → T := fun b => if b then ⟨v, hv⟩ else ⟨z, hz⟩
      have hf : Function.Injective f := by
        intro p q hpq
        cases p <;> cases q <;> simp_all [f, Subtype.ext_iff]
      have hcard := Nat.card_le_card_of_injective f hf
      have hbool : Nat.card Bool = 2 := by rw [Nat.card_eq_fintype_card]; decide
      omega
    have hTsing : T = {z} := by
      ext v
      constructor
      · intro hv; exact huniq v hv
      · intro hv; exact (hv : v = z).symm ▸ hz
    rw [hTsing, boundary_singleton_card] at hc
    have hdeg3 : 3 ≤ G.degree z := hwfree ⟨z, hTA hz⟩
    omega

private theorem third_unique' {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {a b c x y : V}
    (ha : G.degree a = 3) (hab : G.Adj a b) (hac : G.Adj a c) (hbc : b ≠ c)
    (hax : G.Adj a x) (hay : G.Adj a y)
    (hxb : x ≠ b) (hxc : x ≠ c) (hyb : y ≠ b) (hyc : y ≠ c) : x = y := by
  classical
  by_contra hxy
  have hs : ({b, c, x, y} : Finset V) ⊆ G.neighborFinset a := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact (G.mem_neighborFinset a _).mpr hab
    · exact (G.mem_neighborFinset a _).mpr hac
    · exact (G.mem_neighborFinset a _).mpr hax
    · exact (G.mem_neighborFinset a _).mpr hay
  have hc := Finset.card_le_card hs
  have h4 : ({b, c, x, y} : Finset V).card = 4 := by
    simp [hbc, Ne.symm hxb, Ne.symm hxc, Ne.symm hyb, Ne.symm hyc, hxy]
  rw [h4, G.card_neighborFinset_eq_degree, ha] at hc
  omega

/-- Generalization of `minimal_side_ports_nonadjacent` from `Cubic G` to any `SideMinimal` side
    whose two boundary ports have degree 3 (covering all 6 `*-2` leaves). -/
theorem wfree_minimal_side_ports_nonadjacent {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Set V) (a b : A) (hab : a ≠ b) (ha3 : G.degree a.1 = 3) (hb3 : G.degree b.1 = 3)
    (x y : V) (hx : x ∉ A) (hy : y ∉ A) (hax : G.Adj a.1 x) (hby : G.Adj b.1 y)
    (hcut : ∀ z : A, ∀ t : V, t ∉ A → G.Adj z.1 t →
      (z = a ∧ t = x) ∨ (z = b ∧ t = y))
    (hmin : SideMinimal G A) : ¬ G.Adj a.1 b.1 := by
  classical
  intro hadj
  have habv : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
  let T : Set V := {z | z ∈ A ∧ z ≠ a.1 ∧ z ≠ b.1}
  have hTsub : T ⊆ A := fun z hz => hz.1
  have hTne : T.Nonempty := by
    by_contra hn
    have hs : G.neighborFinset a.1 ⊆ {b.1, x} := by
      intro z hz
      have haz := (G.mem_neighborFinset a.1 z).mp hz
      by_cases hzA : z ∈ A
      · by_cases hzb : z = b.1
        · simp [hzb]
        · have hza : z ≠ a.1 := (G.ne_of_adj haz).symm
          exact False.elim (hn ⟨z, hzA, hza, hzb⟩)
      · rcases hcut a z hzA haz with ⟨_, rfl⟩ | ⟨ha, _⟩
        · simp
        · exact False.elim (hab ha)
    have hc := Finset.card_le_card hs
    have hb_x : b.1 ≠ x := fun h => hx (h ▸ b.2)
    rw [G.card_neighborFinset_eq_degree, ha3] at hc
    have hp : ({b.1, x} : Finset V).card = 2 := by simp [hb_x]
    omega
  have hTproper : T ≠ A := by
    intro h
    have haT : a.1 ∈ T := h.symm ▸ a.2
    exact haT.2.1 rfl
  have hend (e : Boundary G T) : e.1.2 = a.1 ∨ e.1.2 = b.1 := by
    by_cases hEA : e.1.2 ∈ A
    · by_contra h
      push Not at h
      exact e.2.2.1 ⟨hEA, h.1, h.2⟩
    · rcases hcut ⟨e.1.1, e.2.1.1⟩ e.1.2 hEA e.2.2.2 with ⟨h, _⟩ | ⟨h, _⟩
      · exact False.elim (e.2.1.2.1 (congrArg Subtype.val h))
      · exact False.elim (e.2.1.2.2 (congrArg Subtype.val h))
  let f : Boundary G T → Bool := fun e => if e.1.2 = a.1 then true else false
  have hf : Function.Injective f := by
    intro p q hpq
    have hends : p.1.2 = q.1.2 := by
      rcases hend p with hp | hp <;> rcases hend q with hq | hq
      · exact hp.trans hq.symm
      · simp [f, hp, hq, habv.symm] at hpq
      · simp [f, hp, hq, habv.symm] at hpq
      · exact hp.trans hq.symm
    apply Subtype.ext
    apply Prod.ext
    · rcases hend p with hp | hp
      · have hq : q.1.2 = a.1 := hends.symm.trans hp
        apply third_unique' G ha3 hadj hax (fun h => hx (h ▸ b.2))
        · simpa [hp] using p.2.2.2.symm
        · simpa [hq] using q.2.2.2.symm
        · exact p.2.1.2.2
        · exact fun h => hx (h ▸ p.2.1.1)
        · exact q.2.1.2.2
        · exact fun h => hx (h ▸ q.2.1.1)
      · have hq : q.1.2 = b.1 := hends.symm.trans hp
        apply third_unique' G hb3 hadj.symm hby (fun h => hy (h ▸ a.2))
        · simpa [hp] using p.2.2.2.symm
        · simpa [hq] using q.2.2.2.symm
        · exact p.2.1.2.1
        · exact fun h => hy (h ▸ p.2.1.1)
        · exact q.2.1.2.1
        · exact fun h => hy (h ▸ q.2.1.1)
    · exact hends
  have hc := Nat.card_le_card_of_injective f hf
  have hb : Nat.card Bool = 2 := by rw [Nat.card_eq_fintype_card]; decide
  have hl := hmin T hTsub hTne hTproper
  omega

private theorem induce_degree_add_out' {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Set V) [DecidablePred (· ∈ A)]
    [DecidableRel (G.induce A).Adj] (v : A) :
    (G.induce A).degree v + ((G.neighborFinset v.1).filter (fun x => x ∉ A)).card =
      G.degree v.1 := by
  classical
  let e : G.neighborSet v.1 ≃
      (G.induce A).neighborSet v ⊕ {x : V // x ∈ (G.neighborFinset v.1).filter (fun x => x ∉ A)} :=
    { toFun := fun z =>
        if h : z.1 ∈ A then Sum.inl ⟨⟨z.1, h⟩, z.2⟩
        else Sum.inr ⟨z.1, Finset.mem_filter.mpr ⟨(G.mem_neighborFinset v.1 z.1).mpr z.2, h⟩⟩
      invFun := Sum.elim (fun z => ⟨z.1.1, z.2⟩)
        (fun z => ⟨z.1, (G.mem_neighborFinset v.1 z.1).mp (Finset.mem_filter.mp z.2).1⟩)
      left_inv := by intro z; by_cases h : z.1 ∈ A <;> simp [h]
      right_inv := by
        rintro (z | z)
        · simp [z.1.2]
        · have hn : z.1 ∉ A := (Finset.mem_filter.mp z.2).2
          simp [hn] }
  have hc := Fintype.card_congr e
  rw [SimpleGraph.card_neighborSet_eq_degree, Fintype.card_sum,
    SimpleGraph.card_neighborSet_eq_degree, Fintype.card_coe] at hc
  exact hc.symm

/-- Completion of a `w`-free minimal 2-cut side has minimum degree `≥ 3` (zero defect vertices!). -/
theorem completion_min_deg_three {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Set V) [DecidablePred (· ∈ A)] (hwfree : ∀ z : A, 3 ≤ G.degree z.1)
    (a b : A) (hab : a ≠ b) (x y : V)
    (hx : x ∉ A) (hy : y ∉ A) (hax : G.Adj a.1 x) (hby : G.Adj b.1 y)
    (hcut : ∀ z : A, ∀ t : V, t ∉ A → G.Adj z.1 t →
      (z = a ∧ t = x) ∨ (z = b ∧ t = y))
    (hnadj : ¬ G.Adj a.1 b.1) :
    ∀ v : A, 3 ≤ Nat.card ((Completion G A a b).neighborSet v) := by
  classical
  let K := G.induce A
  let H := Completion G A a b
  have hout_a : ((G.neighborFinset a.1).filter (fun z => z ∉ A)) = {x} := by
    ext z
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
    constructor
    · rintro ⟨haz, hz⟩
      rcases hcut a z hz haz with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · exact False.elim (hab h)
    · rintro rfl; exact ⟨hax, hx⟩
  have hout_b : ((G.neighborFinset b.1).filter (fun z => z ∉ A)) = {y} := by
    ext z
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
    constructor
    · rintro ⟨hbz, hz⟩
      rcases hcut b z hz hbz with ⟨h, _⟩ | ⟨_, h⟩
      · exact False.elim (hab h.symm)
      · exact h
    · rintro rfl; exact ⟨hby, hy⟩
  intro v
  by_cases hva : v = a
  · subst v
    have hd := induce_degree_add_out' G A a
    rw [hout_a, Finset.card_singleton] at hd
    have ha := degree_add_new_edge_left K a b hab hnadj
    have h3 := hwfree a
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at ha hd h3
    change 3 ≤ Nat.card (H.neighborSet a)
    rw [ha.trans hd]
    exact h3
  by_cases hvb : v = b
  · subst v
    have hd := induce_degree_add_out' G A b
    rw [hout_b, Finset.card_singleton] at hd
    have hb := degree_add_new_edge_right K a b hab hnadj
    have h3 := hwfree b
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hb hd h3
    change 3 ≤ Nat.card (H.neighborSet b)
    rw [hb.trans hd]
    exact h3
  have hout : ((G.neighborFinset v.1).filter (fun z => z ∉ A)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro z hz hn
    rcases hcut v z hn ((G.mem_neighborFinset v.1 z).mp hz) with ⟨h, _⟩ | ⟨h, _⟩
    · exact hva h
    · exact hvb h
  have hd := induce_degree_add_out' G A v
  rw [hout, Finset.card_empty, add_zero] at hd
  let e : H.neighborSet v ≃ K.neighborSet v :=
    { toFun := fun z => ⟨z.1, by
        rcases z.2 with h | h
        · exact h
        · rcases ((SimpleGraph.edge_adj a b v z.1).mp h).1 with ⟨hva', _⟩ | ⟨hvb', _⟩
          · exact False.elim (hva hva')
          · exact False.elim (hvb hvb')⟩
      invFun := fun z => ⟨z.1, Or.inl z.2⟩
      left_inv := by intro z; rfl
      right_inv := by intro z; rfl }
  have heq : Nat.card (H.neighborSet v) = Nat.card (K.neighborSet v) := Nat.card_congr e
  have h3 := hwfree v
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hd h3
  change 3 ≤ Nat.card (H.neighborSet v)
  rw [heq.trans hd]
  exact h3

/-- Deleting the virtual edge `ab` from `Completion G A a b` recovers `G.induce A`. -/
theorem completion_sdiff_edge {V : Type u} (G : SimpleGraph V) (A : Set V)
    (a b : A) (hnadj : ¬ G.Adj a.1 b.1) :
    Completion G A a b \ SimpleGraph.edge a b = G.induce A := by
  ext u v
  simp only [Completion, SimpleGraph.sdiff_adj, SimpleGraph.sup_adj, SimpleGraph.induce_adj]
  constructor
  · rintro ⟨h1 | h2, hnot⟩
    · exact h1
    · exact False.elim (hnot h2)
  · intro huv
    refine ⟨Or.inl huv, ?_⟩
    intro hedge
    rcases ((SimpleGraph.edge_adj a b u v).mp hedge).1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hnadj huv
    · exact hnadj huv.symm

/-- Universal `w`-Free Minimal 2-Cut Normal Form across ALL 6 `*-2` leaves
    (`C-T-2`, `C-N-2`, `S-T-2`, `S-N-2`, `H-T-2`, `H-N-2`). -/
theorem wfree_minimal_bad_two_cut_normal_form
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hm : MinimalBad G) (hcutG : SmallCut G 2) :
    ∃ (A : Set V) (a b : A),
      Nat.card A < Nat.card V ∧
      (Completion G A a b).Adj a b ∧
      (∀ z : A, 3 ≤ Nat.card ((Completion G A a b).neighborSet z)) ∧
      (∀ S : Set A, S.Nonempty → Sᶜ.Nonempty →
        3 ≤ Nat.card (Boundary (Completion G A a b) S)) ∧
      HasPower (Completion G A a b) ∧
      ¬ HasPower (Completion G A a b \ SimpleGraph.edge a b) := by
  classical
  obtain ⟨A, hA, hAc, hB, hwfree, hsm⟩ := select_wfree_minimal_two_cut G hm hcutG
  have hAne : A.Nonempty := by
    by_contra h
    have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    simp [he] at hA
  have hAcne : (Aᶜ : Set V).Nonempty := by
    by_contra h
    have he : (Aᶜ : Set V) = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    simp [he] at hAc
  have hlower : 2 ≤ Nat.card (Boundary G A) := by
    have hs : A.toFinset.Nonempty := by
      obtain ⟨z, hz⟩ := hAne; exact ⟨z, by simpa using hz⟩
    have hsc : (A.toFinset)ᶜ.Nonempty := by
      obtain ⟨z, hz⟩ := hAcne; exact ⟨z, by simpa using hz⟩
    have hh := E64Wave2Conn.minimal_bad_two_edge_connected G hm A.toFinset hs hsc
    simpa only [Boundary, Nat.card_eq_fintype_card, Fintype.card_subtype,
      Set.mem_toFinset] using hh
  have hcard : Nat.card (Boundary G A) = 2 := by omega
  have hU : (Finset.univ : Finset (Boundary G A)).card = 2 := by
    rw [Finset.card_univ]
    simpa only [Nat.card_eq_fintype_card] using hcard
  obtain ⟨p, q, _, hu⟩ := Finset.card_eq_two.mp hU
  let a : A := ⟨p.1.1, p.2.1⟩
  let b : A := ⟨q.1.1, q.2.1⟩
  let x := p.1.2
  let y := q.1.2
  have hx : x ∉ A := p.2.2.1
  have hy : y ∉ A := q.2.2.1
  have hax : G.Adj a.1 x := p.2.2.2
  have hby : G.Adj b.1 y := q.2.2.2
  have hcut : ∀ z : A, ∀ t : V, t ∉ A → G.Adj z.1 t →
      (z = a ∧ t = x) ∨ (z = b ∧ t = y) := by
    intro z t ht hzt
    let e : Boundary G A := ⟨(z.1, t), z.2, ht, hzt⟩
    have he : e = p ∨ e = q := by
      have hh : e ∈ (Finset.univ : Finset (Boundary G A)) := Finset.mem_univ e
      rw [hu] at hh
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hh
    rcases he with he | he
    · exact Or.inl ⟨Subtype.ext (congrArg (fun r : Boundary G A => r.1.1) he),
        congrArg (fun r : Boundary G A => r.1.2) he⟩
    · exact Or.inr ⟨Subtype.ext (congrArg (fun r : Boundary G A => r.1.1) he),
        congrArg (fun r : Boundary G A => r.1.2) he⟩
  have hA2 : 2 ≤ Fintype.card A := by simpa only [Nat.card_eq_fintype_card] using hA
  obtain ⟨hab, ha3, hb3⟩ :=
    E64CutBoundary.wfree_2cut_matching_and_cubic_boundary G hm A hA2 ⟨x, hx⟩ hwfree a b x y hcut
  have hnadj := wfree_minimal_side_ports_nonadjacent G A a b hab ha3 hb3 x y hx hy hax hby hcut hsm
  have hdeg3 := completion_min_deg_three G A hwfree a b hab x y hx hy hax hby hcut hnadj
  have hthree := minimal_side_completion_three_edge_connected G A a b hab x y hcut hnadj hsm
  have hsmall : Fintype.card A < Fintype.card V := by
    apply Fintype.card_lt_of_injective_not_surjective (fun z : A => z.1) Subtype.val_injective
    intro hs
    obtain ⟨z, hz⟩ := hs x
    exact hx (hz ▸ z.2)
  let H := Completion G A a b
  let _ : DecidableRel H.Adj := Classical.decRel _
  have hdeg3' : ∀ z : A, 3 ≤ H.degree z := by
    intro z
    have hz := hdeg3 z
    rwa [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree] at hz
  have hnear : Near H := ⟨⟨a, hdeg3' a⟩, ⟨a, fun z _ => hdeg3' z⟩⟩
  have hpower : HasPower H := hm.2.2.1 A H hsmall hnear
  have hfree : ¬ HasPower (H \ SimpleGraph.edge a b) := by
    rw [completion_sdiff_edge G A a b hnadj]
    exact fun hp => hm.2.1 (power_induce G A hp)
  have hadj_ab : H.Adj a b := Or.inr ((SimpleGraph.edge_adj a b a b).mpr ⟨Or.inl ⟨rfl, rfl⟩, hab⟩)
  exact ⟨A, a, b, by simpa only [Nat.card_eq_fintype_card] using hsmall,
    hadj_ab, hdeg3, hthree, hpower, hfree⟩

/-- Global Edge-Avoiding Power-Cycle Conjecture (`SEGC`): in every 3-edge-connected finite
    simple graph with `δ ≥ 3`, no single edge hits every power-of-2 cycle. -/
def EdgeAvoidingPower : Prop :=
  ∀ (V : Type u) (H : SimpleGraph V) [Fintype V],
    (∀ v : V, 3 ≤ Nat.card (H.neighborSet v)) →
    (∀ S : Set V, S.Nonempty → Sᶜ.Nonempty → 3 ≤ Nat.card (Boundary H S)) →
    ∀ a b : V, H.Adj a b → HasPower (H \ SimpleGraph.edge a b)

/-- `EdgeAvoidingPower` unconditionally excludes ANY `MinimalBad` graph with `SmallCut G 2`
    (all 6 `*-2` leaves simultaneously!). -/
theorem no_minimal_bad_small_cut_two_of_edge_avoiding (hEAP : EdgeAvoidingPower.{u})
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hm : MinimalBad G) (hcut : SmallCut G 2) : False := by
  classical
  obtain ⟨A, a, b, _, hadj, hdeg3, hthree, _, hfree⟩ :=
    wfree_minimal_bad_two_cut_normal_form G hm hcut
  exact hfree (hEAP A (Completion G A a b) hdeg3 hthree a b hadj)

/-- `EdgeAvoidingPower` also unconditionally excludes the core leaf `C-N-R` (`Leaf.cn .core`). -/
theorem exclude_cn_core_of_edge_avoiding (hEAP : EdgeAvoidingPower.{u}) :
    Exclude.{u} (.cn .core) := by
  classical
  intro V G _ _ hm hleaf
  obtain ⟨hC, _, _, hno2, _⟩ := hleaf
  have h3conn : ∀ S : Set V, S.Nonempty → Sᶜ.Nonempty → 3 ≤ Nat.card (Boundary G S) := by
    intro S hS hSc
    by_contra hn
    have hc : Nat.card (Boundary G S) ≤ 2 := by omega
    by_cases hS2 : 2 ≤ Nat.card S
    · by_cases hSc2 : 2 ≤ Nat.card (Sᶜ : Set V)
      · exact hno2 ⟨S, hS2, hSc2, hc⟩
      · obtain ⟨z, hz⟩ := hSc
        have huniq : ∀ v ∈ (Sᶜ : Set V), v = z := by
          intro v hv
          by_contra hvz
          let f : Bool → (Sᶜ : Set V) := fun b => if b then ⟨v, hv⟩ else ⟨z, hz⟩
          have hf : Function.Injective f := by
            intro p q hpq; cases p <;> cases q <;> simp_all [f, Subtype.ext_iff]
          have hcard := Nat.card_le_card_of_injective f hf
          have hbool : Nat.card Bool = 2 := by rw [Nat.card_eq_fintype_card]; decide
          omega
        have hScsing : (Sᶜ : Set V) = {z} := by
          ext v; constructor
          · intro hv; exact huniq v hv
          · intro hv; exact (hv : v = z).symm ▸ hz
        rw [← boundary_compl_card', hScsing, boundary_singleton_card, hC z] at hc
        omega
    · obtain ⟨z, hz⟩ := hS
      have huniq : ∀ v ∈ S, v = z := by
        intro v hv
        by_contra hvz
        let f : Bool → S := fun b => if b then ⟨v, hv⟩ else ⟨z, hz⟩
        have hf : Function.Injective f := by
          intro p q hpq; cases p <;> cases q <;> simp_all [f, Subtype.ext_iff]
        have hcard := Nat.card_le_card_of_injective f hf
        have hbool : Nat.card Bool = 2 := by rw [Nat.card_eq_fintype_card]; decide
        omega
      have hSsing : S = {z} := by
        ext v; constructor
        · intro hv; exact huniq v hv
        · intro hv; exact (hv : v = z).symm ▸ hz
      rw [hSsing, boundary_singleton_card, hC z] at hc
      omega
  obtain ⟨v, hv⟩ := hm.1.1
  have hvpos : 0 < G.degree v := by omega
  obtain ⟨u, hvu⟩ := (G.degree_pos_iff_exists_adj v).mp hvpos
  have hdeg3 : ∀ x : V, 3 ≤ Nat.card (G.neighborSet x) := by
    intro x
    rw [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree, hC x]
  have hp := hEAP V G hdeg3 h3conn v u hvu
  exact hm.2.1 (power_mono (show G \ SimpleGraph.edge v u ≤ G from fun _ _ h => h.1) hp)

/-- Predicate identifying the 6 remaining `*-3` leaves after `EdgeAvoidingPower` closes
    all 6 `*-2` leaves and `C-N-R` (7/13 open leaves closed at once). -/
def isLow3 : Leaf → Bool
  | .ct .low3 | .cn .low3 | .st .low3 | .sn .low3 | .ht .low3 | .hn .low3 => true
  | _ => false

/-- Whole-Problem Closure Gate #2: `EdgeAvoidingPower` + exclusion of the 6 `*-3` leaves
    closes the ENTIRE Erdős #64 conjecture (`Original`). -/
theorem original_of_edge_avoiding_and_low3
    (hEAP : EdgeAvoidingPower.{u})
    (hlow3 : ∀ l : Leaf, isLow3 l = true → Exclude.{u} l) :
    ∀ (V : Type u) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
      G.minDegree ≥ 3 → ∃ (k : ℕ) (v : V) (c : G.Walk v v),
        k ≥ 2 ∧ c.IsCycle ∧ c.length = 2 ^ k := by
  apply E64Remaining.original_of_remaining
  intro l hopen
  cases l with
  | cb => simp [E64Remaining.isClosed] at hopen
  | sb => simp [E64Remaining.isClosed] at hopen
  | ct s =>
    cases s with
    | low2 => exact fun V G _ _ hm hl => no_minimal_bad_small_cut_two_of_edge_avoiding hEAP G hm hl.2.2.2
    | low3 => exact hlow3 (.ct .low3) rfl
    | core => simp [E64Remaining.isClosed] at hopen
  | cn s =>
    cases s with
    | low2 => exact fun V G _ _ hm hl => no_minimal_bad_small_cut_two_of_edge_avoiding hEAP G hm hl.2.2.2
    | low3 => exact hlow3 (.cn .low3) rfl
    | core => exact exclude_cn_core_of_edge_avoiding hEAP
  | st s =>
    cases s with
    | low2 => exact fun V G _ _ hm hl => no_minimal_bad_small_cut_two_of_edge_avoiding hEAP G hm hl.2.2.2
    | low3 => exact hlow3 (.st .low3) rfl
    | core => simp [E64Remaining.isClosed] at hopen
  | sn s =>
    cases s with
    | low2 => exact fun V G _ _ hm hl => no_minimal_bad_small_cut_two_of_edge_avoiding hEAP G hm hl.2.2.2
    | low3 => exact hlow3 (.sn .low3) rfl
    | core => simp [E64Remaining.isClosed] at hopen
  | hb s => simp [E64Remaining.isClosed] at hopen
  | ht s =>
    cases s with
    | low2 => exact fun V G _ _ hm hl => no_minimal_bad_small_cut_two_of_edge_avoiding hEAP G hm hl.2.2.2
    | low3 => exact hlow3 (.ht .low3) rfl
    | core4 => simp [E64Remaining.isClosed] at hopen
    | core5 => simp [E64Remaining.isClosed] at hopen
  | hn s =>
    cases s with
    | low2 => exact fun V G _ _ hm hl => no_minimal_bad_small_cut_two_of_edge_avoiding hEAP G hm hl.2.2.2
    | low3 => exact hlow3 (.hn .low3) rfl
    | core4 => simp [E64Remaining.isClosed] at hopen
    | core5 => simp [E64Remaining.isClosed] at hopen

/-! ## Pillar 3: Universal Perfect-Matching Contraction (`C-N-R`, `C-N-2`, `C-N-3`) -/

/-- Equivalence relation identifying each vertex `v` with its matching partner `m v`. -/
def matchSetoid {V : Type u} (m : V → V) (hm_inv : ∀ v, m (m v) = v) : Setoid V where
  r u v := u = v ∨ v = m u
  iseqv :=
    { refl := fun _ => Or.inl rfl
      symm := by
        intro u v h
        rcases h with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (hm_inv u).symm
      trans := by
        intro u v w h1 h2
        rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact Or.inr rfl
        · exact Or.inl (hm_inv u).symm }

/-- Contraction of a perfect matching `m` in `G`. -/
def MContract {V : Type u} (G : SimpleGraph V) (m : V → V) (hm_inv : ∀ v, m (m v) = v) :
    SimpleGraph (Quotient (matchSetoid m hm_inv)) where
  Adj q1 q2 := q1 ≠ q2 ∧ ∃ u v : V,
    Quotient.mk (matchSetoid m hm_inv) u = q1 ∧
    Quotient.mk (matchSetoid m hm_inv) v = q2 ∧ G.Adj u v
  symm := ⟨fun _ _ h => ⟨h.1.symm, let ⟨u, v, hu, hv, hadj⟩ := h.2; ⟨v, u, hv, hu, hadj.symm⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Four distinct vertices forming a 4-cycle witness `HasPower G`. -/
private theorem hasPower_of_c4 {V : Type u} (G : SimpleGraph V) {a b c d : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) : HasPower G := by
  let w : G.Walk a a := .cons hab (.cons hbc (.cons hcd (.cons hda .nil)))
  have hcyc : w.IsCycle := by
    rw [Walk.isCycle_iff_isPath_tail_and_le_length]
    refine ⟨Walk.IsPath.mk' ?_, by simp [w]⟩
    have h1 : a ≠ b := G.ne_of_adj hab
    have h2 : b ≠ c := G.ne_of_adj hbc
    have h3 : c ≠ d := G.ne_of_adj hcd
    have h4 : d ≠ a := G.ne_of_adj hda
    simp [w, List.nodup_cons, h1.symm, h2, h3, h4, hac.symm, hbd]
  exact ⟨2, a, w, le_rfl, hcyc, by simp [w]⟩

/-- For ANY cubic, triangle-free `MinimalBad` graph `G` (`C-N-R`, `C-N-2`, `C-N-3`) and ANY
    perfect matching `m` (`∀ v, G.Adj v (m v)` and `m (m v) = v`), contracting `m` yields a
    strictly smaller **simple 4-regular** graph `MContract G m` that MUST contain a power cycle. -/
theorem matching_contraction_simple_4reg_power {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hm : MinimalBad G) (hC : Cubic G) (hNT : ¬ Triangle G)
    (m : V → V) (hm_adj : ∀ v, G.Adj v (m v)) (hm_inv : ∀ v, m (m v) = v) :
    let Q := Quotient (matchSetoid m hm_inv)
    let H := MContract G m hm_inv
    Nat.card Q < Nat.card V ∧ (∀ q : Q, Nat.card (H.neighborSet q) = 4) ∧ HasPower H := by
  classical
  let s := matchSetoid m hm_inv
  let Q := Quotient s
  let _ : Fintype Q := Quotient.fintype s
  let H := MContract G m hm_inv
  let _ : DecidableRel H.Adj := Classical.decRel _
  have hm_ne : ∀ v : V, m v ≠ v := fun v => (G.ne_of_adj (hm_adj v)).symm
  have hsmall : Fintype.card Q < Fintype.card V := by
    obtain ⟨v0, _⟩ := hm.1.1
    have hsurj : Function.Surjective (Quotient.mk s) := Quotient.mk_surjective
    have hnotinj : ¬ Function.Injective (Quotient.mk s) := by
      intro hinj
      have hq : Quotient.mk s v0 = Quotient.mk s (m v0) := Quotient.sound (Or.inr rfl)
      exact hm_ne v0 (hinj hq).symm
    by_contra hge
    have hle : Fintype.card V ≤ Fintype.card Q := Nat.le_of_not_lt hge
    have hle2 : Fintype.card Q ≤ Fintype.card V := Fintype.card_le_of_surjective _ hsurj
    have heq : Fintype.card V = Fintype.card Q := le_antisymm hle hle2
    exact hnotinj ((Fintype.bijective_iff_surjective_and_card _).mpr ⟨hsurj, heq⟩).1
  have hdeg4 : ∀ q : Q, H.degree q = 4 := by
    intro q
    induction q using Quotient.ind with
    | _ u =>
      let A1 := {x : V // G.Adj u x ∧ x ≠ m u}
      let A2 := {y : V // G.Adj (m u) y ∧ y ≠ u}
      let φ : A1 ⊕ A2 → H.neighborSet (Quotient.mk s u) :=
        Sum.elim
          (fun x => ⟨Quotient.mk s x.1, by
            refine ⟨?_, u, x.1, rfl, rfl, x.2.1⟩
            intro heq
            rcases Quotient.exact heq with h1 | h2
            · exact G.ne_of_adj x.2.1 h1
            · exact x.2.2 h2⟩)
          (fun y => ⟨Quotient.mk s y.1, by
            refine ⟨?_, m u, y.1, (Quotient.sound (Or.inr rfl)).symm, rfl, y.2.1⟩
            intro heq
            rcases Quotient.exact heq with h1 | h2
            · exact y.2.2 h1.symm
            · exact G.ne_of_adj y.2.1 h2.symm⟩)
      have hφ_bij : Function.Bijective φ := by
        constructor
        · intro p1 p2 hp
          have hq : (φ p1).1 = (φ p2).1 := congrArg Subtype.val hp
          rcases p1 with x1 | y1 <;> rcases p2 with x2 | y2
          · rcases Quotient.exact hq with h1 | h2
            · exact congrArg Sum.inl (Subtype.ext h1)
            · exact False.elim (hNT ⟨u, x1.1, x2.1, x1.2.1, h2 ▸ hm_adj x1.1, x2.2.1.symm⟩)
          · rcases Quotient.exact hq with h1 | h2
            · exact False.elim (hNT ⟨u, m u, x1.1, hm_adj u, h1 ▸ y2.2.1, x1.2.1.symm⟩)
            · have hu_y2 : u ≠ y2.1 := y2.2.2.symm
              have hmu_x1 : m u ≠ x1.1 := x1.2.2.symm
              have hy2_x1 : G.Adj y2.1 x1.1 := by rw [h2]; exact (hm_adj x1.1).symm
              exact False.elim (hm.2.1 (hasPower_of_c4 G (hm_adj u) y2.2.1 hy2_x1 x1.2.1.symm hu_y2 hmu_x1))
          · rcases Quotient.exact hq with h1 | h2
            · exact False.elim (hNT ⟨u, m u, y1.1, hm_adj u, y1.2.1, h1 ▸ x2.2.1.symm⟩)
            · have hu_y1 : u ≠ y1.1 := y1.2.2.symm
              have hmu_x2 : m u ≠ x2.1 := x2.2.2.symm
              have hx2_y1 : G.Adj x2.1 y1.1 := by rw [h2]; exact (hm_adj y1.1).symm
              exact False.elim (hm.2.1 (hasPower_of_c4 G (hm_adj u) y1.2.1 hx2_y1.symm x2.2.1.symm hu_y1 hmu_x2))
          · rcases Quotient.exact hq with h1 | h2
            · exact congrArg Sum.inr (Subtype.ext h1)
            · exact False.elim (hNT ⟨m u, y1.1, y2.1, y1.2.1, h2 ▸ hm_adj y1.1, y2.2.1.symm⟩)
        · rintro ⟨q', hne, a, b, ha, hb, hab⟩
          rcases Quotient.exact ha with rfl | hma
          · have hb_ne : b ≠ m a := by
              intro hbm
              apply hne
              rw [← hb, hbm]
              exact Quotient.sound (Or.inr rfl)
            exact ⟨Sum.inl ⟨b, hab, hb_ne⟩, Subtype.ext hb⟩
          · have hma' : a = m u := by
              have := congrArg m hma
              rw [hm_inv] at this
              exact this.symm
            subst hma'
            have hb_ne : b ≠ u := by
              intro hbu
              apply hne
              rw [← hb, hbu]
            exact ⟨Sum.inr ⟨b, hab, hb_ne⟩, Subtype.ext hb⟩
      have hcard_eq : Fintype.card (A1 ⊕ A2) = Fintype.card (H.neighborSet (Quotient.mk s u)) :=
        Fintype.card_congr (Equiv.ofBijective φ hφ_bij)
      have hA1 : Fintype.card A1 = 2 := by
        have h1 : Fintype.card A1 = ((G.neighborFinset u).erase (m u)).card := by
          refine (Fintype.card_congr (Equiv.ofBijective (fun x : A1 =>
            (⟨x.1, Finset.mem_erase.mpr ⟨x.2.2, (G.mem_neighborFinset u x.1).mpr x.2.1⟩⟩ :
              {z // z ∈ (G.neighborFinset u).erase (m u)})) ?_)).trans (Fintype.card_coe _)
          constructor
          · intro x y h; exact Subtype.ext (by simpa [Subtype.ext_iff] using h)
          · rintro ⟨z, hz⟩
            have hmem := Finset.mem_erase.mp hz
            exact ⟨⟨z, (G.mem_neighborFinset u z).mp hmem.2, hmem.1⟩, rfl⟩
        rw [h1, Finset.card_erase_of_mem ((G.mem_neighborFinset u (m u)).mpr (hm_adj u)),
          SimpleGraph.card_neighborFinset_eq_degree, hC u]
      have hA2 : Fintype.card A2 = 2 := by
        have h2 : Fintype.card A2 = ((G.neighborFinset (m u)).erase u).card := by
          refine (Fintype.card_congr (Equiv.ofBijective (fun y : A2 =>
            (⟨y.1, Finset.mem_erase.mpr ⟨y.2.2, (G.mem_neighborFinset (m u) y.1).mpr y.2.1⟩⟩ :
              {z // z ∈ (G.neighborFinset (m u)).erase u})) ?_)).trans (Fintype.card_coe _)
          constructor
          · intro x y h; exact Subtype.ext (by simpa [Subtype.ext_iff] using h)
          · rintro ⟨z, hz⟩
            have hmem := Finset.mem_erase.mp hz
            exact ⟨⟨z, (G.mem_neighborFinset (m u) z).mp hmem.2, hmem.1⟩, rfl⟩
        rw [h2, Finset.card_erase_of_mem ((G.mem_neighborFinset (m u) u).mpr (hm_adj u).symm),
          SimpleGraph.card_neighborFinset_eq_degree, hC (m u)]
      rw [SimpleGraph.card_neighborSet_eq_degree] at hcard_eq
      rw [Fintype.card_sum, hA1, hA2] at hcard_eq
      omega
  obtain ⟨v0, _⟩ := hm.1.1
  have hnear : Near H :=
    ⟨⟨Quotient.mk s v0, by rw [hdeg4]; omega⟩,
     ⟨Quotient.mk s v0, fun q _ => by rw [hdeg4]; omega⟩⟩
  refine ⟨by simpa only [Nat.card_eq_fintype_card] using hsmall, fun q => ?_, hm.2.2.1 Q H hsmall hnear⟩
  rw [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree, hdeg4 q]

#print axioms minimal_bad_not_bip
#print axioms bipDeg_add_frustDeg
#print axioms exists_max_cut
#print axioms max_cut_frustDeg_le_bipDeg
#print axioms minimal_bad_max_cut_frustrated_matching
#print axioms original_of_max_cut_bipartite_power
#print axioms select_wfree_minimal_two_cut
#print axioms wfree_minimal_side_ports_nonadjacent
#print axioms completion_min_deg_three
#print axioms completion_sdiff_edge
#print axioms wfree_minimal_bad_two_cut_normal_form
#print axioms no_minimal_bad_small_cut_two_of_edge_avoiding
#print axioms exclude_cn_core_of_edge_avoiding
#print axioms original_of_edge_avoiding_and_low3
#print axioms matching_contraction_simple_4reg_power

end E64Wave4Agent6
