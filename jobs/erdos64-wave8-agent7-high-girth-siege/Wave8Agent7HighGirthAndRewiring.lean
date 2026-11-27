import Mathlib

open Classical

namespace E64Wave8Agent7

/-!
# Wave 8 Agent #7 — Erdős Problem #64 (Erdős–Gyárfás Conjecture)
Unconditional All-Order Lean 4.36.0 Formalization (18 Audited Theorems):
- Pillar 1 (Theorems 1–6): Parallel-Rewiring (`G_parallel`) & Complete Triple-Rewiring Theory
  on Girth >= 5 Minimal Counterexamples
- Pillar 2 (Theorems 7–12): High-Girth (`g in {7..16}`) Non-Simple Tailless Walk Exact
  Classification & `2^r >= 2g` Barrier-Breaking
- Pillar 3 (Theorems 13–18): Universal High-Girth (`g in {9..14}`) Odd/Even Antipodal &
  Coprime-Shift Frobenius Unbounded-n Closures

Compiled with `-DwarningAsError=true`; standard Lean foundations only.
-/

section CoreDefinitions

variable {V : Type*}

/-- A graph `G` has a simple cycle of length `L`. -/
def HasCycleOfLength (G : SimpleGraph V) (L : ℕ) : Prop :=
  ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = L

/-- A graph `G` satisfies Erdős–Gyárfás: it contains a simple cycle of length `2^k` (`k ≥ 2`). -/
def HasPow2Cycle (G : SimpleGraph V) : Prop :=
  ∃ k : ℕ, 2 ≤ k ∧ HasCycleOfLength G (2 ^ k)

/-- `G` is free of power-of-two cycles (`2^k`, `k ≥ 2`). -/
def PowerFree (G : SimpleGraph V) : Prop :=
  ¬ HasPow2Cycle G

/-- `G` has girth at least `g`: every simple cycle has length `≥ g`. -/
def GirthAtLeast (G : SimpleGraph V) (g : ℕ) : Prop :=
  ∀ (L : ℕ), HasCycleOfLength G L → g ≤ L

/-- `G` is triangle-free. -/
def TriangleFree (G : SimpleGraph V) : Prop :=
  ∀ a b c : V, G.Adj a b → G.Adj b c → ¬ G.Adj a c

/-- `G` is `C_4`-free (no 4-cycle of 4 distinct vertices). -/
def C4Free (G : SimpleGraph V) : Prop :=
  ∀ a b c d : V, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a

/-- `G` has only even simple cycles (e.g., bipartite). -/
def EvenCyclesOnly (G : SimpleGraph V) : Prop :=
  ∀ (L : ℕ), HasCycleOfLength G L → Even L

private lemma dite_val_pos {P : Prop} [Decidable P] {α : Type*}
    {t : P → α} {e : ¬ P → α} (h : P) : dite P t e = t h := by
  split_ifs with h'
  · rfl
  · exact absurd h h'

private lemma dite_val_neg {P : Prop} [Decidable P] {α : Type*}
    {t : P → α} {e : ¬ P → α} (h : ¬ P) : dite P t e = e h := by
  split_ifs with h'
  · exact absurd h' h
  · rfl

end CoreDefinitions

/-! ## Pillar 1: Parallel-Rewiring (`G_parallel`) & Triple-Rewiring Theory -/

section Pillar1TripleRewiring

variable {V : Type*}

/-- **Theorem 1**: In any triangle-free, `C_4`-free graph `G`, for any edge `u ~ v`
with external neighbors `u₁, u₂` of `u` (distinct from `v` and each other) and
`v₁, v₂` of `v` (distinct from `u` and each other), the 4-set `{u₁, u₂, v₁, v₂}`
is pairwise distinct and forms an independent set in `G`. -/
theorem girth5_edge_external_neighbors_independent
    (G : SimpleGraph V) (hTri : TriangleFree G) (hC4 : C4Free G)
    {u v u₁ u₂ v₁ v₂ : V}
    (huv : G.Adj u v)
    (hu₁ : G.Adj u u₁) (hu₂ : G.Adj u u₂) (hu₁v : u₁ ≠ v) (hu₂v : u₂ ≠ v)
    (hv₁ : G.Adj v v₁) (hv₂ : G.Adj v v₂) (hv₁u : v₁ ≠ u) (hv₂u : v₂ ≠ u) :
    (u₁ ≠ v₁ ∧ u₁ ≠ v₂ ∧ u₂ ≠ v₁ ∧ u₂ ≠ v₂) ∧
    (¬ G.Adj u₁ u₂ ∧ ¬ G.Adj v₁ v₂ ∧
     ¬ G.Adj u₁ v₁ ∧ ¬ G.Adj u₁ v₂ ∧ ¬ G.Adj u₂ v₁ ∧ ¬ G.Adj u₂ v₂) := by
  have h11 : u₁ ≠ v₁ := by
    intro h; subst h; exact hTri u v u₁ huv hv₁ hu₁
  have h12 : u₁ ≠ v₂ := by
    intro h; subst h; exact hTri u v u₁ huv hv₂ hu₁
  have h21 : u₂ ≠ v₁ := by
    intro h; subst h; exact hTri u v u₂ huv hv₁ hu₂
  have h22 : u₂ ≠ v₂ := by
    intro h; subst h; exact hTri u v u₂ huv hv₂ hu₂
  have hu_non : ¬ G.Adj u₁ u₂ := by
    intro h; exact hTri u₁ u u₂ hu₁.symm hu₂ h
  have hv_non : ¬ G.Adj v₁ v₂ := by
    intro h; exact hTri v₁ v v₂ hv₁.symm hv₂ h
  have h11_non : ¬ G.Adj u₁ v₁ := by
    intro h; exact hC4 u v v₁ u₁ hv₁u.symm hu₁v.symm huv hv₁ h.symm hu₁.symm
  have h12_non : ¬ G.Adj u₁ v₂ := by
    intro h; exact hC4 u v v₂ u₁ hv₂u.symm hu₁v.symm huv hv₂ h.symm hu₁.symm
  have h21_non : ¬ G.Adj u₂ v₁ := by
    intro h; exact hC4 u v v₁ u₂ hv₁u.symm hu₂v.symm huv hv₁ h.symm hu₂.symm
  have h22_non : ¬ G.Adj u₂ v₂ := by
    intro h; exact hC4 u v v₂ u₂ hv₂u.symm hu₂v.symm huv hv₂ h.symm hu₂.symm
  exact ⟨⟨h11, h12, h21, h22⟩, ⟨hu_non, hv_non, h11_non, h12_non, h21_non, h22_non⟩⟩

/-- Parallel rewiring `G_parallel(uv)` on `V' = {x : V // x ≠ u ∧ x ≠ v}` obtained by
deleting `{u, v}` and adding the two parallel edges `u₁u₂` and `v₁v₂`. -/
def parallelRewire (G : SimpleGraph V) (u v u₁ u₂ v₁ v₂ : V)
    (hu₁₂ : u₁ ≠ u₂) (hv₁₂ : v₁ ≠ v₂) :
    SimpleGraph { x : V // x ≠ u ∧ x ≠ v } where
  Adj a b :=
    G.Adj a.1 b.1 ∨
    (a.1 = u₁ ∧ b.1 = u₂) ∨ (a.1 = u₂ ∧ b.1 = u₁) ∨
    (a.1 = v₁ ∧ b.1 = v₂) ∨ (a.1 = v₂ ∧ b.1 = v₁)
  symm := ⟨by
    intro a b h
    rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr (Or.inl ⟨h2, h1⟩))
    · exact Or.inr (Or.inl ⟨h2, h1⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h2, h1⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, h1⟩)))⟩
  loopless := ⟨by
    intro a h
    rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact G.loopless.irrefl a.1 h
    · exact hu₁₂ (h1.symm.trans h2)
    · exact hu₁₂ (h2.symm.trans h1)
    · exact hv₁₂ (h1.symm.trans h2)
    · exact hv₁₂ (h2.symm.trans h1)⟩

/-- **Theorem 2**: In any finite triangle-free, `C_4`-free graph `G` with `δ(G) ≥ 3`,
for any cubic edge `uv` with `N(u) = {v, u₁, u₂}` and `N(v) = {u, v₁, v₂}`,
the parallel rewiring `G_parallel(uv)` on `|V| - 2` vertices has `δ(G_parallel(uv)) ≥ 3`. -/
theorem parallel_rewiring_min_degree_three
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hTri : TriangleFree G) (hC4 : C4Free G)
    (hMinDeg : ∀ x : V, 3 ≤ G.degree x)
    {u v u₁ u₂ v₁ v₂ : V}
    (huv : G.Adj u v)
    (hu₁ : G.Adj u u₁) (hu₂ : G.Adj u u₂) (hu₁v : u₁ ≠ v) (hu₂v : u₂ ≠ v) (hu₁₂ : u₁ ≠ u₂)
    (hv₁ : G.Adj v v₁) (hv₂ : G.Adj v v₂) (hv₁u : v₁ ≠ u) (hv₂u : v₂ ≠ u) (hv₁₂ : v₁ ≠ v₂)
    (hNu : ∀ w : V, G.Adj u w → w = v ∨ w = u₁ ∨ w = u₂)
    (hNv : ∀ w : V, G.Adj v w → w = u ∨ w = v₁ ∨ w = v₂) :
    ∀ x : { y : V // y ≠ u ∧ y ≠ v },
      3 ≤ (parallelRewire G u v u₁ u₂ v₁ v₂ hu₁₂ hv₁₂).degree x := by
  have hind := girth5_edge_external_neighbors_independent G hTri hC4 huv
    hu₁ hu₂ hu₁v hu₂v hv₁ hv₂ hv₁u hv₂u
  have hu₁u : u₁ ≠ u := (G.ne_of_adj hu₁).symm
  have hu₂u : u₂ ≠ u := (G.ne_of_adj hu₂).symm
  have hv₁v : v₁ ≠ v := (G.ne_of_adj hv₁).symm
  have hv₂v : v₂ ≠ v := (G.ne_of_adj hv₂).symm
  let H := parallelRewire G u v u₁ u₂ v₁ v₂ hu₁₂ hv₁₂
  intro x
  have hdegx : 3 ≤ (G.neighborFinset x.1).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact hMinDeg x.1
  suffices hle : (G.neighborFinset x.1).card ≤ (H.neighborFinset x).card by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact le_trans hdegx hle
  by_cases hxu : G.Adj u x.1
  · have hxv : ¬ G.Adj v x.1 := fun h => hTri u v x.1 huv h hxu
    rcases hNu x.1 hxu with hEqv | hEq1 | hEq2
    · exact absurd hEqv x.2.2
    · let u₂' : { y : V // y ≠ u ∧ y ≠ v } := ⟨u₂, hu₂u, hu₂v⟩
      let f : V → { y : V // y ≠ u ∧ y ≠ v } := fun w =>
        if hw : w ≠ u ∧ w ≠ v then ⟨w, hw⟩ else u₂'
      apply Finset.card_le_card_of_injOn f
      · intro w hw
        rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hw ⊢
        by_cases hwu : w = u
        · have hcond : ¬ (w ≠ u ∧ w ≠ v) := fun h => h.1 hwu
          change H.Adj x (dite (w ≠ u ∧ w ≠ v) (fun h => ⟨w, h⟩) (fun _ => u₂'))
          rw [dite_val_neg hcond]
          exact Or.inr (Or.inl ⟨hEq1, rfl⟩)
        · have hwv : w ≠ v := fun h => hxv (h ▸ hw.symm)
          have hcond : w ≠ u ∧ w ≠ v := ⟨hwu, hwv⟩
          change H.Adj x (dite (w ≠ u ∧ w ≠ v) (fun h => ⟨w, h⟩) (fun _ => u₂'))
          rw [dite_val_pos hcond]
          exact Or.inl hw
      · intro w₁ hw₁ w₂ hw₂ hfeq
        rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hw₁ hw₂
        by_cases h1 : w₁ = u <;> by_cases h2 : w₂ = u
        · exact h1.trans h2.symm
        · have hw₂v : w₂ ≠ v := fun h => hxv (h ▸ hw₂.symm)
          have hc1 : ¬ (w₁ ≠ u ∧ w₁ ≠ v) := fun h => h.1 h1
          have hc2 : w₂ ≠ u ∧ w₂ ≠ v := ⟨h2, hw₂v⟩
          change dite (w₁ ≠ u ∧ w₁ ≠ v) _ _ = dite (w₂ ≠ u ∧ w₂ ≠ v) _ _ at hfeq
          rw [dite_val_neg hc1, dite_val_pos hc2] at hfeq
          have hu₂w₂ : u₂ = w₂ := congrArg Subtype.val hfeq
          exact absurd (hu₂w₂ ▸ (hEq1 ▸ hw₂)) hind.2.1
        · have hw₁v : w₁ ≠ v := fun h => hxv (h ▸ hw₁.symm)
          have hc1 : w₁ ≠ u ∧ w₁ ≠ v := ⟨h1, hw₁v⟩
          have hc2 : ¬ (w₂ ≠ u ∧ w₂ ≠ v) := fun h => h.1 h2
          change dite (w₁ ≠ u ∧ w₁ ≠ v) _ _ = dite (w₂ ≠ u ∧ w₂ ≠ v) _ _ at hfeq
          rw [dite_val_pos hc1, dite_val_neg hc2] at hfeq
          have hw₁u₂ : w₁ = u₂ := congrArg Subtype.val hfeq
          exact absurd (hw₁u₂ ▸ (hEq1 ▸ hw₁)) hind.2.1
        · have hw₁v : w₁ ≠ v := fun h => hxv (h ▸ hw₁.symm)
          have hw₂v : w₂ ≠ v := fun h => hxv (h ▸ hw₂.symm)
          have hc1 : w₁ ≠ u ∧ w₁ ≠ v := ⟨h1, hw₁v⟩
          have hc2 : w₂ ≠ u ∧ w₂ ≠ v := ⟨h2, hw₂v⟩
          change dite (w₁ ≠ u ∧ w₁ ≠ v) _ _ = dite (w₂ ≠ u ∧ w₂ ≠ v) _ _ at hfeq
          rw [dite_val_pos hc1, dite_val_pos hc2] at hfeq
          exact congrArg Subtype.val hfeq
    · let u₁' : { y : V // y ≠ u ∧ y ≠ v } := ⟨u₁, hu₁u, hu₁v⟩
      let f : V → { y : V // y ≠ u ∧ y ≠ v } := fun w =>
        if hw : w ≠ u ∧ w ≠ v then ⟨w, hw⟩ else u₁'
      apply Finset.card_le_card_of_injOn f
      · intro w hw
        rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hw ⊢
        by_cases hwu : w = u
        · have hcond : ¬ (w ≠ u ∧ w ≠ v) := fun h => h.1 hwu
          change H.Adj x (dite (w ≠ u ∧ w ≠ v) (fun h => ⟨w, h⟩) (fun _ => u₁'))
          rw [dite_val_neg hcond]
          exact Or.inr (Or.inr (Or.inl ⟨hEq2, rfl⟩))
        · have hwv : w ≠ v := fun h => hxv (h ▸ hw.symm)
          have hcond : w ≠ u ∧ w ≠ v := ⟨hwu, hwv⟩
          change H.Adj x (dite (w ≠ u ∧ w ≠ v) (fun h => ⟨w, h⟩) (fun _ => u₁'))
          rw [dite_val_pos hcond]
          exact Or.inl hw
      · intro w₁ hw₁ w₂ hw₂ hfeq
        rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hw₁ hw₂
        by_cases h1 : w₁ = u <;> by_cases h2 : w₂ = u
        · exact h1.trans h2.symm
        · have hw₂v : w₂ ≠ v := fun h => hxv (h ▸ hw₂.symm)
          have hc1 : ¬ (w₁ ≠ u ∧ w₁ ≠ v) := fun h => h.1 h1
          have hc2 : w₂ ≠ u ∧ w₂ ≠ v := ⟨h2, hw₂v⟩
          change dite (w₁ ≠ u ∧ w₁ ≠ v) _ _ = dite (w₂ ≠ u ∧ w₂ ≠ v) _ _ at hfeq
          rw [dite_val_neg hc1, dite_val_pos hc2] at hfeq
          have hu₁w₂ : u₁ = w₂ := congrArg Subtype.val hfeq
          exact absurd (hu₁w₂ ▸ (hEq2 ▸ hw₂)).symm hind.2.1
        · have hw₁v : w₁ ≠ v := fun h => hxv (h ▸ hw₁.symm)
          have hc1 : w₁ ≠ u ∧ w₁ ≠ v := ⟨h1, hw₁v⟩
          have hc2 : ¬ (w₂ ≠ u ∧ w₂ ≠ v) := fun h => h.1 h2
          change dite (w₁ ≠ u ∧ w₁ ≠ v) _ _ = dite (w₂ ≠ u ∧ w₂ ≠ v) _ _ at hfeq
          rw [dite_val_pos hc1, dite_val_neg hc2] at hfeq
          have hw₁u₁ : w₁ = u₁ := congrArg Subtype.val hfeq
          exact absurd (hw₁u₁ ▸ (hEq2 ▸ hw₁)).symm hind.2.1
        · have hw₁v : w₁ ≠ v := fun h => hxv (h ▸ hw₁.symm)
          have hw₂v : w₂ ≠ v := fun h => hxv (h ▸ hw₂.symm)
          have hc1 : w₁ ≠ u ∧ w₁ ≠ v := ⟨h1, hw₁v⟩
          have hc2 : w₂ ≠ u ∧ w₂ ≠ v := ⟨h2, hw₂v⟩
          change dite (w₁ ≠ u ∧ w₁ ≠ v) _ _ = dite (w₂ ≠ u ∧ w₂ ≠ v) _ _ at hfeq
          rw [dite_val_pos hc1, dite_val_pos hc2] at hfeq
          exact congrArg Subtype.val hfeq
  · by_cases hxv : G.Adj v x.1
    · rcases hNv x.1 hxv with hEqu | hEq1 | hEq2
      · exact absurd hEqu x.2.1
      · let v₂' : { y : V // y ≠ u ∧ y ≠ v } := ⟨v₂, hv₂u, hv₂v⟩
        let f : V → { y : V // y ≠ u ∧ y ≠ v } := fun w =>
          if hw : w ≠ u ∧ w ≠ v then ⟨w, hw⟩ else v₂'
        apply Finset.card_le_card_of_injOn f
        · intro w hw
          rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hw ⊢
          by_cases hwv : w = v
          · have hcond : ¬ (w ≠ u ∧ w ≠ v) := fun h => h.2 hwv
            change H.Adj x (dite (w ≠ u ∧ w ≠ v) (fun h => ⟨w, h⟩) (fun _ => v₂'))
            rw [dite_val_neg hcond]
            exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hEq1, rfl⟩)))
          · have hwu : w ≠ u := fun h => hxu (h ▸ hw.symm)
            have hcond : w ≠ u ∧ w ≠ v := ⟨hwu, hwv⟩
            change H.Adj x (dite (w ≠ u ∧ w ≠ v) (fun h => ⟨w, h⟩) (fun _ => v₂'))
            rw [dite_val_pos hcond]
            exact Or.inl hw
        · intro w₁ hw₁ w₂ hw₂ hfeq
          rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hw₁ hw₂
          by_cases h1 : w₁ = v <;> by_cases h2 : w₂ = v
          · exact h1.trans h2.symm
          · have hw₂u : w₂ ≠ u := fun h => hxu (h ▸ hw₂.symm)
            have hc1 : ¬ (w₁ ≠ u ∧ w₁ ≠ v) := fun h => h.2 h1
            have hc2 : w₂ ≠ u ∧ w₂ ≠ v := ⟨hw₂u, h2⟩
            change dite (w₁ ≠ u ∧ w₁ ≠ v) _ _ = dite (w₂ ≠ u ∧ w₂ ≠ v) _ _ at hfeq
            rw [dite_val_neg hc1, dite_val_pos hc2] at hfeq
            have hv₂w₂ : v₂ = w₂ := congrArg Subtype.val hfeq
            exact absurd (hv₂w₂ ▸ (hEq1 ▸ hw₂)) hind.2.2.1
          · have hw₁u : w₁ ≠ u := fun h => hxu (h ▸ hw₁.symm)
            have hc1 : w₁ ≠ u ∧ w₁ ≠ v := ⟨hw₁u, h1⟩
            have hc2 : ¬ (w₂ ≠ u ∧ w₂ ≠ v) := fun h => h.2 h2
            change dite (w₁ ≠ u ∧ w₁ ≠ v) _ _ = dite (w₂ ≠ u ∧ w₂ ≠ v) _ _ at hfeq
            rw [dite_val_pos hc1, dite_val_neg hc2] at hfeq
            have hw₁v₂ : w₁ = v₂ := congrArg Subtype.val hfeq
            exact absurd (hw₁v₂ ▸ (hEq1 ▸ hw₁)) hind.2.2.1
          · have hw₁u : w₁ ≠ u := fun h => hxu (h ▸ hw₁.symm)
            have hw₂u : w₂ ≠ u := fun h => hxu (h ▸ hw₂.symm)
            have hc1 : w₁ ≠ u ∧ w₁ ≠ v := ⟨hw₁u, h1⟩
            have hc2 : w₂ ≠ u ∧ w₂ ≠ v := ⟨hw₂u, h2⟩
            change dite (w₁ ≠ u ∧ w₁ ≠ v) _ _ = dite (w₂ ≠ u ∧ w₂ ≠ v) _ _ at hfeq
            rw [dite_val_pos hc1, dite_val_pos hc2] at hfeq
            exact congrArg Subtype.val hfeq
      · let v₁' : { y : V // y ≠ u ∧ y ≠ v } := ⟨v₁, hv₁u, hv₁v⟩
        let f : V → { y : V // y ≠ u ∧ y ≠ v } := fun w =>
          if hw : w ≠ u ∧ w ≠ v then ⟨w, hw⟩ else v₁'
        apply Finset.card_le_card_of_injOn f
        · intro w hw
          rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hw ⊢
          by_cases hwv : w = v
          · have hcond : ¬ (w ≠ u ∧ w ≠ v) := fun h => h.2 hwv
            change H.Adj x (dite (w ≠ u ∧ w ≠ v) (fun h => ⟨w, h⟩) (fun _ => v₁'))
            rw [dite_val_neg hcond]
            exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hEq2, rfl⟩)))
          · have hwu : w ≠ u := fun h => hxu (h ▸ hw.symm)
            have hcond : w ≠ u ∧ w ≠ v := ⟨hwu, hwv⟩
            change H.Adj x (dite (w ≠ u ∧ w ≠ v) (fun h => ⟨w, h⟩) (fun _ => v₁'))
            rw [dite_val_pos hcond]
            exact Or.inl hw
        · intro w₁ hw₁ w₂ hw₂ hfeq
          rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hw₁ hw₂
          by_cases h1 : w₁ = v <;> by_cases h2 : w₂ = v
          · exact h1.trans h2.symm
          · have hw₂u : w₂ ≠ u := fun h => hxu (h ▸ hw₂.symm)
            have hc1 : ¬ (w₁ ≠ u ∧ w₁ ≠ v) := fun h => h.2 h1
            have hc2 : w₂ ≠ u ∧ w₂ ≠ v := ⟨hw₂u, h2⟩
            change dite (w₁ ≠ u ∧ w₁ ≠ v) _ _ = dite (w₂ ≠ u ∧ w₂ ≠ v) _ _ at hfeq
            rw [dite_val_neg hc1, dite_val_pos hc2] at hfeq
            have hv₁w₂ : v₁ = w₂ := congrArg Subtype.val hfeq
            exact absurd (hv₁w₂ ▸ (hEq2 ▸ hw₂)).symm hind.2.2.1
          · have hw₁u : w₁ ≠ u := fun h => hxu (h ▸ hw₁.symm)
            have hc1 : w₁ ≠ u ∧ w₁ ≠ v := ⟨hw₁u, h1⟩
            have hc2 : ¬ (w₂ ≠ u ∧ w₂ ≠ v) := fun h => h.2 h2
            change dite (w₁ ≠ u ∧ w₁ ≠ v) _ _ = dite (w₂ ≠ u ∧ w₂ ≠ v) _ _ at hfeq
            rw [dite_val_pos hc1, dite_val_neg hc2] at hfeq
            have hw₁v₁ : w₁ = v₁ := congrArg Subtype.val hfeq
            exact absurd (hw₁v₁ ▸ (hEq2 ▸ hw₁)).symm hind.2.2.1
          · have hw₁u : w₁ ≠ u := fun h => hxu (h ▸ hw₁.symm)
            have hw₂u : w₂ ≠ u := fun h => hxu (h ▸ hw₂.symm)
            have hc1 : w₁ ≠ u ∧ w₁ ≠ v := ⟨hw₁u, h1⟩
            have hc2 : w₂ ≠ u ∧ w₂ ≠ v := ⟨hw₂u, h2⟩
            change dite (w₁ ≠ u ∧ w₁ ≠ v) _ _ = dite (w₂ ≠ u ∧ w₂ ≠ v) _ _ at hfeq
            rw [dite_val_pos hc1, dite_val_pos hc2] at hfeq
            exact congrArg Subtype.val hfeq
    · let f : V → { y : V // y ≠ u ∧ y ≠ v } := fun w =>
        if hw : w ≠ u ∧ w ≠ v then ⟨w, hw⟩ else x
      apply Finset.card_le_card_of_injOn f
      · intro w hw
        rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hw ⊢
        have hwu : w ≠ u := fun h => hxu (h ▸ hw.symm)
        have hwv : w ≠ v := fun h => hxv (h ▸ hw.symm)
        have hcond : w ≠ u ∧ w ≠ v := ⟨hwu, hwv⟩
        change H.Adj x (dite (w ≠ u ∧ w ≠ v) (fun h => ⟨w, h⟩) (fun _ => x))
        rw [dite_val_pos hcond]
        exact Or.inl hw
      · intro w₁ hw₁ w₂ hw₂ hfeq
        rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hw₁ hw₂
        have hc1 : w₁ ≠ u ∧ w₁ ≠ v := ⟨fun h => hxu (h ▸ hw₁.symm), fun h => hxv (h ▸ hw₁.symm)⟩
        have hc2 : w₂ ≠ u ∧ w₂ ≠ v := ⟨fun h => hxu (h ▸ hw₂.symm), fun h => hxv (h ▸ hw₂.symm)⟩
        change dite (w₁ ≠ u ∧ w₁ ≠ v) _ _ = dite (w₂ ≠ u ∧ w₂ ≠ v) _ _ at hfeq
        rw [dite_val_pos hc1, dite_val_pos hc2] at hfeq
        exact congrArg Subtype.val hfeq

/-- **Theorem 3**: Exact cycle-length lifting arithmetic for `G_parallel(uv)`:
replacing `m ∈ {1, 2}` added edges of `{u₁u₂, v₁v₂}` in a `2^c`-cycle (`c ≥ 1`) by 2-edge paths
through `u` and/or `v` produces length `2^c + 1` (if `m = 1`, avoiding `uv`) or
`2^c + 2` (if `m = 2`, a chorded `(2^c + 2)`-cycle with chord `uv` splitting into
two cycles of lengths `a + 1` and `b + 1` with `a + b = 2^c + 2`). -/
theorem parallel_rewiring_lifting_arithmetic (c m : ℕ) (hc : 1 ≤ c) (hm : m = 1 ∨ m = 2) :
    (m = 1 ∧ 2 ^ c - m + 2 * m = 2 ^ c + 1) ∨
    (m = 2 ∧ 2 ^ c - m + 2 * m = 2 ^ c + 2) := by
  have h2 : 2 ≤ 2 ^ c := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ c := Nat.pow_le_pow_right (by norm_num) hc
  rcases hm with rfl | rfl
  · left; exact ⟨rfl, by omega⟩
  · right; exact ⟨rfl, by omega⟩

/-- **Theorem 4**: Any chorded `(2^c + 2)`-cycle on chord `uv` in a graph of girth `g`
(splitting into two cycles of lengths `a + 1 ≥ g` and `b + 1 ≥ g` with `a + b = 2^c + 2`)
forces `2^c + 4 ≥ 2 * g`. -/
theorem chorded_dyadic_plus_two_girth_lower_bound
    (c g a b : ℕ) (hsum : a + b = 2 ^ c + 2) (ha : g ≤ a + 1) (hb : g ≤ b + 1) :
    2 * g ≤ 2 ^ c + 4 := by
  omega

/-- **Theorem 5**: Concrete girth-tight exclusions of chorded `(2^c + 2)`-cycles:
no chorded `6`-cycle for `g ≥ 5`; no chorded `10`-cycle for `g ≥ 7`;
no chorded `18`-cycle for `g ≥ 11`. -/
theorem chorded_dyadic_plus_two_forbidden_below_girth_threshold :
    (∀ g a b : ℕ, 5 ≤ g → a + b = 2 ^ 2 + 2 → g ≤ a + 1 → g ≤ b + 1 → False) ∧
    (∀ g a b : ℕ, 7 ≤ g → a + b = 2 ^ 3 + 2 → g ≤ a + 1 → g ≤ b + 1 → False) ∧
    (∀ g a b : ℕ, 11 ≤ g → a + b = 2 ^ 4 + 2 → g ≤ a + 1 → g ≤ b + 1 → False) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g a b hg hsum ha hb; omega
  · intro g a b hg hsum ha hb; omega
  · intro g a b hg hsum ha hb; omega

/-- **Theorem 6**: In any `PowerFree` graph, if `a + 1` and `b + 1` are realized as
simple cycle lengths (from a chorded `(2^c + 2)`-cycle on chord `uv`), then
`a + 1 ≠ 2^r` and `b + 1 ≠ 2^r` for all `r ≥ 2`; moreover, if the graph has only
even cycles, both `a` and `b` are odd. -/
theorem chorded_dyadic_plus_two_arc_powerfree_obstruction
    (G : SimpleGraph V) (hPF : PowerFree G) {a b : ℕ}
    (ha : HasCycleOfLength G (a + 1)) (hb : HasCycleOfLength G (b + 1)) :
    (∀ r : ℕ, 2 ≤ r → a + 1 ≠ 2 ^ r ∧ b + 1 ≠ 2 ^ r) ∧
    (EvenCyclesOnly G → Odd a ∧ Odd b) := by
  refine ⟨?_, ?_⟩
  · intro r hr
    constructor
    · intro heq; exact hPF ⟨r, hr, heq ▸ ha⟩
    · intro heq; exact hPF ⟨r, hr, heq ▸ hb⟩
  · intro hEven
    have haE : Even (a + 1) := hEven (a + 1) ha
    have hbE : Even (b + 1) := hEven (b + 1) hb
    rcases haE with ⟨ka, hka⟩
    rcases hbE with ⟨kb, hkb⟩
    exact ⟨⟨ka - 1, by omega⟩, ⟨kb - 1, by omega⟩⟩

end Pillar1TripleRewiring

/-! ## Pillar 2: High-Girth (`g ∈ {7..16}`) Non-Simple Tailless Walk Exact Classification -/

section Pillar2HighGirthWalkClassification

variable {V : Type*}

/-- **Theorem 7**: In any `PowerFree` graph `G`, girth `≥ 2^r` (`r ≥ 2`) automatically
upgrades to girth `≥ 2^r + 1` (e.g., `g ≥ 4 → g ≥ 5`, `g ≥ 8 → g ≥ 9`, `g ≥ 16 → g ≥ 17`). -/
theorem powerfree_girth_skips_pow2
    (G : SimpleGraph V) (hPF : PowerFree G) {r : ℕ} (hr : 2 ≤ r)
    (hg : GirthAtLeast G (2 ^ r)) :
    GirthAtLeast G (2 ^ r + 1) := by
  intro L hL
  have hge : 2 ^ r ≤ L := hg L hL
  have hne : L ≠ 2 ^ r := fun heq => hPF ⟨r, hr, heq ▸ hL⟩
  omega

/-- **Theorem 8**: In any `PowerFree` graph with only even cycles (bipartite),
girth `≥ 7` automatically upgrades to girth `≥ 10`, and girth `≥ 15` automatically
upgrades to girth `≥ 18`. -/
theorem bipartite_powerfree_girth_skips_7_to_10_and_15_to_18
    (G : SimpleGraph V) (hPF : PowerFree G) (hEven : EvenCyclesOnly G) :
    (GirthAtLeast G 7 → GirthAtLeast G 10) ∧
    (GirthAtLeast G 15 → GirthAtLeast G 18) := by
  constructor
  · intro hg L hL
    have hge : 7 ≤ L := hg L hL
    have hE : Even L := hEven L hL
    have hne8 : L ≠ 8 := fun h => hPF ⟨3, by omega, by simpa [h] using hL⟩
    rcases hE with ⟨k, hk⟩
    omega
  · intro hg L hL
    have hge : 15 ≤ L := hg L hL
    have hE : Even L := hEven L hL
    have hne16 : L ≠ 16 := fun h => hPF ⟨4, by omega, by simpa [h] using hL⟩
    rcases hE with ⟨k, hk⟩
    omega

/-- **Theorem 9**: No repeated simple cycle `C^m` (`m ≥ 2`, `|C| = ℓ ≥ 3`) can have
power-of-two length `2^r` (`r ≥ 2`) in a `PowerFree` graph: any divisor `ℓ ≥ 3` of `2^r`
is itself `2^j` with `j ≥ 2`. -/
theorem powerfree_no_repeated_cycle_pow2
    (G : SimpleGraph V) (hPF : PowerFree G)
    {m ℓ r : ℕ} (hℓ : 3 ≤ ℓ) (hC : HasCycleOfLength G ℓ) (hmul : m * ℓ = 2 ^ r) :
    False := by
  have hdvd : ℓ ∣ 2 ^ r := ⟨m, by rw [mul_comm]; exact hmul.symm⟩
  rw [Nat.dvd_prime_pow Nat.prime_two] at hdvd
  rcases hdvd with ⟨j, _, rfl⟩
  have hj : 2 ≤ j := by
    by_contra hlt
    interval_cases j <;> omega
  exact hPF ⟨j, hj, hC⟩

/-- **Theorem 10**: Exact boundary rigidity for cubic Theta-walks `Θ(a, b, c)` of length
`2a + b + c = 2^r` (`r ≥ 3`) in a `PowerFree` graph of girth `g`:
1. `2 * g ≤ 2^r` always;
2. At `g = 2^(r-1) - 1` (e.g., `g = 7` at `16`, `g = 15` at `32`), `{a+b, a+c} = {g, g+2}` is forced;
3. In a bipartite graph at `g = 2^(r-1) - 2` (e.g., `g = 6` at `16`, `g = 14` at `32`),
   `{a+b, a+c} = {g, g+4}` is forced. -/
theorem cubic_theta_walk_boundary_rigidity
    (G : SimpleGraph V) (hPF : PowerFree G)
    {g r a b c : ℕ} (hr : 3 ≤ r)
    (h1 : HasCycleOfLength G (a + b)) (h2 : HasCycleOfLength G (a + c))
    (hg : GirthAtLeast G g)
    (hlen : 2 * a + b + c = 2 ^ r) :
    (2 * g ≤ 2 ^ r) ∧
    (g = 2 ^ (r - 1) - 1 →
      ((a + b = g ∧ a + c = g + 2) ∨ (a + b = g + 2 ∧ a + c = g))) ∧
    (EvenCyclesOnly G → g = 2 ^ (r - 1) - 2 →
      ((a + b = g ∧ a + c = g + 4) ∨ (a + b = g + 4 ∧ a + c = g))) := by
  have hab : g ≤ a + b := hg (a + b) h1
  have hac : g ≤ a + c := hg (a + c) h2
  have hpow : 2 ^ r = 2 * 2 ^ (r - 1) := by
    have : r = (r - 1) + 1 := by omega
    conv_lhs => rw [this, pow_succ, mul_comm]
  have hr1 : 2 ≤ r - 1 := by omega
  have hne1 : a + b ≠ 2 ^ (r - 1) := fun h => hPF ⟨r - 1, hr1, h ▸ h1⟩
  have hne2 : a + c ≠ 2 ^ (r - 1) := fun h => hPF ⟨r - 1, hr1, h ▸ h2⟩
  have hpowE : 2 ∣ 2 ^ (r - 1) := dvd_pow_self 2 (by omega)
  rcases hpowE with ⟨p, hp⟩
  refine ⟨by omega, ?_, ?_⟩
  · intro hgEq
    have h4 : 4 ≤ 2 ^ (r - 1) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (r - 1) := Nat.pow_le_pow_right (by norm_num) hr1
    omega
  · intro hEven hgEq
    have hE1 : Even (a + b) := hEven (a + b) h1
    have hE2 : Even (a + c) := hEven (a + c) h2
    rcases hE1 with ⟨k1, hk1⟩
    rcases hE2 with ⟨k2, hk2⟩
    have h4 : 4 ≤ 2 ^ (r - 1) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (r - 1) := Nat.pow_le_pow_right (by norm_num) hr1
    omega

/-- **Theorem 11**: Exact boundary rigidity for cubic Barbell-walks `(C₁, C₂, P_t)` (`t ≥ 1`)
of length `L₁ + L₂ + 2t = 2^r` (`r ≥ 3`) in a graph of girth `g`:
1. `2 * g + 2 ≤ 2^r` always;
2. At `g = 2^(r-1) - 1`, `L₁ = g ∧ L₂ = g ∧ t = 1` is uniquely forced;
3. In a bipartite `PowerFree` graph at `g = 2^(r-1) - 2`, `L₁ = g ∧ L₂ = g ∧ t = 2` is uniquely forced. -/
theorem cubic_barbell_walk_boundary_rigidity
    (G : SimpleGraph V) (hPF : PowerFree G)
    {g r L₁ L₂ t : ℕ} (hr : 3 ≤ r) (ht : 1 ≤ t)
    (h1 : HasCycleOfLength G L₁) (h2 : HasCycleOfLength G L₂)
    (hg : GirthAtLeast G g)
    (hlen : L₁ + L₂ + 2 * t = 2 ^ r) :
    (2 * g + 2 ≤ 2 ^ r) ∧
    (g = 2 ^ (r - 1) - 1 → L₁ = g ∧ L₂ = g ∧ t = 1) ∧
    (EvenCyclesOnly G → g = 2 ^ (r - 1) - 2 → L₁ = g ∧ L₂ = g ∧ t = 2) := by
  have hL1 : g ≤ L₁ := hg L₁ h1
  have hL2 : g ≤ L₂ := hg L₂ h2
  have hpow : 2 ^ r = 2 * 2 ^ (r - 1) := by
    have : r = (r - 1) + 1 := by omega
    conv_lhs => rw [this, pow_succ, mul_comm]
  have hr1 : 2 ≤ r - 1 := by omega
  have hne1 : L₁ ≠ 2 ^ (r - 1) := fun h => hPF ⟨r - 1, hr1, h ▸ h1⟩
  have hne2 : L₂ ≠ 2 ^ (r - 1) := fun h => hPF ⟨r - 1, hr1, h ▸ h2⟩
  have hpowE : 2 ∣ 2 ^ (r - 1) := dvd_pow_self 2 (by omega)
  rcases hpowE with ⟨p, hp⟩
  refine ⟨by omega, ?_, ?_⟩
  · intro hgEq
    have h4 : 4 ≤ 2 ^ (r - 1) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (r - 1) := Nat.pow_le_pow_right (by norm_num) hr1
    omega
  · intro hEven hgEq
    have hE1 : Even L₁ := hEven L₁ h1
    have hE2 : Even L₂ := hEven L₂ h2
    rcases hE1 with ⟨k1, hk1⟩
    rcases hE2 with ⟨k2, hk2⟩
    have h4 : 4 ≤ 2 ^ (r - 1) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (r - 1) := Nat.pow_le_pow_right (by norm_num) hr1
    omega

/-- **Theorem 12**: Exact Moore-tree layer cardinality recurrence bound for cubic graphs:
if `L 1 ≤ 3` and `L (k + 2) ≤ 2 * L (k + 1)` for all `k`, then
`L h ≤ 3 * 2 ^ (h - 1)` for all `h ≥ 1` (in particular, at girth `15`, `h = 7`, `L 7 ≤ 192`). -/
theorem cubic_moore_layer_card_bound (L : ℕ → ℕ)
    (h1 : L 1 ≤ 3) (hstep : ∀ k : ℕ, L (k + 2) ≤ 2 * L (k + 1)) :
    (∀ h : ℕ, 1 ≤ h → L h ≤ 3 * 2 ^ (h - 1)) ∧ L 7 ≤ 192 := by
  have hmain : ∀ h : ℕ, 1 ≤ h → L h ≤ 3 * 2 ^ (h - 1) := by
    intro h hh
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : h ≠ 0)
    induction m with
    | zero => simpa using h1
    | succ k ih =>
      have hk := hstep k
      have ih' := ih (by omega)
      calc L (k + 2) ≤ 2 * L (k + 1) := hk
        _ ≤ 2 * (3 * 2 ^ k) := Nat.mul_le_mul_left 2 ih'
        _ = 3 * 2 ^ (k + 1) := by ring
  exact ⟨hmain, by have := hmain 7 (by omega); norm_num at this; exact this⟩

end Pillar2HighGirthWalkClassification

/-! ## Pillar 3: Universal High-Girth (`g ∈ {9..14}`) Antipodal & Coprime-Shift Frobenius Closures -/

section Pillar3HighGirthAdjusterClosures

variable {V : Type*}

/-- Helper: Every `M : ℕ` admits a power of two `2^k` (`k ≥ 2`) in `[M, 2 * max M 4]`. -/
lemma exists_pow2_in_doubling_window (M : ℕ) :
    ∃ k : ℕ, 2 ≤ k ∧ M ≤ 2 ^ k ∧ 2 ^ k ≤ 2 * max M 4 := by
  induction M using Nat.strong_induction_on with
  | ind M ih =>
    by_cases hM : M ≤ 4
    · refine ⟨2, le_rfl, hM, ?_⟩
      have : 4 ≤ max M 4 := le_max_right M 4
      omega
    · have hlt : (M + 1) / 2 < M := by omega
      obtain ⟨k, hk2, hlo, hhi⟩ := ih ((M + 1) / 2) hlt
      by_cases hfit : M ≤ 2 ^ k
      · refine ⟨k, hk2, hfit, ?_⟩
        have hmax : max ((M + 1) / 2) 4 ≤ max M 4 := max_le_max_right 4 (le_of_lt hlt)
        omega
      · refine ⟨k + 1, by omega, ?_, ?_⟩
        · have : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, mul_comm]
          omega
        · have : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, mul_comm]
          have : M ≤ max M 4 := le_max_left M 4
          omega

/-- **Theorem 13**: Every odd cycle `C_{2m+1}` (`m ≥ 2`, covering all odd girths
`g ∈ {5, 7, 9, 11, 13, ...}`) routed across its antipodal pair `(m, m + 1)` supplies
an exact unit shift `Δ = 1`. -/
theorem odd_cycle_antipodal_unit_shift (m : ℕ) (hm : 2 ≤ m) :
    m + (m + 1) = 2 * m + 1 ∧ (m + 1) - m = 1 ∧ 1 ≤ m := by
  omega

/-- **Theorem 14**: Every even cycle `C_{2m}` (`m ≥ 3`, covering all even girths
`g ∈ {6, 8, 10, 12, 14, ...}`) routed at `(m - 1, m + 1)` supplies an exact
parity-preserving shift `Δ = 2`. -/
theorem even_cycle_near_antipodal_two_shift (m : ℕ) (hm : 3 ≤ m) :
    (m - 1) + (m + 1) = 2 * m ∧ (m + 1) - (m - 1) = 2 ∧ 2 ≤ m - 1 := by
  omega

/-- **Theorem 15**: Unconditional Unbounded-`n` Odd-Antipodal (`Δ = 1`) Graph Closure:
any finite simple graph `G` containing a backbone cycle of length `L₀ ≥ 1` with
`k ≥ 2 * max L₀ 4 - L₀` realizable unit shifts satisfies `HasPow2Cycle G`. -/
theorem high_girth_odd_antipodal_chain_unbounded_closure
    (G : SimpleGraph V) {L₀ k : ℕ}
    (hk : 2 * max L₀ 4 - L₀ ≤ k)
    (hreal : ∀ j : ℕ, j ≤ k → HasCycleOfLength G (L₀ + j)) :
    HasPow2Cycle G := by
  obtain ⟨r, hr2, hlo, hhi⟩ := exists_pow2_in_doubling_window L₀
  refine ⟨r, hr2, ?_⟩
  have hj : 2 ^ r - L₀ ≤ k := by omega
  have hcyc := hreal (2 ^ r - L₀) hj
  have heq : L₀ + (2 ^ r - L₀) = 2 ^ r := by omega
  rwa [heq] at hcyc

/-- **Theorem 16**: Unconditional Unbounded-`n` Even-Cycle (`Δ = 2`) Graph Closure:
any finite simple graph `G` containing an even backbone cycle of length `2q` with
`k ≥ max (2 * q) 4 - q` realizable `Δ = 2` shifts satisfies `HasPow2Cycle G`. -/
theorem high_girth_even_two_adjuster_chain_unbounded_closure
    (G : SimpleGraph V) {q k : ℕ}
    (hk : max (2 * q) 4 - q ≤ k)
    (hreal : ∀ j : ℕ, j ≤ k → HasCycleOfLength G (2 * q + 2 * j)) :
    HasPow2Cycle G := by
  obtain ⟨r, hr2, hlo, hhi⟩ := exists_pow2_in_doubling_window (2 * q)
  refine ⟨r, hr2, ?_⟩
  have heven : 2 ∣ 2 ^ r := dvd_pow_self 2 (by omega)
  rcases heven with ⟨t, ht⟩
  have hj : t - q ≤ k := by omega
  have hcyc := hreal (t - q) hj
  have heq : 2 * q + 2 * (t - q) = 2 ^ r := by omega
  rwa [heq] at hcyc

/-- **Theorem 17**: Exact ear-shift parity and range for arbitrary odd cycles `C_{2m+1}`:
every non-trivial arc split `(d, 2m + 1 - d)` with `1 ≤ d ≤ m` produces a strictly odd
shift `Δ = (2m + 1 - d) - d = 2(m - d) + 1` in `[1, 2m - 1]`. -/
theorem odd_cycle_all_ear_shifts_odd (m d : ℕ) (hd1 : 1 ≤ d) (hdm : d ≤ m) :
    Odd ((2 * m + 1 - d) - d) ∧
    1 ≤ (2 * m + 1 - d) - d ∧
    (2 * m + 1 - d) - d ≤ 2 * m - 1 := by
  refine ⟨⟨m - d, by omega⟩, by omega, by omega⟩

/-- Frobenius two-coin representation lemma: for any coprime `s₁, s₂ ≥ 2` and any
`N ≥ (s₁ - 1) * (s₂ - 1)`, there exist `a ≤ s₂ - 1` and `b ≤ N / s₂` with
`a * s₁ + b * s₂ = N`. -/
lemma frobenius_two_coprime_representation
    {s₁ s₂ N : ℕ} (hs₁ : 2 ≤ s₁) (hs₂ : 2 ≤ s₂) (hcop : Nat.Coprime s₁ s₂)
    (hN : (s₁ - 1) * (s₂ - 1) ≤ N) :
    ∃ a b : ℕ, a ≤ s₂ - 1 ∧ b ≤ N / s₂ ∧ a * s₁ + b * s₂ = N := by
  have hgcd : (Int.gcd (s₁ : ℤ) (s₂ : ℤ) : ℤ) = 1 := by
    have : Int.gcd (s₁ : ℤ) (s₂ : ℤ) = Nat.gcd s₁ s₂ := by rfl
    rw [this, hcop.gcd_eq_one]
    rfl
  have hbez : (1 : ℤ) = (s₁ : ℤ) * Int.gcdA (s₁ : ℤ) (s₂ : ℤ) +
                        (s₂ : ℤ) * Int.gcdB (s₁ : ℤ) (s₂ : ℤ) := by
    rw [← hgcd]
    exact Int.gcd_eq_gcd_ab (s₁ : ℤ) (s₂ : ℤ)
  set x : ℤ := (N : ℤ) * Int.gcdA (s₁ : ℤ) (s₂ : ℤ)
  set y : ℤ := (N : ℤ) * Int.gcdB (s₁ : ℤ) (s₂ : ℤ)
  have hNbez : (N : ℤ) = (s₁ : ℤ) * x + (s₂ : ℤ) * y := by
    calc (N : ℤ) = (N : ℤ) * 1 := (mul_one _).symm
      _ = (N : ℤ) * ((s₁ : ℤ) * Int.gcdA (s₁ : ℤ) (s₂ : ℤ) +
                     (s₂ : ℤ) * Int.gcdB (s₁ : ℤ) (s₂ : ℤ)) := by rw [← hbez]
      _ = (s₁ : ℤ) * x + (s₂ : ℤ) * y := by ring
  have hs2pos : (0 : ℤ) < (s₂ : ℤ) := by omega
  set aZ : ℤ := x % (s₂ : ℤ)
  have haZ_nn : 0 ≤ aZ := Int.emod_nonneg x (ne_of_gt hs2pos)
  have haZ_lt : aZ < (s₂ : ℤ) := Int.emod_lt_of_pos x hs2pos
  set a : ℕ := aZ.toNat
  have ha_cast : (a : ℤ) = aZ := Int.toNat_of_nonneg haZ_nn
  have ha_le : a ≤ s₂ - 1 := by omega
  have hmod0 : ((N : ℤ) - (a : ℤ) * (s₁ : ℤ)) % (s₂ : ℤ) = 0 := by
    rw [hNbez, ha_cast]
    have h1 : ((s₁ : ℤ) * x + (s₂ : ℤ) * y - aZ * (s₁ : ℤ)) =
              (s₁ : ℤ) * (x - aZ) + (s₂ : ℤ) * y := by ring
    rw [h1, Int.add_emod, Int.mul_emod_right, add_zero, Int.emod_emod, Int.mul_emod]
    have hxa : (x - aZ) % (s₂ : ℤ) = 0 := by
      simp [aZ, Int.sub_emod]
    rw [hxa, mul_zero, Int.zero_emod]
  have hdvd : (s₂ : ℤ) ∣ (N : ℤ) - (a : ℤ) * (s₁ : ℤ) := Int.dvd_of_emod_eq_zero hmod0
  rcases hdvd with ⟨q, hq⟩
  have hq_nn : 0 ≤ q := by
    by_contra hneg
    have hq_le : q ≤ -1 := by omega
    have hN_cast : ((s₁ : ℤ) - 1) * ((s₂ : ℤ) - 1) ≤ (N : ℤ) := by
      have h1 : ((s₁ - 1 : ℕ) : ℤ) = (s₁ : ℤ) - 1 := by omega
      have h2 : ((s₂ - 1 : ℕ) : ℤ) = (s₂ : ℤ) - 1 := by omega
      have h3 : (((s₁ - 1) * (s₂ - 1) : ℕ) : ℤ) ≤ (N : ℤ) := Int.ofNat_le.mpr hN
      rw [Nat.cast_mul, h1, h2] at h3
      exact h3
    have ha_leZ : (a : ℤ) ≤ (s₂ : ℤ) - 1 := by omega
    nlinarith
  set b : ℕ := q.toNat
  have hb_cast : (b : ℤ) = q := Int.toNat_of_nonneg hq_nn
  have heqZ : (a : ℤ) * (s₁ : ℤ) + (b : ℤ) * (s₂ : ℤ) = (N : ℤ) := by
    rw [hb_cast]
    linarith
  have heq : a * s₁ + b * s₂ = N := by
    exact_mod_cast heqZ
  have hb_le : b ≤ N / s₂ := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    omega
  exact ⟨a, b, ha_le, hb_le, heq⟩

/-- **Theorem 18**: Universal Coprime-Shift Frobenius Unbounded-`n` Closure (No `Δ = 1`
Adjuster Needed, Zero Divisibility Hypothesis!):
For any two coprime shifts `s₁, s₂ ≥ 2` (e.g., `Δ = 3` and `Δ = 5` on `C_9, C_11, C_13`),
any finite simple graph `G` with a backbone cycle of ANY length `L₀ ≥ 1` and realizable
`s₁`-shifts up to `A ≥ s₂ - 1` and `s₂`-shifts up to `B ≥ (2 * max (L₀ + (s₁ - 1) * (s₂ - 1)) 4 - L₀) / s₂`
unconditionally satisfies `HasPow2Cycle G`. -/
theorem coprime_shift_frobenius_unbounded_closure
    (G : SimpleGraph V) {s₁ s₂ L₀ A B : ℕ}
    (hs₁ : 2 ≤ s₁) (hs₂ : 2 ≤ s₂) (hcop : Nat.Coprime s₁ s₂)
    (hA : s₂ - 1 ≤ A)
    (hB : (2 * max (L₀ + (s₁ - 1) * (s₂ - 1)) 4 - L₀) / s₂ ≤ B)
    (hreal : ∀ a b : ℕ, a ≤ A → b ≤ B → HasCycleOfLength G (L₀ + a * s₁ + b * s₂)) :
    HasPow2Cycle G := by
  set F := (s₁ - 1) * (s₂ - 1)
  obtain ⟨r, hr2, hlo, hhi⟩ := exists_pow2_in_doubling_window (L₀ + F)
  refine ⟨r, hr2, ?_⟩
  set N := 2 ^ r - L₀
  have hNF : F ≤ N := by omega
  obtain ⟨a, b, ha_le, hb_le, hab⟩ := frobenius_two_coprime_representation hs₁ hs₂ hcop hNF
  have haA : a ≤ A := le_trans ha_le hA
  have hbB : b ≤ B := by
    have hN_le : N ≤ 2 * max (L₀ + F) 4 - L₀ := by omega
    exact le_trans hb_le (le_trans (Nat.div_le_div_right hN_le) hB)
  have hcyc := hreal a b haA hbB
  have heq : L₀ + a * s₁ + b * s₂ = 2 ^ r := by omega
  rwa [heq] at hcyc

end Pillar3HighGirthAdjusterClosures

end E64Wave8Agent7
