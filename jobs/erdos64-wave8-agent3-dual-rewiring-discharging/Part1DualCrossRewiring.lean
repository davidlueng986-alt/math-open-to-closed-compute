import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic

/-!
# Erdős Problem #64 — Wave 8 Guided Agent #3 (`wave8_agent3`)
## Part 1: Exact Dual Cross-Rewiring Surgery & Simultaneous 2-Pairing Lifting on `MinimalBad2`

All theorems are proved unconditionally in Lean 4.36.0 with `-DwarningAsError=true`
and standard axioms (`propext`, `Classical.choice`, `Quot.sound`) only.
-/

namespace E64Wave8Agent3P1

open SimpleGraph

/-- `IsPow2 n` holds when `n = 2^k` for some `k ≥ 2` (i.e. `n ∈ {4, 8, 16, 32, ...}`). -/
def IsPow2 (n : ℕ) : Prop := ∃ k : ℕ, 2 ≤ k ∧ n = 2 ^ k

/-- `HasPow2Cycle G` holds when `G` contains a simple cycle of length `2^k` (`k ≥ 2`). -/
def HasPow2Cycle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ IsPow2 p.length

/-- `PowerFree G` holds when `G` contains no simple cycle of length `2^k` (`k ≥ 2`). -/
def PowerFree {V : Type*} (G : SimpleGraph V) : Prop := ¬ HasPow2Cycle G

/-- `HasCycleLen G L` holds when `G` contains a simple cycle of exact length `L`. -/
def HasCycleLen {V : Type*} (G : SimpleGraph V) (L : ℕ) : Prop :=
  ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = L

/-- `GirthGe G g` holds when every simple cycle in `G` has length at least `g`. -/
def GirthGe {V : Type*} (G : SimpleGraph V) (g : ℕ) : Prop :=
  ∀ (v : V) (p : G.Walk v v), p.IsCycle → g ≤ p.length

/-- `C4Free G` holds when no four distinct vertices form a 4-cycle. -/
def C4Free {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ a b c d : V, a ≠ b → b ≠ c → c ≠ d → d ≠ a → a ≠ c → b ≠ d →
    ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)

/-- The set of defect vertices (degree < 3) in a finite simple graph. -/
noncomputable def Defects {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Finset V :=
  Finset.univ.filter (fun v => G.degree v < 3)

/-- `MinimalBad2 G`: a vertex-minimal `PowerFree` graph with `δ(G) ≥ 2` and at most 2 defects,
such that every strictly smaller nonempty simple graph with `δ ≥ 2` and at most 2 defects
contains a power-of-two simple cycle. -/
structure MinimalBad2 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop where
  power_free : PowerFree G
  min_deg_two : ∀ v : V, 2 ≤ G.degree v
  defects_le_two : (Defects G).card ≤ 2
  minimal : ∀ {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj],
    Nonempty W →
    Fintype.card W < Fintype.card V →
    (∀ w : W, 2 ≤ H.degree w) →
    (Defects H).card ≤ 2 →
    HasPow2Cycle H

/-- Every `PowerFree` graph is `C4Free`. -/
lemma powerFree_c4Free {V : Type*} (G : SimpleGraph V) (hpf : PowerFree G) : C4Free G := by
  intro a b c d hab hbc hcd hda hac hbd ⟨h1, h2, h3, h4⟩
  let p : G.Walk a a :=
    Walk.cons h1 (Walk.cons h2 (Walk.cons h3 (Walk.cons h4 Walk.nil)))
  have hp_cyc : p.IsCycle := by
    rw [Walk.isCycle_def]
    refine ⟨?_, ?_, ?_⟩
    · rw [Walk.isTrail_def]
      simp only [p, Walk.edges_cons, Walk.edges_nil, List.nodup_cons, List.mem_cons,
        List.not_mem_nil, or_false, List.nodup_nil, and_true, Sym2.eq_iff]
      refine ⟨?_, ?_, ?_⟩
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact hab rfl
        · exact hac rfl
        · exact hac rfl
        · exact hbd rfl
        · exact hda rfl
        · exact hbd rfl
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact hbc rfl
        · exact hbd rfl
        · exact hbd rfl
        · exact hac rfl
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact hcd rfl
        · exact hac rfl
    · simp [p]
    · simp only [p, Walk.support_cons, Walk.support_nil, List.tail_cons, List.nodup_cons,
        List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true]
      refine ⟨?_, ?_, ?_⟩
      · rintro (rfl | rfl | rfl)
        · exact hbc rfl
        · exact hbd rfl
        · exact hab rfl
      · rintro (rfl | rfl)
        · exact hcd rfl
        · exact hac rfl
      · intro h; exact hda h.symm
  exact hpf ⟨a, p, hp_cyc, ⟨2, le_rfl, rfl⟩⟩

/-- Disjointness and non-adjacency of external neighborhoods of a non-triangle edge in a `C4Free` graph. -/
lemma cross_neighbors_disjoint_nonadj {V : Type*} (G : SimpleGraph V) (hc4 : C4Free G)
    {u v u' v' : V} (huv : G.Adj u v)
    (hnotri : ∀ w : V, ¬ (G.Adj u w ∧ G.Adj w v))
    (hu' : G.Adj u u') (hu'v : u' ≠ v) (hv' : G.Adj v v') (hv'u : v' ≠ u) :
    u' ≠ v' ∧ ¬ G.Adj u' v' := by
  have hne : u' ≠ v' := by
    intro h; subst h; exact hnotri u' ⟨hu', hv'.symm⟩
  have hnadj : ¬ G.Adj u' v' := by
    intro hadj
    exact hc4 u u' v' v (G.ne_of_adj hu') hne (G.ne_of_adj hv').symm (G.ne_of_adj huv).symm
      hv'u.symm hu'v ⟨hu', hadj, hv'.symm, huv.symm⟩
  exact ⟨hne, hnadj⟩

/-- The cross-rewired graph `G_×(u, v; u₁, u₂, v₁, v₂)` on `{w : V // w ≠ u ∧ w ≠ v}`,
obtained by deleting `{u, v}` and adding the matching `{u₁v₁, u₂v₂}`. -/
def crossRewire {V : Type*} (G : SimpleGraph V) (u v u₁ u₂ v₁ v₂ : V)
    (h1 : u₁ ≠ v₁) (h2 : u₂ ≠ v₂) : SimpleGraph {w : V // w ≠ u ∧ w ≠ v} where
  Adj x y :=
    G.Adj x.1 y.1 ∨
    (x.1 = u₁ ∧ y.1 = v₁) ∨ (x.1 = v₁ ∧ y.1 = u₁) ∨
    (x.1 = u₂ ∧ y.1 = v₂) ∨ (x.1 = v₂ ∧ y.1 = u₂)
  symm := by
    intro x y h
    rcases h with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  loopless := by
    intro x h
    rcases h with h | ⟨hxa, hxb⟩ | ⟨hxa, hxb⟩ | ⟨hxa, hxb⟩ | ⟨hxa, hxb⟩
    · exact G.loopless x.1 h
    · exact h1 (hxa.symm.trans hxb)
    · exact h1 (hxb.symm.trans hxa)
    · exact h2 (hxa.symm.trans hxb)
    · exact h2 (hxb.symm.trans hxa)

private lemma degree_eq_of_single_replace' {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v : V} (H : SimpleGraph {w : V // w ≠ u ∧ w ≠ v}) [DecidableRel H.Adj]
    (x : {w : V // w ≠ u ∧ w ≠ v})
    (del : V) (add : {w : V // w ≠ u ∧ w ≠ v})
    (hdel_uv : del = u ∨ del = v)
    (hdel_adj : G.Adj x.1 del)
    (hdel_only : ∀ w : V, G.Adj x.1 w → (w = u ∨ w = v) → w = del)
    (hadd_nadj : ¬ G.Adj x.1 add.1)
    (hH_iff : ∀ y : {w : V // w ≠ u ∧ w ≠ v}, H.Adj x y ↔ G.Adj x.1 y.1 ∨ y = add) :
    H.degree x = G.degree x.1 := by
  classical
  have h1 : ((H.neighborFinset x).erase add).card = ((G.neighborFinset x.1).erase del).card := by
    refine Finset.card_bij
      (fun (y : {w : V // w ≠ u ∧ w ≠ v}) _ => y.1) ?_ ?_ ?_
    · intro y hy
      have hy_ne : y ≠ add := (Finset.mem_erase.mp hy).1
      have hy_adj : H.Adj x y := (mem_neighborFinset H x y).mp (Finset.mem_erase.mp hy).2
      have hGadj : G.Adj x.1 y.1 := ((hH_iff y).mp hy_adj).resolve_right hy_ne
      refine Finset.mem_erase.mpr ⟨?_, (mem_neighborFinset G x.1 y.1).mpr hGadj⟩
      intro heq
      rcases hdel_uv with rfl | rfl
      · exact y.2.1 heq
      · exact y.2.2 heq
    · intro y₁ _ y₂ _ heq; exact Subtype.ext heq
    · intro w hw
      have hw_ne : w ≠ del := (Finset.mem_erase.mp hw).1
      have hw_adj : G.Adj x.1 w := (mem_neighborFinset G x.1 w).mp (Finset.mem_erase.mp hw).2
      have hne_uv : w ≠ u ∧ w ≠ v :=
        ⟨fun h => hw_ne (hdel_only w hw_adj (Or.inl h)),
         fun h => hw_ne (hdel_only w hw_adj (Or.inr h))⟩
      refine ⟨⟨w, hne_uv⟩, ?_, rfl⟩
      refine Finset.mem_erase.mpr ⟨?_, (mem_neighborFinset H x ⟨w, hne_uv⟩).mpr
        ((hH_iff ⟨w, hne_uv⟩).mpr (Or.inl hw_adj))⟩
      intro heq
      exact hadd_nadj (congrArg Subtype.val heq ▸ hw_adj)
  have hadd_mem : add ∈ H.neighborFinset x :=
    (mem_neighborFinset H x add).mpr ((hH_iff add).mpr (Or.inr rfl))
  have hdel_mem : del ∈ G.neighborFinset x.1 := (mem_neighborFinset G x.1 del).mpr hdel_adj
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree,
    ← Finset.card_erase_add_one hadd_mem, ← Finset.card_erase_add_one hdel_mem, h1]

/--
Theorem 1 (`crossRewire_exact_degree_eq`):
In any `C4Free` finite simple graph `G`, for any non-triangle cubic edge `uv` with
`N(u) = {v, u₁, u₂}` (`u₁ ≠ u₂`) and `N(v) = {u, v₁, v₂}` (`v₁ ≠ v₂`), the cross-rewired graph
`H = crossRewire G u v u₁ u₂ v₁ v₂` satisfies **exact degree equality** `H.degree x = G.degree x.1`
for every surviving vertex `x : {w : V // w ≠ u ∧ w ≠ v}`.
-/
theorem crossRewire_exact_degree_eq {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc4 : C4Free G) {u v u₁ u₂ v₁ v₂ : V}
    (huv : G.Adj u v)
    (hnotri : ∀ w : V, ¬ (G.Adj u w ∧ G.Adj w v))
    (hu_nb : ∀ w : V, G.Adj u w ↔ w = v ∨ w = u₁ ∨ w = u₂)
    (hv_nb : ∀ w : V, G.Adj v w ↔ w = u ∨ w = v₁ ∨ w = v₂)
    (hu₁₂ : u₁ ≠ u₂) (hv₁₂ : v₁ ≠ v₂)
    (hu₁v : u₁ ≠ v) (hu₂v : u₂ ≠ v) (hv₁u : v₁ ≠ u) (hv₂u : v₂ ≠ u)
    (h1 : u₁ ≠ v₁) (h2 : u₂ ≠ v₂) :
    let H := crossRewire G u v u₁ u₂ v₁ v₂ h1 h2
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    ∀ x : {w : V // w ≠ u ∧ w ≠ v}, H.degree x = G.degree x.1 := by
  classical
  intro H _ x
  have hu₁_adj : G.Adj u u₁ := (hu_nb u₁).mpr (Or.inr (Or.inl rfl))
  have hu₂_adj : G.Adj u u₂ := (hu_nb u₂).mpr (Or.inr (Or.inr rfl))
  have hv₁_adj : G.Adj v v₁ := (hv_nb v₁).mpr (Or.inr (Or.inl rfl))
  have hv₂_adj : G.Adj v v₂ := (hv_nb v₂).mpr (Or.inr (Or.inr rfl))
  have hu₁_ne_u : u₁ ≠ u := (G.ne_of_adj hu₁_adj).symm
  have hu₂_ne_u : u₂ ≠ u := (G.ne_of_adj hu₂_adj).symm
  have hv₁_ne_v : v₁ ≠ v := (G.ne_of_adj hv₁_adj).symm
  have hv₂_ne_v : v₂ ≠ v := (G.ne_of_adj hv₂_adj).symm
  have h11 := cross_neighbors_disjoint_nonadj G hc4 huv hnotri hu₁_adj hu₁v hv₁_adj hv₁u
  have h12 := cross_neighbors_disjoint_nonadj G hc4 huv hnotri hu₁_adj hu₁v hv₂_adj hv₂u
  have h21 := cross_neighbors_disjoint_nonadj G hc4 huv hnotri hu₂_adj hu₂v hv₁_adj hv₁u
  have h22 := cross_neighbors_disjoint_nonadj G hc4 huv hnotri hu₂_adj hu₂v hv₂_adj hv₂u
  by_cases hxu₁ : x.1 = u₁
  · refine degree_eq_of_single_replace' G H x u ⟨v₁, hv₁u, hv₁_ne_v⟩ (Or.inl rfl)
      (hxu₁ ▸ hu₁_adj.symm) ?_ (hxu₁ ▸ h11.2) ?_
    · intro w hw hwu
      rcases hwu with rfl | rfl
      · rfl
      · exact absurd ⟨hu₁_adj, hxu₁ ▸ hw⟩ (hnotri u₁)
    · intro y
      constructor
      · intro h
        rcases h with h | ⟨_, hy⟩ | ⟨hx, _⟩ | ⟨hx, _⟩ | ⟨hx, _⟩
        · exact Or.inl h
        · exact Or.inr (Subtype.ext hy)
        · exact absurd (hxu₁.symm.trans hx) h11.1
        · exact absurd (hxu₁.symm.trans hx) hu₁₂
        · exact absurd (hxu₁.symm.trans hx) h12.1
      · rintro (h | rfl)
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨hxu₁, rfl⟩)
  · by_cases hxu₂ : x.1 = u₂
    · refine degree_eq_of_single_replace' G H x u ⟨v₂, hv₂u, hv₂_ne_v⟩ (Or.inl rfl)
        (hxu₂ ▸ hu₂_adj.symm) ?_ (hxu₂ ▸ h22.2) ?_
      · intro w hw hwu
        rcases hwu with rfl | rfl
        · rfl
        · exact absurd ⟨hu₂_adj, hxu₂ ▸ hw⟩ (hnotri u₂)
      · intro y
        constructor
        · intro h
          rcases h with h | ⟨hx, _⟩ | ⟨hx, _⟩ | ⟨_, hy⟩ | ⟨hx, _⟩
          · exact Or.inl h
          · exact absurd (hxu₂.symm.trans hx) hu₁₂.symm
          · exact absurd (hxu₂.symm.trans hx) h21.1
          · exact Or.inr (Subtype.ext hy)
          · exact absurd (hxu₂.symm.trans hx) h22.1
        · rintro (h | rfl)
          · exact Or.inl h
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hxu₂, rfl⟩)))
    · by_cases hxv₁ : x.1 = v₁
      · refine degree_eq_of_single_replace' G H x v ⟨u₁, hu₁_ne_u, hu₁v⟩ (Or.inr rfl)
          (hxv₁ ▸ hv₁_adj.symm) ?_ (fun hadj => h11.2 (hxv₁ ▸ hadj).symm) ?_
        · intro w hw hwu
          rcases hwu with rfl | rfl
          · exact absurd ⟨(hxv₁ ▸ hw).symm, hv₁_adj.symm⟩ (hnotri v₁)
          · rfl
        · intro y
          constructor
          · intro h
            rcases h with h | ⟨hx, _⟩ | ⟨_, hy⟩ | ⟨hx, _⟩ | ⟨hx, _⟩
            · exact Or.inl h
            · exact absurd (hxv₁.symm.trans hx) h11.1.symm
            · exact Or.inr (Subtype.ext hy)
            · exact absurd (hxv₁.symm.trans hx) h21.1.symm
            · exact absurd (hxv₁.symm.trans hx) hv₁₂
          · rintro (h | rfl)
            · exact Or.inl h
            · exact Or.inr (Or.inr (Or.inl ⟨hxv₁, rfl⟩))
      · by_cases hxv₂ : x.1 = v₂
        · refine degree_eq_of_single_replace' G H x v ⟨u₂, hu₂_ne_u, hu₂v⟩ (Or.inr rfl)
            (hxv₂ ▸ hv₂_adj.symm) ?_ (fun hadj => h22.2 (hxv₂ ▸ hadj).symm) ?_
          · intro w hw hwu
            rcases hwu with rfl | rfl
            · exact absurd ⟨(hxv₂ ▸ hw).symm, hv₂_adj.symm⟩ (hnotri v₂)
            · rfl
          · intro y
            constructor
            · intro h
              rcases h with h | ⟨hx, _⟩ | ⟨hx, _⟩ | ⟨hx, _⟩ | ⟨_, hy⟩
              · exact Or.inl h
              · exact absurd (hxv₂.symm.trans hx) h12.1.symm
              · exact absurd (hxv₂.symm.trans hx) hv₁₂.symm
              · exact absurd (hxv₂.symm.trans hx) h22.1.symm
              · exact Or.inr (Subtype.ext hy)
            · rintro (h | rfl)
              · exact Or.inl h
              · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hxv₂, rfl⟩)))
        · rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
          refine Finset.card_bij (fun (y : {w : V // w ≠ u ∧ w ≠ v}) _ => y.1) ?_ ?_ ?_
          · intro y hy
            have hy_adj : H.Adj x y := (mem_neighborFinset H x y).mp hy
            have hGadj : G.Adj x.1 y.1 := by
              rcases hy_adj with h | ⟨hx, _⟩ | ⟨hx, _⟩ | ⟨hx, _⟩ | ⟨hx, _⟩
              · exact h
              · exact absurd hx hxu₁
              · exact absurd hx hxv₁
              · exact absurd hx hxu₂
              · exact absurd hx hxv₂
            exact (mem_neighborFinset G x.1 y.1).mpr hGadj
          · intro y₁ _ y₂ _ heq; exact Subtype.ext heq
          · intro w hw
            have hxw : G.Adj x.1 w := (mem_neighborFinset G x.1 w).mp hw
            have hne : w ≠ u ∧ w ≠ v := by
              constructor
              · intro hwu; subst hwu
                rcases (hu_nb x.1).mp hxw.symm with h | h | h
                · exact x.2.2 h
                · exact hxu₁ h
                · exact hxu₂ h
              · intro hwv; subst hwv
                rcases (hv_nb x.1).mp hxw.symm with h | h | h
                · exact x.2.1 h
                · exact hxv₁ h
                · exact hxv₂ h
            exact ⟨⟨w, hne⟩, (mem_neighborFinset H x ⟨w, hne⟩).mpr (Or.inl hxw), rfl⟩

/--
Theorem 2 (`crossRewire_preserves_defects`):
Under the hypotheses of Theorem 1, `crossRewire G u v u₁ u₂ v₁ v₂` has at most `(Defects G).card`
defects and preserves `δ ≥ 2`.
-/
theorem crossRewire_preserves_defects {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc4 : C4Free G) (hmin2 : ∀ w : V, 2 ≤ G.degree w) {u v u₁ u₂ v₁ v₂ : V}
    (huv : G.Adj u v)
    (hnotri : ∀ w : V, ¬ (G.Adj u w ∧ G.Adj w v))
    (hu_nb : ∀ w : V, G.Adj u w ↔ w = v ∨ w = u₁ ∨ w = u₂)
    (hv_nb : ∀ w : V, G.Adj v w ↔ w = u ∨ w = v₁ ∨ w = v₂)
    (hu₁₂ : u₁ ≠ u₂) (hv₁₂ : v₁ ≠ v₂)
    (hu₁v : u₁ ≠ v) (hu₂v : u₂ ≠ v) (hv₁u : v₁ ≠ u) (hv₂u : v₂ ≠ u)
    (h1 : u₁ ≠ v₁) (h2 : u₂ ≠ v₂) :
    let H := crossRewire G u v u₁ u₂ v₁ v₂ h1 h2
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    (∀ x : {w : V // w ≠ u ∧ w ≠ v}, 2 ≤ H.degree x) ∧
    (Defects H).card ≤ (Defects G).card := by
  classical
  intro H _
  have hdeg := crossRewire_exact_degree_eq G hc4 huv hnotri hu_nb hv_nb hu₁₂ hv₁₂
    hu₁v hu₂v hv₁u hv₂u h1 h2
  refine ⟨fun x => by rw [hdeg x]; exact hmin2 x.1, ?_⟩
  refine Finset.card_le_card_of_injOn (fun x => x.1) ?_ ?_
  · intro x hx
    simp only [Defects, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [← hdeg x]; exact hx
  · intro x₁ _ x₂ _ heq; exact Subtype.ext heq

/--
Theorem 3 (`minimal_bad2_dual_cross_rewiring_both_pow2`):
In any `MinimalBad2` graph `G`, for any non-triangle cubic edge `uv` with `N(u) = {v, u₁, u₂}`
and `N(v) = {u, v₁, v₂}`, **BOTH** cross-rewirings `G_×^(1)` (adding `{u₁v₁, u₂v₂}`) and
`G_×^(2)` (adding `{u₁v₂, u₂v₁}`) unconditionally contain a simple `2^k`-cycle (`k ≥ 2`).
-/
theorem minimal_bad2_dual_cross_rewiring_both_pow2 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmb : MinimalBad2 G) {u v u₁ u₂ v₁ v₂ : V}
    (huv : G.Adj u v)
    (hnotri : ∀ w : V, ¬ (G.Adj u w ∧ G.Adj w v))
    (hu_nb : ∀ w : V, G.Adj u w ↔ w = v ∨ w = u₁ ∨ w = u₂)
    (hv_nb : ∀ w : V, G.Adj v w ↔ w = u ∨ w = v₁ ∨ w = v₂)
    (hu₁₂ : u₁ ≠ u₂) (hv₁₂ : v₁ ≠ v₂)
    (hu₁v : u₁ ≠ v) (hu₂v : u₂ ≠ v) (hv₁u : v₁ ≠ u) (hv₂u : v₂ ≠ u) :
    ∃ (h11 : u₁ ≠ v₁) (h22 : u₂ ≠ v₂) (h12 : u₁ ≠ v₂) (h21 : u₂ ≠ v₁),
      HasPow2Cycle (crossRewire G u v u₁ u₂ v₁ v₂ h11 h22) ∧
      HasPow2Cycle (crossRewire G u v u₁ u₂ v₂ v₁ h12 h21) := by
  classical
  have hc4 : C4Free G := powerFree_c4Free G hmb.power_free
  have hu₁_adj : G.Adj u u₁ := (hu_nb u₁).mpr (Or.inr (Or.inl rfl))
  have hu₂_adj : G.Adj u u₂ := (hu_nb u₂).mpr (Or.inr (Or.inr rfl))
  have hv₁_adj : G.Adj v v₁ := (hv_nb v₁).mpr (Or.inr (Or.inl rfl))
  have hv₂_adj : G.Adj v v₂ := (hv_nb v₂).mpr (Or.inr (Or.inr rfl))
  have h11 : u₁ ≠ v₁ :=
    (cross_neighbors_disjoint_nonadj G hc4 huv hnotri hu₁_adj hu₁v hv₁_adj hv₁u).1
  have h22 : u₂ ≠ v₂ :=
    (cross_neighbors_disjoint_nonadj G hc4 huv hnotri hu₂_adj hu₂v hv₂_adj hv₂u).1
  have h12 : u₁ ≠ v₂ :=
    (cross_neighbors_disjoint_nonadj G hc4 huv hnotri hu₁_adj hu₁v hv₂_adj hv₂u).1
  have h21 : u₂ ≠ v₁ :=
    (cross_neighbors_disjoint_nonadj G hc4 huv hnotri hu₂_adj hu₂v hv₁_adj hv₁u).1
  have hu₁_ne_u : u₁ ≠ u := (G.ne_of_adj hu₁_adj).symm
  have hneW : Nonempty {w : V // w ≠ u ∧ w ≠ v} := ⟨⟨u₁, hu₁_ne_u, hu₁v⟩⟩
  have hcard_lt : Fintype.card {w : V // w ≠ u ∧ w ≠ v} < Fintype.card V := by
    have hlt : (Finset.univ.filter (fun w : V => w ≠ u ∧ w ≠ v)).card <
        (Finset.univ : Finset V).card := by
      refine Finset.card_lt_card ?_
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.filter_subset _ _, ?_⟩
      intro heq
      have hu_mem : u ∈ Finset.univ.filter (fun w : V => w ≠ u ∧ w ≠ v) := by
        rw [heq]; exact Finset.mem_univ u
      exact (Finset.mem_filter.mp hu_mem).2.1 rfl
    simpa [Fintype.card_subtype] using hlt
  have hv_nb' : ∀ w : V, G.Adj v w ↔ w = u ∨ w = v₂ ∨ w = v₁ := by
    intro w; rw [hv_nb w]; tauto
  have hp1 := crossRewire_preserves_defects G hc4 hmb.min_deg_two huv hnotri hu_nb hv_nb
    hu₁₂ hv₁₂ hu₁v hu₂v hv₁u hv₂u h11 h22
  have hp2 := crossRewire_preserves_defects G hc4 hmb.min_deg_two huv hnotri hu_nb hv_nb'
    hu₁₂ hv₁₂.symm hu₁v hu₂v hv₂u hv₁u h12 h21
  refine ⟨h11, h22, h12, h21, ?_, ?_⟩
  · exact hmb.minimal _ hneW hcard_lt hp1.1 (le_trans hp1.2 hmb.defects_le_two)
  · exact hmb.minimal _ hneW hcard_lt hp2.1 (le_trans hp2.2 hmb.defects_le_two)

/-- Helper: constructing a simple cycle from a simple path `p : G.Walk a c` and a 3-edge closing
path `c - v - u - a` avoiding `p.support`. -/
lemma cycle_of_path_and_edge_bridge {V : Type*} (G : SimpleGraph V)
    {u v a c : V} (p : G.Walk a c) (hp : p.IsPath)
    (huv : G.Adj u v) (hua : G.Adj u a) (hvc : G.Adj v c)
    (hu_not : u ∉ p.support) (hv_not : v ∉ p.support)
    (_hac : a ≠ c) :
    HasCycleLen G (p.length + 3) := by
  let q : G.Walk a a :=
    Walk.cons hua (Walk.cons huv (Walk.cons hvc p.reverse))
  have hne_uv : u ≠ v := G.ne_of_adj huv
  have hne_ua : u ≠ a := G.ne_of_adj hua
  have hne_va : v ≠ a := fun h => hv_not (h ▸ Walk.start_mem_support p)
  have hne_uc : u ≠ c := fun h => hu_not (h ▸ Walk.end_mem_support p)
  have hrev_path : p.reverse.IsPath := hp.reverse
  have hrev_nodup : p.reverse.support.Nodup := hrev_path.support_nodup
  have hsup_q : q.support.tail = u :: v :: p.reverse.support := by
    simp [q, Walk.support_cons]
  have htail_nodup : q.support.tail.Nodup := by
    rw [hsup_q, List.nodup_cons, List.nodup_cons]
    refine ⟨?_, ?_, hrev_nodup⟩
    · simp only [List.mem_cons, Walk.support_reverse, List.mem_reverse, not_or]
      exact ⟨hne_uv, hu_not⟩
    · simp only [Walk.support_reverse, List.mem_reverse]
      exact hv_not
  have hlen : q.length = p.length + 3 := by
    simp [q, Walk.length_cons, Walk.length_reverse]
    omega
  have hq_cyc : q.IsCycle := by
    rw [Walk.isCycle_def]
    refine ⟨?_, ?_, htail_nodup⟩
    · rw [Walk.isTrail_def]
      simp only [q, Walk.edges_cons, List.nodup_cons]
      have hrev_edges_nodup : p.reverse.edges.Nodup := hrev_path.isTrail.edges_nodup
      have h_no_u : ∀ e ∈ p.reverse.edges, u ∉ e := by
        intro e he hmem
        rcases Sym2.mem_iff_exists.mp hmem with ⟨w, rfl⟩
        exact hu_not (Walk.support_reverse p ▸ List.mem_reverse.mpr
          (Walk.fst_mem_support_of_mem_edges p.reverse he))
      have h_no_v : ∀ e ∈ p.reverse.edges, v ∉ e := by
        intro e he hmem
        rcases Sym2.mem_iff_exists.mp hmem with ⟨w, rfl⟩
        exact hv_not (Walk.support_reverse p ▸ List.mem_reverse.mpr
          (Walk.fst_mem_support_of_mem_edges p.reverse he))
      refine ⟨?_, ?_, ?_, hrev_edges_nodup⟩
      · simp only [List.mem_cons, not_or, Sym2.eq_iff]
        refine ⟨?_, ?_, ?_⟩
        · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · exact hne_ua rfl
          · exact hne_va.symm rfl
        · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · exact hne_va.symm rfl
          · exact hne_uc rfl
        · intro hm
          exact h_no_u s(a, u) hm (Sym2.mem_mk_right a u)
      · simp only [List.mem_cons, not_or, Sym2.eq_iff]
        refine ⟨?_, ?_⟩
        · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · exact hne_uv rfl
          · exact hne_uc rfl
        · intro hm
          exact h_no_u s(u, v) hm (Sym2.mem_mk_left u v)
      · intro hm
        exact h_no_v s(v, c) hm (Sym2.mem_mk_left v c)
    · simp [q]
  exact ⟨a, q, hq_cyc, hlen⟩

/--
Theorem 4 (`crossRewire_single_edge_lifts_to_cycle_plus_two`):
**True Graph-Theoretic Type (L1) Lifting**: Any simple path `p : G.Walk a c` of length `2^k - 1`
(`k ≥ 2`) in `G - {u, v}` lifts via `a - u - v - c` to a simple `(2^k + 2)`-cycle in `G`.
-/
theorem crossRewire_single_edge_lifts_to_cycle_plus_two {V : Type*} (G : SimpleGraph V)
    {u v a c : V} {k : ℕ} (hk : 2 ≤ k)
    (p : G.Walk a c) (hp : p.IsPath) (hlen : p.length = 2 ^ k - 1)
    (huv : G.Adj u v) (hua : G.Adj u a) (hvc : G.Adj v c)
    (hu_not : u ∉ p.support) (hv_not : v ∉ p.support) (hac : a ≠ c) :
    HasCycleLen G (2 ^ k + 2) := by
  have h4 : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
  have h := cycle_of_path_and_edge_bridge G p hp huv hua hvc hu_not hv_not hac
  have heq : p.length + 3 = 2 ^ k + 2 := by omega
  exact heq ▸ h

/-- Helper: constructing a simple cycle from two vertex-disjoint simple paths `p₁ : a ↝ d`
and `p₂ : b ↝ c` closed by `a - u - b` and `c - v - d`. -/
lemma cycle_of_two_disjoint_paths_and_two_cherries {V : Type*} (G : SimpleGraph V)
    {u v a b c d : V}
    (p₁ : G.Walk a d) (hp₁ : p₁.IsPath)
    (p₂ : G.Walk b c) (hp₂ : p₂.IsPath)
    (hdisj : ∀ x, x ∈ p₁.support → x ∉ p₂.support)
    (hua : G.Adj u a) (hub : G.Adj u b) (hvc : G.Adj v c) (hvd : G.Adj v d)
    (hu₁ : u ∉ p₁.support) (hu₂ : u ∉ p₂.support)
    (hv₁ : v ∉ p₁.support) (hv₂ : v ∉ p₂.support)
    (huv_ne : u ≠ v) :
    HasCycleLen G (p₁.length + p₂.length + 4) := by
  let w₁ : G.Walk u d := Walk.cons hua p₁
  let w₂ : G.Walk v b := Walk.cons hvc p₂.reverse
  let q : G.Walk u u := w₁.append (Walk.cons hvd.symm (w₂.append (Walk.cons hub.symm Walk.nil)))
  have hlen : q.length = p₁.length + p₂.length + 4 := by
    simp [q, w₁, w₂, Walk.length_append, Walk.length_cons, Walk.length_reverse]
    omega
  have htail : q.support.tail = p₁.support ++ v :: p₂.reverse.support ++ [u] := by
    simp [q, w₁, w₂, Walk.support_append, Walk.support_cons, Walk.support_nil, List.append_assoc]
  have htail_nodup : q.support.tail.Nodup := by
    rw [htail]
    have hp1n : p₁.support.Nodup := hp₁.support_nodup
    have hp2n : p₂.reverse.support.Nodup := hp₂.reverse.support_nodup
    rw [List.nodup_append, List.nodup_append]
    refine ⟨⟨hp1n, ?_, ?_⟩, List.nodup_singleton u, ?_⟩
    · rw [List.nodup_cons]
      exact ⟨by simp [Walk.support_reverse, hv₂], hp2n⟩
    · intro x hx1 hx2
      simp only [List.mem_cons, Walk.support_reverse, List.mem_reverse] at hx2
      rcases hx2 with rfl | hx2
      · exact hv₁ hx1
      · exact hdisj x hx1 hx2
    · intro x hx hxu
      simp only [List.mem_singleton] at hxu
      subst hxu
      simp only [List.mem_append, List.mem_cons, Walk.support_reverse, List.mem_reverse] at hx
      rcases hx with hu | rfl | hu
      · exact hu₁ hu
      · exact huv_ne rfl
      · exact hu₂ hu
  have hq_cyc : q.IsCycle := by
    rw [Walk.isCycle_def]
    refine ⟨?_, ?_, htail_nodup⟩
    · rw [Walk.isTrail_def]
      have he_q : q.edges = s(u, a) :: (p₁.edges ++ (s(d, v) :: s(v, c) :: (p₂.reverse.edges ++ [s(b, u)]))) := by
        simp [q, w₁, w₂, Walk.edges_append, Walk.edges_cons, Walk.edges_nil, List.append_assoc]
      rw [he_q]
      have ha_mem : a ∈ p₁.support := Walk.start_mem_support p₁
      have hd_mem : d ∈ p₁.support := Walk.end_mem_support p₁
      have hb_mem : b ∈ p₂.support := Walk.start_mem_support p₂
      have hc_mem : c ∈ p₂.support := Walk.end_mem_support p₂
      have hab : a ≠ b := fun h => hdisj a ha_mem (h ▸ hb_mem)
      have hdb : d ≠ b := fun h => hdisj d hd_mem (h ▸ hb_mem)
      have hdc : d ≠ c := fun h => hdisj d hd_mem (h ▸ hc_mem)
      have h_no_u1 : ∀ e ∈ p₁.edges, u ∉ e := fun e he hm => by
        rcases Sym2.mem_iff_exists.mp hm with ⟨w, rfl⟩
        exact hu₁ (Walk.fst_mem_support_of_mem_edges p₁ he)
      have h_no_v1 : ∀ e ∈ p₁.edges, v ∉ e := fun e he hm => by
        rcases Sym2.mem_iff_exists.mp hm with ⟨w, rfl⟩
        exact hv₁ (Walk.fst_mem_support_of_mem_edges p₁ he)
      have h_no_u2 : ∀ e ∈ p₂.reverse.edges, u ∉ e := fun e he hm => by
        rcases Sym2.mem_iff_exists.mp hm with ⟨w, rfl⟩
        exact hu₂ (Walk.support_reverse p₂ ▸ List.mem_reverse.mpr
          (Walk.fst_mem_support_of_mem_edges p₂.reverse he))
      have h_no_v2 : ∀ e ∈ p₂.reverse.edges, v ∉ e := fun e he hm => by
        rcases Sym2.mem_iff_exists.mp hm with ⟨w, rfl⟩
        exact hv₂ (Walk.support_reverse p₂ ▸ List.mem_reverse.mpr
          (Walk.fst_mem_support_of_mem_edges p₂.reverse he))
      have h_disj_e : ∀ e ∈ p₁.edges, e ∉ p₂.reverse.edges := fun e he1 he2 => by
        induction e using Sym2.ind with
        | _ x y =>
          exact hdisj x (Walk.fst_mem_support_of_mem_edges p₁ he1)
            (Walk.support_reverse p₂ ▸ List.mem_reverse.mpr
              (Walk.fst_mem_support_of_mem_edges p₂.reverse he2))
      rw [List.nodup_cons]
      refine ⟨?_, ?_⟩
      · simp only [List.mem_append, List.mem_cons, List.mem_singleton, not_or, Sym2.eq_iff]
        refine ⟨fun hm => h_no_u1 s(u, a) hm (Sym2.mem_mk_left u a), ?_, ?_, ?_, ?_⟩
        · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · exact hu₁ hd_mem
          · exact huv_ne rfl
        · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · exact huv_ne rfl
          · exact hu₂ hc_mem
        · intro hm; exact h_no_u2 s(u, a) hm (Sym2.mem_mk_left u a)
        · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · exact hu₂ hb_mem
          · exact hab rfl
      · rw [List.nodup_append]
        refine ⟨hp₁.isTrail.edges_nodup, ?_, ?_⟩
        · rw [List.nodup_cons, List.nodup_cons]
          refine ⟨?_, ?_, ?_⟩
          · simp only [List.mem_cons, List.mem_append, List.mem_singleton, not_or, Sym2.eq_iff]
            refine ⟨?_, fun hm => h_no_v2 s(d, v) hm (Sym2.mem_mk_right d v), ?_⟩
            · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
              · exact hv₁ hd_mem
              · exact hdc rfl
            · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
              · exact hdb rfl
              · exact huv_ne.symm rfl
          · simp only [List.mem_append, List.mem_singleton, not_or, Sym2.eq_iff]
            refine ⟨fun hm => h_no_v2 s(v, c) hm (Sym2.mem_mk_left v c), ?_⟩
            rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
            · exact hv₂ hb_mem
            · exact huv_ne rfl
          · rw [List.nodup_append]
            refine ⟨hp₂.reverse.isTrail.edges_nodup, List.nodup_singleton _, ?_⟩
            intro e he hbu
            rw [List.mem_singleton] at hbu
            subst hbu
            exact h_no_u2 s(b, u) he (Sym2.mem_mk_right b u)
        · intro e he1 he2
          simp only [List.mem_cons, List.mem_append, List.mem_singleton] at he2
          rcases he2 with rfl | rfl | he2 | rfl
          · exact h_no_v1 s(d, v) he1 (Sym2.mem_mk_right d v)
          · exact h_no_v1 s(v, c) he1 (Sym2.mem_mk_left v c)
          · exact h_disj_e e he1 he2
          · exact h_no_u1 s(b, u) he1 (Sym2.mem_mk_right b u)
    · simp [q, w₁, Walk.nil_append]
  exact ⟨u, q, hq_cyc, hlen⟩

/--
Theorem 5 (`crossRewire_twisted_double_lifts_three_cycles`):
**True Graph-Theoretic Type (L2) Lifting**: Two vertex-disjoint simple paths `p₁ : a ↝ d` and
`p₂ : b ↝ c` in `G - {u, v}` with `p₁.length + p₂.length = 2^k - 2` (`k ≥ 2`) simultaneously
produce **three** simple cycles in `G`:
1. a `(2^k + 2)`-cycle avoiding `uv`,
2. a `(p₁.length + 3)`-cycle through `uv`, and
3. a `(p₂.length + 3)`-cycle through `uv`.
-/
theorem crossRewire_twisted_double_lifts_three_cycles {V : Type*} (G : SimpleGraph V)
    {u v a b c d : V} {k : ℕ} (hk : 2 ≤ k)
    (p₁ : G.Walk a d) (hp₁ : p₁.IsPath)
    (p₂ : G.Walk b c) (hp₂ : p₂.IsPath)
    (hsum : p₁.length + p₂.length = 2 ^ k - 2)
    (hdisj : ∀ x, x ∈ p₁.support → x ∉ p₂.support)
    (huv : G.Adj u v) (hua : G.Adj u a) (hub : G.Adj u b)
    (hvc : G.Adj v c) (hvd : G.Adj v d)
    (hu₁ : u ∉ p₁.support) (hu₂ : u ∉ p₂.support)
    (hv₁ : v ∉ p₁.support) (hv₂ : v ∉ p₂.support)
    (had : a ≠ d) (hbc : b ≠ c) :
    HasCycleLen G (2 ^ k + 2) ∧
    HasCycleLen G (p₁.length + 3) ∧
    HasCycleLen G (p₂.length + 3) := by
  have h4 : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
  have h1 := cycle_of_two_disjoint_paths_and_two_cherries G p₁ hp₁ p₂ hp₂ hdisj
    hua hub hvc hvd hu₁ hu₂ hv₁ hv₂ (G.ne_of_adj huv)
  have heq : p₁.length + p₂.length + 4 = 2 ^ k + 2 := by omega
  have h2 := cycle_of_path_and_edge_bridge G p₁ hp₁ huv hua hvd hu₁ hv₁ had
  have h3 := cycle_of_path_and_edge_bridge G p₂ hp₂ huv hub hvc hu₂ hv₂ hbc
  exact ⟨heq ▸ h1, h2, h3⟩

/-- Helper: closing a simple path `p : a ↝ b` (length ≥ 1) via a single cherry `a - u - b`
avoiding `p.support` gives a simple `(p.length + 2)`-cycle. -/
lemma cycle_of_path_and_cherry {V : Type*} (G : SimpleGraph V)
    {u a b : V} (p : G.Walk a b) (hp : p.IsPath) (hlen1 : 1 ≤ p.length)
    (hua : G.Adj u a) (hub : G.Adj u b) (hu_not : u ∉ p.support) :
    ∃ q : G.Walk u u, q.IsCycle ∧ q.length = p.length + 2 ∧
      ∀ x ∈ q.support, x = u ∨ x ∈ p.support := by
  let q : G.Walk u u := Walk.cons hua (p.append (Walk.cons hub.symm Walk.nil))
  have hlen : q.length = p.length + 2 := by
    simp [q, Walk.length_cons, Walk.length_append]
  have hsup : q.support = u :: (p.support ++ [u]) := by
    simp [q, Walk.support_cons, Walk.support_append, Walk.support_nil]
  have htail_nodup : q.support.tail.Nodup := by
    rw [hsup, List.tail_cons, List.nodup_append]
    refine ⟨hp.support_nodup, List.nodup_singleton u, ?_⟩
    intro x hx hxu
    rw [List.mem_singleton] at hxu
    exact hu_not (hxu ▸ hx)
  have hne_ab : a ≠ b := by
    intro h; subst h
    cases p with
    | nil => simp at hlen1
    | cons hadj r =>
      have := hp.support_nodup
      simp only [Walk.support_cons, List.nodup_cons] at this
      exact this.1 (Walk.end_mem_support r)
  have h_no_u : ∀ e ∈ p.edges, u ∉ e := fun e he hm => by
    rcases Sym2.mem_iff_exists.mp hm with ⟨w, rfl⟩
    exact hu_not (Walk.fst_mem_support_of_mem_edges p he)
  have hq_cyc : q.IsCycle := by
    rw [Walk.isCycle_def]
    refine ⟨?_, ?_, htail_nodup⟩
    · rw [Walk.isTrail_def]
      have heq : q.edges = s(u, a) :: (p.edges ++ [s(b, u)]) := by
        simp [q, Walk.edges_cons, Walk.edges_append, Walk.edges_nil]
      rw [heq, List.nodup_cons]
      refine ⟨?_, ?_⟩
      · simp only [List.mem_append, List.mem_singleton, not_or, Sym2.eq_iff]
        refine ⟨fun hm => h_no_u s(u, a) hm (Sym2.mem_mk_left u a), ?_⟩
        rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact hu_not (Walk.end_mem_support p)
        · exact hne_ab rfl
      · rw [List.nodup_append]
        refine ⟨hp.isTrail.edges_nodup, List.nodup_singleton _, ?_⟩
        intro e he hbu
        rw [List.mem_singleton] at hbu
        subst hbu
        exact h_no_u s(b, u) he (Sym2.mem_mk_right b u)
    · simp [q]
  refine ⟨q, hq_cyc, hlen, ?_⟩
  intro x hx
  rw [hsup] at hx
  simp only [List.mem_cons, List.mem_append, List.mem_singleton] at hx
  rcases hx with rfl | hx | rfl
  · exact Or.inl rfl
  · exact Or.inr hx
  · exact Or.inl rfl

/--
Theorem 6 (`crossRewire_parallel_double_lifts_dumbbell`):
**True Graph-Theoretic Type (L3) Dumbbell Lifting**: Two vertex-disjoint simple paths
`qᵤ : a ↝ b` and `qᵥ : c ↝ d` (both of length ≥ 1) in `G - {u, v}` with
`qᵤ.length + qᵥ.length = 2^k - 2` (`k ≥ 2`) lift to **two vertex-disjoint simple cycles**
`Cᵤ` (through `u`) and `Cᵥ` (through `v`) in `G` with `Cᵤ.length + Cᵥ.length = 2^k + 2`.
-/
theorem crossRewire_parallel_double_lifts_dumbbell {V : Type*} (G : SimpleGraph V)
    {u v a b c d : V} {k : ℕ} (hk : 2 ≤ k)
    (qᵤ : G.Walk a b) (hqᵤ : qᵤ.IsPath) (hlu : 1 ≤ qᵤ.length)
    (qᵥ : G.Walk c d) (hqᵥ : qᵥ.IsPath) (hlv : 1 ≤ qᵥ.length)
    (hsum : qᵤ.length + qᵥ.length = 2 ^ k - 2)
    (hdisj : ∀ x, x ∈ qᵤ.support → x ∉ qᵥ.support)
    (huv_ne : u ≠ v) (hua : G.Adj u a) (hub : G.Adj u b)
    (hvc : G.Adj v c) (hvd : G.Adj v d)
    (hu₁ : u ∉ qᵤ.support) (hu₂ : u ∉ qᵥ.support)
    (hv₁ : v ∉ qᵤ.support) (hv₂ : v ∉ qᵥ.support) :
    ∃ (Cᵤ : G.Walk u u) (Cᵥ : G.Walk v v),
      Cᵤ.IsCycle ∧ Cᵥ.IsCycle ∧
      Cᵤ.length + Cᵥ.length = 2 ^ k + 2 ∧
      (∀ x, x ∈ Cᵤ.support → x ∉ Cᵥ.support) := by
  have h4 : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
  rcases cycle_of_path_and_cherry G qᵤ hqᵤ hlu hua hub hu₁ with ⟨Cᵤ, hCu, hlenu, hsupu⟩
  rcases cycle_of_path_and_cherry G qᵥ hqᵥ hlv hvc hvd hv₂ with ⟨Cᵥ, hCv, hlenv, hsupv⟩
  refine ⟨Cᵤ, Cᵥ, hCu, hCv, by omega, ?_⟩
  intro x hxu hxv
  rcases hsupu x hxu with rfl | hxu'
  · rcases hsupv u hxv with h | h
    · exact huv_ne h
    · exact hu₂ h
  · rcases hsupv x hxv with rfl | hxv'
    · exact hv₁ hxu'
    · exact hdisj x hxu' hxv'

/--
Theorem 7 (`dual_cross_rewiring_girth_double_cross_bounds`):
In any graph `G` with `GirthGe G g`:
- Every Type (L2) twisted double-cross lift at scale `k` forces `2 * g ≤ 2 ^ k + 4`,
- Every Type (L3) dumbbell lift at scale `k` forces `2 * g ≤ 2 ^ k + 2`.
In particular, for `g ≥ 5`, no `C₄` (`k = 2`) can be Type (L2) or (L3); for `g ≥ 7`, neither
`C₄` nor `C₈` (`k ≤ 3`) can be Type (L2) or (L3).
-/
theorem dual_cross_rewiring_girth_double_cross_bounds {V : Type*} (G : SimpleGraph V)
    {g k ℓ₁ ℓ₂ : ℕ} (hg : GirthGe G g) (hk : 2 ≤ k)
    (hsum : ℓ₁ + ℓ₂ = 2 ^ k - 2) :
    ((HasCycleLen G (ℓ₁ + 3) ∧ HasCycleLen G (ℓ₂ + 3)) → 2 * g ≤ 2 ^ k + 4) ∧
    ((HasCycleLen G (ℓ₁ + 2) ∧ HasCycleLen G (ℓ₂ + 2)) → 2 * g ≤ 2 ^ k + 2) := by
  have h4 : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
  constructor
  · rintro ⟨⟨v₁, c₁, hc₁, hl₁⟩, ⟨v₂, c₂, hc₂, hl₂⟩⟩
    have hg1 := hg v₁ c₁ hc₁
    have hg2 := hg v₂ c₂ hc₂
    omega
  · rintro ⟨⟨v₁, c₁, hc₁, hl₁⟩, ⟨v₂, c₂, hc₂, hl₂⟩⟩
    have hg1 := hg v₁ c₁ hc₁
    have hg2 := hg v₂ c₂ hc₂
    omega

/--
Theorem 8 (`dual_cross_rewiring_same_scale_L1_must_intersect`):
**Simultaneous 2-Pairing Symmetry Theorem**: Because every edge in `{ac, bd}` shares an endpoint
with every edge in `{ad, bc}`, if both cross-rewirings `G_×^(1)(uv)` and `G_×^(2)(uv)` yield
Type (L1) lifts at the **same** scale `k ≥ 2` (yielding paths `p₁ : a ↝ c` and `p₂ : a ↝ d`
of length `2^k - 1` in `G - {u, v}`), then `p₁` and `p₂` **cannot be internally vertex-disjoint**
in any `PowerFree` graph `G` (otherwise `p₁ ∪ p₂` closed via `c - v - d` is a `2^(k+1)`-cycle).
-/
theorem dual_cross_rewiring_same_scale_L1_must_intersect {V : Type*} (G : SimpleGraph V)
    (hpf : PowerFree G) {v a c d : V} {k : ℕ} (hk : 2 ≤ k)
    (p₁ : G.Walk a c) (hp₁ : p₁.IsPath) (hl₁ : p₁.length = 2 ^ k - 1)
    (p₂ : G.Walk a d) (hp₂ : p₂.IsPath) (hl₂ : p₂.length = 2 ^ k - 1)
    (hvc : G.Adj v c) (hvd : G.Adj v d)
    (hv₁ : v ∉ p₁.support) (hv₂ : v ∉ p₂.support) :
    ∃ x : V, x ≠ a ∧ x ∈ p₁.support ∧ x ∈ p₂.support := by
  by_contra hno
  push_neg at hno
  let p : G.Walk c d := p₁.reverse.append p₂
  have hp_len : p.length = 2 * (2 ^ k - 1) := by
    simp [p, Walk.length_append, Walk.length_reverse, hl₁, hl₂]; omega
  have h4 : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
  have hp_path : p.IsPath := by
    rw [Walk.isPath_def]
    have hsup : p.support = p₁.reverse.support ++ p₂.support.tail := Walk.support_append _ _
    rw [hsup, List.nodup_append]
    refine ⟨hp₁.reverse.support_nodup, hp₂.support_nodup.tail, ?_⟩
    intro x hx1 hx2
    have hx1' : x ∈ p₁.support := List.mem_reverse.mp (Walk.support_reverse p₁ ▸ hx1)
    have hx2' : x ∈ p₂.support := List.mem_of_mem_tail hx2
    have hxa : x ≠ a := by
      intro h; subst h
      have hnd := hp₂.support_nodup
      cases hp2_eq : p₂ with
      | nil => simp [hp2_eq] at hx2
      | cons hadj r =>
        rw [hp2_eq, Walk.support_cons, List.tail_cons] at hx2
        rw [hp2_eq, Walk.support_cons, List.nodup_cons] at hnd
        exact hnd.1 hx2
    exact hno x hxa hx1' hx2'
  have hv_not : v ∉ p.support := by
    rw [Walk.support_append]
    intro hm
    rcases List.mem_append.mp hm with h1 | h2
    · exact hv₁ (List.mem_reverse.mp (Walk.support_reverse p₁ ▸ h1))
    · exact hv₂ (List.mem_of_mem_tail h2)
  rcases cycle_of_path_and_cherry G p hp_path (by omega) hvc hvd hv_not with
    ⟨q, hq_cyc, hq_len, _⟩
  have hpow : IsPow2 q.length := by
    refine ⟨k + 1, by omega, ?_⟩
    rw [hq_len, hp_len, pow_succ]
    omega
  exact hpf ⟨v, q, hq_cyc, hpow⟩

end E64Wave8Agent3P1
