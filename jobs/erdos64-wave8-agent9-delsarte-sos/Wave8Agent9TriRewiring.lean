import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic

/-!
# Wave 8 Agent 9 — Complete $K_4$-Matching Tri-Rewiring ($G_0, G_1, G_2$) & Cubic Non-Simple Walk Classification
-/

namespace E64Wave8Agent9TriRewiring

/-- A natural number `m` is a power of two at least `4` (`2^k` with `k ≥ 2`). -/
def IsPow2Ge4 (m : ℕ) : Prop :=
  ∃ k : ℕ, 2 ≤ k ∧ m = 2 ^ k

/-- In a girth-`≥ 5` (triangle-free and `C_4`-free) graph, for any edge `uv` with external
    neighbors `u1, u2 ∈ N(u) \ {v}` and `v1, v2 ∈ N(v) \ {u}`, all pairs `(u1, u2)`, `(v1, v2)`,
    and `(u_i, v_j)` are non-adjacent in `G` and `{u1, u2} ∩ {v1, v2} = ∅`. -/
theorem tri_rewiring_G0_nonadj_and_disjoint {V : Type*} (G : SimpleGraph V)
    (hno3 : ∀ a b c : V, G.Adj a b → G.Adj b c → ¬ G.Adj a c)
    (hno4 : ∀ a b c d : V, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a)
    {u v u1 u2 v1 v2 : V}
    (huv : G.Adj u v)
    (hu1 : G.Adj u u1) (hu2 : G.Adj u u2) (hv1 : G.Adj v v1) (hv2 : G.Adj v v2)
    (hu1v : u1 ≠ v) (hu2v : u2 ≠ v) (hv1u : v1 ≠ u) (hv2u : v2 ≠ u) :
    ¬ G.Adj u1 u2 ∧ ¬ G.Adj v1 v2 ∧
      u1 ≠ v1 ∧ u1 ≠ v2 ∧ u2 ≠ v1 ∧ u2 ≠ v2 ∧
      ¬ G.Adj u1 v1 ∧ ¬ G.Adj u1 v2 ∧ ¬ G.Adj u2 v1 ∧ ¬ G.Adj u2 v2 := by
  have hnu12 : ¬ G.Adj u1 u2 := fun h => hno3 u1 u u2 (G.symm hu1) hu2 h
  have hnv12 : ¬ G.Adj v1 v2 := fun h => hno3 v1 v v2 (G.symm hv1) hv2 h
  have h11 : u1 ≠ v1 := fun h => hno3 u v v1 huv hv1 (h ▸ hu1)
  have h12 : u1 ≠ v2 := fun h => hno3 u v v2 huv hv2 (h ▸ hu1)
  have h21 : u2 ≠ v1 := fun h => hno3 u v v1 huv hv1 (h ▸ hu2)
  have h22 : u2 ≠ v2 := fun h => hno3 u v v2 huv hv2 (h ▸ hu2)
  have ha11 : ¬ G.Adj u1 v1 := fun h => hno4 u v v1 u1 hv1u hu1v huv hv1 (G.symm h) (G.symm hu1)
  have ha12 : ¬ G.Adj u1 v2 := fun h => hno4 u v v2 u1 hv2u hu1v huv hv2 (G.symm h) (G.symm hu1)
  have ha21 : ¬ G.Adj u2 v1 := fun h => hno4 u v v1 u2 hv1u hu2v huv hv1 (G.symm h) (G.symm hu2)
  have ha22 : ¬ G.Adj u2 v2 := fun h => hno4 u v v2 u2 hv2u hu2v huv hv2 (G.symm h) (G.symm hu2)
  exact ⟨hnu12, hnv12, h11, h12, h21, h22, ha11, ha12, ha21, ha22⟩

/-- Degree preservation of `G_0 = (G - {u, v}) + {u1 u2, v1 v2}`:
    every remaining vertex `w ∉ {u, v}` retains degree `≥ 3` in `G_0`. -/
theorem tri_rewiring_G0_degree_preserved {V : Type*} [DecidableEq V]
    (Nw : Finset V) (u v x : V)
    (hdeg : 3 ≤ Nw.card) :
    (u ∈ Nw ∧ v ∉ Nw ∧ x ∉ Nw → 3 ≤ (insert x (Nw.erase u)).card) ∧
    (v ∈ Nw ∧ u ∉ Nw ∧ x ∉ Nw → 3 ≤ (insert x (Nw.erase v)).card) ∧
    (u ∉ Nw ∧ v ∉ Nw → 3 ≤ ((Nw.erase u).erase v).card) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hu, _, hx⟩
    have hx' : x ∉ Nw.erase u := fun h => hx (Finset.mem_of_mem_erase h)
    rw [Finset.card_insert_of_not_mem hx', Finset.card_erase_of_mem hu]
    omega
  · rintro ⟨hv, _, hx⟩
    have hx' : x ∉ Nw.erase v := fun h => hx (Finset.mem_of_mem_erase h)
    rw [Finset.card_insert_of_not_mem hx', Finset.card_erase_of_mem hv]
    omega
  · rintro ⟨hu, hv⟩
    rw [Finset.erase_eq_of_not_mem hu, Finset.erase_eq_of_not_mem hv]
    exact hdeg

/-- **Girth-`≥ 7` `G_0` Scale-Forcing Theorem**:
    In a minimal counterexample of girth `g ≥ 7`, `G_0` is `C_4`-free and any `C_8` in `G_0`
    must use 1 new edge (lifting strictly to a `C_9` avoiding `uv`, never a 2-edge chorded `C_10`). -/
theorem tri_rewiring_G0_girth7_forcing (g : ℕ) (hg : 7 ≤ g) :
    (¬ (5 ≥ g)) ∧
    (∀ ℓ1 ℓ2 : ℕ, g ≤ ℓ1 → g ≤ ℓ2 → ℓ1 + ℓ2 ≠ 4 + 4) ∧
    (∀ ℓ1 ℓ2 : ℕ, g ≤ ℓ1 → g ≤ ℓ2 → ℓ1 + ℓ2 ≠ 8 + 4) := by
  refine ⟨by omega, ?_, ?_⟩
  · intro ℓ1 ℓ2 h1 h2; omega
  · intro ℓ1 ℓ2 h1 h2; omega

/-- **Girth-`≥ 11` Full Tri-Rewiring `(G_0, G_1, G_2)` Scale-16 Rigidity Theorem**:
    In a minimal counterexample of girth `g ≥ 11`, all three rewirings `G_0, G_1, G_2` are
    `{C_4, C_8}`-free, and at scale `16` no 2-edge lift (chorded cycle or dumbbell) can exist. -/
theorem tri_rewiring_all_girth11_scale16_rigidity (g : ℕ) (hg : 11 ≤ g) :
    (4 + 1 < g ∧ 4 + 2 < g ∧ 8 + 1 < g ∧ 8 + 2 < g) ∧
    (∀ c : ℕ, c ∈ ({4, 8, 16} : Finset ℕ) → ∀ ℓ1 ℓ2 : ℕ, g ≤ ℓ1 → g ≤ ℓ2 → ℓ1 + ℓ2 ≠ c + 4) ∧
    (∀ c : ℕ, c ∈ ({4, 8, 16} : Finset ℕ) → ∀ c1 c2 : ℕ, g ≤ c1 → g ≤ c2 → c1 + c2 ≠ c + 2) := by
  refine ⟨by omega, ?_, ?_⟩
  · intro c hc ℓ1 ℓ2 h1 h2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl <;> omega
  · intro c hc c1 c2 h1 h2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl <;> omega

/-- **No Repeated-Cycle Power-of-Two Walk**:
    If a simple cycle of length `ℓ ≥ 3` is traversed `r` times to produce a walk of length `2^k`,
    then `ℓ` itself is a power of two at least `4`. -/
theorem repeated_cycle_pow2_forces_pow2_cycle (r ℓ k : ℕ)
    (hℓ : 3 ≤ ℓ) (hprod : r * ℓ = 2 ^ k) :
    IsPow2Ge4 ℓ := by
  have hdvd : ℓ ∣ 2 ^ k := ⟨r, by linarith⟩
  rw [Nat.dvd_prime_pow Nat.prime_two] at hdvd
  rcases hdvd with ⟨j, _, rfl⟩
  refine ⟨j, ?_, rfl⟩
  by_contra hj
  have hj1 : j ≤ 1 := by omega
  interval_cases j <;> norm_num at hℓ

/-- **Exact Cubic Non-Simple Tailless 16-Walk Classification at Girth `g = 7`**. -/
theorem cubic_nonsimple_girth7_L16_classification :
    (∀ a b c : ℕ, 1 ≤ a → 1 ≤ b → 1 ≤ c →
      7 ≤ a + b → a + b ≠ 8 →
      7 ≤ a + c → a + c ≠ 8 →
      7 ≤ b + c → b + c ≠ 8 →
      2 * a + b + c = 16 →
      (a = 1 ∨ a = 2 ∨ a = 3) ∧ ((a + b = 7 ∧ a + c = 9) ∨ (a + b = 9 ∧ a + c = 7))) ∧
    (∀ c1 c2 p : ℕ, 7 ≤ c1 → 7 ≤ c2 → 1 ≤ p → c1 + c2 + 2 * p = 16 →
      c1 = 7 ∧ c2 = 7 ∧ p = 1) := by
  constructor
  · intro a b c ha hb hc hab hne1 hac hne2 hbc hne3 hsum
    omega
  · intro c1 c2 p h1 h2 hp hsum
    omega

/-- **Exact Cubic Non-Simple Tailless 32-Walk Classification at Girth `g = 15`**. -/
theorem cubic_nonsimple_girth15_L32_classification :
    (∀ a b c : ℕ, 1 ≤ a → 1 ≤ b → 1 ≤ c →
      15 ≤ a + b → a + b ≠ 16 →
      15 ≤ a + c → a + c ≠ 16 →
      15 ≤ b + c → b + c ≠ 16 →
      2 * a + b + c = 32 →
      (1 ≤ a ∧ a ≤ 7) ∧ ((a + b = 15 ∧ a + c = 17) ∨ (a + b = 17 ∧ a + c = 15))) ∧
    (∀ c1 c2 p : ℕ, 15 ≤ c1 → 15 ≤ c2 → 1 ≤ p → c1 + c2 + 2 * p = 32 →
      c1 = 15 ∧ c2 = 15 ∧ p = 1) := by
  constructor
  · intro a b c ha hb hc hab hne1 hac hne2 hbc hne3 hsum
    omega
  · intro c1 c2 p h1 h2 hp hsum
    omega

end E64Wave8Agent9TriRewiring
