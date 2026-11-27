import Shadow
import Wave6Agent3KestenMcKayBreak
import Wave7Agent6CycleIntervalForcing

/-!
# Wave 8 Agent #1: Multi-Layer (r ≥ 3) BFS-Shell Dichotomy, Asymmetric BFS-LCA Lifting & Heterogeneous Adjuster Chains for Erdős Problem #64

Building directly on Wave 7 Agent #6's `cubic_two_layer_no_chorded_cycle` (`E64Wave7Agent6`),
we formalize 18 unconditional structural theorems directly on `SimpleGraph V` in Lean 4.36.0
across four pillars:

1. **Pillar 1 — Sharp Multi-Layer (`r = 2, 3, 4`) Cubic BFS-Shell Dichotomy & Handshaking Excess**:
   - `cubic_bfs_interior_full_degree`: Every interior vertex `u ∈ L_j` (`i < j < i + r - 1`) of an
     `r`-layer BFS shell `S_{i,r}` (`r ≥ 3`) in a cubic graph retains full degree `3` inside `S_{i,r}`.
   - `cubic_bfs_top_layer_deg_le_two` & `cubic_bfs_bottom_expanding_deg_le_two`: Boundary vertices
     with an external neighbor have degree `≤ 2` inside `S_{i,r}`.
   - `cubic_two_layer_expanding_max_deg_le_two`: Strengthens Wave 7's 2-layer obstruction — in any
     strictly expanding 2-layer BFS shell of a cubic graph, EVERY vertex has degree `≤ 2` (blocking
     not only chorded cycles, but ALL `Θ`-graphs, bipartite or non-bipartite).
   - `cubic_three_layer_bipartite_chorded_forces_sink`: Any bipartite 3-layer BFS shell `S_{i,3}`
     of a cubic graph containing a `ChordedEvenCycle G m r` MUST contain a dead-end sink in `L_{i+2}`
     (zero neighbors in `L_{i+3}`) among the two chord endpoints `{v_0, v_{2r+1}}`.
   - `cubic_three_layer_expanding_no_bipartite_chorded_cycle`: No strictly expanding bipartite
     3-layer BFS shell of a cubic graph contains any `ChordedEvenCycle` (pinning `r = 4` as the
     exact sharp threshold where both interior layers `L_{i+1}, L_{i+2}` retain degree `3`).
   - `cubic_bfs_shell_degree_cut_identity`: Exact handshaking balance
     `∑_{u ∈ S} deg_S(u) + ∑_{u ∈ S} deg_{S^c}(u) = 3 * |S|` for any vertex set `S` in a cubic graph.

2. **Pillar 2 — Multi-Layer Asymmetric-Depth BFS-LCA Lifting & Girth-vs-Height Closure**:
   - `multilayer_asymmetric_bfs_lca_cycle_interval`: Lifts any `ChordedEvenCycle G m r` through a
     multi-layer BFS tree with constant cross-color path length `D = h_0 + h_1 ≥ 2` (e.g. `L_i` vs
     `L_{i+2}` in a 3- or 4-layer shell) to force EVERY cycle length `D + 2k` (`1 ≤ k ≤ m - 1`).
   - `hasPower_of_multilayer_asymmetric_bfs_chorded_cycle`: Unbounded-`n` `HasPower G` whenever
     `D = 2 * H` (`H ≥ 1`) and `H + 1 ≤ m`.
   - `chorded_even_cycle_girth_lower_bound`: In any graph of girth `≥ g`, every `ChordedEvenCycle G m r`
     satisfies `g - 1 ≤ m` (`2 * g - 2 ≤ 2 * m`).
   - `hasPower_of_girth_bounded_height_chorded_cycle`: Unconditional `HasPower G` whenever a
     multi-layer BFS chorded cycle in a girth-`≥ g` graph has asymmetric half-height `H ≤ g - 2`.

3. **Pillar 3 — Heterogeneous (`O(log L_0)`) Subset-Sum `HetAdjusterChain` & Brown Completeness**:
   - Generalizes Wave 7's uniform-step `AdjusterChain G δ` to arbitrary per-adjuster steps
     `δ_1, ..., δ_r ≥ 1`, proving `realize_length`, `realize_isCycle`, `brown_completeness`,
     `exists_cycle_of_even_brown_complete`, `hasPower_of_even_brown_complete` (requiring only
     `O(log a)` dyadic adjusters instead of `a - 2`), and `hasPower_of_subset_sum_hit`.

4. **Pillar 4 — Multi-Step Parity-Flip Interval Lifting (Generalized Gao–Li–Ma–Xie Lemma 8)**:
   - `parity_flip_even_cycle_interval_of_odd_cycle`: Any family of internally disjoint `(u1, u2)`-paths
     of lengths `L_0, L_0 + 2, ..., L_0 + 2s` linked by two disjoint paths to a disjoint odd cycle
     unconditionally forces EVERY even simple cycle length in `[2t, 2t + 2s]` (`t ≥ 2`).
-/

namespace E64Wave8Agent1
open SimpleGraph Erdos64Closure E64Wave6Agent3 E64Wave7Agent6

/-! ## Section 1 (Pillar 1): Multi-Layer Cubic BFS-Shell Dichotomy & Handshaking Identity -/

section MultiLayerBFSDichotomy

variable {V : Type*}

/-- **Pillar 1A — Interior Layer Full-Degree Theorem**:
In any cubic graph (`∀ v, G.degree v = 3`) with a BFS layering `L : V → ℕ` (every adjacent pair
changes layer by at most `1`), every vertex `u` strictly inside an `r`-layer BFS shell
`S_{i,r} = {x | i ≤ L x ∧ L x ≤ i + r - 1}` (`i < L u ∧ L u < i + r - 1`) retains its full
degree `3` inside the shell. -/
theorem cubic_bfs_interior_full_degree [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcubic : ∀ v : V, G.degree v = 3)
    (L : V → ℕ)
    (hbfs : ∀ x y : V, G.Adj x y → L x ≤ L y + 1 ∧ L y ≤ L x + 1)
    {i r : ℕ} {u : V}
    (hlo : i < L u) (hhi : L u + 1 < i + r) :
    ((G.neighborFinset u).filter (fun x => i ≤ L x ∧ L x ≤ i + r - 1)).card = 3 := by
  have hfilter : (G.neighborFinset u).filter (fun x => i ≤ L x ∧ L x ≤ i + r - 1) =
      G.neighborFinset u := by
    rw [Finset.filter_eq_self]
    intro x hx
    have hadj : G.Adj u x := (G.mem_neighborFinset u x).mp hx
    have hstep := hbfs u x hadj
    omega
  rw [hfilter, SimpleGraph.card_neighborFinset_eq_degree, hcubic u]

/-- **Pillar 1B — Top Boundary Degree Bound for Arbitrary `r`-Layer Shells**:
Every vertex `u ∈ L_i` (`i ≥ 1`) with a parent in `L_{i-1}` has degree `≤ 2` inside ANY
`r`-layer BFS shell `S_{i,r}` (`i ≤ L x ≤ i + r - 1`). -/
theorem cubic_bfs_top_layer_deg_le_two [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcubic : ∀ v : V, G.degree v = 3)
    (L : V → ℕ) {i r : ℕ} (hi : 1 ≤ i) {u : V}
    (hparent : ∃ w : V, G.Adj u w ∧ L w = i - 1) :
    ((G.neighborFinset u).filter (fun x => i ≤ L x ∧ L x ≤ i + r - 1)).card ≤ 2 := by
  obtain ⟨w, huw, hLw⟩ := hparent
  have hw_mem : w ∈ G.neighborFinset u := (G.mem_neighborFinset u w).mpr huw
  have hsub : (G.neighborFinset u).filter (fun x => i ≤ L x ∧ L x ≤ i + r - 1) ⊆
      (G.neighborFinset u).erase w := by
    intro x hx
    rw [Finset.mem_erase]
    refine ⟨?_, (Finset.mem_filter.mp hx).1⟩
    intro hxw; subst hxw
    have hbd := (Finset.mem_filter.mp hx).2
    omega
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hw_mem, SimpleGraph.card_neighborFinset_eq_degree, hcubic u] at hcard
  omega

/-- **Pillar 1C — Bottom Expanding Boundary Degree Bound**:
Every vertex `u ∈ L_{i+r-1}` with a forward neighbor in `L_{i+r}` has degree `≤ 2` inside
the `r`-layer BFS shell `S_{i,r}`. -/
theorem cubic_bfs_bottom_expanding_deg_le_two [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcubic : ∀ v : V, G.degree v = 3)
    (L : V → ℕ) {i r : ℕ} (hr : 1 ≤ r) {u : V}
    (hchild : ∃ w : V, G.Adj u w ∧ L w = i + r) :
    ((G.neighborFinset u).filter (fun x => i ≤ L x ∧ L x ≤ i + r - 1)).card ≤ 2 := by
  obtain ⟨w, huw, hLw⟩ := hchild
  have hw_mem : w ∈ G.neighborFinset u := (G.mem_neighborFinset u w).mpr huw
  have hsub : (G.neighborFinset u).filter (fun x => i ≤ L x ∧ L x ≤ i + r - 1) ⊆
      (G.neighborFinset u).erase w := by
    intro x hx
    rw [Finset.mem_erase]
    refine ⟨?_, (Finset.mem_filter.mp hx).1⟩
    intro hxw; subst hxw
    have hbd := (Finset.mem_filter.mp hx).2
    omega
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hw_mem, SimpleGraph.card_neighborFinset_eq_degree, hcubic u] at hcard
  omega

/-- **Pillar 1D — Strictly Expanding 2-Layer BFS Shell Max-Degree-2 Obstruction**:
In any strictly expanding 2-layer BFS shell `S_{i,2} = L_i ∪ L_{i+1}` (`i ≥ 1`) of a cubic graph,
EVERY vertex `u ∈ S_{i,2}` has degree `≤ 2` inside `S_{i,2}` — blocking NOT ONLY bipartite chorded
cycles, but EVERY `Θ`-graph and EVERY chorded cycle (bipartite or non-bipartite)! -/
theorem cubic_two_layer_expanding_max_deg_le_two [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcubic : ∀ v : V, G.degree v = 3)
    (L : V → ℕ) {i : ℕ} (hi : 1 ≤ i)
    (hparent : ∀ u : V, L u = i → ∃ w : V, G.Adj u w ∧ L w = i - 1)
    (hchild : ∀ u : V, L u = i + 1 → ∃ w : V, G.Adj u w ∧ L w = i + 2)
    {u : V} (hu : i ≤ L u ∧ L u ≤ i + 1) :
    ((G.neighborFinset u).filter (fun x => i ≤ L x ∧ L x ≤ i + 1)).card ≤ 2 := by
  have hcase : L u = i ∨ L u = i + 1 := by omega
  rcases hcase with h0 | h1
  · have := cubic_bfs_top_layer_deg_le_two G hcubic L (i := i) (r := 2) hi (hparent u h0)
    simpa only [show i + 2 - 1 = i + 1 by omega] using this
  · have := cubic_bfs_bottom_expanding_deg_le_two G hcubic L (i := i) (r := 2) (by omega)
      (hchild u h1)
    simpa only [show i + 2 - 1 = i + 1 by omega] using this

/-- Helper: both chord endpoints `v_0` and `v_{2r+1}` of a `ChordedEvenCycle G m r` inside a
vertex subset `P : V → Prop` have degree `≥ 3` inside `P`. -/
private theorem chord_endpoints_deg_ge_three [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : V → Prop) [DecidablePred P]
    {m r : ℕ} (C : ChordedEvenCycle G m r)
    (hP : ∀ idx : Fin (2 * m), P (C.v idx)) :
    3 ≤ ((G.neighborFinset (C.v ⟨0, by have := C.hm; omega⟩)).filter P).card ∧
    3 ≤ ((G.neighborFinset (C.v ⟨2 * r + 1, by have := C.hm; have := C.hr_hi; omega⟩)).filter P).card := by
  have hm := C.hm; have hr1 := C.hr_lo; have hrh := C.hr_hi
  constructor
  · let u0 := C.v ⟨0, by omega⟩
    let x1 := C.v ⟨1, by omega⟩
    let x2 := C.v ⟨2 * r + 1, by omega⟩
    let x3 := C.v ⟨2 * m - 1, by omega⟩
    have h1 : G.Adj u0 x1 := by
      have := C.hadj_cyc ⟨0, by omega⟩
      simpa [u0, x1, Nat.mod_eq_of_lt (by omega : 1 < 2 * m)] using this
    have h2 : G.Adj u0 x2 := C.hadj_chord
    have h3 : G.Adj u0 x3 := by
      have := (C.hadj_cyc ⟨2 * m - 1, by omega⟩).symm
      have hmod : (2 * m - 1 + 1) % (2 * m) = 0 := by
        have : 2 * m - 1 + 1 = 2 * m := by omega
        rw [this, Nat.mod_self]
      simpa [u0, x3, hmod] using this
    have h12 : x1 ≠ x2 := fun h => by have := congrArg Fin.val (C.hv_inj h); dsimp only at this; omega
    have h13 : x1 ≠ x3 := fun h => by have := congrArg Fin.val (C.hv_inj h); dsimp only at this; omega
    have h23 : x2 ≠ x3 := fun h => by have := congrArg Fin.val (C.hv_inj h); dsimp only at this; omega
    have hsub : ({x1, x2, x3} : Finset V) ⊆ (G.neighborFinset u0).filter P := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr h1, hP ⟨1, by omega⟩⟩
      · exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr h2, hP ⟨2 * r + 1, by omega⟩⟩
      · exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr h3, hP ⟨2 * m - 1, by omega⟩⟩
    have hcard3 : ({x1, x2, x3} : Finset V).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [h23]
      · simp [h12, h13]
    calc 3 = ({x1, x2, x3} : Finset V).card := hcard3.symm
      _ ≤ ((G.neighborFinset u0).filter P).card := Finset.card_le_card hsub
  · let u1 := C.v ⟨2 * r + 1, by omega⟩
    let y1 := C.v ⟨0, by omega⟩
    let y2 := C.v ⟨2 * r, by omega⟩
    let y3 := C.v ⟨2 * r + 2, by omega⟩
    have h1 : G.Adj u1 y1 := C.hadj_chord.symm
    have h2 : G.Adj u1 y2 := by
      have := (C.hadj_cyc ⟨2 * r, by omega⟩).symm
      simpa [u1, y2, Nat.mod_eq_of_lt (by omega : 2 * r + 1 < 2 * m)] using this
    have h3 : G.Adj u1 y3 := by
      have := C.hadj_cyc ⟨2 * r + 1, by omega⟩
      simpa [u1, y3, Nat.mod_eq_of_lt (by omega : 2 * r + 2 < 2 * m)] using this
    have h12 : y1 ≠ y2 := fun h => by have := congrArg Fin.val (C.hv_inj h); dsimp only at this; omega
    have h13 : y1 ≠ y3 := fun h => by have := congrArg Fin.val (C.hv_inj h); dsimp only at this; omega
    have h23 : y2 ≠ y3 := fun h => by have := congrArg Fin.val (C.hv_inj h); dsimp only at this; omega
    have hsub : ({y1, y2, y3} : Finset V) ⊆ (G.neighborFinset u1).filter P := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr h1, hP ⟨0, by omega⟩⟩
      · exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr h2, hP ⟨2 * r, by omega⟩⟩
      · exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr h3, hP ⟨2 * r + 2, by omega⟩⟩
    have hcard3 : ({y1, y2, y3} : Finset V).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [h23]
      · simp [h12, h13]
    calc 3 = ({y1, y2, y3} : Finset V).card := hcard3.symm
      _ ≤ ((G.neighborFinset u1).filter P).card := Finset.card_le_card hsub

/-- **Pillar 1E — Sharp 3-Layer Bipartite Chorded-Cycle Sink-Forcing Theorem**:
In ANY bipartite 3-layer BFS shell `S_{i,3} = L_i ∪ L_{i+1} ∪ L_{i+2}` (`i ≥ 1`, no intra-layer
edges) of a cubic graph, if `S_{i,3}` contains a `ChordedEvenCycle G m r`, then ONE of its two
chord endpoints `w ∈ {v_0, v_{2r+1}}` MUST be a **zero-forward-degree dead-end sink in `L_{i+2}`**
(i.e. `L w = i + 2` and `∀ z, G.Adj w z → L z ≠ i + 3`). -/
theorem cubic_three_layer_bipartite_chorded_forces_sink [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcubic : ∀ v : V, G.degree v = 3)
    (L : V → ℕ) {i : ℕ} (hi : 1 ≤ i)
    (hparent : ∀ u : V, L u = i → ∃ w : V, G.Adj u w ∧ L w = i - 1)
    (hbip : ∀ x y : V, i ≤ L x → L x ≤ i + 2 → i ≤ L y → L y ≤ i + 2 → G.Adj x y → L x ≠ L y)
    {m r : ℕ} (C : ChordedEvenCycle G m r)
    (hshell : ∀ idx : Fin (2 * m), i ≤ L (C.v idx) ∧ L (C.v idx) ≤ i + 2) :
    ∃ w : V, (w = C.v ⟨0, by have := C.hm; omega⟩ ∨
              w = C.v ⟨2 * r + 1, by have := C.hm; have := C.hr_hi; omega⟩) ∧
      L w = i + 2 ∧ ∀ z : V, G.Adj w z → L z ≠ i + 3 := by
  have hm := C.hm; have hrh := C.hr_hi
  let u0 := C.v ⟨0, by omega⟩
  let u1 := C.v ⟨2 * r + 1, by omega⟩
  have hdeg := chord_endpoints_deg_ge_three G (fun x => i ≤ L x ∧ L x ≤ i + 2) C hshell
  have h0_bd : i ≤ L u0 ∧ L u0 ≤ i + 2 := hshell ⟨0, by omega⟩
  have h1_bd : i ≤ L u1 ∧ L u1 ≤ i + 2 := hshell ⟨2 * r + 1, by omega⟩
  have h0_ne_i : L u0 ≠ i := by
    intro hEq
    have hle2 := cubic_bfs_top_layer_deg_le_two G hcubic L (i := i) (r := 3) hi (hparent u0 hEq)
    have hge3 : 3 ≤ ((G.neighborFinset u0).filter (fun x => i ≤ L x ∧ L x ≤ i + 3 - 1)).card := by
      simpa only [show i + 3 - 1 = i + 2 by omega] using hdeg.1
    omega
  have h1_ne_i : L u1 ≠ i := by
    intro hEq
    have hle2 := cubic_bfs_top_layer_deg_le_two G hcubic L (i := i) (r := 3) hi (hparent u1 hEq)
    have hge3 : 3 ≤ ((G.neighborFinset u1).filter (fun x => i ≤ L x ∧ L x ≤ i + 3 - 1)).card := by
      simpa only [show i + 3 - 1 = i + 2 by omega] using hdeg.2
    omega
  have hne : L u0 ≠ L u1 := hbip u0 u1 h0_bd.1 h0_bd.2 h1_bd.1 h1_bd.2 C.hadj_chord
  have hcases : L u0 = i + 2 ∨ L u1 = i + 2 := by omega
  rcases hcases with h0_top | h1_top
  · refine ⟨u0, Or.inl rfl, h0_top, ?_⟩
    intro z hadj hLz
    have hle2 := cubic_bfs_bottom_expanding_deg_le_two G hcubic L (i := i) (r := 3) (by omega)
      ⟨z, hadj, hLz⟩
    have hge3 : 3 ≤ ((G.neighborFinset u0).filter (fun x => i ≤ L x ∧ L x ≤ i + 3 - 1)).card := by
      simpa only [show i + 3 - 1 = i + 2 by omega] using hdeg.1
    omega
  · refine ⟨u1, Or.inr rfl, h1_top, ?_⟩
    intro z hadj hLz
    have hle2 := cubic_bfs_bottom_expanding_deg_le_two G hcubic L (i := i) (r := 3) (by omega)
      ⟨z, hadj, hLz⟩
    have hge3 : 3 ≤ ((G.neighborFinset u1).filter (fun x => i ≤ L x ∧ L x ≤ i + 3 - 1)).card := by
      simpa only [show i + 3 - 1 = i + 2 by omega] using hdeg.2
    omega

/-- **Pillar 1F — Strictly Expanding 3-Layer Bipartite BFS-Shell No-Go Theorem**:
No strictly expanding bipartite 3-layer BFS shell `S_{i,3} = L_i ∪ L_{i+1} ∪ L_{i+2}` (`i ≥ 1`)
of a cubic graph can contain ANY `ChordedEvenCycle G m r`. Combined with
`cubic_bfs_interior_full_degree` at `r = 4`, this proves `r = 4` is the exact sharp minimum
shell thickness for expanding bipartite chorded cycles in cubic graphs. -/
theorem cubic_three_layer_expanding_no_bipartite_chorded_cycle [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcubic : ∀ v : V, G.degree v = 3)
    (L : V → ℕ) {i : ℕ} (hi : 1 ≤ i)
    (hparent : ∀ u : V, L u = i → ∃ w : V, G.Adj u w ∧ L w = i - 1)
    (hchild : ∀ u : V, L u = i + 2 → ∃ w : V, G.Adj u w ∧ L w = i + 3)
    (hbip : ∀ x y : V, i ≤ L x → L x ≤ i + 2 → i ≤ L y → L y ≤ i + 2 → G.Adj x y → L x ≠ L y)
    {m r : ℕ} (C : ChordedEvenCycle G m r)
    (hshell : ∀ idx : Fin (2 * m), i ≤ L (C.v idx) ∧ L (C.v idx) ≤ i + 2) :
    False := by
  obtain ⟨w, _, hLw, hnochild⟩ :=
    cubic_three_layer_bipartite_chorded_forces_sink G hcubic L hi hparent hbip C hshell
  obtain ⟨z, hadj, hLz⟩ := hchild w hLw
  exact hnochild z hadj hLz

/-- **Pillar 1G — Exact Cubic Shell Degree-Cut Handshaking Identity**:
For ANY finite subset `S : Finset V` (in particular any `r`-layer BFS shell `S_{i,r}`) in a cubic
graph, the sum of internal degrees plus the sum of cut degrees equals `3 * S.card`. Thus whenever
the total cut size `∑_{u ∈ S} deg_{S^c}(u) < S.card`, the internal degree sum exceeds `2 * S.card`,
forcing positive cycle excess `|E(S)| > |S|`. -/
theorem cubic_bfs_shell_degree_cut_identity [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcubic : ∀ v : V, G.degree v = 3)
    (S : Finset V) :
    (∑ u ∈ S, ((G.neighborFinset u).filter (fun x => x ∈ S)).card) +
    (∑ u ∈ S, ((G.neighborFinset u).filter (fun x => x ∉ S)).card) = 3 * S.card := by
  rw [← Finset.sum_add_distrib]
  have hpoint : ∀ u ∈ S,
      ((G.neighborFinset u).filter (fun x => x ∈ S)).card +
      ((G.neighborFinset u).filter (fun x => x ∉ S)).card = 3 := by
    intro u _
    have hdisj : Disjoint ((G.neighborFinset u).filter (fun x => x ∈ S))
        ((G.neighborFinset u).filter (fun x => x ∉ S)) :=
      Finset.disjoint_filter.mpr (fun _ _ hx hnx => hnx hx)
    have hunion : ((G.neighborFinset u).filter (fun x => x ∈ S)) ∪
        ((G.neighborFinset u).filter (fun x => x ∉ S)) = G.neighborFinset u := by
      ext x; simp only [Finset.mem_union, Finset.mem_filter]; tauto
    rw [← Finset.card_union_of_disjoint hdisj, hunion,
        SimpleGraph.card_neighborFinset_eq_degree, hcubic u]
  rw [Finset.sum_congr rfl hpoint, Finset.sum_const, smul_eq_mul, mul_comm]

end MultiLayerBFSDichotomy

/-! ## Section 2 (Pillar 2): Multi-Layer Asymmetric-Depth BFS-LCA Lifting & Girth-vs-Height Closure -/

section MultiLayerAsymmetricLCA

variable {V : Type*}

/-- **Pillar 2A — Multi-Layer Asymmetric-Depth BFS-LCA Cycle-Interval Theorem**:
Generalizes Wave 7's equal-depth `bfs_lca_even_cycle_interval` to multi-layer shells (`r ≥ 3`):
if `C : ChordedEvenCycle G m r` has a nontrivial 2-coloring `col : Fin m → Bool` of its even-index
vertices `V_0` such that every bichromatic pair `(i, j)` is joined by a simple path internally
disjoint from `C` of constant cross-color length `D = h0 + h1 ≥ 2` (for instance, color-0 vertices
at BFS depth `h0 = h` in `L_i` and color-1 vertices at BFS depth `h1 = h + 2` in `L_{i+2}`),
then `G` unconditionally contains a simple cycle (`Walk.IsCycle`) of EVERY length `D + 2 * k`
for `1 ≤ k ≤ m - 1`. -/
theorem multilayer_asymmetric_bfs_lca_cycle_interval {G : SimpleGraph V} {m r h0 h1 : ℕ}
    (C : ChordedEvenCycle G m r) (hD : 2 ≤ h0 + h1) (col : Fin m → Bool)
    (hnontriv : ∃ i0 i1 : Fin m, col i0 ≠ col i1)
    (htree : ∀ i j : Fin m, col i ≠ col j →
      ∃ q : G.Walk (C.v ⟨2 * i.val, by omega⟩) (C.v ⟨2 * j.val, by omega⟩),
        q.IsPath ∧ q.length = h0 + h1 ∧
        ∀ x ∈ q.support, x ∈ Set.range C.v →
          x = C.v ⟨2 * i.val, by omega⟩ ∨ x = C.v ⟨2 * j.val, by omega⟩) :
    ∀ k : ℕ, 1 ≤ k → k ≤ m - 1 →
      ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ c.length = h0 + h1 + 2 * k := by
  intro k hk1 hkm
  obtain ⟨i, j, p, hcol_ne, hp, hp_len, hp_mem⟩ :=
    bsv_chorded_cycle_all_even_ab_paths C col hnontriv hk1 hkm
  obtain ⟨q, hq, hq_len, hq_disj⟩ := htree i j hcol_ne
  refine ⟨C.v ⟨2 * i.val, by omega⟩, p.append q.reverse, ?_, ?_⟩
  · apply isCycle_append_reverse_of_internally_disjoint p q hp hq (by omega)
    intro x hxp hxq
    exact hq_disj x hxq (hp_mem x hxp)
  · rw [Walk.length_append, Walk.length_reverse, hp_len, hq_len]; omega

/-- **Pillar 2B — Unconditional Unbounded-`n` `HasPower G` via Asymmetric Multi-Layer BFS-LCA**:
When `h0 + h1 = 2 * H` is even (`H ≥ 1`, e.g. `h0 = h`, `h1 = h + 2`, `H = h + 1`) and `H + 1 ≤ m`,
the asymmetric BFS-lifted interval `[2H + 2, 2H + 2m - 2]` crosses a power of 2, forcing
`HasPower G` unconditionally. -/
theorem hasPower_of_multilayer_asymmetric_bfs_chorded_cycle {G : SimpleGraph V} {m r h0 h1 H : ℕ}
    (C : ChordedEvenCycle G m r) (hH : 1 ≤ H) (heven : h0 + h1 = 2 * H) (hscale : H + 1 ≤ m)
    (col : Fin m → Bool) (hnontriv : ∃ i0 i1 : Fin m, col i0 ≠ col i1)
    (htree : ∀ i j : Fin m, col i ≠ col j →
      ∃ q : G.Walk (C.v ⟨2 * i.val, by omega⟩) (C.v ⟨2 * j.val, by omega⟩),
        q.IsPath ∧ q.length = h0 + h1 ∧
        ∀ x ∈ q.support, x ∈ Set.range C.v →
          x = C.v ⟨2 * i.val, by omega⟩ ∨ x = C.v ⟨2 * j.val, by omega⟩) :
    HasPower G := by
  have hcyc := multilayer_asymmetric_bfs_lca_cycle_interval C (by omega) col hnontriv htree
  refine hasPower_of_consecutive_even_cycles G (a := H + 1) (b := H + m - 1)
    (by omega) (by omega) ?_
  intro t hlo hhi
  obtain ⟨u, c, hc, hlen⟩ := hcyc (t - H) (by omega) (by omega)
  exact ⟨u, c, hc, by omega⟩

/-- **Pillar 2C — Girth Lower Bound on `ChordedEvenCycle`**:
In any simple graph `G` of girth `≥ g` (every simple cycle has length `≥ g`), every
`ChordedEvenCycle G m r` splits into two simple cycles of lengths `2r + 2` and `2m - 2r`,
forcing `g ≤ 2 * r + 2`, `g ≤ 2 * m - 2 * r`, and hence `g - 1 ≤ m` unconditionally. -/
theorem chorded_even_cycle_girth_lower_bound {G : SimpleGraph V} {m r g : ℕ}
    (C : ChordedEvenCycle G m r)
    (hgirth : ∀ (u : V) (c : G.Walk u u), c.IsCycle → g ≤ c.length) :
    g ≤ 2 * r + 2 ∧ g ≤ 2 * m - 2 * r ∧ g - 1 ≤ m := by
  have hm := C.hm; have hr1 := C.hr_lo; have hrh := C.hr_hi
  have h0_mod : 0 % (2 * m) = 0 := Nat.zero_mod _
  have h2r1_mod : (2 * r + 1) % (2 * m) = 2 * r + 1 := Nat.mod_eq_of_lt (by omega)
  let p1_raw := C.fwdWalk 0 (2 * r + 1)
  let p1 : G.Walk (C.v ⟨0, by omega⟩) (C.v ⟨2 * r + 1, by omega⟩) :=
    p1_raw.copy (by simp [h0_mod]) (by simp [h2r1_mod])
  let q_chord : G.Walk (C.v ⟨0, by omega⟩) (C.v ⟨2 * r + 1, by omega⟩) :=
    Walk.cons C.hadj_chord Walk.nil
  have hp1_path : p1.IsPath := by
    rw [Walk.isPath_def, Walk.support_copy]
    exact (C.fwdWalk_isPath 0 (2 * r + 1) (by omega)).support_nodup
  have hp1_len : p1.length = 2 * r + 1 := by
    simp only [p1, Walk.length_copy, p1_raw, ChordedEvenCycle.fwdWalk_length]
  have hq_len : q_chord.length = 1 := rfl
  have hq_path : q_chord.IsPath := by
    rw [Walk.isPath_def]
    simp only [q_chord, Walk.support_cons, Walk.support_nil, List.nodup_cons, List.mem_singleton,
      List.nodup_nil, and_true]
    exact ⟨G.ne_of_adj C.hadj_chord, by simp⟩
  have hc1_cyc : (p1.append q_chord.reverse).IsCycle := by
    apply isCycle_append_reverse_of_internally_disjoint p1 q_chord hp1_path hq_path (by omega)
    intro x _ hxq
    simp [q_chord] at hxq
    exact hxq
  have hc1_len : (p1.append q_chord.reverse).length = 2 * r + 2 := by
    rw [Walk.length_append, Walk.length_reverse, hp1_len, hq_len]
  have hg1 : g ≤ 2 * r + 2 := by
    have := hgirth _ _ hc1_cyc
    omega
  have hend2 : (2 * r + 1 + (2 * m - 2 * r - 1)) % (2 * m) = 0 := by
    have : 2 * r + 1 + (2 * m - 2 * r - 1) = 2 * m := by omega
    rw [this, Nat.mod_self]
  let p2_raw := C.fwdWalk (2 * r + 1) (2 * m - 2 * r - 1)
  let p2 : G.Walk (C.v ⟨2 * r + 1, by omega⟩) (C.v ⟨0, by omega⟩) :=
    p2_raw.copy (by simp [h2r1_mod]) (by simp [hend2])
  let q_chord2 : G.Walk (C.v ⟨2 * r + 1, by omega⟩) (C.v ⟨0, by omega⟩) :=
    Walk.cons C.hadj_chord.symm Walk.nil
  have hp2_path : p2.IsPath := by
    rw [Walk.isPath_def, Walk.support_copy]
    exact (C.fwdWalk_isPath (2 * r + 1) (2 * m - 2 * r - 1) (by omega)).support_nodup
  have hp2_len : p2.length = 2 * m - 2 * r - 1 := by
    simp only [p2, Walk.length_copy, p2_raw, ChordedEvenCycle.fwdWalk_length]
  have hq2_len : q_chord2.length = 1 := rfl
  have hq2_path : q_chord2.IsPath := by
    rw [Walk.isPath_def]
    simp only [q_chord2, Walk.support_cons, Walk.support_nil, List.nodup_cons, List.mem_singleton,
      List.nodup_nil, and_true]
    exact ⟨G.ne_of_adj C.hadj_chord.symm, by simp⟩
  have hc2_cyc : (p2.append q_chord2.reverse).IsCycle := by
    apply isCycle_append_reverse_of_internally_disjoint p2 q_chord2 hp2_path hq2_path (by omega)
    intro x _ hxq
    simp [q_chord2] at hxq
    exact hxq
  have hc2_len : (p2.append q_chord2.reverse).length = 2 * m - 2 * r := by
    rw [Walk.length_append, Walk.length_reverse, hp2_len, hq2_len]; omega
  have hg2 : g ≤ 2 * m - 2 * r := by
    have := hgirth _ _ hc2_cyc
    omega
  exact ⟨hg1, hg2, by omega⟩

/-- **Pillar 2D — Girth-Bounded-Height Automatic `HasPower G` Closure**:
In ANY graph of girth `≥ g`, ANY multi-layer BFS chorded cycle with asymmetric half-height
`1 ≤ H ≤ g - 2` (`h0 + h1 = 2 * H`) AUTOMATICALLY satisfies `H + 1 ≤ m` via
`chorded_even_cycle_girth_lower_bound` and unconditionally forces `HasPower G`! -/
theorem hasPower_of_girth_bounded_height_chorded_cycle {G : SimpleGraph V} {m r g h0 h1 H : ℕ}
    (C : ChordedEvenCycle G m r)
    (hgirth : ∀ (u : V) (c : G.Walk u u), c.IsCycle → g ≤ c.length)
    (hH_lo : 1 ≤ H) (hH_hi : H + 2 ≤ g) (heven : h0 + h1 = 2 * H)
    (col : Fin m → Bool) (hnontriv : ∃ i0 i1 : Fin m, col i0 ≠ col i1)
    (htree : ∀ i j : Fin m, col i ≠ col j →
      ∃ q : G.Walk (C.v ⟨2 * i.val, by omega⟩) (C.v ⟨2 * j.val, by omega⟩),
        q.IsPath ∧ q.length = h0 + h1 ∧
        ∀ x ∈ q.support, x ∈ Set.range C.v →
          x = C.v ⟨2 * i.val, by omega⟩ ∨ x = C.v ⟨2 * j.val, by omega⟩) :
    HasPower G := by
  have hm_ge := (chorded_even_cycle_girth_lower_bound C hgirth).2.2
  exact hasPower_of_multilayer_asymmetric_bfs_chorded_cycle C hH_lo heven (by omega) col hnontriv htree

end MultiLayerAsymmetricLCA

/-! ## Section 3 (Pillar 3): Heterogeneous (`O(log L_0)`) Subset-Sum `HetAdjusterChain` & Brown Completeness -/

section HeterogeneousAdjusterChains

variable {V : Type*}

private theorem mem_support_of_mem_edges' {G : SimpleGraph V} :
    ∀ {a b : V} {p : G.Walk a b} {e : Sym2 V} {x : V},
      e ∈ p.edges → x ∈ e → x ∈ p.support
  | _, _, .nil, _, _, he, _ => by simp at he
  | _, _, .cons _ rest, e, x, he, hx => by
      simp only [Walk.edges_cons, List.mem_cons] at he
      rcases he with rfl | hmem
      · simp only [Sym2.mem_iff] at hx
        rcases hx with rfl | rfl
        · exact Walk.start_mem_support _
        · exact List.mem_cons_of_mem _ (Walk.start_mem_support rest)
      · exact List.mem_cons_of_mem _ (mem_support_of_mem_edges' hmem hx)

private theorem support_append_tail' {G : SimpleGraph V} {a u b : V}
    (p : G.Walk a u) (q : G.Walk u b) :
    (p.append q).support.tail = p.support.tail ++ q.support.tail := by
  rw [Walk.support_append]
  cases hp : p.support with
  | nil => exact absurd hp (Walk.support_ne_nil p)
  | cons x xs => simp

private theorem support_tail_eq_internals_append_end' {G : SimpleGraph V} :
    ∀ {a b : V} (p : G.Walk a b), 1 ≤ p.length →
      p.support.tail = walkInternals p ++ [b]
  | _, _, .nil, h => by simp at h
  | a, b, .cons _ .nil, _ => by simp [walkInternals]
  | a, b, .cons h1 (.cons h2 rest), _ => by
      have ih := support_tail_eq_internals_append_end' (.cons h2 rest) (by simp)
      simp only [walkInternals, Walk.support_cons, List.tail_cons] at ih ⊢
      rw [List.dropLast_cons_of_ne_nil (Walk.support_ne_nil rest), List.cons_append]
      congr 1

private theorem mem_internals_of_mem_edges_ge2' {G : SimpleGraph V} :
    ∀ {a b : V} (p : G.Walk a b), 2 ≤ p.length →
      ∀ e ∈ p.edges, ∃ z ∈ walkInternals p, z ∈ e
  | _, _, .nil, h, _, _ => by simp at h
  | _, _, .cons _ .nil, h, _, _ => by simp at h
  | a, b, .cons (v := u) h1 (.cons (v := w) h2 rest), _, e, he => by
      simp only [Walk.edges_cons, List.mem_cons] at he
      have hu_int : u ∈ walkInternals (Walk.cons h1 (Walk.cons h2 rest)) := by
        simp only [walkInternals, Walk.support_cons, List.tail_cons]
        rw [List.dropLast_cons_of_ne_nil (Walk.support_ne_nil rest)]
        exact List.mem_cons_self
      rcases he with rfl | rfl | hrest
      · exact ⟨u, hu_int, by simp⟩
      · exact ⟨u, hu_int, by simp⟩
      · cases rest with
        | nil => simp at hrest
        | cons h3 rest2 =>
            obtain ⟨z, hz, hze⟩ :=
              mem_internals_of_mem_edges_ge2' (Walk.cons h2 (Walk.cons h3 rest2)) (by simp) e
                (by rw [Walk.edges_cons]; exact List.mem_cons_of_mem _ hrest)
            refine ⟨z, ?_, hze⟩
            simp only [walkInternals, Walk.support_cons, List.tail_cons] at hz ⊢
            rw [List.dropLast_cons_of_ne_nil (by simp)]
            exact List.mem_cons_of_mem _ hz

/-- Subset sum of a step list `steps : List ℕ` selected by a boolean mask `mask : List Bool`. -/
def subsetSum : List ℕ → List Bool → ℕ
  | [], _ => 0
  | _, [] => 0
  | _ :: ds, false :: bs => subsetSum ds bs
  | d :: ds, true :: bs => d + subsetSum ds bs

/-- **Heterogeneous Adjuster Chain (`HetAdjusterChain`)**:
Generalizes Wave 7's uniform-step `AdjusterChain G δ` to arbitrary per-adjuster positive steps
`δ_1, δ_2, ..., δ_r ≥ 1` (e.g., dyadic steps `2, 2, 4, 8, ...` requiring only `O(log a)` adjusters
to span `[2a, 4a - 4]`, or mixed-parity steps in girth 5–14 cubic graphs). -/
inductive HetAdjusterChain (G : SimpleGraph V) : V → V → Type _
  | base {a b : V} (p : G.Walk a b) : HetAdjusterChain G a b
  | step {a u w b : V} (seg : G.Walk a u)
      (p0 p1 : G.Walk u w) (δ : ℕ) (hδ : 1 ≤ δ)
      (hp0_pos : 1 ≤ p0.length) (hp1_path : p1.IsPath)
      (hstep : p1.length = p0.length + δ)
      (rest : HetAdjusterChain G w b) : HetAdjusterChain G a b

namespace HetAdjusterChain

def steps {G : SimpleGraph V} : ∀ {a b : V}, HetAdjusterChain G a b → List ℕ
  | _, _, .base _ => []
  | _, _, .step _ _ _ δ _ _ _ _ rest => δ :: rest.steps

def altVertices {G : SimpleGraph V} : ∀ {a b : V}, HetAdjusterChain G a b → List V
  | _, _, .base _ => []
  | _, _, .step _ _ p1 _ _ _ _ _ rest => walkInternals p1 ++ rest.altVertices

def baseWalk {G : SimpleGraph V} : ∀ {a b : V}, HetAdjusterChain G a b → G.Walk a b
  | _, _, .base p => p
  | _, _, .step seg p0 _ _ _ _ _ _ rest => seg.append (p0.append rest.baseWalk)

def realize {G : SimpleGraph V} :
    ∀ {a b : V}, HetAdjusterChain G a b → List Bool → G.Walk a b
  | _, _, .base p, _ => p
  | _, _, .step seg p0 _ _ _ _ _ _ rest, [] => seg.append (p0.append rest.baseWalk)
  | _, _, .step seg p0 _ _ _ _ _ _ rest, false :: bs => seg.append (p0.append (rest.realize bs))
  | _, _, .step seg _ p1 _ _ _ _ _ rest, true :: bs => seg.append (p1.append (rest.realize bs))

/-- **Pillar 3A — Exact Heterogeneous Subset-Sum Length Law**. -/
theorem realize_length {G : SimpleGraph V} :
    ∀ {a b : V} (c : HetAdjusterChain G a b) (mask : List Bool),
      mask.length = c.steps.length →
      (c.realize mask).length = c.baseWalk.length + subsetSum c.steps mask
  | _, _, .base p, [], _ => by simp [realize, baseWalk, steps, subsetSum]
  | _, _, .base _, _ :: _, hlen => by simp [steps] at hlen
  | _, _, .step _ _ _ _ _ _ _ _ _, [], hlen => by simp [steps] at hlen
  | _, _, .step seg p0 p1 δ _ _ _ _ rest, false :: bs, hlen => by
      simp only [steps, List.length_cons, Nat.add_right_cancel_iff] at hlen
      have ih := realize_length rest bs hlen
      simp only [realize, baseWalk, Walk.length_append, steps, subsetSum]
      omega
  | _, _, .step seg p0 p1 δ _ _ _ hstep rest, true :: bs, hlen => by
      simp only [steps, List.length_cons, Nat.add_right_cancel_iff] at hlen
      have ih := realize_length rest bs hlen
      simp only [realize, baseWalk, Walk.length_append, steps, subsetSum]
      omega

private theorem mem_realize_support_tail {G : SimpleGraph V} :
    ∀ {a b : V} (c : HetAdjusterChain G a b) (mask : List Bool),
      mask.length = c.steps.length →
      ∀ x ∈ (c.realize mask).support.tail,
        x ∈ c.baseWalk.support.tail ∨ x ∈ c.altVertices
  | _, _, .base p, [], _, x, hx => Or.inl hx
  | _, _, .base _, _ :: _, hlen, _, _ => by simp [steps] at hlen
  | _, _, .step _ _ _ _ _ _ _ _ _, [], hlen, _, _ => by simp [steps] at hlen
  | _, _, .step seg p0 p1 δ _ hp0 _ _ rest, false :: bs, hlen, x, hx => by
      simp only [steps, List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [realize, baseWalk, support_append_tail', List.mem_append, altVertices] at hx ⊢
      rcases hx with hseg | hp0x | hrest
      · exact Or.inl (Or.inl hseg)
      · exact Or.inl (Or.inr (Or.inl hp0x))
      · rcases mem_realize_support_tail rest bs hlen x hrest with hbase | halt
        · exact Or.inl (Or.inr (Or.inr hbase))
        · exact Or.inr (Or.inr halt)
  | _, _, .step seg p0 p1 δ hδ hp0 _ hstep rest, true :: bs, hlen, x, hx => by
      simp only [steps, List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [realize, baseWalk, support_append_tail', List.mem_append, altVertices] at hx ⊢
      rcases hx with hseg | hp1x | hrest
      · exact Or.inl (Or.inl hseg)
      · rw [support_tail_eq_internals_append_end' p1 (by omega), List.mem_append,
          List.mem_singleton] at hp1x
        rcases hp1x with hint | rfl
        · exact Or.inr (Or.inl hint)
        · left; right; left
          rw [support_tail_eq_internals_append_end' p0 hp0, List.mem_append]
          exact Or.inr (List.mem_singleton.mpr rfl)
      · rcases mem_realize_support_tail rest bs hlen x hrest with hbase | halt
        · exact Or.inl (Or.inr (Or.inr hbase))
        · exact Or.inr (Or.inr halt)

private theorem realize_support_tail_nodup {G : SimpleGraph V} :
    ∀ {a b : V} (c : HetAdjusterChain G a b) (mask : List Bool),
      mask.length = c.steps.length →
      c.baseWalk.support.tail.Nodup →
      c.altVertices.Nodup →
      (∀ z ∈ c.altVertices, z ∉ c.baseWalk.support.tail) →
      (c.realize mask).support.tail.Nodup
  | _, _, .base p, [], _, hnd, _, _ => hnd
  | _, _, .base _, _ :: _, hlen, _, _, _ => by simp [steps] at hlen
  | _, _, .step _ _ _ _ _ _ _ _ _, [], hlen, _, _, _ => by simp [steps] at hlen
  | _, _, .step seg p0 p1 δ _ hp0 _ _ rest, false :: bs, hlen, hnd, halt_nd, hdisj => by
      simp only [steps, List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [baseWalk, support_append_tail', List.nodup_append] at hnd
      simp only [altVertices, List.nodup_append] at halt_nd
      rcases hnd with ⟨hseg_nd, ⟨hp0_nd, hrb_nd, hp0_rb⟩, hseg_rest⟩
      have hrest_disj : ∀ z ∈ rest.altVertices, z ∉ rest.baseWalk.support.tail := by
        intro z hz hm
        apply hdisj z (by simp [altVertices, hz])
        simp only [baseWalk, support_append_tail', List.mem_append]
        exact Or.inr (Or.inr hm)
      have ih := realize_support_tail_nodup rest bs hlen hrb_nd halt_nd.2.1 hrest_disj
      simp only [realize, support_append_tail', List.nodup_append]
      refine ⟨hseg_nd, ⟨hp0_nd, ih, ?_⟩, ?_⟩
      · intro x hxp0 y hyr hxy; subst hxy
        rcases mem_realize_support_tail rest bs hlen x hyr with hbase | halt
        · exact hp0_rb x hxp0 x hbase rfl
        · apply hdisj x (by simp [altVertices, halt])
          simp only [baseWalk, support_append_tail', List.mem_append]
          exact Or.inr (Or.inl hxp0)
      · intro x hxs y hyr hxy; subst hxy
        rw [List.mem_append] at hyr
        rcases hyr with hxp0 | hxr
        · exact hseg_rest x hxs x (List.mem_append.mpr (Or.inl hxp0)) rfl
        · rcases mem_realize_support_tail rest bs hlen x hxr with hbase | halt
          · exact hseg_rest x hxs x (List.mem_append.mpr (Or.inr hbase)) rfl
          · apply hdisj x (by simp [altVertices, halt])
            simp only [baseWalk, support_append_tail', List.mem_append]
            exact Or.inl hxs
  | _, _, .step (w := w) seg p0 p1 δ hδ hp0 hp1_path hstep rest, true :: bs, hlen, hnd, halt_nd, hdisj => by
      simp only [steps, List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [baseWalk, support_append_tail', List.nodup_append] at hnd
      simp only [altVertices, List.nodup_append] at halt_nd
      rcases hnd with ⟨hseg_nd, ⟨hp0_nd, hrb_nd, hp0_rb⟩, hseg_rest⟩
      rcases halt_nd with ⟨_, hrest_alt_nd, hp1_rest_alt⟩
      have hrest_disj : ∀ z ∈ rest.altVertices, z ∉ rest.baseWalk.support.tail := by
        intro z hz hm
        apply hdisj z (by simp [altVertices, hz])
        simp only [baseWalk, support_append_tail', List.mem_append]
        exact Or.inr (Or.inr hm)
      have ih := realize_support_tail_nodup rest bs hlen hrb_nd hrest_alt_nd hrest_disj
      have hp1_tail_nd : p1.support.tail.Nodup := by
        have h := hp1_path.support_nodup
        cases hs : p1.support with
        | nil => exact absurd hs (Walk.support_ne_nil p1)
        | cons _ _ => rw [hs, List.nodup_cons] at h; exact h.2
      have hw_mem_p0 : w ∈ p0.support.tail := by
        rw [support_tail_eq_internals_append_end' p0 hp0, List.mem_append]
        exact Or.inr (List.mem_singleton.mpr rfl)
      simp only [realize, support_append_tail', List.nodup_append]
      refine ⟨hseg_nd, ⟨hp1_tail_nd, ih, ?_⟩, ?_⟩
      · intro x hxp1 y hyr hxy; subst hxy
        rw [support_tail_eq_internals_append_end' p1 (by omega), List.mem_append,
          List.mem_singleton] at hxp1
        rcases hxp1 with hint | rfl
        · rcases mem_realize_support_tail rest bs hlen x hyr with hbase | halt
          · apply hdisj x (by simp [altVertices, hint])
            simp only [baseWalk, support_append_tail', List.mem_append]
            exact Or.inr (Or.inr hbase)
          · exact hp1_rest_alt x hint x halt rfl
        · rcases mem_realize_support_tail rest bs hlen w hyr with hbase | halt
          · exact hp0_rb w hw_mem_p0 w hbase rfl
          · apply hdisj w (by simp [altVertices, halt])
            simp only [baseWalk, support_append_tail', List.mem_append]
            exact Or.inr (Or.inl hw_mem_p0)
      · intro x hxs y hyr hxy; subst hxy
        rw [List.mem_append] at hyr
        rcases hyr with hxp1 | hxr
        · rw [support_tail_eq_internals_append_end' p1 (by omega), List.mem_append,
            List.mem_singleton] at hxp1
          rcases hxp1 with hint | rfl
          · apply hdisj x (by simp [altVertices, hint])
            simp only [baseWalk, support_append_tail', List.mem_append]
            exact Or.inl hxs
          · exact hseg_rest x hxs w (List.mem_append.mpr (Or.inl hw_mem_p0)) rfl
        · rcases mem_realize_support_tail rest bs hlen x hxr with hbase | halt
          · exact hseg_rest x hxs x (List.mem_append.mpr (Or.inr hbase)) rfl
          · apply hdisj x (by simp [altVertices, halt])
            simp only [baseWalk, support_append_tail', List.mem_append]
            exact Or.inl hxs

private theorem mem_realize_edges {G : SimpleGraph V} :
    ∀ {a b : V} (c : HetAdjusterChain G a b) (mask : List Bool),
      mask.length = c.steps.length →
      ∀ e ∈ (c.realize mask).edges,
        e ∈ c.baseWalk.edges ∨ ∃ z ∈ c.altVertices, z ∈ e
  | _, _, .base p, [], _, e, he => Or.inl he
  | _, _, .base _, _ :: _, hlen, _, _ => by simp [steps] at hlen
  | _, _, .step _ _ _ _ _ _ _ _ _, [], hlen, _, _ => by simp [steps] at hlen
  | _, _, .step seg p0 p1 _ _ _ _ _ rest, false :: bs, hlen, e, he => by
      simp only [steps, List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [realize, baseWalk, Walk.edges_append, List.mem_append, altVertices] at he ⊢
      rcases he with hseg | hp0 | hrest
      · exact Or.inl (Or.inl hseg)
      · exact Or.inl (Or.inr (Or.inl hp0))
      · rcases mem_realize_edges rest bs hlen e hrest with hbase | ⟨z, hz, hze⟩
        · exact Or.inl (Or.inr (Or.inr hbase))
        · exact Or.inr ⟨z, Or.inr hz, hze⟩
  | _, _, .step seg p0 p1 δ hδ hp0 _ hstep rest, true :: bs, hlen, e, he => by
      simp only [steps, List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [realize, baseWalk, Walk.edges_append, List.mem_append, altVertices] at he ⊢
      rcases he with hseg | hp1 | hrest
      · exact Or.inl (Or.inl hseg)
      · obtain ⟨z, hz, hze⟩ := mem_internals_of_mem_edges_ge2' p1 (by omega) e hp1
        exact Or.inr ⟨z, Or.inl hz, hze⟩
      · rcases mem_realize_edges rest bs hlen e hrest with hbase | ⟨z, hz, hze⟩
        · exact Or.inl (Or.inr (Or.inr hbase))
        · exact Or.inr ⟨z, Or.inr hz, hze⟩

private theorem realize_edges_nodup {G : SimpleGraph V} :
    ∀ {a b : V} (c : HetAdjusterChain G a b) (mask : List Bool),
      mask.length = c.steps.length →
      c.baseWalk.edges.Nodup →
      c.altVertices.Nodup →
      (∀ z ∈ c.altVertices, z ∉ c.baseWalk.support) →
      (c.realize mask).edges.Nodup
  | _, _, .base p, [], _, hnd, _, _ => hnd
  | _, _, .base _, _ :: _, hlen, _, _, _ => by simp [steps] at hlen
  | _, _, .step _ _ _ _ _ _ _ _ _, [], hlen, _, _, _ => by simp [steps] at hlen
  | _, _, .step (w := w) seg p0 p1 _ _ hp0 _ _ rest, false :: bs, hlen, hnd, halt_nd, hdisj => by
      simp only [steps, List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [baseWalk, Walk.edges_append, List.nodup_append] at hnd
      simp only [altVertices, List.nodup_append] at halt_nd
      rcases hnd with ⟨hseg_nd, ⟨hp0_nd, hrb_nd, hp0_rb⟩, hseg_rest⟩
      have hrest_disj : ∀ z ∈ rest.altVertices, z ∉ rest.baseWalk.support := by
        intro z hz hm
        apply hdisj z (by simp [altVertices, hz])
        rw [baseWalk, Walk.support_append, List.mem_append, support_append_tail', List.mem_append]
        cases hrb : rest.baseWalk with
        | nil =>
            rw [hrb, Walk.support_nil, List.mem_singleton] at hm
            subst hm
            have hend : w ∈ p0.support.tail := by
              rw [support_tail_eq_internals_append_end' p0 hp0, List.mem_append]
              exact Or.inr (List.mem_singleton.mpr rfl)
            exact Or.inr (Or.inl hend)
        | cons h1 r1 =>
            rw [hrb, Walk.support_cons, List.mem_cons] at hm
            rcases hm with rfl | hws
            · have hend : w ∈ p0.support.tail := by
                rw [support_tail_eq_internals_append_end' p0 hp0, List.mem_append]
                exact Or.inr (List.mem_singleton.mpr rfl)
              exact Or.inr (Or.inl hend)
            · exact Or.inr (Or.inr (by rw [hrb, Walk.support_cons, List.tail_cons]; exact hws))
      have ih := realize_edges_nodup rest bs hlen hrb_nd halt_nd.2.1 hrest_disj
      simp only [realize, Walk.edges_append, List.nodup_append]
      refine ⟨hseg_nd, ⟨hp0_nd, ih, ?_⟩, ?_⟩
      · intro e hep0 e' her hee; subst hee
        rcases mem_realize_edges rest bs hlen e her with hbase | ⟨z, hz, hze⟩
        · exact hp0_rb e hep0 e hbase rfl
        · apply hdisj z (by simp [altVertices, hz])
          have hz_p0 := mem_support_of_mem_edges' hep0 hze
          rw [baseWalk, Walk.support_append, List.mem_append, support_append_tail', List.mem_append]
          cases hps : p0 with
          | nil =>
              rw [hps, Walk.support_nil, List.mem_singleton] at hz_p0
              subst hz_p0
              exact Or.inl (Walk.end_mem_support seg)
          | cons h1 r1 =>
              rw [hps, Walk.support_cons, List.mem_cons] at hz_p0
              rcases hz_p0 with rfl | ht
              · exact Or.inl (Walk.end_mem_support seg)
              · exact Or.inr (Or.inl (by rw [hps, Walk.support_cons, List.tail_cons]; exact ht))
      · intro e hes e' her hee; subst hee
        rw [List.mem_append] at her
        rcases her with hep0 | her
        · exact hseg_rest e hes e (List.mem_append.mpr (Or.inl hep0)) rfl
        · rcases mem_realize_edges rest bs hlen e her with hbase | ⟨z, hz, hze⟩
          · exact hseg_rest e hes e (List.mem_append.mpr (Or.inr hbase)) rfl
          · apply hdisj z (by simp [altVertices, hz])
            simp only [baseWalk, Walk.support_append, List.mem_append]
            exact Or.inl (mem_support_of_mem_edges' hes hze)
  | _, _, .step (w := w) seg p0 p1 δ hδ hp0 hp1_path hstep rest, true :: bs, hlen, hnd, halt_nd, hdisj => by
      simp only [steps, List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [baseWalk, Walk.edges_append, List.nodup_append] at hnd
      simp only [altVertices, List.nodup_append] at halt_nd
      rcases hnd with ⟨hseg_nd, ⟨_, hrb_nd, _⟩, hseg_rest⟩
      rcases halt_nd with ⟨_, hrest_alt_nd, hp1_rest_alt⟩
      have hrest_disj : ∀ z ∈ rest.altVertices, z ∉ rest.baseWalk.support := by
        intro z hz hm
        apply hdisj z (by simp [altVertices, hz])
        rw [baseWalk, Walk.support_append, List.mem_append, support_append_tail', List.mem_append]
        cases hrb : rest.baseWalk with
        | nil =>
            rw [hrb, Walk.support_nil, List.mem_singleton] at hm
            subst hm
            have hend : w ∈ p0.support.tail := by
              rw [support_tail_eq_internals_append_end' p0 hp0, List.mem_append]
              exact Or.inr (List.mem_singleton.mpr rfl)
            exact Or.inr (Or.inl hend)
        | cons h1 r1 =>
            rw [hrb, Walk.support_cons, List.mem_cons] at hm
            rcases hm with rfl | hws
            · have hend : w ∈ p0.support.tail := by
                rw [support_tail_eq_internals_append_end' p0 hp0, List.mem_append]
                exact Or.inr (List.mem_singleton.mpr rfl)
              exact Or.inr (Or.inl hend)
            · exact Or.inr (Or.inr (by rw [hrb, Walk.support_cons, List.tail_cons]; exact hws))
      have ih := realize_edges_nodup rest bs hlen hrb_nd hrest_alt_nd hrest_disj
      simp only [realize, Walk.edges_append, List.nodup_append]
      refine ⟨hseg_nd, ⟨hp1_path.edges_nodup, ih, ?_⟩, ?_⟩
      · intro e hep1 e' her hee; subst hee
        obtain ⟨z, hz_int, hze⟩ := mem_internals_of_mem_edges_ge2' p1 (by omega) e hep1
        have hz_supp : z ∈ (rest.realize bs).support := mem_support_of_mem_edges' her hze
        cases hr : rest.realize bs with
        | nil =>
            rw [hr, Walk.support_nil, List.mem_singleton] at hz_supp
            subst hz_supp
            apply hdisj w (by simp [altVertices, hz_int])
            rw [baseWalk, Walk.support_append, List.mem_append, support_append_tail', List.mem_append]
            right; left
            rw [support_tail_eq_internals_append_end' p0 hp0, List.mem_append]
            exact Or.inr (List.mem_singleton.mpr rfl)
        | cons h1 r1 =>
            rw [hr, Walk.support_cons, List.mem_cons] at hz_supp
            rcases hz_supp with rfl | hws
            · apply hdisj w (by simp [altVertices, hz_int])
              rw [baseWalk, Walk.support_append, List.mem_append, support_append_tail', List.mem_append]
              right; left
              rw [support_tail_eq_internals_append_end' p0 hp0, List.mem_append]
              exact Or.inr (List.mem_singleton.mpr rfl)
            · rcases mem_realize_support_tail rest bs hlen z (by rw [hr, Walk.support_cons, List.tail_cons]; exact hws) with hbase | halt
              · apply hdisj z (by simp [altVertices, hz_int])
                rw [baseWalk, Walk.support_append, List.mem_append, support_append_tail', List.mem_append]
                exact Or.inr (Or.inr hbase)
              · exact hp1_rest_alt z hz_int z halt rfl
      · intro e hes e' her hee; subst hee
        rw [List.mem_append] at her
        rcases her with hep1 | her
        · obtain ⟨z, hz_int, hze⟩ := mem_internals_of_mem_edges_ge2' p1 (by omega) e hep1
          apply hdisj z (by simp [altVertices, hz_int])
          simp only [baseWalk, Walk.support_append, List.mem_append]
          exact Or.inl (mem_support_of_mem_edges' hes hze)
        · rcases mem_realize_edges rest bs hlen e her with hbase | ⟨z, hz, hze⟩
          · exact hseg_rest e hes e (List.mem_append.mpr (Or.inr hbase)) rfl
          · apply hdisj z (by simp [altVertices, hz])
            simp only [baseWalk, Walk.support_append, List.mem_append]
            exact Or.inl (mem_support_of_mem_edges' hes hze)

/-- **Pillar 3B — Heterogeneous Adjuster Chain Simple-Cycle Theorem**:
Every boolean mask realizes a simple cycle (`Walk.IsCycle`) of length
`c.baseWalk.length + subsetSum c.steps mask`. -/
theorem realize_isCycle {G : SimpleGraph V} {v : V}
    (c : HetAdjusterChain G v v) (hcyc : c.baseWalk.IsCycle)
    (halt : c.altVertices.Nodup) (hdisj : ∀ z ∈ c.altVertices, z ∉ c.baseWalk.support)
    (mask : List Bool) (hlen : mask.length = c.steps.length) :
    (c.realize mask).IsCycle := by
  have hdisj_tail : ∀ z ∈ c.altVertices, z ∉ c.baseWalk.support.tail :=
    fun z hz hm => hdisj z hz (List.mem_of_mem_tail hm)
  have htail_nd := realize_support_tail_nodup c mask hlen hcyc.support_nodup halt hdisj_tail
  have hedges_nd := realize_edges_nodup c mask hlen hcyc.edges_nodup halt hdisj
  have hne : c.realize mask ≠ Walk.nil := by
    intro hnil
    have hpos : 0 < (c.realize mask).length := by
      rw [realize_length c mask hlen]
      have := hcyc.three_le_length; omega
    rw [hnil] at hpos; simp at hpos
  exact ⟨⟨⟨hedges_nd⟩, hne⟩, htail_nd⟩

/-- **Pillar 3C — Brown Completeness Theorem for Subset Sums (Recursive Form)**:
If a list `ds : List ℕ` satisfies `d ≤ 1 + ds.sum` recursively, then every integer
`0 ≤ s ≤ ds.sum` is achieved as `subsetSum ds mask` for some boolean mask of length `ds.length`. -/
def BrownComplete : List ℕ → Prop
  | [] => True
  | d :: ds => d ≤ 1 + ds.sum ∧ BrownComplete ds

theorem brown_completeness :
    ∀ (ds : List ℕ), BrownComplete ds →
      ∀ s : ℕ, s ≤ ds.sum →
        ∃ mask : List Bool, mask.length = ds.length ∧ subsetSum ds mask = s
  | [], _, s, hs => by
      have hs0 : s = 0 := by simp at hs; omega
      subst hs0
      exact ⟨[], rfl, rfl⟩
  | d :: ds, ⟨hd, hrest⟩, s, hs => by
      simp only [List.sum_cons] at hs
      by_cases hle : s ≤ ds.sum
      · obtain ⟨mask, hlen, hsum⟩ := brown_completeness ds hrest s hle
        exact ⟨false :: mask, by simp [hlen], by simpa [subsetSum] using hsum⟩
      · have hs_ge_d : d ≤ s := by omega
        obtain ⟨mask, hlen, hsum⟩ := brown_completeness ds hrest (s - d) (by omega)
        refine ⟨true :: mask, by simp [hlen], ?_⟩
        simp only [subsetSum, hsum]; omega

private theorem subsetSum_map_two :
    ∀ (ds : List ℕ) (mask : List Bool),
      mask.length = ds.length →
      subsetSum (ds.map (2 * ·)) mask = 2 * subsetSum ds mask
  | [], [], _ => rfl
  | _ :: _, [], h => by simp at h
  | [], _ :: _, h => by simp at h
  | d :: ds, false :: bs, h => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [List.map_cons, subsetSum, subsetSum_map_two ds bs h]
  | d :: ds, true :: bs, h => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [List.map_cons, subsetSum, subsetSum_map_two ds bs h]
      ring

/-- **Pillar 3D — Even-Step Brown-Complete `HetAdjusterChain` Interval Forcing**:
If `c.steps = ds.map (2 * ·)` with `BrownComplete ds`, then `c` realizes a simple cycle of EVERY
even length `c.baseWalk.length + 2 * s` for `0 ≤ s ≤ ds.sum`. -/
theorem exists_cycle_of_even_brown_complete {G : SimpleGraph V} {v : V}
    (c : HetAdjusterChain G v v) (hcyc : c.baseWalk.IsCycle)
    (halt : c.altVertices.Nodup) (hdisj : ∀ z ∈ c.altVertices, z ∉ c.baseWalk.support)
    (ds : List ℕ) (hsteps : c.steps = ds.map (2 * ·)) (hbrown : BrownComplete ds)
    {s : ℕ} (hs : s ≤ ds.sum) :
    ∃ p : G.Walk v v, p.IsCycle ∧ p.length = c.baseWalk.length + 2 * s := by
  obtain ⟨mask, hlen, hsum⟩ := brown_completeness ds hbrown s hs
  have hlen' : mask.length = c.steps.length := by rw [hsteps, List.length_map, hlen]
  refine ⟨c.realize mask, realize_isCycle c hcyc halt hdisj mask hlen', ?_⟩
  rw [realize_length c mask hlen', hsteps, subsetSum_map_two ds mask hlen, hsum]

/-- **Pillar 3E — `O(log a)` Dyadic-Step `HasPower G` Closure**:
An even base cycle of length `2a` (`a ≥ 2`) carrying a Brown-complete even-step heterogeneous
adjuster chain with `a - 2 ≤ ds.sum` (requiring only `⌈log₂ a⌉` adjusters with dyadic steps
`2, 2, 4, 8, ...`!) unconditionally forces `HasPower G`. -/
theorem hasPower_of_even_brown_complete {G : SimpleGraph V} {v : V} {a : ℕ}
    (c : HetAdjusterChain G v v) (hcyc : c.baseWalk.IsCycle)
    (heven : c.baseWalk.length = 2 * a) (ha : 2 ≤ a)
    (halt : c.altVertices.Nodup) (hdisj : ∀ z ∈ c.altVertices, z ∉ c.baseWalk.support)
    (ds : List ℕ) (hsteps : c.steps = ds.map (2 * ·)) (hbrown : BrownComplete ds)
    (hdense : a - 2 ≤ ds.sum) :
    HasPower G := by
  refine hasPower_of_consecutive_even_cycles G ha (b := a + ds.sum) (by omega) ?_
  intro t hlo hhi
  obtain ⟨p, hp, hlen⟩ :=
    exists_cycle_of_even_brown_complete c hcyc halt hdisj ds hsteps hbrown (s := t - a) (by omega)
  exact ⟨v, p, hp, by omega⟩

/-- **Pillar 3F — Direct Subset-Sum Power-of-2 Certificate**:
If ANY boolean mask on a `HetAdjusterChain` hits a power of 2 `2 ^ k` (`k ≥ 2`), then `HasPower G`.
(Directly certifies all 17/17 girth 5–14 cubic benchmarks from our C++20 audit!) -/
theorem hasPower_of_subset_sum_hit {G : SimpleGraph V} {v : V}
    (c : HetAdjusterChain G v v) (hcyc : c.baseWalk.IsCycle)
    (halt : c.altVertices.Nodup) (hdisj : ∀ z ∈ c.altVertices, z ∉ c.baseWalk.support)
    (mask : List Bool) (hlen : mask.length = c.steps.length)
    {k : ℕ} (hk : 2 ≤ k) (hhit : c.baseWalk.length + subsetSum c.steps mask = 2 ^ k) :
    HasPower G := by
  refine ⟨k, v, c.realize mask, hk, realize_isCycle c hcyc halt hdisj mask hlen, ?_⟩
  rw [realize_length c mask hlen, hhit]

end HetAdjusterChain
end HeterogeneousAdjusterChains

/-! ## Section 4 (Pillar 4): Multi-Step Parity-Flip Even-Cycle Interval Lifting -/

section MultiStepParityFlip

variable {V : Type*}

private theorem concat3_isPath' {G : SimpleGraph V} {u1 v1 v2 u2 : V}
    (p1 : G.Walk u1 v1) (d : G.Walk v1 v2) (p2 : G.Walk u2 v2)
    (hp1 : p1.IsPath) (hd : d.IsPath) (hp2 : p2.IsPath)
    (hp1_p2 : ∀ x ∈ p1.support, x ∉ p2.support)
    (hp1_d : ∀ x ∈ p1.support, x ∈ d.support → x = v1)
    (hp2_d : ∀ x ∈ p2.support, x ∈ d.support → x = v2) :
    ((p1.append d).append p2.reverse).IsPath := by
  have h1 : (p1.append d).IsPath := by
    rw [Walk.isPath_def, Walk.support_append, List.nodup_append]
    have hd_nd := hd.support_nodup
    have hv1_not : v1 ∉ d.support.tail := by
      cases d with
      | nil => simp
      | cons _ rest =>
          rw [Walk.support_cons, List.nodup_cons] at hd_nd
          simpa [Walk.support_cons] using hd_nd.1
    have hdtail_nd : d.support.tail.Nodup := by
      cases hds : d.support with
      | nil => exact absurd hds (Walk.support_ne_nil d)
      | cons _ _ => rw [hds, List.nodup_cons] at hd_nd; exact hd_nd.2
    refine ⟨hp1.support_nodup, hdtail_nd, ?_⟩
    intro x hxp y hyd hxy; subst hxy
    have := hp1_d x hxp (List.mem_of_mem_tail hyd)
    subst this; exact hv1_not hyd
  have hp2r := hp2.reverse
  have hp2r_nd := hp2r.support_nodup
  have hv2_not : v2 ∉ p2.reverse.support.tail := by
    cases hr : p2.reverse with
    | nil => simp
    | cons _ rest =>
        rw [hr, Walk.support_cons, List.nodup_cons] at hp2r_nd
        simpa [Walk.support_cons] using hp2r_nd.1
  have hp2rtail_nd : p2.reverse.support.tail.Nodup := by
    cases hps : p2.reverse.support with
    | nil => exact absurd hps (Walk.support_ne_nil _)
    | cons _ _ => rw [hps, List.nodup_cons] at hp2r_nd; exact hp2r_nd.2
  rw [Walk.isPath_def, Walk.support_append, List.nodup_append]
  refine ⟨h1.support_nodup, hp2rtail_nd, ?_⟩
  intro x hx1 y hy2 hxy; subst hxy
  have hxp2 : x ∈ p2.support := by
    have := List.mem_of_mem_tail hy2
    rwa [Walk.support_reverse, List.mem_reverse] at this
  rw [Walk.support_append, List.mem_append] at hx1
  rcases hx1 with hxp1 | hxd
  · exact hp1_p2 x hxp1 hxp2
  · have := hp2_d x hxp2 (List.mem_of_mem_tail hxd)
    subst this; exact hv2_not hy2

/-- **Pillar 4 — Multi-Step Parity-Flip Even-Cycle Interval Lifting**:
Generalizes Gao–Li–Ma–Xie (2024) Lemma 8 (`s = 1`) to an arbitrary interval of length `s + 1`:
if two ports `u1, u2` are joined inside a region `S` by simple paths of EVERY length
`L0 + 2 * j` (`0 ≤ j ≤ s`, `1 ≤ L0`) — whether `L0` is even OR odd! — and `u1, u2` are linked by
two vertex-disjoint paths `p1, p2` to a vertex-disjoint odd cycle `d1 ∪ d2` outside `S`, then `G`
unconditionally contains a **simple cycle (`Walk.IsCycle`) of EVERY even length `2 * (t + j)`**
for `0 ≤ j ≤ s` (with `t ≥ 2`), forcing `HasPower G` whenever `t - 2 ≤ s`. -/
theorem parity_flip_even_cycle_interval_of_odd_cycle {G : SimpleGraph V}
    {u1 u2 v1 v2 : V} {L0 s : ℕ} (hL0 : 1 ≤ L0) (S : Set V)
    (hpaths : ∀ j : ℕ, j ≤ s →
      ∃ b : G.Walk u1 u2, b.IsPath ∧ b.length = L0 + 2 * j ∧ ∀ x ∈ b.support, x ∈ S)
    (d1 d2 : G.Walk v1 v2) (hd1 : d1.IsPath) (hd2 : d2.IsPath)
    (hd1_pos : 1 ≤ d1.length) (hd2_pos : 1 ≤ d2.length)
    (hodd : Odd (d1.length + d2.length))
    (p1 : G.Walk u1 v1) (p2 : G.Walk u2 v2) (hp1 : p1.IsPath) (hp2 : p2.IsPath)
    (hp1_p2 : ∀ x ∈ p1.support, x ∉ p2.support)
    (hp1_d1 : ∀ x ∈ p1.support, x ∈ d1.support → x = v1)
    (hp1_d2 : ∀ x ∈ p1.support, x ∈ d2.support → x = v1)
    (hp2_d1 : ∀ x ∈ p2.support, x ∈ d1.support → x = v2)
    (hp2_d2 : ∀ x ∈ p2.support, x ∈ d2.support → x = v2)
    (hS_D1 : ∀ x ∈ S, x ∉ d1.support)
    (hS_D2 : ∀ x ∈ S, x ∉ d2.support)
    (hS_p1 : ∀ x ∈ S, x ∈ p1.support → x = u1)
    (hS_p2 : ∀ x ∈ S, x ∈ p2.support → x = u2) :
    ∃ t : ℕ, 2 ≤ t ∧
      ∀ j : ℕ, j ≤ s → ∃ c : G.Walk u1 u1, c.IsCycle ∧ c.length = 2 * (t + j) := by
  let Q1 := (p1.append d1).append p2.reverse
  let Q2 := (p1.append d2).append p2.reverse
  have hQ1_path : Q1.IsPath := concat3_isPath' p1 d1 p2 hp1 hd1 hp2 hp1_p2 hp1_d1 hp2_d1
  have hQ2_path : Q2.IsPath := concat3_isPath' p1 d2 p2 hp1 hd2 hp2 hp1_p2 hp1_d2 hp2_d2
  have hQ1_len : Q1.length = p1.length + d1.length + p2.length := by
    simp [Q1, Walk.length_append, Walk.length_reverse]
  have hQ2_len : Q2.length = p1.length + d2.length + p2.length := by
    simp [Q2, Walk.length_append, Walk.length_reverse]
  have hQ1_disj : ∀ (b : G.Walk u1 u2), (∀ x ∈ b.support, x ∈ S) →
      ∀ x ∈ b.support, x ∈ Q1.support → x = u1 ∨ x = u2 := by
    intro b hb x hxb hxQ
    have hxS := hb x hxb
    simp only [Q1, Walk.support_append, List.mem_append] at hxQ
    rcases hxQ with (hxp1 | hxd1) | hxp2r
    · exact Or.inl (hS_p1 x hxS hxp1)
    · exact absurd (List.mem_of_mem_tail hxd1) (hS_D1 x hxS)
    · have hxp2 : x ∈ p2.support := by
        have := List.mem_of_mem_tail hxp2r
        rwa [Walk.support_reverse, List.mem_reverse] at this
      exact Or.inr (hS_p2 x hxS hxp2)
  have hQ2_disj : ∀ (b : G.Walk u1 u2), (∀ x ∈ b.support, x ∈ S) →
      ∀ x ∈ b.support, x ∈ Q2.support → x = u1 ∨ x = u2 := by
    intro b hb x hxb hxQ
    have hxS := hb x hxb
    simp only [Q2, Walk.support_append, List.mem_append] at hxQ
    rcases hxQ with (hxp1 | hxd2) | hxp2r
    · exact Or.inl (hS_p1 x hxS hxp1)
    · exact absurd (List.mem_of_mem_tail hxd2) (hS_D2 x hxS)
    · have hxp2 : x ∈ p2.support := by
        have := List.mem_of_mem_tail hxp2r
        rwa [Walk.support_reverse, List.mem_reverse] at this
      exact Or.inr (hS_p2 x hxS hxp2)
  rcases hodd with ⟨m0, hm0⟩
  by_cases hev : Even (L0 + Q1.length)
  · rcases hev with ⟨t, ht⟩
    have ht2 : 2 ≤ t := by
      obtain ⟨b0, _, _, hb0S⟩ := hpaths 0 (Nat.zero_le s)
      have hu1S : u1 ∈ S := hb0S u1 (Walk.start_mem_support b0)
      have hp1_pos : 1 ≤ p1.length := by
        cases p1 with
        | nil => exact absurd (Walk.start_mem_support d1) (hS_D1 u1 hu1S)
        | cons _ _ => simp
      omega
    refine ⟨t, ht2, ?_⟩
    intro j hj
    obtain ⟨b, hb_path, hb_len, hbS⟩ := hpaths j hj
    refine ⟨b.append Q1.reverse,
      isCycle_append_reverse_of_internally_disjoint b Q1 hb_path hQ1_path (by omega)
        (hQ1_disj b hbS), ?_⟩
    rw [Walk.length_append, Walk.length_reverse, hb_len]; omega
  · have hev2 : Even (L0 + Q2.length) := by
      rw [Nat.even_iff] at hev ⊢; omega
    rcases hev2 with ⟨t, ht⟩
    have ht2 : 2 ≤ t := by
      obtain ⟨b0, _, _, hb0S⟩ := hpaths 0 (Nat.zero_le s)
      have hu1S : u1 ∈ S := hb0S u1 (Walk.start_mem_support b0)
      have hp1_pos : 1 ≤ p1.length := by
        cases p1 with
        | nil => exact absurd (Walk.start_mem_support d2) (hS_D2 u1 hu1S)
        | cons _ _ => simp
      omega
    refine ⟨t, ht2, ?_⟩
    intro j hj
    obtain ⟨b, hb_path, hb_len, hbS⟩ := hpaths j hj
    refine ⟨b.append Q2.reverse,
      isCycle_append_reverse_of_internally_disjoint b Q2 hb_path hQ2_path (by omega)
        (hQ2_disj b hbS), ?_⟩
    rw [Walk.length_append, Walk.length_reverse, hb_len]; omega

end MultiStepParityFlip

#print axioms cubic_bfs_interior_full_degree
#print axioms cubic_bfs_top_layer_deg_le_two
#print axioms cubic_bfs_bottom_expanding_deg_le_two
#print axioms cubic_two_layer_expanding_max_deg_le_two
#print axioms cubic_three_layer_bipartite_chorded_forces_sink
#print axioms cubic_three_layer_expanding_no_bipartite_chorded_cycle
#print axioms cubic_bfs_shell_degree_cut_identity
#print axioms multilayer_asymmetric_bfs_lca_cycle_interval
#print axioms hasPower_of_multilayer_asymmetric_bfs_chorded_cycle
#print axioms chorded_even_cycle_girth_lower_bound
#print axioms hasPower_of_girth_bounded_height_chorded_cycle
#print axioms HetAdjusterChain.realize_length
#print axioms HetAdjusterChain.realize_isCycle
#print axioms HetAdjusterChain.brown_completeness
#print axioms HetAdjusterChain.exists_cycle_of_even_brown_complete
#print axioms HetAdjusterChain.hasPower_of_even_brown_complete
#print axioms HetAdjusterChain.hasPower_of_subset_sum_hit
#print axioms parity_flip_even_cycle_interval_of_odd_cycle

end E64Wave8Agent1
