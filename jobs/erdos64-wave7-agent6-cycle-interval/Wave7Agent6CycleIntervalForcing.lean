import Shadow
import Wave6Agent3KestenMcKayBreak

/-!
# Wave 7 Agent #6: Structural Even-Cycle Interval Forcing for Erdős Problem #64

Attacking the unproved structural premise of Wave 6 Agent #3's
`erdos64_of_even_cycle_interval_forcing` across three genuine graph-theoretic pillars
formalized directly on `SimpleGraph V` in Lean 4.36.0:

1. **Pillar 1 — Bondy–Simonovits–Verstraëte (1974 / 2000) Chorded-Cycle Path-Spectrum,
   BFS-LCA Even-Cycle Interval Lifting & Cubic 2-Layer BFS-Shell Obstruction**:
   - `isCycle_append_reverse_of_internally_disjoint`: Glues any two internally vertex-disjoint
     simple `(u, v)`-paths of total length `≥ 3` into a simple cycle (`Walk.IsCycle`).
   - `bsv_chorded_cycle_all_even_ab_paths`: Every bipartite even cycle `C_{2m}` (`m ≥ 3`) with
     any bipartite chord `v_0 — v_{2r+1}` (`1 ≤ r ≤ m - 2`) and any nontrivial 2-coloring of
     its even-index vertices `V_0` contains simple bichromatic paths of EVERY even length
     `2, 4, ..., 2(m - 1)`.
   - `bfs_lca_even_cycle_interval` & `hasPower_of_bfs_chorded_cycle`: Lifting through a BFS tree
     LCA of height `h ≥ 1` produces EVERY even cycle length in `[2h + 2, 2h + 2m - 2]`, forcing
     `HasPower G` unconditionally whenever `m ≥ h + 1`.
   - `cubic_two_layer_deg_le_two` & `cubic_two_layer_no_chorded_cycle`: Proves formally why
     Verstraëte / Sudakov–Verstraëte 2-layer BFS shells fail on cubic (`C-N-R`) graphs: every
     vertex in `L_i` (`i ≥ 1`) has degree `≤ 2` in `L_i ∪ L_{i+1}`, blocking bipartite chorded
     cycles inside any 2-layer BFS shell of a cubic graph.

2. **Pillar 2 — Gao–Li–Ma–Xie (2024) Quasi-Diagonal Even+Odd Cycle Gluing**:
   - `quasi_diagonal_even_odd_consecutive_even_cycles`: Any even cycle split at quasi-diagonal
     ports (arcs differing by `2`) joined by two disjoint paths to a disjoint odd cycle forces
     two simple cycles of consecutive even lengths `2t` and `2t + 2`.
   - `hasPower_of_quasi_diagonal_even_odd_hit`: Immediate `HasPower G` closure when `{2t, 2t+2}`
     hits a power of 2.

3. **Pillar 3 — Arbitrary-Girth Quasi-Diagonal `AdjusterChain` (Liu–Montgomery `δ ∈ {1, 2}`)**:
   - Generalizes Wave 6 Agent #3's triangle-only `BypassChain` (`g = 3`) to arbitrary fixed girth
     `g ≥ 3` with arbitrary disjoint path switches of uniform step `δ` (`δ = 1` for odd-cycle
     quasi-diagonal adjusters at any odd girth `2s + 1 ≥ 3`; `δ = 2` for even-cycle quasi-diagonal
     adjusters at any even girth `2s ≥ 6`).
   - `AdjusterChain.realize_length`, `realize_isCycle`, `exists_cycle_of_step_Icc`,
     `hasPower_of_delta1_adjusters`, `hasPower_of_delta2_even_adjusters`,
     `interior_edge_saturation`.
-/

namespace E64Wave7Agent6
open SimpleGraph Erdos64Closure E64Wave6Agent3

/-! ## Section 1: Core Simple-Cycle Gluing Engine -/

section CoreGluing

variable {V : Type*}

private theorem support_eq_cons_start {G : SimpleGraph V} {a b : V} (p : G.Walk a b) :
    p.support = a :: p.support.tail := by
  cases p <;> rfl

private theorem start_notMem_support_tail_of_isPath {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (hp : p.IsPath) : a ∉ p.support.tail := by
  have hnd := hp.support_nodup
  rw [support_eq_cons_start p, List.nodup_cons] at hnd
  exact hnd.1

private theorem support_tail_nodup_of_isPath {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (hp : p.IsPath) : p.support.tail.Nodup := by
  have hnd := hp.support_nodup
  rw [support_eq_cons_start p, List.nodup_cons] at hnd
  exact hnd.2

private theorem mem_support_of_mem_edges {G : SimpleGraph V} :
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
      · exact List.mem_cons_of_mem _ (mem_support_of_mem_edges hmem hx)

private theorem support_append_tail {G : SimpleGraph V} {a u b : V}
    (p : G.Walk a u) (q : G.Walk u b) :
    (p.append q).support.tail = p.support.tail ++ q.support.tail := by
  rw [Walk.support_append, support_eq_cons_start p]
  rfl

private theorem length_eq_one_of_isPath_mem_edges_endpoints {G : SimpleGraph V} :
    ∀ {u v : V} (p : G.Walk u v), p.IsPath → s(u, v) ∈ p.edges → p.length = 1
  | _, _, .nil, _, he => by simp at he
  | u, v, .cons (v := w) h rest, hp, he => by
      have hnd := hp.support_nodup
      rw [Walk.support_cons, List.nodup_cons] at hnd
      simp only [Walk.edges_cons, List.mem_cons] at he
      rcases he with hEq | hmem
      · rw [Sym2.eq_iff] at hEq
        rcases hEq with ⟨_, hwv⟩ | ⟨huw, _⟩
        · subst hwv
          cases rest with
          | nil => rfl
          | cons h2 rest2 =>
              exfalso
              have hnd2 := hnd.2
              rw [Walk.support_cons, List.nodup_cons] at hnd2
              exact hnd2.1 (Walk.end_mem_support rest2)
        · exfalso
          exact hnd.1 (by rw [huw]; exact Walk.start_mem_support rest)
      · exfalso
        exact hnd.1 (mem_support_of_mem_edges hmem (by simp))

/-- **Core Simple-Cycle Gluing Theorem**: Two internally vertex-disjoint simple `(u, v)`-paths
`p` and `q` with `p.length + q.length ≥ 3` glue into a simple cycle `p.append q.reverse` of
exact length `p.length + q.length`. -/
theorem isCycle_append_reverse_of_internally_disjoint {G : SimpleGraph V} {u v : V}
    (p q : G.Walk u v) (hp : p.IsPath) (hq : q.IsPath)
    (hlen : 3 ≤ p.length + q.length)
    (hdisj : ∀ x, x ∈ p.support → x ∈ q.support → x = u ∨ x = v) :
    (p.append q.reverse).IsCycle := by
  have hqr : q.reverse.IsPath := hq.reverse
  have hne : p.append q.reverse ≠ Walk.nil := by
    intro hnil
    have hpos : 0 < (p.append q.reverse).length := by
      rw [Walk.length_append, Walk.length_reverse]; omega
    rw [hnil] at hpos; simp at hpos
  have hu_not_ptail := start_notMem_support_tail_of_isPath p hp
  have hv_not_qrtail := start_notMem_support_tail_of_isPath q.reverse hqr
  have htail_nd : (p.append q.reverse).support.tail.Nodup := by
    rw [support_append_tail, List.nodup_append]
    refine ⟨support_tail_nodup_of_isPath p hp, support_tail_nodup_of_isPath q.reverse hqr, ?_⟩
    intro x hxp y hyq hxy
    subst hxy
    have hxp' : x ∈ p.support := List.mem_of_mem_tail hxp
    have hxq' : x ∈ q.support := by
      have := List.mem_of_mem_tail hyq
      rwa [Walk.support_reverse, List.mem_reverse] at this
    rcases hdisj x hxp' hxq' with rfl | rfl
    · exact hu_not_ptail hxp
    · exact hv_not_qrtail hyq
  have hedges_nd : (p.append q.reverse).edges.Nodup := by
    rw [Walk.edges_append, List.nodup_append]
    refine ⟨hp.edges_nodup, hqr.edges_nodup, ?_⟩
    intro e hep e' heq hee
    subst hee
    have heq' : e ∈ q.edges := by rwa [Walk.edges_reverse, List.mem_reverse] at heq
    induction e using Sym2.ind with
    | _ x y =>
        have hxp : x ∈ p.support := mem_support_of_mem_edges hep (by simp)
        have hyp : y ∈ p.support := mem_support_of_mem_edges hep (by simp)
        have hxq : x ∈ q.support := mem_support_of_mem_edges heq' (by simp)
        have hyq : y ∈ q.support := mem_support_of_mem_edges heq' (by simp)
        have hxy_ne : x ≠ y := G.ne_of_adj (Walk.adj_of_mem_edges p hep)
        have hxe : s(x, y) = s(u, v) := by
          rcases hdisj x hxp hxq with rfl | rfl <;>
          rcases hdisj y hyp hyq with rfl | rfl
          · exact absurd rfl hxy_ne
          · rfl
          · exact Sym2.eq_swap
          · exact absurd rfl hxy_ne
        rw [hxe] at hep heq'
        have hp1 := length_eq_one_of_isPath_mem_edges_endpoints p hp hep
        have hq1 := length_eq_one_of_isPath_mem_edges_endpoints q hq heq'
        omega
  exact ⟨⟨⟨hedges_nd⟩, hne⟩, htail_nd⟩

end CoreGluing

/-! ## Section 2 (Pillar 1): Bondy–Simonovits–Verstraëte Chorded-Cycle Path-Spectrum,
BFS-LCA Lifting & Cubic 2-Layer BFS-Shell Obstruction -/

section BondySimonovitsVerstraete

variable {V : Type*}

/-- An embedded bipartite even cycle `C_{2m}` (`m ≥ 3`) with a bipartite chord `v_0 — v_{2r+1}`
(`1 ≤ r ≤ m - 2`) in a simple graph `G`. -/
structure ChordedEvenCycle (G : SimpleGraph V) (m r : ℕ) where
  hm : 3 ≤ m
  hr_lo : 1 ≤ r
  hr_hi : r ≤ m - 2
  v : Fin (2 * m) → V
  hv_inj : Function.Injective v
  hadj_cyc : ∀ i : Fin (2 * m),
    G.Adj (v i) (v ⟨(i.val + 1) % (2 * m), Nat.mod_lt _ (by omega)⟩)
  hadj_chord : G.Adj (v ⟨0, by omega⟩) (v ⟨2 * r + 1, by omega⟩)

namespace ChordedEvenCycle

/-- Build a forward walk of length `len` along the cycle starting at `start` (mod `2m`). -/
def fwdWalk {G : SimpleGraph V} {m r : ℕ} (C : ChordedEvenCycle G m r) :
    (start len : ℕ) →
      G.Walk (C.v ⟨start % (2 * m), Nat.mod_lt _ (by have := C.hm; omega)⟩)
             (C.v ⟨(start + len) % (2 * m), Nat.mod_lt _ (by have := C.hm; omega)⟩)
  | start, 0 => Walk.nil
  | start, len + 1 =>
      have hpos : 0 < 2 * m := by have := C.hm; omega
      have hstep : (start % (2 * m) + 1) % (2 * m) = (start + 1) % (2 * m) := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      have hadj : G.Adj (C.v ⟨start % (2 * m), Nat.mod_lt _ hpos⟩)
                        (C.v ⟨(start + 1) % (2 * m), Nat.mod_lt _ hpos⟩) := by
        have h := C.hadj_cyc ⟨start % (2 * m), Nat.mod_lt _ hpos⟩
        simpa only [hstep] using h
      Walk.cons hadj ((C.fwdWalk (start + 1) len).copy rfl
        (by congr 1; apply Fin.ext; dsimp only; congr 1; omega))

theorem fwdWalk_length {G : SimpleGraph V} {m r : ℕ} (C : ChordedEvenCycle G m r) :
    ∀ (start len : ℕ), (C.fwdWalk start len).length = len
  | _, 0 => rfl
  | start, len + 1 => by
      simp only [fwdWalk, Walk.length_cons, Walk.length_copy]
      rw [fwdWalk_length C (start + 1) len]

theorem fwdWalk_support {G : SimpleGraph V} {m r : ℕ} (C : ChordedEvenCycle G m r) :
    ∀ (start len : ℕ),
      (C.fwdWalk start len).support =
        (List.range (len + 1)).map (fun t =>
          C.v ⟨(start + t) % (2 * m), Nat.mod_lt _ (by have := C.hm; omega)⟩)
  | start, 0 => by simp [fwdWalk]
  | start, len + 1 => by
      simp only [fwdWalk, Walk.support_cons, Walk.support_copy]
      rw [fwdWalk_support C (start + 1) len]
      conv_rhs => rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      apply congrArg (C.v ⟨start % (2 * m), _⟩ :: ·)
      apply List.map_congr_left
      intro t _
      simp only [Function.comp_apply]
      congr 1
      apply Fin.ext
      dsimp only
      congr 1; omega

theorem fwdWalk_isPath {G : SimpleGraph V} {m r : ℕ} (C : ChordedEvenCycle G m r)
    (start len : ℕ) (hlen : len < 2 * m) :
    (C.fwdWalk start len).IsPath := by
  rw [Walk.isPath_def, fwdWalk_support]
  rw [List.nodup_map_iff_inj_on List.nodup_range]
  intro t1 ht1 t2 ht2 hEq
  rw [List.mem_range] at ht1 ht2
  have hfin := C.hv_inj hEq
  have hval : (start + t1) % (2 * m) = (start + t2) % (2 * m) := congrArg Fin.val hfin
  have hpos : 0 < 2 * m := by have := C.hm; omega
  have h1 : (start + t1) % (2 * m) = (start % (2 * m) + t1) % (2 * m) := by
    rw [Nat.add_mod]; conv_rhs => rw [Nat.add_mod, Nat.mod_mod]
  have h2 : (start + t2) % (2 * m) = (start % (2 * m) + t2) % (2 * m) := by
    rw [Nat.add_mod]; conv_rhs => rw [Nat.add_mod, Nat.mod_mod]
  rw [h1, h2] at hval
  set s := start % (2 * m)
  have hs : s < 2 * m := Nat.mod_lt _ hpos
  have hmod1 : (s + t1) % (2 * m) = if s + t1 < 2 * m then s + t1 else s + t1 - 2 * m := by
    split_ifs with hlt
    · exact Nat.mod_eq_of_lt hlt
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  have hmod2 : (s + t2) % (2 * m) = if s + t2 < 2 * m then s + t2 else s + t2 - 2 * m := by
    split_ifs with hlt
    · exact Nat.mod_eq_of_lt hlt
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [hmod1, hmod2] at hval
  split_ifs at hval <;> omega

theorem fwdWalk_mem_range {G : SimpleGraph V} {m r : ℕ} (C : ChordedEvenCycle G m r)
    (start len : ℕ) : ∀ x ∈ (C.fwdWalk start len).support, x ∈ Set.range C.v := by
  intro x hx
  rw [fwdWalk_support, List.mem_map] at hx
  rcases hx with ⟨t, _, rfl⟩
  exact ⟨_, rfl⟩

private theorem chord_bridge_isPath {G : SimpleGraph V} {m r : ℕ} (C : ChordedEvenCycle G m r)
    {u w : V} (p : G.Walk u (C.v ⟨0, by have := C.hm; omega⟩))
    (q : G.Walk (C.v ⟨2 * r + 1, by have := C.hm; have := C.hr_hi; omega⟩) w)
    (hp : p.IsPath) (hq : q.IsPath)
    (hdisj : ∀ x ∈ p.support, x ∉ q.support) :
    (p.append (Walk.cons C.hadj_chord q)).IsPath := by
  rw [Walk.isPath_def, Walk.support_append, Walk.support_cons, List.tail_cons, List.nodup_append]
  refine ⟨hp.support_nodup, hq.support_nodup, ?_⟩
  intro x hxp y hyq hxy
  subst hxy
  exact hdisj x hxp hyq

/-- **Type 1 Chord Path** (Arc 1 `→ 0 → 2r+1 →` Arc 2):
For `0 ≤ a ≤ r` and `1 ≤ b ≤ m - r - 1`, produces a simple path of length `2(a + b)`
from `v_{2a}` to `v_{2(r+b)}` inside `Set.range C.v`. -/
theorem exists_chord_path_type1 {G : SimpleGraph V} {m r : ℕ} (C : ChordedEvenCycle G m r)
    {a b : ℕ} (ha : a ≤ r) (hb1 : 1 ≤ b) (hb2 : b ≤ m - r - 1) :
    ∃ p : G.Walk (C.v ⟨2 * a, by have := C.hm; have := C.hr_hi; omega⟩)
                 (C.v ⟨2 * (r + b), by have := C.hm; have := C.hr_hi; omega⟩),
      p.IsPath ∧ p.length = 2 * (a + b) ∧ ∀ x ∈ p.support, x ∈ Set.range C.v := by
  have hm := C.hm; have hr1 := C.hr_lo; have hrh := C.hr_hi
  have h1 : (2 * a) % (2 * m) = 2 * a := Nat.mod_eq_of_lt (by omega)
  have h2 : (2 * r + 1 + (2 * b - 1)) % (2 * m) = 2 * (r + b) := by
    have heq : 2 * r + 1 + (2 * b - 1) = 2 * (r + b) := by omega
    rw [heq]
    exact Nat.mod_eq_of_lt (by omega)
  have h0 : 0 % (2 * m) = 0 := Nat.zero_mod _
  have h2r1 : (2 * r + 1) % (2 * m) = 2 * r + 1 := Nat.mod_eq_of_lt (by omega)
  let p0 := (C.fwdWalk 0 (2 * a)).reverse
  let q0 := C.fwdWalk (2 * r + 1) (2 * b - 1)
  have hp0_path : p0.IsPath := (C.fwdWalk_isPath 0 (2 * a) (by omega)).reverse
  have hq0_path : q0.IsPath := C.fwdWalk_isPath (2 * r + 1) (2 * b - 1) (by omega)
  let p : G.Walk (C.v ⟨2 * a, by omega⟩) (C.v ⟨0, by omega⟩) :=
    p0.copy (by simp [h1]) (by simp [h0])
  let q : G.Walk (C.v ⟨2 * r + 1, by omega⟩) (C.v ⟨2 * (r + b), by omega⟩) :=
    q0.copy (by simp [h2r1]) (by simp [h2])
  have hp_path : p.IsPath := by simpa [p] using hp0_path
  have hq_path : q.IsPath := by simpa [q] using hq0_path
  have hdisj : ∀ x ∈ p.support, x ∉ q.support := by
    intro x hxp hxq
    rw [Walk.support_copy] at hxp hxq
    rw [Walk.support_reverse, List.mem_reverse, fwdWalk_support, List.mem_map] at hxp
    rw [fwdWalk_support, List.mem_map] at hxq
    rcases hxp with ⟨t1, ht1, rfl⟩
    rcases hxq with ⟨t2, ht2, hEq⟩
    rw [List.mem_range] at ht1 ht2
    have hval := congrArg Fin.val (C.hv_inj hEq)
    dsimp only at hval
    have hlt1 : (0 + t1) % (2 * m) = 0 + t1 := Nat.mod_eq_of_lt (by omega)
    have hlt2 : (2 * r + 1 + t2) % (2 * m) = 2 * r + 1 + t2 := Nat.mod_eq_of_lt (by omega)
    rw [hlt1, hlt2] at hval
    omega
  refine ⟨p.append (Walk.cons C.hadj_chord q), chord_bridge_isPath C p q hp_path hq_path hdisj, ?_, ?_⟩
  · simp only [Walk.length_append, Walk.length_cons, p, q, Walk.length_copy, p0, q0,
      Walk.length_reverse, fwdWalk_length]
    omega
  · intro x hx
    rw [Walk.support_append, Walk.support_cons, List.tail_cons, List.mem_append] at hx
    rcases hx with hxp | hxq
    · rw [Walk.support_copy, Walk.support_reverse, List.mem_reverse] at hxp
      exact C.fwdWalk_mem_range 0 (2 * a) x hxp
    · rw [Walk.support_copy] at hxq
      exact C.fwdWalk_mem_range (2 * r + 1) (2 * b - 1) x hxq

/-- **Type 2 Chord Path** (Arc 2 `→ 0 → 2r+1 →` Arc 1):
For `0 ≤ a ≤ m - r - 1` and `1 ≤ b ≤ r`, produces a simple path of length `2(a + b)`
from `v_{2((m - a) % m)}` to `v_{2(r + 1 - b)}` inside `Set.range C.v`. -/
theorem exists_chord_path_type2 {G : SimpleGraph V} {m r : ℕ} (C : ChordedEvenCycle G m r)
    {a b : ℕ} (ha : a ≤ m - r - 1) (hb1 : 1 ≤ b) (hb2 : b ≤ r) :
    ∃ p : G.Walk (C.v ⟨2 * ((m - a) % m), by
                    have := C.hm; have := Nat.mod_lt (m - a) (by omega : 0 < m); omega⟩)
                 (C.v ⟨2 * (r + 1 - b), by have := C.hm; have := C.hr_hi; omega⟩),
      p.IsPath ∧ p.length = 2 * (a + b) ∧ ∀ x ∈ p.support, x ∈ Set.range C.v := by
  have hm := C.hm; have hr1 := C.hr_lo; have hrh := C.hr_hi
  have hmod_lt : (m - a) % m < m := Nat.mod_lt _ (by omega)
  have h1 : (2 * m - 2 * a) % (2 * m) = 2 * ((m - a) % m) := by
    by_cases ha0 : a = 0
    · subst ha0; simp
    · have hlt1 : (2 * m - 2 * a) % (2 * m) = 2 * m - 2 * a := Nat.mod_eq_of_lt (by omega)
      have hlt2 : (m - a) % m = m - a := Nat.mod_eq_of_lt (by omega)
      rw [hlt1, hlt2]; omega
  have h2 : (2 * m - 2 * a + 2 * a) % (2 * m) = 0 := by
    have : 2 * m - 2 * a + 2 * a = 2 * m := by omega
    rw [this, Nat.mod_self]
  have h3 : (2 * (r + 1 - b)) % (2 * m) = 2 * (r + 1 - b) := Nat.mod_eq_of_lt (by omega)
  have h4 : (2 * (r + 1 - b) + (2 * b - 1)) % (2 * m) = 2 * r + 1 := by
    have heq : 2 * (r + 1 - b) + (2 * b - 1) = 2 * r + 1 := by omega
    rw [heq]
    exact Nat.mod_eq_of_lt (by omega)
  let p0 := C.fwdWalk (2 * m - 2 * a) (2 * a)
  let q0 := (C.fwdWalk (2 * (r + 1 - b)) (2 * b - 1)).reverse
  have hp0_path : p0.IsPath := C.fwdWalk_isPath (2 * m - 2 * a) (2 * a) (by omega)
  have hq0_path : q0.IsPath := (C.fwdWalk_isPath (2 * (r + 1 - b)) (2 * b - 1) (by omega)).reverse
  let p : G.Walk (C.v ⟨2 * ((m - a) % m), by omega⟩) (C.v ⟨0, by omega⟩) :=
    p0.copy (by simp [h1]) (by simp [h2])
  let q : G.Walk (C.v ⟨2 * r + 1, by omega⟩) (C.v ⟨2 * (r + 1 - b), by omega⟩) :=
    q0.copy (by simp [h4]) (by simp [h3])
  have hp_path : p.IsPath := by simpa [p] using hp0_path
  have hq_path : q.IsPath := by simpa [q] using hq0_path
  have hdisj : ∀ x ∈ p.support, x ∉ q.support := by
    intro x hxp hxq
    rw [Walk.support_copy] at hxp hxq
    rw [fwdWalk_support, List.mem_map] at hxp
    rw [Walk.support_reverse, List.mem_reverse, fwdWalk_support, List.mem_map] at hxq
    rcases hxp with ⟨t1, ht1, rfl⟩
    rcases hxq with ⟨t2, ht2, hEq⟩
    rw [List.mem_range] at ht1 ht2
    have hval := congrArg Fin.val (C.hv_inj hEq)
    dsimp only at hval
    have hq_lt : (2 * (r + 1 - b) + t2) % (2 * m) = 2 * (r + 1 - b) + t2 :=
      Nat.mod_eq_of_lt (by omega)
    rw [hq_lt] at hval
    by_cases ht1_end : t1 = 2 * a
    · subst ht1_end
      have : (2 * m - 2 * a + 2 * a) % (2 * m) = 0 := by
        have : 2 * m - 2 * a + 2 * a = 2 * m := by omega
        rw [this, Nat.mod_self]
      rw [this] at hval; omega
    · have hp_lt : (2 * m - 2 * a + t1) % (2 * m) = 2 * m - 2 * a + t1 :=
        Nat.mod_eq_of_lt (by omega)
      rw [hp_lt] at hval; omega
  refine ⟨p.append (Walk.cons C.hadj_chord q), chord_bridge_isPath C p q hp_path hq_path hdisj, ?_, ?_⟩
  · simp only [Walk.length_append, Walk.length_cons, p, q, Walk.length_copy, p0, q0,
      Walk.length_reverse, fwdWalk_length]
    omega
  · intro x hx
    rw [Walk.support_append, Walk.support_cons, List.tail_cons, List.mem_append] at hx
    rcases hx with hxp | hxq
    · rw [Walk.support_copy] at hxp
      exact C.fwdWalk_mem_range (2 * m - 2 * a) (2 * a) x hxp
    · rw [Walk.support_copy, Walk.support_reverse, List.mem_reverse] at hxq
      exact C.fwdWalk_mem_range (2 * (r + 1 - b)) (2 * b - 1) x hxq

/-- **Type 3 Chord Path** (Arc 2 `→ 0 → 2r+1 →` Arc 2, disjoint):
For `0 ≤ a` and `1 ≤ b` with `a + b ≤ m - r - 1`, produces a simple path of length `2(a + b)`
from `v_{2((m - a) % m)}` to `v_{2(r + b)}` inside `Set.range C.v`. -/
theorem exists_chord_path_type3 {G : SimpleGraph V} {m r : ℕ} (C : ChordedEvenCycle G m r)
    {a b : ℕ} (hb1 : 1 ≤ b) (hab : a + b ≤ m - r - 1) :
    ∃ p : G.Walk (C.v ⟨2 * ((m - a) % m), by
                    have := C.hm; have := Nat.mod_lt (m - a) (by omega : 0 < m); omega⟩)
                 (C.v ⟨2 * (r + b), by have := C.hm; have := C.hr_hi; omega⟩),
      p.IsPath ∧ p.length = 2 * (a + b) ∧ ∀ x ∈ p.support, x ∈ Set.range C.v := by
  have hm := C.hm; have hr1 := C.hr_lo; have hrh := C.hr_hi
  have hmod_lt : (m - a) % m < m := Nat.mod_lt _ (by omega)
  have h1 : (2 * m - 2 * a) % (2 * m) = 2 * ((m - a) % m) := by
    by_cases ha0 : a = 0
    · subst ha0; simp
    · have hlt1 : (2 * m - 2 * a) % (2 * m) = 2 * m - 2 * a := Nat.mod_eq_of_lt (by omega)
      have hlt2 : (m - a) % m = m - a := Nat.mod_eq_of_lt (by omega)
      rw [hlt1, hlt2]; omega
  have h2 : (2 * m - 2 * a + 2 * a) % (2 * m) = 0 := by
    have : 2 * m - 2 * a + 2 * a = 2 * m := by omega
    rw [this, Nat.mod_self]
  have h2r1 : (2 * r + 1) % (2 * m) = 2 * r + 1 := Nat.mod_eq_of_lt (by omega)
  have h3 : (2 * r + 1 + (2 * b - 1)) % (2 * m) = 2 * (r + b) := by
    have heq : 2 * r + 1 + (2 * b - 1) = 2 * (r + b) := by omega
    rw [heq]
    exact Nat.mod_eq_of_lt (by omega)
  let p0 := C.fwdWalk (2 * m - 2 * a) (2 * a)
  let q0 := C.fwdWalk (2 * r + 1) (2 * b - 1)
  have hp0_path : p0.IsPath := C.fwdWalk_isPath (2 * m - 2 * a) (2 * a) (by omega)
  have hq0_path : q0.IsPath := C.fwdWalk_isPath (2 * r + 1) (2 * b - 1) (by omega)
  let p : G.Walk (C.v ⟨2 * ((m - a) % m), by omega⟩) (C.v ⟨0, by omega⟩) :=
    p0.copy (by simp [h1]) (by simp [h2])
  let q : G.Walk (C.v ⟨2 * r + 1, by omega⟩) (C.v ⟨2 * (r + b), by omega⟩) :=
    q0.copy (by simp [h2r1]) (by simp [h3])
  have hp_path : p.IsPath := by simpa [p] using hp0_path
  have hq_path : q.IsPath := by simpa [q] using hq0_path
  have hdisj : ∀ x ∈ p.support, x ∉ q.support := by
    intro x hxp hxq
    rw [Walk.support_copy] at hxp hxq
    rw [fwdWalk_support, List.mem_map] at hxp hxq
    rcases hxp with ⟨t1, ht1, rfl⟩
    rcases hxq with ⟨t2, ht2, hEq⟩
    rw [List.mem_range] at ht1 ht2
    have hval := congrArg Fin.val (C.hv_inj hEq)
    dsimp only at hval
    have hq_lt : (2 * r + 1 + t2) % (2 * m) = 2 * r + 1 + t2 := Nat.mod_eq_of_lt (by omega)
    rw [hq_lt] at hval
    by_cases ht1_end : t1 = 2 * a
    · subst ht1_end
      have : (2 * m - 2 * a + 2 * a) % (2 * m) = 0 := by
        have : 2 * m - 2 * a + 2 * a = 2 * m := by omega
        rw [this, Nat.mod_self]
      rw [this] at hval; omega
    · have hp_lt : (2 * m - 2 * a + t1) % (2 * m) = 2 * m - 2 * a + t1 :=
        Nat.mod_eq_of_lt (by omega)
      rw [hp_lt] at hval; omega
  refine ⟨p.append (Walk.cons C.hadj_chord q), chord_bridge_isPath C p q hp_path hq_path hdisj, ?_, ?_⟩
  · simp only [Walk.length_append, Walk.length_cons, p, q, Walk.length_copy, p0, q0, fwdWalk_length]
    omega
  · intro x hx
    rw [Walk.support_append, Walk.support_cons, List.tail_cons, List.mem_append] at hx
    rcases hx with hxp | hxq
    · rw [Walk.support_copy] at hxp
      exact C.fwdWalk_mem_range (2 * m - 2 * a) (2 * a) x hxp
    · rw [Walk.support_copy] at hxq
      exact C.fwdWalk_mem_range (2 * r + 1) (2 * b - 1) x hxq

/-- Reflect a `ChordedEvenCycle G m r` to `ChordedEvenCycle G m (m - 1 - r)` via `i ↦ (2m - i) % 2m`. -/
def reflect {G : SimpleGraph V} {m r : ℕ} (C : ChordedEvenCycle G m r) :
    ChordedEvenCycle G m (m - 1 - r) where
  hm := C.hm
  hr_lo := by have := C.hm; have := C.hr_hi; omega
  hr_hi := by have := C.hm; have := C.hr_lo; omega
  v := fun i => C.v ⟨(2 * m - i.val) % (2 * m), Nat.mod_lt _ (by have := C.hm; omega)⟩
  hv_inj := by
    intro i j hEq
    have hfin := C.hv_inj hEq
    have hval := congrArg Fin.val hfin
    dsimp only at hval
    have hm := C.hm; have hi := i.isLt; have hj := j.isLt
    by_cases hi0 : i.val = 0 <;> by_cases hj0 : j.val = 0
    · exact Fin.ext (by omega)
    · have hj_lt : (2 * m - j.val) % (2 * m) = 2 * m - j.val := Nat.mod_eq_of_lt (by omega)
      rw [hi0, Nat.sub_zero, Nat.mod_self, hj_lt] at hval; omega
    · have hi_lt : (2 * m - i.val) % (2 * m) = 2 * m - i.val := Nat.mod_eq_of_lt (by omega)
      rw [hj0, Nat.sub_zero, Nat.mod_self, hi_lt] at hval; omega
    · have hi_lt : (2 * m - i.val) % (2 * m) = 2 * m - i.val := Nat.mod_eq_of_lt (by omega)
      have hj_lt : (2 * m - j.val) % (2 * m) = 2 * m - j.val := Nat.mod_eq_of_lt (by omega)
      rw [hi_lt, hj_lt] at hval
      exact Fin.ext (by omega)
  hadj_cyc := by
    intro i
    have hm := C.hm; have hi := i.isLt
    let j : Fin (2 * m) := ⟨(2 * m - (i.val + 1) % (2 * m)) % (2 * m), Nat.mod_lt _ (by omega)⟩
    have hj_next : (j.val + 1) % (2 * m) = (2 * m - i.val) % (2 * m) := by
      dsimp only [j]
      by_cases hi_last : i.val + 1 = 2 * m
      · have h1 : 1 % (2 * m) = 1 := Nat.mod_eq_of_lt (by omega)
        have h2 : (2 * m - i.val) % (2 * m) = 2 * m - i.val := Nat.mod_eq_of_lt (by omega)
        rw [hi_last, Nat.mod_self, Nat.sub_zero, Nat.mod_self, Nat.zero_add, h1, h2]; omega
      · have hstep1 : (i.val + 1) % (2 * m) = i.val + 1 := Nat.mod_eq_of_lt (by omega)
        rw [hstep1]
        have hstep2 : (2 * m - (i.val + 1)) % (2 * m) = 2 * m - (i.val + 1) :=
          Nat.mod_eq_of_lt (by omega)
        rw [hstep2]
        have hstep3 : 2 * m - (i.val + 1) + 1 = 2 * m - i.val := by omega
        rw [hstep3]
    have h := (C.hadj_cyc j).symm
    simpa only [j, hj_next] using h
  hadj_chord := by
    have hm := C.hm; have hr1 := C.hr_lo; have hrh := C.hr_hi
    have h0 : (2 * m - 0) % (2 * m) = 0 := by simp
    have h1 : (2 * m - (2 * (m - 1 - r) + 1)) % (2 * m) = 2 * r + 1 := by
      have heq : 2 * m - (2 * (m - 1 - r) + 1) = 2 * r + 1 := by omega
      rw [heq]
      exact Nat.mod_eq_of_lt (by omega)
    simpa only [h0, h1] using C.hadj_chord

private theorem mod_add_cancel_right {d u v w : ℕ} (hd : 0 < d) (hu : u < d) (hv : v < d)
    (h : (u + w) % d = (v + w) % d) : u = v := by
  have h1 : (u + w) % d = (u + w % d) % d := by
    rw [Nat.add_mod]; conv_rhs => rw [Nat.add_mod, Nat.mod_mod]
  have h2 : (v + w) % d = (v + w % d) % d := by
    rw [Nat.add_mod]; conv_rhs => rw [Nat.add_mod, Nat.mod_mod]
  rw [h1, h2] at h
  set r := w % d
  have hr : r < d := Nat.mod_lt _ hd
  have hm1 : (u + r) % d = if u + r < d then u + r else u + r - d := by
    split_ifs with hlt
    · exact Nat.mod_eq_of_lt hlt
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  have hm2 : (v + r) % d = if v + r < d then v + r else v + r - d := by
    split_ifs with hlt
    · exact Nat.mod_eq_of_lt hlt
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [hm1, hm2] at h
  split_ifs at h <;> omega

private theorem add_sub_mod_cancel_any {d a b : ℕ} (hd : 0 < d) :
    (a + (b + d - a % d) % d) % d = b % d := by
  have ha : a % d < d := Nat.mod_lt _ hd
  have h1 : (a + (b + d - a % d) % d) % d = (a % d + (b + d - a % d)) % d := by
    rw [Nat.add_mod, Nat.mod_mod]
    conv_rhs => rw [Nat.add_mod, Nat.mod_mod]
  rw [h1]
  have hsum : a % d + (b + d - a % d) = b + d := by omega
  rw [hsum, Nat.add_mod_right]

private theorem add_sub_mod_cancel {d a b : ℕ} (hd : 0 < d) (hb : b < d) :
    (a + (b + d - a % d) % d) % d = b := by
  rw [add_sub_mod_cancel_any hd, Nat.mod_eq_of_lt hb]

private theorem add_neg_mod_eq_zero {d x : ℕ} (hd : 0 < d) :
    (x + (d - x % d) % d) % d = 0 := by
  have h := add_sub_mod_cancel (d := d) (a := x) (b := 0) hd hd
  simpa using h

/-- Algebraic heart of Bondy–Simonovits–Verstraëte: if a `d`-periodic coloring `f : ℕ → Bool`
(`d ∣ m`, `d ∣ k`, `1 ≤ k < m`, `1 ≤ r ≤ m - r - 1`) satisfies the Type 1, Type 2, and (when
`k ≤ m - r - 1`) Type 3 chord invariances, then `f` is constant! -/
private theorem bsv_periodic_coloring_const {m r k : ℕ} (_hm : 3 ≤ m)
    (hr1 : 1 ≤ r) (hr_half : r ≤ m - r - 1) (hk1 : 1 ≤ k) (hkm : k < m)
    (f : ℕ → Bool)
    (hper_m : ∀ x, f (x + m) = f x)
    (hper_k : ∀ x, f (x + k) = f x)
    (htype1 : ∀ a b, a ≤ r → 1 ≤ b → b ≤ m - r - 1 → a + b = k → f a = f (r + b))
    (htype2 : ∀ a b, a ≤ m - r - 1 → 1 ≤ b → b ≤ r → a + b = k →
      f ((m - a) % m) = f (r + 1 - b))
    (htype3 : ∀ a b, 1 ≤ b → a + b ≤ m - r - 1 → a + b = k →
      f ((m - a) % m) = f (r + b)) :
    ∀ x, f x = f 0 := by
  let d := Nat.gcd k m
  have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left m (by omega)
  have hd_dvd_k : d ∣ k := Nat.gcd_dvd_left k m
  have hd_dvd_m : d ∣ m := Nat.gcd_dvd_right k m
  have hper_d : ∀ x, f (x + d) = f x := by
    have hmul_m : ∀ t x, f (x + t * m) = f x := by
      intro t
      induction t with
      | zero => intro x; simp
      | succ t ih =>
          intro x
          have : x + (t + 1) * m = (x + t * m) + m := by ring
          rw [this, hper_m, ih]
    have hmul_k : ∀ t x, f (x + t * k) = f x := by
      intro t
      induction t with
      | zero => intro x; simp
      | succ t ih =>
          intro x
          have : x + (t + 1) * k = (x + t * k) + k := by ring
          rw [this, hper_k, ih]
    have hbez := Nat.gcd_eq_gcd_ab k m
    set A : ℤ := Nat.gcdA k m
    set B : ℤ := Nat.gcdB k m
    let p1 : ℕ := Int.toNat (max A 0)
    let n1 : ℕ := Int.toNat (max (-A) 0)
    let p2 : ℕ := Int.toNat (max B 0)
    let n2 : ℕ := Int.toNat (max (-B) 0)
    have hEq_nat : d + n1 * k + n2 * m = p1 * k + p2 * m := by
      have hA : (p1 : ℤ) - (n1 : ℤ) = A := by omega
      have hB : (p2 : ℤ) - (n2 : ℤ) = B := by omega
      have hZ : (d : ℤ) + (n1 : ℤ) * (k : ℤ) + (n2 : ℤ) * (m : ℤ) =
                (p1 : ℤ) * (k : ℤ) + (p2 : ℤ) * (m : ℤ) := by
        have : (d : ℤ) = (k : ℤ) * A + (m : ℤ) * B := hbez
        nlinarith
      exact_mod_cast hZ
    intro x
    calc f (x + d) = f (x + d + n1 * k + n2 * m) := by rw [hmul_m, hmul_k]
      _ = f (x + (d + n1 * k + n2 * m)) := by congr 1; omega
      _ = f (x + (p1 * k + p2 * m)) := by rw [hEq_nat]
      _ = f (x + p1 * k + p2 * m) := by congr 1; omega
      _ = f x := by rw [hmul_m, hmul_k]
  have hper_mod : ∀ x y, x % d = y % d → f x = f y := by
    have hstep : ∀ q r0, f (r0 + q * d) = f r0 := by
      intro q
      induction q with
      | zero => intro r0; simp
      | succ q ih =>
          intro r0
          have : r0 + (q + 1) * d = (r0 + q * d) + d := by ring
          rw [this, hper_d, ih]
    intro x y hxy
    have hx : x = x % d + (x / d) * d := by have := Nat.div_add_mod x d; linarith
    have hy : y = y % d + (y / d) * d := by have := Nat.div_add_mod y d; linarith
    conv_lhs => rw [hx, hstep]
    conv_rhs => rw [hy, hstep]
    rw [hxy]
  have htype2_mod : ∀ a b, a ≤ m - r - 1 → 1 ≤ b → b ≤ r → a + b = k →
      f b = f (r + 1 - b) := by
    intro a b ha hb1 hb2 hab
    have h := htype2 a b ha hb1 hb2 hab
    have hmod : ((m - a) % m) % d = b % d := by
      rw [Nat.mod_mod_of_dvd (m - a) hd_dvd_m]
      rcases hd_dvd_m with ⟨qm, hqm⟩
      rcases hd_dvd_k with ⟨qk, hqk⟩
      have hsum : (m - a) + k = b + m := by omega
      have hmod1 : ((m - a) + k) % d = (m - a) % d := by rw [hqk, Nat.add_mul_mod_self_left]
      have hmod2 : (b + m) % d = b % d := by rw [hqm, Nat.add_mul_mod_self_left]
      rw [← hmod1, hsum, hmod2]
    rw [← hper_mod _ _ hmod]
    exact h
  have htype1_mod : ∀ a b, a ≤ r → 1 ≤ b → b ≤ m - r - 1 → a + b = k →
      f a = f (r + k - a) := by
    intro a b ha hb1 hb2 hab
    have h := htype1 a b ha hb1 hb2 hab
    have : r + b = r + k - a := by omega
    rwa [this] at h
  by_cases hd1 : d = 1
  · intro x; exact hper_mod x 0 (by simp [hd1, Nat.mod_one])
  have hd2 : 2 ≤ d := by omega
  have hk_ge_d : d ≤ k := Nat.le_of_dvd (by omega) hd_dvd_k
  have hk_le_md : k ≤ m - d := by
    rcases hd_dvd_m with ⟨qm, hqm⟩
    rcases hd_dvd_k with ⟨qk, hqk⟩
    have : qk < qm := by nlinarith
    have : d * qk + d ≤ d * qm := by nlinarith
    omega
  by_cases hdr : d ≤ r
  · -- Case 1 (`d ≤ r`): Both Type 1 and Type 2 cover a full residue system mod `d`!
    have hstep1 : ∀ y, f y = f (y + 1) := by
      intro y
      let lo1 := k - (m - r - 1)
      let lo2 := max 1 (k - (m - r - 1))
      let target := (r + k + d - y % d) % d
      have htar_lt : target < d := Nat.mod_lt _ hd_pos
      let t1 := (target + d - lo1 % d) % d
      let x0 := lo1 + t1
      have hx0_mod : x0 % d = target := add_sub_mod_cancel hd_pos htar_lt
      have ht1_lt : t1 < d := Nat.mod_lt _ hd_pos
      have hx0_le_r : x0 ≤ r := by dsimp only [x0, lo1]; omega
      have hx0_le_k1 : x0 ≤ k - 1 := by dsimp only [x0, lo1]; omega
      have hT1 : f x0 = f (r + k - x0) :=
        htype1_mod x0 (k - x0) hx0_le_r (by omega) (by dsimp only [x0, lo1]; omega) (by omega)
      let t2 := (target + d - lo2 % d) % d
      let x1 := lo2 + t2
      have hx1_mod : x1 % d = target := add_sub_mod_cancel hd_pos htar_lt
      have ht2_lt : t2 < d := Nat.mod_lt _ hd_pos
      have hx1_le_r : x1 ≤ r := by dsimp only [x1, lo2]; omega
      have hx1_le_k : x1 ≤ k := by dsimp only [x1, lo2]; omega
      have hx1_ge_1 : 1 ≤ x1 := by dsimp only [x1, lo2]; omega
      have hT2 : f x1 = f (r + 1 - x1) :=
        htype2_mod (k - x1) x1 (by dsimp only [x1, lo2]; omega) hx1_ge_1 hx1_le_r (by omega)
      have hfx0_x1 : f x0 = f x1 := hper_mod x0 x1 (by rw [hx0_mod, hx1_mod])
      have hyt : (y + target) % d = (r + k) % d := add_sub_mod_cancel_any hd_pos
      have hy_mod : (r + k - x0) % d = y % d := by
        apply mod_add_cancel_right hd_pos (Nat.mod_lt _ hd_pos) (Nat.mod_lt _ hd_pos) (w := target)
        have hL : ((r + k - x0) % d + target) % d = (r + k) % d := by
          rw [← hx0_mod, ← Nat.add_mod]
          have : r + k - x0 + x0 = r + k := by omega
          rw [this]
        have hR : (y % d + target) % d = (r + k) % d := by
          have h1 : (y % d + target) % d = (y + target) % d := by
            rw [Nat.add_mod, Nat.mod_mod]; conv_rhs => rw [Nat.add_mod]
          rw [h1, hyt]
        rw [hL, hR]
      have hy1_mod : (r + 1 - x1) % d = (y + 1) % d := by
        apply mod_add_cancel_right hd_pos (Nat.mod_lt _ hd_pos) (Nat.mod_lt _ hd_pos) (w := target)
        rcases hd_dvd_k with ⟨qk, hqk⟩
        have hL : ((r + 1 - x1) % d + target) % d = (r + 1) % d := by
          rw [← hx1_mod, ← Nat.add_mod]
          have : r + 1 - x1 + x1 = r + 1 := by omega
          rw [this]
        have hR : ((y + 1) % d + target) % d = (r + 1) % d := by
          have h1 : ((y + 1) % d + target) % d = ((y + target) + 1) % d := by
            have h2 : ((y + 1) % d + target) % d = ((y + 1) + target) % d := by
              rw [Nat.add_mod, Nat.mod_mod]; conv_rhs => rw [Nat.add_mod]
            rw [h2]; congr 1; omega
          rw [h1, Nat.add_mod, hyt, ← Nat.add_mod]
          have : r + k + 1 = (r + 1) + d * qk := by omega
          rw [this, Nat.add_mul_mod_self_left]
        rw [hL, hR]
      calc f y = f (r + k - x0) := hper_mod y (r + k - x0) hy_mod.symm
        _ = f x0 := hT1.symm
        _ = f x1 := hfx0_x1
        _ = f (r + 1 - x1) := hT2
        _ = f (y + 1) := hper_mod (r + 1 - x1) (y + 1) hy1_mod
    intro x
    induction x with
    | zero => rfl
    | succ n ih => rw [← hstep1 n, ih]
  · -- Case 2 (`r < d`): Automatically `k ≤ m - d ≤ m - r - 1`!
    have hlt_rd : r < d := by omega
    have hk_le_mr1 : k ≤ m - r - 1 := by omega
    have hblock : ∀ j, j ≤ r → f j = f 0 := by
      intro j
      induction j with
      | zero => intro _; rfl
      | succ j ih =>
          intro hjr
          have hT2 : f (j + 1) = f (r - j) := by
            have := htype2_mod (k - (j + 1)) (j + 1) (by omega) (by omega) (by omega) (by omega)
            have heq : r + 1 - (j + 1) = r - j := by omega
            rwa [heq] at this
          have hT1 : f (r - j) = f (j + k) := by
            have := htype1_mod (r - j) (k - (r - j)) (by omega) (by omega) (by omega) (by omega)
            have heq : r + k - (r - j) = j + k := by omega
            rwa [heq] at this
          rw [hT2, hT1, hper_k, ih (by omega)]
    have hper_r : ∀ x, f (x + r) = f x := by
      intro x
      let a := (d - x % d) % d
      have ha_lt_d : a < d := Nat.mod_lt _ hd_pos
      have hb_ge1 : 1 ≤ k - a := by omega
      have hT3 := htype3 a (k - a) hb_ge1 (by omega) (by omega)
      have hxa0 : (x + a) % d = 0 := add_neg_mod_eq_zero hd_pos
      have hx_mod : ((m - a) % m) % d = x % d := by
        rw [Nat.mod_mod_of_dvd (m - a) hd_dvd_m]
        apply mod_add_cancel_right hd_pos (Nat.mod_lt _ hd_pos) (Nat.mod_lt _ hd_pos) (w := a)
        rcases hd_dvd_m with ⟨qm, hqm⟩
        have hL : ((m - a) % d + a) % d = 0 := by
          have h1 : ((m - a) % d + a) % d = (m - a + a) % d := by
            rw [Nat.add_mod, Nat.mod_mod]; conv_rhs => rw [Nat.add_mod]
          rw [h1]
          have : m - a + a = d * qm := by omega
          rw [this, Nat.mul_mod_right]
        have hR : (x % d + a) % d = 0 := by
          have h1 : (x % d + a) % d = (x + a) % d := by
            rw [Nat.add_mod, Nat.mod_mod]; conv_rhs => rw [Nat.add_mod]
          rw [h1]; exact hxa0
        rw [hL, hR]
      have hxr_mod : (r + (k - a)) % d = (x + r) % d := by
        apply mod_add_cancel_right hd_pos (Nat.mod_lt _ hd_pos) (Nat.mod_lt _ hd_pos) (w := a)
        rcases hd_dvd_k with ⟨qk, hqk⟩
        have hL : ((r + (k - a)) % d + a) % d = r % d := by
          have h1 : ((r + (k - a)) % d + a) % d = (r + (k - a) + a) % d := by
            rw [Nat.add_mod, Nat.mod_mod]; conv_rhs => rw [Nat.add_mod]
          rw [h1]
          have : r + (k - a) + a = r + d * qk := by omega
          rw [this, Nat.add_mul_mod_self_left]
        have hR : ((x + r) % d + a) % d = r % d := by
          have h1 : ((x + r) % d + a) % d = ((x + a) + r) % d := by
            have h2 : ((x + r) % d + a) % d = (x + r + a) % d := by
              rw [Nat.add_mod, Nat.mod_mod]; conv_rhs => rw [Nat.add_mod]
            rw [h2]; congr 1; omega
          rw [h1, Nat.add_mod, hxa0, Nat.zero_add, Nat.mod_mod]
        rw [hL, hR]
      calc f (x + r) = f (r + (k - a)) := hper_mod _ _ hxr_mod.symm
        _ = f ((m - a) % m) := hT3.symm
        _ = f x := hper_mod _ _ hx_mod
    intro x
    have hmul_r : ∀ q y, f (y + q * r) = f y := by
      intro q
      induction q with
      | zero => intro y; simp
      | succ q ih =>
          intro y
          have : y + (q + 1) * r = (y + q * r) + r := by ring
          rw [this, hper_r, ih]
    have hx : x = x % r + (x / r) * r := by have := Nat.div_add_mod x r; linarith
    rw [hx, hmul_r]
    exact hblock (x % r) (Nat.le_of_lt (Nat.mod_lt x (by omega)))

end ChordedEvenCycle

/-- **Pillar 1A — Bondy–Simonovits–Verstraëte (1974 / 2000) Chorded-Cycle Path-Spectrum Theorem**:
For ANY bipartite even cycle `C_{2m}` (`m ≥ 3`) with ANY bipartite chord `v_0 — v_{2r+1}`
(`1 ≤ r ≤ m - 2`), ANY nontrivial 2-coloring `col : Fin m → Bool` of the even-index vertices
`V_0 = {v_0, v_2, ..., v_{2m-2}}`, and ANY `1 ≤ k ≤ m - 1`, there exist `i, j : Fin m` with
`col i ≠ col j` and a **simple path** (`Walk.IsPath`) in `G` of exact length `2k` from `v_{2i}`
to `v_{2j}` whose vertices all lie in `Set.range C.v`. -/
theorem bsv_chorded_cycle_all_even_ab_paths {G : SimpleGraph V} {m r : ℕ}
    (C : ChordedEvenCycle G m r) (col : Fin m → Bool)
    (hnontriv : ∃ i0 i1 : Fin m, col i0 ≠ col i1)
    {k : ℕ} (hk1 : 1 ≤ k) (hkm : k ≤ m - 1) :
    ∃ (i j : Fin m)
      (p : G.Walk (C.v ⟨2 * i.val, by omega⟩) (C.v ⟨2 * j.val, by omega⟩)),
      col i ≠ col j ∧ p.IsPath ∧ p.length = 2 * k ∧ ∀ x ∈ p.support, x ∈ Set.range C.v := by
  have hmain : ∀ {r' : ℕ} (C' : ChordedEvenCycle G m r') (col' : Fin m → Bool),
      (∃ i0 i1 : Fin m, col' i0 ≠ col' i1) →
      r' ≤ m - r' - 1 →
      ∃ (i j : Fin m)
        (p : G.Walk (C'.v ⟨2 * i.val, by omega⟩) (C'.v ⟨2 * j.val, by omega⟩)),
        col' i ≠ col' j ∧ p.IsPath ∧ p.length = 2 * k ∧ ∀ x ∈ p.support, x ∈ Set.range C'.v := by
    intro r' C' col' hnt hr_half
    by_contra hnone
    have hno : ∀ (i j : Fin m)
        (p : G.Walk (C'.v ⟨2 * i.val, by omega⟩) (C'.v ⟨2 * j.val, by omega⟩)),
        col' i ≠ col' j → p.IsPath → p.length = 2 * k →
        (∀ x ∈ p.support, x ∈ Set.range C'.v) → False :=
      fun i j p h1 h2 h3 h4 => hnone ⟨i, j, p, h1, h2, h3, h4⟩
    have hm := C'.hm
    let f : ℕ → Bool := fun x => col' ⟨x % m, Nat.mod_lt _ (by omega)⟩
    have hper_m : ∀ x, f (x + m) = f x := by
      intro x; simp [f, Nat.add_mod_right]
    have hper_k : ∀ x, f (x + k) = f x := by
      intro x
      let i : Fin m := ⟨x % m, Nat.mod_lt _ (by omega)⟩
      let j : Fin m := ⟨(x + k) % m, Nat.mod_lt _ (by omega)⟩
      have hstart : (2 * i.val) % (2 * m) = 2 * i.val := Nat.mod_eq_of_lt (by omega)
      have hend : (2 * i.val + 2 * k) % (2 * m) = 2 * j.val := by
        dsimp only [i, j]
        have h1 : 2 * (x % m) + 2 * k = 2 * (x % m + k) := by ring
        rw [h1, Nat.mul_mod_mul_left]
        congr 1
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      let p0 := C'.fwdWalk (2 * i.val) (2 * k)
      let p : G.Walk (C'.v ⟨2 * i.val, by omega⟩) (C'.v ⟨2 * j.val, by omega⟩) :=
        p0.copy (by simp [hstart]) (by simp [hend])
      have hp_path : p.IsPath := by simpa [p] using C'.fwdWalk_isPath (2 * i.val) (2 * k) (by omega)
      have hp_len : p.length = 2 * k := by simp [p, p0, ChordedEvenCycle.fwdWalk_length]
      have hp_mem : ∀ z ∈ p.support, z ∈ Set.range C'.v := by
        intro z hz; rw [Walk.support_copy] at hz
        exact C'.fwdWalk_mem_range (2 * i.val) (2 * k) z hz
      by_contra hne
      exact hno i j p (fun h => hne h.symm) hp_path hp_len hp_mem
    have htype1 : ∀ a b, a ≤ r' → 1 ≤ b → b ≤ m - r' - 1 → a + b = k → f a = f (r' + b) := by
      intro a b ha hb1 hb2 hab
      obtain ⟨p, hp, hlen, hmem⟩ := C'.exists_chord_path_type1 ha hb1 hb2
      let i : Fin m := ⟨a, by have := C'.hr_hi; omega⟩
      let j : Fin m := ⟨r' + b, by omega⟩
      have hi_fin : (⟨a % m, Nat.mod_lt _ (by omega)⟩ : Fin m) = i :=
        Fin.ext (Nat.mod_eq_of_lt (by have := C'.hr_hi; omega))
      have hj_fin : (⟨(r' + b) % m, Nat.mod_lt _ (by omega)⟩ : Fin m) = j :=
        Fin.ext (Nat.mod_eq_of_lt (by omega))
      by_contra hne
      have hcol_ne : col' i ≠ col' j := by
        intro h; apply hne; dsimp only [f]; rw [hi_fin, hj_fin]; exact h
      exact hno i j p hcol_ne hp (by omega) hmem
    have htype2 : ∀ a b, a ≤ m - r' - 1 → 1 ≤ b → b ≤ r' → a + b = k →
        f ((m - a) % m) = f (r' + 1 - b) := by
      intro a b ha hb1 hb2 hab
      obtain ⟨p, hp, hlen, hmem⟩ := C'.exists_chord_path_type2 ha hb1 hb2
      let i : Fin m := ⟨(m - a) % m, Nat.mod_lt _ (by omega)⟩
      let j : Fin m := ⟨r' + 1 - b, by have := C'.hr_hi; omega⟩
      have hi_fin : (⟨((m - a) % m) % m, Nat.mod_lt _ (by omega)⟩ : Fin m) = i :=
        Fin.ext (Nat.mod_mod _ _)
      have hj_fin : (⟨(r' + 1 - b) % m, Nat.mod_lt _ (by omega)⟩ : Fin m) = j :=
        Fin.ext (Nat.mod_eq_of_lt (by have := C'.hr_hi; omega))
      by_contra hne
      have hcol_ne : col' i ≠ col' j := by
        intro h; apply hne; dsimp only [f]; rw [hi_fin, hj_fin]; exact h
      exact hno i j p hcol_ne hp (by omega) hmem
    have htype3 : ∀ a b, 1 ≤ b → a + b ≤ m - r' - 1 → a + b = k →
        f ((m - a) % m) = f (r' + b) := by
      intro a b hb1 hab_le hab
      obtain ⟨p, hp, hlen, hmem⟩ := C'.exists_chord_path_type3 hb1 hab_le
      let i : Fin m := ⟨(m - a) % m, Nat.mod_lt _ (by omega)⟩
      let j : Fin m := ⟨r' + b, by omega⟩
      have hi_fin : (⟨((m - a) % m) % m, Nat.mod_lt _ (by omega)⟩ : Fin m) = i :=
        Fin.ext (Nat.mod_mod _ _)
      have hj_fin : (⟨(r' + b) % m, Nat.mod_lt _ (by omega)⟩ : Fin m) = j :=
        Fin.ext (Nat.mod_eq_of_lt (by omega))
      by_contra hne
      have hcol_ne : col' i ≠ col' j := by
        intro h; apply hne; dsimp only [f]; rw [hi_fin, hj_fin]; exact h
      exact hno i j p hcol_ne hp (by omega) hmem
    have hconst := ChordedEvenCycle.bsv_periodic_coloring_const hm C'.hr_lo hr_half hk1
      (by omega) f hper_m hper_k htype1 htype2 htype3
    rcases hnt with ⟨i0, i1, hne⟩
    have h0 : col' i0 = f 0 := by
      have h := hconst i0.val
      have hfin : (⟨i0.val % m, Nat.mod_lt _ (by omega)⟩ : Fin m) = i0 :=
        Fin.ext (Nat.mod_eq_of_lt i0.isLt)
      dsimp only [f] at h
      rwa [hfin] at h
    have h1 : col' i1 = f 0 := by
      have h := hconst i1.val
      have hfin : (⟨i1.val % m, Nat.mod_lt _ (by omega)⟩ : Fin m) = i1 :=
        Fin.ext (Nat.mod_eq_of_lt i1.isLt)
      dsimp only [f] at h
      rwa [hfin] at h
    exact hne (h0.trans h1.symm)
  by_cases hr_half : r ≤ m - r - 1
  · exact hmain C col hnontriv hr_half
  · have hm := C.hm; have hr1 := C.hr_lo; have hrh := C.hr_hi
    let C' := C.reflect
    let refIdx : Fin m → Fin m := fun i => ⟨(m - i.val) % m, Nat.mod_lt _ (by omega)⟩
    let col' : Fin m → Bool := fun i => col (refIdx i)
    have href_invol : ∀ i : Fin m, refIdx (refIdx i) = i := by
      intro i; apply Fin.ext; dsimp only [refIdx]
      have hi := i.isLt
      by_cases hi0 : i.val = 0
      · simp [hi0]
      · have h1 : (m - i.val) % m = m - i.val := Nat.mod_eq_of_lt (by omega)
        rw [h1]
        have h2 : (m - (m - i.val)) % m = m - (m - i.val) := Nat.mod_eq_of_lt (by omega)
        rw [h2]; omega
    have hnt' : ∃ i0 i1 : Fin m, col' i0 ≠ col' i1 := by
      rcases hnontriv with ⟨i0, i1, hne⟩
      refine ⟨refIdx i0, refIdx i1, ?_⟩
      simpa only [col', href_invol] using hne
    have hr_half' : m - 1 - r ≤ m - (m - 1 - r) - 1 := by omega
    obtain ⟨i', j', p', hcol_ne', hp', hlen', hmem'⟩ := hmain C' col' hnt' hr_half'
    have hv_eq : ∀ u : Fin m, C'.v ⟨2 * u.val, by omega⟩ = C.v ⟨2 * (refIdx u).val, by omega⟩ := by
      intro u; dsimp only [C', ChordedEvenCycle.reflect, refIdx]
      have hu := u.isLt
      congr 1; apply Fin.ext; dsimp only
      by_cases hu0 : u.val = 0
      · simp [hu0]
      · have h1 : (2 * m - 2 * u.val) % (2 * m) = 2 * m - 2 * u.val := Nat.mod_eq_of_lt (by omega)
        have h2 : (m - u.val) % m = m - u.val := Nat.mod_eq_of_lt (by omega)
        rw [h1, h2]; omega
    have hrange_eq : ∀ z, z ∈ Set.range C'.v → z ∈ Set.range C.v := by
      rintro z ⟨idx, rfl⟩; exact ⟨_, rfl⟩
    let p : G.Walk (C.v ⟨2 * (refIdx i').val, by omega⟩) (C.v ⟨2 * (refIdx j').val, by omega⟩) :=
      p'.copy (hv_eq i') (hv_eq j')
    refine ⟨refIdx i', refIdx j', p, hcol_ne', by simpa [p] using hp',
      by simpa [p] using hlen', ?_⟩
    intro z hz; rw [Walk.support_copy] at hz
    exact hrange_eq z (hmem' z hz)

/-- **Pillar 1B — BFS-LCA Even-Cycle Interval Lifting Theorem**:
If `C : ChordedEvenCycle G m r` has its even-index vertices `V_0` nontrivially partitioned by
BFS-tree branches below a lowest common ancestor of height `h ≥ 1` (so every bichromatic pair
`(i, j)` is joined by a simple tree path of exact length `2h` internally disjoint from `C`),
then `G` contains a **simple cycle (`Walk.IsCycle`) of EVERY even length `2 * t` for
`t ∈ [h + 1, h + m - 1]`**. -/
theorem bfs_lca_even_cycle_interval {G : SimpleGraph V} {m r h : ℕ}
    (C : ChordedEvenCycle G m r) (hh : 1 ≤ h) (col : Fin m → Bool)
    (hnontriv : ∃ i0 i1 : Fin m, col i0 ≠ col i1)
    (htree : ∀ i j : Fin m, col i ≠ col j →
      ∃ q : G.Walk (C.v ⟨2 * i.val, by omega⟩) (C.v ⟨2 * j.val, by omega⟩),
        q.IsPath ∧ q.length = 2 * h ∧
        ∀ x ∈ q.support, x ∈ Set.range C.v →
          x = C.v ⟨2 * i.val, by omega⟩ ∨ x = C.v ⟨2 * j.val, by omega⟩) :
    ∀ t : ℕ, h + 1 ≤ t → t ≤ h + m - 1 →
      ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ c.length = 2 * t := by
  intro t hlo hhi
  have hm := C.hm
  let k := t - h
  have hk1 : 1 ≤ k := by omega
  have hkm : k ≤ m - 1 := by omega
  obtain ⟨i, j, p, hcol_ne, hp, hp_len, hp_mem⟩ :=
    bsv_chorded_cycle_all_even_ab_paths C col hnontriv hk1 hkm
  obtain ⟨q, hq, hq_len, hq_disj⟩ := htree i j hcol_ne
  refine ⟨C.v ⟨2 * i.val, by omega⟩, p.append q.reverse, ?_, ?_⟩
  · apply isCycle_append_reverse_of_internally_disjoint p q hp hq (by omega)
    intro x hxp hxq
    exact hq_disj x hxq (hp_mem x hxp)
  · rw [Walk.length_append, Walk.length_reverse, hp_len, hq_len]; omega

/-- **Pillar 1C — Unconditional Unbounded-`n` Power-of-2 Closure via BFS Chorded Cycles**:
Whenever `h + 1 ≤ m` (equivalently `2m ≥ 2h + 2`), the BFS-lifted even-cycle interval
`[2h + 2, 2h + 2m - 2]` crosses a power of 2, forcing `HasPower G` unconditionally. -/
theorem hasPower_of_bfs_chorded_cycle {G : SimpleGraph V} {m r h : ℕ}
    (C : ChordedEvenCycle G m r) (hh : 1 ≤ h) (hscale : h + 1 ≤ m)
    (col : Fin m → Bool) (hnontriv : ∃ i0 i1 : Fin m, col i0 ≠ col i1)
    (htree : ∀ i j : Fin m, col i ≠ col j →
      ∃ q : G.Walk (C.v ⟨2 * i.val, by omega⟩) (C.v ⟨2 * j.val, by omega⟩),
        q.IsPath ∧ q.length = 2 * h ∧
        ∀ x ∈ q.support, x ∈ Set.range C.v →
          x = C.v ⟨2 * i.val, by omega⟩ ∨ x = C.v ⟨2 * j.val, by omega⟩) :
    HasPower G := by
  have hcyc := bfs_lca_even_cycle_interval C hh col hnontriv htree
  exact hasPower_of_consecutive_even_cycles G (a := h + 1) (b := h + m - 1)
    (by omega) (by omega) hcyc

/-- **Pillar 1D (Part 1) — Cubic 2-Layer BFS-Shell Degree Bound**:
In any cubic graph (`∀ v, G.degree v = 3`) with a BFS layering `L : V → ℕ` (every vertex at
depth `i ≥ 1` has a neighbor at depth `i - 1`), every vertex `u` in layer `L_i` has at most `2`
neighbors in the two-layer shell `L_i ∪ L_{i+1}`. -/
theorem cubic_two_layer_deg_le_two [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcubic : ∀ v : V, G.degree v = 3)
    (L : V → ℕ) {i : ℕ} (hi : 1 ≤ i) {u : V} (hu : L u = i)
    (hparent : ∃ w : V, G.Adj u w ∧ L w = i - 1) :
    ((G.neighborFinset u).filter (fun x => L x = i ∨ L x = i + 1)).card ≤ 2 := by
  obtain ⟨w, huw, hLw⟩ := hparent
  have hw_mem : w ∈ G.neighborFinset u := (G.mem_neighborFinset u w).mpr huw
  have hw_not : w ∉ (G.neighborFinset u).filter (fun x => L x = i ∨ L x = i + 1) := by
    simp only [Finset.mem_filter]; omega
  have hsub : (G.neighborFinset u).filter (fun x => L x = i ∨ L x = i + 1) ⊆
      (G.neighborFinset u).erase w := by
    intro x hx
    rw [Finset.mem_erase]
    refine ⟨?_, (Finset.mem_filter.mp hx).1⟩
    intro hxw; subst hxw; exact hw_not hx
  have hcard_le := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hw_mem, SimpleGraph.card_neighborFinset_eq_degree, hcubic u] at hcard_le
  omega

/-- **Pillar 1D (Part 2) — Cubic 2-Layer BFS-Shell No-Go Theorem**:
No two-layer BFS shell `L_i ∪ L_{i+1}` (`i ≥ 1`) of a cubic graph can contain a bipartite
chorded cycle `C : ChordedEvenCycle G m r` with `v_0 ∈ L_i` (because `v_0` has 3 distinct
neighbors `v_1, v_{2m-1}, v_{2r+1}` in the shell, contradicting `cubic_two_layer_deg_le_two`). -/
theorem cubic_two_layer_no_chorded_cycle [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcubic : ∀ v : V, G.degree v = 3)
    (L : V → ℕ) {i : ℕ} (hi : 1 ≤ i)
    (hparent : ∀ u : V, L u = i → ∃ w : V, G.Adj u w ∧ L w = i - 1)
    {m r : ℕ} (C : ChordedEvenCycle G m r)
    (hLv0 : L (C.v ⟨0, by have := C.hm; omega⟩) = i)
    (hshell : ∀ idx : Fin (2 * m), L (C.v idx) = i ∨ L (C.v idx) = i + 1) :
    False := by
  have hm := C.hm; have hr1 := C.hr_lo; have hrh := C.hr_hi
  let u0 := C.v ⟨0, by omega⟩
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
  have h12 : x1 ≠ x2 := fun h => by
    have := congrArg Fin.val (C.hv_inj h); dsimp only at this; omega
  have h13 : x1 ≠ x3 := fun h => by
    have := congrArg Fin.val (C.hv_inj h); dsimp only at this; omega
  have h23 : x2 ≠ x3 := fun h => by
    have := congrArg Fin.val (C.hv_inj h); dsimp only at this; omega
  let S := (G.neighborFinset u0).filter (fun x => L x = i ∨ L x = i + 1)
  have hsub : ({x1, x2, x3} : Finset V) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr h1, hshell ⟨1, by omega⟩⟩
    · exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr h2, hshell ⟨2 * r + 1, by omega⟩⟩
    · exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr h3, hshell ⟨2 * m - 1, by omega⟩⟩
  have hcard3 : ({x1, x2, x3} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [h23]
    · simp [h12, h13]
  have hle2 := cubic_two_layer_deg_le_two G hcubic L hi hLv0 (hparent u0 hLv0)
  have h3le2 : 3 ≤ 2 := by
    calc 3 = ({x1, x2, x3} : Finset V).card := hcard3.symm
      _ ≤ S.card := Finset.card_le_card hsub
      _ ≤ 2 := hle2
  omega

end BondySimonovitsVerstraete

/-! ## Section 3 (Pillar 2): Gao–Li–Ma–Xie (2024) Quasi-Diagonal Even+Odd Cycle Gluing -/

section GaoLiMaXie

variable {V : Type*}

private theorem concat3_isPath {G : SimpleGraph V} {u1 v1 v2 u2 : V}
    (p1 : G.Walk u1 v1) (d : G.Walk v1 v2) (p2 : G.Walk u2 v2)
    (hp1 : p1.IsPath) (hd : d.IsPath) (hp2 : p2.IsPath)
    (hp1_p2 : ∀ x ∈ p1.support, x ∉ p2.support)
    (hp1_d : ∀ x ∈ p1.support, x ∈ d.support → x = v1)
    (hp2_d : ∀ x ∈ p2.support, x ∈ d.support → x = v2) :
    ((p1.append d).append p2.reverse).IsPath := by
  have h1 : (p1.append d).IsPath := by
    rw [Walk.isPath_def, Walk.support_append, List.nodup_append]
    refine ⟨hp1.support_nodup, support_tail_nodup_of_isPath d hd, ?_⟩
    intro x hxp y hyd hxy; subst hxy
    have := hp1_d x hxp (List.mem_of_mem_tail hyd)
    subst this; exact start_notMem_support_tail_of_isPath d hd hyd
  have hp2r := hp2.reverse
  rw [Walk.isPath_def, Walk.support_append, List.nodup_append]
  refine ⟨h1.support_nodup, support_tail_nodup_of_isPath p2.reverse hp2r, ?_⟩
  intro x hx1 y hy2 hxy; subst hxy
  have hxp2 : x ∈ p2.support := by
    have := List.mem_of_mem_tail hy2
    rwa [Walk.support_reverse, List.mem_reverse] at this
  rw [Walk.support_append, List.mem_append] at hx1
  rcases hx1 with hxp1 | hxd
  · exact hp1_p2 x hxp1 hxp2
  · have := hp2_d x hxp2 (List.mem_of_mem_tail hxd)
    subst this; exact start_notMem_support_tail_of_isPath p2.reverse hp2r hy2

private theorem length_pos_of_ne_endpoints {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (hne : a ≠ b) : 1 ≤ p.length := by
  cases p with
  | nil => exact absurd rfl hne
  | cons _ _ => simp

/-- **Pillar 2 — Gao–Li–Ma–Xie (2024) Lemma 8 (Quasi-Diagonal Even+Odd Cycle Gluing)**:
Given an even cycle split at quasi-diagonal vertices `u1, u2` into two internally disjoint
simple paths `b1, b2` (`b2.length = b1.length + 2`, `1 ≤ b1.length`), a vertex-disjoint odd
cycle split at `v1, v2` into two internally disjoint simple paths `d1, d2` (`Odd (d1.length + d2.length)`),
and two vertex-disjoint connecting paths `p1 : u1 ⇝ v1`, `p2 : u2 ⇝ v2` internally disjoint from
both cycles, `G` **unconditionally contains TWO SIMPLE CYCLES of consecutive even lengths
`2 * t` and `2 * t + 2`** (`t ≥ 2`). -/
theorem quasi_diagonal_even_odd_consecutive_even_cycles {G : SimpleGraph V}
    {u1 u2 v1 v2 : V}
    (b1 b2 : G.Walk u1 u2) (hb1 : b1.IsPath) (hb2 : b2.IsPath)
    (hb1_pos : 1 ≤ b1.length) (hb_quasi : b2.length = b1.length + 2)
    (d1 d2 : G.Walk v1 v2) (hd1 : d1.IsPath) (hd2 : d2.IsPath)
    (hd1_pos : 1 ≤ d1.length) (hd2_pos : 1 ≤ d2.length)
    (hodd : Odd (d1.length + d2.length))
    (p1 : G.Walk u1 v1) (p2 : G.Walk u2 v2) (hp1 : p1.IsPath) (hp2 : p2.IsPath)
    (hp1_p2 : ∀ x ∈ p1.support, x ∉ p2.support)
    (hp1_d1 : ∀ x ∈ p1.support, x ∈ d1.support → x = v1)
    (hp1_d2 : ∀ x ∈ p1.support, x ∈ d2.support → x = v1)
    (hp2_d1 : ∀ x ∈ p2.support, x ∈ d1.support → x = v2)
    (hp2_d2 : ∀ x ∈ p2.support, x ∈ d2.support → x = v2)
    (hB_D1 : ∀ x, (x ∈ b1.support ∨ x ∈ b2.support) → x ∉ d1.support)
    (hB_D2 : ∀ x, (x ∈ b1.support ∨ x ∈ b2.support) → x ∉ d2.support)
    (hB_p1 : ∀ x, (x ∈ b1.support ∨ x ∈ b2.support) → x ∈ p1.support → x = u1)
    (hB_p2 : ∀ x, (x ∈ b1.support ∨ x ∈ b2.support) → x ∈ p2.support → x = u2) :
    ∃ t : ℕ, 2 ≤ t ∧
      (∃ c1 : G.Walk u1 u1, c1.IsCycle ∧ c1.length = 2 * t) ∧
      (∃ c2 : G.Walk u1 u1, c2.IsCycle ∧ c2.length = 2 * t + 2) := by
  have hp1_pos : 1 ≤ p1.length := length_pos_of_ne_endpoints p1 (fun h => by
    subst h; exact hB_D1 u1 (Or.inl (Walk.start_mem_support b1)) (Walk.start_mem_support d1))
  have hp2_pos : 1 ≤ p2.length := length_pos_of_ne_endpoints p2 (fun h => by
    subst h; exact hB_D1 u2 (Or.inl (Walk.end_mem_support b1)) (Walk.end_mem_support d1))
  let Q1 := (p1.append d1).append p2.reverse
  let Q2 := (p1.append d2).append p2.reverse
  have hQ1_path : Q1.IsPath :=
    concat3_isPath p1 d1 p2 hp1 hd1 hp2 hp1_p2 hp1_d1 hp2_d1
  have hQ2_path : Q2.IsPath :=
    concat3_isPath p1 d2 p2 hp1 hd2 hp2 hp1_p2 hp1_d2 hp2_d2
  have hQ1_len : Q1.length = p1.length + d1.length + p2.length := by
    simp [Q1, Walk.length_append, Walk.length_reverse]
  have hQ2_len : Q2.length = p1.length + d2.length + p2.length := by
    simp [Q2, Walk.length_append, Walk.length_reverse]
  have hQ1_disj : ∀ (b : G.Walk u1 u2), (∀ x ∈ b.support, x ∈ b1.support ∨ x ∈ b2.support) →
      ∀ x ∈ b.support, x ∈ Q1.support → x = u1 ∨ x = u2 := by
    intro b hb x hxb hxQ
    have hxB := hb x hxb
    simp only [Q1, Walk.support_append, List.mem_append] at hxQ
    rcases hxQ with (hxp1 | hxd1) | hxp2r
    · exact Or.inl (hB_p1 x hxB hxp1)
    · exact absurd (List.mem_of_mem_tail hxd1) (hB_D1 x hxB)
    · have hxp2 : x ∈ p2.support := by
        have := List.mem_of_mem_tail hxp2r
        rwa [Walk.support_reverse, List.mem_reverse] at this
      exact Or.inr (hB_p2 x hxB hxp2)
  have hQ2_disj : ∀ (b : G.Walk u1 u2), (∀ x ∈ b.support, x ∈ b1.support ∨ x ∈ b2.support) →
      ∀ x ∈ b.support, x ∈ Q2.support → x = u1 ∨ x = u2 := by
    intro b hb x hxb hxQ
    have hxB := hb x hxb
    simp only [Q2, Walk.support_append, List.mem_append] at hxQ
    rcases hxQ with (hxp1 | hxd2) | hxp2r
    · exact Or.inl (hB_p1 x hxB hxp1)
    · exact absurd (List.mem_of_mem_tail hxd2) (hB_D2 x hxB)
    · have hxp2 : x ∈ p2.support := by
        have := List.mem_of_mem_tail hxp2r
        rwa [Walk.support_reverse, List.mem_reverse] at this
      exact Or.inr (hB_p2 x hxB hxp2)
  rcases hodd with ⟨s, hs⟩
  by_cases hev : Even (b1.length + Q1.length)
  · rcases hev with ⟨t, ht⟩
    have ht2 : 2 ≤ t := by omega
    refine ⟨t, ht2, ?_, ?_⟩
    · refine ⟨b1.append Q1.reverse,
        isCycle_append_reverse_of_internally_disjoint b1 Q1 hb1 hQ1_path (by omega)
          (hQ1_disj b1 (fun _ hx => Or.inl hx)), ?_⟩
      rw [Walk.length_append, Walk.length_reverse]; omega
    · refine ⟨b2.append Q1.reverse,
        isCycle_append_reverse_of_internally_disjoint b2 Q1 hb2 hQ1_path (by omega)
          (hQ1_disj b2 (fun _ hx => Or.inr hx)), ?_⟩
      rw [Walk.length_append, Walk.length_reverse]; omega
  · have hev2 : Even (b1.length + Q2.length) := by
      rw [Nat.even_iff] at hev ⊢
      omega
    rcases hev2 with ⟨t, ht⟩
    have ht2 : 2 ≤ t := by omega
    refine ⟨t, ht2, ?_, ?_⟩
    · refine ⟨b1.append Q2.reverse,
        isCycle_append_reverse_of_internally_disjoint b1 Q2 hb1 hQ2_path (by omega)
          (hQ2_disj b1 (fun _ hx => Or.inl hx)), ?_⟩
      rw [Walk.length_append, Walk.length_reverse]; omega
    · refine ⟨b2.append Q2.reverse,
        isCycle_append_reverse_of_internally_disjoint b2 Q2 hb2 hQ2_path (by omega)
          (hQ2_disj b2 (fun _ hx => Or.inr hx)), ?_⟩
      rw [Walk.length_append, Walk.length_reverse]; omega

/-- Corollary: if two consecutive even cycles `{2t, 2t + 2}` contain a power of 2 `2 ^ k`
(`k ≥ 2`, e.g., `{6, 8}`, `{14, 16}`, `{30, 32}`), then `HasPower G`. -/
theorem hasPower_of_quasi_diagonal_even_odd_hit {G : SimpleGraph V} {u : V} {t k : ℕ}
    (hk : 2 ≤ k)
    (hc1 : ∃ c1 : G.Walk u u, c1.IsCycle ∧ c1.length = 2 * t)
    (hc2 : ∃ c2 : G.Walk u u, c2.IsCycle ∧ c2.length = 2 * t + 2)
    (hhit : 2 * t = 2 ^ k ∨ 2 * t + 2 = 2 ^ k) :
    HasPower G := by
  rcases hhit with h1 | h2
  · obtain ⟨c1, hcyc, hlen⟩ := hc1
    exact ⟨k, u, c1, hk, hcyc, hlen.trans h1⟩
  · obtain ⟨c2, hcyc, hlen⟩ := hc2
    exact ⟨k, u, c2, hk, hcyc, hlen.trans h2⟩

end GaoLiMaXie

/-! ## Section 4 (Pillar 3): Arbitrary-Girth Quasi-Diagonal `AdjusterChain` (Liu–Montgomery) -/

section AdjusterChains

variable {V : Type*}

/-- Internal vertices of a walk `p : G.Walk a b` (all vertices except start `a` and end `b`). -/
def walkInternals {G : SimpleGraph V} {a b : V} (p : G.Walk a b) : List V :=
  p.support.tail.dropLast

private theorem support_tail_eq_internals_append_end {G : SimpleGraph V} :
    ∀ {a b : V} (p : G.Walk a b), 1 ≤ p.length →
      p.support.tail = walkInternals p ++ [b]
  | _, _, .nil, h => by simp at h
  | _, _, .cons _ .nil, _ => by simp [walkInternals]
  | _, b, .cons h1 (.cons h2 rest), _ => by
      have ih := support_tail_eq_internals_append_end (.cons h2 rest) (by simp)
      simp only [walkInternals, Walk.support_cons, List.tail_cons] at ih ⊢
      rw [List.dropLast_cons_of_ne_nil (Walk.support_ne_nil rest), List.cons_append, ← ih]

private theorem mem_internals_of_mem_edges_ge2 {G : SimpleGraph V} :
    ∀ {a b : V} (p : G.Walk a b), 2 ≤ p.length →
      ∀ e ∈ p.edges, ∃ z ∈ walkInternals p, z ∈ e
  | _, _, .nil, h, _, _ => by simp at h
  | _, _, .cons _ .nil, h, _, _ => by simp at h
  | _, _, .cons (v := u) h1 (.cons (v := w) h2 rest), _, e, he => by
      simp only [Walk.edges_cons, List.mem_cons] at he
      have hu_int : u ∈ walkInternals (Walk.cons h1 (Walk.cons h2 rest)) := by
        simp only [walkInternals, Walk.support_cons, List.tail_cons,
          List.dropLast_cons_of_ne_nil (Walk.support_ne_nil rest), List.mem_cons, true_or]
      rcases he with rfl | rfl | hrest
      · exact ⟨u, hu_int, by simp⟩
      · exact ⟨u, hu_int, by simp⟩
      · cases rest with
        | nil => simp at hrest
        | cons h3 rest2 =>
            obtain ⟨z, hz, hze⟩ :=
              mem_internals_of_mem_edges_ge2 (Walk.cons h2 (Walk.cons h3 rest2)) (by simp) e
                (List.mem_cons_of_mem _ hrest)
            refine ⟨z, ?_, hze⟩
            simp only [walkInternals, Walk.support_cons, List.tail_cons] at hz ⊢
            rw [List.dropLast_cons_of_ne_nil (by simp)]
            exact List.mem_cons_of_mem u hz

/-- An arbitrary-girth Liu–Montgomery / quasi-diagonal adjuster chain of uniform step `δ ≥ 1`:
at each `step`, the chain may traverse either the short path `p0 : G.Walk u w` or the long
path `p1 : G.Walk u w` with `p1.length = p0.length + δ` and `1 ≤ p0.length`.
- `δ = 1`: odd-cycle quasi-diagonal adjusters at ANY odd girth `g = 2s + 1 ≥ 3` (`s` vs `s + 1`).
- `δ = 2`: even-cycle quasi-diagonal adjusters at ANY even girth `g = 2s ≥ 6` (`s - 1` vs `s + 1`). -/
inductive AdjusterChain (G : SimpleGraph V) (δ : ℕ) : V → V → Type _
  | base {a b : V} (p : G.Walk a b) : AdjusterChain G δ a b
  | step {a u w b : V} (seg : G.Walk a u)
      (p0 p1 : G.Walk u w) (hp0_pos : 1 ≤ p0.length)
      (hp1_path : p1.IsPath) (hstep : p1.length = p0.length + δ)
      (rest : AdjusterChain G δ w b) : AdjusterChain G δ a b

namespace AdjusterChain

def numAdjusters {G : SimpleGraph V} {δ : ℕ} : ∀ {a b : V}, AdjusterChain G δ a b → ℕ
  | _, _, .base _ => 0
  | _, _, .step _ _ _ _ _ _ rest => rest.numAdjusters + 1

def altVertices {G : SimpleGraph V} {δ : ℕ} : ∀ {a b : V}, AdjusterChain G δ a b → List V
  | _, _, .base _ => []
  | _, _, .step _ _ p1 _ _ _ rest => walkInternals p1 ++ rest.altVertices

def baseWalk {G : SimpleGraph V} {δ : ℕ} : ∀ {a b : V}, AdjusterChain G δ a b → G.Walk a b
  | _, _, .base p => p
  | _, _, .step seg p0 _ _ _ _ rest => seg.append (p0.append rest.baseWalk)

def realize {G : SimpleGraph V} {δ : ℕ} :
    ∀ {a b : V}, AdjusterChain G δ a b → List Bool → G.Walk a b
  | _, _, .base p, _ => p
  | _, _, .step seg p0 _ _ _ _ rest, [] => seg.append (p0.append rest.baseWalk)
  | _, _, .step seg p0 _ _ _ _ rest, false :: bs => seg.append (p0.append (rest.realize bs))
  | _, _, .step seg _ p1 _ _ _ rest, true :: bs => seg.append (p1.append (rest.realize bs))

/-- Exact length law for arbitrary-girth `δ`-step adjusters. -/
theorem realize_length {G : SimpleGraph V} {δ : ℕ} :
    ∀ {a b : V} (c : AdjusterChain G δ a b) (mask : List Bool),
      mask.length = c.numAdjusters →
      (c.realize mask).length = c.baseWalk.length + δ * mask.count true
  | _, _, .base p, [], _ => by simp [realize, baseWalk]
  | _, _, .base _, _ :: _, hlen => by simp [numAdjusters] at hlen
  | _, _, .step _ _ _ _ _ _ _, [], hlen => by simp [numAdjusters] at hlen
  | _, _, .step seg p0 p1 _ _ _ rest, false :: bs, hlen => by
      simp only [numAdjusters, List.length_cons, Nat.add_right_cancel_iff] at hlen
      have ih := realize_length rest bs hlen
      simp only [realize, baseWalk, Walk.length_append, List.count_cons]
      simp only [beq_iff_eq, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      omega
  | _, _, .step seg p0 p1 _ _ hstep rest, true :: bs, hlen => by
      simp only [numAdjusters, List.length_cons, Nat.add_right_cancel_iff] at hlen
      have ih := realize_length rest bs hlen
      simp only [realize, baseWalk, Walk.length_append, List.count_cons,
        beq_self_eq_true, ↓reduceIte]
      rw [hstep, ih]; ring

private theorem mem_realize_support_tail {G : SimpleGraph V} {δ : ℕ} :
    ∀ {a b : V} (c : AdjusterChain G δ a b) (mask : List Bool),
      mask.length = c.numAdjusters →
      ∀ x ∈ (c.realize mask).support.tail,
        x ∈ c.baseWalk.support.tail ∨ x ∈ c.altVertices
  | _, _, .base p, [], _, x, hx => Or.inl hx
  | _, _, .base _, _ :: _, hlen, _, _ => by simp [numAdjusters] at hlen
  | _, _, .step _ _ _ _ _ _ _, [], hlen, _, _ => by simp [numAdjusters] at hlen
  | _, _, .step seg p0 p1 hp0 _ _ rest, false :: bs, hlen, x, hx => by
      simp only [numAdjusters, List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [realize, baseWalk, support_append_tail, List.mem_append, altVertices] at hx ⊢
      rcases hx with hseg | hp0x | hrest
      · exact Or.inl (Or.inl hseg)
      · exact Or.inl (Or.inr (Or.inl hp0x))
      · rcases mem_realize_support_tail rest bs hlen x hrest with hbase | halt
        · exact Or.inl (Or.inr (Or.inr hbase))
        · exact Or.inr (Or.inr halt)
  | _, _, .step seg p0 p1 hp0 _ hstep rest, true :: bs, hlen, x, hx => by
      simp only [numAdjusters, List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [realize, baseWalk, support_append_tail, List.mem_append, altVertices] at hx ⊢
      rcases hx with hseg | hp1x | hrest
      · exact Or.inl (Or.inl hseg)
      · rw [support_tail_eq_internals_append_end p1 (by omega), List.mem_append,
          List.mem_singleton] at hp1x
        rcases hp1x with hint | rfl
        · exact Or.inr (Or.inl hint)
        · left; right; left
          rw [support_tail_eq_internals_append_end p0 hp0, List.mem_append]
          exact Or.inr (List.mem_singleton.mpr rfl)
      · rcases mem_realize_support_tail rest bs hlen x hrest with hbase | halt
        · exact Or.inl (Or.inr (Or.inr hbase))
        · exact Or.inr (Or.inr halt)

private theorem realize_support_tail_nodup {G : SimpleGraph V} {δ : ℕ} :
    ∀ {a b : V} (c : AdjusterChain G δ a b) (mask : List Bool),
      mask.length = c.numAdjusters →
      c.baseWalk.support.tail.Nodup →
      c.altVertices.Nodup →
      (∀ z ∈ c.altVertices, z ∉ c.baseWalk.support.tail) →
      (c.realize mask).support.tail.Nodup
  | _, _, .base p, [], _, hnd, _, _ => hnd
  | _, _, .base _, _ :: _, hlen, _, _, _ => by simp [numAdjusters] at hlen
  | _, _, .step _ _ _ _ _ _ _, [], hlen, _, _, _ => by simp [numAdjusters] at hlen
  | _, _, .step seg p0 p1 hp0 _ _ rest, false :: bs, hlen, hnd, halt_nd, hdisj => by
      simp only [numAdjusters, List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [baseWalk, support_append_tail, List.nodup_append] at hnd
      simp only [altVertices, List.nodup_append] at halt_nd
      rcases hnd with ⟨hseg_nd, ⟨hp0_nd, hrb_nd, hp0_rb⟩, hseg_rest⟩
      have hrest_disj : ∀ z ∈ rest.altVertices, z ∉ rest.baseWalk.support.tail := by
        intro z hz hm
        apply hdisj z (by simp [altVertices, hz])
        simp only [baseWalk, support_append_tail, List.mem_append]
        exact Or.inr (Or.inr hm)
      have ih := realize_support_tail_nodup rest bs hlen hrb_nd halt_nd.2.1 hrest_disj
      simp only [realize, support_append_tail, List.nodup_append]
      refine ⟨hseg_nd, ⟨hp0_nd, ih, ?_⟩, ?_⟩
      · intro x hxp0 y hyr hxy; subst hxy
        rcases mem_realize_support_tail rest bs hlen x hyr with hbase | halt
        · exact hp0_rb x hxp0 x hbase rfl
        · apply hdisj x (by simp [altVertices, halt])
          simp only [baseWalk, support_append_tail, List.mem_append]
          exact Or.inr (Or.inl hxp0)
      · intro x hxs y hyr hxy; subst hxy
        rw [List.mem_append] at hyr
        rcases hyr with hxp0 | hxr
        · exact hseg_rest x hxs x (List.mem_append.mpr (Or.inl hxp0)) rfl
        · rcases mem_realize_support_tail rest bs hlen x hxr with hbase | halt
          · exact hseg_rest x hxs x (List.mem_append.mpr (Or.inr hbase)) rfl
          · apply hdisj x (by simp [altVertices, halt])
            simp only [baseWalk, support_append_tail, List.mem_append]
            exact Or.inl hxs
  | _, _, .step (w := w) seg p0 p1 hp0 hp1_path hstep rest, true :: bs, hlen, hnd, halt_nd, hdisj => by
      simp only [numAdjusters, List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [baseWalk, support_append_tail, List.nodup_append] at hnd
      simp only [altVertices, List.nodup_append] at halt_nd
      rcases hnd with ⟨hseg_nd, ⟨hp0_nd, hrb_nd, hp0_rb⟩, hseg_rest⟩
      rcases halt_nd with ⟨_, hrest_alt_nd, hp1_rest_alt⟩
      have hrest_disj : ∀ z ∈ rest.altVertices, z ∉ rest.baseWalk.support.tail := by
        intro z hz hm
        apply hdisj z (by simp [altVertices, hz])
        simp only [baseWalk, support_append_tail, List.mem_append]
        exact Or.inr (Or.inr hm)
      have ih := realize_support_tail_nodup rest bs hlen hrb_nd hrest_alt_nd hrest_disj
      have hp1_tail_nd := support_tail_nodup_of_isPath p1 hp1_path
      have hw_mem_p0 : w ∈ p0.support.tail := by
        rw [support_tail_eq_internals_append_end p0 hp0, List.mem_append]
        exact Or.inr (List.mem_singleton.mpr rfl)
      simp only [realize, support_append_tail, List.nodup_append]
      refine ⟨hseg_nd, ⟨hp1_tail_nd, ih, ?_⟩, ?_⟩
      · intro x hxp1 y hyr hxy; subst hxy
        rw [support_tail_eq_internals_append_end p1 (by omega), List.mem_append,
          List.mem_singleton] at hxp1
        rcases hxp1 with hint | rfl
        · rcases mem_realize_support_tail rest bs hlen x hyr with hbase | halt
          · apply hdisj x (by simp [altVertices, hint])
            simp only [baseWalk, support_append_tail, List.mem_append]
            exact Or.inr (Or.inr hbase)
          · exact hp1_rest_alt x hint x halt rfl
        · rcases mem_realize_support_tail rest bs hlen x hyr with hbase | halt
          · exact hp0_rb x hw_mem_p0 x hbase rfl
          · apply hdisj x (by simp [altVertices, halt])
            simp only [baseWalk, support_append_tail, List.mem_append]
            exact Or.inr (Or.inl hw_mem_p0)
      · intro x hxs y hyr hxy; subst hxy
        rw [List.mem_append] at hyr
        rcases hyr with hxp1 | hxr
        · rw [support_tail_eq_internals_append_end p1 (by omega), List.mem_append,
            List.mem_singleton] at hxp1
          rcases hxp1 with hint | rfl
          · apply hdisj x (by simp [altVertices, hint])
            simp only [baseWalk, support_append_tail, List.mem_append]
            exact Or.inl hxs
          · exact hseg_rest x hxs x (List.mem_append.mpr (Or.inl hw_mem_p0)) rfl
        · rcases mem_realize_support_tail rest bs hlen x hxr with hbase | halt
          · exact hseg_rest x hxs x (List.mem_append.mpr (Or.inr hbase)) rfl
          · apply hdisj x (by simp [altVertices, halt])
            simp only [baseWalk, support_append_tail, List.mem_append]
            exact Or.inl hxs

private theorem mem_realize_edges {G : SimpleGraph V} {δ : ℕ} (hδ : 1 ≤ δ) :
    ∀ {a b : V} (c : AdjusterChain G δ a b) (mask : List Bool),
      mask.length = c.numAdjusters →
      ∀ e ∈ (c.realize mask).edges,
        e ∈ c.baseWalk.edges ∨ ∃ z ∈ c.altVertices, z ∈ e
  | _, _, .base p, [], _, e, he => Or.inl he
  | _, _, .base _, _ :: _, hlen, _, _ => by simp [numAdjusters] at hlen
  | _, _, .step _ _ _ _ _ _ _, [], hlen, _, _ => by simp [numAdjusters] at hlen
  | _, _, .step seg p0 p1 _ _ _ rest, false :: bs, hlen, e, he => by
      simp only [numAdjusters, List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [realize, baseWalk, Walk.edges_append, List.mem_append, altVertices] at he ⊢
      rcases he with hseg | hp0 | hrest
      · exact Or.inl (Or.inl hseg)
      · exact Or.inl (Or.inr (Or.inl hp0))
      · rcases mem_realize_edges hδ rest bs hlen e hrest with hbase | ⟨z, hz, hze⟩
        · exact Or.inl (Or.inr (Or.inr hbase))
        · exact Or.inr ⟨z, Or.inr hz, hze⟩
  | _, _, .step seg p0 p1 hp0 _ hstep rest, true :: bs, hlen, e, he => by
      simp only [numAdjusters, List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [realize, baseWalk, Walk.edges_append, List.mem_append, altVertices] at he ⊢
      rcases he with hseg | hp1 | hrest
      · exact Or.inl (Or.inl hseg)
      · obtain ⟨z, hz, hze⟩ := mem_internals_of_mem_edges_ge2 p1 (by omega) e hp1
        exact Or.inr ⟨z, Or.inl hz, hze⟩
      · rcases mem_realize_edges hδ rest bs hlen e hrest with hbase | ⟨z, hz, hze⟩
        · exact Or.inl (Or.inr (Or.inr hbase))
        · exact Or.inr ⟨z, Or.inr hz, hze⟩

private theorem mem_append_support_right {G : SimpleGraph V} {a u b : V}
    (p : G.Walk a u) (q : G.Walk u b) {z : V} (hz : z ∈ q.support) :
    z ∈ (p.append q).support := by
  rw [Walk.support_append, List.mem_append]
  rw [support_eq_cons_start q, List.mem_cons] at hz
  rcases hz with rfl | ht
  · exact Or.inl (Walk.end_mem_support p)
  · exact Or.inr ht

private theorem realize_edges_nodup {G : SimpleGraph V} {δ : ℕ} (hδ : 1 ≤ δ) :
    ∀ {a b : V} (c : AdjusterChain G δ a b) (mask : List Bool),
      mask.length = c.numAdjusters →
      c.baseWalk.edges.Nodup →
      c.altVertices.Nodup →
      (∀ z ∈ c.altVertices, z ∉ c.baseWalk.support) →
      (c.realize mask).edges.Nodup
  | _, _, .base p, [], _, hnd, _, _ => hnd
  | _, _, .base _, _ :: _, hlen, _, _, _ => by simp [numAdjusters] at hlen
  | _, _, .step _ _ _ _ _ _ _, [], hlen, _, _, _ => by simp [numAdjusters] at hlen
  | _, _, .step seg p0 p1 _ _ _ rest, false :: bs, hlen, hnd, halt_nd, hdisj => by
      simp only [numAdjusters, List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [baseWalk, Walk.edges_append, List.nodup_append] at hnd
      simp only [altVertices, List.nodup_append] at halt_nd
      rcases hnd with ⟨hseg_nd, ⟨hp0_nd, hrb_nd, hp0_rb⟩, hseg_rest⟩
      have hrest_disj : ∀ z ∈ rest.altVertices, z ∉ rest.baseWalk.support := by
        intro z hz hm
        apply hdisj z (by simp [altVertices, hz])
        exact mem_append_support_right seg (p0.append rest.baseWalk)
          (mem_append_support_right p0 rest.baseWalk hm)
      have ih := realize_edges_nodup hδ rest bs hlen hrb_nd halt_nd.2.1 hrest_disj
      simp only [realize, Walk.edges_append, List.nodup_append]
      refine ⟨hseg_nd, ⟨hp0_nd, ih, ?_⟩, ?_⟩
      · intro e hep0 e' her hee; subst hee
        rcases mem_realize_edges hδ rest bs hlen e her with hbase | ⟨z, hz, hze⟩
        · exact hp0_rb e hep0 e hbase rfl
        · apply hdisj z (by simp [altVertices, hz])
          exact mem_append_support_right seg (p0.append rest.baseWalk)
            (by rw [Walk.support_append, List.mem_append]; exact Or.inl (mem_support_of_mem_edges hep0 hze))
      · intro e hes e' her hee; subst hee
        rw [List.mem_append] at her
        rcases her with hep0 | her
        · exact hseg_rest e hes e (List.mem_append.mpr (Or.inl hep0)) rfl
        · rcases mem_realize_edges hδ rest bs hlen e her with hbase | ⟨z, hz, hze⟩
          · exact hseg_rest e hes e (List.mem_append.mpr (Or.inr hbase)) rfl
          · apply hdisj z (by simp [altVertices, hz])
            simp only [baseWalk, Walk.support_append, List.mem_append]
            exact Or.inl (mem_support_of_mem_edges hes hze)
  | _, _, .step (w := w) seg p0 p1 hp0 hp1_path hstep rest, true :: bs, hlen, hnd, halt_nd, hdisj => by
      simp only [numAdjusters, List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [baseWalk, Walk.edges_append, List.nodup_append] at hnd
      simp only [altVertices, List.nodup_append] at halt_nd
      rcases hnd with ⟨hseg_nd, ⟨_, hrb_nd, _⟩, hseg_rest⟩
      rcases halt_nd with ⟨_, hrest_alt_nd, hp1_rest_alt⟩
      have hrest_disj : ∀ z ∈ rest.altVertices, z ∉ rest.baseWalk.support := by
        intro z hz hm
        apply hdisj z (by simp [altVertices, hz])
        exact mem_append_support_right seg (p0.append rest.baseWalk)
          (mem_append_support_right p0 rest.baseWalk hm)
      have ih := realize_edges_nodup hδ rest bs hlen hrb_nd hrest_alt_nd hrest_disj
      simp only [realize, Walk.edges_append, List.nodup_append]
      refine ⟨hseg_nd, ⟨hp1_path.edges_nodup, ih, ?_⟩, ?_⟩
      · intro e hep1 e' her hee; subst hee
        obtain ⟨z, hz_int, hze⟩ := mem_internals_of_mem_edges_ge2 p1 (by omega) e hep1
        have hz_supp : z ∈ (rest.realize bs).support := mem_support_of_mem_edges her hze
        rw [support_eq_cons_start (rest.realize bs), List.mem_cons] at hz_supp
        rcases hz_supp with rfl | hws
        · apply hdisj z (by simp [altVertices, hz_int])
          exact mem_append_support_right seg (p0.append rest.baseWalk)
            (mem_append_support_right p0 rest.baseWalk (Walk.start_mem_support rest.baseWalk))
        · rcases mem_realize_support_tail rest bs hlen z hws with hbase | halt
          · apply hdisj z (by simp [altVertices, hz_int])
            exact mem_append_support_right seg (p0.append rest.baseWalk)
              (mem_append_support_right p0 rest.baseWalk (List.mem_of_mem_tail hbase))
          · exact hp1_rest_alt z hz_int z halt rfl
      · intro e hes e' her hee; subst hee
        rw [List.mem_append] at her
        rcases her with hep1 | her
        · obtain ⟨z, hz_int, hze⟩ := mem_internals_of_mem_edges_ge2 p1 (by omega) e hep1
          apply hdisj z (by simp [altVertices, hz_int])
          simp only [baseWalk, Walk.support_append, List.mem_append]
          exact Or.inl (mem_support_of_mem_edges hes hze)
        · rcases mem_realize_edges hδ rest bs hlen e her with hbase | ⟨z, hz, hze⟩
          · exact hseg_rest e hes e (List.mem_append.mpr (Or.inr hbase)) rfl
          · apply hdisj z (by simp [altVertices, hz])
            simp only [baseWalk, Walk.support_append, List.mem_append]
            exact Or.inl (mem_support_of_mem_edges hes hze)

/-- **Pillar 3A — Generalized Arbitrary-Girth `AdjusterChain` Simple-Cycle Theorem**:
For ANY uniform step `δ ≥ 1` (covering both `δ = 1` odd-cycle and `δ = 2` even-cycle
quasi-diagonal adjusters at arbitrary fixed girth `g ≥ 3`), every boolean mask realizes a
**simple cycle (`Walk.IsCycle`)** of exact length `L_0 + δ * mask.count true`. -/
theorem realize_isCycle {G : SimpleGraph V} {δ : ℕ} (hδ : 1 ≤ δ) {v : V}
    (c : AdjusterChain G δ v v) (hcyc : c.baseWalk.IsCycle)
    (halt : c.altVertices.Nodup) (hdisj : ∀ z ∈ c.altVertices, z ∉ c.baseWalk.support)
    (mask : List Bool) (hlen : mask.length = c.numAdjusters) :
    (c.realize mask).IsCycle := by
  have hdisj_tail : ∀ z ∈ c.altVertices, z ∉ c.baseWalk.support.tail :=
    fun z hz hm => hdisj z hz (List.mem_of_mem_tail hm)
  have htail_nd := realize_support_tail_nodup c mask hlen hcyc.support_nodup halt hdisj_tail
  have hedges_nd := realize_edges_nodup hδ c mask hlen hcyc.edges_nodup halt hdisj
  have hne : c.realize mask ≠ Walk.nil := by
    intro hnil
    have hpos : 0 < (c.realize mask).length := by
      rw [realize_length c mask hlen]
      have := hcyc.three_le_length; omega
    rw [hnil] at hpos; simp at hpos
  exact ⟨⟨⟨hedges_nd⟩, hne⟩, htail_nd⟩

/-- Realizes EVERY cycle length `L_0 + δ * j` for `0 ≤ j ≤ r`. -/
theorem exists_cycle_of_step_Icc {G : SimpleGraph V} {δ : ℕ} (hδ : 1 ≤ δ) {v : V}
    (c : AdjusterChain G δ v v) (hcyc : c.baseWalk.IsCycle)
    (halt : c.altVertices.Nodup) (hdisj : ∀ z ∈ c.altVertices, z ∉ c.baseWalk.support)
    {j : ℕ} (hj : j ≤ c.numAdjusters) :
    ∃ p : G.Walk v v, p.IsCycle ∧ p.length = c.baseWalk.length + δ * j := by
  let mask : List Bool := List.replicate j true ++ List.replicate (c.numAdjusters - j) false
  have hlen : mask.length = c.numAdjusters := by simp [mask]; omega
  have hcnt : mask.count true = j := by simp [mask, List.count_append, List.count_replicate]
  refine ⟨c.realize mask, realize_isCycle hδ c hcyc halt hdisj mask hlen, ?_⟩
  rw [realize_length c mask hlen, hcnt]

/-- **Pillar 3B — Unbounded-`n`, Arbitrary Fixed Odd Girth (`δ = 1`) Closure**:
Any simple cycle of length `L_0` with `r ≥ L_0 - 2` vertex-disjoint `δ = 1` adjusters
(e.g., quasi-diagonal `C_5, C_7, ..., C_{2s+1}` adjusters at arbitrary odd girth `g = 2s + 1`)
unconditionally forces `HasPower G`. -/
theorem hasPower_of_delta1_adjusters {G : SimpleGraph V} {v : V}
    (c : AdjusterChain G 1 v v) (hcyc : c.baseWalk.IsCycle)
    (halt : c.altVertices.Nodup) (hdisj : ∀ z ∈ c.altVertices, z ∉ c.baseWalk.support)
    (hdense : c.baseWalk.length - 2 ≤ c.numAdjusters) :
    HasPower G := by
  have hL3 : 3 ≤ c.baseWalk.length := hcyc.three_le_length
  refine hasPower_of_consecutive_cycles G hL3 (B := c.baseWalk.length + c.numAdjusters) (by omega) ?_
  intro L hlo hhi
  obtain ⟨p, hp, hlen⟩ :=
    exists_cycle_of_step_Icc (by omega) c hcyc halt hdisj (j := L - c.baseWalk.length) (by omega)
  exact ⟨v, p, hp, by omega⟩

/-- **Pillar 3C — Unbounded-`n`, Arbitrary Fixed Even Girth (`δ = 2`) Closure**:
Any simple even cycle of length `2a` (`a ≥ 2`) with `r ≥ a - 2` vertex-disjoint `δ = 2` adjusters
(e.g., quasi-diagonal `C_6, C_8, C_{10}, ..., C_{2s}` adjusters at arbitrary even girth `g = 2s`)
unconditionally forces `HasPower G`. -/
theorem hasPower_of_delta2_even_adjusters {G : SimpleGraph V} {v : V} {a : ℕ}
    (c : AdjusterChain G 2 v v) (hcyc : c.baseWalk.IsCycle)
    (heven : c.baseWalk.length = 2 * a) (ha : 2 ≤ a)
    (halt : c.altVertices.Nodup) (hdisj : ∀ z ∈ c.altVertices, z ∉ c.baseWalk.support)
    (hdense : a - 2 ≤ c.numAdjusters) :
    HasPower G := by
  refine hasPower_of_consecutive_even_cycles G ha (b := a + c.numAdjusters) (by omega) ?_
  intro m hlo hhi
  obtain ⟨p, hp, hlen⟩ :=
    exists_cycle_of_step_Icc (by omega) c hcyc halt hdisj (j := m - a) (by omega)
  exact ⟨v, p, hp, by omega⟩

/-- **Pillar 3D — Arbitrary-Girth Strict-Interior Edge Saturation**:
Whenever `target = L_0 + δ * j` with `1 ≤ j < r`, EVERY adjuster `i < r` has BOTH a simple
`target`-cycle taking the short path (`mask[i] = false`) AND a simple `target`-cycle taking
the long path (`mask[i] = true`). -/
theorem interior_edge_saturation {G : SimpleGraph V} {δ : ℕ} (hδ : 1 ≤ δ) {v : V}
    (c : AdjusterChain G δ v v) (hcyc : c.baseWalk.IsCycle)
    (halt : c.altVertices.Nodup) (hdisj : ∀ z ∈ c.altVertices, z ∉ c.baseWalk.support)
    {j i : ℕ} (hj1 : 1 ≤ j) (hjr : j < c.numAdjusters) (hi : i < c.numAdjusters) :
    (∃ mask : List Bool, ∃ hlen : mask.length = c.numAdjusters,
      mask[i]'(by omega) = false ∧ (c.realize mask).IsCycle ∧
      (c.realize mask).length = c.baseWalk.length + δ * j) ∧
    (∃ mask : List Bool, ∃ hlen : mask.length = c.numAdjusters,
      mask[i]'(by omega) = true ∧ (c.realize mask).IsCycle ∧
      (c.realize mask).length = c.baseWalk.length + δ * j) := by
  let r := c.numAdjusters
  constructor
  · let a := min i j
    let b := j - a
    have ha_le_i : a ≤ i := Nat.min_le_left i j
    have hb_le : b ≤ r - 1 - i := by omega
    let pre : List Bool := List.replicate a true ++ List.replicate (i - a) false
    let suf : List Bool := List.replicate b true ++ List.replicate (r - 1 - i - b) false
    let mask : List Bool := pre ++ (false :: suf)
    have hpre_len : pre.length = i := by simp [pre]; omega
    have hsuf_len : suf.length = r - 1 - i := by simp [suf]; omega
    have hlen : mask.length = r := by simp [mask, hpre_len, hsuf_len]; omega
    have hget : mask[i]'(by omega) = false := by
      simp [mask, List.getElem_append_right, hpre_len]
    have hcnt : mask.count true = j := by
      simp [mask, pre, suf, List.count_append, List.count_replicate]; omega
    refine ⟨mask, hlen, hget, realize_isCycle hδ c hcyc halt hdisj mask hlen, ?_⟩
    rw [realize_length c mask hlen, hcnt]
  · let a := min i (j - 1)
    let b := (j - 1) - a
    have ha_le_i : a ≤ i := Nat.min_le_left i (j - 1)
    have hb_le : b ≤ r - 1 - i := by omega
    let pre : List Bool := List.replicate a true ++ List.replicate (i - a) false
    let suf : List Bool := List.replicate b true ++ List.replicate (r - 1 - i - b) false
    let mask : List Bool := pre ++ (true :: suf)
    have hpre_len : pre.length = i := by simp [pre]; omega
    have hsuf_len : suf.length = r - 1 - i := by simp [suf]; omega
    have hlen : mask.length = r := by simp [mask, hpre_len, hsuf_len]; omega
    have hget : mask[i]'(by omega) = true := by
      simp [mask, List.getElem_append_right, hpre_len]
    have hcnt : mask.count true = j := by
      simp [mask, pre, suf, List.count_append, List.count_replicate]; omega
    refine ⟨mask, hlen, hget, realize_isCycle hδ c hcyc halt hdisj mask hlen, ?_⟩
    rw [realize_length c mask hlen, hcnt]

end AdjusterChain
end AdjusterChains

#print axioms isCycle_append_reverse_of_internally_disjoint
#print axioms bsv_chorded_cycle_all_even_ab_paths
#print axioms bfs_lca_even_cycle_interval
#print axioms hasPower_of_bfs_chorded_cycle
#print axioms cubic_two_layer_deg_le_two
#print axioms cubic_two_layer_no_chorded_cycle
#print axioms quasi_diagonal_even_odd_consecutive_even_cycles
#print axioms hasPower_of_quasi_diagonal_even_odd_hit
#print axioms AdjusterChain.realize_length
#print axioms AdjusterChain.realize_isCycle
#print axioms AdjusterChain.exists_cycle_of_step_Icc
#print axioms AdjusterChain.hasPower_of_delta1_adjusters
#print axioms AdjusterChain.hasPower_of_delta2_even_adjusters
#print axioms AdjusterChain.interior_edge_saturation

end E64Wave7Agent6
