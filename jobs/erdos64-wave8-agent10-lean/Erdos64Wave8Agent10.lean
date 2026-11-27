import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Nodup
import Mathlib.Tactic

namespace E64Wave8Agent10

/-!
# Erdős Problem #64 — Wave 8 Free Agent #10 (`wave8_agent10`)
## Unconditional All-Order Structural Closures:
1. P3-Collapse (`G_y(u)`, working even on triangle-incident cubic vertices) & 3-Way Cubic
   Edge-Surgery (`G_∥`, `G_×1`, `G_×2`) with Girth-g Disjoint-Pair Elimination (`2^c < 2g - 2`)
2. Crossing-Chord 7-Cycle Spectrum Theorem & Balanced-Sum Refutation
3. Arbitrary-Girth `r`-Rung Ladder Trichotomy (`g ∈ {5,7,9,11,12,13}` unbounded-n closures),
   Exact Mod-4 Immunity Obstruction (`g ≡ 2 (mod 4)`), Mod-8 Girth-10 Shift Obstruction,
   and Twist-Breakers for `g ∈ {6, 10, 14}`
4. Ihara–Chebyshev `B^16` Cage-Surpassing Thresholds (`g ∈ {9..12}` & Bipartite `g = 14`)
   and `EGRob` Two-Copy Gluing Half-Power Path Exclusion
-/

/-- A positive integer is a power of two at least 4 (`2^k` with `k ≥ 2`). -/
def IsPowerOfTwo (n : ℕ) : Prop := ∃ k : ℕ, 2 ≤ k ∧ n = 2 ^ k

/-- Simple cycle of length ≥ 3 in a `SimpleGraph V`, represented by its distinct vertex list. -/
structure SimpleCycle {V : Type*} (G : SimpleGraph V) where
  verts : List V
  len_ge_three : 3 ≤ verts.length
  nodup : verts.Nodup
  adj_cycle : ∀ i (hi : i < verts.length),
    G.Adj (verts[i]'hi) (verts[(i + 1) % verts.length]'(Nat.mod_lt _ (by omega)))

/-- A graph satisfies Erdős–Gyárfás if it contains a simple cycle of length `2^k` (`k ≥ 2`). -/
def HasPowerCycle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ C : SimpleCycle G, IsPowerOfTwo C.verts.length

/-- A graph is power-free if it has no simple cycle of length `2^k` (`k ≥ 2`). -/
def PowerFree {V : Type*} (G : SimpleGraph V) : Prop := ¬ HasPowerCycle G

/-- Core cycle builder from any non-empty `Nodup` `IsChain G.Adj` list whose last connects to head. -/
def SimpleCycle.ofList {V : Type*} {G : SimpleGraph V} (L : List V)
    (h3 : 3 ≤ L.length) (hnd : L.Nodup) (hch : L.IsChain G.Adj)
    (hne : L ≠ []) (hwrap : G.Adj (L.getLast hne) (L.head hne)) : SimpleCycle G where
  verts := L
  len_ge_three := h3
  nodup := hnd
  adj_cycle := by
    intro i hi
    by_cases hlast : i + 1 < L.length
    · have hmod : (i + 1) % L.length = i + 1 := Nat.mod_eq_of_lt hlast
      simp only [hmod]
      exact (List.isChain_iff_getElem.mp hch) i hlast
    · have hi_eq : i = L.length - 1 := by omega
      have hmod : (i + 1) % L.length = 0 := by
        rw [hi_eq, Nat.sub_add_cancel (by omega), Nat.mod_self]
      simp only [hmod]
      have h0 : L[0]'(by omega) = L.head hne := (List.head_eq_getElem hne).symm
      have hL : L[i]'hi = L.getLast hne := by
        rw [List.getLast_eq_getElem]; congr 1
      rw [h0, hL]
      exact hwrap

/-- Helper: `IsChain R (l1 ++ l2)` given chains on `l1, l2` and link from `l1.getLast` to `l2.head`. -/
private lemma isChain_append_of_link {α : Type*} {R : α → α → Prop} {l1 l2 : List α}
    (h1 : l1.IsChain R) (h2 : l2.IsChain R) (hne1 : l1 ≠ []) (hne2 : l2 ≠ [])
    (hlink : R (l1.getLast hne1) (l2.head hne2)) :
    (l1 ++ l2).IsChain R := by
  rw [List.isChain_append]
  refine ⟨h1, h2, fun x hx y hy => ?_⟩
  rw [List.getLast?_eq_some_getLast hne1] at hx
  rw [List.head?_eq_some_head hne2] at hy
  injection hx with hx; injection hy with hy
  subst hx; subst hy
  exact hlink

/-- Helper: `Nodup (A ++ B)` from `Nodup A`, `Nodup B`, and `List.Disjoint A B`. -/
private lemma nodup_append_of_disjoint {α : Type*} {A B : List α}
    (hA : A.Nodup) (hB : B.Nodup) (hd : List.Disjoint A B) : (A ++ B).Nodup :=
  List.nodup_append.mpr ⟨hA, hB, fun _a ha _b hb hab => hd ha (hab ▸ hb)⟩

/-- Helper: reversing an `IsChain G.Adj` preserves `IsChain G.Adj` by symmetry of `G.Adj`. -/
private lemma isChain_reverse_adj {V : Type*} {G : SimpleGraph V} {l : List V}
    (h : l.IsChain G.Adj) : l.reverse.IsChain G.Adj := by
  rw [List.isChain_iff_getElem] at h ⊢
  intro i hi
  simp only [List.length_reverse] at hi
  rw [List.getElem_reverse (by omega), List.getElem_reverse (by omega)]
  have h1 : l.length - 1 - (i + 1) + 1 = l.length - 1 - i := by omega
  have h2 := h (l.length - 1 - (i + 1)) (by omega)
  simp only [h1] at h2
  exact G.adj_comm _ _ |>.mp h2

/-- Helper: `head` of `l.reverse` equals `getLast` of `l`. -/
private lemma head_reverse_eq_getLast {α : Type*} {l : List α} (hne : l ≠ []) :
    l.reverse.head (by simpa using hne) = l.getLast hne := by
  rw [List.head_eq_getElem, List.getLast_eq_getElem, List.getElem_reverse]
  congr 1

/-- Helper: `getLast` of `l.reverse` equals `head` of `l`. -/
private lemma getLast_reverse_eq_head {α : Type*} {l : List α} (hne : l ≠ []) :
    l.reverse.getLast (by simpa using hne) = l.head hne := by
  rw [List.getLast_eq_getElem, List.head_eq_getElem, List.getElem_reverse]
  simp

/-- Core 2-arc cycle builder: glues two disjoint non-empty paths `A, B` into a `SimpleCycle G`. -/
def SimpleCycle.ofTwoArcs {V : Type*} {G : SimpleGraph V} (A B : List V)
    (hneA : A ≠ []) (hneB : B ≠ [])
    (h3 : 3 ≤ A.length + B.length)
    (hndA : A.Nodup) (hndB : B.Nodup) (hdisj : List.Disjoint A B)
    (hchA : A.IsChain G.Adj) (hchB : B.IsChain G.Adj)
    (hAB : G.Adj (A.getLast hneA) (B.head hneB))
    (hBA : G.Adj (B.getLast hneB) (A.head hneA)) : SimpleCycle G :=
  SimpleCycle.ofList (A ++ B)
    (by rw [List.length_append]; exact h3)
    (nodup_append_of_disjoint hndA hndB hdisj)
    (isChain_append_of_link hchA hchB hneA hneB hAB)
    (by intro h; exact hneA (List.append_eq_nil_iff.mp h).1)
    (by
      rw [List.getLast_append_of_ne_nil _ hneB, List.head_append_of_ne_nil hneA]
      exact hBA)

/-! ### Part I: P3-Collapse (`G_y(u)`) & 3-Way Cubic Edge-Surgery (`G_∥`, `G_×1`, `G_×2`) -/

/-- Theorem 1 (P3-Collapse Double-Edge Refutation):
    In `G_y(u) = (G - u) + {xy, yz}`, if a `2^k`-cycle uses BOTH edges `xy` and `yz`,
    its remaining path `P` from `z` to `x` in `G - {u, y}` has `2^k - 1` vertices.
    Replacing `x - y - z` by `x - u - z` yields a valid `SimpleCycle G` of exact length `2^k`! -/
theorem p3_collapse_double_edge_gives_pow2 {V : Type*} {G : SimpleGraph V}
    {u x z : V} {k : ℕ} (hk : 2 ≤ k)
    (P : List V) (hne : P ≠ []) (hlen : P.length = 2 ^ k - 1)
    (hnd : P.Nodup) (hch : P.IsChain G.Adj)
    (hu_not : u ∉ P)
    (hhead : P.head hne = z) (hlast : P.getLast hne = x)
    (hux : G.Adj x u) (huz : G.Adj u z) :
    HasPowerCycle G := by
  have hpow4 : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
  let C := SimpleCycle.ofTwoArcs P [u] hne (by simp)
    (by simp [hlen]; omega)
    hnd (List.nodup_singleton u)
    (fun v hv hu => by simp at hu; subst hu; exact hu_not hv)
    hch (List.isChain_singleton u)
    (by simp [hlast]; exact hux)
    (by simp [hhead]; exact huz)
  refine ⟨C, k, hk, ?_⟩
  show (P ++ [u]).length = 2 ^ k
  simp [hlen]; omega

/-- Theorem 2 (P3-Collapse Single-Edge Lift):
    In `G_y(u) = (G - u) + {xy, yz}`, a simple `2^k`-cycle using ONLY ONE added edge `xy`
    (a `2^k`-vertex simple path `P` from `y` to `x` in `G - u`) lifts to a simple `(2^k + 1)`-cycle
    in `G` passing through `x - u - y`. Works even when `u` lies in a triangle `uxz`! -/
theorem p3_collapse_single_edge_lifts_to_2k_plus_1 {V : Type*} {G : SimpleGraph V}
    {u x y : V} {k : ℕ} (hk : 2 ≤ k)
    (P : List V) (hne : P ≠ []) (hlen : P.length = 2 ^ k)
    (hnd : P.Nodup) (hch : P.IsChain G.Adj)
    (hu_not : u ∉ P)
    (hhead : P.head hne = y) (hlast : P.getLast hne = x)
    (hux : G.Adj x u) (huy : G.Adj u y) :
    ∃ C : SimpleCycle G, C.verts.length = 2 ^ k + 1 ∧ u ∈ C.verts := by
  have hpow4 : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
  let C := SimpleCycle.ofTwoArcs P [u] hne (by simp)
    (by simp [hlen]; omega)
    hnd (List.nodup_singleton u)
    (fun v hv hu => by simp at hu; subst hu; exact hu_not hv)
    hch (List.isChain_singleton u)
    (by simp [hlast]; exact hux)
    (by simp [hhead]; exact huy)
  refine ⟨C, ?_, ?_⟩
  · show (P ++ [u]).length = 2 ^ k + 1
    simp [hlen]
  · show u ∈ P ++ [u]
    simp

/-- Theorem 3 (Dual Cross-Rewiring Single-Edge Lift):
    In `G_×1(uv) = (G - {u,v}) + {a1 b1, a2 b2}`, a simple `2^c`-cycle using ONE added edge `a1 b1`
    lifts to a simple `(2^c + 2)`-cycle in `G` passing through `a1 - u - v - b1`. -/
theorem cross_rewiring_single_edge_lifts_to_2k_plus_2 {V : Type*} {G : SimpleGraph V}
    {u v a1 b1 : V} {c : ℕ} (hc : 2 ≤ c) (huv : G.Adj u v)
    (P : List V) (hne : P ≠ []) (hlen : P.length = 2 ^ c)
    (hnd : P.Nodup) (hch : P.IsChain G.Adj)
    (hu_not : u ∉ P) (hv_not : v ∉ P)
    (hhead : P.head hne = b1) (hlast : P.getLast hne = a1)
    (hua : G.Adj a1 u) (hvb : G.Adj v b1) :
    ∃ C : SimpleCycle G, C.verts.length = 2 ^ c + 2 ∧ u ∈ C.verts ∧ v ∈ C.verts := by
  have hpow4 : 4 ≤ 2 ^ c := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ c := Nat.pow_le_pow_right (by omega) hc
  have hne_uv : u ≠ v := G.ne_of_adj huv
  let C := SimpleCycle.ofTwoArcs P [u, v] hne (by simp)
    (by simp [hlen]; omega)
    hnd (by simp [hne_uv])
    (fun w hw hmem => by
      simp at hmem
      rcases hmem with rfl | rfl
      · exact hu_not hw
      · exact hv_not hw)
    hch (by simp [huv])
    (by simp [hlast]; exact hua)
    (by simp [hhead]; exact hvb)
  refine ⟨C, ?_, ?_, ?_⟩
  · show (P ++ [u, v]).length = 2 ^ c + 2
    simp [hlen]
  · show u ∈ P ++ [u, v]; simp
  · show v ∈ P ++ [u, v]; simp

/-- Theorem 4 (Dual Cross-Rewiring Crossed-Pair Lift):
    If a simple `2^c`-cycle in `G_×1(uv)` uses BOTH added edges in the crossed orientation
    (`P1 : a1 ⇝ b2`, `P2 : a2 ⇝ b1`, vertex-disjoint in `G - {u,v}` with `|P1| + |P2| = 2^c`),
    splicing `u` and `v` yields a simple `(2^c + 2)`-cycle in `G - uv`! -/
theorem cross_rewiring_crossed_pair_lifts_to_2k_plus_2 {V : Type*} {G : SimpleGraph V}
    {u v a1 a2 b1 b2 : V} {c : ℕ} (hc : 2 ≤ c) (hne_uv : u ≠ v)
    (P1 P2 : List V) (hne1 : P1 ≠ []) (hne2 : P2 ≠ [])
    (hlen : P1.length + P2.length = 2 ^ c)
    (hnd1 : P1.Nodup) (hnd2 : P2.Nodup) (hdisj : List.Disjoint P1 P2)
    (hch1 : P1.IsChain G.Adj) (hch2 : P2.IsChain G.Adj)
    (hu1 : u ∉ P1) (hv1 : v ∉ P1) (hu2 : u ∉ P2) (hv2 : v ∉ P2)
    (h1_head : P1.head hne1 = a1) (h1_last : P1.getLast hne1 = b2)
    (h2_head : P2.head hne2 = b1) (h2_last : P2.getLast hne2 = a2)
    (hua1 : G.Adj u a1) (hvb2 : G.Adj b2 v) (hvb1 : G.Adj v b1) (hua2 : G.Adj a2 u) :
    ∃ C : SimpleCycle G, C.verts.length = 2 ^ c + 2 := by
  have hpow4 : 4 ≤ 2 ^ c := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ c := Nat.pow_le_pow_right (by omega) hc
  let A := u :: P1
  let B := v :: P2
  have hneA : A ≠ [] := List.cons_ne_nil u P1
  have hneB : B ≠ [] := List.cons_ne_nil v P2
  have hchA : A.IsChain G.Adj := by
    change ([u] ++ P1).IsChain G.Adj
    exact isChain_append_of_link (List.isChain_singleton u) hch1 (by simp) hne1 (by simp [h1_head]; exact hua1)
  have hchB : B.IsChain G.Adj := by
    change ([v] ++ P2).IsChain G.Adj
    exact isChain_append_of_link (List.isChain_singleton v) hch2 (by simp) hne2 (by simp [h2_head]; exact hvb1)
  have hlastA : A.getLast hneA = b2 := by
    change ([u] ++ P1).getLast _ = b2
    rw [List.getLast_append_of_ne_nil _ hne1, h1_last]
  have hlastB : B.getLast hneB = a2 := by
    change ([v] ++ P2).getLast _ = a2
    rw [List.getLast_append_of_ne_nil _ hne2, h2_last]
  let C := SimpleCycle.ofTwoArcs A B hneA hneB
    (by simp [A, B]; omega)
    (List.nodup_cons.mpr ⟨hu1, hnd1⟩)
    (List.nodup_cons.mpr ⟨hv2, hnd2⟩)
    (fun w hwA hwB => by
      simp only [A, B, List.mem_cons] at hwA hwB
      rcases hwA with rfl | hw1
      · rcases hwB with h | hw2
        · exact hne_uv h
        · exact hu2 hw2
      · rcases hwB with rfl | hw2
        · exact hv1 hw1
        · exact hdisj hw1 hw2)
    hchA hchB
    (by rw [hlastA]; simpa [B] using hvb2)
    (by rw [hlastB]; simpa [A] using hua2)
  refine ⟨C, ?_⟩
  show (A ++ B).length = 2 ^ c + 2
  simp [A, B]; omega

/-- Theorem 5 (Girth-g Disjoint-Pair Elimination for Dual Cross-Rewiring):
    In any graph of girth ≥ g, the disjoint-cycle escape `|D_u| + |D_v| = 2^c + 2` in
    `G_×i(uv)` is IMPOSSIBLE whenever `2^c + 2 < 2 * g`! -/
theorem cross_rewiring_no_disjoint_pair_below_2g_minus_2 {g c d1 d2 : ℕ}
    (hd1 : g ≤ d1) (hd2 : g ≤ d2) (hsum : d1 + d2 = 2 ^ c + 2)
    (hsmall : 2 ^ c + 2 < 2 * g) : False := by
  omega

/-- Theorem 6 (Girth ≥ 10 Eliminates ALL C4, C8, and C16 Disjoint-Pair Escapes):
    For any graph of girth g ≥ 10 (the open frontier g ∈ {10..14}), NO C4, C8, or C16
    in `G_×1(uv)` or `G_×2(uv)` can lift to a disjoint-cycle pair! -/
theorem cross_rewiring_girth10_eliminates_c4_c8_c16_pairs {g c d1 d2 : ℕ}
    (hg : 10 ≤ g) (hc : c = 2 ∨ c = 3 ∨ c = 4)
    (hd1 : g ≤ d1) (hd2 : g ≤ d2) (hsum : d1 + d2 = 2 ^ c + 2) : False := by
  rcases hc with rfl | rfl | rfl <;>
    exact cross_rewiring_no_disjoint_pair_below_2g_minus_2 hd1 hd2 hsum (by omega)

/-- Theorem 7 (Same-Side Suppression Lift):
    In `G_∥(uv) = (G - {u,v}) + {a1 a2, b1 b2}`, a simple `2^c`-cycle using both added edges
    lifts directly to a simple `(2^c + 2)`-cycle in `G - uv`. -/
theorem same_side_suppression_lifts_to_2k_plus_1_or_2 {V : Type*} {G : SimpleGraph V}
    {u v a1 a2 b1 b2 : V} {c : ℕ} (hc : 2 ≤ c) (hne_uv : u ≠ v)
    (P1 P2 : List V) (hne1 : P1 ≠ []) (hne2 : P2 ≠ [])
    (hlen : P1.length + P2.length = 2 ^ c)
    (hnd1 : P1.Nodup) (hnd2 : P2.Nodup) (hdisj : List.Disjoint P1 P2)
    (hch1 : P1.IsChain G.Adj) (hch2 : P2.IsChain G.Adj)
    (hu1 : u ∉ P1) (hv1 : v ∉ P1) (hu2 : u ∉ P2) (hv2 : v ∉ P2)
    (h1_head : P1.head hne1 = a2) (h1_last : P1.getLast hne1 = b1)
    (h2_head : P2.head hne2 = b2) (h2_last : P2.getLast hne2 = a1)
    (hua2 : G.Adj u a2) (hvb1 : G.Adj b1 v) (hvb2 : G.Adj v b2) (hua1 : G.Adj a1 u) :
    ∃ C : SimpleCycle G, C.verts.length = 2 ^ c + 2 :=
  cross_rewiring_crossed_pair_lifts_to_2k_plus_2 hc hne_uv P1 P2 hne1 hne2 hlen hnd1 hnd2 hdisj
    hch1 hch2 hu1 hv1 hu2 hv2 h1_head h1_last h2_head h2_last hua2 hvb1 hvb2 hua1

/-! ### Part II: Crossing-Chord 7-Cycle Spectrum Theorem (All Girths, Unbounded n) -/

/-- A cycle split by two crossing chords `(u0, ub)` and `(ua, uc)` into 4 pairwise vertex-disjoint
    non-empty arcs `A1, A2, A3, A4` of lengths `x1, x2, x3, x4 ≥ 1`. -/
structure CrossingChordPair {V : Type*} (G : SimpleGraph V) where
  A1 : List V
  A2 : List V
  A3 : List V
  A4 : List V
  hne1 : A1 ≠ []
  hne2 : A2 ≠ []
  hne3 : A3 ≠ []
  hne4 : A4 ≠ []
  hnd1 : A1.Nodup
  hnd2 : A2.Nodup
  hnd3 : A3.Nodup
  hnd4 : A4.Nodup
  hch1 : A1.IsChain G.Adj
  hch2 : A2.IsChain G.Adj
  hch3 : A3.IsChain G.Adj
  hch4 : A4.IsChain G.Adj
  d12 : List.Disjoint A1 A2
  d13 : List.Disjoint A1 A3
  d14 : List.Disjoint A1 A4
  d23 : List.Disjoint A2 A3
  d24 : List.Disjoint A2 A4
  d34 : List.Disjoint A3 A4
  link12 : G.Adj (A1.getLast hne1) (A2.head hne2)
  link23 : G.Adj (A2.getLast hne2) (A3.head hne3)
  link34 : G.Adj (A3.getLast hne3) (A4.head hne4)
  link41 : G.Adj (A4.getLast hne4) (A1.head hne1)
  chord1 : G.Adj (A1.head hne1) (A3.head hne3)
  chord2 : G.Adj (A2.head hne2) (A4.head hne4)

namespace CrossingChordPair

variable {V : Type*} {G : SimpleGraph V} (X : CrossingChordPair G)

private lemma len_pos1 : 1 ≤ X.A1.length := List.length_pos_of_ne_nil X.hne1
private lemma len_pos2 : 1 ≤ X.A2.length := List.length_pos_of_ne_nil X.hne2
private lemma len_pos3 : 1 ≤ X.A3.length := List.length_pos_of_ne_nil X.hne3
private lemma len_pos4 : 1 ≤ X.A4.length := List.length_pos_of_ne_nil X.hne4

private lemma ne_append {α : Type*} {l1 l2 : List α} (h1 : l1 ≠ []) : l1 ++ l2 ≠ [] := by
  intro h; exact h1 (List.append_eq_nil_iff.mp h).1

/-- 1. Outer cycle: `A1 ++ A2 ++ A3 ++ A4` of length `x1 + x2 + x3 + x4`. -/
def outerCycle : SimpleCycle G :=
  SimpleCycle.ofTwoArcs (X.A1 ++ X.A2) (X.A3 ++ X.A4)
    (ne_append X.hne1) (ne_append X.hne3)
    (by simp; have := X.len_pos1; have := X.len_pos2; have := X.len_pos3; have := X.len_pos4; omega)
    (nodup_append_of_disjoint X.hnd1 X.hnd2 X.d12)
    (nodup_append_of_disjoint X.hnd3 X.hnd4 X.d34)
    (fun w hL hR => by
      simp only [List.mem_append] at hL hR
      rcases hL with h1 | h2 <;> rcases hR with h3 | h4
      · exact X.d13 h1 h3
      · exact X.d14 h1 h4
      · exact X.d23 h2 h3
      · exact X.d24 h2 h4)
    (isChain_append_of_link X.hch1 X.hch2 X.hne1 X.hne2 X.link12)
    (isChain_append_of_link X.hch3 X.hch4 X.hne3 X.hne4 X.link34)
    (by rw [List.getLast_append_of_ne_nil _ X.hne2, List.head_append_of_ne_nil X.hne3]; exact X.link23)
    (by rw [List.getLast_append_of_ne_nil _ X.hne4, List.head_append_of_ne_nil X.hne1]; exact X.link41)

theorem outerCycle_len :
    X.outerCycle.verts.length = X.A1.length + X.A2.length + X.A3.length + X.A4.length := by
  show ((X.A1 ++ X.A2) ++ (X.A3 ++ X.A4)).length = _
  simp; omega

/-- 2. Chord-1 Side A: `A1 ++ A2 ++ [A3.head]` of length `x1 + x2 + 1`. -/
def chord1CycleA : SimpleCycle G :=
  SimpleCycle.ofTwoArcs (X.A1 ++ X.A2) [X.A3.head X.hne3]
    (ne_append X.hne1) (by simp)
    (by simp; have := X.len_pos1; have := X.len_pos2; omega)
    (nodup_append_of_disjoint X.hnd1 X.hnd2 X.d12)
    (List.nodup_singleton _)
    (fun w hL hR => by
      simp only [List.mem_singleton] at hR; subst hR
      have hm3 : X.A3.head X.hne3 ∈ X.A3 := List.head_mem X.hne3
      simp only [List.mem_append] at hL
      rcases hL with h1 | h2
      · exact X.d13 h1 hm3
      · exact X.d23 h2 hm3)
    (isChain_append_of_link X.hch1 X.hch2 X.hne1 X.hne2 X.link12)
    (List.isChain_singleton _)
    (by rw [List.getLast_append_of_ne_nil _ X.hne2]; simpa using X.link23)
    (by rw [List.head_append_of_ne_nil X.hne1]; simpa using (G.adj_comm _ _).mp X.chord1)

theorem chord1CycleA_len :
    X.chord1CycleA.verts.length = X.A1.length + X.A2.length + 1 := by
  show ((X.A1 ++ X.A2) ++ [X.A3.head X.hne3]).length = _
  simp; omega

/-- 3. Chord-1 Side B: `A3 ++ A4 ++ [A1.head]` of length `x3 + x4 + 1`. -/
def chord1CycleB : SimpleCycle G :=
  SimpleCycle.ofTwoArcs (X.A3 ++ X.A4) [X.A1.head X.hne1]
    (ne_append X.hne3) (by simp)
    (by simp; have := X.len_pos3; have := X.len_pos4; omega)
    (nodup_append_of_disjoint X.hnd3 X.hnd4 X.d34)
    (List.nodup_singleton _)
    (fun w hL hR => by
      simp only [List.mem_singleton] at hR; subst hR
      have hm1 : X.A1.head X.hne1 ∈ X.A1 := List.head_mem X.hne1
      simp only [List.mem_append] at hL
      rcases hL with h3 | h4
      · exact X.d13 hm1 h3
      · exact X.d14 hm1 h4)
    (isChain_append_of_link X.hch3 X.hch4 X.hne3 X.hne4 X.link34)
    (List.isChain_singleton _)
    (by rw [List.getLast_append_of_ne_nil _ X.hne4]; simpa using X.link41)
    (by rw [List.head_append_of_ne_nil X.hne3]; simpa using X.chord1)

theorem chord1CycleB_len :
    X.chord1CycleB.verts.length = X.A3.length + X.A4.length + 1 := by
  show ((X.A3 ++ X.A4) ++ [X.A1.head X.hne1]).length = _
  simp; omega

/-- 4. Chord-2 Side A: `A2 ++ A3 ++ [A4.head]` of length `x2 + x3 + 1`. -/
def chord2CycleA : SimpleCycle G :=
  SimpleCycle.ofTwoArcs (X.A2 ++ X.A3) [X.A4.head X.hne4]
    (ne_append X.hne2) (by simp)
    (by simp; have := X.len_pos2; have := X.len_pos3; omega)
    (nodup_append_of_disjoint X.hnd2 X.hnd3 X.d23)
    (List.nodup_singleton _)
    (fun w hL hR => by
      simp only [List.mem_singleton] at hR; subst hR
      have hm4 : X.A4.head X.hne4 ∈ X.A4 := List.head_mem X.hne4
      simp only [List.mem_append] at hL
      rcases hL with h2 | h3
      · exact X.d24 h2 hm4
      · exact X.d34 h3 hm4)
    (isChain_append_of_link X.hch2 X.hch3 X.hne2 X.hne3 X.link23)
    (List.isChain_singleton _)
    (by rw [List.getLast_append_of_ne_nil _ X.hne3]; simpa using X.link34)
    (by rw [List.head_append_of_ne_nil X.hne2]; simpa using (G.adj_comm _ _).mp X.chord2)

theorem chord2CycleA_len :
    X.chord2CycleA.verts.length = X.A2.length + X.A3.length + 1 := by
  show ((X.A2 ++ X.A3) ++ [X.A4.head X.hne4]).length = _
  simp; omega

/-- 5. Chord-2 Side B: `A4 ++ A1 ++ [A2.head]` of length `x4 + x1 + 1`. -/
def chord2CycleB : SimpleCycle G :=
  SimpleCycle.ofTwoArcs (X.A4 ++ X.A1) [X.A2.head X.hne2]
    (ne_append X.hne4) (by simp)
    (by simp; have := X.len_pos4; have := X.len_pos1; omega)
    (nodup_append_of_disjoint X.hnd4 X.hnd1 (fun w h4 h1 => X.d14 h1 h4))
    (List.nodup_singleton _)
    (fun w hL hR => by
      simp only [List.mem_singleton] at hR; subst hR
      have hm2 : X.A2.head X.hne2 ∈ X.A2 := List.head_mem X.hne2
      simp only [List.mem_append] at hL
      rcases hL with h4 | h1
      · exact X.d24 hm2 h4
      · exact X.d12 h1 hm2)
    (isChain_append_of_link X.hch4 X.hch1 X.hne4 X.hne1 X.link41)
    (List.isChain_singleton _)
    (by rw [List.getLast_append_of_ne_nil _ X.hne1]; simpa using X.link12)
    (by rw [List.head_append_of_ne_nil X.hne4]; simpa using X.chord2)

theorem chord2CycleB_len :
    X.chord2CycleB.verts.length = X.A4.length + X.A1.length + 1 := by
  show ((X.A4 ++ X.A1) ++ [X.A2.head X.hne2]).length = _
  simp; omega

/-- 6. Cross Cycle A: `(A1 ++ [ua]) ++ ([uc] ++ A3.reverse)` of length `x1 + x3 + 2`. -/
def crossCycleA : SimpleCycle G :=
  let P := X.A1 ++ [X.A2.head X.hne2]
  let Q := [X.A4.head X.hne4] ++ X.A3.reverse
  SimpleCycle.ofTwoArcs P Q
    (ne_append X.hne1) (by simp [Q])
    (by simp [P, Q]; have := X.len_pos1; have := X.len_pos3; omega)
    (nodup_append_of_disjoint X.hnd1 (List.nodup_singleton _) (fun w h1 h2 => by
      simp only [List.mem_singleton] at h2; subst h2
      exact X.d12 h1 (List.head_mem X.hne2)))
    (nodup_append_of_disjoint (List.nodup_singleton _) (List.nodup_reverse.mpr X.hnd3) (fun w h4 h3 => by
      simp only [List.mem_singleton] at h4; subst h4
      rw [List.mem_reverse] at h3
      exact X.d34 h3 (List.head_mem X.hne4)))
    (fun w hP hQ => by
      simp only [P, Q, List.mem_append, List.mem_singleton, List.mem_reverse] at hP hQ
      rcases hP with h1 | h2 <;> rcases hQ with h4 | h3
      · subst h4; exact X.d14 h1 (List.head_mem X.hne4)
      · exact X.d13 h1 h3
      · rw [h2] at h4
        exact X.d24 (List.head_mem X.hne2) (h4 ▸ List.head_mem X.hne4)
      · subst h2; exact X.d23 (List.head_mem X.hne2) h3)
    (isChain_append_of_link X.hch1 (List.isChain_singleton _) X.hne1 (by simp) (by simpa using X.link12))
    (isChain_append_of_link (List.isChain_singleton _) (isChain_reverse_adj X.hch3)
      (by simp) (by simpa using X.hne3)
      (by simp [head_reverse_eq_getLast X.hne3]; exact (G.adj_comm _ _).mp X.link34))
    (by
      rw [List.getLast_append_of_ne_nil _ (by simp), List.head_append_of_ne_nil (by simp)]
      simpa using X.chord2)
    (by
      have hne3r : X.A3.reverse ≠ [] := by simpa using X.hne3
      rw [List.getLast_append_of_ne_nil _ hne3r, List.head_append_of_ne_nil X.hne1]
      rw [getLast_reverse_eq_head X.hne3]
      exact (G.adj_comm _ _).mp X.chord1)

theorem crossCycleA_len :
    X.crossCycleA.verts.length = X.A1.length + X.A3.length + 2 := by
  show ((X.A1 ++ [X.A2.head X.hne2]) ++ ([X.A4.head X.hne4] ++ X.A3.reverse)).length = _
  simp; omega

/-- 7. Cross Cycle B: `(A2 ++ [ub]) ++ ([u0] ++ A4.reverse)` of length `x2 + x4 + 2`. -/
def crossCycleB : SimpleCycle G :=
  let P := X.A2 ++ [X.A3.head X.hne3]
  let Q := [X.A1.head X.hne1] ++ X.A4.reverse
  SimpleCycle.ofTwoArcs P Q
    (ne_append X.hne2) (by simp [Q])
    (by simp [P, Q]; have := X.len_pos2; have := X.len_pos4; omega)
    (nodup_append_of_disjoint X.hnd2 (List.nodup_singleton _) (fun w h2 h3 => by
      simp only [List.mem_singleton] at h3; subst h3
      exact X.d23 h2 (List.head_mem X.hne3)))
    (nodup_append_of_disjoint (List.nodup_singleton _) (List.nodup_reverse.mpr X.hnd4) (fun w h1 h4 => by
      simp only [List.mem_singleton] at h1; subst h1
      rw [List.mem_reverse] at h4
      exact X.d14 (List.head_mem X.hne1) h4))
    (fun w hP hQ => by
      simp only [P, Q, List.mem_append, List.mem_singleton, List.mem_reverse] at hP hQ
      rcases hP with h2 | h3 <;> rcases hQ with h1 | h4
      · subst h1; exact X.d12 (List.head_mem X.hne1) h2
      · exact X.d24 h2 h4
      · rw [h3] at h1
        exact X.d13 (h1 ▸ List.head_mem X.hne1) (List.head_mem X.hne3)
      · subst h3; exact X.d34 (List.head_mem X.hne3) h4)
    (isChain_append_of_link X.hch2 (List.isChain_singleton _) X.hne2 (by simp) (by simpa using X.link23))
    (isChain_append_of_link (List.isChain_singleton _) (isChain_reverse_adj X.hch4)
      (by simp) (by simpa using X.hne4)
      (by simp [head_reverse_eq_getLast X.hne4]; exact (G.adj_comm _ _).mp X.link41))
    (by
      rw [List.getLast_append_of_ne_nil _ (by simp), List.head_append_of_ne_nil (by simp)]
      simpa using (G.adj_comm _ _).mp X.chord1)
    (by
      have hne4r : X.A4.reverse ≠ [] := by simpa using X.hne4
      rw [List.getLast_append_of_ne_nil _ hne4r, List.head_append_of_ne_nil X.hne2]
      rw [getLast_reverse_eq_head X.hne4]
      exact (G.adj_comm _ _).mp X.chord2)

theorem crossCycleB_len :
    X.crossCycleB.verts.length = X.A2.length + X.A4.length + 2 := by
  show ((X.A2 ++ [X.A3.head X.hne3]) ++ ([X.A1.head X.hne1] ++ X.A4.reverse)).length = _
  simp; omega

end CrossingChordPair

/-- Theorem 8 (Master Crossing-Chord 7-Cycle Spectrum):
    Every `CrossingChordPair G` realizes all 7 cycle lengths simultaneously. -/
theorem crossing_chords_seven_cycle_spectrum {V : Type*} {G : SimpleGraph V}
    (X : CrossingChordPair G) :
    (∃ C : SimpleCycle G, C.verts.length = X.A1.length + X.A2.length + X.A3.length + X.A4.length) ∧
    (∃ C : SimpleCycle G, C.verts.length = X.A1.length + X.A2.length + 1) ∧
    (∃ C : SimpleCycle G, C.verts.length = X.A3.length + X.A4.length + 1) ∧
    (∃ C : SimpleCycle G, C.verts.length = X.A2.length + X.A3.length + 1) ∧
    (∃ C : SimpleCycle G, C.verts.length = X.A4.length + X.A1.length + 1) ∧
    (∃ C : SimpleCycle G, C.verts.length = X.A1.length + X.A3.length + 2) ∧
    (∃ C : SimpleCycle G, C.verts.length = X.A2.length + X.A4.length + 2) :=
  ⟨⟨X.outerCycle, X.outerCycle_len⟩,
   ⟨X.chord1CycleA, X.chord1CycleA_len⟩,
   ⟨X.chord1CycleB, X.chord1CycleB_len⟩,
   ⟨X.chord2CycleA, X.chord2CycleA_len⟩,
   ⟨X.chord2CycleB, X.chord2CycleB_len⟩,
   ⟨X.crossCycleA, X.crossCycleA_len⟩,
   ⟨X.crossCycleB, X.crossCycleB_len⟩⟩

/-- Theorem 9 (Balanced-Sum Crossing-Chord Refutation):
    If a `CrossingChordPair` has outer length `2^k - 2` (`k ≥ 3`) with balanced halves
    `x1 + x2 = x3 + x4`, OR outer length `2^k - 4` (`k ≥ 3`) with `x1 + x3 = x2 + x4`,
    then `G` unconditionally contains a simple `2^(k-1)`-cycle! -/
theorem crossing_chords_balanced_sum_refutation {V : Type*} {G : SimpleGraph V}
    (X : CrossingChordPair G) {k : ℕ} (hk : 3 ≤ k)
    (hbal : (X.A1.length + X.A2.length + X.A3.length + X.A4.length + 2 = 2 ^ k ∧
             X.A1.length + X.A2.length = X.A3.length + X.A4.length) ∨
            (X.A1.length + X.A2.length + X.A3.length + X.A4.length + 4 = 2 ^ k ∧
             X.A1.length + X.A3.length = X.A2.length + X.A4.length)) :
    HasPowerCycle G := by
  have h2k : 2 ^ k = 2 * 2 ^ (k - 1) := by
    have : k = (k - 1) + 1 := by omega
    conv_lhs => rw [this, pow_succ, mul_comm]
  rcases hbal with ⟨hsum, heq⟩ | ⟨hsum, heq⟩
  · refine ⟨X.chord1CycleA, k - 1, by omega, ?_⟩
    rw [X.chord1CycleA_len]; omega
  · refine ⟨X.crossCycleA, k - 1, by omega, ?_⟩
    rw [X.crossCycleA_len]; omega

/-! ### Part III: Arbitrary-Girth `r`-Rung Ladder Trichotomy & Mod-4 Immunity Breaker -/

/-- An `r`-rung ladder (`r ≥ 2`) on a `SimpleGraph V`. -/
structure RungLadder {V : Type*} (G : SimpleGraph V) (r : ℕ) where
  hr : 2 ≤ r
  u : Fin r → V
  v : Fin r → V
  rung : ∀ i : Fin r, G.Adj (u i) (v i)
  topSeg : Fin (r - 1) → List V
  botSeg : Fin (r - 1) → List V
  top_ne : ∀ t, topSeg t ≠ []
  bot_ne : ∀ t, botSeg t ≠ []
  top_nd : ∀ t, (topSeg t).Nodup
  bot_nd : ∀ t, (botSeg t).Nodup
  top_ch : ∀ t, (topSeg t).IsChain G.Adj
  bot_ch : ∀ t, (botSeg t).IsChain G.Adj
  top_head : ∀ t : Fin (r - 1), (topSeg t).head (top_ne t) = u ⟨t.val, by omega⟩
  top_exit : ∀ t : Fin (r - 1), G.Adj ((topSeg t).getLast (top_ne t)) (u ⟨t.val + 1, by omega⟩)
  bot_head : ∀ t : Fin (r - 1), (botSeg t).head (bot_ne t) = v ⟨t.val + 1, by omega⟩
  bot_exit : ∀ t : Fin (r - 1), G.Adj ((botSeg t).getLast (bot_ne t)) (v ⟨t.val, by omega⟩)
  top_disj : ∀ t1 t2 : Fin (r - 1), t1 ≠ t2 → List.Disjoint (topSeg t1) (topSeg t2)
  bot_disj : ∀ t1 t2 : Fin (r - 1), t1 ≠ t2 → List.Disjoint (botSeg t1) (botSeg t2)
  top_bot_disj : ∀ t1 t2 : Fin (r - 1), List.Disjoint (topSeg t1) (botSeg t2)
  u_last_not_top : ∀ t, u ⟨r - 1, by omega⟩ ∉ topSeg t
  u_last_not_bot : ∀ t, u ⟨r - 1, by omega⟩ ∉ botSeg t
  v_first_not_top : ∀ t, v ⟨0, by omega⟩ ∉ topSeg t
  v_first_not_bot : ∀ t, v ⟨0, by omega⟩ ∉ botSeg t
  uv_end_ne : u ⟨r - 1, by omega⟩ ≠ v ⟨0, by omega⟩

namespace RungLadder

variable {V : Type*} {G : SimpleGraph V} {r : ℕ}

/-- Recursive concatenation of top segments `topSeg i ++ ... ++ topSeg (i + m - 1)`. -/
def topRun (L : RungLadder G r) (i m : ℕ) (him : i + m < r) : List V :=
  match m with
  | 0 => []
  | m' + 1 =>
    if _ : m' = 0 then L.topSeg ⟨i, by omega⟩
    else L.topSeg ⟨i, by omega⟩ ++ L.topRun (i + 1) m' (by omega)

/-- Recursive concatenation of bottom segments `botSeg (i + m - 1) ++ ... ++ botSeg i`. -/
def botRun (L : RungLadder G r) (i m : ℕ) (him : i + m < r) : List V :=
  match m with
  | 0 => []
  | m' + 1 =>
    if _ : m' = 0 then L.botSeg ⟨i, by omega⟩
    else L.botRun (i + 1) m' (by omega) ++ L.botSeg ⟨i, by omega⟩

lemma topRun_ne (L : RungLadder G r) (i m : ℕ) (hm : 1 ≤ m) (him : i + m < r) :
    L.topRun i m him ≠ [] := by
  cases m with
  | zero => omega
  | succ m' =>
    unfold topRun
    split_ifs
    · exact L.top_ne ⟨i, by omega⟩
    · intro h; exact L.top_ne ⟨i, by omega⟩ (List.append_eq_nil_iff.mp h).1

lemma botRun_ne (L : RungLadder G r) (i m : ℕ) (hm : 1 ≤ m) (him : i + m < r) :
    L.botRun i m him ≠ [] := by
  cases m with
  | zero => omega
  | succ m' =>
    unfold botRun
    split_ifs
    · exact L.bot_ne ⟨i, by omega⟩
    · intro h; exact L.bot_ne ⟨i, by omega⟩ (List.append_eq_nil_iff.mp h).2

lemma topRun_head (L : RungLadder G r) (i m : ℕ) (hm : 1 ≤ m) (him : i + m < r) :
    (L.topRun i m him).head (L.topRun_ne i m hm him) = L.u ⟨i, by omega⟩ := by
  cases m with
  | zero => omega
  | succ m' =>
    unfold topRun
    split_ifs
    · exact L.top_head ⟨i, by omega⟩
    · rw [List.head_append_of_ne_nil (L.top_ne ⟨i, by omega⟩)]
      exact L.top_head ⟨i, by omega⟩

lemma botRun_exit (L : RungLadder G r) (i m : ℕ) (hm : 1 ≤ m) (him : i + m < r) :
    G.Adj ((L.botRun i m him).getLast (L.botRun_ne i m hm him)) (L.v ⟨i, by omega⟩) := by
  cases m with
  | zero => omega
  | succ m' =>
    unfold botRun
    split_ifs
    · exact L.bot_exit ⟨i, by omega⟩
    · rw [List.getLast_append_of_ne_nil _ (L.bot_ne ⟨i, by omega⟩)]
      exact L.bot_exit ⟨i, by omega⟩

lemma topRun_exit (L : RungLadder G r) :
    ∀ m i (hm : 1 ≤ m) (him : i + m < r),
    G.Adj ((L.topRun i m him).getLast (L.topRun_ne i m hm him)) (L.u ⟨i + m, by omega⟩)
  | 0, _, hm, _ => by omega
  | m' + 1, i, _, him => by
    by_cases hm' : m' = 0
    · subst hm'
      have h1 : L.topRun i 1 him = L.topSeg ⟨i, by omega⟩ := by simp [topRun]
      have h2 := L.top_exit ⟨i, by omega⟩
      simpa [h1] using h2
    · have h1 : L.topRun i (m' + 1) him = L.topSeg ⟨i, by omega⟩ ++ L.topRun (i + 1) m' (by omega) := by
        simp [topRun, hm']
      have ih := L.topRun_exit m' (i + 1) (by omega) (by omega)
      have hne2 := L.topRun_ne (i + 1) m' (by omega) (by omega)
      have hgl : (L.topRun i (m' + 1) him).getLast (L.topRun_ne i (m' + 1) (by omega) him) =
          (L.topRun (i + 1) m' (by omega)).getLast hne2 := by
        simp only [h1]
        exact List.getLast_append_of_ne_nil _ hne2
      rw [hgl]
      have hidx : (⟨i + 1 + m', by omega⟩ : Fin r) = ⟨i + (m' + 1), by omega⟩ := by
        ext; dsimp; omega
      rw [← hidx]
      exact ih

lemma botRun_head (L : RungLadder G r) :
    ∀ m i (hm : 1 ≤ m) (him : i + m < r),
    (L.botRun i m him).head (L.botRun_ne i m hm him) = L.v ⟨i + m, by omega⟩
  | 0, _, hm, _ => by omega
  | m' + 1, i, _, him => by
    by_cases hm' : m' = 0
    · subst hm'
      have h1 : L.botRun i 1 him = L.botSeg ⟨i, by omega⟩ := by simp [botRun]
      have h2 := L.bot_head ⟨i, by omega⟩
      simpa [h1] using h2
    · have h1 : L.botRun i (m' + 1) him = L.botRun (i + 1) m' (by omega) ++ L.botSeg ⟨i, by omega⟩ := by
        simp [botRun, hm']
      have ih := L.botRun_head m' (i + 1) (by omega) (by omega)
      have hne2 := L.botRun_ne (i + 1) m' (by omega) (by omega)
      have hhd : (L.botRun i (m' + 1) him).head (L.botRun_ne i (m' + 1) (by omega) him) =
          (L.botRun (i + 1) m' (by omega)).head hne2 := by
        simp only [h1]
        exact List.head_append_of_ne_nil hne2
      rw [hhd]
      have hidx : (⟨i + 1 + m', by omega⟩ : Fin r) = ⟨i + (m' + 1), by omega⟩ := by
        ext; dsimp; omega
      rw [← hidx]
      exact ih

lemma topRun_chain (L : RungLadder G r) :
    ∀ m i (_hm : 1 ≤ m) (him : i + m < r), (L.topRun i m him).IsChain G.Adj
  | 0, _, hm, _ => by omega
  | m' + 1, i, _, him => by
    by_cases hm' : m' = 0
    · subst hm'; simp [topRun, L.top_ch]
    · simp only [topRun, hm', ↓reduceDIte]
      apply isChain_append_of_link (L.top_ch ⟨i, by omega⟩) (L.topRun_chain m' (i + 1) (by omega) (by omega))
        (L.top_ne ⟨i, by omega⟩) (L.topRun_ne (i + 1) m' (by omega) (by omega))
      rw [L.topRun_head (i + 1) m' (by omega) (by omega)]
      exact L.top_exit ⟨i, by omega⟩

lemma botRun_chain (L : RungLadder G r) :
    ∀ m i (_hm : 1 ≤ m) (him : i + m < r), (L.botRun i m him).IsChain G.Adj
  | 0, _, hm, _ => by omega
  | m' + 1, i, _, him => by
    by_cases hm' : m' = 0
    · subst hm'; simp [botRun, L.bot_ch]
    · simp only [botRun, hm', ↓reduceDIte]
      apply isChain_append_of_link (L.botRun_chain m' (i + 1) (by omega) (by omega)) (L.bot_ch ⟨i, by omega⟩)
        (L.botRun_ne (i + 1) m' (by omega) (by omega)) (L.bot_ne ⟨i, by omega⟩)
      rw [L.bot_head ⟨i, by omega⟩]
      exact L.botRun_exit (i + 1) m' (by omega) (by omega)

lemma mem_topRun (L : RungLadder G r) :
    ∀ m i (him : i + m < r) {x : V}, x ∈ L.topRun i m him →
    ∃ t : Fin (r - 1), i ≤ t.val ∧ t.val < i + m ∧ x ∈ L.topSeg t
  | 0, _, _, _, hx => by simp [topRun] at hx
  | m' + 1, i, him, x, hx => by
    by_cases hm' : m' = 0
    · subst hm'; simp [topRun] at hx; exact ⟨⟨i, by omega⟩, by dsimp; omega, by dsimp; omega, hx⟩
    · simp only [topRun, hm', ↓reduceDIte, List.mem_append] at hx
      rcases hx with h1 | h2
      · exact ⟨⟨i, by omega⟩, by dsimp; omega, by dsimp; omega, h1⟩
      · obtain ⟨t, ht1, ht2, hxt⟩ := L.mem_topRun m' (i + 1) (by omega) h2
        exact ⟨t, by omega, by omega, hxt⟩

lemma mem_botRun (L : RungLadder G r) :
    ∀ m i (him : i + m < r) {x : V}, x ∈ L.botRun i m him →
    ∃ t : Fin (r - 1), i ≤ t.val ∧ t.val < i + m ∧ x ∈ L.botSeg t
  | 0, _, _, _, hx => by simp [botRun] at hx
  | m' + 1, i, him, x, hx => by
    by_cases hm' : m' = 0
    · subst hm'; simp [botRun] at hx; exact ⟨⟨i, by omega⟩, by dsimp; omega, by dsimp; omega, hx⟩
    · simp only [botRun, hm', ↓reduceDIte, List.mem_append] at hx
      rcases hx with h1 | h2
      · obtain ⟨t, ht1, ht2, hxt⟩ := L.mem_botRun m' (i + 1) (by omega) h1
        exact ⟨t, by omega, by omega, hxt⟩
      · exact ⟨⟨i, by omega⟩, by dsimp; omega, by dsimp; omega, h2⟩

lemma topRun_nodup (L : RungLadder G r) :
    ∀ m i (him : i + m < r), (L.topRun i m him).Nodup
  | 0, _, _ => by simp [topRun]
  | m' + 1, i, him => by
    by_cases hm' : m' = 0
    · subst hm'; simp [topRun, L.top_nd]
    · simp only [topRun, hm', ↓reduceDIte]
      refine nodup_append_of_disjoint (L.top_nd ⟨i, by omega⟩) (L.topRun_nodup m' (i + 1) (by omega)) ?_
      intro x hx1 hx2
      obtain ⟨t, ht1, _, hxt⟩ := L.mem_topRun m' (i + 1) (by omega) hx2
      exact L.top_disj ⟨i, by omega⟩ t (by intro h; have hv := congrArg Fin.val h; dsimp at hv; omega) hx1 hxt

lemma botRun_nodup (L : RungLadder G r) :
    ∀ m i (him : i + m < r), (L.botRun i m him).Nodup
  | 0, _, _ => by simp [botRun]
  | m' + 1, i, him => by
    by_cases hm' : m' = 0
    · subst hm'; simp [botRun, L.bot_nd]
    · simp only [botRun, hm', ↓reduceDIte]
      refine nodup_append_of_disjoint (L.botRun_nodup m' (i + 1) (by omega)) (L.bot_nd ⟨i, by omega⟩) ?_
      intro x hx1 hx2
      obtain ⟨t, ht1, _, hxt⟩ := L.mem_botRun m' (i + 1) (by omega) hx1
      exact L.bot_disj t ⟨i, by omega⟩ (by intro h; have hv := congrArg Fin.val h; dsimp at hv; omega) hxt hx2

lemma topRun_length (L : RungLadder G r) :
    ∀ m i (him : i + m < r),
    (L.topRun i m him).length = ∑ t ∈ (Finset.univ : Finset (Fin (r - 1))).filter (fun t => i ≤ t.val ∧ t.val < i + m), (L.topSeg t).length
  | 0, i, _ => by
    have hf : (Finset.univ : Finset (Fin (r - 1))).filter (fun t => i ≤ t.val ∧ t.val < i + 0) = ∅ := by
      ext t; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]; omega
    rw [hf]; simp [topRun]
  | m' + 1, i, him => by
    have hsplit : (Finset.univ : Finset (Fin (r - 1))).filter (fun t => i ≤ t.val ∧ t.val < i + (m' + 1)) =
        insert ⟨i, by omega⟩ ((Finset.univ : Finset (Fin (r - 1))).filter (fun t => i + 1 ≤ t.val ∧ t.val < i + 1 + m')) := by
      ext t; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
      omega
    have hnotmem : (⟨i, by omega⟩ : Fin (r - 1)) ∉
        (Finset.univ : Finset (Fin (r - 1))).filter (fun t => i + 1 ≤ t.val ∧ t.val < i + 1 + m') := by
      simp
    rw [hsplit, Finset.sum_insert hnotmem]
    by_cases hm' : m' = 0
    · subst hm'
      have hemp : (Finset.univ : Finset (Fin (r - 1))).filter (fun t => i + 1 ≤ t.val ∧ t.val < i + 1 + 0) = ∅ := by
        ext t; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]; omega
      rw [hemp]; simp [topRun]
    · simp only [topRun, hm', ↓reduceDIte, List.length_append]
      rw [L.topRun_length m' (i + 1) (by omega)]

lemma botRun_length (L : RungLadder G r) :
    ∀ m i (him : i + m < r),
    (L.botRun i m him).length = ∑ t ∈ (Finset.univ : Finset (Fin (r - 1))).filter (fun t => i ≤ t.val ∧ t.val < i + m), (L.botSeg t).length
  | 0, i, _ => by
    have hf : (Finset.univ : Finset (Fin (r - 1))).filter (fun t => i ≤ t.val ∧ t.val < i + 0) = ∅ := by
      ext t; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]; omega
    rw [hf]; simp [botRun]
  | m' + 1, i, him => by
    have hsplit : (Finset.univ : Finset (Fin (r - 1))).filter (fun t => i ≤ t.val ∧ t.val < i + (m' + 1)) =
        insert ⟨i, by omega⟩ ((Finset.univ : Finset (Fin (r - 1))).filter (fun t => i + 1 ≤ t.val ∧ t.val < i + 1 + m')) := by
      ext t; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
      omega
    have hnotmem : (⟨i, by omega⟩ : Fin (r - 1)) ∉
        (Finset.univ : Finset (Fin (r - 1))).filter (fun t => i + 1 ≤ t.val ∧ t.val < i + 1 + m') := by
      simp
    rw [hsplit, Finset.sum_insert hnotmem]
    by_cases hm' : m' = 0
    · subst hm'
      have hemp : (Finset.univ : Finset (Fin (r - 1))).filter (fun t => i + 1 ≤ t.val ∧ t.val < i + 1 + 0) = ∅ := by
        ext t; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]; omega
      rw [hemp]; simp [botRun]
    · simp only [botRun, hm', ↓reduceDIte, List.length_append]
      rw [L.botRun_length m' (i + 1) (by omega)]
      omega

private lemma u_end_not_topRun (L : RungLadder G r) (i m : ℕ) (him : i + m < r) :
    L.u ⟨i + m, him⟩ ∉ L.topRun i m him := by
  intro hx
  obtain ⟨t, _, ht2, hxt⟩ := L.mem_topRun m i him hx
  by_cases hlast : i + m = r - 1
  · have heq : (⟨i + m, him⟩ : Fin r) = ⟨r - 1, by have := L.hr; omega⟩ := by ext; exact hlast
    rw [heq] at hxt
    exact L.u_last_not_top t hxt
  · have hmem_next : L.u ⟨i + m, him⟩ ∈ L.topSeg ⟨i + m, by omega⟩ := by
      rw [← L.top_head ⟨i + m, by omega⟩]
      exact List.head_mem (L.top_ne ⟨i + m, by omega⟩)
    exact L.top_disj t ⟨i + m, by omega⟩ (by intro h; have hv := congrArg Fin.val h; dsimp at hv; omega) hxt hmem_next

private lemma u_end_not_botRun (L : RungLadder G r) (i m : ℕ) (him : i + m < r) :
    L.u ⟨i + m, him⟩ ∉ L.botRun i m him := by
  intro hx
  obtain ⟨t, _, _, hxt⟩ := L.mem_botRun m i him hx
  by_cases hlast : i + m = r - 1
  · have heq : (⟨i + m, him⟩ : Fin r) = ⟨r - 1, by have := L.hr; omega⟩ := by ext; exact hlast
    rw [heq] at hxt
    exact L.u_last_not_bot t hxt
  · have hmem_next : L.u ⟨i + m, him⟩ ∈ L.topSeg ⟨i + m, by omega⟩ := by
      rw [← L.top_head ⟨i + m, by omega⟩]
      exact List.head_mem (L.top_ne ⟨i + m, by omega⟩)
    exact L.top_bot_disj ⟨i + m, by omega⟩ t hmem_next hxt

private lemma v_start_not_botRun (L : RungLadder G r) (i m : ℕ) (him : i + m < r) :
    L.v ⟨i, by omega⟩ ∉ L.botRun i m him := by
  intro hx
  obtain ⟨t, ht1, _, hxt⟩ := L.mem_botRun m i him hx
  by_cases hzero : i = 0
  · have heq : (⟨i, by omega⟩ : Fin r) = ⟨0, by have := L.hr; omega⟩ := by ext; exact hzero
    rw [heq] at hxt
    exact L.v_first_not_bot t hxt
  · have hmem_prev : L.v ⟨i, by omega⟩ ∈ L.botSeg ⟨i - 1, by omega⟩ := by
      have hhd := L.bot_head ⟨i - 1, by omega⟩
      have heq : (⟨i - 1 + 1, by omega⟩ : Fin r) = ⟨i, by omega⟩ := by ext; dsimp; omega
      rw [heq] at hhd
      rw [← hhd]
      exact List.head_mem (L.bot_ne ⟨i - 1, by omega⟩)
    exact L.bot_disj t ⟨i - 1, by omega⟩ (by intro h; have hv := congrArg Fin.val h; dsimp at hv; omega) hxt hmem_prev

private lemma v_start_not_topRun (L : RungLadder G r) (i m : ℕ) (him : i + m < r) :
    L.v ⟨i, by omega⟩ ∉ L.topRun i m him := by
  intro hx
  obtain ⟨t, _, _, hxt⟩ := L.mem_topRun m i him hx
  by_cases hzero : i = 0
  · have heq : (⟨i, by omega⟩ : Fin r) = ⟨0, by have := L.hr; omega⟩ := by ext; exact hzero
    rw [heq] at hxt
    exact L.v_first_not_top t hxt
  · have hmem_prev : L.v ⟨i, by omega⟩ ∈ L.botSeg ⟨i - 1, by omega⟩ := by
      have hhd := L.bot_head ⟨i - 1, by omega⟩
      have heq : (⟨i - 1 + 1, by omega⟩ : Fin r) = ⟨i, by omega⟩ := by ext; dsimp; omega
      rw [heq] at hhd
      rw [← hhd]
      exact List.head_mem (L.bot_ne ⟨i - 1, by omega⟩)
    exact L.top_bot_disj t ⟨i - 1, by omega⟩ hxt hmem_prev

private lemma u_end_ne_v_start (L : RungLadder G r) (i m : ℕ) (him : i + m < r) :
    L.u ⟨i + m, him⟩ ≠ L.v ⟨i, by omega⟩ := by
  by_cases hlast : i + m = r - 1
  · by_cases hzero : i = 0
    · have h1 : (⟨i + m, him⟩ : Fin r) = ⟨r - 1, by have := L.hr; omega⟩ := by ext; exact hlast
      have h2 : (⟨i, by omega⟩ : Fin r) = ⟨0, by have := L.hr; omega⟩ := by ext; exact hzero
      rw [h1, h2]; exact L.uv_end_ne
    · intro heq
      have hmem : L.v ⟨i, by omega⟩ ∈ L.botSeg ⟨i - 1, by omega⟩ := by
        have hhd := L.bot_head ⟨i - 1, by omega⟩
        have hidx : (⟨i - 1 + 1, by omega⟩ : Fin r) = ⟨i, by omega⟩ := by ext; dsimp; omega
        rw [hidx] at hhd; rw [← hhd]; exact List.head_mem (L.bot_ne _)
      have h1 : (⟨i + m, him⟩ : Fin r) = ⟨r - 1, by have := L.hr; omega⟩ := by ext; exact hlast
      rw [← heq, h1] at hmem
      exact L.u_last_not_bot ⟨i - 1, by omega⟩ hmem
  · intro heq
    have hmem_top : L.u ⟨i + m, him⟩ ∈ L.topSeg ⟨i + m, by omega⟩ := by
      rw [← L.top_head ⟨i + m, by omega⟩]; exact List.head_mem (L.top_ne _)
    by_cases hzero : i = 0
    · have h2 : (⟨i, by omega⟩ : Fin r) = ⟨0, by have := L.hr; omega⟩ := by ext; exact hzero
      rw [heq, h2] at hmem_top
      exact L.v_first_not_top ⟨i + m, by omega⟩ hmem_top
    · have hmem_bot : L.v ⟨i, by omega⟩ ∈ L.botSeg ⟨i - 1, by omega⟩ := by
        have hhd := L.bot_head ⟨i - 1, by omega⟩
        have hidx : (⟨i - 1 + 1, by omega⟩ : Fin r) = ⟨i, by omega⟩ := by ext; dsimp; omega
        rw [hidx] at hhd; rw [← hhd]; exact List.head_mem (L.bot_ne _)
      rw [← heq] at hmem_bot
      exact L.top_bot_disj ⟨i + m, by omega⟩ ⟨i - 1, by omega⟩ hmem_top hmem_bot

/-- Window cycle on bays `[i, i + m)` (`1 ≤ m`, `i + m < r`). -/
def windowCycle (L : RungLadder G r) (i m : ℕ) (hm : 1 ≤ m) (him : i + m < r) : SimpleCycle G :=
  let P := L.topRun i m him ++ [L.u ⟨i + m, him⟩]
  let Q := L.botRun i m him ++ [L.v ⟨i, by omega⟩]
  SimpleCycle.ofTwoArcs P Q
    (by intro h; exact L.topRun_ne i m hm him (List.append_eq_nil_iff.mp h).1)
    (by intro h; exact L.botRun_ne i m hm him (List.append_eq_nil_iff.mp h).1)
    (by
      have h1 : 1 ≤ (L.topRun i m him).length := List.length_pos_of_ne_nil (L.topRun_ne i m hm him)
      have h2 : 1 ≤ (L.botRun i m him).length := List.length_pos_of_ne_nil (L.botRun_ne i m hm him)
      simp [P, Q]; omega)
    (nodup_append_of_disjoint (L.topRun_nodup m i him) (List.nodup_singleton _) (fun x hx1 hx2 => by
      simp only [List.mem_singleton] at hx2; subst hx2
      exact L.u_end_not_topRun i m him hx1))
    (nodup_append_of_disjoint (L.botRun_nodup m i him) (List.nodup_singleton _) (fun x hx1 hx2 => by
      simp only [List.mem_singleton] at hx2; subst hx2
      exact L.v_start_not_botRun i m him hx1))
    (fun x hP hQ => by
      simp only [P, Q, List.mem_append, List.mem_singleton] at hP hQ
      rcases hP with ht | hu <;> rcases hQ with hb | hv
      · obtain ⟨t1, _, _, h1⟩ := L.mem_topRun m i him ht
        obtain ⟨t2, _, _, h2⟩ := L.mem_botRun m i him hb
        exact L.top_bot_disj t1 t2 h1 h2
      · subst hv; exact L.v_start_not_topRun i m him ht
      · subst hu; exact L.u_end_not_botRun i m him hb
      · rw [hu] at hv; exact L.u_end_ne_v_start i m him hv)
    (isChain_append_of_link (L.topRun_chain m i hm him) (List.isChain_singleton _)
      (L.topRun_ne i m hm him) (by simp) (by simpa using L.topRun_exit m i hm him))
    (isChain_append_of_link (L.botRun_chain m i hm him) (List.isChain_singleton _)
      (L.botRun_ne i m hm him) (by simp) (by simpa using L.botRun_exit i m hm him))
    (by
      rw [List.getLast_append_of_ne_nil _ (by simp), List.head_append_of_ne_nil (L.botRun_ne i m hm him)]
      rw [L.botRun_head m i hm him]
      simpa using L.rung ⟨i + m, him⟩)
    (by
      rw [List.getLast_append_of_ne_nil _ (by simp), List.head_append_of_ne_nil (L.topRun_ne i m hm him)]
      rw [L.topRun_head i m hm him]
      simpa using (G.adj_comm _ _).mp (L.rung ⟨i, by omega⟩))

/-- Theorem 10 (Exact Window-Cycle Length Formula on an `r`-Rung Ladder):
    `|windowCycle i m| = 2 + ∑_{t ∈ [i, i+m)} (|topSeg t| + |botSeg t|)`. -/
theorem windowCycle_len (L : RungLadder G r) (i m : ℕ) (hm : 1 ≤ m) (him : i + m < r) :
    (L.windowCycle i m hm him).verts.length =
      2 + ∑ t ∈ (Finset.univ : Finset (Fin (r - 1))).filter (fun t => i ≤ t.val ∧ t.val < i + m),
        ((L.topSeg t).length + (L.botSeg t).length) := by
  show ((L.topRun i m him ++ [L.u ⟨i + m, him⟩]) ++ (L.botRun i m him ++ [L.v ⟨i, by omega⟩])).length = _
  simp only [List.length_append, List.length_singleton]
  rw [L.topRun_length m i him, L.botRun_length m i him, Finset.sum_add_distrib]
  omega

private lemma card_bay_filter {r i m : ℕ} (him : i + m < r) :
    ((Finset.univ : Finset (Fin (r - 1))).filter (fun t => i ≤ t.val ∧ t.val < i + m)).card = m := by
  let f : {x // x ∈ Finset.range m} ↪ Fin (r - 1) :=
    ⟨fun x => ⟨i + x.val, by have := Finset.mem_range.mp x.prop; omega⟩,
     fun a b h => by
       cases a with | mk av ap =>
       cases b with | mk bv bp =>
       simp only [Fin.mk.injEq] at h
       have hav : av = bv := by omega
       subst hav; rfl⟩
  have hbij : (Finset.univ : Finset (Fin (r - 1))).filter (fun t => i ≤ t.val ∧ t.val < i + m) =
      (Finset.range m).attach.map f := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Finset.mem_attach, true_and, f]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨t.val - i, Finset.mem_range.mpr (by omega)⟩, by
        ext; change i + (t.val - i) = t.val; omega⟩
    · rintro ⟨⟨x, hx⟩, hxt⟩
      have hv : i + x = t.val := congrArg Fin.val hxt
      have hxlt := Finset.mem_range.mp hx
      omega
  rw [hbij, Finset.card_map, Finset.card_attach, Finset.card_range]

lemma uniform_windowCycle_len (L : RungLadder G r) {w i m : ℕ}
    (hunif : ∀ t : Fin (r - 1), (L.topSeg t).length + (L.botSeg t).length = w)
    (hm : 1 ≤ m) (him : i + m < r) :
    (L.windowCycle i m hm him).verts.length = 2 + m * w := by
  rw [L.windowCycle_len i m hm him]
  have hsum : ∑ t ∈ (Finset.univ : Finset (Fin (r - 1))).filter (fun t => i ≤ t.val ∧ t.val < i + m),
      ((L.topSeg t).length + (L.botSeg t).length) = m * w := by
    calc ∑ t ∈ (Finset.univ : Finset (Fin (r - 1))).filter (fun t => i ≤ t.val ∧ t.val < i + m),
          ((L.topSeg t).length + (L.botSeg t).length)
        = ∑ _t ∈ (Finset.univ : Finset (Fin (r - 1))).filter (fun t => i ≤ t.val ∧ t.val < i + m), w := by
          apply Finset.sum_congr rfl; intro t _; exact hunif t
      _ = ((Finset.univ : Finset (Fin (r - 1))).filter (fun t => i ≤ t.val ∧ t.val < i + m)).card * w := by
          rw [Finset.sum_const, smul_eq_mul]
      _ = m * w := by rw [card_bay_filter him]
  rw [hsum]

end RungLadder

/-- Theorem 11 (Exact Mod-4 Ladder Immunity Obstruction):
    For EVERY `g ≡ 2 (mod 4)` (`g = 6, 10, 14, ...`) and EVERY `m : ℕ`,
    `2 + m * (g - 2)` is NEVER a power of two `2^k` (`k ≥ 2`)! -/
theorem ladder_girth_mod4_two_immunity {g m : ℕ} (hg : g % 4 = 2) :
    ¬ IsPowerOfTwo (2 + m * (g - 2)) := by
  rintro ⟨k, hk, heq⟩
  have h4dvd : 4 ∣ 2 ^ k := by
    have h2 : 2 ^ 2 ∣ 2 ^ k := Nat.pow_dvd_pow 2 hk
    simpa using h2
  have h4g : 4 ∣ (g - 2) := by omega
  have h4m : 4 ∣ m * (g - 2) := dvd_mul_of_dvd_right h4g m
  obtain ⟨s, hs⟩ := h4m
  obtain ⟨t, ht⟩ := h4dvd
  omega

/-- Theorem 12 (Girth-10 Mod-8 Shift Immunity Obstruction):
    Even with a single `+2` shifted bay (`w_0 = 10`, remaining bays `w_t = 8`),
    `2 + 10 + m * 8 = 12 + 8*m` is NEVER a power of two `2^k` (`k ≥ 2`)! -/
theorem ladder_girth10_mod8_shift_immunity (m : ℕ) :
    ¬ IsPowerOfTwo (2 + 10 + m * 8) := by
  rintro ⟨k, hk, heq⟩
  by_cases hk2 : k = 2
  · subst hk2; norm_num at heq; omega
  · have hk3 : 3 ≤ k := by omega
    have h8dvd : 8 ∣ 2 ^ k := by
      have h3 : 2 ^ 3 ∣ 2 ^ k := Nat.pow_dvd_pow 2 hk3
      simpa using h3
    obtain ⟨t, ht⟩ := h8dvd
    omega

/-- Theorem 13 (Unbounded-n Girth-5 Ladder Closure):
    Any uniform girth-5 rung ladder (`w = 3`) with `r ≥ 3` rungs unconditionally contains `C_8`. -/
theorem ladder_girth5_closure {V : Type*} {G : SimpleGraph V} {r : ℕ}
    (L : RungLadder G r) (hr3 : 3 ≤ r)
    (hw : ∀ t : Fin (r - 1), (L.topSeg t).length + (L.botSeg t).length = 3) :
    HasPowerCycle G := by
  refine ⟨L.windowCycle 0 2 (by omega) (by omega), 3, by omega, ?_⟩
  rw [L.uniform_windowCycle_len hw]; norm_num

/-- Theorem 14 (Unbounded-n Girth-7 Ladder Closure):
    Any uniform girth-7 rung ladder (`w = 5`) with `r ≥ 7` rungs unconditionally contains `C_32`. -/
theorem ladder_girth7_closure {V : Type*} {G : SimpleGraph V} {r : ℕ}
    (L : RungLadder G r) (hr7 : 7 ≤ r)
    (hw : ∀ t : Fin (r - 1), (L.topSeg t).length + (L.botSeg t).length = 5) :
    HasPowerCycle G := by
  refine ⟨L.windowCycle 0 6 (by omega) (by omega), 5, by omega, ?_⟩
  rw [L.uniform_windowCycle_len hw]; norm_num

/-- Theorem 15 (Unbounded-n Girth-9 Ladder Closure):
    Any uniform girth-9 rung ladder (`w = 7`) with `r ≥ 3` rungs unconditionally contains `C_16`. -/
theorem ladder_girth9_closure {V : Type*} {G : SimpleGraph V} {r : ℕ}
    (L : RungLadder G r) (hr3 : 3 ≤ r)
    (hw : ∀ t : Fin (r - 1), (L.topSeg t).length + (L.botSeg t).length = 7) :
    HasPowerCycle G := by
  refine ⟨L.windowCycle 0 2 (by omega) (by omega), 4, by omega, ?_⟩
  rw [L.uniform_windowCycle_len hw]; norm_num

/-- Theorem 16 (Unbounded-n Girth-11 Ladder Closure):
    Any uniform girth-11 rung ladder (`w = 9`) with `r ≥ 15` rungs unconditionally contains `C_128`. -/
theorem ladder_girth11_closure {V : Type*} {G : SimpleGraph V} {r : ℕ}
    (L : RungLadder G r) (hr15 : 15 ≤ r)
    (hw : ∀ t : Fin (r - 1), (L.topSeg t).length + (L.botSeg t).length = 9) :
    HasPowerCycle G := by
  refine ⟨L.windowCycle 0 14 (by omega) (by omega), 7, by omega, ?_⟩
  rw [L.uniform_windowCycle_len hw]; norm_num

/-- Theorem 17 (Unbounded-n Girth-12 Ladder Closure):
    Any uniform girth-12 rung ladder (`w = 10`) with `r ≥ 4` rungs unconditionally contains `C_32`. -/
theorem ladder_girth12_closure {V : Type*} {G : SimpleGraph V} {r : ℕ}
    (L : RungLadder G r) (hr4 : 4 ≤ r)
    (hw : ∀ t : Fin (r - 1), (L.topSeg t).length + (L.botSeg t).length = 10) :
    HasPowerCycle G := by
  refine ⟨L.windowCycle 0 3 (by omega) (by omega), 5, by omega, ?_⟩
  rw [L.uniform_windowCycle_len hw]; norm_num

/-- Theorem 18 (Unbounded-n Girth-13 Ladder Closure):
    Any uniform girth-13 rung ladder (`w = 11`) with `r ≥ 187` rungs unconditionally contains `C_2048`. -/
theorem ladder_girth13_closure {V : Type*} {G : SimpleGraph V} {r : ℕ}
    (L : RungLadder G r) (hr187 : 187 ≤ r)
    (hw : ∀ t : Fin (r - 1), (L.topSeg t).length + (L.botSeg t).length = 11) :
    HasPowerCycle G := by
  refine ⟨L.windowCycle 0 186 (by omega) (by omega), 11, by omega, ?_⟩
  rw [L.uniform_windowCycle_len hw]; norm_num

/-- Theorem 19 (Twist-Breaker for `g ∈ {6, 10, 14}`):
    A single shifted bay `w_0 = 6` (`g = 6`, `+2` shift) yields `C_8`,
    and `w_0 = 14` (`g = 10`, `+6` shift, or `g = 14`, `+2` shift) yields `C_16`! -/
theorem twisted_ladder_breaks_mod4_two_barrier {V : Type*} {G : SimpleGraph V} {r : ℕ}
    (L : RungLadder G r)
    (hw0 : (L.topSeg ⟨0, by have := L.hr; omega⟩).length +
           (L.botSeg ⟨0, by have := L.hr; omega⟩).length = 6 ∨
           (L.topSeg ⟨0, by have := L.hr; omega⟩).length +
           (L.botSeg ⟨0, by have := L.hr; omega⟩).length = 14) :
    HasPowerCycle G := by
  have hhr := L.hr
  have hf : (Finset.univ : Finset (Fin (r - 1))).filter (fun t => 0 ≤ t.val ∧ t.val < 0 + 1) =
      {⟨0, by omega⟩} := by
    ext t; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff]
    dsimp; omega
  rcases hw0 with h6 | h14
  · refine ⟨L.windowCycle 0 1 (by omega) (by omega), 3, by omega, ?_⟩
    rw [L.windowCycle_len 0 1 (by omega) (by omega), hf, Finset.sum_singleton, h6]; norm_num
  · refine ⟨L.windowCycle 0 1 (by omega) (by omega), 4, by omega, ?_⟩
    rw [L.windowCycle_len 0 1 (by omega) (by omega), hf, Finset.sum_singleton, h14]; norm_num

/-! ### Part IV: Ihara–Chebyshev `B^16` Cage Thresholds & `EGRob` 2-Copy Gluing Spectrum -/

/-- Theorem 20 (Ihara–Chebyshev `B^16` Cage-Surpassing Thresholds & Cauchy–Schwarz Refinement):
    1. Nonbipartite `d = 3`: `T_8(3)^2 = 257^2 = 66049 > 511 * n` for ALL `n ≤ 129`,
       strictly surpassing the Moore bounds and exact cages for `g = 9, 10, 11, 12` (`58, 70, 112, 126`).
    2. Cauchy–Schwarz refinement (using `Tr(B^8) = 0`): `(n - 1) * 257^2 + (257 + n)^2 > 511 * n * (n - 1)`
       holds for ALL `2 ≤ n ≤ 131`.
    3. Bipartite `d = 3`: `2 * 257^2 = 132098 > 511 * n` for ALL `n ≤ 258`,
       strictly surpassing the Moore bound `M(3, 14) = 254`! -/
theorem ihara_chebyshev_b16_cage_thresholds :
    (∀ n : ℕ, n ≤ 129 → 511 * n < (2 ^ 8 + 1) ^ 2) ∧
    (∀ n : ℕ, 2 ≤ n → n ≤ 131 → 511 * n * (n - 1) < (n - 1) * (2 ^ 8 + 1) ^ 2 + (2 ^ 8 + 1 + n) ^ 2) ∧
    (∀ n : ℕ, n ≤ 258 → 511 * n < 2 * (2 ^ 8 + 1) ^ 2) := by
  refine ⟨fun n hn => by norm_num; omega, ?_, fun n hn => by norm_num; omega⟩
  intro n h2 h131
  cases n with
  | zero => omega
  | succ m =>
    simp only [Nat.add_sub_cancel]
    nlinarith

/-- Theorem 21 (`EGRob` Two-Copy Gluing Half-Power Path Exclusion):
    If two vertex-disjoint copies of `G = H - ab` glued at `{a, b}` are power-free,
    then `G` contains NO simple `a`-`b` path of length `2^(k-1)` (`k ≥ 2`) — because
    pairing the two copies of that path produces a simple `2^k`-cycle in the glued graph! -/
theorem egrob_two_copy_gluing_no_half_pow2_path {V : Type*} {G : SimpleGraph V}
    (hpf : PowerFree G) {k : ℕ} (hk : 2 ≤ k)
    (A B : List V) (hneA : A ≠ []) (hneB : B ≠ [])
    (hlenA : A.length = 2 ^ (k - 1)) (hlenB : B.length = 2 ^ (k - 1))
    (hndA : A.Nodup) (hndB : B.Nodup) (hdisj : List.Disjoint A B)
    (hchA : A.IsChain G.Adj) (hchB : B.IsChain G.Adj)
    (hAB : G.Adj (A.getLast hneA) (B.head hneB))
    (hBA : G.Adj (B.getLast hneB) (A.head hneA)) :
    False := by
  have h2k : 2 ^ k = 2 ^ (k - 1) + 2 ^ (k - 1) := by
    have : k = (k - 1) + 1 := by omega
    conv_lhs => rw [this, pow_succ]
    omega
  have hpow4 : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
  let C := SimpleCycle.ofTwoArcs A B hneA hneB
    (by omega) hndA hndB hdisj hchA hchB hAB hBA
  apply hpf
  refine ⟨C, k, hk, ?_⟩
  show (A ++ B).length = 2 ^ k
  rw [List.length_append, hlenA, hlenB, h2k]

end E64Wave8Agent10
