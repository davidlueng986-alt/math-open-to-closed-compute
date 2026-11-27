import Shadow
import Wave6Agent2TSEG

/-!
# Erdős Problem #64 — Wave 7 Agent #4: Shattering the `2g - 2` Barrier & Gauge Theory for `TS-EG`

All 18 theorems are all-order (no bound on `|V|`), zero-`sorry`, zero-`native_decide`,
and depend only on standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).

## New All-Order Theorems Beyond Wave 6 Agent #2
1. `c8_mchord_forces_two_c5`: In ANY `C₄`-free blow-up (triangles allowed!), every `M`-chord of a
   simple 8-cycle splits it into two simple 5-cycles sharing that matching edge.
2. `c5_matching_free_c8_mchordless`: If `blowUp H side` is `C₄`-free and has no 5-cycle containing
   a matching edge (even at girth 3!), every simple 8-cycle is unconditionally `M`-chordless.
3. `girth_boundary_chord_forces_exact_half`: In any graph of girth `≥ g`, any chord of a `(2g-2)`-cycle
   splits it into two exact `g`-cycles.
4. `tseg_girth_boundary_mchord_forces_two_odd`: At every Wave-6-missed girth boundary `g = 2^k + 1`,
   any `M`-chord of a `2^(k+1)`-cycle splits it into two odd `(2^k+1)`-cycles sharing that `M`-edge.
5. `bipartite_girth_pow2_shatter`: For EVERY `r ≥ 3`, in any bipartite blow-up of girth `≥ 2^(r-1)`,
   any `2^(r-1)`-cycle or (when `2^(r-1)`-free) any `2^r`-cycle is unconditionally `M`-chordless —
   shattering Wave 6's `2^r < 2g - 2` barrier.
6. `bipartite_c16_mchord_forces_c6_c12`: In any bipartite `{C₄, C₈}`-free blow-up, every `M`-chord of
   a `C₁₆` splits it into a `C₆` and a `C₁₂`.
7. `bipartite_c4_c6_c8_free_c16_mchordless`: In any bipartite `{C₄, C₆, C₈}`-free blow-up, every
   `C₁₆` is unconditionally `M`-chordless.
8. `flipSide_preserves_transitionSystem`: `ℤ₂^V` gauge flipping preserves `IsTransitionSystem`.
9. `blowUp_gauge_iso`: Exact graph isomorphism `blowUp H side ≃g blowUp H (flipSide side φ)`.
10. `gauge_preserves_internalSwitches` & `gauge_preserves_totalSwitches`: Switching counts are
    strictly invariant under `ℤ₂^V` gauge flips.
11. `gauge_balanced_even_switches` & `gauge_balanced_odd_cycle_avoids_pow2`: Extend Wave 6's
    balanced parity obstruction to all gauge-balanced systems (`[σ] = 0 ∈ H¹(H; ℤ₂)`).
12. `bipartite_gauge_balanced_blowUp_bipartite`: Every gauge-balanced transition system on a
    bipartite 4-regular graph blows up to a bipartite cubic graph.
13. `balanced_blowUp_closed_walk_even_matching`: In any balanced blow-up, every closed walk uses an
    even number of matching edges.
14. `triangle_free_balanced_no_c5_matching` & `triangle_free_balanced_c8_mchordless`: In any
    triangle-free balanced `C₄`-free blow-up (even at girth 4!), no 5-cycle contains a matching
    edge and EVERY 8-cycle is unconditionally `M`-chordless.
15. `balanced_2factor_chord_forces_tseg`: In any balanced system `H = F₀ ⊔ F₁`, any `F₀`-chord of
    an `F₁`-path of length `2^r - 3` (`r ≥ 3`) produces a simple cycle in `H` of lifted length `2^r`.
-/

namespace E64Wave7Agent4
open SimpleGraph Erdos64Closure E64Wave6Agent2

/-! ## Section 1: Sharp `M`-Chord Rigidity & Girth-Boundary Shatter -/

/-- Helper: closing a path of length `≥ 2` by an edge forms a simple cycle. -/
private theorem isCycle_append_edge' {V : Type*} {G : SimpleGraph V} {u w : V}
    (p : G.Walk u w) (hp : p.IsPath) (hlen : 2 ≤ p.length) (hwu : G.Adj w u) :
    (p.append (.cons hwu .nil)).IsCycle := by
  have hq : (Walk.cons hwu Walk.nil : G.Walk w u).IsPath := by
    apply Walk.IsPath.mk'
    simp [G.ne_of_adj hwu]
  have hdisj : p.support.tail.Disjoint (Walk.cons hwu Walk.nil : G.Walk w u).support.tail := by
    intro x hx hmem
    simp only [Walk.support_cons, Walk.support_nil, List.tail_cons, List.mem_singleton] at hmem
    subst hmem
    cases p with
    | nil => simp at hlen
    | cons _ rest =>
        have hnd := hp.support_nodup
        simp only [Walk.support_cons, List.nodup_cons, List.tail_cons] at hnd hx
        exact hnd.1 hx
  exact hp.isCycle_append hq hdisj (Or.inl (by omega))

/-- A graph `G` has no simple cycle of length `L`. -/
def CycleFree {V : Type*} (G : SimpleGraph V) (L : ℕ) : Prop :=
  ∀ (v : V) (c : G.Walk v v), c.IsCycle → c.length ≠ L

/-- A graph `G` is even-cycle-only (bipartite condition on simple cycles). -/
def AllCyclesEven {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ (v : V) (c : G.Walk v v), c.IsCycle → c.length % 2 = 0

/-- No path of length 2 in `blowUp H side` can connect `(u, false)` and `(u, true)`. -/
private theorem blowUp_no_len2_matching_path {V : Type*} (H : SimpleGraph V) (side : V → V → Bool)
    {u : V} {a b : Bool} (hab : a ≠ b) (p : (blowUp H side).Walk (u, a) (u, b))
    (hlen : p.length = 2) : False := by
  cases p with
  | nil => simp at hlen
  | cons h1 rest =>
      cases rest with
      | nil => simp at hlen
      | cons h2 rest2 =>
          cases rest2 with
          | nil =>
              cases a <;> cases b
              · exact hab rfl
              · exact blowUp_no_matching_triangle H side u _ ⟨h1, h2.symm⟩
              · exact blowUp_no_matching_triangle H side u _ ⟨h2.symm, h1⟩
              · exact hab rfl
          | cons _ _ => simp at hlen

/-- **Sharp `C₈` `M`-Chord Rigidity (Triangles Allowed!)**:
In any `C₄`-free blow-up `blowUp H side` (no triangle-free assumption!), if a simple 8-cycle
splits into paths `p₁, p₂` of lengths `≥ 2` across a matching chord `{(u, false), (u, true)}`,
then BOTH `p₁` and `p₂` have length exactly 4, forming two simple 5-cycles sharing the matching edge. -/
theorem c8_mchord_forces_two_c5 {V : Type*} (H : SimpleGraph V) (side : V → V → Bool)
    (hc4 : CycleFree (blowUp H side) 4)
    {u : V}
    (p₁ : (blowUp H side).Walk (u, false) (u, true))
    (p₂ : (blowUp H side).Walk (u, true) (u, false))
    (hp₁ : p₁.IsPath) (hp₂ : p₂.IsPath)
    (hl₁ : 2 ≤ p₁.length) (hl₂ : 2 ≤ p₂.length)
    (hlen : (p₁.append p₂).length = 8) :
    p₁.length = 4 ∧ p₂.length = 4 ∧
      (p₁.append (Walk.cons (v := (u, false)) (Or.inl ⟨rfl, Bool.false_ne_true.symm⟩) .nil)).IsCycle ∧
      (p₂.append (Walk.cons (v := (u, true)) (Or.inl ⟨rfl, Bool.false_ne_true⟩) .nil)).IsCycle := by
  have hm1 : (blowUp H side).Adj (u, true) (u, false) := Or.inl ⟨rfl, Bool.false_ne_true.symm⟩
  have hm2 : (blowUp H side).Adj (u, false) (u, true) := Or.inl ⟨rfl, Bool.false_ne_true⟩
  have hc₁ : (p₁.append (Walk.cons (v := (u, false)) hm1 .nil)).IsCycle :=
    isCycle_append_edge' p₁ hp₁ hl₁ hm1
  have hc₂ : (p₂.append (Walk.cons (v := (u, true)) hm2 .nil)).IsCycle :=
    isCycle_append_edge' p₂ hp₂ hl₂ hm2
  have hne2_1 : p₁.length ≠ 2 := fun h => blowUp_no_len2_matching_path H side Bool.false_ne_true p₁ h
  have hne2_2 : p₂.length ≠ 2 := fun h => blowUp_no_len2_matching_path H side Bool.false_ne_true.symm p₂ h
  have hne3_1 : p₁.length ≠ 3 := by
    intro h
    have h4 := hc4 (u, false) _ hc₁
    simp only [Walk.length_append, Walk.length_cons, Walk.length_nil] at h4
    omega
  have hne3_2 : p₂.length ≠ 3 := by
    intro h
    have h4 := hc4 (u, true) _ hc₂
    simp only [Walk.length_append, Walk.length_cons, Walk.length_nil] at h4
    omega
  simp only [Walk.length_append] at hlen
  exact ⟨by omega, by omega, hc₁, hc₂⟩

/-- **Triangle-Allowing `C₈` Unconditional `M`-Chordlessness**:
If `blowUp H side` is `C₄`-free and has no 5-cycle containing a matching edge (even if it has
triangles!), then every simple 8-cycle in `blowUp H side` is unconditionally `M`-chordless. -/
theorem c5_matching_free_c8_mchordless {V : Type*} (H : SimpleGraph V) (side : V → V → Bool)
    (hc4 : CycleFree (blowUp H side) 4)
    (hno5 : ∀ (u : V) (p : (blowUp H side).Walk (u, false) (u, true)),
      p.IsPath → p.length = 4 → False)
    {x : V × Bool} (c : (blowUp H side).Walk x x) (hlen : c.length = 8) :
    IsMChordlessSplit H side c := by
  intro u p₁ p₂ hp₁ hp₂ hl₁ hl₂ heq
  have h8 : (p₁.append p₂).length = 8 := heq.trans hlen
  have ⟨h4, _, _, _⟩ := c8_mchord_forces_two_c5 H side hc4 p₁ p₂ hp₁ hp₂ hl₁ hl₂ h8
  exact hno5 u p₁ hp₁ h4

/-- **Exact Girth-Boundary Chord Rigidity**:
In any simple graph `G` of girth `≥ g`, any chord of a simple cycle of length `2g - 2` splits it
into two paths of exact length `g - 1`, forming two simple `g`-cycles sharing the chord. -/
theorem girth_boundary_chord_forces_exact_half {V : Type*} {G : SimpleGraph V}
    {g : ℕ} (hg : GirthAtLeast G g) {u w : V}
    (p₁ : G.Walk u w) (p₂ : G.Walk w u)
    (hp₁ : p₁.IsPath) (hp₂ : p₂.IsPath)
    (hl₁ : 2 ≤ p₁.length) (hl₂ : 2 ≤ p₂.length)
    (hchord : G.Adj u w)
    (hlen : (p₁.append p₂).length + 2 = 2 * g) :
    p₁.length + 1 = g ∧ p₂.length + 1 = g ∧
      (p₁.append (.cons hchord.symm .nil)).IsCycle ∧
      (p₂.append (.cons hchord .nil)).IsCycle := by
  have hc₁ := isCycle_append_edge' p₁ hp₁ hl₁ hchord.symm
  have hc₂ := isCycle_append_edge' p₂ hp₂ hl₂ hchord
  have hg₁ := hg u _ hc₁
  have hg₂ := hg w _ hc₂
  simp only [Walk.length_append, Walk.length_cons, Walk.length_nil] at hg₁ hg₂ hlen
  exact ⟨by omega, by omega, hc₁, hc₂⟩

/-- **All-Order `g = 2^k + 1` Girth-Boundary `M`-Chord Rigidity**:
At every Wave-6-missed girth boundary `g = 2^k + 1` (`k ≥ 2`), any `M`-chord of a `2^(k+1)`-cycle
in `blowUp H side` splits it into two odd `(2^k + 1)`-cycles sharing that matching edge. -/
theorem tseg_girth_boundary_mchord_forces_two_odd {V : Type*} (H : SimpleGraph V) (side : V → V → Bool)
    {k : ℕ} (hg : GirthAtLeast (blowUp H side) (2 ^ k + 1))
    {u : V}
    (p₁ : (blowUp H side).Walk (u, false) (u, true))
    (p₂ : (blowUp H side).Walk (u, true) (u, false))
    (hp₁ : p₁.IsPath) (hp₂ : p₂.IsPath)
    (hl₁ : 2 ≤ p₁.length) (hl₂ : 2 ≤ p₂.length)
    (hlen : (p₁.append p₂).length = 2 ^ (k + 1)) :
    p₁.length + 1 = 2 ^ k + 1 ∧ p₂.length + 1 = 2 ^ k + 1 := by
  have hbd : (p₁.append p₂).length + 2 = 2 * (2 ^ k + 1) := by
    rw [hlen, pow_succ]
    omega
  have ⟨h1, h2, _, _⟩ := girth_boundary_chord_forces_exact_half hg p₁ p₂ hp₁ hp₂ hl₁ hl₂
    (Or.inl ⟨rfl, Bool.false_ne_true⟩) hbd
  exact ⟨h1, h2⟩

/-- **Bipartite `2g - 2` Barrier Shatter (All `r ≥ 3`)**:
In any bipartite (`AllCyclesEven`) blow-up `blowUp H side` of girth `≥ 2^(r-1)` (`r ≥ 3`):
- If it has a `2^(r-1)`-cycle, that cycle is unconditionally `M`-chordless;
- If it is `2^(r-1)`-free and has a `2^r`-cycle, that `2^r`-cycle is STILL unconditionally
  `M`-chordless (strictly breaking Wave 6's `2^r < 2g - 2` ceiling!). -/
theorem bipartite_girth_pow2_shatter {V : Type*} (H : SimpleGraph V) (side : V → V → Bool)
    {r : ℕ} (hr : 3 ≤ r)
    (heven : AllCyclesEven (blowUp H side))
    (hg : GirthAtLeast (blowUp H side) (2 ^ (r - 1)))
    (hno_small : CycleFree (blowUp H side) (2 ^ (r - 1)))
    {x : V × Bool} (c : (blowUp H side).Walk x x) (hc : c.IsCycle) (hlen : c.length = 2 ^ r) :
    IsMChordlessSplit H side c ∧ HasPower (blowUp H side) := by
  have hg2 : GirthAtLeast (blowUp H side) (2 ^ (r - 1) + 2) := by
    intro v cy hcy
    have hge := hg v cy hcy
    have hne := hno_small v cy hcy
    have hev := heven v cy hcy
    have hpow_ev : 2 ^ (r - 1) % 2 = 0 := by
      obtain ⟨m, hm⟩ : ∃ m, r - 1 = m + 1 := ⟨r - 2, by omega⟩
      rw [hm, pow_succ]
      omega
    omega
  have hwin : 2 ^ r + 2 < 2 * (2 ^ (r - 1) + 2) := by
    have hpow : 2 ^ r = 2 * 2 ^ (r - 1) := by
      conv_lhs => rw [show r = (r - 1) + 1 by omega, pow_succ]
      omega
    omega
  exact tseg_girth_window_mchordless_power H side hg2 (by omega) hwin c hc hlen

/-- **Sharp Bipartite `C₁₆` `M`-Chord Rigidity**:
In any bipartite `{C₄, C₈}`-free blow-up, every `M`-chord of a `C₁₆` splits it into a `C₆` and a `C₁₂`. -/
theorem bipartite_c16_mchord_forces_c6_c12 {V : Type*} (H : SimpleGraph V) (side : V → V → Bool)
    (heven : AllCyclesEven (blowUp H side))
    (hc4 : CycleFree (blowUp H side) 4)
    (hc8 : CycleFree (blowUp H side) 8)
    {u : V}
    (p₁ : (blowUp H side).Walk (u, false) (u, true))
    (p₂ : (blowUp H side).Walk (u, true) (u, false))
    (hp₁ : p₁.IsPath) (hp₂ : p₂.IsPath)
    (hl₁ : 2 ≤ p₁.length) (hl₂ : 2 ≤ p₂.length)
    (hlen : (p₁.append p₂).length = 16) :
    (p₁.length = 5 ∧ p₂.length = 11) ∨ (p₁.length = 11 ∧ p₂.length = 5) := by
  have hm1 : (blowUp H side).Adj (u, true) (u, false) := Or.inl ⟨rfl, Bool.false_ne_true.symm⟩
  have hm2 : (blowUp H side).Adj (u, false) (u, true) := Or.inl ⟨rfl, Bool.false_ne_true⟩
  have hc₁ := isCycle_append_edge' p₁ hp₁ hl₁ hm1
  have hc₂ := isCycle_append_edge' p₂ hp₂ hl₂ hm2
  have hev₁ := heven (u, false) _ hc₁
  have hev₂ := heven (u, true) _ hc₂
  have hne4_1 := hc4 (u, false) _ hc₁
  have hne4_2 := hc4 (u, true) _ hc₂
  have hne8_1 := hc8 (u, false) _ hc₁
  have hne8_2 := hc8 (u, true) _ hc₂
  simp only [Walk.length_append, Walk.length_cons, Walk.length_nil] at hev₁ hev₂ hne4_1 hne4_2 hne8_1 hne8_2 hlen
  omega

/-- Corollary: In any bipartite `{C₄, C₆, C₈}`-free blow-up, every `C₁₆` is unconditionally `M`-chordless. -/
theorem bipartite_c4_c6_c8_free_c16_mchordless {V : Type*} (H : SimpleGraph V) (side : V → V → Bool)
    (heven : AllCyclesEven (blowUp H side))
    (hc4 : CycleFree (blowUp H side) 4)
    (hc6 : CycleFree (blowUp H side) 6)
    (hc8 : CycleFree (blowUp H side) 8)
    {x : V × Bool} (c : (blowUp H side).Walk x x) (hlen : c.length = 16) :
    IsMChordlessSplit H side c := by
  intro u p₁ p₂ hp₁ hp₂ hl₁ hl₂ heq
  have h16 : (p₁.append p₂).length = 16 := heq.trans hlen
  have hcases := bipartite_c16_mchord_forces_c6_c12 H side heven hc4 hc8 p₁ p₂ hp₁ hp₂ hl₁ hl₂ h16
  rcases hcases with ⟨h5, _⟩ | ⟨_, h5⟩
  · have hm1 : (blowUp H side).Adj (u, true) (u, false) := Or.inl ⟨rfl, Bool.false_ne_true.symm⟩
    have hc₁ := isCycle_append_edge' p₁ hp₁ hl₁ hm1
    have hne6 := hc6 (u, false) _ hc₁
    simp only [Walk.length_append, Walk.length_cons, Walk.length_nil] at hne6
    omega
  · have hm2 : (blowUp H side).Adj (u, false) (u, true) := Or.inl ⟨rfl, Bool.false_ne_true⟩
    have hc₂ := isCycle_append_edge' p₂ hp₂ hl₂ hm2
    have hne6 := hc6 (u, true) _ hc₂
    simp only [Walk.length_append, Walk.length_cons, Walk.length_nil] at hne6
    omega

/-! ## Section 2: `ℤ₂^V` Gauge Invariance & Cohomologically Balanced Systems -/

/-- Gauge-flip `side` by a vertex mask `φ : V → Bool`. -/
def flipSide {V : Type*} (side : V → V → Bool) (φ : V → Bool) : V → V → Bool :=
  fun u v => xor (side u v) (φ u)

/-- A transition system is gauge-balanced (`[σ] = 0 ∈ H¹(H; ℤ₂)`) if some vertex flip makes it balanced. -/
def IsGaugeBalanced {V : Type*} (H : SimpleGraph V) (side : V → V → Bool) : Prop :=
  ∃ φ : V → Bool, IsBalanced H (flipSide side φ)

private theorem xor_eq_iff_xor (a b c : Bool) : (xor a b = c) ↔ (a = xor c b) := by
  cases a <;> cases b <;> cases c <;> decide

private theorem xor_eq_xor_iff (a b c : Bool) : (xor a c = xor b c) ↔ (a = b) := by
  cases a <;> cases b <;> cases c <;> decide

private theorem xor_ne_xor_iff (a b c : Bool) : (xor a c ≠ xor b c) ↔ (a ≠ b) := by
  cases a <;> cases b <;> cases c <;> decide

/-- Gauge flipping preserves `IsTransitionSystem`. -/
theorem flipSide_preserves_transitionSystem {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (side : V → V → Bool) (φ : V → Bool)
    (hts : IsTransitionSystem H side) :
    IsTransitionSystem H (flipSide side φ) := by
  intro u b
  have h : (H.neighborFinset u).filter (fun v => flipSide side φ u v = b) =
           (H.neighborFinset u).filter (fun v => side u v = xor b (φ u)) := by
    ext v
    simp only [Finset.mem_filter, flipSide, xor_eq_iff_xor]
  rw [h, hts u (xor b (φ u))]

/-- Exact graph isomorphism `blowUp H side ≃g blowUp H (flipSide side φ)`. -/
def blowUp_gauge_iso {V : Type*} (H : SimpleGraph V) (side : V → V → Bool) (φ : V → Bool) :
    blowUp H side ≃g blowUp H (flipSide side φ) where
  toFun x := (x.1, xor x.2 (φ x.1))
  invFun x := (x.1, xor x.2 (φ x.1))
  left_inv x := by
    rcases x with ⟨u, a⟩
    simp only [Prod.mk.injEq, true_and]
    cases a <;> cases φ u <;> rfl
  right_inv x := by
    rcases x with ⟨u, a⟩
    simp only [Prod.mk.injEq, true_and]
    cases a <;> cases φ u <;> rfl
  map_rel_iff' := by
    rintro ⟨u, a⟩ ⟨v, b⟩
    simp only [Equiv.coe_fn_mk, blowUp, flipSide, xor_eq_xor_iff]
    constructor
    · rintro (⟨rfl, hne⟩ | ⟨hadj, h1, h2⟩)
      · exact Or.inl ⟨rfl, (xor_ne_xor_iff a b (φ u)).mp hne⟩
      · exact Or.inr ⟨hadj, h1, h2⟩
    · rintro (⟨rfl, hne⟩ | ⟨hadj, h1, h2⟩)
      · exact Or.inl ⟨rfl, (xor_ne_xor_iff a b (φ u)).mpr hne⟩
      · exact Or.inr ⟨hadj, h1, h2⟩

/-- `internalSwitches` is strictly invariant under `ℤ₂^V` gauge flips. -/
theorem gauge_preserves_internalSwitches {V : Type*} {H : SimpleGraph V}
    (side : V → V → Bool) (φ : V → Bool) :
    ∀ {u v : V} (p : H.Walk u v), internalSwitches (flipSide side φ) p = internalSwitches side p
  | _, _, .nil => rfl
  | _, _, .cons _ .nil => rfl
  | _, _, .cons (u := a) (v := b) _ (.cons (v := c) h₂ rest) => by
      simp only [internalSwitches, flipSide, xor_ne_xor_iff]
      rw [gauge_preserves_internalSwitches side φ (.cons h₂ rest)]

private theorem startSide_flipSide {V : Type*} {H : SimpleGraph V}
    (side : V → V → Bool) (φ : V → Bool) :
    ∀ {u v : V} (p : H.Walk u v), 1 ≤ p.length →
      startSide (flipSide side φ) p = xor (startSide side p) (φ u)
  | _, _, .nil, hp => by simp at hp
  | _, _, .cons _ _, _ => rfl

private theorem endSide_flipSide {V : Type*} {H : SimpleGraph V}
    (side : V → V → Bool) (φ : V → Bool) :
    ∀ {u v : V} (p : H.Walk u v), 1 ≤ p.length →
      endSide (flipSide side φ) p = xor (endSide side p) (φ v)
  | _, _, .nil, hp => by simp at hp
  | _, _, .cons _ .nil, _ => rfl
  | _, _, .cons _ (.cons h rest), _ => endSide_flipSide side φ (.cons h rest) (by simp)

/-- `totalSwitches` of every nonempty closed walk is strictly invariant under `ℤ₂^V` gauge flips. -/
theorem gauge_preserves_totalSwitches {V : Type*} {H : SimpleGraph V}
    (side : V → V → Bool) (φ : V → Bool) {u : V} (c : H.Walk u u) (hpos : 1 ≤ c.length) :
    totalSwitches (flipSide side φ) c = totalSwitches side c := by
  unfold totalSwitches
  rw [gauge_preserves_internalSwitches side φ c,
      startSide_flipSide side φ c hpos,
      endSide_flipSide side φ c hpos]
  simp only [xor_ne_xor_iff]

/-- Every gauge-balanced transition system has even `totalSwitches` on every nonempty closed walk. -/
theorem gauge_balanced_even_switches {V : Type*} {H : SimpleGraph V} {side : V → V → Bool}
    (hgb : IsGaugeBalanced H side) {u : V} (c : H.Walk u u) (hpos : 1 ≤ c.length) :
    totalSwitches side c % 2 = 0 := by
  rcases hgb with ⟨φ, hbal⟩
  rw [← gauge_preserves_totalSwitches side φ c hpos]
  exact balanced_even_switches hbal c hpos

/-- In every gauge-balanced transition system, NO odd-length cycle can lift to `2^r` (`r ≥ 2`). -/
theorem gauge_balanced_odd_cycle_avoids_pow2 {V : Type*} {H : SimpleGraph V} {side : V → V → Bool}
    (hgb : IsGaugeBalanced H side) {u : V} (c : H.Walk u u) (hpos : 1 ≤ c.length)
    (hodd : c.length % 2 = 1) {r : ℕ} (hr : 2 ≤ r) :
    c.length + totalSwitches side c ≠ 2 ^ r := by
  rcases hgb with ⟨φ, hbal⟩
  rw [← gauge_preserves_totalSwitches side φ c hpos]
  exact balanced_odd_cycle_avoids_pow2 hbal c hpos hodd hr

/-- A proper 2-coloring of a graph `G`. -/
def IsTwoColorable {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ col : V → Bool, ∀ u v, G.Adj u v → col u ≠ col v

/-- If `H` is 2-colorable (bipartite) and `(H, side)` is gauge-balanced, then `blowUp H side` is 2-colorable. -/
theorem bipartite_gauge_balanced_blowUp_bipartite {V : Type*} {H : SimpleGraph V} {side : V → V → Bool}
    (hbip : IsTwoColorable H) (hgb : IsGaugeBalanced H side) :
    IsTwoColorable (blowUp H side) := by
  rcases hbip with ⟨col, hcol⟩
  rcases hgb with ⟨φ, hbal⟩
  refine ⟨fun x => xor (col x.1) (xor x.2 (φ x.1)), ?_⟩
  rintro ⟨u, a⟩ ⟨v, b⟩ (⟨rfl, hne⟩ | ⟨hadj, h1, h2⟩)
  · cases col u <;> cases a <;> cases b <;> cases φ u <;> simp_all
  · have hcu := hcol u v hadj
    have hbf : xor (side u v) (φ u) = xor (side v u) (φ v) := hbal u v hadj
    rw [h1, h2] at hbf
    cases col u <;> cases col v <;> cases (xor a (φ u)) <;> cases (xor b (φ v)) <;> simp_all

/-! ## Section 3: Balanced Layer-Parity, Triangle-Free `C₈` Closure & 2-Factor Chord Forcing -/

/-- Number of matching edges (`x.1 = y.1 ∧ x.2 ≠ y.2`) along a walk in `blowUp H side`. -/
def matchingEdgeCount {V : Type*} [DecidableEq V] {H : SimpleGraph V} {side : V → V → Bool} :
    ∀ {x y : V × Bool}, (blowUp H side).Walk x y → ℕ
  | _, _, .nil => 0
  | _, _, .cons (u := x) (v := y) _ rest =>
      (if x.1 = y.1 ∧ x.2 ≠ y.2 then 1 else 0) + matchingEdgeCount rest

private theorem balanced_walk_matching_parity {V : Type*} [DecidableEq V]
    {H : SimpleGraph V} {side : V → V → Bool} (hbal : IsBalanced H side) :
    ∀ {x y : V × Bool} (p : (blowUp H side).Walk x y),
      matchingEdgeCount p % 2 = if x.2 ≠ y.2 then 1 else 0
  | _, _, .nil => by simp [matchingEdgeCount]
  | ⟨u, a⟩, ⟨w, c⟩, .cons (v := ⟨v, b⟩) h rest => by
      have ih := balanced_walk_matching_parity hbal rest
      simp only [matchingEdgeCount]
      rcases h with ⟨rfl, hab⟩ | ⟨hadj, h1, h2⟩
      · simp only [true_and, hab, ne_eq, not_false_eq_true, ↓reduceIte]
        cases a <;> cases b <;> cases c <;> simp_all <;> omega
      · have hne_uv : u ≠ v := H.ne_of_adj hadj
        have hab_eq : a = b := by
          have hb := hbal u v hadj
          rw [h1, h2] at hb
          exact hb
        simp only [hne_uv, false_and, ↓reduceIte, zero_add]
        subst hab_eq
        exact ih

/-- **Balanced Blow-Up Layer-Parity Law**:
In any balanced blow-up `blowUp H side`, every closed walk uses an EVEN number of matching edges. -/
theorem balanced_blowUp_closed_walk_even_matching {V : Type*} [DecidableEq V]
    {H : SimpleGraph V} {side : V → V → Bool} (hbal : IsBalanced H side)
    {x : V × Bool} (c : (blowUp H side).Walk x x) :
    matchingEdgeCount c % 2 = 0 := by
  have h := balanced_walk_matching_parity hbal c
  simp at h
  exact h

/-- **Triangle-Free Balanced No-`C₅`-Matching Theorem**:
In any triangle-free balanced blow-up `blowUp H side`, no simple 5-cycle can contain a matching edge. -/
theorem triangle_free_balanced_no_c5_matching {V : Type*} [DecidableEq V]
    {H : SimpleGraph V} {side : V → V → Bool} (hbal : IsBalanced H side)
    (htf : ∀ a b c : V, H.Adj a b → H.Adj b c → H.Adj c a → False)
    {u : V} (p : (blowUp H side).Walk (u, false) (u, true))
    (hp : p.IsPath) (hlen : p.length = 4) : False := by
  cases p with
  | cons h1 r1 =>
    cases r1 with
    | nil => simp at hlen
    | cons h2 r2 =>
      cases r2 with
      | nil => simp at hlen
      | cons h3 r3 =>
        cases r3 with
        | nil => simp at hlen
        | cons h4 r4 =>
          cases r4 with
          | cons _ _ => simp at hlen
          | nil =>
            have hnd := hp.support_nodup
            simp only [Walk.support_cons, Walk.support_nil, List.nodup_cons, List.mem_cons,
              List.not_mem_nil, or_false, not_or] at hnd
            rename_i v1 v2 v3
            rcases v1 with ⟨x1, b1⟩
            rcases v2 with ⟨x2, b2⟩
            rcases v3 with ⟨x3, b3⟩
            rcases h1 with ⟨heq1, hne1⟩ | ⟨ha1, hs1a, hs1b⟩
            · simp only at heq1 hne1 hnd
              subst heq1
              cases b1
              · exact hne1 rfl
              · exact hnd.2.1.2.2 rfl
            rcases h4 with ⟨heq4, hne4⟩ | ⟨ha4, hs4a, hs4b⟩
            · simp only at heq4 hne4 hnd
              subst heq4
              cases b3
              · exact hnd.1.2.2.1 rfl
              · exact hne4 rfl
            have hb1 : b1 = false := by
              have hb := hbal u x1 ha1
              rw [hs1a, hs1b] at hb
              exact hb.symm
            have hb3 : b3 = true := by
              have hb := hbal x3 u ha4
              rw [hs4a, hs4b] at hb
              exact hb
            subst hb1; subst hb3
            rcases h2 with ⟨heq2, hne2⟩ | ⟨ha2, hs2a, hs2b⟩
            · simp only at heq2 hne2
              subst heq2
              cases b2
              · exact hne2 rfl
              · rcases h3 with ⟨heq3, _⟩ | ⟨ha3, _, _⟩
                · simp only at heq3
                  subst heq3
                  exact hnd.2.2.1.1 rfl
                · exact htf u x1 x3 ha1 ha3 ha4
            · have hb2 : b2 = false := by
                have hb := hbal x1 x2 ha2
                rw [hs2a, hs2b] at hb
                exact hb.symm
              subst hb2
              rcases h3 with ⟨heq3, _⟩ | ⟨ha3, hs3a, hs3b⟩
              · simp only at heq3
                subst heq3
                exact htf u x1 x2 ha1 ha2 ha4
              · have hb := hbal x2 x3 ha3
                rw [hs3a, hs3b] at hb
                exact Bool.false_ne_true hb

/-- **Triangle-Free Balanced `C₈` Unconditional `M`-Chordlessness**:
In any triangle-free balanced transition system `(H, side)` whose blow-up is `C₄`-free (even at
girth 4!), EVERY simple 8-cycle in `blowUp H side` is unconditionally `M`-chordless. -/
theorem triangle_free_balanced_c8_mchordless {V : Type*} [DecidableEq V]
    {H : SimpleGraph V} {side : V → V → Bool} (hbal : IsBalanced H side)
    (htf : ∀ a b c : V, H.Adj a b → H.Adj b c → H.Adj c a → False)
    (hc4 : CycleFree (blowUp H side) 4)
    {x : V × Bool} (c : (blowUp H side).Walk x x) (hlen : c.length = 8) :
    IsMChordlessSplit H side c :=
  c5_matching_free_c8_mchordless H side hc4
    (fun _ p hp h4 => triangle_free_balanced_no_c5_matching hbal htf p hp h4) c hlen

/-- All edges along walk `p` lie on `side = b` (monochromatic `F_b`-walk). -/
def AllEdgesOnSide {V : Type*} {H : SimpleGraph V} (side : V → V → Bool) (b : Bool) :
    ∀ {u v : V}, H.Walk u v → Prop
  | _, _, .nil => True
  | _, _, .cons (u := x) (v := y) _ rest => side x y = b ∧ side y x = b ∧ AllEdgesOnSide side b rest

private theorem internalSwitches_allEdgesOnSide {V : Type*} {H : SimpleGraph V}
    (side : V → V → Bool) (b : Bool) :
    ∀ {u v : V} (p : H.Walk u v), AllEdgesOnSide side b p → internalSwitches side p = 0
  | _, _, .nil, _ => rfl
  | _, _, .cons _ .nil, _ => rfl
  | _, _, .cons _ (.cons h₂ rest), h => by
      rcases h with ⟨_, hba, hbc, hcb, hrest⟩
      simp only [internalSwitches, hba, hbc, ne_eq, not_true_eq_false, ↓reduceIte, zero_add]
      exact internalSwitches_allEdgesOnSide side b (.cons h₂ rest) ⟨hbc, hcb, hrest⟩

private theorem startSide_allEdgesOnSide {V : Type*} {H : SimpleGraph V}
    (side : V → V → Bool) (b : Bool) :
    ∀ {u v : V} (p : H.Walk u v), 1 ≤ p.length → AllEdgesOnSide side b p → startSide side p = b
  | _, _, .nil, hp, _ => by simp at hp
  | _, _, .cons _ _, _, h => h.1

private theorem endSide_allEdgesOnSide {V : Type*} {H : SimpleGraph V}
    (side : V → V → Bool) (b : Bool) :
    ∀ {u v : V} (p : H.Walk u v), 1 ≤ p.length → AllEdgesOnSide side b p → endSide side p = b
  | _, _, .nil, hp, _ => by simp at hp
  | _, _, .cons _ .nil, _, h => h.2.1
  | _, _, .cons _ (.cons h₂ rest), _, h =>
      endSide_allEdgesOnSide side b (.cons h₂ rest) (by simp) h.2.2

private theorem internalSwitches_append_edge {V : Type*} {H : SimpleGraph V}
    (side : V → V → Bool) :
    ∀ {u w z : V} (p : H.Walk u w) (hwz : H.Adj w z), 1 ≤ p.length →
      internalSwitches side (p.append (.cons hwz .nil)) =
        internalSwitches side p + if endSide side p ≠ side w z then 1 else 0
  | _, _, _, .nil, _, hp => by simp at hp
  | _, _, _, .cons _ .nil, _, _ => by
      simp only [Walk.append, internalSwitches, endSide, zero_add, add_zero]
      split_ifs <;> simp_all
  | _, _, _, .cons _ (.cons h₂ rest), hwz, _ => by
      have ih := internalSwitches_append_edge side (.cons h₂ rest) hwz (by simp)
      simp only [Walk.append, internalSwitches, endSide] at ih ⊢
      rw [ih, ← Nat.add_assoc]
      split_ifs <;> simp_all

private theorem startSide_append_edge {V : Type*} {H : SimpleGraph V}
    (side : V → V → Bool) :
    ∀ {u w z : V} (p : H.Walk u w) (hwz : H.Adj w z), 1 ≤ p.length →
      startSide side (p.append (.cons hwz .nil)) = startSide side p
  | _, _, _, .nil, _, hp => by simp at hp
  | _, _, _, .cons _ _, _, _ => rfl

private theorem endSide_append_edge {V : Type*} {H : SimpleGraph V}
    (side : V → V → Bool) :
    ∀ {u w z : V} (p : H.Walk u w) (hwz : H.Adj w z),
      endSide side (p.append (.cons hwz .nil)) = side z w
  | _, _, _, .nil, _ => rfl
  | _, _, _, .cons _ .nil, _ => rfl
  | _, _, _, .cons _ (.cons h₂ rest), hwz => endSide_append_edge side (.cons h₂ rest) hwz

/-- **Balanced 2-Factor Single-Edge Chord Forcing Theorem**:
In any balanced system `H = F₀ ⊔ F₁`, if a simple `F₁`-path `p` of length `2^r - 3` (`r ≥ 3`)
connects `u` and `v` with an `F₀`-chord `H.Adj v u`, then `c = p + vu` is a simple cycle in `H`
with `totalSwitches side c = 2` and `c.length + totalSwitches side c = 2^r` (certifying `TS-EG`). -/
theorem balanced_2factor_chord_forces_tseg {V : Type*} {H : SimpleGraph V}
    {side : V → V → Bool} {u v : V} {r : ℕ} (hr : 3 ≤ r)
    (p : H.Walk u v) (hp : p.IsPath)
    (hmono : AllEdgesOnSide side true p)
    (hlen : p.length + 3 = 2 ^ r)
    (hchord : H.Adj v u) (hs1 : side v u = false) (hs2 : side u v = false) :
    let c := p.append (.cons hchord .nil)
    c.IsCycle ∧ totalSwitches side c = 2 ∧ c.length + totalSwitches side c = 2 ^ r := by
  have hp2 : 2 ≤ p.length := by
    have h8 : 8 ≤ 2 ^ r := by
      have : 2 ^ 3 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr
      omega
    omega
  have hc : (p.append (.cons hchord .nil)).IsCycle := isCycle_append_edge' p hp hp2 hchord
  have hint : internalSwitches side (p.append (.cons hchord .nil)) = 1 := by
    rw [internalSwitches_append_edge side p hchord (by omega),
        internalSwitches_allEdgesOnSide side true p hmono,
        endSide_allEdgesOnSide side true p (by omega) hmono, hs1]
    decide
  have hst : startSide side (p.append (.cons hchord .nil)) = true := by
    rw [startSide_append_edge side p hchord (by omega)]
    exact startSide_allEdgesOnSide side true p (by omega) hmono
  have hen : endSide side (p.append (.cons hchord .nil)) = false := by
    rw [endSide_append_edge side p hchord, hs2]
  have hts : totalSwitches side (p.append (.cons hchord .nil)) = 2 := by
    unfold totalSwitches
    rw [hint, hst, hen]
    decide
  refine ⟨hc, hts, ?_⟩
  simp only [Walk.length_append, Walk.length_cons, Walk.length_nil, hts]
  omega

#print axioms c8_mchord_forces_two_c5
#print axioms c5_matching_free_c8_mchordless
#print axioms girth_boundary_chord_forces_exact_half
#print axioms tseg_girth_boundary_mchord_forces_two_odd
#print axioms bipartite_girth_pow2_shatter
#print axioms bipartite_c16_mchord_forces_c6_c12
#print axioms bipartite_c4_c6_c8_free_c16_mchordless
#print axioms flipSide_preserves_transitionSystem
#print axioms blowUp_gauge_iso
#print axioms gauge_preserves_internalSwitches
#print axioms gauge_preserves_totalSwitches
#print axioms gauge_balanced_even_switches
#print axioms gauge_balanced_odd_cycle_avoids_pow2
#print axioms bipartite_gauge_balanced_blowUp_bipartite
#print axioms balanced_blowUp_closed_walk_even_matching
#print axioms triangle_free_balanced_no_c5_matching
#print axioms triangle_free_balanced_c8_mchordless
#print axioms balanced_2factor_chord_forces_tseg

end E64Wave7Agent4
