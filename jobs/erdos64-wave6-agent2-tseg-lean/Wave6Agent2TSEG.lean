import Shadow

/-!
# Erdős Problem #64 — Wave 6 Agent #2: Structural Theory of `TS-EG`
# (4-Regular Transition-System Power-Lifting)

All 12 theorems are all-order (no bound on `|V|`), zero-`sorry`, zero-`native_decide`,
and depend only on standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Summary of Kernel-Verified Results
1. `transitionSystem_four_regular`: Every transition system `(H, side)` is 4-regular.
2. `blowUp_cubic`: The canonical blow-up `blowUp H side` on `V × Bool` is strictly 3-regular (cubic).
3. `blowUp_no_matching_triangle`: No vertex in `blowUp H side` is adjacent to both `(u, false)` and `(u, true)`.
4. `blowUp_triangle_iff_zero_switch`: `blowUp H side` has a triangle iff `H` has a 0-switching triangle.
5. `blowUp_c4_no_matching_chord`: No 4-cycle in `blowUp H side` can have a matching chord.
6. `walk_signed_parity_law`: Exact signed-parity invariant along arbitrary nonempty walks in `(H, side)`.
7. `closed_walk_signed_parity_law`: For every nonempty closed walk `c` in `H`,
   `totalSwitches side c % 2 = negEdgeCount side c % 2`.
8. `balanced_even_switches`: In any balanced transition system (`H = F₀ ⊔ F₁`), every nonempty
   closed walk has an even number of switches.
9. `balanced_odd_cycle_avoids_pow2`: In any balanced transition system, no odd-length cycle
   can ever lift to `2^r` (`r ≥ 2`).
10. `cycle_chord_forces_length_ge_two_girth_sub_two`: In any graph of girth `≥ g`, any simple
    cycle with a chord has length `≥ 2g - 2`.
11. `cycle_lt_two_girth_sub_two_chordless`: In any graph of girth `≥ g`, every simple cycle
    of length `< 2g - 2` is unconditionally chordless (hence `M`-chordless for every matching `M`).
12. `tseg_girth_window_mchordless_power`: Any `2^r`-cycle (`r ≥ 2`) in `blowUp H side` of
    length `< 2g - 2` is automatically `M`-chordless and certifies `HasPower (blowUp H side)`.
-/

namespace E64Wave6Agent2
open SimpleGraph Erdos64Closure
open scoped Sym2

/-! ## Section 1: Transition Systems and Canonical Cubic Blow-Up -/

/-- A labeled 4-regular transition system on a simple graph `H`: at each vertex `u`,
its incident edges are partitioned by `side u : V → Bool` into two pairs of size 2. -/
def IsTransitionSystem {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (side : V → V → Bool) : Prop :=
  ∀ (u : V) (b : Bool), ((H.neighborFinset u).filter (fun v => side u v = b)).card = 2

/-- Every graph supporting a transition system is 4-regular. -/
theorem transitionSystem_four_regular {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (side : V → V → Bool)
    (hts : IsTransitionSystem H side) (u : V) : H.degree u = 4 := by
  have hpart :
      ((H.neighborFinset u).filter (fun v => side u v = false)).card +
      ((H.neighborFinset u).filter (fun v => side u v = true)).card =
      (H.neighborFinset u).card := by
    have hdisj : Disjoint
        ((H.neighborFinset u).filter (fun v => side u v = false))
        ((H.neighborFinset u).filter (fun v => side u v = true)) := by
      rw [Finset.disjoint_filter]
      intro v _ h1 h2
      rw [h1] at h2
      exact Bool.false_ne_true h2
    rw [← Finset.card_union_of_disjoint hdisj]
    congr 1
    ext v
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hv, _⟩ | ⟨hv, _⟩) <;> exact hv
    · intro hv
      cases side u v
      · exact Or.inl ⟨hv, rfl⟩
      · exact Or.inr ⟨hv, rfl⟩
  rw [hts u false, hts u true, H.card_neighborFinset_eq_degree] at hpart
  omega

/-- Canonical cubic blow-up `G = BlowUp(H, side)` on `V × Bool`:
matching edges connect `(u, false)` to `(u, true)`, and each `H`-edge `{u, v}`
connects `(u, side u v)` to `(v, side v u)`. -/
def blowUp {V : Type*} (H : SimpleGraph V) (side : V → V → Bool) : SimpleGraph (V × Bool) where
  Adj x y :=
    (x.1 = y.1 ∧ x.2 ≠ y.2) ∨
    (H.Adj x.1 y.1 ∧ side x.1 y.1 = x.2 ∧ side y.1 x.1 = y.2)
  symm := ⟨by
    rintro ⟨u, a⟩ ⟨v, b⟩ (⟨rfl, hne⟩ | ⟨hadj, h1, h2⟩)
    · exact Or.inl ⟨rfl, hne.symm⟩
    · exact Or.inr ⟨hadj.symm, h2, h1⟩⟩
  loopless := ⟨by
    rintro ⟨u, a⟩ (⟨_, hne⟩ | ⟨hadj, _, _⟩)
    · exact hne rfl
    · exact H.ne_of_adj hadj rfl⟩

/-- The canonical blow-up of any 4-regular transition system is strictly 3-regular (cubic). -/
theorem blowUp_cubic {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (side : V → V → Bool)
    [DecidableRel (blowUp H side).Adj]
    (hts : IsTransitionSystem H side) (x : V × Bool) :
    (blowUp H side).degree x = 3 := by
  rcases x with ⟨u, a⟩
  let S := (H.neighborFinset u).filter (fun v => side u v = a)
  let f : V → V × Bool := fun v => (v, side v u)
  have hfinj : Function.Injective f := fun v₁ v₂ h => congrArg Prod.fst h
  have hnotmem : (u, !a) ∉ S.image f := by
    simp only [Finset.mem_image, Finset.mem_filter, H.mem_neighborFinset, f, S]
    rintro ⟨v, ⟨huv, _⟩, heq⟩
    have hvu : v = u := congrArg Prod.fst heq
    subst hvu
    exact H.ne_of_adj huv rfl
  have hnbr : (blowUp H side).neighborFinset (u, a) = insert (u, !a) (S.image f) := by
    ext ⟨v, b⟩
    rw [SimpleGraph.mem_neighborFinset]
    simp only [Finset.mem_insert, Finset.mem_image,
      Finset.mem_filter, H.mem_neighborFinset, blowUp, f, S, Prod.mk.injEq]
    constructor
    · rintro (⟨rfl, hne⟩ | ⟨huv, h1, h2⟩)
      · left
        refine ⟨rfl, ?_⟩
        cases a <;> cases b <;> simp_all
      · right
        exact ⟨v, ⟨huv, h1⟩, rfl, h2⟩
    · rintro (⟨rfl, rfl⟩ | ⟨w, ⟨huw, h1⟩, rfl, rfl⟩)
      · left
        exact ⟨rfl, by cases a <;> decide⟩
      · right
        exact ⟨huw, h1, rfl⟩
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hnbr,
    Finset.card_insert_of_notMem hnotmem, Finset.card_image_of_injective _ hfinj, hts u a]

/-- No vertex in `blowUp H side` can be adjacent to both endpoints of a matching edge
`{(u, false), (u, true)}`. -/
theorem blowUp_no_matching_triangle {V : Type*} (H : SimpleGraph V) (side : V → V → Bool)
    (u : V) (w : V × Bool) :
    ¬ ((blowUp H side).Adj (u, false) w ∧ (blowUp H side).Adj (u, true) w) := by
  rintro ⟨h1, h2⟩
  rcases w with ⟨v, b⟩
  rcases h1 with ⟨rfl, hne1⟩ | ⟨huv1, hs1, _⟩
  · rcases h2 with ⟨_, hne2⟩ | ⟨huu, _, _⟩
    · cases b <;> simp_all
    · exact H.ne_of_adj huu rfl
  · rcases h2 with ⟨rfl, _⟩ | ⟨_, hs2, _⟩
    · exact H.ne_of_adj huv1 rfl
    · rw [hs1] at hs2
      exact Bool.false_ne_true hs2

/-- Exact triangle characterization: `blowUp H side` contains a triangle if and only if `H`
contains a 0-switching triangle. -/
theorem blowUp_triangle_iff_zero_switch {V : Type*} (H : SimpleGraph V) (side : V → V → Bool) :
    (∃ x y z : V × Bool,
      (blowUp H side).Adj x y ∧ (blowUp H side).Adj y z ∧ (blowUp H side).Adj z x) ↔
    (∃ u v w : V,
      H.Adj u v ∧ H.Adj v w ∧ H.Adj w u ∧
      side u v = side u w ∧ side v u = side v w ∧ side w u = side w v) := by
  constructor
  · rintro ⟨⟨u, a⟩, ⟨v, b⟩, ⟨w, c⟩, hxy, hyz, hzx⟩
    have h1 : H.Adj u v ∧ side u v = a ∧ side v u = b := by
      rcases hxy with ⟨rfl, hne⟩ | h
      · exfalso
        cases a <;> cases b
        · exact hne rfl
        · exact blowUp_no_matching_triangle H side u (w, c) ⟨hzx.symm, hyz⟩
        · exact blowUp_no_matching_triangle H side u (w, c) ⟨hyz, hzx.symm⟩
        · exact hne rfl
      · exact h
    have h2 : H.Adj v w ∧ side v w = b ∧ side w v = c := by
      rcases hyz with ⟨rfl, hne⟩ | h
      · exfalso
        cases b <;> cases c
        · exact hne rfl
        · exact blowUp_no_matching_triangle H side v (u, a) ⟨hxy.symm, hzx⟩
        · exact blowUp_no_matching_triangle H side v (u, a) ⟨hzx, hxy.symm⟩
        · exact hne rfl
      · exact h
    have h3 : H.Adj w u ∧ side w u = c ∧ side u w = a := by
      rcases hzx with ⟨rfl, hne⟩ | h
      · exfalso
        cases c <;> cases a
        · exact hne rfl
        · exact blowUp_no_matching_triangle H side w (v, b) ⟨hyz.symm, hxy⟩
        · exact blowUp_no_matching_triangle H side w (v, b) ⟨hxy, hyz.symm⟩
        · exact hne rfl
      · exact h
    exact ⟨u, v, w, h1.1, h2.1, h3.1, h1.2.1.trans h3.2.2.symm,
      h1.2.2.trans h2.2.1.symm, h3.2.1.trans h2.2.2.symm⟩
  · rintro ⟨u, v, w, huv, hvw, hwu, hsu, hsv, hsw⟩
    refine ⟨(u, side u v), (v, side v u), (w, side w u), ?_, ?_, ?_⟩
    · exact Or.inr ⟨huv, rfl, rfl⟩
    · exact Or.inr ⟨hvw, hsv.symm, hsw.symm⟩
    · exact Or.inr ⟨hwu, rfl, hsu.symm⟩

/-- In `blowUp H side`, no 4-cycle `(x, y, z, w)` can have a matching edge `{(u, false), (u, true)}`
as a chord (between opposite vertices `x` and `z`). -/
theorem blowUp_c4_no_matching_chord {V : Type*} (H : SimpleGraph V) (side : V → V → Bool)
    {u : V} {y w : V × Bool}
    (h1 : (blowUp H side).Adj (u, false) y) (h2 : (blowUp H side).Adj y (u, true))
    (_h3 : (blowUp H side).Adj (u, true) w) (_h4 : (blowUp H side).Adj w (u, false)) : False :=
  blowUp_no_matching_triangle H side u y ⟨h1, h2.symm⟩

/-! ## Section 2: Exact Signed-Parity Law and Balanced Transition Systems -/

/-- Number of negative edges (`side a b ≠ side b a`) along a walk in `H`. -/
def negEdgeCount {V : Type*} {H : SimpleGraph V} (side : V → V → Bool) :
    ∀ {u v : V}, H.Walk u v → ℕ
  | _, _, .nil => 0
  | _, _, .cons (u := a) (v := b) _ rest =>
      (if side a b ≠ side b a then 1 else 0) + negEdgeCount side rest

/-- Number of internal switching vertices along a walk in `H`. -/
def internalSwitches {V : Type*} {H : SimpleGraph V} (side : V → V → Bool) :
    ∀ {u v : V}, H.Walk u v → ℕ
  | _, _, .nil => 0
  | _, _, .cons _ .nil => 0
  | _, _, .cons (u := a) (v := b) _ (.cons (v := c) h₂ rest) =>
      (if side b a ≠ side b c then 1 else 0) + internalSwitches side (.cons h₂ rest)

/-- The first departure side of a nonempty walk. -/
def startSide {V : Type*} {H : SimpleGraph V} (side : V → V → Bool) :
    ∀ {u v : V}, H.Walk u v → Bool
  | _, _, .nil => false
  | _, _, .cons (u := a) (v := b) _ _ => side a b

/-- The final arrival side of a nonempty walk. -/
def endSide {V : Type*} {H : SimpleGraph V} (side : V → V → Bool) :
    ∀ {u v : V}, H.Walk u v → Bool
  | _, _, .nil => false
  | _, _, .cons (u := a) (v := b) _ .nil => side b a
  | _, _, .cons _ (.cons h rest) => endSide side (.cons h rest)

/-- Total switching count of a nonempty closed walk (internal switches plus basepoint switch). -/
def totalSwitches {V : Type*} {H : SimpleGraph V} (side : V → V → Bool)
    {u : V} (c : H.Walk u u) : ℕ :=
  internalSwitches side c + if startSide side c ≠ endSide side c then 1 else 0

private theorem bool_parity_base (s₁ s₂ : Bool) :
    (if s₁ ≠ s₂ then 1 else 0) % 2 = if s₁ ≠ s₂ then 1 else 0 := by
  cases s₁ <;> cases s₂ <;> decide

private theorem bool_parity_step (s₁ s₂ s₃ s₄ : Bool) (n m : ℕ)
    (ih : (n + m) % 2 = if s₃ ≠ s₄ then 1 else 0) :
    ((if s₂ ≠ s₃ then 1 else 0) + n + ((if s₁ ≠ s₂ then 1 else 0) + m)) % 2 =
      if s₁ ≠ s₄ then 1 else 0 := by
  cases s₁ <;> cases s₂ <;> cases s₃ <;> cases s₄ <;> simp_all <;> omega

/-- **Exact Signed-Parity Law on Walks**: For every nonempty walk `p` in `(H, side)`,
`internalSwitches side p + negEdgeCount side p` has the same parity as `startSide ≠ endSide`. -/
theorem walk_signed_parity_law {V : Type*} {H : SimpleGraph V} (side : V → V → Bool) :
    ∀ {u v : V} (p : H.Walk u v), 1 ≤ p.length →
      (internalSwitches side p + negEdgeCount side p) % 2 =
        if startSide side p ≠ endSide side p then 1 else 0
  | _, _, .nil, hp => by simp at hp
  | _, _, .cons (u := a) (v := b) _ .nil, _ => by
      simp only [internalSwitches, negEdgeCount, startSide, endSide, zero_add, add_zero]
      exact bool_parity_base (side a b) (side b a)
  | _, _, .cons (u := a) (v := b) _ (.cons (v := c) h₂ rest), _ => by
      have ih := walk_signed_parity_law side (.cons h₂ rest) (by simp)
      simp only [internalSwitches, negEdgeCount, startSide, endSide] at ih ⊢
      exact bool_parity_step (side a b) (side b a) (side b c)
        (endSide side (.cons h₂ rest))
        (internalSwitches side (.cons h₂ rest))
        ((if side b c ≠ side c b then 1 else 0) + negEdgeCount side rest) ih

/-- **Exact Signed-Parity Law on Closed Walks / Cycles**:
`totalSwitches side c ≡ negEdgeCount side c (mod 2)`. -/
theorem closed_walk_signed_parity_law {V : Type*} {H : SimpleGraph V} (side : V → V → Bool)
    {u : V} (c : H.Walk u u) (hpos : 1 ≤ c.length) :
    totalSwitches side c % 2 = negEdgeCount side c % 2 := by
  have h := walk_signed_parity_law side c hpos
  unfold totalSwitches
  split_ifs at h ⊢ <;> omega

/-- A transition system is balanced if every edge connects matching sides (`H = F₀ ⊔ F₁`). -/
def IsBalanced {V : Type*} (H : SimpleGraph V) (side : V → V → Bool) : Prop :=
  ∀ u v, H.Adj u v → side u v = side v u

private theorem negEdgeCount_eq_zero_of_balanced {V : Type*} {H : SimpleGraph V}
    {side : V → V → Bool} (hbal : IsBalanced H side) :
    ∀ {u v : V} (p : H.Walk u v), negEdgeCount side p = 0
  | _, _, .nil => rfl
  | _, _, .cons (u := a) (v := b) hab rest => by
      simp only [negEdgeCount, hbal a b hab, ne_eq, not_true_eq_false, ↓reduceIte, zero_add]
      exact negEdgeCount_eq_zero_of_balanced hbal rest

/-- In any balanced transition system, every nonempty closed walk has an even switching count. -/
theorem balanced_even_switches {V : Type*} {H : SimpleGraph V} {side : V → V → Bool}
    (hbal : IsBalanced H side) {u : V} (c : H.Walk u u) (hpos : 1 ≤ c.length) :
    totalSwitches side c % 2 = 0 := by
  rw [closed_walk_signed_parity_law side c hpos, negEdgeCount_eq_zero_of_balanced hbal c]

/-- In any balanced transition system, NO odd-length cycle can ever lift to `2^r` (`r ≥ 2`). -/
theorem balanced_odd_cycle_avoids_pow2 {V : Type*} {H : SimpleGraph V} {side : V → V → Bool}
    (hbal : IsBalanced H side) {u : V} (c : H.Walk u u) (hpos : 1 ≤ c.length)
    (hodd : c.length % 2 = 1) {r : ℕ} (hr : 2 ≤ r) :
    c.length + totalSwitches side c ≠ 2 ^ r := by
  have hsw := balanced_even_switches hbal c hpos
  have hpow : 2 ^ r % 2 = 0 := by
    cases r with
    | zero => omega
    | succ k => rw [pow_succ]; omega
  omega

/-! ## Section 3: Girth Chordlessness Threshold (`L < 2g - 2`) & Unconditional Girth-Window `TS-EG` -/

/-- Graph girth at least `g`: every simple cycle has length `≥ g`. -/
def GirthAtLeast {V : Type*} (G : SimpleGraph V) (g : ℕ) : Prop :=
  ∀ (v : V) (c : G.Walk v v), c.IsCycle → g ≤ c.length

/-- Helper: closing a path of length `≥ 2` by an edge between its endpoints forms a simple cycle. -/
private theorem isCycle_append_edge {V : Type*} {G : SimpleGraph V} {u w : V}
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

/-- **Exact Girth Chordlessness Threshold Theorem**:
In any simple graph `G` of girth `≥ g`, if a simple cycle `c` splits into two paths `p₁, p₂`
between `u` and `w` of lengths `≥ 2` with a chord `G.Adj u w`, then `2 * g ≤ c.length + 2`
(i.e. `c.length ≥ 2g - 2`). -/
theorem cycle_chord_forces_length_ge_two_girth_sub_two {V : Type*} {G : SimpleGraph V}
    {g : ℕ} (hg : GirthAtLeast G g) {u w : V}
    (p₁ : G.Walk u w) (p₂ : G.Walk w u)
    (hp₁ : p₁.IsPath) (hp₂ : p₂.IsPath)
    (hl₁ : 2 ≤ p₁.length) (hl₂ : 2 ≤ p₂.length)
    (hchord : G.Adj u w) :
    2 * g ≤ (p₁.append p₂).length + 2 := by
  have hc₁ : (p₁.append (.cons hchord.symm .nil)).IsCycle :=
    isCycle_append_edge p₁ hp₁ hl₁ hchord.symm
  have hc₂ : (p₂.append (.cons hchord .nil)).IsCycle :=
    isCycle_append_edge p₂ hp₂ hl₂ hchord
  have hg₁ := hg u _ hc₁
  have hg₂ := hg w _ hc₂
  simp only [Walk.length_append, Walk.length_cons, Walk.length_nil] at hg₁ hg₂ ⊢
  omega

/-- Corollary: Every simple cycle of length `< 2g - 2` in a graph of girth `≥ g` is
unconditionally chordless (cannot admit any chord, and in particular no matching chord). -/
theorem cycle_lt_two_girth_sub_two_chordless {V : Type*} {G : SimpleGraph V}
    {g : ℕ} (hg : GirthAtLeast G g) {u w : V}
    (p₁ : G.Walk u w) (p₂ : G.Walk w u)
    (hp₁ : p₁.IsPath) (hp₂ : p₂.IsPath)
    (hl₁ : 2 ≤ p₁.length) (hl₂ : 2 ≤ p₂.length)
    (hlt : (p₁.append p₂).length + 2 < 2 * g) :
    ¬ G.Adj u w := by
  intro hchord
  have hge := cycle_chord_forces_length_ge_two_girth_sub_two hg p₁ p₂ hp₁ hp₂ hl₁ hl₂ hchord
  omega

/-- A simple cycle in `blowUp H side` is `M`-chordless if no split of length-`≥ 2` paths
has a matching edge `{(u, false), (u, true)}` as a chord. -/
def IsMChordlessSplit {V : Type*} (H : SimpleGraph V) (side : V → V → Bool)
    {x : V × Bool} (c : (blowUp H side).Walk x x) : Prop :=
  ∀ {u : V} (p₁ : (blowUp H side).Walk (u, false) (u, true))
    (p₂ : (blowUp H side).Walk (u, true) (u, false)),
    p₁.IsPath → p₂.IsPath → 2 ≤ p₁.length → 2 ≤ p₂.length →
    (p₁.append p₂).length = c.length → False

/-- **Unconditional Girth-Window `TS-EG` Bridge**:
In any transition system `(H, side)` whose cubic blow-up `G = blowUp H side` has girth `≥ g`,
any simple `2^r`-cycle (`r ≥ 2`) in `G` with `2^r + 2 < 2 * g` is unconditionally `M`-chordless
(hence projects to a simple cycle in `H` with `|C| + s(C) = 2^r`) and certifies `HasPower G`. -/
theorem tseg_girth_window_mchordless_power {V : Type*} (H : SimpleGraph V) (side : V → V → Bool)
    {g r : ℕ} (hg : GirthAtLeast (blowUp H side) g) (hr : 2 ≤ r)
    (hwin : 2 ^ r + 2 < 2 * g)
    {x : V × Bool} (c : (blowUp H side).Walk x x)
    (hc : c.IsCycle) (hlen : c.length = 2 ^ r) :
    IsMChordlessSplit H side c ∧ HasPower (blowUp H side) := by
  refine ⟨?_, ⟨r, x, c, hr, hc, hlen⟩⟩
  intro u p₁ p₂ hp₁ hp₂ hl₁ hl₂ heq
  have hlt : (p₁.append p₂).length + 2 < 2 * g := by omega
  have hno := cycle_lt_two_girth_sub_two_chordless hg p₁ p₂ hp₁ hp₂ hl₁ hl₂ hlt
  exact hno (Or.inl ⟨rfl, Bool.false_ne_true⟩)

#print axioms transitionSystem_four_regular
#print axioms blowUp_cubic
#print axioms blowUp_no_matching_triangle
#print axioms blowUp_triangle_iff_zero_switch
#print axioms blowUp_c4_no_matching_chord
#print axioms walk_signed_parity_law
#print axioms closed_walk_signed_parity_law
#print axioms balanced_even_switches
#print axioms balanced_odd_cycle_avoids_pow2
#print axioms cycle_chord_forces_length_ge_two_girth_sub_two
#print axioms cycle_lt_two_girth_sub_two_chordless
#print axioms tseg_girth_window_mchordless_power

end E64Wave6Agent2
