import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic

/-!
# Wave 8 Free Agent #5 — Erdős Problem #64 (Erdős–Gyárfás Conjecture)

Two unconditional, all-order (unbounded-`n`) theorem families:
1. **Abelian-Cover Homological Commutator Theory**:
   - Regular `Γ`-voltage lifts `VoltageLift G α` over an arbitrary abelian group `[AddCommGroup Γ]`.
   - Zero-voltage cycle lifting (`zero_voltage_cycle_lifts`).
   - Universal Theta-Commutator Theorem (`abelian_cover_theta_commutator_simple`,
     `abelian_cover_theta_dichotomy`, `abelian_cover_theta_pow2_of_girth`) closing unbounded-order
     high-girth abelian covers (`Θ(2,3,3)`, `Θ(1,3,4)`, `Θ(5,5,6)`).
   - Universal Barbell-Commutator Theorem (`abelian_cover_barbell_commutator_simple`,
     `abelian_cover_barbell_pow2`).
2. **Tait 3-Edge-Coloring / Even 2-Factor Chord & Multi-Bridge Rigidity**:
   - Exact odd-chord exclusion on `C₆` and `C₁₂` (`c6_no_antipodal_chord_of_no_pow2`,
     `c12_no_odd_chord_of_no_pow2`).
   - Crossing-chord 6-cycle forcing (`crossing_chords_six_cycles`) and exact `C₁₀` single-chord
     theorem (`c10_no_two_antipodal_chords`).
   - Exact two-cycle bridge bounds (`two_disjoint_c5_at_most_one_bridge`,
     `two_disjoint_c6_no_equal_dist_bridges`, `two_disjoint_c6_bipartite_at_most_two_bridges`).
   - Even `C₆`-ring distance-1 closure (`tait_even_c6_ring_dist1_spectrum_hits_pow2`).

Zero `sorry`, zero `native_decide`, standard Lean axioms only (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace E64Wave8Agent5
open SimpleGraph

set_option maxHeartbeats 800000

/-- Exact Erdős–Gyárfás predicate: existence of a simple cycle of length `2^k` with `k ≥ 2`. -/
def HasPower {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k

/-- Girth lower bound: every simple cycle has length at least `g`. -/
def GirthGe {V : Type*} (G : SimpleGraph V) (g : ℕ) : Prop :=
  ∀ (v : V) (c : G.Walk v v), c.IsCycle → g ≤ c.length

/-! ### Section 0: List, Walk & Cycle Helper Lemmas -/

lemma nodup_append_of_disjoint {α : Type*} {l₁ l₂ : List α}
    (h1 : l₁.Nodup) (h2 : l₂.Nodup) (hd : ∀ x ∈ l₁, x ∉ l₂) :
    (l₁ ++ l₂).Nodup :=
  List.nodup_append.mpr ⟨h1, h2, fun a ha b hb hab => hd a ha (hab ▸ hb)⟩

lemma eq_of_mem_of_map_nodup {α β : Type*} {f : α → β} {l : List α}
    (hn : (l.map f).Nodup) {x y : α} (hx : x ∈ l) (hy : y ∈ l) (heq : f x = f y) :
    x = y := by
  induction l with
  | nil => simp at hx
  | cons a t ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    simp only [List.mem_cons] at hx hy
    rcases hx with rfl | hxt <;> rcases hy with rfl | hyt
    · rfl
    · exact (hn.1 (heq ▸ List.mem_map_of_mem hyt)).elim
    · exact (hn.1 (heq.symm ▸ List.mem_map_of_mem hxt)).elim
    · exact ih hn.2 hxt hyt

/-- A closed walk of length `≥ 3` whose `support.tail` is `Nodup` is a simple cycle. -/
lemma isCycle_of_length_ge_three_nodup {V : Type*} {G : SimpleGraph V} {u : V}
    {p : G.Walk u u} (hlen : 3 ≤ p.length) (hnodup : p.support.tail.Nodup) :
    p.IsCycle := by
  cases p with
  | nil => simp at hlen
  | @cons _ v _ h q =>
    have hq_path : q.IsPath := Walk.IsPath.mk' (by simpa [Walk.support_cons] using hnodup)
    have hq_len : 2 ≤ q.length := by
      simp only [Walk.length_cons] at hlen
      omega
    have hne_nil : Walk.cons h q ≠ Walk.nil := by simp
    have hnotmem : s(u, v) ∉ q.edges := by
      intro hmem
      cases q with
      | nil => simp at hq_len
      | @cons _ w _ hvw r =>
        simp only [Walk.edges_cons, List.mem_cons] at hmem
        rcases hmem with heq | hmem_r
        · rw [Sym2.eq_iff] at heq
          rcases heq with ⟨huv, _⟩ | ⟨huw, _⟩
          · exact G.ne_of_adj h huv
          · subst huw
            have hnodup_q : (v :: u :: r.support.tail).Nodup := by
              simpa [Walk.support_cons] using hnodup
            cases r with
            | nil =>
              simp only [Walk.length_cons, Walk.length_nil] at hq_len
              omega
            | @cons _ z _ huz r' =>
              have hnodup_u : (u :: z :: r'.support.tail).Nodup := by
                have := (List.nodup_cons.mp hnodup_q).2
                simpa [Walk.support_cons] using this
              have hu_end : u ∈ (z :: r'.support.tail) := by
                have := r'.end_mem_support
                simpa [Walk.support_cons] using this
              exact (List.nodup_cons.mp hnodup_u).1 hu_end
        · have hv_mem_r : v ∈ r.support := Walk.snd_mem_support_of_mem_edges r hmem_r
          have hnodup_q : (v :: r.support).Nodup := by
            simpa [Walk.support_cons] using hnodup
          exact (List.nodup_cons.mp hnodup_q).1 hv_mem_r
    rw [Walk.isCycle_def]
    refine ⟨Walk.IsTrail.mk ?_, hne_nil, hnodup⟩
    rw [Walk.edges_cons, List.nodup_cons]
    exact ⟨hnotmem, hq_path.isTrail.edges_nodup⟩

/-- Combining two internally disjoint simple paths `p, q : G.Walk u v` with `len p + len q ≥ 3`
gives a simple cycle `p.append q.reverse`. -/
lemma cycle_of_two_disjoint_paths {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (q : G.Walk u v)
    (hp : p.IsPath) (hq : q.IsPath)
    (hdisj : ∀ x, x ∈ p.support.tail → x ∈ q.support.tail → x = v)
    (hlen : 3 ≤ p.length + q.length) :
    (p.append q.reverse).IsCycle := by
  apply isCycle_of_length_ge_three_nodup
  · rw [Walk.length_append, Walk.length_reverse]; exact hlen
  · rw [Walk.support_append, List.tail_append_of_ne_nil (Walk.support_ne_nil p)]
    apply nodup_append_of_disjoint hp.support_nodup.tail
    · have hrev : q.reverse.support.Nodup := by
        rw [Walk.support_reverse]
        exact List.nodup_reverse.mpr hq.support_nodup
      exact hrev.tail
    · intro x hx_p hx_q
      have hx_q_supp : x ∈ q.support := by
        have := List.mem_of_mem_tail hx_q
        rw [Walk.support_reverse, List.mem_reverse] at this
        exact this
      have hx_ne_v : x ≠ v := by
        intro hxv
        have hv_q : v ∈ q.reverse.support.tail := hxv ▸ hx_q
        have hrev : q.reverse.support.Nodup := by
          rw [Walk.support_reverse]
          exact List.nodup_reverse.mpr hq.support_nodup
        have hhead : q.reverse.support = v :: q.reverse.support.tail := by
          cases q.reverse with
          | nil => simp [Walk.support_nil] at hv_q
          | cons _ _ => simp [Walk.support_cons]
        rw [hhead, List.nodup_cons] at hrev
        exact hrev.1 hv_q
      have hx_ne_u : x ≠ u := by
        intro hxu
        have hu_p : u ∈ p.support.tail := hxu ▸ hx_p
        have hp_nodup := hp.support_nodup
        cases p with
        | nil => simp at hu_p
        | cons _ _ =>
          simp only [Walk.support_cons, List.nodup_cons] at hp_nodup
          exact hp_nodup.1 hu_p
      have hx_q_tail : x ∈ q.support.tail := by
        cases q with
        | nil =>
          simp at hx_q_supp
          exact (hx_ne_u hx_q_supp).elim
        | cons _ _ =>
          simp only [Walk.support_cons, List.mem_cons] at hx_q_supp
          rcases hx_q_supp with rfl | htail
          · exact (hx_ne_u rfl).elim
          · exact htail
      exact hx_ne_v (hdisj x hx_p hx_q_tail)

lemma walk_append_support_tail {V : Type*} {G : SimpleGraph V} {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).support.tail = p.support.tail ++ q.support.tail := by
  rw [Walk.support_append, List.tail_append_of_ne_nil (Walk.support_ne_nil p)]

lemma start_not_mem_support_tail_of_isPath {V : Type*} {G : SimpleGraph V} {u v : V}
    {p : G.Walk u v} (hp : p.IsPath) : u ∉ p.support.tail := by
  cases p with
  | nil => simp
  | cons _ _ =>
    have h := hp.support_nodup
    simp only [Walk.support_cons, List.nodup_cons] at h
    exact h.1

lemma end_not_mem_reverse_support_tail_of_isPath {V : Type*} {G : SimpleGraph V} {u v : V}
    {p : G.Walk u v} (hp : p.IsPath) : v ∉ p.reverse.support.tail :=
  start_not_mem_support_tail_of_isPath hp.reverse

lemma mem_support_of_mem_tail {V : Type*} {G : SimpleGraph V} {u v : V}
    {p : G.Walk u v} {x : V} (hx : x ∈ p.support.tail) : x ∈ p.support :=
  List.mem_of_mem_tail hx

lemma mem_support_of_mem_reverse_tail {V : Type*} {G : SimpleGraph V} {u v : V}
    {p : G.Walk u v} {x : V} (hx : x ∈ p.reverse.support.tail) : x ∈ p.support := by
  have h := List.mem_of_mem_tail hx
  rwa [Walk.support_reverse, List.mem_reverse] at h

/-! ### Section 1: Pillar 1 — Abelian-Cover Homological Commutator Theory -/

/-- A skew-symmetric voltage assignment `α : V × V → Γ` into an abelian group `Γ`. -/
structure SkewVoltage (V : Type*) (Γ : Type*) [AddCommGroup Γ] where
  val : V → V → Γ
  skew : ∀ u v, val v u = -val u v

/-- The regular abelian cover (voltage lift) `VoltageLift G α` on `V × Γ`. -/
def VoltageLift {V Γ : Type*} [AddCommGroup Γ] (G : SimpleGraph V) (α : SkewVoltage V Γ) :
    SimpleGraph (V × Γ) where
  Adj x y := G.Adj x.1 y.1 ∧ y.2 = x.2 + α.val x.1 y.1
  symm := ⟨by
    rintro ⟨u, g⟩ ⟨v, h⟩ ⟨hadj, rfl⟩
    refine ⟨hadj.symm, ?_⟩
    rw [α.skew u v]
    abel⟩
  loopless := ⟨by rintro ⟨u, g⟩ ⟨hadj, _⟩; exact G.loopless.irrefl u hadj⟩

/-- Total voltage accumulated along a walk in the base graph `G`. -/
def walkVoltage {V Γ : Type*} [AddCommGroup Γ] {G : SimpleGraph V}
    (α : SkewVoltage V Γ) : ∀ {u v : V}, G.Walk u v → Γ
  | _, _, .nil => 0
  | u, _, .cons (v := v) _ q => α.val u v + walkVoltage α q

lemma walkVoltage_append {V Γ : Type*} [AddCommGroup Γ] {G : SimpleGraph V}
    (α : SkewVoltage V Γ) {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    walkVoltage α (p.append q) = walkVoltage α p + walkVoltage α q := by
  induction p with
  | nil => simp [walkVoltage]
  | cons _ p ih =>
    simp only [Walk.cons_append, walkVoltage, ih]
    abel

/-- Lifting a base walk `p : G.Walk u v` starting at sheet `g : Γ`. -/
def liftWalk {V Γ : Type*} [AddCommGroup Γ] {G : SimpleGraph V}
    (α : SkewVoltage V Γ) : ∀ {u v : V} (p : G.Walk u v) (g : Γ),
    (VoltageLift G α).Walk (u, g) (v, g + walkVoltage α p)
  | u, _, .nil, g =>
    Walk.copy Walk.nil rfl (by simp [walkVoltage])
  | u, w, .cons (v := v) h q, g =>
    Walk.copy
      (Walk.cons (show (VoltageLift G α).Adj (u, g) (v, g + α.val u v) from ⟨h, rfl⟩)
        (liftWalk α q (g + α.val u v)))
      rfl
      (by simp [walkVoltage, add_assoc])

lemma liftWalk_length {V Γ : Type*} [AddCommGroup Γ] {G : SimpleGraph V}
    (α : SkewVoltage V Γ) {u v : V} (p : G.Walk u v) (g : Γ) :
    (liftWalk α p g).length = p.length := by
  induction p generalizing g with
  | nil => simp [liftWalk]
  | cons h q ih =>
    simp only [liftWalk, Walk.length_copy, Walk.length_cons, ih]

lemma liftWalk_support_map_fst {V Γ : Type*} [AddCommGroup Γ] {G : SimpleGraph V}
    (α : SkewVoltage V Γ) {u v : V} (p : G.Walk u v) (g : Γ) :
    (liftWalk α p g).support.map Prod.fst = p.support := by
  induction p generalizing g with
  | nil => simp [liftWalk]
  | cons h q ih =>
    simp only [liftWalk, Walk.support_copy, Walk.support_cons, List.map_cons, ih]

lemma liftWalk_support_tail_map_fst {V Γ : Type*} [AddCommGroup Γ] {G : SimpleGraph V}
    (α : SkewVoltage V Γ) {u v : V} (p : G.Walk u v) (g : Γ) :
    (liftWalk α p g).support.tail.map Prod.fst = p.support.tail := by
  rw [List.map_tail, liftWalk_support_map_fst]

lemma liftWalk_support_shift {V Γ : Type*} [AddCommGroup Γ] {G : SimpleGraph V}
    (α : SkewVoltage V Γ) {u v : V} (p : G.Walk u v) (g δ : Γ) :
    (liftWalk α p (g + δ)).support = (liftWalk α p g).support.map (fun x => (x.1, x.2 + δ)) := by
  induction p generalizing g with
  | nil => simp [liftWalk]
  | @cons a b c h q ih =>
    simp only [liftWalk, Walk.support_copy, Walk.support_cons, List.map_cons]
    congr 1
    have hEq : g + δ + α.val a b = (g + α.val a b) + δ := by abel
    rw [hEq, ih]

lemma liftWalk_isPath {V Γ : Type*} [AddCommGroup Γ] {G : SimpleGraph V}
    (α : SkewVoltage V Γ) {u v : V} {p : G.Walk u v} (hp : p.IsPath) (g : Γ) :
    (liftWalk α p g).IsPath := by
  apply Walk.IsPath.mk'
  have hmap : ((liftWalk α p g).support.map Prod.fst).Nodup := by
    rw [liftWalk_support_map_fst]
    exact hp.support_nodup
  exact List.Nodup.of_map Prod.fst hmap

/-- Sheet-shift disjointness: two lifts of the same simple base path `p` from distinct starting
sheets `g₁ ≠ g₂` have completely vertex-disjoint supports. -/
lemma liftWalk_support_disjoint_of_ne {V Γ : Type*} [AddCommGroup Γ] {G : SimpleGraph V}
    (α : SkewVoltage V Γ) {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    {g₁ g₂ : Γ} (hne : g₁ ≠ g₂) :
    ∀ x, x ∈ (liftWalk α p g₁).support → x ∉ (liftWalk α p g₂).support := by
  rintro ⟨z, s⟩ hx1 hx2
  have h1 : (z, s) ∈ (liftWalk α p (0 + g₁)).support := by rwa [zero_add]
  have h2 : (z, s) ∈ (liftWalk α p (0 + g₂)).support := by rwa [zero_add]
  rw [liftWalk_support_shift, List.mem_map] at h1 h2
  rcases h1 with ⟨⟨z₁, t₁⟩, hm1, heq1⟩
  rcases h2 with ⟨⟨z₂, t₂⟩, hm2, heq2⟩
  have hz1 : z₁ = z := congrArg Prod.fst heq1
  have hz2 : z₂ = z := congrArg Prod.fst heq2
  have hs1 : t₁ + g₁ = s := congrArg Prod.snd heq1
  have hs2 : t₂ + g₂ = s := congrArg Prod.snd heq2
  have hnodup : ((liftWalk α p 0).support.map Prod.fst).Nodup := by
    rw [liftWalk_support_map_fst]
    exact hp.support_nodup
  have ht : (z₁, t₁) = (z₂, t₂) := eq_of_mem_of_map_nodup hnodup hm1 hm2 (hz1.trans hz2.symm)
  have ht_eq : t₁ = t₂ := congrArg Prod.snd ht
  subst ht_eq
  exact hne (add_left_cancel (hs1.trans hs2.symm))

/-- Sheet-shift disjointness for `support.tail` of a simple cycle `c` at distinct sheets `g₁ ≠ g₂`. -/
lemma liftWalk_cycle_tail_disjoint_of_ne {V Γ : Type*} [AddCommGroup Γ] {G : SimpleGraph V}
    (α : SkewVoltage V Γ) {u : V} (c : G.Walk u u) (hc : c.IsCycle)
    {g₁ g₂ : Γ} (hne : g₁ ≠ g₂) :
    ∀ x, x ∈ (liftWalk α c g₁).support.tail → x ∉ (liftWalk α c g₂).support.tail := by
  rintro ⟨z, s⟩ hx1 hx2
  have hshift1 : (liftWalk α c (0 + g₁)).support.tail =
      (liftWalk α c 0).support.tail.map (fun x => (x.1, x.2 + g₁)) := by
    rw [liftWalk_support_shift, ← List.map_tail]
  have hshift2 : (liftWalk α c (0 + g₂)).support.tail =
      (liftWalk α c 0).support.tail.map (fun x => (x.1, x.2 + g₂)) := by
    rw [liftWalk_support_shift, ← List.map_tail]
  have h1 : (z, s) ∈ (liftWalk α c (0 + g₁)).support.tail := by rwa [zero_add]
  have h2 : (z, s) ∈ (liftWalk α c (0 + g₂)).support.tail := by rwa [zero_add]
  rw [hshift1, List.mem_map] at h1
  rw [hshift2, List.mem_map] at h2
  rcases h1 with ⟨⟨z₁, t₁⟩, hm1, heq1⟩
  rcases h2 with ⟨⟨z₂, t₂⟩, hm2, heq2⟩
  have hz1 : z₁ = z := congrArg Prod.fst heq1
  have hz2 : z₂ = z := congrArg Prod.fst heq2
  have hs1 : t₁ + g₁ = s := congrArg Prod.snd heq1
  have hs2 : t₂ + g₂ = s := congrArg Prod.snd heq2
  have hnodup : ((liftWalk α c 0).support.tail.map Prod.fst).Nodup := by
    rw [liftWalk_support_tail_map_fst]
    exact hc.support_nodup
  have ht : (z₁, t₁) = (z₂, t₂) := eq_of_mem_of_map_nodup hnodup hm1 hm2 (hz1.trans hz2.symm)
  have ht_eq : t₁ = t₂ := congrArg Prod.snd ht
  subst ht_eq
  exact hne (add_left_cancel (hs1.trans hs2.symm))

/-- Theorem 1: Any simple cycle `c` in `G` with zero total voltage lifts to a simple cycle of the
exact same length in `VoltageLift G α`. -/
theorem zero_voltage_cycle_lifts {V Γ : Type*} [AddCommGroup Γ]
    (G : SimpleGraph V) (α : SkewVoltage V Γ) {u : V} (c : G.Walk u u)
    (hc : c.IsCycle) (hzero : walkVoltage α c = 0) :
    ∃ w : (VoltageLift G α).Walk (u, 0) (u, 0), w.IsCycle ∧ w.length = c.length := by
  let w : (VoltageLift G α).Walk (u, 0) (u, 0) :=
    Walk.copy (liftWalk α c 0) rfl (by simp [hzero])
  refine ⟨w, ?_, ?_⟩
  · apply isCycle_of_length_ge_three_nodup
    · simp only [w, Walk.length_copy, liftWalk_length]
      exact hc.three_le_length
    · simp only [w, Walk.support_copy]
      have hmap : ((liftWalk α c 0).support.tail.map Prod.fst).Nodup := by
        rw [liftWalk_support_tail_map_fst]
        exact hc.support_nodup
      exact List.Nodup.of_map Prod.fst hmap
  · simp [w, liftWalk_length]

lemma fst_mem_of_mem_liftWalk_support {V Γ : Type*} [AddCommGroup Γ] {G : SimpleGraph V}
    (α : SkewVoltage V Γ) {u v : V} (p : G.Walk u v) (g : Γ) {x : V × Γ}
    (hx : x ∈ (liftWalk α p g).support) : x.1 ∈ p.support := by
  rw [← liftWalk_support_map_fst α p g]
  exact List.mem_map_of_mem hx

lemma fst_mem_of_mem_liftWalk_tail {V Γ : Type*} [AddCommGroup Γ] {G : SimpleGraph V}
    (α : SkewVoltage V Γ) {u v : V} (p : G.Walk u v) (g : Γ) {x : V × Γ}
    (hx : x ∈ (liftWalk α p g).support.tail) : x.1 ∈ p.support.tail := by
  rw [← liftWalk_support_tail_map_fst α p g]
  exact List.mem_map_of_mem hx

lemma snd_eq_start_of_fst_eq_start {V Γ : Type*} [AddCommGroup Γ] {G : SimpleGraph V}
    (α : SkewVoltage V Γ) {u v : V} (p : G.Walk u v) (hp : p.IsPath) (g : Γ)
    {x : V × Γ} (hx : x ∈ (liftWalk α p g).support) (hxf : x.1 = u) : x.2 = g := by
  have hnodup : ((liftWalk α p g).support.map Prod.fst).Nodup := by
    rw [liftWalk_support_map_fst]; exact hp.support_nodup
  have hstart : (u, g) ∈ (liftWalk α p g).support := Walk.start_mem_support _
  have heq : x = (u, g) := eq_of_mem_of_map_nodup hnodup hx hstart hxf
  exact congrArg Prod.snd heq

lemma snd_eq_end_of_fst_eq_end {V Γ : Type*} [AddCommGroup Γ] {G : SimpleGraph V}
    (α : SkewVoltage V Γ) {u v : V} (p : G.Walk u v) (hp : p.IsPath) (g : Γ)
    {x : V × Γ} (hx : x ∈ (liftWalk α p g).support) (hxf : x.1 = v) :
    x.2 = g + walkVoltage α p := by
  have hnodup : ((liftWalk α p g).support.map Prod.fst).Nodup := by
    rw [liftWalk_support_map_fst]; exact hp.support_nodup
  have hend : (v, g + walkVoltage α p) ∈ (liftWalk α p g).support := Walk.end_mem_support _
  have heq : x = (v, g + walkVoltage α p) := eq_of_mem_of_map_nodup hnodup hx hend hxf
  exact congrArg Prod.snd heq

lemma fst_ne_start_of_mem_liftWalk_tail {V Γ : Type*} [AddCommGroup Γ] {G : SimpleGraph V}
    (α : SkewVoltage V Γ) {u v : V} (p : G.Walk u v) (hp : p.IsPath) (g : Γ)
    {x : V × Γ} (hx : x ∈ (liftWalk α p g).support.tail) : x.1 ≠ u := by
  intro h
  have hm := fst_mem_of_mem_liftWalk_tail α p g hx
  rw [h] at hm
  exact start_not_mem_support_tail_of_isPath hp hm

lemma fst_ne_end_of_mem_liftWalk_reverse_tail {V Γ : Type*} [AddCommGroup Γ] {G : SimpleGraph V}
    (α : SkewVoltage V Γ) {u v : V} (p : G.Walk u v) (hp : p.IsPath) (g : Γ)
    {x : V × Γ} (hx : x ∈ (liftWalk α p g).reverse.support.tail) : x.1 ≠ v := by
  intro h
  have hm : x ∈ (liftWalk α p g).support := mem_support_of_mem_reverse_tail hx
  have hs := snd_eq_end_of_fst_eq_end α p hp g hm h
  have hxeq : x = (v, g + walkVoltage α p) := Prod.ext h hs
  rw [hxeq] at hx
  exact end_not_mem_reverse_support_tail_of_isPath (liftWalk_isPath α hp g) hx

/-- Theorem 2 (Universal Abelian-Cover Theta-Commutator Theorem):
For ANY base graph `G`, ANY abelian group `Γ`, ANY skew-symmetric voltage `α`, and ANY theta
subgraph `Θ(a, b, c)` formed by three internally vertex-disjoint simple paths `p1, p2, p3 : G.Walk u v`
whose voltages are pairwise distinct, the commutator walk `p1 · p2⁻¹ · p3 · p1⁻¹ · p2 · p3⁻¹` lifts
to a SIMPLE CYCLE of length `2 * (p1.length + p2.length + p3.length)` in `VoltageLift G α`. -/
theorem abelian_cover_theta_commutator_simple {V Γ : Type*} [AddCommGroup Γ]
    (G : SimpleGraph V) (α : SkewVoltage V Γ) {u v : V}
    (p1 p2 p3 : G.Walk u v)
    (hp1 : p1.IsPath) (hp2 : p2.IsPath) (hp3 : p3.IsPath)
    (hl1 : 1 ≤ p1.length) (hl2 : 1 ≤ p2.length) (hl3 : 1 ≤ p3.length)
    (hd12 : ∀ x, x ∈ p1.support → x ∈ p2.support → x = u ∨ x = v)
    (hd23 : ∀ x, x ∈ p2.support → x ∈ p3.support → x = u ∨ x = v)
    (hd13 : ∀ x, x ∈ p1.support → x ∈ p3.support → x = u ∨ x = v)
    (h12 : walkVoltage α p1 ≠ walkVoltage α p2)
    (h23 : walkVoltage α p2 ≠ walkVoltage α p3)
    (h13 : walkVoltage α p1 ≠ walkVoltage α p3) :
    ∃ w : (VoltageLift G α).Walk (u, 0) (u, 0),
      w.IsCycle ∧ w.length = 2 * (p1.length + p2.length + p3.length) := by
  let a := walkVoltage α p1
  let b := walkVoltage α p2
  let c := walkVoltage α p3
  have hab : a ≠ b := h12
  have hbc : b ≠ c := h23
  have hac : a ≠ c := h13
  let s1 : (VoltageLift G α).Walk (u, 0) (v, a) :=
    Walk.copy (liftWalk α p1 0) rfl (by simp [a])
  let s2 : (VoltageLift G α).Walk (v, a) (u, a - b) :=
    Walk.copy (liftWalk α p2 (a - b)).reverse (by simp [b]) rfl
  let s3 : (VoltageLift G α).Walk (u, a - b) (v, a - b + c) :=
    Walk.copy (liftWalk α p3 (a - b)) rfl (by simp [c])
  let s4 : (VoltageLift G α).Walk (v, a - b + c) (u, c - b) :=
    Walk.copy (liftWalk α p1 (c - b)).reverse (by simp only [a]; congr 1; abel) rfl
  let s5 : (VoltageLift G α).Walk (u, c - b) (v, c) :=
    Walk.copy (liftWalk α p2 (c - b)) rfl (by simp [b])
  let s6 : (VoltageLift G α).Walk (v, c) (u, 0) :=
    Walk.copy (liftWalk α p3 0).reverse (by simp [c]) rfl
  let w : (VoltageLift G α).Walk (u, 0) (u, 0) :=
    s1.append (s2.append (s3.append (s4.append (s5.append s6))))
  have hlen : w.length = 2 * (p1.length + p2.length + p3.length) := by
    simp only [w, s1, s2, s3, s4, s5, s6, Walk.length_append, Walk.length_copy,
      Walk.length_reverse, liftWalk_length]
    omega
  refine ⟨w, ?_, hlen⟩
  apply isCycle_of_length_ge_three_nodup (by omega)
  have htail : w.support.tail =
      (liftWalk α p1 0).support.tail ++
      ((liftWalk α p2 (a - b)).reverse.support.tail ++
      ((liftWalk α p3 (a - b)).support.tail ++
      ((liftWalk α p1 (c - b)).reverse.support.tail ++
      ((liftWalk α p2 (c - b)).support.tail ++
      (liftWalk α p3 0).reverse.support.tail)))) := by
    simp only [w, s1, s2, s3, s4, s5, s6, walk_append_support_tail, Walk.support_copy]
  rw [htail]
  have hn1 : (liftWalk α p1 0).support.tail.Nodup := (liftWalk_isPath α hp1 0).support_nodup.tail
  have hn2 : (liftWalk α p2 (a - b)).reverse.support.tail.Nodup :=
    (liftWalk_isPath α hp2 (a - b)).reverse.support_nodup.tail
  have hn3 : (liftWalk α p3 (a - b)).support.tail.Nodup :=
    (liftWalk_isPath α hp3 (a - b)).support_nodup.tail
  have hn4 : (liftWalk α p1 (c - b)).reverse.support.tail.Nodup :=
    (liftWalk_isPath α hp1 (c - b)).reverse.support_nodup.tail
  have hn5 : (liftWalk α p2 (c - b)).support.tail.Nodup :=
    (liftWalk_isPath α hp2 (c - b)).support_nodup.tail
  have hn6 : (liftWalk α p3 0).reverse.support.tail.Nodup :=
    (liftWalk_isPath α hp3 0).reverse.support_nodup.tail
  have d12 : ∀ x ∈ (liftWalk α p1 0).support.tail,
      x ∉ (liftWalk α p2 (a - b)).reverse.support.tail := by
    intro x h1 h2
    have hm1 := mem_support_of_mem_tail h1
    have hm2 := mem_support_of_mem_reverse_tail h2
    rcases hd12 x.1 (fst_mem_of_mem_liftWalk_support α p1 0 hm1)
        (fst_mem_of_mem_liftWalk_support α p2 (a - b) hm2) with hxu | hxv
    · exact fst_ne_start_of_mem_liftWalk_tail α p1 hp1 0 h1 hxu
    · exact fst_ne_end_of_mem_liftWalk_reverse_tail α p2 hp2 (a - b) h2 hxv
  have d13 : ∀ x ∈ (liftWalk α p1 0).support.tail,
      x ∉ (liftWalk α p3 (a - b)).support.tail := by
    intro x h1 h3
    have hm1 := mem_support_of_mem_tail h1
    have hm3 := mem_support_of_mem_tail h3
    rcases hd13 x.1 (fst_mem_of_mem_liftWalk_support α p1 0 hm1)
        (fst_mem_of_mem_liftWalk_support α p3 (a - b) hm3) with hxu | hxv
    · exact fst_ne_start_of_mem_liftWalk_tail α p1 hp1 0 h1 hxu
    · have s1e := snd_eq_end_of_fst_eq_end α p1 hp1 0 hm1 hxv
      have s3e := snd_eq_end_of_fst_eq_end α p3 hp3 (a - b) hm3 hxv
      have heq : (0 : Γ) + a = a - b + c := s1e.symm.trans s3e
      exact hbc (eq_of_sub_eq_zero (by have h0 := sub_eq_zero.mpr heq; calc b - c = (0 + a) - (a - b + c) := by abel
        _ = 0 := h0))
  have d14 : ∀ x ∈ (liftWalk α p1 0).support.tail,
      x ∉ (liftWalk α p1 (c - b)).reverse.support.tail := by
    intro x h1 h4
    have hne : (0 : Γ) ≠ c - b := fun h => hbc (sub_eq_zero.mp h.symm).symm
    exact liftWalk_support_disjoint_of_ne α p1 hp1 hne x
      (mem_support_of_mem_tail h1) (mem_support_of_mem_reverse_tail h4)
  have d15 : ∀ x ∈ (liftWalk α p1 0).support.tail,
      x ∉ (liftWalk α p2 (c - b)).support.tail := by
    intro x h1 h5
    have hm1 := mem_support_of_mem_tail h1
    have hm5 := mem_support_of_mem_tail h5
    rcases hd12 x.1 (fst_mem_of_mem_liftWalk_support α p1 0 hm1)
        (fst_mem_of_mem_liftWalk_support α p2 (c - b) hm5) with hxu | hxv
    · exact fst_ne_start_of_mem_liftWalk_tail α p1 hp1 0 h1 hxu
    · have s1e := snd_eq_end_of_fst_eq_end α p1 hp1 0 hm1 hxv
      have s5e := snd_eq_end_of_fst_eq_end α p2 hp2 (c - b) hm5 hxv
      have heq : (0 : Γ) + a = c - b + b := s1e.symm.trans s5e
      exact hac (by simpa [a, b, c] using heq)
  have d16 : ∀ x ∈ (liftWalk α p1 0).support.tail,
      x ∉ (liftWalk α p3 0).reverse.support.tail := by
    intro x h1 h6
    have hm1 := mem_support_of_mem_tail h1
    have hm6 := mem_support_of_mem_reverse_tail h6
    rcases hd13 x.1 (fst_mem_of_mem_liftWalk_support α p1 0 hm1)
        (fst_mem_of_mem_liftWalk_support α p3 0 hm6) with hxu | hxv
    · exact fst_ne_start_of_mem_liftWalk_tail α p1 hp1 0 h1 hxu
    · exact fst_ne_end_of_mem_liftWalk_reverse_tail α p3 hp3 0 h6 hxv
  have d23 : ∀ x ∈ (liftWalk α p2 (a - b)).reverse.support.tail,
      x ∉ (liftWalk α p3 (a - b)).support.tail := by
    intro x h2 h3
    have hm2 := mem_support_of_mem_reverse_tail h2
    have hm3 := mem_support_of_mem_tail h3
    rcases hd23 x.1 (fst_mem_of_mem_liftWalk_support α p2 (a - b) hm2)
        (fst_mem_of_mem_liftWalk_support α p3 (a - b) hm3) with hxu | hxv
    · exact fst_ne_start_of_mem_liftWalk_tail α p3 hp3 (a - b) h3 hxu
    · exact fst_ne_end_of_mem_liftWalk_reverse_tail α p2 hp2 (a - b) h2 hxv
  have d24 : ∀ x ∈ (liftWalk α p2 (a - b)).reverse.support.tail,
      x ∉ (liftWalk α p1 (c - b)).reverse.support.tail := by
    intro x h2 h4
    have hm2 := mem_support_of_mem_reverse_tail h2
    have hm4 := mem_support_of_mem_reverse_tail h4
    rcases hd12 x.1 (fst_mem_of_mem_liftWalk_support α p1 (c - b) hm4)
        (fst_mem_of_mem_liftWalk_support α p2 (a - b) hm2) with hxu | hxv
    · have s2s := snd_eq_start_of_fst_eq_start α p2 hp2 (a - b) hm2 hxu
      have s4s := snd_eq_start_of_fst_eq_start α p1 hp1 (c - b) hm4 hxu
      exact hac (sub_left_inj.mp (s2s.symm.trans s4s))
    · exact fst_ne_end_of_mem_liftWalk_reverse_tail α p2 hp2 (a - b) h2 hxv
  have d25 : ∀ x ∈ (liftWalk α p2 (a - b)).reverse.support.tail,
      x ∉ (liftWalk α p2 (c - b)).support.tail := by
    intro x h2 h5
    have hne : a - b ≠ c - b := fun h => hac (sub_left_inj.mp h)
    exact liftWalk_support_disjoint_of_ne α p2 hp2 hne x
      (mem_support_of_mem_reverse_tail h2) (mem_support_of_mem_tail h5)
  have d26 : ∀ x ∈ (liftWalk α p2 (a - b)).reverse.support.tail,
      x ∉ (liftWalk α p3 0).reverse.support.tail := by
    intro x h2 h6
    have hm2 := mem_support_of_mem_reverse_tail h2
    have hm6 := mem_support_of_mem_reverse_tail h6
    rcases hd23 x.1 (fst_mem_of_mem_liftWalk_support α p2 (a - b) hm2)
        (fst_mem_of_mem_liftWalk_support α p3 0 hm6) with hxu | hxv
    · have s2s := snd_eq_start_of_fst_eq_start α p2 hp2 (a - b) hm2 hxu
      have s6s := snd_eq_start_of_fst_eq_start α p3 hp3 0 hm6 hxu
      exact hab (sub_eq_zero.mp (s2s.symm.trans s6s))
    · exact fst_ne_end_of_mem_liftWalk_reverse_tail α p2 hp2 (a - b) h2 hxv
  have d34 : ∀ x ∈ (liftWalk α p3 (a - b)).support.tail,
      x ∉ (liftWalk α p1 (c - b)).reverse.support.tail := by
    intro x h3 h4
    have hm3 := mem_support_of_mem_tail h3
    have hm4 := mem_support_of_mem_reverse_tail h4
    rcases hd13 x.1 (fst_mem_of_mem_liftWalk_support α p1 (c - b) hm4)
        (fst_mem_of_mem_liftWalk_support α p3 (a - b) hm3) with hxu | hxv
    · exact fst_ne_start_of_mem_liftWalk_tail α p3 hp3 (a - b) h3 hxu
    · exact fst_ne_end_of_mem_liftWalk_reverse_tail α p1 hp1 (c - b) h4 hxv
  have d35 : ∀ x ∈ (liftWalk α p3 (a - b)).support.tail,
      x ∉ (liftWalk α p2 (c - b)).support.tail := by
    intro x h3 h5
    have hm3 := mem_support_of_mem_tail h3
    have hm5 := mem_support_of_mem_tail h5
    rcases hd23 x.1 (fst_mem_of_mem_liftWalk_support α p2 (c - b) hm5)
        (fst_mem_of_mem_liftWalk_support α p3 (a - b) hm3) with hxu | hxv
    · exact fst_ne_start_of_mem_liftWalk_tail α p3 hp3 (a - b) h3 hxu
    · have s3e := snd_eq_end_of_fst_eq_end α p3 hp3 (a - b) hm3 hxv
      have s5e := snd_eq_end_of_fst_eq_end α p2 hp2 (c - b) hm5 hxv
      have heq : a - b + c = c - b + b := s3e.symm.trans s5e
      exact hab (eq_of_sub_eq_zero (by have h0 := sub_eq_zero.mpr heq; calc a - b = (a - b + c) - (c - b + b) := by abel
        _ = 0 := h0))
  have d36 : ∀ x ∈ (liftWalk α p3 (a - b)).support.tail,
      x ∉ (liftWalk α p3 0).reverse.support.tail := by
    intro x h3 h6
    have hne : a - b ≠ 0 := fun h => hab (sub_eq_zero.mp h)
    exact liftWalk_support_disjoint_of_ne α p3 hp3 hne x
      (mem_support_of_mem_tail h3) (mem_support_of_mem_reverse_tail h6)
  have d45 : ∀ x ∈ (liftWalk α p1 (c - b)).reverse.support.tail,
      x ∉ (liftWalk α p2 (c - b)).support.tail := by
    intro x h4 h5
    have hm4 := mem_support_of_mem_reverse_tail h4
    have hm5 := mem_support_of_mem_tail h5
    rcases hd12 x.1 (fst_mem_of_mem_liftWalk_support α p1 (c - b) hm4)
        (fst_mem_of_mem_liftWalk_support α p2 (c - b) hm5) with hxu | hxv
    · exact fst_ne_start_of_mem_liftWalk_tail α p2 hp2 (c - b) h5 hxu
    · exact fst_ne_end_of_mem_liftWalk_reverse_tail α p1 hp1 (c - b) h4 hxv
  have d46 : ∀ x ∈ (liftWalk α p1 (c - b)).reverse.support.tail,
      x ∉ (liftWalk α p3 0).reverse.support.tail := by
    intro x h4 h6
    have hm4 := mem_support_of_mem_reverse_tail h4
    have hm6 := mem_support_of_mem_reverse_tail h6
    rcases hd13 x.1 (fst_mem_of_mem_liftWalk_support α p1 (c - b) hm4)
        (fst_mem_of_mem_liftWalk_support α p3 0 hm6) with hxu | hxv
    · have s4s := snd_eq_start_of_fst_eq_start α p1 hp1 (c - b) hm4 hxu
      have s6s := snd_eq_start_of_fst_eq_start α p3 hp3 0 hm6 hxu
      exact hbc (sub_eq_zero.mp (s4s.symm.trans s6s)).symm
    · exact fst_ne_end_of_mem_liftWalk_reverse_tail α p1 hp1 (c - b) h4 hxv
  have d56 : ∀ x ∈ (liftWalk α p2 (c - b)).support.tail,
      x ∉ (liftWalk α p3 0).reverse.support.tail := by
    intro x h5 h6
    have hm5 := mem_support_of_mem_tail h5
    have hm6 := mem_support_of_mem_reverse_tail h6
    rcases hd23 x.1 (fst_mem_of_mem_liftWalk_support α p2 (c - b) hm5)
        (fst_mem_of_mem_liftWalk_support α p3 0 hm6) with hxu | hxv
    · exact fst_ne_start_of_mem_liftWalk_tail α p2 hp2 (c - b) h5 hxu
    · exact fst_ne_end_of_mem_liftWalk_reverse_tail α p3 hp3 0 h6 hxv
  apply nodup_append_of_disjoint hn1
  · apply nodup_append_of_disjoint hn2
    · apply nodup_append_of_disjoint hn3
      · apply nodup_append_of_disjoint hn4
        · exact nodup_append_of_disjoint hn5 hn6 d56
        · intro x hx4 h56; simp only [List.mem_append] at h56
          rcases h56 with h5 | h6
          · exact d45 x hx4 h5
          · exact d46 x hx4 h6
      · intro x hx3 h456; simp only [List.mem_append] at h456
        rcases h456 with h4 | h5 | h6
        · exact d34 x hx3 h4
        · exact d35 x hx3 h5
        · exact d36 x hx3 h6
    · intro x hx2 h3456; simp only [List.mem_append] at h3456
      rcases h3456 with h3 | h4 | h5 | h6
      · exact d23 x hx2 h3
      · exact d24 x hx2 h4
      · exact d25 x hx2 h5
      · exact d26 x hx2 h6
  · intro x hx1 h23456; simp only [List.mem_append] at h23456
    rcases h23456 with h2 | h3 | h4 | h5 | h6
    · exact d12 x hx1 h2
    · exact d13 x hx1 h3
    · exact d14 x hx1 h4
    · exact d15 x hx1 h5
    · exact d16 x hx1 h6

/-- Theorem 3 (Universal Abelian-Cover Theta Dichotomy):
Every abelian cover of a graph containing `Θ(a, b, c)` (with `a+b, b+c, a+c ≥ 3`) contains a simple
cycle of length `a+b`, `b+c`, `a+c`, OR `2*(a+b+c)`. -/
theorem abelian_cover_theta_dichotomy {V Γ : Type*} [AddCommGroup Γ]
    (G : SimpleGraph V) (α : SkewVoltage V Γ) {u v : V}
    (p1 p2 p3 : G.Walk u v)
    (hp1 : p1.IsPath) (hp2 : p2.IsPath) (hp3 : p3.IsPath)
    (hl1 : 1 ≤ p1.length) (hl2 : 1 ≤ p2.length) (hl3 : 1 ≤ p3.length)
    (h12_len : 3 ≤ p1.length + p2.length)
    (h23_len : 3 ≤ p2.length + p3.length)
    (h13_len : 3 ≤ p1.length + p3.length)
    (hd12 : ∀ x, x ∈ p1.support → x ∈ p2.support → x = u ∨ x = v)
    (hd23 : ∀ x, x ∈ p2.support → x ∈ p3.support → x = u ∨ x = v)
    (hd13 : ∀ x, x ∈ p1.support → x ∈ p3.support → x = u ∨ x = v) :
    ∃ (w : (VoltageLift G α).Walk (u, 0) (u, 0)), w.IsCycle ∧
      (w.length = p1.length + p2.length ∨
       w.length = p2.length + p3.length ∨
       w.length = p1.length + p3.length ∨
       w.length = 2 * (p1.length + p2.length + p3.length)) := by
  by_cases h12 : walkVoltage α p1 = walkVoltage α p2
  · let w : (VoltageLift G α).Walk (u, 0) (u, 0) :=
      (liftWalk α p1 0).append (Walk.copy (liftWalk α p2 0).reverse (by simp [h12]) rfl)
    refine ⟨w, ?_, Or.inl (by simp [w, liftWalk_length])⟩
    apply isCycle_of_length_ge_three_nodup (by simp [w, liftWalk_length, h12_len])
    rw [walk_append_support_tail, Walk.support_copy]
    apply nodup_append_of_disjoint (liftWalk_isPath α hp1 0).support_nodup.tail
      (liftWalk_isPath α hp2 0).reverse.support_nodup.tail
    intro x hx1 hx2
    have hm1 := mem_support_of_mem_tail hx1
    have hm2 := mem_support_of_mem_reverse_tail hx2
    rcases hd12 x.1 (fst_mem_of_mem_liftWalk_support α p1 0 hm1)
        (fst_mem_of_mem_liftWalk_support α p2 0 hm2) with hxu | hxv
    · exact fst_ne_start_of_mem_liftWalk_tail α p1 hp1 0 hx1 hxu
    · exact fst_ne_end_of_mem_liftWalk_reverse_tail α p2 hp2 0 hx2 hxv
  · by_cases h23 : walkVoltage α p2 = walkVoltage α p3
    · let w : (VoltageLift G α).Walk (u, 0) (u, 0) :=
        (liftWalk α p2 0).append (Walk.copy (liftWalk α p3 0).reverse (by simp [h23]) rfl)
      refine ⟨w, ?_, Or.inr (Or.inl (by simp [w, liftWalk_length]))⟩
      apply isCycle_of_length_ge_three_nodup (by simp [w, liftWalk_length, h23_len])
      rw [walk_append_support_tail, Walk.support_copy]
      apply nodup_append_of_disjoint (liftWalk_isPath α hp2 0).support_nodup.tail
        (liftWalk_isPath α hp3 0).reverse.support_nodup.tail
      intro x hx2 hx3
      have hm2 := mem_support_of_mem_tail hx2
      have hm3 := mem_support_of_mem_reverse_tail hx3
      rcases hd23 x.1 (fst_mem_of_mem_liftWalk_support α p2 0 hm2)
          (fst_mem_of_mem_liftWalk_support α p3 0 hm3) with hxu | hxv
      · exact fst_ne_start_of_mem_liftWalk_tail α p2 hp2 0 hx2 hxu
      · exact fst_ne_end_of_mem_liftWalk_reverse_tail α p3 hp3 0 hx3 hxv
    · by_cases h13 : walkVoltage α p1 = walkVoltage α p3
      · let w : (VoltageLift G α).Walk (u, 0) (u, 0) :=
          (liftWalk α p1 0).append (Walk.copy (liftWalk α p3 0).reverse (by simp [h13]) rfl)
        refine ⟨w, ?_, Or.inr (Or.inr (Or.inl (by simp [w, liftWalk_length])))⟩
        apply isCycle_of_length_ge_three_nodup (by simp [w, liftWalk_length, h13_len])
        rw [walk_append_support_tail, Walk.support_copy]
        apply nodup_append_of_disjoint (liftWalk_isPath α hp1 0).support_nodup.tail
          (liftWalk_isPath α hp3 0).reverse.support_nodup.tail
        intro x hx1 hx3
        have hm1 := mem_support_of_mem_tail hx1
        have hm3 := mem_support_of_mem_reverse_tail hx3
        rcases hd13 x.1 (fst_mem_of_mem_liftWalk_support α p1 0 hm1)
            (fst_mem_of_mem_liftWalk_support α p3 0 hm3) with hxu | hxv
        · exact fst_ne_start_of_mem_liftWalk_tail α p1 hp1 0 hx1 hxu
        · exact fst_ne_end_of_mem_liftWalk_reverse_tail α p3 hp3 0 hx3 hxv
      · obtain ⟨w, hwc, hwl⟩ := abelian_cover_theta_commutator_simple G α p1 p2 p3
          hp1 hp2 hp3 hl1 hl2 hl3 hd12 hd23 hd13 h12 h23 h13
        exact ⟨w, hwc, Or.inr (Or.inr (Or.inr hwl))⟩

/-- Theorem 4 (High-Girth Abelian-Cover Power-of-Two Closure):
If `G` contains `Θ(a, b, c)` with `a + b + c = 2^(k-1)` (`k ≥ 3`), then EVERY abelian cover
`VoltageLift G α` of girth `> max(a+b, b+c, a+c)` unconditionally has a simple `2^k`-cycle. -/
theorem abelian_cover_theta_pow2_of_girth {V Γ : Type*} [AddCommGroup Γ]
    (G : SimpleGraph V) (α : SkewVoltage V Γ) {u v : V}
    (p1 p2 p3 : G.Walk u v) (k : ℕ) (hk : 3 ≤ k)
    (hp1 : p1.IsPath) (hp2 : p2.IsPath) (hp3 : p3.IsPath)
    (hl1 : 1 ≤ p1.length) (hl2 : 1 ≤ p2.length) (hl3 : 1 ≤ p3.length)
    (h12_len : 3 ≤ p1.length + p2.length)
    (h23_len : 3 ≤ p2.length + p3.length)
    (h13_len : 3 ≤ p1.length + p3.length)
    (hd12 : ∀ x, x ∈ p1.support → x ∈ p2.support → x = u ∨ x = v)
    (hd23 : ∀ x, x ∈ p2.support → x ∈ p3.support → x = u ∨ x = v)
    (hd13 : ∀ x, x ∈ p1.support → x ∈ p3.support → x = u ∨ x = v)
    (hsum : p1.length + p2.length + p3.length = 2 ^ (k - 1))
    (hgirth : GirthGe (VoltageLift G α)
      (max (p1.length + p2.length) (max (p2.length + p3.length) (p1.length + p3.length)) + 1)) :
    HasPower (VoltageLift G α) := by
  obtain ⟨w, hwc, hwl⟩ := abelian_cover_theta_dichotomy G α p1 p2 p3
    hp1 hp2 hp3 hl1 hl2 hl3 h12_len h23_len h13_len hd12 hd23 hd13
  have hge := hgirth (u, 0) w hwc
  rcases hwl with h | h | h | h
  · omega
  · omega
  · omega
  · refine ⟨k, (u, 0), w, by omega, hwc, ?_⟩
    rw [h, hsum]
    have hk1 : k = (k - 1) + 1 := by omega
    conv_rhs => rw [hk1, pow_succ]
    ring

/-- Theorem 5: Every girth-`≥ 7` abelian cover of ANY graph containing `Θ(2,3,3)` has a simple `C₁₆`. -/
theorem abelian_cover_theta233_girth7_hasPower {V Γ : Type*} [AddCommGroup Γ]
    (G : SimpleGraph V) (α : SkewVoltage V Γ) {u v : V}
    (p1 p2 p3 : G.Walk u v)
    (hp1 : p1.IsPath) (hp2 : p2.IsPath) (hp3 : p3.IsPath)
    (hl1 : p1.length = 2) (hl2 : p2.length = 3) (hl3 : p3.length = 3)
    (hd12 : ∀ x, x ∈ p1.support → x ∈ p2.support → x = u ∨ x = v)
    (hd23 : ∀ x, x ∈ p2.support → x ∈ p3.support → x = u ∨ x = v)
    (hd13 : ∀ x, x ∈ p1.support → x ∈ p3.support → x = u ∨ x = v)
    (hgirth : GirthGe (VoltageLift G α) 7) :
    HasPower (VoltageLift G α) := by
  apply abelian_cover_theta_pow2_of_girth G α p1 p2 p3 4 (by omega)
    hp1 hp2 hp3 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    hd12 hd23 hd13 (by omega)
  intro x c hc
  have := hgirth x c hc
  omega

/-- Theorem 6: Every girth-`≥ 8` abelian cover of ANY graph containing `Θ(1,3,4)` has a simple `C₁₆`. -/
theorem abelian_cover_theta134_girth8_hasPower {V Γ : Type*} [AddCommGroup Γ]
    (G : SimpleGraph V) (α : SkewVoltage V Γ) {u v : V}
    (p1 p2 p3 : G.Walk u v)
    (hp1 : p1.IsPath) (hp2 : p2.IsPath) (hp3 : p3.IsPath)
    (hl1 : p1.length = 1) (hl2 : p2.length = 3) (hl3 : p3.length = 4)
    (hd12 : ∀ x, x ∈ p1.support → x ∈ p2.support → x = u ∨ x = v)
    (hd23 : ∀ x, x ∈ p2.support → x ∈ p3.support → x = u ∨ x = v)
    (hd13 : ∀ x, x ∈ p1.support → x ∈ p3.support → x = u ∨ x = v)
    (hgirth : GirthGe (VoltageLift G α) 8) :
    HasPower (VoltageLift G α) := by
  apply abelian_cover_theta_pow2_of_girth G α p1 p2 p3 4 (by omega)
    hp1 hp2 hp3 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    hd12 hd23 hd13 (by omega)
  intro x c hc
  have := hgirth x c hc
  omega

/-- Theorem 7: Every girth-`≥ 12` abelian cover of ANY graph containing `Θ(5,5,6)` has a simple `C₃₂`. -/
theorem abelian_cover_theta556_girth12_hasPower {V Γ : Type*} [AddCommGroup Γ]
    (G : SimpleGraph V) (α : SkewVoltage V Γ) {u v : V}
    (p1 p2 p3 : G.Walk u v)
    (hp1 : p1.IsPath) (hp2 : p2.IsPath) (hp3 : p3.IsPath)
    (hl1 : p1.length = 5) (hl2 : p2.length = 5) (hl3 : p3.length = 6)
    (hd12 : ∀ x, x ∈ p1.support → x ∈ p2.support → x = u ∨ x = v)
    (hd23 : ∀ x, x ∈ p2.support → x ∈ p3.support → x = u ∨ x = v)
    (hd13 : ∀ x, x ∈ p1.support → x ∈ p3.support → x = u ∨ x = v)
    (hgirth : GirthGe (VoltageLift G α) 12) :
    HasPower (VoltageLift G α) := by
  apply abelian_cover_theta_pow2_of_girth G α p1 p2 p3 5 (by omega)
    hp1 hp2 hp3 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    hd12 hd23 hd13 (by omega)
  intro x c hc
  have := hgirth x c hc
  omega

/-- Helper: for a non-nil walk `w : G.Walk a b`, its endpoint `b` lies in `w.support.tail`. -/
lemma end_mem_support_tail_of_pos {V : Type*} {G : SimpleGraph V} {a b : V}
    (w : G.Walk a b) (hpos : 1 ≤ w.length) : b ∈ w.support.tail := by
  cases w with
  | nil => simp at hpos
  | cons _ q =>
    simp only [Walk.support_cons, List.tail_cons]
    exact q.end_mem_support

/-- Helper: for any walk `w : G.Walk a b` and `x ∈ w.support`, if `x ≠ a` then `x ∈ w.support.tail`. -/
lemma mem_support_tail_of_ne_start {V : Type*} {G : SimpleGraph V} {a b : V}
    (w : G.Walk a b) {x : V} (hx : x ∈ w.support) (hne : x ≠ a) : x ∈ w.support.tail := by
  cases w with
  | nil =>
    simp at hx
    exact (hne hx).elim
  | cons _ _ =>
    simp only [Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | ht
    · exact (hne rfl).elim
    · exact ht

/-- Theorem 8 (Universal Abelian-Cover Barbell-Commutator Theorem):
For ANY barbell consisting of two vertex-disjoint simple cycles `c1 : G.Walk u u`, `c2 : G.Walk v v`
joined by an internally disjoint simple path `p : G.Walk u v` (`p.length ≥ 1`), if the cycle
voltages `w1 = walkVoltage α c1`, `w2 = walkVoltage α c2` satisfy `w1 ≠ 0`, `w2 ≠ 0`, `w1 ≠ w2`,
and `w1 + w2 ≠ 0`, then `VoltageLift G α` contains a SIMPLE CYCLE of length
`2 * (c1.length + c2.length + 2 * p.length)`. -/
theorem abelian_cover_barbell_commutator_simple {V Γ : Type*} [AddCommGroup Γ]
    (G : SimpleGraph V) (α : SkewVoltage V Γ) {u v : V}
    (c1 : G.Walk u u) (c2 : G.Walk v v) (p : G.Walk u v)
    (hc1 : c1.IsCycle) (hc2 : c2.IsCycle) (hp : p.IsPath) (hlp : 1 ≤ p.length)
    (hd12 : ∀ x, x ∈ c1.support → x ∉ c2.support)
    (hd1p : ∀ x, x ∈ c1.support → x ∈ p.support → x = u)
    (hd2p : ∀ x, x ∈ c2.support → x ∈ p.support → x = v)
    (hw1 : walkVoltage α c1 ≠ 0) (hw2 : walkVoltage α c2 ≠ 0)
    (hw12 : walkVoltage α c1 ≠ walkVoltage α c2)
    (hwsum : walkVoltage α c1 + walkVoltage α c2 ≠ 0) :
    ∃ w : (VoltageLift G α).Walk (u, 0) (u, 0),
      w.IsCycle ∧ w.length = 2 * (c1.length + c2.length + 2 * p.length) := by
  let w1 := walkVoltage α c1
  let w2 := walkVoltage α c2
  let wP := walkVoltage α p
  let b1 : (VoltageLift G α).Walk (u, 0) (u, w1) :=
    Walk.copy (liftWalk α c1 0) rfl (by simp [w1])
  let b2 : (VoltageLift G α).Walk (u, w1) (v, w1 + wP) :=
    Walk.copy (liftWalk α p w1) rfl (by simp [wP])
  let b3 : (VoltageLift G α).Walk (v, w1 + wP) (v, w1 + w2 + wP) :=
    Walk.copy (liftWalk α c2 (w1 + wP)) rfl (by simp only [w2]; congr 1; abel)
  let b4 : (VoltageLift G α).Walk (v, w1 + w2 + wP) (u, w1 + w2) :=
    Walk.copy (liftWalk α p (w1 + w2)).reverse (by simp [wP]) rfl
  let b5 : (VoltageLift G α).Walk (u, w1 + w2) (u, w2) :=
    Walk.copy (liftWalk α c1 w2).reverse (by simp only [w1]; congr 1; abel) rfl
  let b6 : (VoltageLift G α).Walk (u, w2) (v, w2 + wP) :=
    Walk.copy (liftWalk α p w2) rfl (by simp [wP])
  let b7 : (VoltageLift G α).Walk (v, w2 + wP) (v, wP) :=
    Walk.copy (liftWalk α c2 wP).reverse (by simp only [w2]; congr 1; abel) rfl
  let b8 : (VoltageLift G α).Walk (v, wP) (u, 0) :=
    Walk.copy (liftWalk α p 0).reverse (by simp [wP]) rfl
  let w : (VoltageLift G α).Walk (u, 0) (u, 0) :=
    b1.append (b2.append (b3.append (b4.append (b5.append (b6.append (b7.append b8))))))
  have hlen : w.length = 2 * (c1.length + c2.length + 2 * p.length) := by
    simp only [w, b1, b2, b3, b4, b5, b6, b7, b8, Walk.length_append, Walk.length_copy,
      Walk.length_reverse, liftWalk_length]
    omega
  refine ⟨w, ?_, hlen⟩
  have hc1_3 := hc1.three_le_length
  have hc2_3 := hc2.three_le_length
  apply isCycle_of_length_ge_three_nodup (by omega)
  have htail : w.support.tail =
      (liftWalk α c1 0).support.tail ++
      ((liftWalk α p w1).support.tail ++
      ((liftWalk α c2 (w1 + wP)).support.tail ++
      ((liftWalk α p (w1 + w2)).reverse.support.tail ++
      ((liftWalk α c1 w2).reverse.support.tail ++
      ((liftWalk α p w2).support.tail ++
      ((liftWalk α c2 wP).reverse.support.tail ++
      (liftWalk α p 0).reverse.support.tail)))))) := by
    simp only [w, b1, b2, b3, b4, b5, b6, b7, b8, walk_append_support_tail, Walk.support_copy]
  rw [htail]
  have cycle_tail_nodup : ∀ {z : V} (c : G.Walk z z) (hc : c.IsCycle) (g : Γ),
      (liftWalk α c g).support.tail.Nodup := by
    intro z c hc g
    have hmap : ((liftWalk α c g).support.tail.map Prod.fst).Nodup := by
      rw [liftWalk_support_tail_map_fst]; exact hc.support_nodup
    exact List.Nodup.of_map Prod.fst hmap
  have cycle_rev_tail_map_fst : ∀ {z : V} (c : G.Walk z z) (g : Γ),
      (liftWalk α c g).reverse.support.tail.map Prod.fst = c.reverse.support.tail := by
    intro z c g
    rw [List.map_tail, Walk.support_reverse, ← List.map_reverse, liftWalk_support_map_fst,
      ← Walk.support_reverse]
  have cycle_rev_tail_nodup : ∀ {z : V} (c : G.Walk z z) (hc : c.IsCycle) (g : Γ),
      (liftWalk α c g).reverse.support.tail.Nodup := by
    intro z c hc g
    have hmap : ((liftWalk α c g).reverse.support.tail.map Prod.fst).Nodup := by
      rw [cycle_rev_tail_map_fst]; exact hc.reverse.support_nodup
    exact List.Nodup.of_map Prod.fst hmap
  have cycle_tail_at_base : ∀ {z : V} (c : G.Walk z z) (hc : c.IsCycle) (g : Γ) {x : V × Γ},
      x ∈ (liftWalk α c g).support.tail → x.1 = z → x.2 = g + walkVoltage α c := by
    intro z c hc g x hx hxz
    have hnodup : ((liftWalk α c g).support.tail.map Prod.fst).Nodup := by
      rw [liftWalk_support_tail_map_fst]; exact hc.support_nodup
    have hend : (z, g + walkVoltage α c) ∈ (liftWalk α c g).support.tail :=
      end_mem_support_tail_of_pos (liftWalk α c g) (by rw [liftWalk_length]; have := hc.three_le_length; omega)
    exact congrArg Prod.snd (eq_of_mem_of_map_nodup hnodup hx hend hxz)
  have cycle_rev_tail_at_base : ∀ {z : V} (c : G.Walk z z) (hc : c.IsCycle) (g : Γ) {x : V × Γ},
      x ∈ (liftWalk α c g).reverse.support.tail → x.1 = z → x.2 = g := by
    intro z c hc g x hx hxz
    have hnodup : ((liftWalk α c g).reverse.support.tail.map Prod.fst).Nodup := by
      rw [cycle_rev_tail_map_fst]; exact hc.reverse.support_nodup
    have hend : (z, g) ∈ (liftWalk α c g).reverse.support.tail :=
      end_mem_support_tail_of_pos (liftWalk α c g).reverse
        (by rw [Walk.length_reverse, liftWalk_length]; have := hc.three_le_length; omega)
    exact congrArg Prod.snd (eq_of_mem_of_map_nodup hnodup hx hend hxz)
  have cycle_tail_rev_disj : ∀ {z : V} (c : G.Walk z z) (hc : c.IsCycle) {g₁ g₂ : Γ},
      g₁ ≠ g₂ → g₁ + walkVoltage α c ≠ g₂ →
      ∀ x ∈ (liftWalk α c g₁).support.tail, x ∉ (liftWalk α c g₂).reverse.support.tail := by
    intro z c hc g₁ g₂ hne1 hne2 x hx1 hx2
    by_cases hxz : x.1 = z
    · have s1 := cycle_tail_at_base c hc g₁ hx1 hxz
      have s2 := cycle_rev_tail_at_base c hc g₂ hx2 hxz
      exact hne2 (s1.symm.trans s2)
    · have hx2_supp : x ∈ (liftWalk α c g₂).support := mem_support_of_mem_reverse_tail hx2
      have hx2_tail : x ∈ (liftWalk α c g₂).support.tail :=
        mem_support_tail_of_ne_start (liftWalk α c g₂) hx2_supp (fun h => hxz (congrArg Prod.fst h))
      exact liftWalk_cycle_tail_disjoint_of_ne α c hc hne1 x hx1 hx2_tail
  have hn1 := cycle_tail_nodup c1 hc1 0
  have hn2 := (liftWalk_isPath α hp w1).support_nodup.tail
  have hn3 := cycle_tail_nodup c2 hc2 (w1 + wP)
  have hn4 := (liftWalk_isPath α hp (w1 + w2)).reverse.support_nodup.tail
  have hn5 := cycle_rev_tail_nodup c1 hc1 w2
  have hn6 := (liftWalk_isPath α hp w2).support_nodup.tail
  have hn7 := cycle_rev_tail_nodup c2 hc2 wP
  have hn8 := (liftWalk_isPath α hp 0).reverse.support_nodup.tail
  have c1_p_disj : ∀ (g1 g2 : Γ) {x}, x ∈ (liftWalk α c1 g1).support.tail →
      x ∈ (liftWalk α p g2).support.tail → False := by
    intro g1 g2 x h1 h2
    have hxu := hd1p x.1 (fst_mem_of_mem_liftWalk_support α c1 g1 (mem_support_of_mem_tail h1))
      (fst_mem_of_mem_liftWalk_support α p g2 (mem_support_of_mem_tail h2))
    exact fst_ne_start_of_mem_liftWalk_tail α p hp g2 h2 hxu
  have c1r_p_disj : ∀ (g1 g2 : Γ) {x}, x ∈ (liftWalk α c1 g1).reverse.support.tail →
      x ∈ (liftWalk α p g2).support.tail → False := by
    intro g1 g2 x h1 h2
    have hxu := hd1p x.1 (fst_mem_of_mem_liftWalk_support α c1 g1 (mem_support_of_mem_reverse_tail h1))
      (fst_mem_of_mem_liftWalk_support α p g2 (mem_support_of_mem_tail h2))
    exact fst_ne_start_of_mem_liftWalk_tail α p hp g2 h2 hxu
  have c2_pr_disj : ∀ (g1 g2 : Γ) {x}, x ∈ (liftWalk α c2 g1).support.tail →
      x ∈ (liftWalk α p g2).reverse.support.tail → False := by
    intro g1 g2 x h1 h2
    have hxv := hd2p x.1 (fst_mem_of_mem_liftWalk_support α c2 g1 (mem_support_of_mem_tail h1))
      (fst_mem_of_mem_liftWalk_support α p g2 (mem_support_of_mem_reverse_tail h2))
    exact fst_ne_end_of_mem_liftWalk_reverse_tail α p hp g2 h2 hxv
  have c2r_pr_disj : ∀ (g1 g2 : Γ) {x}, x ∈ (liftWalk α c2 g1).reverse.support.tail →
      x ∈ (liftWalk α p g2).reverse.support.tail → False := by
    intro g1 g2 x h1 h2
    have hxv := hd2p x.1 (fst_mem_of_mem_liftWalk_support α c2 g1 (mem_support_of_mem_reverse_tail h1))
      (fst_mem_of_mem_liftWalk_support α p g2 (mem_support_of_mem_reverse_tail h2))
    exact fst_ne_end_of_mem_liftWalk_reverse_tail α p hp g2 h2 hxv
  have c1_pr_disj : ∀ {g1 g2 : Γ}, g1 + w1 ≠ g2 →
      ∀ {x}, x ∈ (liftWalk α c1 g1).support.tail → x ∈ (liftWalk α p g2).reverse.support.tail → False := by
    intro g1 g2 hne x h1 h2
    have hxu := hd1p x.1 (fst_mem_of_mem_liftWalk_support α c1 g1 (mem_support_of_mem_tail h1))
      (fst_mem_of_mem_liftWalk_support α p g2 (mem_support_of_mem_reverse_tail h2))
    have s1 := cycle_tail_at_base c1 hc1 g1 h1 hxu
    have s2 := snd_eq_start_of_fst_eq_start α p hp g2 (mem_support_of_mem_reverse_tail h2) hxu
    exact hne (s1.symm.trans s2)
  have c1r_pr_disj : ∀ {g1 g2 : Γ}, g1 ≠ g2 →
      ∀ {x}, x ∈ (liftWalk α c1 g1).reverse.support.tail → x ∈ (liftWalk α p g2).reverse.support.tail → False := by
    intro g1 g2 hne x h1 h2
    have hxu := hd1p x.1 (fst_mem_of_mem_liftWalk_support α c1 g1 (mem_support_of_mem_reverse_tail h1))
      (fst_mem_of_mem_liftWalk_support α p g2 (mem_support_of_mem_reverse_tail h2))
    have s1 := cycle_rev_tail_at_base c1 hc1 g1 h1 hxu
    have s2 := snd_eq_start_of_fst_eq_start α p hp g2 (mem_support_of_mem_reverse_tail h2) hxu
    exact hne (s1.symm.trans s2)
  have c2_p_disj : ∀ {g1 g2 : Γ}, g1 + w2 ≠ g2 + wP →
      ∀ {x}, x ∈ (liftWalk α c2 g1).support.tail → x ∈ (liftWalk α p g2).support.tail → False := by
    intro g1 g2 hne x h1 h2
    have hxv := hd2p x.1 (fst_mem_of_mem_liftWalk_support α c2 g1 (mem_support_of_mem_tail h1))
      (fst_mem_of_mem_liftWalk_support α p g2 (mem_support_of_mem_tail h2))
    have s1 := cycle_tail_at_base c2 hc2 g1 h1 hxv
    have s2 := snd_eq_end_of_fst_eq_end α p hp g2 (mem_support_of_mem_tail h2) hxv
    exact hne (s1.symm.trans s2)
  have c2r_p_disj : ∀ {g1 g2 : Γ}, g1 ≠ g2 + wP →
      ∀ {x}, x ∈ (liftWalk α c2 g1).reverse.support.tail → x ∈ (liftWalk α p g2).support.tail → False := by
    intro g1 g2 hne x h1 h2
    have hxv := hd2p x.1 (fst_mem_of_mem_liftWalk_support α c2 g1 (mem_support_of_mem_reverse_tail h1))
      (fst_mem_of_mem_liftWalk_support α p g2 (mem_support_of_mem_tail h2))
    have s1 := cycle_rev_tail_at_base c2 hc2 g1 h1 hxv
    have s2 := snd_eq_end_of_fst_eq_end α p hp g2 (mem_support_of_mem_tail h2) hxv
    exact hne (s1.symm.trans s2)
  have c1_c2_disj : ∀ {x : V × Γ} {g1 g2 : Γ},
      x ∈ (liftWalk α c1 g1).support → x ∈ (liftWalk α c2 g2).support → False := by
    intro x g1 g2 h1 h2
    exact hd12 x.1 (fst_mem_of_mem_liftWalk_support α c1 g1 h1)
      (fst_mem_of_mem_liftWalk_support α c2 g2 h2)
  apply nodup_append_of_disjoint hn1
  · apply nodup_append_of_disjoint hn2
    · apply nodup_append_of_disjoint hn3
      · apply nodup_append_of_disjoint hn4
        · apply nodup_append_of_disjoint hn5
          · apply nodup_append_of_disjoint hn6
            · exact nodup_append_of_disjoint hn7 hn8 (fun x h7 h8 => c2r_pr_disj wP 0 h7 h8)
            · intro x h6 h78; simp only [List.mem_append] at h78
              rcases h78 with h7 | h8
              · exact c2r_p_disj (by intro h; exact hw2 (by have h0 := sub_eq_zero.mpr h; calc w2 = -(wP - (w2 + wP)) := by abel
                  _ = 0 := by rw [h0]; abel)) h7 h6
              · exact liftWalk_support_disjoint_of_ne α p hp hw2 x
                  (mem_support_of_mem_tail h6) (mem_support_of_mem_reverse_tail h8)
          · intro x h5 h678; simp only [List.mem_append] at h678
            rcases h678 with h6 | h7 | h8
            · exact c1r_p_disj w2 w2 h5 h6
            · exact c1_c2_disj (mem_support_of_mem_reverse_tail h5) (mem_support_of_mem_reverse_tail h7)
            · exact c1r_pr_disj hw2 h5 h8
        · intro x h4 h5678; simp only [List.mem_append] at h5678
          rcases h5678 with h5 | h6 | h7 | h8
          · exact c1r_pr_disj (by intro h; exact hw1 (by have h0 := sub_eq_zero.mpr h; calc w1 = -(w2 - (w1 + w2)) := by abel
              _ = 0 := by rw [h0]; abel)) h5 h4
          · exact liftWalk_support_disjoint_of_ne α p hp (by intro h; exact hw1 (by have h0 := sub_eq_zero.mpr h; calc w1 = (w1 + w2) - w2 := by abel
              _ = 0 := h0)) x
              (mem_support_of_mem_reverse_tail h4) (mem_support_of_mem_tail h6)
          · exact c2r_pr_disj wP (w1 + w2) h7 h4
          · exact liftWalk_support_disjoint_of_ne α p hp hwsum x
              (mem_support_of_mem_reverse_tail h4) (mem_support_of_mem_reverse_tail h8)
      · intro x h3 h45678; simp only [List.mem_append] at h45678
        rcases h45678 with h4 | h5 | h6 | h7 | h8
        · exact c2_pr_disj (w1 + wP) (w1 + w2) h3 h4
        · exact c1_c2_disj (mem_support_of_mem_reverse_tail h5) (mem_support_of_mem_tail h3)
        · exact c2_p_disj (by intro h; exact hw1 (by have h0 := sub_eq_zero.mpr h; calc w1 = (w1 + wP + w2) - (w2 + wP) := by abel
            _ = 0 := h0)) h3 h6
        · exact cycle_tail_rev_disj c2 hc2
            (by intro h; exact hw1 (by have h0 := sub_eq_zero.mpr h; calc w1 = (w1 + wP) - wP := by abel
            _ = 0 := h0))
            (by intro h; exact hwsum (by have h0 := sub_eq_zero.mpr h; calc w1 + w2 = (w1 + wP + w2) - wP := by abel
            _ = 0 := h0)) x h3 h7
        · exact c2_pr_disj (w1 + wP) 0 h3 h8
    · intro x h2 h345678; simp only [List.mem_append] at h345678
      rcases h345678 with h3 | h4 | h5 | h6 | h7 | h8
      · exact c2_p_disj (by intro h; exact hw2 (by have h0 := sub_eq_zero.mpr h; calc w2 = (w1 + wP + w2) - (w1 + wP) := by abel
          _ = 0 := h0)) h3 h2
      · exact liftWalk_support_disjoint_of_ne α p hp (by intro h; exact hw2 (by have h0 := sub_eq_zero.mpr h; calc w2 = -(w1 - (w1 + w2)) := by abel
          _ = 0 := by rw [h0]; abel)) x
          (mem_support_of_mem_tail h2) (mem_support_of_mem_reverse_tail h4)
      · exact c1r_p_disj w2 w1 h5 h2
      · exact liftWalk_support_disjoint_of_ne α p hp hw12 x
          (mem_support_of_mem_tail h2) (mem_support_of_mem_tail h6)
      · exact c2r_p_disj (by intro h; exact hw1 (by have h0 := sub_eq_zero.mpr h; calc w1 = -(wP - (w1 + wP)) := by abel
          _ = 0 := by rw [h0]; abel)) h7 h2
      · exact liftWalk_support_disjoint_of_ne α p hp hw1 x
          (mem_support_of_mem_tail h2) (mem_support_of_mem_reverse_tail h8)
  · intro x h1 h2345678; simp only [List.mem_append] at h2345678
    rcases h2345678 with h2 | h3 | h4 | h5 | h6 | h7 | h8
    · exact c1_p_disj 0 w1 h1 h2
    · exact c1_c2_disj (mem_support_of_mem_tail h1) (mem_support_of_mem_tail h3)
    · exact c1_pr_disj (by intro h; exact hw2 (by have h0 := sub_eq_zero.mpr h; calc w2 = -(0 + w1 - (w1 + w2)) := by abel
        _ = 0 := by rw [h0]; abel)) h1 h4
    · exact cycle_tail_rev_disj c1 hc1 hw2.symm (by simpa [zero_add] using hw12) x h1 h5
    · exact c1_p_disj 0 w2 h1 h6
    · exact c1_c2_disj (mem_support_of_mem_tail h1) (mem_support_of_mem_reverse_tail h7)
    · exact c1_pr_disj (by simpa [zero_add] using hw1) h1 h8

/-- Theorem 9: Barbell-commutator power-of-two forcing when `L1 + L2 + 2t = 2^(k-1)` (`k ≥ 4`). -/
theorem abelian_cover_barbell_pow2 {V Γ : Type*} [AddCommGroup Γ]
    (G : SimpleGraph V) (α : SkewVoltage V Γ) {u v : V}
    (c1 : G.Walk u u) (c2 : G.Walk v v) (p : G.Walk u v) (k : ℕ) (hk : 4 ≤ k)
    (hc1 : c1.IsCycle) (hc2 : c2.IsCycle) (hp : p.IsPath) (hlp : 1 ≤ p.length)
    (hd12 : ∀ x, x ∈ c1.support → x ∉ c2.support)
    (hd1p : ∀ x, x ∈ c1.support → x ∈ p.support → x = u)
    (hd2p : ∀ x, x ∈ c2.support → x ∈ p.support → x = v)
    (hw1 : walkVoltage α c1 ≠ 0) (hw2 : walkVoltage α c2 ≠ 0)
    (hw12 : walkVoltage α c1 ≠ walkVoltage α c2)
    (hwsum : walkVoltage α c1 + walkVoltage α c2 ≠ 0)
    (hsum : c1.length + c2.length + 2 * p.length = 2 ^ (k - 1)) :
    HasPower (VoltageLift G α) := by
  obtain ⟨w, hwc, hwl⟩ := abelian_cover_barbell_commutator_simple G α c1 c2 p
    hc1 hc2 hp hlp hd12 hd1p hd2p hw1 hw2 hw12 hwsum
  refine ⟨k, (u, 0), w, by omega, hwc, ?_⟩
  rw [hwl, hsum]
  have hk1 : k = (k - 1) + 1 := by omega
  conv_rhs => rw [hk1, pow_succ]
  ring

/-! ### Section 2: Pillar 2 — Tait 3-Edge-Coloring / Even 2-Factor Chord & Multi-Bridge Rigidity -/

lemma chord_creates_two_cycles {V : Type*} {G : SimpleGraph V} {u v : V}
    (p q : G.Walk u v) (hp : p.IsPath) (hq : q.IsPath)
    (hlp : 2 ≤ p.length) (hlq : 2 ≤ q.length) (hadj : G.Adj u v) :
    (∃ c1 : G.Walk u u, c1.IsCycle ∧ c1.length = p.length + 1) ∧
    (∃ c2 : G.Walk u u, c2.IsCycle ∧ c2.length = q.length + 1) := by
  have edge_path : (Walk.cons hadj Walk.nil : G.Walk u v).IsPath := by
    apply Walk.IsPath.mk'
    simp [G.ne_of_adj hadj]
  constructor
  · refine ⟨p.append (Walk.cons hadj Walk.nil).reverse, ?_, by simp⟩
    apply cycle_of_two_disjoint_paths p (Walk.cons hadj Walk.nil) hp edge_path
    · intro x _ hx2; simpa using hx2
    · simp; omega
  · refine ⟨q.append (Walk.cons hadj Walk.nil).reverse, ?_, by simp⟩
    apply cycle_of_two_disjoint_paths q (Walk.cons hadj Walk.nil) hq edge_path
    · intro x _ hx2; simpa using hx2
    · simp; omega

/-- Helper: bridging two vertex-disjoint simple paths `p : u1 → u2` and `q : v1 → v2` by two
edges `u1 ~ v1` and `u2 ~ v2` produces a simple cycle of length `p.length + q.length + 2`. -/
lemma cycle_of_two_disjoint_paths_bridged {V : Type*} (G : SimpleGraph V)
    {u1 u2 v1 v2 : V} (p : G.Walk u1 u2) (q : G.Walk v1 v2)
    (hp : p.IsPath) (hq : q.IsPath)
    (hlp : 1 ≤ p.length) (hlq : 1 ≤ q.length)
    (hd : ∀ z, z ∈ p.support → z ∉ q.support)
    (he1 : G.Adj u1 v1) (he2 : G.Adj u2 v2) :
    ∃ c : G.Walk u1 u1, c.IsCycle ∧ c.length = p.length + q.length + 2 := by
  let w : G.Walk u1 u1 := p.append (Walk.cons he2 (q.reverse.append (Walk.cons he1.symm Walk.nil)))
  refine ⟨w, ?_, ?_⟩
  · apply isCycle_of_length_ge_three_nodup
    · simp only [w, Walk.length_append, Walk.length_cons, Walk.length_reverse, Walk.length_nil]
      omega
    · have htail : w.support.tail = p.support.tail ++ (q.reverse.support ++ [u1]) := by
        simp only [w, walk_append_support_tail, Walk.support_cons, List.tail_cons,
          Walk.support_append, Walk.support_nil]
      rw [htail]
      have hqr : q.reverse.support.Nodup := by
        rw [Walk.support_reverse]; exact List.nodup_reverse.mpr hq.support_nodup
      apply nodup_append_of_disjoint hp.support_nodup.tail
      · apply nodup_append_of_disjoint hqr (List.nodup_singleton u1)
        intro z hz hzu
        simp only [List.mem_singleton] at hzu
        subst hzu
        rw [Walk.support_reverse, List.mem_reverse] at hz
        exact hd u1 p.start_mem_support hz
      · intro z hzp hzq
        simp only [List.mem_append, List.mem_singleton] at hzq
        rcases hzq with hzq | rfl
        · rw [Walk.support_reverse, List.mem_reverse] at hzq
          exact hd z (mem_support_of_mem_tail hzp) hzq
        · exact start_not_mem_support_tail_of_isPath hp hzp
  · simp only [w, Walk.length_append, Walk.length_cons, Walk.length_reverse, Walk.length_nil]
    omega

/-- Theorem 10: In any power-free graph, no `C₆` has an antipodal (distance-3) chord. -/
theorem c6_no_antipodal_chord_of_no_pow2 {V : Type*} (G : SimpleGraph V) (hno : ¬HasPower G)
    {u v : V} (p q : G.Walk u v) (hp : p.IsPath) (hq : q.IsPath)
    (hlp : p.length = 3) (hlq : q.length = 3) : ¬G.Adj u v := by
  intro hadj
  obtain ⟨⟨c1, hc1, hl1⟩, _⟩ := chord_creates_two_cycles p q hp hq (by omega) (by omega) hadj
  exact hno ⟨2, u, c1, by omega, hc1, by omega⟩

/-- Theorem 11: In any power-free graph, no `C₁₂` has ANY odd-distance chord (`d ∈ {3, 5, 7, 9}`). -/
theorem c12_no_odd_chord_of_no_pow2 {V : Type*} (G : SimpleGraph V) (hno : ¬HasPower G)
    {u v : V} (p q : G.Walk u v) (hp : p.IsPath) (hq : q.IsPath)
    (hsum : p.length + q.length = 12) (hlp : 2 ≤ p.length) (hlq : 2 ≤ q.length)
    (hodd : p.length % 2 = 1) : ¬G.Adj u v := by
  intro hadj
  obtain ⟨⟨c1, hc1, hl1⟩, ⟨c2, hc2, hl2⟩⟩ :=
    chord_creates_two_cycles p q hp hq hlp hlq hadj
  have hcases : p.length = 3 ∨ p.length = 5 ∨ p.length = 7 ∨ p.length = 9 := by omega
  rcases hcases with h | h | h | h
  · exact hno ⟨2, u, c1, by omega, hc1, by omega⟩
  · exact hno ⟨3, u, c2, by omega, hc2, by omega⟩
  · exact hno ⟨3, u, c1, by omega, hc1, by omega⟩
  · exact hno ⟨2, u, c2, by omega, hc2, by omega⟩

/-- Theorem 12 (Crossing-Chord 6-Cycle Theorem):
Two crossing chords `u ~ v` and `x ~ y` on a cycle partitioned into four internally disjoint paths
`pa : u → x`, `pb : x → v`, `pc : v → y`, `pd : y → u` force simple cycles of lengths
`pa.length + pc.length + 2` and `pb.length + pd.length + 2`. -/
theorem crossing_chords_six_cycles {V : Type*} (G : SimpleGraph V) {u x v y : V}
    (pa : G.Walk u x) (pb : G.Walk x v) (pc : G.Walk v y) (pd : G.Walk y u)
    (ha : pa.IsPath) (hb : pb.IsPath) (hc : pc.IsPath) (hd : pd.IsPath)
    (hla : 1 ≤ pa.length) (hlb : 1 ≤ pb.length) (hlc : 1 ≤ pc.length) (hld : 1 ≤ pd.length)
    (hdisj_ac : ∀ z, z ∈ pa.support → z ∉ pc.support)
    (hdisj_bd : ∀ z, z ∈ pb.support → z ∉ pd.support)
    (huv : G.Adj u v) (hxy : G.Adj x y) :
    (∃ c1 : G.Walk u u, c1.IsCycle ∧ c1.length = pa.length + pc.length + 2) ∧
    (∃ c2 : G.Walk x x, c2.IsCycle ∧ c2.length = pb.length + pd.length + 2) :=
  ⟨cycle_of_two_disjoint_paths_bridged G pa pc ha hc hla hlc hdisj_ac huv hxy,
   cycle_of_two_disjoint_paths_bridged G pb pd hb hd hlb hld hdisj_bd hxy huv.symm⟩

/-- Theorem 13 (Exact `C₁₀` Crossing-Chord Exclusion):
In any power-free graph, two antipodal (crossing) chords on a `C₁₀` are impossible (`C₄` or `C₈`). -/
theorem c10_no_two_antipodal_chords {V : Type*} (G : SimpleGraph V) (hno : ¬HasPower G)
    {u x v y : V}
    (pa : G.Walk u x) (pb : G.Walk x v) (pc : G.Walk v y) (pd : G.Walk y u)
    (ha : pa.IsPath) (hb : pb.IsPath) (hc : pc.IsPath) (hd : pd.IsPath)
    (hla : 1 ≤ pa.length) (hlb : 1 ≤ pb.length) (hlc : 1 ≤ pc.length) (hld : 1 ≤ pd.length)
    (hab5 : pa.length + pb.length = 5) (hbc5 : pb.length + pc.length = 5)
    (hcd5 : pc.length + pd.length = 5)
    (hdisj_ac : ∀ z, z ∈ pa.support → z ∉ pc.support)
    (hdisj_bd : ∀ z, z ∈ pb.support → z ∉ pd.support) :
    ¬(G.Adj u v ∧ G.Adj x y) := by
  rintro ⟨huv, hxy⟩
  obtain ⟨⟨c1, hc1, hl1⟩, ⟨c2, hc2, hl2⟩⟩ :=
    crossing_chords_six_cycles G pa pb pc pd ha hb hc hd hla hlb hlc hld hdisj_ac hdisj_bd huv hxy
  have hcases : pa.length = 1 ∨ pa.length = 2 ∨ pa.length = 3 ∨ pa.length = 4 := by omega
  rcases hcases with h | h | h | h
  · exact hno ⟨2, u, c1, by omega, hc1, by omega⟩
  · exact hno ⟨3, x, c2, by omega, hc2, by omega⟩
  · exact hno ⟨3, u, c1, by omega, hc1, by omega⟩
  · exact hno ⟨2, x, c2, by omega, hc2, by omega⟩

lemma two_bridges_four_cycles {V : Type*} (G : SimpleGraph V)
    {u1 u2 v1 v2 : V}
    (p1 p1' : G.Walk u1 u2) (q1 q1' : G.Walk v1 v2)
    (hp1 : p1.IsPath) (hp1' : p1'.IsPath) (hq1 : q1.IsPath) (hq1' : q1'.IsPath)
    (hlp1 : 1 ≤ p1.length) (hlp1' : 1 ≤ p1'.length) (hlq1 : 1 ≤ q1.length) (hlq1' : 1 ≤ q1'.length)
    (hdisj : ∀ z, (z ∈ p1.support ∨ z ∈ p1'.support) → z ∉ q1.support ∧ z ∉ q1'.support)
    (he1 : G.Adj u1 v1) (he2 : G.Adj u2 v2) :
    (∃ c : G.Walk u1 u1, c.IsCycle ∧ c.length = p1.length + q1.length + 2) ∧
    (∃ c : G.Walk u1 u1, c.IsCycle ∧ c.length = p1'.length + q1.length + 2) ∧
    (∃ c : G.Walk u1 u1, c.IsCycle ∧ c.length = p1.length + q1'.length + 2) ∧
    (∃ c : G.Walk u1 u1, c.IsCycle ∧ c.length = p1'.length + q1'.length + 2) :=
  ⟨cycle_of_two_disjoint_paths_bridged G p1 q1 hp1 hq1 hlp1 hlq1 (fun z hz => (hdisj z (Or.inl hz)).1) he1 he2,
   cycle_of_two_disjoint_paths_bridged G p1' q1 hp1' hq1 hlp1' hlq1 (fun z hz => (hdisj z (Or.inr hz)).1) he1 he2,
   cycle_of_two_disjoint_paths_bridged G p1 q1' hp1 hq1' hlp1 hlq1' (fun z hz => (hdisj z (Or.inl hz)).2) he1 he2,
   cycle_of_two_disjoint_paths_bridged G p1' q1' hp1' hq1' hlp1' hlq1' (fun z hz => (hdisj z (Or.inr hz)).2) he1 he2⟩

/-- Theorem 14 (Universal `C₅ ↔ C₅` Single-Bridge Theorem):
In ANY power-free graph, two vertex-disjoint `C₅`'s cannot have TWO independent bridge edges. -/
theorem two_disjoint_c5_at_most_one_bridge {V : Type*} (G : SimpleGraph V) (hno : ¬HasPower G)
    {u1 u2 v1 v2 : V}
    (p1 p1' : G.Walk u1 u2) (q1 q1' : G.Walk v1 v2)
    (hp1 : p1.IsPath) (hp1' : p1'.IsPath) (hq1 : q1.IsPath) (hq1' : q1'.IsPath)
    (hlp1 : 1 ≤ p1.length) (hlp1' : 1 ≤ p1'.length) (hlq1 : 1 ≤ q1.length) (hlq1' : 1 ≤ q1'.length)
    (hc5_1 : p1.length + p1'.length = 5) (hc5_2 : q1.length + q1'.length = 5)
    (hdisj : ∀ z, (z ∈ p1.support ∨ z ∈ p1'.support) → z ∉ q1.support ∧ z ∉ q1'.support) :
    ¬(G.Adj u1 v1 ∧ G.Adj u2 v2) := by
  rintro ⟨he1, he2⟩
  obtain ⟨⟨c1, hc1, hl1⟩, ⟨c2, hc2, hl2⟩, ⟨c3, hc3, hl3⟩, ⟨c4, hc4, hl4⟩⟩ :=
    two_bridges_four_cycles G p1 p1' q1 q1' hp1 hp1' hq1 hq1' hlp1 hlp1' hlq1 hlq1' hdisj he1 he2
  have h1 : p1.length = 1 ∨ p1.length = 2 ∨ p1.length = 3 ∨ p1.length = 4 := by omega
  have h2 : q1.length = 1 ∨ q1.length = 2 ∨ q1.length = 3 ∨ q1.length = 4 := by omega
  rcases h1 with a | a | a | a <;> rcases h2 with b | b | b | b
  · exact hno ⟨2, u1, c1, by omega, hc1, by omega⟩
  · exact hno ⟨3, u1, c2, by omega, hc2, by omega⟩
  · exact hno ⟨3, u1, c4, by omega, hc4, by omega⟩
  · exact hno ⟨2, u1, c3, by omega, hc3, by omega⟩
  · exact hno ⟨3, u1, c3, by omega, hc3, by omega⟩
  · exact hno ⟨3, u1, c4, by omega, hc4, by omega⟩
  · exact hno ⟨3, u1, c2, by omega, hc2, by omega⟩
  · exact hno ⟨3, u1, c1, by omega, hc1, by omega⟩
  · exact hno ⟨3, u1, c4, by omega, hc4, by omega⟩
  · exact hno ⟨3, u1, c3, by omega, hc3, by omega⟩
  · exact hno ⟨3, u1, c1, by omega, hc1, by omega⟩
  · exact hno ⟨3, u1, c2, by omega, hc2, by omega⟩
  · exact hno ⟨2, u1, c2, by omega, hc2, by omega⟩
  · exact hno ⟨3, u1, c1, by omega, hc1, by omega⟩
  · exact hno ⟨3, u1, c3, by omega, hc3, by omega⟩
  · exact hno ⟨2, u1, c4, by omega, hc4, by omega⟩

/-- Theorem 15 (`C₆ ↔ C₆` Equal-Distance Bridge Exclusion):
In ANY power-free graph, no two independent bridges between two vertex-disjoint `C₆`'s can have
equal cycle distance (`d1 = d2 ∈ {1, 2, 3}` forces `C₄` or `C₈`). -/
theorem two_disjoint_c6_no_equal_dist_bridges {V : Type*} (G : SimpleGraph V) (hno : ¬HasPower G)
    {u1 u2 v1 v2 : V}
    (p1 p1' : G.Walk u1 u2) (q1 q1' : G.Walk v1 v2)
    (hp1 : p1.IsPath) (hp1' : p1'.IsPath) (hq1 : q1.IsPath) (hq1' : q1'.IsPath)
    (hlp1 : 1 ≤ p1.length) (hlp1' : 1 ≤ p1'.length) (hlq1 : 1 ≤ q1.length) (hlq1' : 1 ≤ q1'.length)
    (hc6_1 : p1.length + p1'.length = 6) (hc6_2 : q1.length + q1'.length = 6)
    (heq : p1.length = q1.length ∨ p1.length = q1'.length)
    (hdisj : ∀ z, (z ∈ p1.support ∨ z ∈ p1'.support) → z ∉ q1.support ∧ z ∉ q1'.support) :
    ¬(G.Adj u1 v1 ∧ G.Adj u2 v2) := by
  rintro ⟨he1, he2⟩
  obtain ⟨⟨c1, hc1, hl1⟩, ⟨c2, hc2, hl2⟩, ⟨c3, hc3, hl3⟩, ⟨c4, hc4, hl4⟩⟩ :=
    two_bridges_four_cycles G p1 p1' q1 q1' hp1 hp1' hq1 hq1' hlp1 hlp1' hlq1 hlq1' hdisj he1 he2
  have h1 : p1.length = 1 ∨ p1.length = 2 ∨ p1.length = 3 ∨ p1.length = 4 ∨ p1.length = 5 := by omega
  rcases heq with heq | heq
  · rcases h1 with a | a | a | a | a
    · exact hno ⟨2, u1, c1, by omega, hc1, by omega⟩
    · exact hno ⟨3, u1, c2, by omega, hc2, by omega⟩
    · exact hno ⟨3, u1, c1, by omega, hc1, by omega⟩
    · exact hno ⟨3, u1, c2, by omega, hc2, by omega⟩
    · exact hno ⟨2, u1, c4, by omega, hc4, by omega⟩
  · rcases h1 with a | a | a | a | a
    · exact hno ⟨2, u1, c3, by omega, hc3, by omega⟩
    · exact hno ⟨3, u1, c1, by omega, hc1, by omega⟩
    · exact hno ⟨3, u1, c1, by omega, hc1, by omega⟩
    · exact hno ⟨3, u1, c1, by omega, hc1, by omega⟩
    · exact hno ⟨2, u1, c2, by omega, hc2, by omega⟩

/-- Theorem 16 (Bipartite `C₆ ↔ C₆` Two-Bridge Bound):
Any three independent bridges between two properly 2-colored `C₆`'s contain a pair at equal
cycle-distance 2 on both `C₆`'s (which forces `C₈` by Theorem 15). -/
theorem two_disjoint_c6_bipartite_at_most_two_bridges
    (col1 col2 : Fin 6 → Bool) (hproper1 : ∀ i : Fin 6, col1 i ≠ col1 (i + 1))
    (hproper2 : ∀ i : Fin 6, col2 i ≠ col2 (i + 1))
    (u1 u2 u3 v1 v2 v3 : Fin 6)
    (hu12 : u1 ≠ u2) (hu23 : u2 ≠ u3) (hu13 : u1 ≠ u3)
    (hv12 : v1 ≠ v2) (hv23 : v2 ≠ v3) (hv13 : v1 ≠ v3)
    (hbip : (col1 u1 = col2 v1 ∧ col1 u2 = col2 v2 ∧ col1 u3 = col2 v3) ∨
            (col1 u1 ≠ col2 v1 ∧ col1 u2 ≠ col2 v2 ∧ col1 u3 ≠ col2 v3)) :
    ∃ a b c d : Fin 6,
      ((a = u1 ∧ b = u2 ∧ c = v1 ∧ d = v2) ∨
       (a = u2 ∧ b = u3 ∧ c = v2 ∧ d = v3) ∨
       (a = u1 ∧ b = u3 ∧ c = v1 ∧ d = v3)) ∧
      ((a - b).val = 2 ∨ (b - a).val = 2) ∧
      ((c - d).val = 2 ∨ (d - c).val = 2) := by
  have hcol_dist2 : ∀ (col : Fin 6 → Bool), (∀ i : Fin 6, col i ≠ col (i + 1)) →
      ∀ x y : Fin 6, x ≠ y → col x = col y → (x - y).val = 2 ∨ (y - x).val = 2 := by
    intro col hpr x y hne hce
    have p0 : col 0 ≠ col 1 := hpr 0
    have p1 : col 1 ≠ col 2 := hpr 1
    have p2 : col 2 ≠ col 3 := hpr 2
    have p3 : col 3 ≠ col 4 := hpr 3
    have p4 : col 4 ≠ col 5 := hpr 4
    have e2 : col 2 = col 0 := by cases h0 : col 0 <;> cases h1 : col 1 <;> cases h2 : col 2 <;> simp_all
    have e3 : col 3 = col 1 := by cases h1 : col 1 <;> cases h2 : col 2 <;> cases h3 : col 3 <;> simp_all
    have e4 : col 4 = col 0 := by cases h0 : col 0 <;> cases h3 : col 3 <;> cases h4 : col 4 <;> simp_all
    have e5 : col 5 = col 1 := by cases h0 : col 0 <;> cases h1 : col 1 <;> cases h4 : col 4 <;> cases h5 : col 5 <;> simp_all
    fin_cases x <;> fin_cases y <;> simp_all <;> decide
  by_cases h12 : col1 u1 = col1 u2
  · refine ⟨u1, u2, v1, v2, Or.inl ⟨rfl, rfl, rfl, rfl⟩,
      hcol_dist2 col1 hproper1 u1 u2 hu12 h12,
      hcol_dist2 col2 hproper2 v1 v2 hv12 ?_⟩
    rcases hbip with ⟨e1, e2, _⟩ | ⟨e1, e2, _⟩
    · exact e1.symm.trans (h12.trans e2)
    · cases c1 : col1 u1 <;> cases c2 : col1 u2 <;> cases d1 : col2 v1 <;> cases d2 : col2 v2 <;> simp_all
  · by_cases h23 : col1 u2 = col1 u3
    · refine ⟨u2, u3, v2, v3, Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩),
        hcol_dist2 col1 hproper1 u2 u3 hu23 h23,
        hcol_dist2 col2 hproper2 v2 v3 hv23 ?_⟩
      rcases hbip with ⟨_, e2, e3⟩ | ⟨_, e2, e3⟩
      · exact e2.symm.trans (h23.trans e3)
      · cases c2 : col1 u2 <;> cases c3 : col1 u3 <;> cases d2 : col2 v2 <;> cases d3 : col2 v3 <;> simp_all
    · have h13 : col1 u1 = col1 u3 := by
        cases c1 : col1 u1 <;> cases c2 : col1 u2 <;> cases c3 : col1 u3 <;> simp_all
      refine ⟨u1, u3, v1, v3, Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩),
        hcol_dist2 col1 hproper1 u1 u3 hu13 h13,
        hcol_dist2 col2 hproper2 v1 v3 hv13 ?_⟩
      rcases hbip with ⟨e1, _, e3⟩ | ⟨e1, _, e3⟩
      · exact e1.symm.trans (h13.trans e3)
      · cases c1 : col1 u1 <;> cases c3 : col1 u3 <;> cases d1 : col2 v1 <;> cases d3 : col2 v3 <;> simp_all

/-- Theorem 17 (Tait Even `C₆`-Ring Arithmetic Power-of-Two Forcing — Unbounded `r`):
For EVERY even `r = 2 * m` (`m ≥ 1`), the cycle-length spectrum `{2*r + 4*j | 0 ≤ j ≤ r}` of a
ring of `r` disjoint `C₆`'s entered/exited at distance 1 ALWAYS contains a power of 2 `2^k` (`k ≥ 2`). -/
theorem tait_even_c6_ring_dist1_spectrum_hits_pow2 (m : ℕ) (hm : 1 ≤ m) :
    ∃ (k j : ℕ), 2 ≤ k ∧ j ≤ 2 * m ∧ 4 * m + 4 * j = 2 ^ k := by
  let s := Nat.log 2 (3 * m)
  have hs_le : 2 ^ s ≤ 3 * m := Nat.pow_log_le_self 2 (by omega)
  have hs_gt : 3 * m < 2 ^ (s + 1) := Nat.lt_pow_succ_log_self (by omega) (3 * m)
  have hm_le : m ≤ 2 ^ s := by
    have : 2 ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; ring
    omega
  refine ⟨s + 2, 2 ^ s - m, by omega, by omega, ?_⟩
  have hpow : 2 ^ (s + 2) = 4 * 2 ^ s := by rw [pow_add]; norm_num; ring
  omega

end E64Wave8Agent5
