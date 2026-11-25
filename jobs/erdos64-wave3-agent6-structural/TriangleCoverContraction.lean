import Core
import Leaves
import PairedShadow

/-!
Erdos 64 (Wave 3, Agent #6): Triangle-Cover Contraction Theorem.
First Lean 4.36.0 formalization of Wave 1's flagship C/S/H-T-* exclusion (all finite orders,
standard axioms only):
No MinimalBad(G) admits a nonempty collection of pairwise vertex-disjoint degree-3 triangles
{T_i : i ∈ I} whose complement R = V \ ⋃_i T_i has at most one internal edge.
In particular, no MinimalBad(G) admits a triangle-factor (no truncated simple cubic graph).
-/

namespace E64TriangleCover
open SimpleGraph Erdos64Closure E64Core E64Leaves Erdos64Paired
universe u

/-- A collection of pairwise vertex-disjoint degree-3 triangles in `G`, indexed by `I`. -/
structure TriangleFamily {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (I : Type u) [Fintype I] where
  v : I → Fin 3 → V
  inj : Function.Injective (fun p : I × Fin 3 => v p.1 p.2)
  tri : ∀ (i : I) (a b : Fin 3), a ≠ b → G.Adj (v i a) (v i b)
  deg3 : ∀ (i : I) (a : Fin 3), G.degree (v i a) = 3

namespace TriangleFamily

variable {V I : Type u} [Fintype V] [Fintype I] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Predicate: `x` lies in one of the triangles of `F`. -/
def inTri (F : TriangleFamily G I) (x : V) : Prop :=
  ∃ (i : I) (a : Fin 3), F.v i a = x

/-- Residual vertex type `R = V \ ⋃_i T_i`. -/
abbrev Res (F : TriangleFamily G I) := {x : V // ¬ F.inTri x}

/-- Contracted vertex type `W = I ⊕ R`. -/
abbrev ContrV (F : TriangleFamily G I) := I ⊕ F.Res

/-- Projection map `π : V → I ⊕ R`. -/
noncomputable def proj (F : TriangleFamily G I) (x : V) : F.ContrV :=
  open Classical in
  if h : F.inTri x then Sum.inl (Classical.choose h)
  else Sum.inr ⟨x, h⟩

theorem proj_tri (F : TriangleFamily G I) (i : I) (a : Fin 3) :
    F.proj (F.v i a) = Sum.inl i := by
  classical
  have h : F.inTri (F.v i a) := ⟨i, a, rfl⟩
  unfold proj
  simp only [h, ↓reduceDIte]
  congr 1
  obtain ⟨b, hb⟩ := Classical.choose_spec h
  have := @F.inj (Classical.choose h, b) (i, a) hb
  exact congrArg Prod.fst this

theorem proj_res (F : TriangleFamily G I) (r : F.Res) :
    F.proj r.1 = Sum.inr r := by
  classical
  unfold proj
  simp [r.2]

/-- Helper: injectivity of `F.v i` on `Fin 3`. -/
theorem v_ne_of_ne (F : TriangleFamily G I) (i : I) {a b : Fin 3} (hab : a ≠ b) :
    F.v i a ≠ F.v i b := by
  intro h
  have := @F.inj (i, a) (i, b) h
  exact hab (congrArg Prod.snd this)

/-- Helper: for any distinct `a, b : Fin 3`, there is a third `c : Fin 3` distinct from both. -/
theorem exists_third_fin3 {a b : Fin 3} (hab : a ≠ b) : ∃ c : Fin 3, a ≠ c ∧ b ≠ c := by
  revert hab
  fin_cases a <;> fin_cases b <;> decide

/-- Each vertex `F.v i a` has a unique external neighbor outside triangle `i`. -/
theorem unique_ext_neighbor (F : TriangleFamily G I) (i : I) (a : Fin 3) :
    ∃! y : V, G.Adj (F.v i a) y ∧ F.proj y ≠ Sum.inl i := by
  classical
  let b : Fin 3 := a + 1
  let c : Fin 3 := a + 2
  have hab : a ≠ b := by fin_cases a <;> decide
  have hac : a ≠ c := by fin_cases a <;> decide
  have hbc : b ≠ c := by fin_cases a <;> decide
  have hvbc : F.v i b ≠ F.v i c := F.v_ne_of_ne i hbc
  have hex : ∃ y : V, G.Adj (F.v i a) y ∧ y ≠ F.v i b ∧ y ≠ F.v i c := by
    by_contra h
    push Not at h
    have hs : G.neighborFinset (F.v i a) ⊆ ({F.v i b, F.v i c} : Finset V) := by
      intro x hx
      have hadj := (G.mem_neighborFinset _ x).mp hx
      by_cases hxb : x = F.v i b
      · simp [hxb]
      · simp [h x hadj hxb]
    have hc := Finset.card_le_card hs
    rw [G.card_neighborFinset_eq_degree, F.deg3 i a] at hc
    have h2 : ({F.v i b, F.v i c} : Finset V).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨y, hay, hyb, hyc⟩ := hex
  have hy_out : F.proj y ≠ Sum.inl i := by
    intro hp
    by_cases h : F.inTri y
    · unfold proj at hp
      simp only [h, ↓reduceDIte] at hp
      have hi : Classical.choose h = i := Sum.inl.inj hp
      obtain ⟨d, hd⟩ := Classical.choose_spec h
      rw [hi] at hd
      have hda : d = a ∨ d = b ∨ d = c := by fin_cases a <;> fin_cases d <;> decide
      rcases hda with rfl | rfl | rfl
      · exact G.ne_of_adj hay hd
      · exact hyb hd.symm
      · exact hyc hd.symm
    · unfold proj at hp
      simp only [h, ↓reduceDIte] at hp
      cases hp
  refine ⟨y, ⟨hay, hy_out⟩, fun z ⟨haz, hz_out⟩ => ?_⟩
  by_contra hzy
  have hzb : z ≠ F.v i b := fun h => hz_out (by rw [h, F.proj_tri])
  have hzc : z ≠ F.v i c := fun h => hz_out (by rw [h, F.proj_tri])
  have hs : ({F.v i b, F.v i c, y, z} : Finset V) ⊆ G.neighborFinset (F.v i a) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact (G.mem_neighborFinset _ _).mpr (F.tri i a b hab)
    · exact (G.mem_neighborFinset _ _).mpr (F.tri i a c hac)
    · exact (G.mem_neighborFinset _ _).mpr hay
    · exact (G.mem_neighborFinset _ _).mpr haz
  have hc := Finset.card_le_card hs
  have h4 : ({F.v i b, F.v i c, y, z} : Finset V).card = 4 := by
    simp [hvbc, Ne.symm hyb, Ne.symm hyc, Ne.symm hzb, Ne.symm hzc, Ne.symm hzy]
  rw [h4, G.card_neighborFinset_eq_degree, F.deg3 i a] at hc
  omega

/-- Contracted simple graph `H` on `I ⊕ R`. -/
noncomputable def contrGraph (F : TriangleFamily G I) : SimpleGraph F.ContrV where
  Adj u v := u ≠ v ∧ ∃ x y : V, F.proj x = u ∧ F.proj y = v ∧ G.Adj x y
  symm := ⟨by
    rintro u v ⟨hne, x, y, hx, hy, hadj⟩
    exact ⟨hne.symm, y, x, hy, hx, hadj.symm⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

/-- Helper: if `F.proj x = Sum.inl i`, then `∃ a, F.v i a = x`. -/
theorem eq_v_of_proj_inl (F : TriangleFamily G I) {x : V} {i : I}
    (hx : F.proj x = Sum.inl i) : ∃ a : Fin 3, F.v i a = x := by
  classical
  by_cases h : F.inTri x
  · unfold proj at hx
    simp only [h, ↓reduceDIte] at hx
    obtain ⟨a, ha⟩ := Classical.choose_spec h
    exact ⟨a, (Sum.inl.inj hx) ▸ ha⟩
  · unfold proj at hx
    simp only [h, ↓reduceDIte] at hx
    cases hx

/-- Helper: if `F.proj x = Sum.inr r`, then `x = r.1`. -/
theorem eq_val_of_proj_inr (F : TriangleFamily G I) {x : V} {r : F.Res}
    (hx : F.proj x = Sum.inr r) : x = r.1 := by
  classical
  by_cases h : F.inTri x
  · unfold proj at hx
    simp only [h, ↓reduceDIte] at hx
    cases hx
  · unfold proj at hx
    simp only [h, ↓reduceDIte] at hx
    exact congrArg Subtype.val (Sum.inr.inj hx)

/-- In a power-free graph, no two distinct vertices of triangle `i` have external neighbors
    projecting to the same vertex of `I ⊕ R` (otherwise a C4 arises). -/
theorem no_parallel_from_tri (F : TriangleFamily G I) (hfree : ¬ HasPower G)
    (i : I) {a b : Fin 3} (hab : a ≠ b) {y₁ y₂ : V}
    (h1 : G.Adj (F.v i a) y₁) (h2 : G.Adj (F.v i b) y₂)
    (ho1 : F.proj y₁ ≠ Sum.inl i) (ho2 : F.proj y₂ ≠ Sum.inl i)
    (heq : F.proj y₁ = F.proj y₂) : False := by
  obtain ⟨c, hac, hbc⟩ := exists_third_fin3 hab
  have hva_vb : F.v i a ≠ F.v i b := F.v_ne_of_ne i hab
  have hva_vc : F.v i a ≠ F.v i c := F.v_ne_of_ne i hac
  have hvb_vc : F.v i b ≠ F.v i c := F.v_ne_of_ne i hbc
  have hy1_not_i : ∀ d : Fin 3, y₁ ≠ F.v i d := fun d h => ho1 (by rw [h, F.proj_tri])
  have hy2_not_i : ∀ d : Fin 3, y₂ ≠ F.v i d := fun d h => ho2 (by rw [h, F.proj_tri])
  by_cases hy12 : y₁ = y₂
  · subst hy12
    exact hfree (rectangle_power G hva_vc hva_vb (hy1_not_i a).symm
      hvb_vc.symm (hy1_not_i c).symm (hy1_not_i b).symm
      (F.tri i a c hac) (F.tri i c b hbc.symm) h2 h1.symm)
  · have hadj12 : G.Adj y₁ y₂ := by
      cases hp1 : F.proj y₁ with
      | inl j =>
        obtain ⟨d₁, hd₁⟩ := F.eq_v_of_proj_inl hp1
        obtain ⟨d₂, hd₂⟩ := F.eq_v_of_proj_inl (heq.symm.trans hp1)
        have hd12 : d₁ ≠ d₂ := fun h => hy12 (hd₁.symm.trans (h ▸ hd₂))
        rw [← hd₁, ← hd₂]
        exact F.tri j d₁ d₂ hd12
      | inr r =>
        have h1' := F.eq_val_of_proj_inr hp1
        have h2' := F.eq_val_of_proj_inr (heq.symm.trans hp1)
        exact False.elim (hy12 (h1'.trans h2'.symm))
    exact hfree (rectangle_power G hva_vb (hy2_not_i a).symm (hy1_not_i a).symm
      (hy2_not_i b).symm (hy1_not_i b).symm (Ne.symm hy12)
      (F.tri i a b hab) h2 hadj12.symm h1.symm)

/-- Every triangle vertex `Sum.inl i` has degree exactly 3 in `contrGraph`. -/
theorem contr_degree_tri (F : TriangleFamily G I) (hfree : ¬ HasPower G)
    [Fintype F.ContrV] [DecidableRel F.contrGraph.Adj] (i : I) :
    F.contrGraph.degree (Sum.inl i) = 3 := by
  classical
  let extN : Fin 3 → V := fun a => Classical.choose (F.unique_ext_neighbor i a).exists
  have hextN : ∀ a, G.Adj (F.v i a) (extN a) ∧ F.proj (extN a) ≠ Sum.inl i :=
    fun a => Classical.choose_spec (F.unique_ext_neighbor i a).exists
  let f : Fin 3 → F.contrGraph.neighborSet (Sum.inl i) := fun a =>
    ⟨F.proj (extN a), ⟨(hextN a).2.symm, F.v i a, extN a, F.proj_tri i a, rfl, (hextN a).1⟩⟩
  have hfinj : Function.Injective f := by
    intro a b heq
    by_contra hab
    exact F.no_parallel_from_tri hfree i hab (hextN a).1 (hextN b).1 (hextN a).2 (hextN b).2
      (congrArg Subtype.val heq)
  have hfsurj : Function.Surjective f := by
    rintro ⟨q, hne, x, y, hx, hy, hxy⟩
    obtain ⟨a, ha⟩ := F.eq_v_of_proj_inl hx
    have hy_out : F.proj y ≠ Sum.inl i := fun h => hne (hy.symm.trans h).symm
    have hy_eq : y = extN a := (F.unique_ext_neighbor i a).unique ⟨ha ▸ hxy, hy_out⟩ (hextN a)
    exact ⟨a, Subtype.ext (by simp [f, ← hy_eq, hy])⟩
  have hc := Fintype.card_congr (Equiv.ofBijective f ⟨hfinj, hfsurj⟩)
  rw [SimpleGraph.card_neighborSet_eq_degree, Fintype.card_fin] at hc
  exact hc.symm

/-- Every residual vertex `Sum.inr r` keeps its exact degree `G.degree r.1` in `contrGraph`. -/
theorem contr_degree_res (F : TriangleFamily G I) (hfree : ¬ HasPower G)
    [Fintype F.ContrV] [DecidableRel F.contrGraph.Adj] (r : F.Res) :
    F.contrGraph.degree (Sum.inr r) = G.degree r.1 := by
  classical
  let f : G.neighborSet r.1 → F.contrGraph.neighborSet (Sum.inr r) := fun u =>
    ⟨F.proj u.1, ⟨fun heq => by
      exact (G.ne_of_adj u.2) (F.eq_val_of_proj_inr heq.symm).symm,
      r.1, u.1, F.proj_res r, rfl, u.2⟩⟩
  have hfinj : Function.Injective f := by
    intro u₁ u₂ heq
    apply Subtype.ext
    by_contra hne
    have hp : F.proj u₁.1 = F.proj u₂.1 := congrArg Subtype.val heq
    cases hp1 : F.proj u₁.1 with
    | inl j =>
      obtain ⟨a₁, ha₁⟩ := F.eq_v_of_proj_inl hp1
      obtain ⟨a₂, ha₂⟩ := F.eq_v_of_proj_inl (hp.symm.trans hp1)
      have ha12 : a₁ ≠ a₂ := fun h => hne (ha₁.symm.trans (h ▸ ha₂))
      have hro : F.proj r.1 ≠ Sum.inl j := by rw [F.proj_res r]; intro h; cases h
      exact F.no_parallel_from_tri hfree j ha12
        (ha₁ ▸ u₁.2.symm) (ha₂ ▸ u₂.2.symm) hro hro rfl
    | inr r' =>
      have h1' := F.eq_val_of_proj_inr hp1
      have h2' := F.eq_val_of_proj_inr (hp.symm.trans hp1)
      exact hne (h1'.trans h2'.symm)
  have hfsurj : Function.Surjective f := by
    rintro ⟨q, _, x, y, hx, hy, hxy⟩
    have hxr : x = r.1 := F.eq_val_of_proj_inr hx
    exact ⟨⟨y, hxr ▸ hxy⟩, Subtype.ext hy⟩
  have hc := Fintype.card_congr (Equiv.ofBijective f ⟨hfinj, hfsurj⟩)
  rw [SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.card_neighborSet_eq_degree] at hc
  exact hc.symm

/-- Strict cardinality drop: `|I ⊕ R| < |V|` whenever `Nonempty I`. -/
theorem card_contr_lt (F : TriangleFamily G I) [Fintype F.ContrV] (hI : Nonempty I) :
    Fintype.card F.ContrV < Fintype.card V := by
  classical
  let _ : Fintype F.Res := Subtype.fintype (fun x => ¬ F.inTri x)
  have e : (I × Fin 3) ⊕ F.Res ≃ V :=
    { toFun := Sum.elim (fun p => F.v p.1 p.2) Subtype.val
      invFun := fun x =>
        if h : F.inTri x then
          Sum.inl (Classical.choose h, Classical.choose (Classical.choose_spec h))
        else Sum.inr ⟨x, h⟩
      left_inv := by
        rintro (⟨i, a⟩ | r)
        · have h : F.inTri (F.v i a) := ⟨i, a, rfl⟩
          simp only [Sum.elim_inl, h, ↓reduceDIte]
          congr 1
          have hspec := Classical.choose_spec (Classical.choose_spec h)
          exact @F.inj (Classical.choose h, Classical.choose (Classical.choose_spec h)) (i, a) hspec
        · simp only [Sum.elim_inr, r.2, ↓reduceDIte]
      right_inv := by
        intro x
        by_cases h : F.inTri x
        · simp [h]
          exact Classical.choose_spec (Classical.choose_spec h)
        · simp [h] }
  have hc := Fintype.card_congr e
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] at hc
  have hsum : Fintype.card F.ContrV = Fintype.card I + Fintype.card F.Res := by
    convert @Fintype.card_sum I F.Res _ _
  have hpos : 0 < Fintype.card I := Fintype.card_pos_iff.mpr hI
  omega

/-- Extract the left component of a sum as an `Option`. -/
def getInl {α β : Type*} : α ⊕ β → Option α
  | Sum.inl i => some i
  | Sum.inr _ => none

/-- Vertex-weight function for cycle doubling. -/
def triWt {α β : Type*} [DecidableEq α] (S_list : List α) : α ⊕ β → ℕ
  | Sum.inr _ => 0
  | Sum.inl i => if i ∈ S_list then 2 else 1

/-- Helper list lemma: `filterMap getInl` has the same length as `filter Sum.isLeft`. -/
theorem filterMap_inl_length {α β : Type*} (l : List (α ⊕ β)) :
    (l.filterMap getInl).length = (l.filter Sum.isLeft).length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    cases x with
    | inl _ => simp only [List.filterMap_cons, getInl, List.filter_cons, Sum.isLeft_inl, ↓reduceIte, List.length_cons, ih]
    | inr _ => simp only [List.filterMap_cons, getInl, List.filter_cons, Sum.isLeft_inr, Bool.false_eq_true, ↓reduceIte, ih]

/-- Helper list lemma: `filter Sum.isRight` + `filter Sum.isLeft` = total length. -/
theorem filter_right_add_left {α β : Type*} (l : List (α ⊕ β)) :
    (l.filter Sum.isRight).length + (l.filter Sum.isLeft).length = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    cases x with
    | inl _ => simp only [List.filter_cons, Sum.isRight_inl, Sum.isLeft_inl, Bool.false_eq_true,
        ↓reduceIte, List.length_cons]; omega
    | inr _ => simp only [List.filter_cons, Sum.isRight_inr, Sum.isLeft_inr, Bool.false_eq_true,
        ↓reduceIte, List.length_cons]; omega

/-- Helper list lemma: `filterMap getInl` preserves `Nodup`. -/
theorem filterMap_inl_nodup {α β : Type*} {l : List (α ⊕ β)} (hnd : l.Nodup) :
    (l.filterMap getInl).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    rw [List.nodup_cons] at hnd
    cases x with
    | inr _ => exact ih hnd.2
    | inl i =>
      simp only [List.filterMap_cons, getInl]
      rw [List.nodup_cons]
      refine ⟨?_, ih hnd.2⟩
      intro hm
      obtain ⟨y, hy, hyi⟩ := List.mem_filterMap.mp hm
      cases y with
      | inr _ => simp [getInl] at hyi
      | inl j => simp [getInl] at hyi; subst hyi; exact hnd.1 hy

/-- Helper list lemma: sum of weights along a list of `α ⊕ β`. -/
theorem sum_wt_split {α β : Type*} [DecidableEq α] (S_list : List α) (l : List (α ⊕ β)) :
    (l.map (triWt S_list)).sum =
      (l.filterMap getInl).length +
      ((l.filterMap getInl).filter (fun i => decide (i ∈ S_list))).length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    cases x with
    | inr _ => simp [triWt, getInl, ih]
    | inl i =>
      by_cases hi : i ∈ S_list
      · simp [triWt, getInl, hi, ih]; omega
      · simp [triWt, getInl, hi, ih]; omega

/-- Unique bridge edge in `G` lifting an edge `u - v` of `contrGraph` when `G` is power-free. -/
theorem bridge_edge_exists (F : TriangleFamily G I) {u v : F.ContrV}
    (h : F.contrGraph.Adj u v) :
    ∃ x y : V, F.proj x = u ∧ F.proj y = v ∧ G.Adj x y := h.2

/-- Lift a simple cycle of length `2^k` in `contrGraph` to a simple cycle of length `2^(k+1)` in `G`
    whenever the number of residual vertices `r` on the cycle satisfies `r ≤ t`. -/
theorem lift_cycle_double (F : TriangleFamily G I)
    {k : ℕ} (hk : 2 ≤ k) {q₀ : F.ContrV} (c : F.contrGraph.Walk q₀ q₀)
    (hc : c.IsCycle) (hlen : c.length = 2 ^ k)
    (hcount : (c.support.tail.filter Sum.isRight).length ≤
              (c.support.tail.filter Sum.isLeft).length) : HasPower G := by
  classical
  have hge4 : 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide : 0 < 2) hk
  let outV : (u v : F.ContrV) → F.contrGraph.Adj u v → V :=
    fun _ _ h => Classical.choose h.2
  let inV : (u v : F.ContrV) → F.contrGraph.Adj u v → V :=
    fun _ _ h => Classical.choose (Classical.choose_spec h.2)
  have hbridge : ∀ {u v : F.ContrV} (h : F.contrGraph.Adj u v),
      F.proj (outV u v h) = u ∧ F.proj (inV u v h) = v ∧ G.Adj (outV u v h) (inV u v h) :=
    fun h => Classical.choose_spec (Classical.choose_spec h.2)
  let L_tri : List I := c.support.tail.filterMap getInl
  have hL_len : L_tri.length = (c.support.tail.filter Sum.isLeft).length :=
    filterMap_inl_length c.support.tail
  let r := (c.support.tail.filter Sum.isRight).length
  let S_list : List I := L_tri.take r
  have hS_len : S_list.length = r := by
    rw [List.length_take, hL_len]
    exact Nat.min_eq_left hcount
  have htri_path : ∀ (i : I) (x y : V), F.proj x = Sum.inl i → F.proj y = Sum.inl i → x ≠ y →
      ∃ p : G.Walk x y, p.IsPath ∧
        (p.length = if i ∈ S_list then 2 else 1) ∧
        (∀ z ∈ p.support, F.proj z = Sum.inl i) := by
    intro i x y hx hy hxy
    obtain ⟨a, ha⟩ := F.eq_v_of_proj_inl hx
    obtain ⟨b, hb⟩ := F.eq_v_of_proj_inl hy
    have hab : a ≠ b := fun h => hxy (ha.symm.trans (h ▸ hb))
    by_cases hS : i ∈ S_list
    · obtain ⟨c3, hac, hbc⟩ := exists_third_fin3 hab
      have hadj1 : G.Adj x (F.v i c3) := ha ▸ F.tri i a c3 hac
      have hadj2 : G.Adj (F.v i c3) y := hb ▸ F.tri i c3 b hbc.symm
      let p : G.Walk x y := .cons hadj1 (.cons hadj2 .nil)
      have hxc : x ≠ F.v i c3 := G.ne_of_adj hadj1
      have hcy : F.v i c3 ≠ y := G.ne_of_adj hadj2
      refine ⟨p, Walk.IsPath.mk' (by simp [p, hxc, hxy, hcy]), by simp [p, hS], ?_⟩
      intro z hz
      simp [p] at hz
      rcases hz with rfl | rfl | rfl
      · rw [← ha, F.proj_tri]
      · exact F.proj_tri i c3
      · rw [← hb, F.proj_tri]
    · have hadj : G.Adj x y := ha ▸ hb ▸ F.tri i a b hab
      let p : G.Walk x y := .cons hadj .nil
      refine ⟨p, Walk.IsPath.mk' (by simp [p, hxy]), by simp [p, hS], ?_⟩
      intro z hz
      simp [p] at hz
      rcases hz with rfl | rfl
      · rw [← ha, F.proj_tri]
      · rw [← hb, F.proj_tri]
  have hres_eq : ∀ (u : F.Res) (x y : V), F.proj x = Sum.inr u → F.proj y = Sum.inr u → x = y := by
    intro u x y hx hy
    exact (F.eq_val_of_proj_inr hx).trans (F.eq_val_of_proj_inr hy).symm
  have hdistinct_ports : ∀ (i : I) {q₁ q₂ : F.ContrV} (hne : q₁ ≠ q₂)
      (h1 : F.contrGraph.Adj q₁ (Sum.inl i)) (h2 : F.contrGraph.Adj (Sum.inl i) q₂),
      inV q₁ (Sum.inl i) h1 ≠ outV (Sum.inl i) q₂ h2 := by
    intro i q₁ q₂ hne h1 h2 heq
    have hb1 := hbridge h1
    have hb2 := hbridge h2
    obtain ⟨a, ha⟩ := F.eq_v_of_proj_inl hb1.2.1
    have h1' : G.Adj (F.v i a) (outV q₁ (Sum.inl i) h1) := ha ▸ hb1.2.2.symm
    have h2' : G.Adj (F.v i a) (inV (Sum.inl i) q₂ h2) := (ha.trans heq) ▸ hb2.2.2
    have ho1 : F.proj (outV q₁ (Sum.inl i) h1) ≠ Sum.inl i := by rw [hb1.1]; exact h1.1
    have ho2 : F.proj (inV (Sum.inl i) q₂ h2) ≠ Sum.inl i := by rw [hb2.2.1]; exact h2.1.symm
    have heqy := (F.unique_ext_neighbor i a).unique ⟨h1', ho1⟩ ⟨h2', ho2⟩
    exact hne (hb1.1.symm.trans ((congrArg F.proj heqy).trans hb2.2.1))
  let wt : F.ContrV → ℕ := triWt S_list
  cases hce : c with
  | nil =>
    rw [hce] at hlen; simp at hlen; omega
  | @cons _ q₁ _ h₁ q =>
    have hqpath : q.IsPath := by
      apply Walk.IsPath.mk'
      have hsn := hc.support_nodup
      rw [hce, Walk.support_cons, List.tail_cons] at hsn
      exact hsn
    have hqlen : q.length + 1 = 2 ^ k := by
      have := congrArg Walk.length hce; simp at this; omega
    have hlift_path : ∀ {a b : F.ContrV} (p : F.contrGraph.Walk a b), p.IsPath →
        ∀ (x_in : V) (hx_in : F.proj x_in = a)
          (hport : ∀ {c' : F.ContrV} (h : F.contrGraph.Adj a c') (r : F.contrGraph.Walk c' b),
            p = .cons h r → a.isLeft → x_in ≠ outV a c' h)
          (x_out : V) (hx_out : F.proj x_out = b)
          (hport_end : ∀ {c' : F.ContrV} (h : F.contrGraph.Adj c' b) (r : F.contrGraph.Walk a c'),
            p = r.append (.cons h .nil) → b.isLeft → inV c' b h ≠ x_out)
          (hport_nil : p.Nil → a.isLeft → x_in ≠ x_out),
        ∃ W : G.Walk x_in x_out,
          W.IsPath ∧
          W.length = p.length + (p.support.map wt).sum ∧
          (∀ z ∈ W.support, F.proj z ∈ p.support) := by
      intro a b p
      induction p with
      | @nil a =>
        intro _ x_in hx_in _ x_out hx_out _ hport_nil
        cases a with
        | inr u =>
          have heq := hres_eq u x_in x_out hx_in hx_out
          subst heq
          exact ⟨.nil, Walk.IsPath.nil, by simp [wt, triWt], by intro z hz; simp at hz; simp [hz, hx_in]⟩
        | inl i =>
          have hne := hport_nil Walk.Nil.nil rfl
          obtain ⟨seg, hsegP, hsegL, hsegS⟩ := htri_path i x_in x_out hx_in hx_out hne
          exact ⟨seg, hsegP, by simp [wt, triWt, hsegL], fun z hz => by simp [hsegS z hz]⟩
      | @cons a c' b hac r ih =>
        intro hp x_in hx_in hport x_out hx_out hport_end _
        have hrp : r.IsPath := by
          apply Walk.IsPath.mk'
          have hnd := hp.support_nodup
          rw [Walk.support_cons, List.nodup_cons] at hnd
          exact hnd.2
        have ha_not_r : a ∉ r.support := by
          have hnd := hp.support_nodup
          rw [Walk.support_cons, List.nodup_cons] at hnd
          exact hnd.1
        have hbr := hbridge hac
        have hseg1 : ∃ seg1 : G.Walk x_in (outV a c' hac),
            seg1.IsPath ∧ seg1.length = wt a ∧ (∀ z ∈ seg1.support, F.proj z = a) := by
          cases a with
          | inr u =>
            have heq := hres_eq u x_in (outV (Sum.inr u) c' hac) hx_in hbr.1
            subst heq
            exact ⟨.nil, Walk.IsPath.nil, by simp [wt, triWt], by intro z hz; simp at hz; simp [hz, hx_in]⟩
          | inl i =>
            have hne := hport hac r rfl rfl
            obtain ⟨seg, hsegP, hsegL, hsegS⟩ := htri_path i x_in (outV (Sum.inl i) c' hac) hx_in hbr.1 hne
            exact ⟨seg, hsegP, by simp [wt, triWt, hsegL], hsegS⟩
        obtain ⟨seg1, hseg1P, hseg1L, hseg1S⟩ := hseg1
        have hport_r : ∀ {d : F.ContrV} (h : F.contrGraph.Adj c' d) (r' : F.contrGraph.Walk d b),
            r = .cons h r' → c'.isLeft → inV a c' hac ≠ outV c' d h := by
          intro d h r' hr_eq hc'L
          cases c' with
          | inr _ => simp at hc'L
          | inl j =>
            have had : a ≠ d := by
              intro h_eq
              subst h_eq
              apply ha_not_r
              rw [hr_eq, Walk.support_cons]; simp
            exact hdistinct_ports j had hac h
        have hport_end_r : ∀ {d : F.ContrV} (h : F.contrGraph.Adj d b) (r' : F.contrGraph.Walk c' d),
            r = r'.append (.cons h .nil) → b.isLeft → inV d b h ≠ x_out := by
          intro d h r' hr_eq hbL
          exact hport_end h (.cons hac r') (by rw [hr_eq]; rfl) hbL
        have hport_nil_r : r.Nil → c'.isLeft → inV a c' hac ≠ x_out := by
          intro hrnil hc'L
          cases r with
          | nil => exact hport_end hac .nil rfl hc'L
          | cons _ _ => exact False.elim (by cases hrnil)
        obtain ⟨W2, hW2P, hW2L, hW2S⟩ := ih hrp (inV a c' hac) hbr.2.1 hport_r x_out hx_out hport_end_r hport_nil_r
        let W : G.Walk x_in x_out := seg1.append (.cons hbr.2.2 W2)
        have hWL : W.length = (Walk.cons hac r).length + ((Walk.cons hac r).support.map wt).sum := by
          simp only [W, Walk.length_append, Walk.length_cons, hseg1L, hW2L, Walk.support_cons,
            List.map_cons, List.sum_cons]
          omega
        have hWS : ∀ z ∈ W.support, F.proj z ∈ (Walk.cons hac r).support := by
          intro z hz
          rw [Walk.support_append] at hz
          rcases List.mem_append.mp hz with hz1 | hz2
          · rw [Walk.support_cons, hseg1S z hz1]; exact List.mem_cons_self
          · have hz2' : z ∈ W2.support := by
              have : (Walk.cons hbr.2.2 W2).support.tail = W2.support := by simp [Walk.support_cons]
              rwa [this] at hz2
            rw [Walk.support_cons]
            exact List.mem_cons_of_mem _ (hW2S z hz2')
        have hWP : W.IsPath := by
          apply Walk.IsPath.mk'
          have hsupp : W.support = seg1.support ++ W2.support := by
            rw [Walk.support_append, Walk.support_cons, List.tail_cons]
          rw [hsupp]
          refine List.nodup_append'.mpr ⟨hseg1P.support_nodup, hW2P.support_nodup, ?_⟩
          intro z hz1 hz2
          have hp1 : F.proj z = a := hseg1S z hz1
          have hp2 : F.proj z ∈ r.support := hW2S z hz2
          exact ha_not_r (hp1 ▸ hp2)
        exact ⟨W, hWP, hWL, hWS⟩
    have hbr1 := hbridge h₁
    have hq_not_nil : ¬ q.Nil := by
      intro hn; have := Walk.length_eq_zero_iff.mpr hn; omega
    have hport_q : ∀ {c' : F.ContrV} (h : F.contrGraph.Adj q₁ c') (r' : F.contrGraph.Walk c' q₀),
        q = .cons h r' → q₁.isLeft → inV q₀ q₁ h₁ ≠ outV q₁ c' h := by
      intro c' h r' hq_eq hq1L
      cases q₁ with
      | inr _ => simp at hq1L
      | inl j =>
        have hne : q₀ ≠ c' := by
          intro heq
          subst heq
          have hr'nil : r'.Nil := by
            have hsn := hqpath.support_nodup
            rw [hq_eq, Walk.support_cons, List.nodup_cons] at hsn
            cases r' with
            | nil => exact Walk.Nil.nil
            | cons e' s' =>
              have hnd := hsn.2
              rw [Walk.support_cons, List.nodup_cons] at hnd
              exact False.elim (hnd.1 (Walk.end_mem_support s'))
          have hrl : r'.length = 0 := Walk.length_eq_zero_iff.mpr hr'nil
          have hcl : c.length = 2 := by rw [hce, hq_eq]; simp [hrl]
          omega
        exact hdistinct_ports j hne h₁ h
    have hport_end_q : ∀ {c' : F.ContrV} (h : F.contrGraph.Adj c' q₀) (r' : F.contrGraph.Walk q₁ c'),
        q = r'.append (.cons h .nil) → q₀.isLeft → inV c' q₀ h ≠ outV q₀ q₁ h₁ := by
      intro c' h r' hq_eq hq0L
      cases q₀ with
      | inr _ => simp at hq0L
      | inl j =>
        have hne : c' ≠ q₁ := by
          intro heq
          subst heq
          have hr'p : r'.IsPath := by
            have h1' : (r'.append (.cons h .nil)).IsPath := hq_eq ▸ hqpath
            apply Walk.IsPath.mk'
            have hsn := h1'.support_nodup
            rw [Walk.support_append] at hsn
            exact (List.nodup_append.mp hsn).1
          have hrl : r'.length = 0 := by
            cases r' with
            | nil => rfl
            | cons e' s' =>
              have hnd := hr'p.support_nodup
              rw [Walk.support_cons, List.nodup_cons] at hnd
              exact False.elim (hnd.1 (Walk.end_mem_support s'))
          have hql' : q.length = 1 := by rw [hq_eq, Walk.length_append, hrl]; simp
          omega
        exact hdistinct_ports j hne h h₁
    obtain ⟨W, hWP, hWL, _⟩ := hlift_path q hqpath (inV q₀ q₁ h₁) hbr1.2.1 hport_q
      (outV q₀ q₁ h₁) hbr1.1 hport_end_q (fun hn => False.elim (hq_not_nil hn))
    let cyc : G.Walk (outV q₀ q₁ h₁) (outV q₀ q₁ h₁) := .cons hbr1.2.2 W
    have hcyc_len : cyc.length = 2 ^ (k + 1) := by
      have hqs : q.support = c.support.tail := by rw [hce, Walk.support_cons, List.tail_cons]
      have hsum_wt : (c.support.tail.map wt).sum = 2 ^ k := by
        have hL_nodup : L_tri.Nodup := filterMap_inl_nodup hc.support_nodup
        have hsum_split : (c.support.tail.map wt).sum =
            L_tri.length + (L_tri.filter (fun i => decide (i ∈ S_list))).length :=
          sum_wt_split S_list c.support.tail
        have hfilt_eq : (L_tri.filter (fun i => decide (i ∈ S_list))).length = r := by
          have hperm : L_tri.filter (fun i => decide (i ∈ S_list)) = S_list := by
            have htake : L_tri = S_list ++ L_tri.drop r := (List.take_append_drop r L_tri).symm
            conv_lhs => rw [htake]
            rw [List.filter_append]
            have h1 : S_list.filter (fun i => decide (i ∈ S_list)) = S_list :=
              List.filter_eq_self.mpr (fun i hi => by simp [hi])
            have h2 : (L_tri.drop r).filter (fun i => decide (i ∈ S_list)) = [] := by
              apply List.filter_eq_nil_iff.mpr
              intro i hi
              simp only [decide_eq_true_eq]
              intro hiS
              have hnd' := hL_nodup
              rw [htake] at hnd'
              exact (List.nodup_append.mp hnd').2.2 i hiS i hi rfl
            rw [h1, h2, List.append_nil]
          rw [hperm, hS_len]
        have htot := filter_right_add_left c.support.tail
        have hclen_tail : c.support.tail.length = 2 ^ k := by
          have := Walk.length_support c
          have h1 : c.support.length = c.support.tail.length + 1 := by
            rw [← c.cons_tail_support]; simp
          omega
        rw [hsum_split, hfilt_eq, hL_len]
        change (c.support.tail.filter Sum.isLeft).length + (c.support.tail.filter Sum.isRight).length = 2 ^ k
        omega
      simp only [cyc, Walk.length_cons, hWL, hqs, hsum_wt, pow_succ]
      omega
    have hcyc_is : cyc.IsCycle := by
      apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      refine ⟨?_, ?_⟩
      · simpa [cyc] using hWP
      · rw [hcyc_len, pow_succ]; omega
    exact ⟨k + 1, outV q₀ q₁ h₁, cyc, by omega, hcyc_is, hcyc_len⟩

end TriangleFamily

/-- NEW (Wave 3, Agent #6): Triangle-Cover Contraction Theorem.
    No MinimalBad(G) admits a nonempty collection of pairwise vertex-disjoint degree-3
    triangles whose complement R has at most one internal edge. -/
theorem no_triangle_cover_le_one_edge {V I : Type u} [Fintype V] [DecidableEq V] [Fintype I]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (hI : Nonempty I) (F : TriangleFamily G I)
    (hR1 : ∃ r₁ r₂ : V, ∀ u v : F.Res, G.Adj u.1 v.1 → s(u.1, v.1) = s(r₁, r₂)) : False := by
  classical
  let H := F.contrGraph
  let _ : Fintype F.Res := Subtype.fintype (fun x => ¬ F.inTri x)
  let _ : Fintype F.ContrV := inferInstance
  let _ : DecidableRel H.Adj := fun _ _ => Classical.dec _
  rcases hI with ⟨i₀⟩
  have hI' : Nonempty I := ⟨i₀⟩
  obtain ⟨_, w, hw⟩ := hm.1
  have hnear : Near H := by
    refine ⟨⟨Sum.inl i₀, by rw [F.contr_degree_tri hm.2.1 i₀]⟩, ?_⟩
    by_cases hwin : F.inTri w
    · refine ⟨Sum.inl i₀, fun q _ => ?_⟩
      cases q with
      | inl i => rw [F.contr_degree_tri hm.2.1 i]
      | inr r =>
        rw [F.contr_degree_res hm.2.1 r]
        exact hw r.1 (fun h => r.2 (h ▸ hwin))
    · refine ⟨Sum.inr ⟨w, hwin⟩, fun q hq => ?_⟩
      cases q with
      | inl i => rw [F.contr_degree_tri hm.2.1 i]
      | inr r =>
        rw [F.contr_degree_res hm.2.1 r]
        exact hw r.1 (fun h => hq (by congr 1; exact Subtype.ext h))
  have hpow : HasPower H := hm.2.2.1 F.ContrV H (F.card_contr_lt hI') hnear
  obtain ⟨k, q₀, c, hk, hc, hlen⟩ := hpow
  obtain ⟨r₁, r₂, hR_edge⟩ := hR1
  have hcount : (c.support.tail.filter Sum.isRight).length ≤
                (c.support.tail.filter Sum.isLeft).length := by
    have hRR_edge_uniq : ∀ {e₁ e₂ : Sym2 F.ContrV},
        e₁ ∈ H.edgeSet → e₂ ∈ H.edgeSet →
        (∀ q ∈ e₁, q.isRight) → (∀ q ∈ e₂, q.isRight) → e₁ = e₂ := by
      intro e₁ e₂ he1 he2 hr1 hr2
      obtain ⟨u₁, v₁⟩ := e₁
      obtain ⟨u₂, v₂⟩ := e₂
      have hu1 : u₁.isRight := hr1 u₁ (by simp)
      have hv1 : v₁.isRight := hr1 v₁ (by simp)
      have hu2 : u₂.isRight := hr2 u₂ (by simp)
      have hv2 : v₂.isRight := hr2 v₂ (by simp)
      cases u₁ with | inl _ => simp at hu1 | inr a₁ =>
      cases v₁ with | inl _ => simp at hv1 | inr b₁ =>
      cases u₂ with | inl _ => simp at hu2 | inr a₂ =>
      cases v₂ with | inl _ => simp at hv2 | inr b₂ =>
      have hadj1 : G.Adj a₁.1 b₁.1 := by
        obtain ⟨_, x, y, hx, hy, hxy⟩ := (H.mem_edgeSet).mp he1
        exact (F.eq_val_of_proj_inr hx) ▸ (F.eq_val_of_proj_inr hy) ▸ hxy
      have hadj2 : G.Adj a₂.1 b₂.1 := by
        obtain ⟨_, x, y, hx, hy, hxy⟩ := (H.mem_edgeSet).mp he2
        exact (F.eq_val_of_proj_inr hx) ▸ (F.eq_val_of_proj_inr hy) ▸ hxy
      have hs1 := hR_edge a₁ b₁ hadj1
      have hs2 := hR_edge a₂ b₂ hadj2
      have hseq : s(a₁.1, b₁.1) = s(a₂.1, b₂.1) := hs1.trans hs2.symm
      rcases Sym2.eq_iff.mp hseq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have ha : a₁ = a₂ := Subtype.ext h1
        have hb : b₁ = b₂ := Subtype.ext h2
        rw [ha, hb]
      · have ha : a₁ = b₂ := Subtype.ext h1
        have hb : b₁ = a₂ := Subtype.ext h2
        rw [ha, hb]
        exact Quot.sound (Sym2.Rel.swap _ _)
    have hwalk_ineq : ∀ {u v : F.ContrV} (p : H.Walk u v),
        (p.support.tail.filter Sum.isRight).length + (if u.isRight then 1 else 0) ≤
        (p.support.tail.filter Sum.isLeft).length +
        (p.edges.filter (fun e => decide (∀ q ∈ e, q.isRight))).length +
        (if v.isRight then 1 else 0) := by
      intro u v p
      induction p with
      | nil => simp
      | @cons a b d hab r ih =>
        have htail : (Walk.cons hab r).support.tail = b :: r.support.tail := by
          rw [Walk.support_cons, List.tail_cons, r.cons_tail_support]
        rw [htail, Walk.edges_cons, List.filter_cons, List.filter_cons, List.filter_cons]
        cases a <;> cases b <;> simp at ih ⊢ <;> omega
    have hineq := hwalk_ineq c
    have hRR_le1 : (c.edges.filter (fun e => decide (∀ q ∈ e, q.isRight))).length ≤ 1 := by
      have hnd := hc.isTrail.edges_nodup.filter (fun e => decide (∀ q ∈ e, q.isRight))
      cases hf : c.edges.filter (fun e => decide (∀ q ∈ e, q.isRight)) with
      | nil => simp
      | cons e₁ rest =>
        cases rest with
        | nil => simp
        | cons e₂ rest' =>
          rw [hf] at hnd
          have he1_mem : e₁ ∈ c.edges.filter (fun e => decide (∀ q ∈ e, q.isRight)) := by rw [hf]; simp
          have he2_mem : e₂ ∈ c.edges.filter (fun e => decide (∀ q ∈ e, q.isRight)) := by rw [hf]; simp
          have h1 := List.mem_filter.mp he1_mem
          have h2 := List.mem_filter.mp he2_mem
          have heq := hRR_edge_uniq (c.edges_subset_edgeSet h1.1) (c.edges_subset_edgeSet h2.1)
            (of_decide_eq_true h1.2) (of_decide_eq_true h2.2)
          rw [List.nodup_cons] at hnd
          exact False.elim (hnd.1 (by simp [heq]))
    have htot : (c.support.tail.filter Sum.isRight).length +
        (c.support.tail.filter Sum.isLeft).length = 2 ^ k := by
      have hsum := TriangleFamily.filter_right_add_left c.support.tail
      have h1 : c.support.length = c.support.tail.length + 1 := by
        rw [← c.cons_tail_support]; simp
      have h2 := Walk.length_support c
      omega
    have heven : (2 ^ k) % 2 = 0 := by
      cases k with
      | zero => omega
      | succ k => rw [pow_succ]; omega
    omega
  exact hm.2.1 (F.lift_cycle_double hk c hc hlen hcount)

#print axioms TriangleFamily.no_parallel_from_tri
#print axioms TriangleFamily.contr_degree_tri
#print axioms TriangleFamily.contr_degree_res
#print axioms TriangleFamily.lift_cycle_double
#print axioms no_triangle_cover_le_one_edge

end E64TriangleCover
