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

variable {V : Type u}

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
  if h : F.inTri x then Sum.inl (Classical.choose h)
  else Sum.inr ⟨x, h⟩

theorem proj_tri (F : TriangleFamily G I) (i : I) (a : Fin 3) :
    F.proj (F.v i a) = Sum.inl i := by
  have h : F.inTri (F.v i a) := ⟨i, a, rfl⟩
  unfold proj
  rw [dif_pos h]
  congr 1
  obtain ⟨b, hb⟩ := Classical.choose_spec h
  have := F.inj hb
  exact congrArg Prod.fst this

theorem proj_res (F : TriangleFamily G I) (r : F.Res) :
    F.proj r.1 = Sum.inr r := by
  unfold proj
  rw [dif_neg r.2]

/-- Each vertex `F.v i a` has a unique external neighbor outside triangle `i`. -/
theorem unique_ext_neighbor (F : TriangleFamily G I) (i : I) (a : Fin 3) :
    ∃! y : V, G.Adj (F.v i a) y ∧ F.proj y ≠ Sum.inl i := by
  classical
  let b : Fin 3 := a + 1
  let c : Fin 3 := a + 2
  have hab : a ≠ b := by fin_cases a <;> decide
  have hac : a ≠ c := by fin_cases a <;> decide
  have hbc : b ≠ c := by fin_cases a <;> decide
  have hvb : F.v i b ≠ F.v i a := fun h => hab.symm (congrArg Prod.snd (F.inj h))
  have hvc : F.v i c ≠ F.v i a := fun h => hac.symm (congrArg Prod.snd (F.inj h))
  have hvbc : F.v i b ≠ F.v i c := fun h => hbc (congrArg Prod.snd (F.inj h))
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
      rw [dif_pos h] at hp
      have hi : Classical.choose h = i := Sum.inl.inj hp
      obtain ⟨d, hd⟩ := Classical.choose_spec h
      rw [hi] at hd
      have hda : d = a ∨ d = b ∨ d = c := by fin_cases a <;> fin_cases d <;> decide
      rcases hda with rfl | rfl | rfl
      · exact G.ne_of_adj hay hd.symm
      · exact hyb hd.symm
      · exact hyc hd.symm
    · unfold proj at hp
      rw [dif_neg h] at hp
      exact Sum.noConfusion hp
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

/-- In a power-free graph, no two distinct vertices of triangle `i` have external neighbors
    projecting to the same vertex of `I ⊕ R` (otherwise a C4 arises). -/
theorem no_parallel_from_tri (F : TriangleFamily G I) (hfree : ¬ HasPower G)
    (i : I) {a b : Fin 3} (hab : a ≠ b) {y₁ y₂ : V}
    (h1 : G.Adj (F.v i a) y₁) (h2 : G.Adj (F.v i b) y₂)
    (ho1 : F.proj y₁ ≠ Sum.inl i) (ho2 : F.proj y₂ ≠ Sum.inl i)
    (heq : F.proj y₁ = F.proj y₂) : False := by
  let c : Fin 3 := -(a + b)
  have hac : a ≠ c := by fin_cases a <;> fin_cases b <;> simp_all [c]
  have hbc : b ≠ c := by fin_cases a <;> fin_cases b <;> simp_all [c]
  have hva_vb : F.v i a ≠ F.v i b := fun h => hab (congrArg Prod.snd (F.inj h))
  have hva_vc : F.v i a ≠ F.v i c := fun h => hac (congrArg Prod.snd (F.inj h))
  have hvb_vc : F.v i b ≠ F.v i c := fun h => hbc (congrArg Prod.snd (F.inj h))
  have hy1_not_i : ∀ d : Fin 3, y₁ ≠ F.v i d := fun d h => ho1 (by rw [h, F.proj_tri])
  have hy2_not_i : ∀ d : Fin 3, y₂ ≠ F.v i d := fun d h => ho2 (by rw [h, F.proj_tri])
  by_cases hy12 : y₁ = y₂
  · subst hy12
    exact hfree (rectangle_power G hva_vc hva_vb (hy1_not_i a).symm
      hvb_vc.symm (hy1_not_i c).symm (hy1_not_i b).symm
      (F.tri i a c hac) (F.tri i c b hbc.symm) h2 h1.symm)
  · have hadj12 : G.Adj y₁ y₂ := by
      by_cases h1in : F.inTri y₁
      · unfold proj at heq
        rw [dif_pos h1in] at heq
        by_cases h2in : F.inTri y₂
        · rw [dif_pos h2in] at heq
          have hj : Classical.choose h1in = Classical.choose h2in := Sum.inl.inj heq
          obtain ⟨d₁, hd₁⟩ := Classical.choose_spec h1in
          obtain ⟨d₂, hd₂⟩ := Classical.choose_spec h2in
          rw [← hj] at hd₂
          have hd12 : d₁ ≠ d₂ := fun h => hy12 (hd₁.symm.trans (h ▸ hd₂))
          rw [← hd₁, ← hd₂]
          exact F.tri _ d₁ d₂ hd12
        · rw [dif_neg h2in] at heq; exact Sum.noConfusion heq
      · unfold proj at heq
        rw [dif_neg h1in] at heq
        by_cases h2in : F.inTri y₂
        · rw [dif_pos h2in] at heq; exact Sum.noConfusion heq
        · rw [dif_neg h2in] at heq
          have : y₁ = y₂ := congrArg Subtype.val (Sum.inr.inj heq)
          exact False.elim (hy12 this)
    exact hfree (rectangle_power G hva_vb (hy2_not_i a).symm (hy1_not_i a).symm
      (hy2_not_i b).symm (hy1_not_i b).symm (Ne.symm hy12)
      (F.tri i a b hab) h2 hadj12.symm h1.symm)

/-- Every triangle vertex `Sum.inl i` has degree exactly 3 in `contrGraph`. -/
theorem contr_degree_tri (F : TriangleFamily G I) (hfree : ¬ HasPower G) (i : I) :
    letI : Fintype F.ContrV := inferInstance
    letI : DecidableRel F.contrGraph.Adj := fun _ _ => Classical.dec _
    F.contrGraph.degree (Sum.inl i) = 3 := by
  classical
  intro _ _
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
    have hx_in : F.inTri x := by
      by_contra hn; unfold proj at hx; rw [dif_neg hn] at hx; exact Sum.noConfusion hx
    unfold proj at hx; rw [dif_pos hx_in] at hx
    have hi : Classical.choose hx_in = i := Sum.inl.inj hx
    obtain ⟨a, ha⟩ := Classical.choose_spec hx_in
    rw [hi] at ha
    have hy_out : F.proj y ≠ Sum.inl i := fun h => hne (hy.symm.trans h).symm
    have hy_eq : y = extN a := (F.unique_ext_neighbor i a).unique ⟨ha ▸ hxy, hy_out⟩ (hextN a)
    exact ⟨a, Subtype.ext (by simp [f, ← hy_eq, hy])⟩
  have hc := Fintype.card_congr (Equiv.ofBijective f ⟨hfinj, hfsurj⟩)
  rw [SimpleGraph.card_neighborSet_eq_degree, Fintype.card_fin] at hc
  exact hc.symm

/-- Every residual vertex `Sum.inr r` keeps its exact degree `G.degree r.1` in `contrGraph`. -/
theorem contr_degree_res (F : TriangleFamily G I) (hfree : ¬ HasPower G) (r : F.Res) :
    letI : Fintype F.ContrV := inferInstance
    letI : DecidableRel F.contrGraph.Adj := fun _ _ => Classical.dec _
    F.contrGraph.degree (Sum.inr r) = G.degree r.1 := by
  classical
  intro _ _
  let f : G.neighborSet r.1 → F.contrGraph.neighborSet (Sum.inr r) := fun u =>
    ⟨F.proj u.1, ⟨fun heq => by
      by_cases hu : F.inTri u.1
      · unfold proj at heq; rw [dif_pos hu] at heq; exact Sum.noConfusion heq
      · unfold proj at heq; rw [dif_neg hu] at heq
        exact (G.ne_of_adj u.2) (congrArg Subtype.val (Sum.inr.inj heq)).symm,
      r.1, u.1, F.proj_res r, rfl, u.2⟩⟩
  have hfinj : Function.Injective f := by
    intro u₁ u₂ heq
    apply Subtype.ext
    by_contra hne
    have hp : F.proj u₁.1 = F.proj u₂.1 := congrArg Subtype.val heq
    by_cases h1 : F.inTri u₁.1
    · unfold proj at hp; rw [dif_pos h1] at hp
      by_cases h2 : F.inTri u₂.1
      · rw [dif_pos h2] at hp
        have hi : Classical.choose h1 = Classical.choose h2 := Sum.inl.inj hp
        obtain ⟨a₁, ha₁⟩ := Classical.choose_spec h1
        obtain ⟨a₂, ha₂⟩ := Classical.choose_spec h2
        rw [← hi] at ha₂
        have ha12 : a₁ ≠ a₂ := fun h => hne (ha₁.symm.trans (h ▸ ha₂))
        have hro : F.proj r.1 ≠ Sum.inl (Classical.choose h1) := by
          rw [F.proj_res r]; exact Sum.noConfusion
        exact F.no_parallel_from_tri hfree (Classical.choose h1) ha12
          (ha₁ ▸ u₁.2.symm) (ha₂ ▸ u₂.2.symm) hro hro rfl
      · rw [dif_neg h2] at hp; exact Sum.noConfusion hp
    · unfold proj at hp; rw [dif_neg h1] at hp
      by_cases h2 : F.inTri u₂.1
      · rw [dif_pos h2] at hp; exact Sum.noConfusion hp
      · rw [dif_neg h2] at hp
        exact hne (congrArg Subtype.val (Sum.inr.inj hp))
  have hfsurj : Function.Surjective f := by
    rintro ⟨q, _, x, y, hx, hy, hxy⟩
    have hxr : x = r.1 := by
      by_cases hxi : F.inTri x
      · unfold proj at hx; rw [dif_pos hxi] at hx; exact Sum.noConfusion hx
      · unfold proj at hx; rw [dif_neg hxi] at hx
        exact congrArg Subtype.val (Sum.inr.inj hx)
    exact ⟨⟨y, hxr ▸ hxy⟩, Subtype.ext hy⟩
  have hc := Fintype.card_congr (Equiv.ofBijective f ⟨hfinj, hfsurj⟩)
  rw [SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.card_neighborSet_eq_degree] at hc
  exact hc.symm

/-- Strict cardinality drop: `|I ⊕ R| < |V|` whenever `Nonempty I`. -/
theorem card_contr_lt (F : TriangleFamily G I) (hI : Nonempty I) :
    Fintype.card F.ContrV < Fintype.card V := by
  classical
  have e : (I × Fin 3) ⊕ F.Res ≃ V :=
    { toFun := Sum.elim (fun p => F.v p.1 p.2) Subtype.val
      invFun := fun x =>
        if h : F.inTri x then
          Sum.inl (Classical.choose h, Classical.choose (Classical.choose_spec h))
        else Sum.inr ⟨x, h⟩
      left_inv := by
        rintro (⟨i, a⟩ | r)
        · have h : F.inTri (F.v i a) := ⟨i, a, rfl⟩
          simp only [Sum.elim_inl, dif_pos h]
          congr 1
          have hspec := Classical.choose_spec (Classical.choose_spec h)
          exact F.inj hspec
        · simp only [Sum.elim_inr, dif_neg r.2]
      right_inv := by
        intro x
        by_cases h : F.inTri x
        · simp only [dif_pos h, Sum.elim_inl]
          exact Classical.choose_spec (Classical.choose_spec h)
        · simp only [dif_neg h, Sum.elim_inr] }
  have hc := Fintype.card_congr e
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] at hc
  rw [Fintype.card_sum]
  have hpos : 0 < Fintype.card I := Fintype.card_pos_iff.mpr hI
  omega

/-- Lift a simple cycle of length `2^k` in `contrGraph` to a simple cycle of length `2^(k+1)` in `G`
    whenever the number of residual vertices `r` on the cycle satisfies `r ≤ t`. -/
theorem lift_cycle_double (F : TriangleFamily G I)
    {k : ℕ} (hk : 2 ≤ k) {q₀ : F.ContrV} (c : F.contrGraph.Walk q₀ q₀)
    (hc : c.IsCycle) (hlen : c.length = 2 ^ k)
    (hcount : (c.support.tail.filter (fun q => q.isRight)).length ≤
              (c.support.tail.filter (fun q => q.isLeft)).length) : HasPower G := by
  classical
  let outV : (u v : F.ContrV) → F.contrGraph.Adj u v → V :=
    fun _ _ h => Classical.choose h.2
  let inV : (u v : F.ContrV) → F.contrGraph.Adj u v → V :=
    fun _ _ h => Classical.choose (Classical.choose_spec h.2)
  have hbridge : ∀ {u v : F.ContrV} (h : F.contrGraph.Adj u v),
      F.proj (outV u v h) = u ∧ F.proj (inV u v h) = v ∧ G.Adj (outV u v h) (inV u v h) :=
    fun h => Classical.choose_spec (Classical.choose_spec h.2)
  let L_tri : List I := c.support.tail.filterMap (fun q => match q with | Sum.inl i => some i | Sum.inr _ => none)
  have hL_len : L_tri.length = (c.support.tail.filter (fun q => q.isLeft)).length := by
    induction c.support.tail with
    | nil => rfl
    | cons x xs ih =>
      cases x with
      | inl i => simp [L_tri, ih]
      | inr r => simp [L_tri, ih]
  let r := (c.support.tail.filter (fun q => q.isRight)).length
  let S_list : List I := L_tri.take r
  have hS_len : S_list.length = r := by
    rw [List.length_take, hL_len]
    exact Nat.min_eq_left hcount
  have htri_path : ∀ (i : I) (x y : V), F.proj x = Sum.inl i → F.proj y = Sum.inl i → x ≠ y →
      ∃ p : G.Walk x y, p.IsPath ∧
        (p.length = if i ∈ S_list then 2 else 1) ∧
        (∀ z ∈ p.support, F.proj z = Sum.inl i) := by
    intro i x y hx hy hxy
    have hxin : F.inTri x := by by_contra h; unfold proj at hx; rw [dif_neg h] at hx; exact Sum.noConfusion hx
    have hyin : F.inTri y := by by_contra h; unfold proj at hy; rw [dif_neg h] at hy; exact Sum.noConfusion hy
    unfold proj at hx hy; rw [dif_pos hxin] at hx; rw [dif_pos hyin] at hy
    obtain ⟨a, ha⟩ := Classical.choose_spec hxin
    obtain ⟨b, hb⟩ := Classical.choose_spec hyin
    rw [Sum.inl.inj hx] at ha
    rw [Sum.inl.inj hy] at hb
    have hab : a ≠ b := fun h => hxy (ha.symm.trans (h ▸ hb))
    by_cases hS : i ∈ S_list
    · let c3 : Fin 3 := -(a + b)
      have hac : a ≠ c3 := by fin_cases a <;> fin_cases b <;> simp_all [c3]
      have hbc : b ≠ c3 := by fin_cases a <;> fin_cases b <;> simp_all [c3]
      have hadj1 : G.Adj x (F.v i c3) := ha ▸ F.tri i a c3 hac
      have hadj2 : G.Adj (F.v i c3) y := hb ▸ F.tri i c3 b hbc.symm
      let p : G.Walk x y := .cons hadj1 (.cons hadj2 .nil)
      have hxc : x ≠ F.v i c3 := G.ne_of_adj hadj1
      have hcy : F.v i c3 ≠ y := G.ne_of_adj hadj2
      refine ⟨p, Walk.IsPath.mk' (by simp [p, hxc, hxy, hcy]), by simp [p, hS], ?_⟩
      intro z hz
      simp only [p, Walk.support_cons, Walk.support_nil, List.mem_cons, List.notMem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl
      · rw [← ha, F.proj_tri]
      · exact F.proj_tri i c3
      · rw [← hb, F.proj_tri]
    · have hadj : G.Adj x y := ha ▸ hb ▸ F.tri i a b hab
      let p : G.Walk x y := .cons hadj .nil
      refine ⟨p, Walk.IsPath.mk' (by simp [p, hxy]), by simp [p, hS], ?_⟩
      intro z hz
      simp only [p, Walk.support_cons, Walk.support_nil, List.mem_cons, List.notMem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · rw [← ha, F.proj_tri]
      · rw [← hb, F.proj_tri]
  have hres_eq : ∀ (u : F.Res) (x y : V), F.proj x = Sum.inr u → F.proj y = Sum.inr u → x = y := by
    intro u x y hx hy
    have h1 : x = u.1 := by
      by_cases h : F.inTri x
      · unfold proj at hx; rw [dif_pos h] at hx; exact Sum.noConfusion hx
      · unfold proj at hx; rw [dif_neg h] at hx; exact congrArg Subtype.val (Sum.inr.inj hx)
    have h2 : y = u.1 := by
      by_cases h : F.inTri y
      · unfold proj at hy; rw [dif_pos h] at hy; exact Sum.noConfusion hy
      · unfold proj at hy; rw [dif_neg h] at hy; exact congrArg Subtype.val (Sum.inr.inj hy)
    exact h1.trans h2.symm
  have hdistinct_ports : ∀ (i : I) {q₁ q₂ : F.ContrV} (hne : q₁ ≠ q₂)
      (h1 : F.contrGraph.Adj q₁ (Sum.inl i)) (h2 : F.contrGraph.Adj (Sum.inl i) q₂),
      inV q₁ (Sum.inl i) h1 ≠ outV (Sum.inl i) q₂ h2 := by
    intro i q₁ q₂ hne h1 h2 heq
    have hb1 := hbridge h1
    have hb2 := hbridge h2
    have hxin : F.inTri (inV q₁ (Sum.inl i) h1) := by
      by_contra h; unfold proj at hb1; rw [dif_neg h] at hb1; exact Sum.noConfusion hb1.2.1
    unfold proj at hb1; rw [dif_pos hxin] at hb1
    obtain ⟨a, ha⟩ := Classical.choose_spec hxin
    rw [Sum.inl.inj hb1.2.1] at ha
    have h1' : G.Adj (F.v i a) (outV q₁ (Sum.inl i) h1) := ha ▸ hb1.2.2.symm
    have h2' : G.Adj (F.v i a) (inV (Sum.inl i) q₂ h2) := (ha.trans heq) ▸ hb2.2.2
    have ho1 : F.proj (outV q₁ (Sum.inl i) h1) ≠ Sum.inl i := by rw [hb1.1]; exact h1.1
    have ho2 : F.proj (inV (Sum.inl i) q₂ h2) ≠ Sum.inl i := by rw [hb2.2.1]; exact h2.1.symm
    have heqy := (F.unique_ext_neighbor i a).unique ⟨h1', ho1⟩ ⟨h2', ho2⟩
    exact hne (hb1.1.symm.trans ((congrArg F.proj heqy).trans hb2.2.1))
  let wt : F.ContrV → ℕ := fun q =>
    match q with
    | Sum.inr _ => 0
    | Sum.inl i => if i ∈ S_list then 2 else 1
  cases hce : c with
  | nil =>
    rw [hce] at hlen
    have : 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
    simp at hlen; omega
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
      | nil =>
        intro _ x_in hx_in _ x_out hx_out _ hport_nil
        cases a with
        | inr u =>
          have heq := hres_eq u x_in x_out hx_in hx_out
          subst heq
          exact ⟨.nil, Walk.IsPath.nil, by simp [wt], by intro z hz; simp at hz; simp [hz, hx_in]⟩
        | inl i =>
          have hne := hport_nil Walk.Nil.nil rfl
          obtain ⟨seg, hsegP, hsegL, hsegS⟩ := htri_path i x_in x_out hx_in hx_out hne
          exact ⟨seg, hsegP, by simp [wt, hsegL], fun z hz => by simp [hsegS z hz]⟩
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
            exact ⟨.nil, Walk.IsPath.nil, by simp [wt], by intro z hz; simp at hz; simp [hz, hx_in]⟩
          | inl i =>
            have hne := hport hac r rfl rfl
            obtain ⟨seg, hsegP, hsegL, hsegS⟩ := htri_path i x_in (outV (Sum.inl i) c' hac) hx_in hbr.1 hne
            exact ⟨seg, hsegP, by simp [wt, hsegL], hsegS⟩
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
          | nil =>
            exact hport_end hac .nil rfl hc'L
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
          · rw [Walk.support_cons]; simp [hseg1S z hz1]
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
      intro hn; have := Walk.length_eq_zero_iff.mpr hn
      have : 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
      omega
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
          have : 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
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
          have : 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
          omega
        exact hdistinct_ports j hne h h₁
    obtain ⟨W, hWP, hWL, _⟩ := hlift_path q hqpath (inV q₀ q₁ h₁) hbr1.2.1 hport_q
      (outV q₀ q₁ h₁) hbr1.1 hport_end_q (fun hn => False.elim (hq_not_nil hn))
    let cyc : G.Walk (outV q₀ q₁ h₁) (outV q₀ q₁ h₁) := .cons hbr1.2.2 W
    have hcyc_len : cyc.length = 2 ^ (k + 1) := by
      have hqs : q.support = c.support.tail := by rw [hce, Walk.support_cons, List.tail_cons]
      have hsum_wt : (c.support.tail.map wt).sum = 2 ^ k := by
        have hL_nodup : L_tri.Nodup := by
          have hnd := hc.support_nodup
          clear hsum_wt hWL hWP W hport_end_q hport_q hlift_path
          induction c.support.tail with
          | nil => exact List.nodup_nil
          | cons x xs ih =>
            rw [List.nodup_cons] at hnd
            cases x with
            | inr _ => exact ih hnd.2
            | inl i =>
              simp only [L_tri, List.filterMap_cons]
              rw [List.nodup_cons]
              refine ⟨?_, ih hnd.2⟩
              intro hm
              obtain ⟨y, hy, hyi⟩ := List.mem_filterMap.mp hm
              cases y with
              | inr _ => simp at hyi
              | inl j =>
                simp at hyi
                subst hyi
                exact hnd.1 hy
        have hsum_split : (c.support.tail.map wt).sum =
            L_tri.length + (L_tri.filter (fun i => decide (i ∈ S_list))).length := by
          clear hL_nodup hWL hWP W hport_end_q hport_q hlift_path
          induction c.support.tail with
          | nil => simp [L_tri]
          | cons x xs ih =>
            cases x with
            | inr u => simp [wt, L_tri, ih]
            | inl i =>
              by_cases hi : i ∈ S_list
              · simp [wt, L_tri, hi, ih]; omega
              · simp [wt, L_tri, hi, ih]; omega
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
        have htot : (c.support.tail.filter (fun q => q.isRight)).length +
            (c.support.tail.filter (fun q => q.isLeft)).length = c.support.tail.length := by
          clear hfilt_eq hsum_split hL_nodup hWL hWP W hport_end_q hport_q hlift_path
          induction c.support.tail with
          | nil => simp
          | cons x xs ih =>
            cases x <;> simp [ih] <;> omega
        have hclen_tail : c.support.tail.length = 2 ^ k := by
          have := Walk.length_support c
          have hcons := c.cons_tail_support
          have h1 : c.support.length = c.support.tail.length + 1 := by
            rw [← hcons]; simp
          omega
        rw [hsum_split, hfilt_eq, hL_len]
        change (c.support.tail.filter (fun q => q.isLeft)).length + r = 2 ^ k
        omega
      simp only [cyc, Walk.length_cons, hWL, hqs, hsum_wt, pow_succ]
      omega
    have hcyc_is : cyc.IsCycle := by
      apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      refine ⟨?_, ?_⟩
      · simpa [cyc] using hWP
      · rw [hcyc_len, pow_succ]
        have : 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
        omega
    exact ⟨k + 1, outV q₀ q₁ h₁, cyc, by omega, hcyc_is, hcyc_len⟩

/-- NEW (Wave 3, Agent #6): Triangle-Cover Contraction Theorem.
    No MinimalBad(G) admits a nonempty collection of pairwise vertex-disjoint degree-3
    triangles whose complement R has at most one internal edge. -/
theorem no_triangle_cover_le_one_edge [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hm : MinimalBad G)
    (I : Type u) [Fintype I] (hI : Nonempty I)
    (F : TriangleFamily G I)
    (hR1 : ∃ r₁ r₂ : V, ∀ u v : F.Res, G.Adj u.1 v.1 → s(u.1, v.1) = s(r₁, r₂)) : False := by
  classical
  let H := F.contrGraph
  letI : DecidableRel H.Adj := fun _ _ => Classical.dec _
  obtain ⟨i₀⟩ := hI
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
  have hpow : HasPower H := hm.2.2.1 F.ContrV H (F.card_contr_lt hI) hnear
  obtain ⟨k, q₀, c, hk, hc, hlen⟩ := hpow
  obtain ⟨r₁, r₂, hR_edge⟩ := hR1
  have hcount : (c.support.tail.filter (fun q => q.isRight)).length ≤
                (c.support.tail.filter (fun q => q.isLeft)).length := by
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
        have hxa : x = a₁.1 := by
          by_cases h : F.inTri x
          · unfold proj at hx; rw [dif_pos h] at hx; exact Sum.noConfusion hx
          · unfold proj at hx; rw [dif_neg h] at hx; exact congrArg Subtype.val (Sum.inr.inj hx)
        have hyb : y = b₁.1 := by
          by_cases h : F.inTri y
          · unfold proj at hy; rw [dif_pos h] at hy; exact Sum.noConfusion hy
          · unfold proj at hy; rw [dif_neg h] at hy; exact congrArg Subtype.val (Sum.inr.inj hy)
        exact hxa ▸ hyb ▸ hxy
      have hadj2 : G.Adj a₂.1 b₂.1 := by
        obtain ⟨_, x, y, hx, hy, hxy⟩ := (H.mem_edgeSet).mp he2
        have hxa : x = a₂.1 := by
          by_cases h : F.inTri x
          · unfold proj at hx; rw [dif_pos h] at hx; exact Sum.noConfusion hx
          · unfold proj at hx; rw [dif_neg h] at hx; exact congrArg Subtype.val (Sum.inr.inj hx)
        have hyb : y = b₂.1 := by
          by_cases h : F.inTri y
          · unfold proj at hy; rw [dif_pos h] at hy; exact Sum.noConfusion hy
          · unfold proj at hy; rw [dif_neg h] at hy; exact congrArg Subtype.val (Sum.inr.inj hy)
        exact hxa ▸ hyb ▸ hxy
      have hs1 := hR_edge a₁ b₁ hadj1
      have hs2 := hR_edge a₂ b₂ hadj2
      have hseq : s(a₁.1, b₁.1) = s(a₂.1, b₂.1) := hs1.trans hs2.symm
      rcases Sym2.eq_iff.mp hseq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have ha : a₁ = a₂ := Subtype.ext h1
        have hb : b₁ = b₂ := Subtype.ext h2
        rw [ha, hb]
      · have ha : a₁ = b₂ := Subtype.ext h1
        have hb : b₁ = a₂ := Subtype.ext h2
        rw [ha, hb, Sym2.eq_swap]
    have hwalk_ineq : ∀ {u v : F.ContrV} (p : H.Walk u v),
        (p.support.tail.filter (fun q => q.isRight)).length + (if u.isRight then 1 else 0) ≤
        (p.support.tail.filter (fun q => q.isLeft)).length +
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
    have htot : (c.support.tail.filter (fun q => q.isRight)).length +
        (c.support.tail.filter (fun q => q.isLeft)).length = 2 ^ k := by
      have hsum : (c.support.tail.filter (fun q => q.isRight)).length +
          (c.support.tail.filter (fun q => q.isLeft)).length = c.support.tail.length := by
        clear hRR_le1 hineq hwalk_ineq hRR_edge_uniq
        induction c.support.tail with
        | nil => simp
        | cons x xs ih => cases x <;> simp [ih] <;> omega
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

end TriangleFamily

#print axioms TriangleFamily.no_parallel_from_tri
#print axioms TriangleFamily.contr_degree_tri
#print axioms TriangleFamily.contr_degree_res
#print axioms TriangleFamily.lift_cycle_double
#print axioms TriangleFamily.no_triangle_cover_le_one_edge

end E64TriangleCover
