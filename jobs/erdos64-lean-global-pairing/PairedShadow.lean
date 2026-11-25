import Shadow

namespace Erdos64Paired
open SimpleGraph
open scoped Sym2
open Erdos64Closure
universe u
variable {V X Y : Type u}

/-- Four distinct vertices on the alternating rectangle produce an actual C4. -/
theorem rectangle_power (G : SimpleGraph V) {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (e1 : G.Adj a b) (e2 : G.Adj b c) (e3 : G.Adj c d)
    (e4 : G.Adj d a) : HasPower G := by
  let w : G.Walk a a := .cons e1 (.cons e2 (.cons e3 (.cons e4 .nil)))
  have hc : w.IsCycle := by
    apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    constructor
    · apply Walk.IsPath.mk'
      simp [w, Walk.tail_cons, Walk.support_cons, hbc, hbd, hcd,
        Ne.symm hab, Ne.symm hac, Ne.symm had]
    · change 3 ≤ 4
      decide
  exact ⟨2, a, w, by decide, hc, by change 4 = 2^2; decide⟩

def shadow (R : X → Y → Prop) : SimpleGraph X where
  Adj a b := a ≠ b ∧ ∃ y, R a y ∧ R b y
  symm := ⟨by
    rintro a b ⟨hab, y, ha, hb⟩
    exact ⟨hab.symm, y, hb, ha⟩⟩
  loopless := ⟨by intro a h; exact h.1 rfl⟩

/-- Each used row has exactly two selected columns. -/
def Paired (R : X → Y → Prop) : Prop :=
  ∀ y a, R a y → ∃! b, b ≠ a ∧ R b y

theorem paired_of_two_rows [Fintype X] [DecidableEq X]
    (R : X → Y → Prop) [DecidableRel R]
    (h : ∀ y, (Finset.univ.filter (fun a => R a y)).card = 0 ∨
      (Finset.univ.filter (fun a => R a y)).card = 2) : Paired R := by
  intro y a ha
  let S := Finset.univ.filter (fun a => R a y)
  have ham : a ∈ S := by simp [S, ha]
  have hs : S.card = 2 := by
    rcases h y with hz | ht
    · have hpos : 0 < S.card := Finset.card_pos.mpr ⟨a, ham⟩
      exact False.elim ((Nat.ne_of_gt hpos) hz)
    · exact ht
  obtain ⟨b,c,hbc,hS⟩ := Finset.card_eq_two.mp hs
  have hmem : a = b ∨ a = c := by simpa [hS] using ham
  have hb : R b y := by
    have : b ∈ S := by simp [hS]
    simpa [S] using this
  have hcr : R c y := by
    have : c ∈ S := by simp [hS]
    simpa [S] using this
  rcases hmem with hab | hac
  · subst a
    refine ⟨c, ⟨hbc.symm,hcr⟩, ?_⟩
    intro z hz
    have hz' : z ∈ S := by simp [S, hz.2]
    have hz'' : z = b ∨ z = c := by simpa [hS] using hz'
    exact hz''.resolve_left hz.1
  · subst a
    refine ⟨b, ⟨hbc,hb⟩, ?_⟩
    intro z hz
    have hz' : z ∈ S := by simp [S, hz.2]
    have hz'' : z = b ∨ z = c := by simpa [hS] using hz'
    exact hz''.resolve_right hz.1

/-- This proves the previously informal combinatorial step:
every legal paired incidence structure with enough degrees gives a genuine
smaller near graph, not merely a closed walk with possible collisions.
The graph can be of ANY finite order. -/
theorem safe_step_of_paired_incidence (G : SimpleGraph V)
    [Fintype V] [Fintype X] [Fintype Y]
    (f : X → V) (g : Y → V) (hf : Function.Injective f)
    (hg : Function.Injective g) (hsep : ∀ x y, f x ≠ g y)
    (R : X → Y → Prop) [DecidableRel R] (hR : ∀ x y, R x y → G.Adj (f x) (g y))
    (hp : Paired R) (hY : Nonempty Y) (hsize : Fintype.card X < Fintype.card V)
    (hdegrees : ∃ a w : X,
      3 ≤ Fintype.card {y // R a y} ∧
      ∀ x, x ≠ w → 3 ≤ Fintype.card {y // R x y})
    (hfree : ¬ HasPower G) : SafeStep G := by
  classical
  let H := shadow R
  let _ : DecidableRel H.Adj := Classical.decRel _
  have huniq : ∀ a b y z, a ≠ b → R a y → R b y →
      R a z → R b z → y = z := by
    intro a b y z hab hay hby haz hbz
    by_contra hn
    exact hfree (rectangle_power G (hsep a y) (fun h => hab (hf h))
      (hsep a z) (Ne.symm (hsep b y)) (fun h => hn (hg h)) (hsep b z)
      (hR a y hay) (hR b y hby).symm (hR b z hbz) (hR a z haz).symm)
  have hdeg (a : X) : Fintype.card {y // R a y} ≤ H.degree a := by
    let pick : {y // R a y} → H.neighborSet a := fun y =>
      let b := Classical.choose (hp y.1 a y.2).exists
      let hb := Classical.choose_spec (hp y.1 a y.2).exists
      ⟨b, ⟨hb.1.symm, y.1, y.2, hb.2⟩⟩
    have hpinj : Function.Injective pick := by
      intro y z heq
      apply Subtype.ext
      let b := Classical.choose (hp y.1 a y.2).exists
      have hb := Classical.choose_spec (hp y.1 a y.2).exists
      have hz := Classical.choose_spec (hp z.1 a z.2).exists
      have hbe : b = Classical.choose (hp z.1 a z.2).exists :=
        congrArg Subtype.val heq
      exact huniq a b y.1 z.1 hb.1.symm y.2 hb.2 z.2 (hbe ▸ hz.2)
    have hcard := Fintype.card_le_of_injective pick hpinj
    rwa [SimpleGraph.card_neighborSet_eq_degree] at hcard
  obtain ⟨a,w,ha,hw⟩ := hdegrees
  have hnear : Near H := ⟨⟨a,ha.trans (hdeg a)⟩,
    ⟨w,fun x hx => (hw x hx).trans (hdeg x)⟩⟩
  let midY : Sym2 X → Y := fun e =>
    if h : ∃ y, ∀ x ∈ e, R x y then Classical.choose h
    else Classical.choice hY
  have hmid {a b : X} (he : H.Adj a b) :
      R a (midY s(a,b)) ∧ R b (midY s(a,b)) := by
    obtain ⟨_, y, ha, hb⟩ := he
    have hex : ∃ y, ∀ x ∈ s(a,b), R x y := ⟨y, Sym2.ball.mpr ⟨ha,hb⟩⟩
    unfold midY
    rw [dif_pos hex]
    exact Sym2.ball.mp (Classical.choose_spec hex)
  have hinjMid : ∀ e ∈ H.edgeSet, ∀ e' ∈ H.edgeSet,
      midY e = midY e' → e = e' := by
    intro e he e' he' hm
    obtain ⟨a,b⟩ := e
    obtain ⟨c,d⟩ := e'
    have h1 : H.Adj a b := (H.mem_edgeSet).mp he
    have h2 : H.Adj c d := (H.mem_edgeSet).mp he'
    have h1' := hmid h1
    have h2' := hmid h2
    rw [← hm] at h2'
    have hab : a ≠ b := h1.1
    have hcd : c ≠ d := h2.1
    have all : ∀ z, R z (midY s(a,b)) → z = a ∨ z = b := by
      intro z hz
      by_cases hza : z = a
      · exact Or.inl hza
      · exact Or.inr ((hp _ a h1'.1).unique ⟨hza,hz⟩ ⟨hab.symm,h1'.2⟩)
    rcases all c h2'.1 with rfl | rfl <;>
      rcases all d h2'.2 with rfl | rfl
    · contradiction
    · rfl
    · exact Sym2.eq_swap
    · contradiction
  let mid : Sym2 X → V := fun e => g (midY e)
  apply safe_step_of_uniform_shadow G H hsize hnear f mid
  · intro a b h
    exact hR a _ (hmid h).1
  · intro a b h
    exact (hR b _ (hmid h).2).symm
  · exact hf
  · intro a c hc
    apply (List.nodup_map_iff_inj_on hc.isTrail.edges_nodup).mpr
    intro e he e' he' hh
    exact hinjMid e (c.edges_subset_edgeSet he) e' (c.edges_subset_edgeSet he') (hg hh)
  · intro a c hc
    intro v h1 h2
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp h1
    obtain ⟨e,_,he⟩ := List.mem_map.mp h2
    exact hsep x (midY e) he.symm

#print axioms rectangle_power
#print axioms paired_of_two_rows
#print axioms safe_step_of_paired_incidence
end Erdos64Paired
