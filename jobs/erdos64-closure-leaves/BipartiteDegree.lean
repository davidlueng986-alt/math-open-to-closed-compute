import Mathlib

namespace E64Bipartite
open SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V]

def sideSum (G : SimpleGraph V) [DecidableRel G.Adj]
    (color : V → Bool) (b : Bool) : ℕ :=
  ∑ v, if color v = b then G.degree v else 0

def sideCard (color : V → Bool) (b : Bool) : ℕ :=
  (Finset.univ.filter (fun v => color v=b)).card

theorem degree_indicator (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    G.degree x = ∑ y, if G.Adj x y then (1 : ℕ) else 0 := by
  classical
  rw [← Finset.sum_filter, ← G.card_neighborFinset_eq_degree]
  have h : (Finset.univ.filter fun y => G.Adj x y) = G.neighborFinset x := by
    ext y
    simp
  rw [h]
  simp

theorem side_balance (G : SimpleGraph V) [DecidableRel G.Adj]
    (color : V → Bool)
    (hproper : ∀ a b, G.Adj a b → color a ≠ color b) :
    sideSum G color false = sideSum G color true := by
  classical
  unfold sideSum
  calc
    _ = ∑ x, ∑ y, if color x=false ∧ G.Adj x y then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [degree_indicator G x]
      by_cases h : color x=false
      · simp [h]
      · simp [h]
    _ = ∑ y, ∑ x, if color x=false ∧ G.Adj x y then (1 : ℕ) else 0 :=
      Finset.sum_comm
    _ = ∑ y, ∑ x, if color y=true ∧ G.Adj y x then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : G.Adj x y
      · have hne := hproper x y h
        have hs := h.symm
        cases hx : color x <;> cases hy : color y <;> simp_all
      · have hn : ¬ G.Adj y x := fun h' => h h'.symm
        simp [h,hn]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y _
      rw [degree_indicator G y]
      by_cases h : color y=true
      · simp [h]
      · simp [h]

theorem side_cubic (G : SimpleGraph V) [DecidableRel G.Adj]
    (color : V → Bool) (b : Bool) (h : ∀ v, G.degree v=3) :
    sideSum G color b = 3*sideCard color b := by
  classical
  unfold sideSum sideCard
  simp_rw [h]
  rw [← Finset.sum_filter]
  simp [Nat.mul_comm]

theorem side_one_defect (G : SimpleGraph V) [DecidableRel G.Adj]
    (color : V → Bool) (b : Bool) (w : V)
    (hw : G.degree w=2) (h : ∀ v, v≠w → G.degree v=3) :
    sideSum G color b + (if color w=b then 1 else 0) = 3*sideCard color b := by
  classical
  unfold sideSum sideCard
  calc
    _ = (∑ v, if color v=b then G.degree v else 0) +
        ∑ v, if v=w then (if color w=b then 1 else 0) else 0 := by simp
    _ = ∑ v, ((if color v=b then G.degree v else 0) +
          (if v=w then (if color w=b then 1 else 0) else 0)) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ v, if color v=b then 3 else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : v=w
      · subst v
        by_cases hc : color w=b <;> simp [hc,hw]
      · by_cases hc : color v=b <;> simp [hv,hc,h v hv]
    _ = _ := by
      rw [← Finset.sum_filter]
      simp [Nat.mul_comm]

/-- Full closure leaf S-B: no bipartite finite graph can have exactly
one degree-two vertex and every other vertex degree three. -/
theorem no_bipartite_one_defect (G : SimpleGraph V) [DecidableRel G.Adj]
    (color : V → Bool)
    (hproper : ∀ a b, G.Adj a b → color a ≠ color b)
    (w : V) (hw : G.degree w=2)
    (hrest : ∀ v, v≠w → G.degree v=3) : False := by
  have hbal := side_balance G color hproper
  have h0 := side_one_defect G color false w hw hrest
  have h1 := side_one_defect G color true w hw hrest
  cases h : color w <;> simp [h] at h0 h1 <;> omega

#print axioms side_balance
#print axioms side_cubic
#print axioms side_one_defect
#print axioms no_bipartite_one_defect
end E64Bipartite
