import Triples

namespace Hadamard2396.Obstructions

/-- The correlation on one 3-cycle in the horizontal direction. -/
def cycle (a b c : Bool) : Int :=
  sign a * sign b + sign b * sign c + sign c * sign a

private theorem cycle_lower (a b c : Bool) : -1 ≤ cycle a b c := by
  cases a <;> cases b <;> cases c <;> decide

private theorem constant_cycle (b : Bool) : cycle b b b = 3 := by
  cases b <;> decide

abbrev Plane := Fin 3 → Fin 3 → Bool

/-- The first argument is the transverse coordinate y, the second is the coordinate x. -/
def horizontal (a : Plane) : Int :=
  cycle (a 0 0) (a 0 1) (a 0 2) + cycle (a 1 0) (a 1 1) (a 1 2) +
  cycle (a 2 0) (a 2 1) (a 2 2)

def shearFixed (a : Plane) : Prop := ∀ y x : Fin 3, a y (x+y) = a y x

private theorem plane_lower (a b : Plane) (h : shearFixed a) :
    2 ≤ horizontal a + horizontal b := by
  have h₁ : a 1 1 = a 1 0 := h 1 0
  have h₂ : a 1 2 = a 1 1 := h 1 1
  have h₃ : a 2 2 = a 2 0 := h 2 0
  have h₄ : a 2 1 = a 2 2 := h 2 2
  unfold horizontal
  rw [h₂,h₁,h₄,h₃,constant_cycle,constant_cycle]
  have a₀ := cycle_lower (a 0 0) (a 0 1) (a 0 2)
  have b₀ := cycle_lower (b 0 0) (b 0 1) (b 0 2)
  have b₁ := cycle_lower (b 1 0) (b 1 1) (b 1 2)
  have b₂ := cycle_lower (b 2 0) (b 2 1) (b 2 2)
  omega

/-- The shear (x,y,k) ↦ (x+y,y,k) forces horizontal correlation at least 2m
    even if only one word is invariant. The index k enumerates any m-element factor. -/
theorem shear_lower (m : Nat) (a b : Nat → Plane) (h : ∀ i, i < m → shearFixed (a i)) :
    2 * (m : Int) ≤ sumAt m (fun k => horizontal (a k)) + sumAt m (fun k => horizontal (b k)) := by
  induction m with
  | zero => simp [sumAt]
  | succ m ih =>
    have hsmall := ih (fun i hi => h i (by omega))
    have last := plane_lower (a m) (b m) (h m (by omega))
    rw [sumAt_succ,sumAt_succ,Int.natCast_succ]
    omega

theorem no_pure_shear_1197 (a b : Nat → Plane)
    (h : ∀ i, i < 133 → shearFixed (a i)) :
    266 ≤ sumAt 133 (fun k => horizontal (a k)) + sumAt 133 (fun k => horizontal (b k)) :=
  shear_lower 133 a b h

/-- A nonidentity involution on the 3² factor negates a nontrivial order-3 character.
    The equalities in the premise say that the matrix squares to the identity. -/
theorem involution_negates_character :
    ∀ a b c d : Fin 3, a*a+b*c=1 → a*b+b*d=0 → c*a+d*c=0 → c*b+d*d=1 →
    ¬(a=1 ∧ b=0 ∧ c=0 ∧ d=1) →
    ∃ i j : Fin 3, (i ≠ 0 ∨ j ≠ 0) ∧ i*a+j*c = -i ∧ i*b+j*d = -j := by decide +kernel

/-- The support identity and the sign bound specialize to exactly seven heavy entries. -/
theorem seven_heavy (w d : Int) (norm : 18*w + 2*d = 124) (lo : -w ≤ d) (hi : d ≤ w) :
    w = 7 ∧ d = -1 := by omega

/-- At a nonzero shift the compressed equation and singleton bounds force 0 or -1. -/
theorem sparse_correlation (h k l : Int) (equation : 324*h + 18*k + l = -38)
    (crossLo : -14 ≤ k) (crossHi : k ≤ 14) (singleLo : -90 ≤ l) (singleHi : l ≤ 126) :
    h = 0 ∨ h = -1 := by omega

#print axioms shear_lower
#print axioms no_pure_shear_1197
#print axioms involution_negates_character
#print axioms seven_heavy
#print axioms sparse_correlation
end Hadamard2396.Obstructions
