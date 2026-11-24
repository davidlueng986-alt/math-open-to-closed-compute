import Mathlib

/-!
E077: one completely specified eight-relation branch cannot be a 5-net(10).

`L` supplies the three Latin-square coordinates on the 10 by 10 grid.
`hpair` is exactly the assertion that distinct points agree in at most one
of the five coordinates (row, column, and the three entries).
`hfit` says that every point satisfies the eight explicit binary equations
encoded by `labels`. This assumption is NOT claimed for every possible OA.

The six finite lemmas below enumerate 10^3 possibilities each using `decide`,
not `native_decide`. The final theorem closes this particular code branch.
-/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace MOLS10.E077.Code8

abbrev Symbol := Fin 10
abbrev Point := Fin 5 → Symbol

def labels : Fin 5 → Symbol → Nat :=
  ![ ![33, 32, 35, 37, 41, 49, 1, 97, 161, 222],
     ![0, 77, 118, 37, 3, 238, 207, 242, 151, 89],
     ![0, 85, 239, 155, 249, 122, 87, 179, 46, 104],
     ![0, 248, 80, 142, 67, 87, 74, 99, 177, 170],
     ![0, 23, 46, 140, 167, 81, 200, 208, 143, 212] ]

def mk (r c x y z : Symbol) : Point := ![r,c,x,y,z]

def Fits (p : Point) : Prop :=
  Nat.xor (Nat.xor (Nat.xor (Nat.xor
    (labels 0 (p 0)) (labels 1 (p 1)))
    (labels 2 (p 2))) (labels 3 (p 3))) (labels 4 (p 4)) = 0

def Compatible (p q : Point) : Prop :=
  ∀ i j : Fin 5, i ≠ j → p i ≠ q i ∨ p j ≠ q j

instance (p : Point) : Decidable (Fits p) := by
  unfold Fits
  infer_instance

instance (p q : Point) : Decidable (Compatible p q) := by
  unfold Compatible
  infer_instance

def p1 : Point := mk 7 4 0 9 6
def p2 : Point := mk 6 1 6 6 5
def p3 : Point := mk 4 1 2 4 6
def p4 : Point := mk 0 9 5 3 3
def p5 : Point := mk 0 8 8 2 6

theorem force1 : ∀ x y z : Symbol,
    Fits (mk 7 4 x y z) → mk 7 4 x y z = p1 := by decide

theorem force2 : ∀ x y z : Symbol,
    Fits (mk 6 1 x y z) → Compatible (mk 6 1 x y z) p1 →
      mk 6 1 x y z = p2 := by decide

theorem force3 : ∀ x y z : Symbol,
    Fits (mk 4 1 x y z) → Compatible (mk 4 1 x y z) p1 →
      Compatible (mk 4 1 x y z) p2 → mk 4 1 x y z = p3 := by decide

theorem force4 : ∀ x y z : Symbol,
    Fits (mk 0 9 x y z) → Compatible (mk 0 9 x y z) p1 →
      Compatible (mk 0 9 x y z) p2 → Compatible (mk 0 9 x y z) p3 →
      mk 0 9 x y z = p4 := by decide

theorem force5 : ∀ x y z : Symbol,
    Fits (mk 0 8 x y z) → Compatible (mk 0 8 x y z) p1 →
      Compatible (mk 0 8 x y z) p2 → Compatible (mk 0 8 x y z) p3 →
      Compatible (mk 0 8 x y z) p4 → mk 0 8 x y z = p5 := by decide

theorem no_cell_01 : ∀ x y z : Symbol,
    Fits (mk 0 1 x y z) → Compatible (mk 0 1 x y z) p1 →
      Compatible (mk 0 1 x y z) p2 → Compatible (mk 0 1 x y z) p3 →
      Compatible (mk 0 1 x y z) p4 → Compatible (mk 0 1 x y z) p5 → False := by decide

def cell (L : Symbol → Symbol → Fin 3 → Symbol) (r c : Symbol) : Point :=
  mk r c (L r c 0) (L r c 1) (L r c 2)

theorem no_OA_with_this_code
    (L : Symbol → Symbol → Fin 3 → Symbol)
    (hfit : ∀ r c, Fits (cell L r c))
    (hpair : ∀ r c r' c', (r,c) ≠ (r',c') →
      Compatible (cell L r c) (cell L r' c')) : False := by
  have comp (r c r' c' : Symbol) (hne : (r,c) ≠ (r',c'))
      {p : Point} (hp : cell L r' c' = p) : Compatible (cell L r c) p := by
    rw [← hp]
    exact hpair r c r' c' hne
  have h1 : cell L 7 4 = p1 := force1 _ _ _ (hfit 7 4)
  have h2 : cell L 6 1 = p2 := force2 _ _ _ (hfit 6 1)
    (comp 6 1 7 4 (by decide) h1)
  have h3 : cell L 4 1 = p3 := force3 _ _ _ (hfit 4 1)
    (comp 4 1 7 4 (by decide) h1) (comp 4 1 6 1 (by decide) h2)
  have h4 : cell L 0 9 = p4 := force4 _ _ _ (hfit 0 9)
    (comp 0 9 7 4 (by decide) h1) (comp 0 9 6 1 (by decide) h2)
    (comp 0 9 4 1 (by decide) h3)
  have h5 : cell L 0 8 = p5 := force5 _ _ _ (hfit 0 8)
    (comp 0 8 7 4 (by decide) h1) (comp 0 8 6 1 (by decide) h2)
    (comp 0 8 4 1 (by decide) h3) (comp 0 8 0 9 (by decide) h4)
  exact no_cell_01 _ _ _ (hfit 0 1)
    (comp 0 1 7 4 (by decide) h1) (comp 0 1 6 1 (by decide) h2)
    (comp 0 1 4 1 (by decide) h3) (comp 0 1 0 9 (by decide) h4)
    (comp 0 1 0 8 (by decide) h5)

#print axioms force1
#print axioms force2
#print axioms force3
#print axioms force4
#print axioms force5
#print axioms no_cell_01
#print axioms no_OA_with_this_code

end MOLS10.E077.Code8
