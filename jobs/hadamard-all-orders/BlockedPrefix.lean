import Parity

namespace HadamardAllOrders

-- Point membership is encoded by bits of a block mask.
private def blocks : List Nat :=
  [885, 1819, 2174, 2667, 3245, 3544, 4551, 5546, 5857, 5940, 6866, 7052,
   7191, 8678, 8892, 9395, 10058, 11153, 11589, 11910, 12505, 12815, 13404,
   14633, 14642, 15968]

private def innerMasks : List Nat :=
  [31991091, 37103254, 40024233, 43545194, 52742502]

def order28Outer : Family := fun j r => (blocks[r]?.getD 0).testBit j
def order28Inner : Family := fun j r => (innerMasks[j]?.getD 0).testBit r

theorem order28_outer : Outer 7 order28Outer := by
  refine ⟨?_, ?_, ?_⟩
  · have h : ∀ r : Fin 26, weight 14 (fun j => order28Outer j r) = 7 := by decide
    exact fun r hr => h ⟨r, hr⟩
  · have h : ∀ j : Fin 14, weight 26 (order28Outer j) = 13 := by decide
    exact fun j hj => h ⟨j, hj⟩
  · have h : ∀ i j : Fin 14, i < j → meet 26 (order28Outer i) (order28Outer j) = 6 := by decide
    exact fun i j hij hj => h ⟨i, Nat.lt_trans hij hj⟩ ⟨j, hj⟩ hij

theorem order28_inner : Inner 7 5 order28Inner := by
  refine ⟨?_, ?_⟩
  · have h : ∀ j : Fin 5, weight 26 (order28Inner j) = 12 := by decide
    exact fun j hj => h ⟨j, hj⟩
  · have h : ∀ i j : Fin 5, i < j → meet 26 (order28Inner i) (order28Inner j) = 5 := by decide
    exact fun i j hij hj => h ⟨i, Nat.lt_trans hij hj⟩ ⟨j, hj⟩ hij

theorem order28_mixed : Mixed 7 5 order28Outer order28Inner := by
  have h : ∀ (i : Fin 5) (j : Fin 14), meet 26 (order28Outer j) (order28Inner i) = 6 := by decide
  exact fun i hi j hj => h ⟨i, hi⟩ ⟨j, hj⟩

theorem order28_capacity : Capacity 7 5 order28Inner := by
  have h : ∀ r : Fin 26, 0 ≤ need 7 5 order28Inner r ∧ need 7 5 order28Inner r ≤ 8 := by decide
  exact fun r hr => h ⟨r, hr⟩

theorem order28_prefix : Prefix 7 5 :=
  ⟨order28Outer, order28Inner, order28_outer, order28_inner, order28_mixed, order28_capacity⟩

/-- This particular capacity-feasible prefix has an exact fractional next
column, but cannot acquire any binary next column that preserves its five
inside intersections. It stops strictly before the last-seven threshold. -/
theorem order28_prefix_cannot_extend (z : Column) :
    ¬ (∀ i, i < 5 → meet 26 z (order28Inner i) = 5) := by
  have h : ∀ r : Fin 26, load order28Inner 5 r % 2 = 0 := by decide
  exact no_next_of_even_load (t := 7) (j := 5) (by decide) (by decide)
    (fun r hr => h ⟨r, hr⟩) z

private def repairedColumns : List Column :=
  ((List.range 20).filter (fun i => i != 9 && i != 12 && i != 19)).map
    (joined 7 order28Outer order28Inner) ++
    [210585043, 90966887, 54089267, 43457415, 238560157, 72738319,
     82980019, 51293467, 174485591, 219361643, 102562017].map
      (fun mask r => Nat.testBit mask r)

/-- Deleting the three indexed columns permits repair by a full order-28 matrix. -/
theorem order28_repaired : Had 28 := by
  let repaired : Family := fun j => repairedColumns[j]?.getD (fun _ => false)
  refine ⟨repaired, ?_⟩
  have check : ∀ i j : Fin 28, i < j → dot 28 (repaired i) (repaired j) = 0 := by
    decide
  exact fun i j hij hj => check ⟨i, Nat.lt_trans hij hj⟩ ⟨j, hj⟩ hij

#print axioms order28_prefix
#print axioms order28_prefix_cannot_extend
#print axioms order28_repaired

end HadamardAllOrders
