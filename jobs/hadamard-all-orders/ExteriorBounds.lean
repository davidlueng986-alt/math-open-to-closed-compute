namespace HadamardAllOrders

/-- The diagonal quadratic bound from a one-minus row type. -/
theorem one_minus_count_bound {t a : Int} (ht : 65 ≤ t)
    (odd : t % 2 = 1) (ha : a ≤ t - 2)
    (condition : 0 ≤ (2*a-t)*(2*a-5*t)+8*t) : 2*a ≤ t+1 := by
  by_cases hn : 2*a ≤ t+1
  · exact hn
  have lower : 3 ≤ 2*a-t := by omega
  have upper : 2*a-5*t ≤ -3*t-4 := by omega
  have step₁ := Int.mul_le_mul_of_nonneg_left upper (by omega : 0 ≤ 2*a-t)
  have step₂ := Int.mul_le_mul_of_nonpos_right lower (by omega : -3*t-4 ≤ 0)
  grind

/-- The two Parseval inequalities on a largest two-minus split contradict
one another. Here m is the split size and u is the absolute tetrahedral sum. -/
theorem four_stack_arithmetic {t m u : Int} (ht : 65 ≤ t)
    (hm : 0 ≤ m) (maxm : m ≤ t-1) (largest : t-1 ≤ 3*m)
    (hu : 0 ≤ u) (maxu : u ≤ t+4)
    (diagonal : 4*t*(4*m-t-4) ≤ (u+2*m)*(u+2*m))
    (pair : 8*t*(t-6+u-2*m) ≤ (3*t+2-u-2*m)*(3*t+2-u-2*m)) : False := by
  let a := u+2*m
  have aNonneg : 0 ≤ a := by dsimp [a]; omega
  have aUpper : a ≤ 3*t+2 := by dsimp [a]; omega
  have tBound : t ≤ 4*(4*m-t-4) := by omega
  have squared : t*t ≤ a*a := by
    have h := Int.mul_le_mul_of_nonneg_left tBound (by omega : 0 ≤ t)
    change 4*t*(4*m-t-4) ≤ a*a at diagonal
    grind
  have aLower : t ≤ a := by
    by_cases hn : t ≤ a
    · exact hn
    have pos := Int.mul_pos (by omega : 0 < t-a) (by omega : 0 < t+a)
    grind
  have doubled := Int.mul_le_mul_of_nonneg_left diagonal (by decide : 0 ≤ (2 : Int))
  have combined := Int.add_le_add pair doubled
  have polynomial : 0 ≤ 3*a*a-(14*t+4)*a+9*t*t+92*t+4 := by
    dsimp [a] at *
    grind
  have chord := Int.mul_nonpos_of_nonneg_of_nonpos (by omega : 0 ≤ a-t)
    (by omega : 3*a-11*t-4 ≤ 0)
  have endpoint := Int.mul_pos (by omega : 0 < t) (by omega : 0 < t-44)
  have endpointLower := Int.mul_le_mul_of_nonneg_left (by omega : 21 ≤ t-44)
    (by omega : 0 ≤ t)
  grind

#print axioms one_minus_count_bound
#print axioms four_stack_arithmetic

end HadamardAllOrders
