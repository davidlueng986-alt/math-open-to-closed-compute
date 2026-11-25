import Rounding

namespace HadamardAllOrders

open Hadamard2396 (sumAt sumAt_succ sumAt_congr)

/-- The second row-load moment is determined by the inside intersection counts. -/
theorem squared_load {t j : Nat} {x : Family} (hx : Inner t j x) :
    sumAt (lowerRows t) (fun r => load x j r * load x j r) =
      (j : Int) * ((j : Int) * ((t : Int) - 2) + (t : Int)) := by
  have expand (r : Nat) : load x j r * load x j r =
      sumAt j (fun i => bit (x i r) * load x j r) := by
    exact sum_mul (load x j r) j _
  rw [sumAt_congr _ (fun r _ => expand r), swap_sums, ← sum_const]
  exact sumAt_congr _ (fun _ hi => inner_load hx hi)

private theorem sum_divisible (m : Int) (n : Nat) (f : Nat → Int)
    (h : ∀ i, i < n → f i % m = 0) : sumAt n f % m = 0 := by
  induction n with
  | zero => simp [sumAt]
  | succ n ih =>
    rw [sumAt_succ, Int.add_emod, ih (fun i hi => h i (by omega)), h n (by omega)]
    simp

private theorem even_square_sub_twice (d : Int) (even : d % 2 = 0) :
    (d * d - 2 * d) % 8 = 0 := by
  have h : d % 8 = 0 ∨ d % 8 = 2 ∨ d % 8 = 4 ∨ d % 8 = 6 := by omega
  rw [Int.sub_emod, Int.mul_emod d d 8, Int.mul_emod 2 d 8]
  rcases h with h | h | h | h <;> simp [h]

/-- An odd-width inside family whose columns XOR to zero must have a width
congruent to the full inside width modulo eight. -/
theorem even_load_width_mod_eight {t j : Nat} {x : Family} (oddT : t % 2 = 1)
    (oddJ : j % 2 = 1) (hx : Inner t j x)
    (even : ∀ r, r < lowerRows t → load x j r % 2 = 0) :
    (j : Int) % 8 = (2 * (t : Int) - 1) % 8 := by
  have h := sum_divisible 8 (lowerRows t)
    (fun r => load x j r * load x j r - 2 * load x j r)
    (fun r hr => even_square_sub_twice _ (even r hr))
  rw [sum_sub, ← mul_sum, squared_load hx, total_load t j x hx] at h
  let a : Int := j
  let b : Int := t
  have eq : a * (a * (b - 2) + b) - 2 * (a * (2 * b - 2)) =
      a * (a * (b - 2) - 3 * b + 4) := by grind
  change (a * (a * (b - 2) + b) - 2 * (a * (2 * b - 2))) % 8 = 0 at h
  rw [eq, Int.mul_emod a, Int.add_emod, Int.sub_emod, Int.mul_emod a,
    Int.sub_emod, Int.mul_emod 3 b] at h
  have ar : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by dsimp [a]; omega
  have br : b % 8 = 1 ∨ b % 8 = 3 ∨ b % 8 = 5 ∨ b % 8 = 7 := by dsimp [b]; omega
  change a % 8 = (2 * b - 1) % 8
  rw [Int.sub_emod, Int.mul_emod 2 b]
  rcases ar with ar | ar | ar | ar <;> rcases br with br | br | br | br <;>
    simp_all [Int.sub_emod b 2 8] <;> omega

/-- An odd-width inside family whose columns XOR to zero cannot gain a new
inside column even if only the previous inside intersection counts are required. -/
theorem no_next_of_even_load {t j : Nat} {x : Family} (oddT : t % 2 = 1)
    (oddJ : j % 2 = 1) (even : ∀ r, r < lowerRows t → load x j r % 2 = 0)
    (z : Column) (next : ∀ i, i < j → meet (lowerRows t) z (x i) = (t : Int) - 2) : False := by
  have h := sum_divisible 2 (lowerRows t) (fun r => bit (z r) * load x j r) (by
    intro r hr
    rw [Int.mul_emod, even r hr, Int.mul_zero]
    decide)
  change countOn (lowerRows t) z (load x j) % 2 = 0 at h
  rw [load_on, sumAt_congr _ next, sum_const, Int.mul_emod] at h
  have tx : ((t : Int) - 2) % 2 = 1 := by omega
  have jx : (j : Int) % 2 = 1 := by omega
  simp [tx, jx] at h

/-- For balanced nonconstant columns in a normalized partial Hadamard
matrix, uniform row parity at even total width forces defect divisible by eight. -/
theorem normalized_even_load_mod_eight {t j : Nat} {x : Family}
    (oddT : t % 2 = 1) (oddJ : j % 2 = 1)
    (balanced : ∀ i, i < j → weight (4*t) (x i) = 2*(t : Int))
    (common : ∀ i l, i < l → l < j → meet (4*t) (x i) (x l) = t)
    (even : ∀ r, r < 4*t → load x j r % 2 = 0) :
    j % 8 = 3 := by
  have total : sumAt (4*t) (load x j) = (j : Int)*(2*(t : Int)) := by
    unfold load weight
    rw [swap_sums, ← sum_const]
    exact sumAt_congr _ balanced
  have onCol (i : Nat) (hi : i < j) :
      countOn (4*t) (x i) (load x j) = (j : Int)*(t : Int) + t := by
    rw [load_on]
    have pair (l : Nat) (hl : l < j) :
        meet (4*t) (x i) (x l) = (t : Int) + if l = i then (t : Int) else 0 := by
      by_cases h : l = i
      · subst l
        rw [meet_self, balanced i hi]
        simp
        omega
      · simp only [ite_eq_right h, Int.add_zero]
        by_cases before : i < l
        · exact common i l before hl
        · rw [meet_comm]
          exact common l i (by omega) hi
    rw [sumAt_congr _ pair, Hadamard2396.sumAt_add, sum_const, sum_single hi]
  have moment : sumAt (4*t) (fun r => load x j r * load x j r) =
      (j : Int) * ((j : Int)*(t : Int) + t) := by
    have expand (r : Nat) : load x j r * load x j r =
        sumAt j (fun i => bit (x i r) * load x j r) :=
      sum_mul (load x j r) j _
    rw [sumAt_congr _ (fun r _ => expand r), swap_sums, ← sum_const]
    exact sumAt_congr _ onCol
  have h := sum_divisible 8 (4*t) (fun r => load x j r * load x j r - 2 * load x j r)
    (fun r hr => even_square_sub_twice _ (even r hr))
  rw [sum_sub, ← mul_sum, moment, total] at h
  let a : Int := j
  let b : Int := t
  have eq : a * (a * b + b) - 2 * (a * (2 * b)) = b * a * (a - 3) := by grind
  change (a * (a * b + b) - 2 * (a * (2 * b))) % 8 = 0 at h
  rw [eq, Int.mul_emod, Int.mul_emod b, Int.sub_emod] at h
  have ar : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by dsimp [a]; omega
  have br : b % 8 = 1 ∨ b % 8 = 3 ∨ b % 8 = 5 ∨ b % 8 = 7 := by dsimp [b]; omega
  have res : a % 8 = 3 := by
    rcases ar with ar | ar | ar | ar <;> rcases br with br | br | br | br <;> simp_all
  dsimp [a] at res
  omega

#print axioms squared_load
#print axioms even_load_width_mod_eight
#print axioms no_next_of_even_load
#print axioms normalized_even_load_mod_eight

end HadamardAllOrders
