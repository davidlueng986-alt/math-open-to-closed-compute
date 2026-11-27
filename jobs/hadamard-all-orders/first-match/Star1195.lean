import Std

namespace HadamardAllOrders

/-- The determinant's remaining factor when the smaller positive class count is 2i. -/
def star1195Product (i : Nat) : Nat := 1197*(4*i+1)*(1197-4*i)

private theorem star1195_checked :
    (List.range 149).all (fun j =>
      let q := star1195Product (j+1)
      decide (q.sqrt*q.sqrt ≠ q)) = true := by
  decide +kernel

theorem star1195_sqrt_square_ne (i : Nat) (positive : 0 < i) (bound : i < 150) :
    (star1195Product i).sqrt*(star1195Product i).sqrt ≠ star1195Product i := by
  have mem : i-1 ∈ List.range 149 := List.mem_range.mpr (by omega)
  have checked := List.all_eq_true.mp star1195_checked (i-1) mem
  simpa [show i-1+1 = i by omega] using checked

theorem star1195_no_square (i : Nat) (positive : 0 < i) (bound : i < 150) :
    ¬ ∃ s : Nat, s*s = star1195Product i := by
  rintro ⟨s, eq⟩
  let q := star1195Product i
  change s*s = q at eq
  have lo := Nat.sqrt_le q
  have hi := Nat.lt_succ_sqrt q
  have root_le : q.sqrt ≤ s := by
    by_cases h : s < q.sqrt
    · have impossible := Nat.mul_self_lt_mul_self h
      omega
    · omega
  have root_ge : s ≤ q.sqrt := by
    by_cases h : q.sqrt < s
    · have impossible := Nat.mul_self_le_mul_self (show q.sqrt.succ ≤ s by omega)
      omega
    · omega
  have root : q.sqrt = s := by omega
  apply star1195_sqrt_square_ne i positive bound
  change q.sqrt*q.sqrt = q
  rwa [root]

private theorem star1195_ordered_split_no_square {u v : Nat} (total : u+v = 598)
    (positive : 0 < u) (smaller : u ≤ v) (even : u%2 = 0) :
    ¬ ∃ s : Nat, s*s = 1197*(2*u+1)*(2*v+1) := by
  have eq : star1195Product (u/2) = 1197*(2*u+1)*(2*v+1) := by
    unfold star1195Product
    rw [show 4*(u/2)+1 = 2*u+1 by omega, show 1197-4*(u/2) = 2*v+1 by omega]
  rw [← eq]
  exact star1195_no_square (u/2) (by omega) (by omega)

/-- The finite arithmetic exclusion for every positive even split of k=598. -/
theorem star1195_even_split_no_square {u v : Nat} (total : u+v = 598)
    (positiveU : 0 < u) (positiveV : 0 < v) (evenU : u%2 = 0) (evenV : v%2 = 0) :
    ¬ ∃ s : Nat, s*s = 1197*(2*u+1)*(2*v+1) := by
  by_cases order : u ≤ v
  · exact star1195_ordered_split_no_square total positiveU order evenU
  · rw [show 1197*(2*u+1)*(2*v+1) = 1197*(2*v+1)*(2*u+1) by ac_rfl]
    exact star1195_ordered_split_no_square (by omega) positiveV (by omega) evenV

#print axioms star1195_sqrt_square_ne
#print axioms star1195_no_square
#print axioms star1195_even_split_no_square

end HadamardAllOrders
