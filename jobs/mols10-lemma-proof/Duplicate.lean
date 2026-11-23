import Mathlib
namespace MOLS10E074Duplicate
abbrev Bit := ZMod 2

private theorem pair_comparison (a0 a1 b0 b1 d0 d1 : Bit)
    (ha : a0+a1=1) (hb : b0+b1=1)
    (h0 : (a0,b0) ≠ (d0,d1)) (h1 : (a1,b1) ≠ (d0,d1)) :
    a0+b0+d0+d1=1 := by
  fin_cases a0 <;> fin_cases a1 <;> fin_cases b0 <;> fin_cases b1 <;>
    fin_cases d0 <;> fin_cases d1 <;> simp_all <;> decide

/-- The point matching e i j is the unique bijection between the two
coarse OA layers induced by their (i,j) projections. -/
theorem three_complementary_directions_impossible
    (a a' d : Fin 3 → Fin 25 → Bit)
    (e : Fin 3 → Fin 3 → Equiv.Perm (Fin 25))
    (hcomp : ∀ i p, a i p + a' i p = 1)
    (h0 : ∀ i j, i ≠ j → ∀ p,
      (a i p,a j p) ≠ (d i (e i j p),d j (e i j p)))
    (h1 : ∀ i j, i ≠ j → ∀ p,
      (a' i p,a' j p) ≠ (d i (e i j p),d j (e i j p))) :
    False := by
  let S (i : Fin 3) : Bit := (∑ p, a i p) + (∑ p, d i p)
  have pairSum (i j : Fin 3) (hij : i ≠ j) : S i + S j = 1 := by
    calc
      _ = ∑ p, (a i p+a j p+d i (e i j p)+d j (e i j p)) := by
        unfold S
        simp only [Finset.sum_add_distrib]
        rw [Equiv.sum_comp (e i j) (d i), Equiv.sum_comp (e i j) (d j)]
        ring
      _ = ∑ _ : Fin 25, (1 : Bit) := Finset.sum_congr rfl (fun p _ =>
        pair_comparison _ _ _ _ _ _ (hcomp i p) (hcomp j p) (h0 i j hij p) (h1 i j hij p))
      _ = 1 := by decide
  have h01 := pairSum 0 1 (by decide)
  have h02 := pairSum 0 2 (by decide)
  have h12 := pairSum 1 2 (by decide)
  have hEq : S 1 = S 2 := add_left_cancel (h01.trans h02.symm)
  rw [← hEq] at h12
  have hz (x : Bit) : x+x=0 := by fin_cases x <;> decide
  rw [hz] at h12
  exact (by decide : (0 : Bit) ≠ 1) h12

#print axioms three_complementary_directions_impossible
end MOLS10E074Duplicate
