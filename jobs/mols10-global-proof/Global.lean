import Mathlib

/-!
E075. Unrestricted incidence-matrix obstruction.
No four-layer or affine decomposition assumption.
This file formalizes the algebraic steps of the rank obstruction.
It does not assert that all SRGs fail it or that 3-MOLS(10) is solved.
-/
open scoped BigOperators
open Finset

namespace MOLS10.E075

theorem class_sums_vanish (s : Fin 5 → ZMod 5)
    (h : ∀ i, (∑ j, s j) = s i) : ∀ i, s i = 0 := by
  have hz : (∑ j, s j) = 0 := by
    calc
      (∑ j, s j) = ∑ _i : Fin 5, (∑ j, s j) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (h i).symm
      _ = 0 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have h5 : (5 : ZMod 5) = 0 := by decide
        rw [h5, zero_mul]
  intro i
  exact (h i).symm.trans hz

theorem dot_divisible_five (d c : ℤ)
    (h : (25 : ℤ) ∣ 10 * d + c) (hc : (25 : ℤ) ∣ c) :
    (5 : ℤ) ∣ d := by
  omega

theorem dot_divisible_two (d c : ℤ)
    (h : (4 : ℤ) ∣ 10 * d + c) (hc : (4 : ℤ) ∣ c) :
    (2 : ℤ) ∣ d := by
  omega

theorem odd_class_sums_contradiction (s q : ℤ)
    (hs : s % 2 = 1) (hq : q % 2 = 0)
    (h : (4 : ℤ) ∣ 10 * s + 2 * q) : False := by
  omega

theorem adjacency_square {R : Type*} [Ring R] (T J : R)
    (h : T * T = 10 * T + 20 * J) :
    (T - 5) * (T - 5) = 25 + 20 * J := by
  calc
    (T - 5) * (T - 5) = T * T - 10 * T + 25 := by noncomm_ring <;> norm_num
    _ = 25 + 20 * J := by rw [h]; noncomm_ring

/-- Exact rank identity when the kernel of the first map is contained
in the range of the second map, and the two maps have equal rank. -/
theorem rank_product_of_kernel_in_range
    {K U V : Type*} [Field K]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : U →ₗ[K] V) (g : V →ₗ[K] U)
    (h : LinearMap.ker f ≤ LinearMap.range g)
    (hr : Module.finrank K (LinearMap.range g) =
      Module.finrank K (LinearMap.range f)) :
    Module.finrank K (LinearMap.range (f.comp g)) +
      Module.finrank K U = 2 * Module.finrank K (LinearMap.range f) := by
  let r : LinearMap.range g →ₗ[K] V := f.comp (LinearMap.range g).subtype
  have hrange : LinearMap.range r = LinearMap.range (f.comp g) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨v, hv⟩ := x.property
      exact ⟨v, by change f (g v) = f x.val; rw [hv]⟩
    · rintro ⟨v, rfl⟩
      exact ⟨⟨g v, ⟨v, rfl⟩⟩, rfl⟩
  let e : LinearMap.ker r ≃ₗ[K] LinearMap.ker f :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      invFun := fun x => ⟨⟨x.val, h x.property⟩, x.property⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hk := e.finrank_eq
  have h1 := r.finrank_range_add_finrank_ker
  have h2 := f.finrank_range_add_finrank_ker
  rw [hrange, hk, hr] at h1
  omega

theorem rank_is_even (r s : ℕ) (h : s + 50 = 2 * r) :
    Even s := by
  refine ⟨r - 25, ?_⟩
  omega

#print axioms class_sums_vanish
#print axioms dot_divisible_five
#print axioms dot_divisible_two
#print axioms odd_class_sums_contradiction
#print axioms adjacency_square
#print axioms rank_product_of_kernel_in_range
#print axioms rank_is_even
end MOLS10.E075
