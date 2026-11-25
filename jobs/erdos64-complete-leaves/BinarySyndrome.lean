import Mathlib

namespace Erdos64Binary
open scoped BigOperators
variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]

def unit (y : Y) : Y → ZMod 2 := fun z => if z = y then 1 else 0

omit [Fintype Y] in
theorem unit_nonzero (y : Y) : unit y ≠ 0 := by
  intro h
  have h' := congrFun h y
  simp [unit] at h'

/-- Full rank, low codimension, and an odd-weight vector force a unit
syndrome. This is an unbounded finite-dimensional theorem, with no SAT
or graph enumeration. -/
theorem kernel_or_unit (F : (X → ZMod 2) →ₗ[ZMod 2] (Y → ZMod 2))
    (hy : Nonempty Y) (hsize : Fintype.card Y ≤ Fintype.card X + 1)
    (hodd : ∃ a, ∑ y, F a y = 1) :
    (∃ a, a ≠ 0 ∧ F a = 0) ∨ (∃ a y, F a = unit y) := by
  classical
  by_contra h
  push Not at h
  have hinj : Function.Injective F := by
    intro a b hab
    by_contra hne
    exact h.1 (a-b) (sub_ne_zero.mpr hne) (by rw [map_sub, hab, sub_self])
  obtain ⟨y0⟩ := hy
  let e := unit y0
  let shift : (X → ZMod 2) × Bool → (Y → ZMod 2) :=
    fun p => F p.1 + if p.2 then e else 0
  have hshift : Function.Injective shift := by
    rintro ⟨a, p⟩ ⟨b, q⟩ heq
    cases p <;> cases q
    · have h' : F a = F b := by simpa [shift] using heq
      simp [hinj h']
    · have h' : F a = F b + e := by simpa [shift] using heq
      have hh : F (a-b) = unit y0 := by
        rw [map_sub, h']
        change F b + e - F b = e
        abel
      exact False.elim (h.2 (a-b) y0 hh)
    · have h' : F a + e = F b := by simpa [shift] using heq
      have hh : F (b-a) = unit y0 := by
        rw [map_sub, ← h']
        change F a + e - F a = e
        abel
      exact False.elim (h.2 (b-a) y0 hh)
    · have h' : F a + e = F b + e := by simpa [shift] using heq
      simp [hinj (add_right_cancel h')]
  have hc : Fintype.card (Y → ZMod 2) ≤ Fintype.card ((X → ZMod 2) × Bool) := by
    simp only [Fintype.card_fun, ZMod.card, Fintype.card_prod, Fintype.card_bool]
    rw [← pow_succ]
    exact Nat.pow_le_pow_right (by decide) hsize
  have hsurj : Function.Surjective shift := by
    by_contra hn
    have := Fintype.card_lt_of_injective_not_surjective shift hshift hn
    omega
  have hex : ∀ y, ∃ a, F a = unit y - e := by
    intro y
    obtain ⟨⟨a,b⟩, hab⟩ := hsurj (unit y)
    cases b
    · have hh : F a = unit y := by simpa [shift] using hab
      exact False.elim (h.2 a y hh)
    · have hh : F a + e = unit y := by simpa [shift] using hab
      exact ⟨a, eq_sub_of_add_eq hh⟩
  choose g hg using hex
  obtain ⟨a, ha⟩ := hodd
  let w := F a
  have hw : ∑ y, w y = 1 := ha
  have hsum : (∑ y, w y • unit y) = w := by
    ext z
    simp [unit, Pi.smul_apply, smul_eq_mul, mul_ite]
  have hval : F (∑ y, w y • g y) = w - e := by
    rw [map_sum]
    simp_rw [map_smul, hg, smul_sub]
    rw [Finset.sum_sub_distrib, hsum, ← Finset.sum_smul, hw, one_smul]
  have hlast : F (a - ∑ y, w y • g y) = unit y0 := by
    rw [map_sub, hval]
    change w - (w-e) = e
    abel
  exact h.2 _ _ hlast

#print axioms unit_nonzero
#print axioms kernel_or_unit
end Erdos64Binary

