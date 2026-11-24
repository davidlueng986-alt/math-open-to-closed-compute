import Mathlib

/-! E077. The relabelling used by the 336-to-79 first-pair reduction.
    All proofs are about actual square functions and orthogonality.
    The finite orbit transports are checked separately in OrbitTable.lean. -/
namespace MOLS10.E077

def Latin {S : Type*} (L : S → S → S) : Prop :=
  (∀ r, Function.Injective (L r)) ∧
  (∀ c, Function.Injective (fun r => L r c))

def Orthogonal {S : Type*} (L K : S → S → S) : Prop :=
  Function.Injective (fun x : S × S => (L x.1 x.2, K x.1 x.2))

def relabel {S : Type*} (s : Equiv.Perm S) (L : S → S → S) (r c : S) : S :=
  s (L (s.symm r) (s.symm c))

theorem relabel_latin {S : Type*} (s : Equiv.Perm S) (L : S → S → S)
    (hL : Latin L) : Latin (relabel s L) := by
  constructor
  · intro r a b h
    exact s.symm.injective (hL.1 (s.symm r) (s.injective h))
  · intro c a b h
    exact s.symm.injective (hL.2 (s.symm c) (s.injective h))

theorem relabel_orthogonal {S : Type*} (s : Equiv.Perm S) (L K : S → S → S)
    (hLK : Orthogonal L K) : Orthogonal (relabel s L) (relabel s K) := by
  intro x y h
  have hL := s.injective (congrArg Prod.fst h)
  have hK := s.injective (congrArg Prod.snd h)
  have hxy : (s.symm x.1, s.symm x.2) = (s.symm y.1, s.symm y.2) :=
    hLK (Prod.ext hL hK)
  exact Prod.ext (s.symm.injective (congrArg Prod.fst hxy))
    (s.symm.injective (congrArg Prod.snd hxy))

theorem inverse_fixes {S : Type*} (s : Equiv.Perm S) (z : S)
    (hz : s z = z) : s.symm z = z := by
  apply s.injective
  rw [Equiv.apply_symm_apply, hz]

theorem commuting_fixes_next {S : Type*} (s : Equiv.Perm S)
    (p : S → S) (z o : S) (hz : s z = z) (hpz : p z = o)
    (hcomm : ∀ x, s (p x) = p (s x)) : s o = o := by
  rw [← hpz, hcomm, hz]

theorem normalized_row_preserved {S : Type*} (s : Equiv.Perm S)
    (L : S → S → S) (z : S) (hz : s z = z) (hrow : ∀ c, L z c = c) :
    ∀ c, relabel s L z c = c := by
  intro c
  simp only [relabel, inverse_fixes s z hz, hrow, Equiv.apply_symm_apply]

theorem normalized_column_preserved {S : Type*} (s : Equiv.Perm S)
    (L : S → S → S) (z : S) (hz : s z = z) (hcol : ∀ r, L r z = r) :
    ∀ r, relabel s L r z = r := by
  intro r
  simp only [relabel, inverse_fixes s z hz, hcol, Equiv.apply_symm_apply]

theorem canonical_second_row_preserved {S : Type*} (s : Equiv.Perm S)
    (L : S → S → S) (p : S → S) (z o : S) (hz : s z = z)
    (hpz : p z = o) (hcomm : ∀ x, s (p x) = p (s x))
    (hrow : ∀ c, L o c = p c) : ∀ c, relabel s L o c = p c := by
  intro c
  have ho := commuting_fixes_next s p z o hz hpz hcomm
  simp only [relabel, inverse_fixes s o ho, hrow, hcomm, Equiv.apply_symm_apply]

theorem initial_pair_transport {S : Type*} (s : Equiv.Perm S)
    (L K : S → S → S) (p : S → S) (z o : S) (hz : s z = z)
    (hpz : p z = o) (hcomm : ∀ x, s (p x) = p (s x)) :
    (relabel s L o z, relabel s K o z) = (s (L o z), s (K o z)) := by
  have ho := commuting_fixes_next s p z o hz hpz hcomm
  simp only [relabel, inverse_fixes s z hz, inverse_fixes s o ho]

#print axioms relabel_latin
#print axioms relabel_orthogonal
#print axioms inverse_fixes
#print axioms commuting_fixes_next
#print axioms normalized_row_preserved
#print axioms normalized_column_preserved
#print axioms canonical_second_row_preserved
#print axioms initial_pair_transport

/-- Ten rows have two equal three-bit parity signatures. -/
theorem common_signature_rows (f : Fin 10 → (Fin 3 → Bool)) :
    ∃ r s, r ≠ s ∧ f r = f s := by
  classical
  by_contra hn
  have hf : Function.Injective f := by
    intro r s h
    by_contra hrs
    exact hn ⟨r, s, hrs, h⟩
  have hc := Fintype.card_le_of_injective f hf
  norm_num at hc

theorem units_eq_of_positive_bit (a b : ℤˣ)
    (h : decide (a = 1) = decide (b = 1)) : a = b := by
  rcases Int.units_eq_one_or a with ha | ha <;>
    rcases Int.units_eq_one_or b with hb | hb <;>
    norm_num [ha, hb] at h ⊢

/-- All three relative second rows can simultaneously be chosen even. -/
theorem simultaneous_even_relative_rows
    (rows : Fin 3 → Fin 10 → Equiv.Perm (Fin 10)) :
    ∃ r s, r ≠ s ∧ ∀ k,
      Equiv.Perm.sign ((rows k r)⁻¹ * rows k s) = 1 := by
  let bits : Fin 10 → (Fin 3 → Bool) :=
    fun r k => decide (Equiv.Perm.sign (rows k r) = 1)
  obtain ⟨r, s, hrs, hbits⟩ := common_signature_rows bits
  refine ⟨r, s, hrs, ?_⟩
  intro k
  have heq : Equiv.Perm.sign (rows k r) = Equiv.Perm.sign (rows k s) :=
    units_eq_of_positive_bit _ _ (congrFun hbits k)
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, heq]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (rows k s)) with h | h <;> simp [h]

theorem conjugation_preserves_sign (s p : Equiv.Perm (Fin 10)) :
    Equiv.Perm.sign (s * p * s⁻¹) = Equiv.Perm.sign p := by
  rw [map_mul, map_mul, map_inv]
  simp [mul_comm, mul_left_comm]

#print axioms common_signature_rows
#print axioms units_eq_of_positive_bit
#print axioms simultaneous_even_relative_rows
#print axioms conjugation_preserves_sign

end MOLS10.E077
