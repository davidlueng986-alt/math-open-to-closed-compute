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
end MOLS10.E077
