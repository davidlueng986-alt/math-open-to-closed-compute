import Mathlib

/-!
E074: odd-order four-layer lifting obstruction.
The theorem applies to arbitrary stacks of four order-five strength-two OAs,
not merely aligned affine cosets. It is conditional on three fully rigid
directions. It does not assume or prove that every order-ten OA is such a stack.
-/
namespace MOLS10E074

abbrev Bit := ZMod 2
abbrev Color := Bit × Bit
def cA : Color := (1, 0)
def cB : Color := (0, 1)
def cC : Color := (1, 1)
def zeroColor : Color := (0, 0)

def color (b : Fin 4 → Bit) : Color := (b 0 + b 1, b 0 + b 2)

-- The three layers 0,1,2 already suffice: distinct pairs imply
-- nonzero and unequal partition colors. The fourth layer is not needed here.
private theorem three_pair_bits (a0 a1 a2 b0 b1 b2 : Bit)
    (h01 : (a0,b0) ≠ (a1,b1))
    (h02 : (a0,b0) ≠ (a2,b2))
    (h12 : (a1,b1) ≠ (a2,b2)) :
    (a0+a1,a0+a2) ≠ zeroColor ∧
    (b0+b1,b0+b2) ≠ zeroColor ∧
    (a0+a1,a0+a2) ≠ (b0+b1,b0+b2) := by
  fin_cases a0 <;> fin_cases a1 <;> fin_cases a2 <;>
    fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;>
    simp_all [zeroColor] <;> decide

theorem orthogonal_colors (a b : Fin 4 → Bit)
    (h : Function.Injective (fun l => (a l,b l))) :
    color a ≠ zeroColor ∧ color b ≠ zeroColor ∧ color a ≠ color b := by
  have h01 : (a 0,b 0) ≠ (a 1,b 1) := fun e => (by decide : (0 : Fin 4) ≠ 1) (h e)
  have h02 : (a 0,b 0) ≠ (a 2,b 2) := fun e => (by decide : (0 : Fin 4) ≠ 2) (h e)
  have h12 : (a 1,b 1) ≠ (a 2,b 2) := fun e => (by decide : (1 : Fin 4) ≠ 2) (h e)
  exact three_pair_bits _ _ _ _ _ _ h01 h02 h12

private theorem color_cases (v : Color) (h : v ≠ zeroColor) :
    v = cA ∨ v = cB ∨ v = cC := by
  rcases v with ⟨a,b⟩
  fin_cases a <;> fin_cases b <;> simp_all [cA,cB,cC,zeroColor] <;> decide

private theorem avoidsA (v : Color) (hn : v ≠ zeroColor) (h : v ≠ cA) :
    v.2 = 1 := by
  rcases color_cases v hn with e | e | e
  · exact False.elim (h e)
  · rw [e]; rfl
  · rw [e]; rfl

private theorem avoidsB (v : Color) (hn : v ≠ zeroColor) (h : v ≠ cB) :
    v.1 = 1 := by
  rcases color_cases v hn with e | e | e
  · rw [e]; rfl
  · exact False.elim (h e)
  · rw [e]; rfl

private theorem avoidsC (v : Color) (hn : v ≠ zeroColor) (h : v ≠ cC) :
    v.1 + v.2 = 1 := by
  rcases color_cases v hn with e | e | e
  · rw [e]; decide
  · rw [e]; decide
  · exact False.elim (h e)

def sumX (f : Fin 5 → Color) : Bit := ∑ t, (f t).1
def sumY (f : Fin 5 → Color) : Bit := ∑ t, (f t).2

-- Odd-order parity, independent of the structure of the four layers.
theorem odd_three_avoidance (fA fB fC : Fin 5 → Color)
    (hA : ∀ t, fA t ≠ zeroColor ∧ fA t ≠ cA)
    (hB : ∀ t, fB t ≠ zeroColor ∧ fB t ≠ cB)
    (hC : ∀ t, fC t ≠ zeroColor ∧ fC t ≠ cC)
    (hxAB : sumX fA = sumX fB) (hxAC : sumX fA = sumX fC)
    (hyAB : sumY fA = sumY fB) (hyAC : sumY fA = sumY fC) :
    False := by
  have hy : sumY fA = 1 := by
    unfold sumY
    calc
      _ = ∑ _ : Fin 5, (1 : Bit) := Finset.sum_congr rfl (fun t _ => avoidsA _ (hA t).1 (hA t).2)
      _ = 1 := by decide
  have hx : sumX fB = 1 := by
    unfold sumX
    calc
      _ = ∑ _ : Fin 5, (1 : Bit) := Finset.sum_congr rfl (fun t _ => avoidsB _ (hB t).1 (hB t).2)
      _ = 1 := by decide
  have hsum : sumX fC + sumY fC = 1 := by
    unfold sumX sumY
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _ : Fin 5, (1 : Bit) := Finset.sum_congr rfl (fun t _ => avoidsC _ (hC t).1 (hC t).2)
      _ = 1 := by decide
  have hx' : sumX fC = 1 := hxAC.symm.trans (hxAB.trans hx)
  have hy' : sumY fC = 1 := hyAC.symm.trans hy
  rw [hx',hy'] at hsum
  exact (by decide : (1 : Bit) + 1 ≠ 1) hsum

-- A coarse fibre has five rows per layer. In each of three other
-- directions, its five buckets reindex those same rows via a permutation.
def bucketColor (b : Fin 4 → Fin 5 → Bit)
    (e : Fin 4 → Equiv.Perm (Fin 5)) (t : Fin 5) : Color :=
  color (fun l => b l (e l t))

theorem sumX_bucket (b : Fin 4 → Fin 5 → Bit)
    (e : Fin 4 → Equiv.Perm (Fin 5)) :
    sumX (bucketColor b e) = (∑ t, b 0 t) + (∑ t, b 1 t) := by
  unfold sumX bucketColor color
  simp only
  rw [Finset.sum_add_distrib]
  congr 1
  · exact Equiv.sum_comp (e 0) (b 0)
  · exact Equiv.sum_comp (e 1) (b 1)

theorem sumY_bucket (b : Fin 4 → Fin 5 → Bit)
    (e : Fin 4 → Equiv.Perm (Fin 5)) :
    sumY (bucketColor b e) = (∑ t, b 0 t) + (∑ t, b 2 t) := by
  unfold sumY bucketColor color
  simp only
  rw [Finset.sum_add_distrib]
  congr 1
  · exact Equiv.sum_comp (e 0) (b 0)
  · exact Equiv.sum_comp (e 2) (b 2)

theorem no_three_constant_partitions (b : Fin 4 → Fin 5 → Bit)
    (eA eB eC : Fin 4 → Equiv.Perm (Fin 5))
    (hA : ∀ t, bucketColor b eA t ≠ zeroColor ∧ bucketColor b eA t ≠ cA)
    (hB : ∀ t, bucketColor b eB t ≠ zeroColor ∧ bucketColor b eB t ≠ cB)
    (hC : ∀ t, bucketColor b eC t ≠ zeroColor ∧ bucketColor b eC t ≠ cC) :
    False := by
  exact odd_three_avoidance _ _ _ hA hB hC
    ((sumX_bucket b eA).trans (sumX_bucket b eB).symm)
    ((sumX_bucket b eA).trans (sumX_bucket b eC).symm)
    ((sumY_bucket b eA).trans (sumY_bucket b eB).symm)
    ((sumY_bucket b eA).trans (sumY_bucket b eC).symm)

-- Any three pairwise distinct nonzero colors exhaust the three colors.
private theorem avoidAll (a b c d : Color)
    (ha : a ≠ zeroColor) (hb : b ≠ zeroColor) (hc : c ≠ zeroColor)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hd : d ≠ zeroColor) (hda : d ≠ a) (hdb : d ≠ b) (hdc : d ≠ c) : False := by
  rcases color_cases a ha with ea|ea|ea <;>
    rcases color_cases b hb with eb|eb|eb <;>
    rcases color_cases c hc with ec|ec|ec <;>
    rcases color_cases d hd with ed|ed|ed <;>
    simp_all

-- A full layer stack supplies bucket permutations by strength two.
-- The fields are consequences of the desired fine OA, not hypotheses about
-- the existence of such a stack. This structure records the minimal data
-- needed from four directions and a chosen fibre of a fourth direction.
structure RigidTripleData where
  b : Fin 4 → Fin 5 → Bit
  eA : Fin 4 → Equiv.Perm (Fin 5)
  eB : Fin 4 → Equiv.Perm (Fin 5)
  eC : Fin 4 → Equiv.Perm (Fin 5)
  hA : ∀ t, bucketColor b eA t ≠ zeroColor ∧ bucketColor b eA t ≠ cA
  hB : ∀ t, bucketColor b eB t ≠ zeroColor ∧ bucketColor b eB t ≠ cB
  hC : ∀ t, bucketColor b eC t ≠ zeroColor ∧ bucketColor b eC t ≠ cC

theorem rigid_triple_impossible (s : RigidTripleData) : False :=
  no_three_constant_partitions s.b s.eA s.eB s.eC s.hA s.hB s.hC

#print axioms orthogonal_colors
#print axioms odd_three_avoidance
#print axioms no_three_constant_partitions
#print axioms rigid_triple_impossible

end MOLS10E074
