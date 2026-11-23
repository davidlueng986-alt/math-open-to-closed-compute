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
  fin_cases a <;> fin_cases b
  · exact (h (by decide)).elim
  · decide
  · decide
  · decide

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
    (_hyAB : sumY fA = sumY fB) (hyAC : sumY fA = sumY fC) :
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


-- The avoidance lemma in coordinate-free form.
private theorem odd_avoidance_sum (f : Fin 5 → Color) (c : Color)
    (hc : c ≠ zeroColor) (h : ∀ t, f t ≠ zeroColor ∧ f t ≠ c) :
    (sumX f, sumY f) ≠ zeroColor ∧ (sumX f, sumY f) ≠ c := by
  rcases color_cases c hc with e | e | e
  · subst c
    have hy : sumY f = 1 := by
      unfold sumY
      calc
        _ = ∑ _ : Fin 5, (1 : Bit) := Finset.sum_congr rfl (fun t _ => avoidsA _ (h t).1 (h t).2)
        _ = 1 := by decide
    constructor <;> intro eq
    · have z : sumY f = 0 := congrArg Prod.snd eq
      exact (by decide : (1 : Bit) ≠ 0) (hy.symm.trans z)
    · have z : sumY f = 0 := congrArg Prod.snd eq
      exact (by decide : (1 : Bit) ≠ 0) (hy.symm.trans z)
  · subst c
    have hx : sumX f = 1 := by
      unfold sumX
      calc
        _ = ∑ _ : Fin 5, (1 : Bit) := Finset.sum_congr rfl (fun t _ => avoidsB _ (h t).1 (h t).2)
        _ = 1 := by decide
    constructor <;> intro eq
    · have z : sumX f = 0 := congrArg Prod.fst eq
      exact (by decide : (1 : Bit) ≠ 0) (hx.symm.trans z)
    · have z : sumX f = 0 := congrArg Prod.fst eq
      exact (by decide : (1 : Bit) ≠ 0) (hx.symm.trans z)
  · subst c
    have hs : sumX f + sumY f = 1 := by
      unfold sumX sumY
      rw [← Finset.sum_add_distrib]
      calc
        _ = ∑ _ : Fin 5, (1 : Bit) := Finset.sum_congr rfl (fun t _ => avoidsC _ (h t).1 (h t).2)
        _ = 1 := by decide
    constructor <;> intro eq
    · have hx : sumX f = 0 := congrArg Prod.fst eq
      have hy : sumY f = 0 := congrArg Prod.snd eq
      rw [hx, hy] at hs
      exact (by decide : (0 : Bit) + 0 ≠ 1) hs
    · have hx : sumX f = 1 := congrArg Prod.fst eq
      have hy : sumY f = 1 := congrArg Prod.snd eq
      rw [hx, hy] at hs
      exact (by decide : (1 : Bit) + 1 ≠ 1) hs

theorem arbitrary_three_partitions (b : Fin 4 → Fin 5 → Bit)
    (ea eb ec : Fin 4 → Equiv.Perm (Fin 5)) (a d c : Color)
    (ha : a ≠ zeroColor) (hd : d ≠ zeroColor) (hc : c ≠ zeroColor)
    (had : a ≠ d) (hac : a ≠ c) (hdc : d ≠ c)
    (hA : ∀ t, bucketColor b ea t ≠ zeroColor ∧ bucketColor b ea t ≠ a)
    (hB : ∀ t, bucketColor b eb t ≠ zeroColor ∧ bucketColor b eb t ≠ d)
    (hC : ∀ t, bucketColor b ec t ≠ zeroColor ∧ bucketColor b ec t ≠ c) :
    False := by
  have h1 := odd_avoidance_sum _ a ha hA
  have h2 := odd_avoidance_sum _ d hd hB
  have h3 := odd_avoidance_sum _ c hc hC
  have eqB : (sumX (bucketColor b ea), sumY (bucketColor b ea)) =
      (sumX (bucketColor b eb), sumY (bucketColor b eb)) := by
    rw [sumX_bucket, sumY_bucket, sumX_bucket, sumY_bucket]
  have eqC : (sumX (bucketColor b ea), sumY (bucketColor b ea)) =
      (sumX (bucketColor b ec), sumY (bucketColor b ec)) := by
    rw [sumX_bucket, sumY_bucket, sumX_bucket, sumY_bucket]
  rw [← eqB] at h2
  rw [← eqC] at h3
  exact avoidAll a d c _ ha hd hc had hac hdc h1.1 h1.2 h2.2 h3.2

/-- A four-layer strength-two OA lifting provides these data by indexing
each fibre in each layer and reindexing it via the other coordinate. -/
structure LayeredLift where
  bits : Fin 5 → Fin 5 → Fin 4 → Fin 5 → Bit
  index : Fin 5 → Fin 5 → Fin 5 → Fin 4 → Equiv.Perm (Fin 5)
  orthogonal : ∀ i j : Fin 5, i ≠ j → ∀ u v : Fin 5,
    Function.Injective (fun l =>
      (bits i u l (index i u j l v), bits j v l (index j v i l u)))

def FullyRigid (s : LayeredLift) (i : Fin 5) (f : Fin 5 → Color) : Prop :=
  ∀ u j v, i ≠ j → bucketColor (s.bits i u) (s.index i u j) v = f u

private theorem rigid_pair (s : LayeredLift) (i j u v : Fin 5)
    (hij : i ≠ j) (fi fj : Fin 5 → Color)
    (hi : FullyRigid s i fi) (hj : FullyRigid s j fj) :
    fi u ≠ zeroColor ∧ fj v ≠ zeroColor ∧ fi u ≠ fj v := by
  have h := orthogonal_colors _ _ (s.orthogonal i j hij u v)
  change bucketColor (s.bits i u) (s.index i u j) v ≠ zeroColor ∧
    bucketColor (s.bits j v) (s.index j v i) u ≠ zeroColor ∧
    bucketColor (s.bits i u) (s.index i u j) v ≠
      bucketColor (s.bits j v) (s.index j v i) u at h
  rw [hi u j v hij, hj v i u (Ne.symm hij)] at h
  exact h

private theorem avoidsRigid (s : LayeredLift) (i j u v : Fin 5)
    (hij : i ≠ j) (fj : Fin 5 → Color) (hj : FullyRigid s j fj) :
    bucketColor (s.bits i u) (s.index i u j) v ≠ zeroColor ∧
    bucketColor (s.bits i u) (s.index i u j) v ≠ fj v := by
  have h := orthogonal_colors _ _ (s.orthogonal i j hij u v)
  change bucketColor (s.bits i u) (s.index i u j) v ≠ zeroColor ∧
    bucketColor (s.bits j v) (s.index j v i) u ≠ zeroColor ∧
    bucketColor (s.bits i u) (s.index i u j) v ≠
      bucketColor (s.bits j v) (s.index j v i) u at h
  rw [hj v i u (Ne.symm hij)] at h
  exact ⟨h.1, h.2.2⟩

/-- No three fully rigid directions in a four-layer lift of odd order five.
No assumption that every OA(100,5,10,2) admits such a layered representation. -/
theorem no_three_rigid_directions (s : LayeredLift) (i j k l : Fin 5)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hli : l ≠ i) (hlj : l ≠ j) (hlk : l ≠ k)
    (fi fj fk : Fin 5 → Color)
    (hi : FullyRigid s i fi) (hj : FullyRigid s j fj) (hk : FullyRigid s k fk) :
    False := by
  have p := rigid_pair s i j 0 0 hij fi fj hi hj
  have q := rigid_pair s i k 0 0 hik fi fk hi hk
  have r := rigid_pair s j k 0 0 hjk fj fk hj hk
  have hI (u : Fin 5) : fi u = fi 0 := by
    by_contra h
    have p' := rigid_pair s i j u 0 hij fi fj hi hj
    have q' := rigid_pair s i k u 0 hik fi fk hi hk
    exact avoidAll _ _ _ _ p.1 p.2.1 q.2.1 p.2.2 q.2.2 r.2.2
      p'.1 h p'.2.2 q'.2.2
  have hJ (u : Fin 5) : fj u = fj 0 := by
    by_contra h
    have p' := rigid_pair s i j 0 u hij fi fj hi hj
    have r' := rigid_pair s j k u 0 hjk fj fk hj hk
    exact avoidAll _ _ _ _ p.1 p.2.1 q.2.1 p.2.2 q.2.2 r.2.2
      p'.2.1 (Ne.symm p'.2.2) h r'.2.2
  have hK (u : Fin 5) : fk u = fk 0 := by
    by_contra h
    have q' := rigid_pair s i k 0 u hik fi fk hi hk
    have r' := rigid_pair s j k 0 u hjk fj fk hj hk
    exact avoidAll _ _ _ _ p.1 p.2.1 q.2.1 p.2.2 q.2.2 r.2.2
      q'.2.1 (Ne.symm q'.2.2) (Ne.symm r'.2.2) h
  apply arbitrary_three_partitions (s.bits l 0) (s.index l 0 i)
    (s.index l 0 j) (s.index l 0 k) (fi 0) (fj 0) (fk 0)
    p.1 p.2.1 q.2.1 p.2.2 q.2.2 r.2.2
  · intro v
    simpa only [hI v] using avoidsRigid s l i 0 v hli fi hi
  · intro v
    simpa only [hJ v] using avoidsRigid s l j 0 v hlj fj hj
  · intro v
    simpa only [hK v] using avoidsRigid s l k 0 v hlk fk hk

-- Abstract arithmetic behind the cyclotomic Fourier-rank lemma.
def det3 {R : Type*} [CommRing R] (m : Fin 3 → Fin 3 → R) : R :=
  m 0 0 * (m 1 1 * m 2 2 - m 1 2 * m 2 1) -
  m 0 1 * (m 1 0 * m 2 2 - m 1 2 * m 2 0) +
  m 0 2 * (m 1 0 * m 2 1 - m 1 1 * m 2 0)

def geom {R : Type*} [CommRing R] (z : R) (e : ℕ) : R :=
  ∑ k ∈ Finset.range e, z ^ k

private theorem geom_mul {R : Type*} [CommRing R] (z : R) (e : ℕ) :
    (z - 1) * geom z e = z ^ e - 1 := by
  induction e with
  | zero => simp [geom]
  | succ e ih =>
    unfold geom at *
    rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
    ring

private theorem map_geom {R : Type*} [CommRing R] (φ : R →+* ZMod 5)
    (z : R) (hz : φ z = 1) (e : ℕ) :
    φ (geom z e) = (e : ZMod 5) := by
  simp [geom, map_sum, hz]

theorem cyclotomic_det_nonzero {R : Type*} [CommRing R] [IsDomain R]
    (φ : R →+* ZMod 5) (z : R) (hz : φ z = 1) (hz' : z ≠ 1)
    (e : Fin 3 → Fin 3 → ℕ)
    (h : det3 (fun i j => (e i j : ZMod 5)) ≠ 0) :
    det3 (fun i j => z ^ e i j - 1) ≠ 0 := by
  have hn : det3 (fun i j => geom z (e i j)) ≠ 0 := by
    intro h0
    apply h
    have hm := congrArg φ h0
    simpa [det3, map_geom φ z hz] using hm
  have heq : det3 (fun i j => z ^ e i j - 1) =
      (z - 1)^3 * det3 (fun i j => geom z (e i j)) := by
    simp only [← geom_mul z]
    unfold det3
    ring
  rw [heq]
  exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hz')) hn

#print axioms arbitrary_three_partitions
#print axioms no_three_rigid_directions
#print axioms cyclotomic_det_nonzero

end MOLS10E074
