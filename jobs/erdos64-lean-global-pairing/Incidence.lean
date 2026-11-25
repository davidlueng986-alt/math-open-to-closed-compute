import BinarySyndrome
import PairedShadow

namespace Erdos64Incidence
open SimpleGraph Erdos64Closure Erdos64Paired
open scoped BigOperators
universe u
variable {V X Y : Type u}
variable [Fintype X] [Fintype Y]

def syndrome (R : X → Y → Prop) [DecidableRel R] :
    (X → ZMod 2) →ₗ[ZMod 2] (Y → ZMod 2) where
  toFun z y := ∑ x, if R x y then z x else 0
  map_add' a b := by
    ext y
    change (∑ x, if R x y then a x+b x else 0) =
      (∑ x, if R x y then a x else 0)+(∑ x, if R x y then b x else 0)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : R x y <;> simp [h]
  map_smul' m a := by
    ext y
    change (∑ x, if R x y then m*a x else 0) =
      m*(∑ x, if R x y then a x else 0)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : R x y <;> simp [h]

theorem field_cases (a : ZMod 2) : a=0 ∨ a=1 := by
  have ha : a.val < 2 := ZMod.val_lt a
  have h : a.val = 0 ∨ a.val = 1 := by omega
  rcases h with h | h
  · left
    apply ZMod.val_injective 2
    rw [h]
    decide
  · right
    apply ZMod.val_injective 2
    rw [h]
    decide

theorem indicator_sum {T : Type*} [Fintype T] (P : T → Prop) [DecidablePred P] :
    (∑ t, if P t then (1 : ZMod 2) else 0) =
    (Fintype.card {t // P t} : ZMod 2) := by
  rw [Fintype.card_subtype, ← Finset.sum_filter]
  simp

omit [Fintype Y] in
theorem syndrome_unit [DecidableEq X] (R : X → Y → Prop) [DecidableRel R]
    (a : X) (y : Y) :
    syndrome R (Erdos64Binary.unit a) y = if R a y then 1 else 0 := by
  classical
  change (∑ x, if R x y then Erdos64Binary.unit a x else 0) = (if R a y then (1 : ZMod 2) else 0)
  calc
    (∑ x, if R x y then Erdos64Binary.unit a x else 0) =
        ∑ x, if x=a then (if R a y then (1 : ZMod 2) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : x=a
      · subst x
        simp [Erdos64Binary.unit]
      · simp [Erdos64Binary.unit,h]
    _ = _ := by simp

abbrev Support (z : X → ZMod 2) := {x : X // z x=1}

omit [Fintype Y] in
theorem support_row (R : X → Y → Prop) [DecidableRel R]
    (z : X → ZMod 2) (y : Y) :
    (Fintype.card {x : Support z // R x.1 y} : ZMod 2) = syndrome R z y := by
  let e : {x : Support z // R x.1 y} ≃ {x : X // R x y ∧ z x=1} :=
    { toFun := fun x => ⟨x.1.1,x.2,x.1.2⟩
      invFun := fun x => ⟨⟨x.1,x.2.2⟩,x.2.1⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  rw [Fintype.card_congr e, ← indicator_sum]
  change (∑ x, if R x y ∧ z x=1 then 1 else 0) =
    ∑ x, if R x y then z x else 0
  apply Finset.sum_congr rfl
  intro x _
  rcases field_cases (z x) with hz | hz <;> by_cases h : R x y <;> simp [h,hz]

omit [Fintype Y] in
theorem support_row_le (R : X → Y → Prop) [DecidableRel R]
    (z : X → ZMod 2) (y : Y) :
    Fintype.card {x : Support z // R x.1 y} ≤ Fintype.card {x : X // R x y} := by
  exact Fintype.card_le_of_injective
    (fun x : {x : Support z // R x.1 y} => (⟨x.1.1,x.2⟩ : {x : X // R x y}))
    (by intro a b h; apply Subtype.ext; apply Subtype.ext; exact congrArg (fun t : {x : X // R x y} => t.val) h)

omit [Fintype Y] in
theorem support_row_mod (R : X → Y → Prop) [DecidableRel R]
    (z : X → ZMod 2) (y : Y) :
    Fintype.card {x : Support z // R x.1 y} % 2 = (syndrome R z y).val := by
  simpa only [ZMod.val_natCast] using congrArg ZMod.val (support_row R z y)

omit [Fintype X] in
theorem support_nonempty (z : X → ZMod 2) (hz : z ≠ 0) :
    Nonempty (Support z) := by
  by_contra h
  apply hz
  ext x
  rcases field_cases (z x) with h0 | h1
  · exact h0
  · exact False.elim (h ⟨⟨x,h1⟩⟩)

theorem card_remove_one {T : Type*} [Fintype T] [DecidableEq T]
    (P : T → Prop) [DecidablePred P] (a : T) (ha : P a) :
    Fintype.card {t // P t ∧ t≠a} + 1 = Fintype.card {t // P t} := by
  rw [Fintype.card_subtype, Fintype.card_subtype]
  have h : (Finset.univ.filter (fun t => P t ∧ t≠a)) =
      (Finset.univ.filter P).erase a := by
    ext t
    simp [and_comm]
  rw [h]
  exact Finset.card_erase_add_one (by simp [ha])

/-- Actual graph-level near condition follows from row pairing,
    minimum selected incidence degree two and at most one exception. -/
theorem safe_step_of_rows (G : SimpleGraph V) [Fintype V]
    (f : X → V) (g : Y → V) (hf : Function.Injective f)
    (hg : Function.Injective g) (hsep : ∀ x y, f x ≠ g y)
    (R : X → Y → Prop) [DecidableRel R]
    (hR : ∀ x y, R x y → G.Adj (f x) (g y))
    (hY : Nonempty Y) (hsize : Fintype.card X < Fintype.card V)
    (hrow : ∀ y, Fintype.card {x // R x y}=0 ∨ Fintype.card {x // R x y}=2)
    (w : X) (hdeg : ∀ x, 2 ≤ Fintype.card {y // R x y})
    (hrest : ∀ x, x≠w → 3 ≤ Fintype.card {y // R x y})
    (hfree : ¬HasPower G) : SafeStep G := by
  classical
  have hp : Paired R := by
    apply paired_of_two_rows
    intro y
    simpa only [Fintype.card_subtype] using hrow y
  have hn : 0 < Fintype.card {y // R w y} := by have := hdeg w; omega
  obtain ⟨⟨y,hy⟩⟩ := Fintype.card_pos_iff.mp hn
  obtain ⟨a,ha,_⟩ := hp y w hy
  exact safe_step_of_paired_incidence G f g hf hg hsep R hR hp hY hsize
    ⟨a,w,hrest a ha.1,hrest⟩ hfree

/-- End-to-end unbounded safe step: the parity support and row deletion
are derived by Lean, NOT supplied by SAT or a computational witness.

The ordinary branch side has incidence degree exactly three, the
midpoint side at most three, and the number of midpoint vertices
is at most one more than the number of ordinary branches. -/
theorem safe_step_of_low_codim_incidence (G : SimpleGraph V) [Fintype V]
    (f : X → V) (g : Y → V) (hf : Function.Injective f)
    (hg : Function.Injective g) (hsep : ∀ x y, f x ≠ g y)
    (R : X → Y → Prop) [DecidableRel R]
    (hR : ∀ x y, R x y → G.Adj (f x) (g y))
    (hX : Nonempty X) (hY : Nonempty Y)
    (hsize : Fintype.card X < Fintype.card V)
    (hcodim : Fintype.card Y ≤ Fintype.card X + 1)
    (hbranch : ∀ x, Fintype.card {y // R x y}=3)
    (hmid : ∀ y, Fintype.card {x // R x y}≤3)
    (hfree : ¬HasPower G) : SafeStep G := by
  classical
  have hodd : ∃ z, ∑ y, syndrome R z y = 1 := by
    obtain ⟨x⟩ := hX
    refine ⟨Erdos64Binary.unit x, ?_⟩
    simp_rw [syndrome_unit]
    rw [indicator_sum, hbranch]
    decide
  rcases Erdos64Binary.kernel_or_unit (syndrome R) hY hcodim hodd with
    ⟨z,hz,hzero⟩ | ⟨z,y0,hunit⟩
  · let S := Support z
    let R0 : S → Y → Prop := fun x y => R x.1 y
    let _ : DecidableRel R0 := fun x y => Classical.propDecidable (R0 x y)
    let f0 : S → V := fun x => f x.1
    have hf0 : Function.Injective f0 := fun _ _ h => Subtype.ext (hf h)
    have hsize0 : Fintype.card S < Fintype.card V :=
      (Fintype.card_subtype_le _).trans_lt hsize
    obtain ⟨w⟩ := support_nonempty z hz
    have hrow (y : Y) :
        Fintype.card {x // R0 x y}=0 ∨ Fintype.card {x // R0 x y}=2 := by
      have hm := support_row_mod R z y
      rw [congrFun hzero y] at hm
      simp at hm
      have hb := (support_row_le R z y).trans (hmid y)
      have he : Fintype.card {x : S // R0 x y} = Fintype.card {x : Support z // R x.1 y} :=
        Fintype.card_congr (Equiv.subtypeEquivRight (fun x => Iff.rfl))
      omega
    have hc (x : S) : Fintype.card {y // R0 x y} = Fintype.card {y // R x.1 y} :=
      Fintype.card_congr (Equiv.subtypeEquivRight (fun y => Iff.rfl))
    have hdeg (x : S) : 3 ≤ Fintype.card {y // R0 x y} := by
      rw [hc, hbranch]
    exact safe_step_of_rows G f0 g hf0 hg (fun x y => hsep x.1 y) R0
      (fun x y h => hR x.1 y h) hY hsize0 hrow w
      (fun x => (by decide : 2 ≤ 3).trans (hdeg x))
      (fun x _ => hdeg x) hfree
  · let S := Support z
    let f0 : S → V := fun x => f x.1
    have hf0 : Function.Injective f0 := fun _ _ h => Subtype.ext (hf h)
    have hsize0 : Fintype.card S < Fintype.card V :=
      (Fintype.card_subtype_le _).trans_lt hsize
    have hpar (y : Y) : Fintype.card {x : S // R x.1 y}%2 =
        if y=y0 then 1 else 0 := by
      have hm := support_row_mod R z y
      rw [congrFun hunit y] at hm
      by_cases h : y=y0
      · simp [Erdos64Binary.unit,h] at hm ⊢
        exact hm
      · simp [Erdos64Binary.unit,h] at hm ⊢
        exact hm
    have hpos : 0 < Fintype.card {x : S // R x.1 y0} := by
      have h := hpar y0
      simp at h
      omega
    obtain ⟨⟨w,hw⟩⟩ := Fintype.card_pos_iff.mp hpos
    let R1 : S → Y → Prop := fun x y => R x.1 y ∧ (x≠w ∨ y≠y0)
    let _ : DecidableRel R1 := fun x y => Classical.propDecidable (R1 x y)
    have hrow (y : Y) :
        Fintype.card {x // R1 x y}=0 ∨ Fintype.card {x // R1 x y}=2 := by
      have hb : Fintype.card {x : S // R x.1 y} ≤3 :=
        (support_row_le R z y).trans (hmid y)
      have hp := hpar y
      by_cases hy : y=y0
      · subst y
        have hc : Fintype.card {x // R1 x y0}+1 =
            Fintype.card {x : S // R x.1 y0} := by
          have he : Fintype.card {x // R1 x y0} =
            Fintype.card {x : S // R x.1 y0 ∧ x≠w} :=
            Fintype.card_congr (Equiv.subtypeEquivRight (fun x => by simp [R1]))
          rw [he]
          exact card_remove_one (fun x : S => R x.1 y0) w hw
        simp at hp
        omega
      · have he : Fintype.card {x // R1 x y} =
            Fintype.card {x : S // R x.1 y} :=
          Fintype.card_congr (Equiv.subtypeEquivRight (fun x => by simp [R1,hy]))
        simp [hy] at hp
        omega
    have hdeg (x : S) : 2 ≤ Fintype.card {y // R1 x y} := by
      by_cases hx : x=w
      · subst x
        have he : Fintype.card {y // R1 w y} =
            Fintype.card {y // R w.1 y ∧ y≠y0} :=
          Fintype.card_congr (Equiv.subtypeEquivRight (fun y => by simp [R1]))
        have hcard := card_remove_one (R w.1) y0 hw
        rw [hbranch] at hcard
        omega
      · have he : Fintype.card {y // R1 x y} = Fintype.card {y // R x.1 y} :=
          Fintype.card_congr (Equiv.subtypeEquivRight (fun y => by simp [R1,hx]))
        rw [he,hbranch]
        decide
    have hrest (x : S) (hx : x≠w) : 3 ≤ Fintype.card {y // R1 x y} := by
      have he : Fintype.card {y // R1 x y} = Fintype.card {y // R x.1 y} :=
        Fintype.card_congr (Equiv.subtypeEquivRight (fun y => by simp [R1,hx]))
      rw [he,hbranch]
    exact safe_step_of_rows G f0 g hf0 hg (fun x y => hsep x.1 y) R1
      (fun x y h => hR x.1 y h.1) hY hsize0 hrow w hdeg hrest hfree

#print axioms syndrome_unit
#print axioms support_row
#print axioms card_remove_one
#print axioms safe_step_of_rows
#print axioms safe_step_of_low_codim_incidence

end Erdos64Incidence
