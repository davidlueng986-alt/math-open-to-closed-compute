import Wave8Agent5Core

namespace E64Wave8Agent5
open SimpleGraph
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def petersenEdges : List (Fin 10 × Fin 10) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(5,7),(7,9),(9,6),(6,8),(8,5),(0,5),(1,6),(2,7),(3,8),(4,9)]

def Petersen : SimpleGraph (Fin 10) where
  Adj u v := (u, v) ∈ petersenEdges ∨ (v, u) ∈ petersenEdges
  symm := ⟨by intro u v h; exact h.elim Or.inr Or.inl⟩
  loopless := ⟨by intro u; fin_cases u <;> decide⟩

instance : DecidableRel Petersen.Adj := fun u v =>
  inferInstanceAs (Decidable ((u, v) ∈ petersenEdges ∨ (v, u) ∈ petersenEdges))

def pT0x : Petersen.Walk 0 2 := (.cons (show Petersen.Adj 0 1 by decide) (.cons (show Petersen.Adj 1 2 by decide) .nil))
def pT0y : Petersen.Walk 0 2 := (.cons (show Petersen.Adj 0 4 by decide) (.cons (show Petersen.Adj 4 3 by decide) (.cons (show Petersen.Adj 3 2 by decide) .nil)))
def pT0z : Petersen.Walk 0 2 := (.cons (show Petersen.Adj 0 5 by decide) (.cons (show Petersen.Adj 5 7 by decide) (.cons (show Petersen.Adj 7 2 by decide) .nil)))
def pT1x : Petersen.Walk 0 3 := (.cons (show Petersen.Adj 0 4 by decide) (.cons (show Petersen.Adj 4 3 by decide) .nil))
def pT1y : Petersen.Walk 0 3 := (.cons (show Petersen.Adj 0 1 by decide) (.cons (show Petersen.Adj 1 2 by decide) (.cons (show Petersen.Adj 2 3 by decide) .nil)))
def pT1z : Petersen.Walk 0 3 := (.cons (show Petersen.Adj 0 5 by decide) (.cons (show Petersen.Adj 5 8 by decide) (.cons (show Petersen.Adj 8 3 by decide) .nil)))
def pT2x : Petersen.Walk 0 6 := (.cons (show Petersen.Adj 0 1 by decide) (.cons (show Petersen.Adj 1 6 by decide) .nil))
def pT2y : Petersen.Walk 0 6 := (.cons (show Petersen.Adj 0 4 by decide) (.cons (show Petersen.Adj 4 9 by decide) (.cons (show Petersen.Adj 9 6 by decide) .nil)))
def pT2z : Petersen.Walk 0 6 := (.cons (show Petersen.Adj 0 5 by decide) (.cons (show Petersen.Adj 5 8 by decide) (.cons (show Petersen.Adj 8 6 by decide) .nil)))
def pT3x : Petersen.Walk 0 7 := (.cons (show Petersen.Adj 0 5 by decide) (.cons (show Petersen.Adj 5 7 by decide) .nil))
def pT3y : Petersen.Walk 0 7 := (.cons (show Petersen.Adj 0 1 by decide) (.cons (show Petersen.Adj 1 2 by decide) (.cons (show Petersen.Adj 2 7 by decide) .nil)))
def pT3z : Petersen.Walk 0 7 := (.cons (show Petersen.Adj 0 4 by decide) (.cons (show Petersen.Adj 4 9 by decide) (.cons (show Petersen.Adj 9 7 by decide) .nil)))
def pT4x : Petersen.Walk 0 8 := (.cons (show Petersen.Adj 0 5 by decide) (.cons (show Petersen.Adj 5 8 by decide) .nil))
def pT4y : Petersen.Walk 0 8 := (.cons (show Petersen.Adj 0 1 by decide) (.cons (show Petersen.Adj 1 6 by decide) (.cons (show Petersen.Adj 6 8 by decide) .nil)))
def pT4z : Petersen.Walk 0 8 := (.cons (show Petersen.Adj 0 4 by decide) (.cons (show Petersen.Adj 4 3 by decide) (.cons (show Petersen.Adj 3 8 by decide) .nil)))
def pT5x : Petersen.Walk 0 9 := (.cons (show Petersen.Adj 0 4 by decide) (.cons (show Petersen.Adj 4 9 by decide) .nil))
def pT5y : Petersen.Walk 0 9 := (.cons (show Petersen.Adj 0 1 by decide) (.cons (show Petersen.Adj 1 6 by decide) (.cons (show Petersen.Adj 6 9 by decide) .nil)))
def pT5z : Petersen.Walk 0 9 := (.cons (show Petersen.Adj 0 5 by decide) (.cons (show Petersen.Adj 5 7 by decide) (.cons (show Petersen.Adj 7 9 by decide) .nil)))

def pC0 : Petersen.Walk 0 0 := (.cons (show Petersen.Adj 0 4 by decide) (.cons (show Petersen.Adj 4 9 by decide) (.cons (show Petersen.Adj 9 6 by decide) (.cons (show Petersen.Adj 6 1 by decide) (.cons (show Petersen.Adj 1 2 by decide) (.cons (show Petersen.Adj 2 7 by decide) (.cons (show Petersen.Adj 7 5 by decide) (.cons (show Petersen.Adj 5 0 by decide) .nil))))))))
def pC1 : Petersen.Walk 0 0 := (.cons (show Petersen.Adj 0 4 by decide) (.cons (show Petersen.Adj 4 3 by decide) (.cons (show Petersen.Adj 3 2 by decide) (.cons (show Petersen.Adj 2 1 by decide) (.cons (show Petersen.Adj 1 6 by decide) (.cons (show Petersen.Adj 6 8 by decide) (.cons (show Petersen.Adj 8 5 by decide) (.cons (show Petersen.Adj 5 0 by decide) .nil))))))))
def pC2 : Petersen.Walk 0 0 := (.cons (show Petersen.Adj 0 1 by decide) (.cons (show Petersen.Adj 1 6 by decide) (.cons (show Petersen.Adj 6 8 by decide) (.cons (show Petersen.Adj 8 3 by decide) (.cons (show Petersen.Adj 3 2 by decide) (.cons (show Petersen.Adj 2 7 by decide) (.cons (show Petersen.Adj 7 5 by decide) (.cons (show Petersen.Adj 5 0 by decide) .nil))))))))
def pC3 : Petersen.Walk 0 0 := (.cons (show Petersen.Adj 0 1 by decide) (.cons (show Petersen.Adj 1 6 by decide) (.cons (show Petersen.Adj 6 8 by decide) (.cons (show Petersen.Adj 8 5 by decide) (.cons (show Petersen.Adj 5 7 by decide) (.cons (show Petersen.Adj 7 9 by decide) (.cons (show Petersen.Adj 9 4 by decide) (.cons (show Petersen.Adj 4 0 by decide) .nil))))))))
def pC4 : Petersen.Walk 0 0 := (.cons (show Petersen.Adj 0 1 by decide) (.cons (show Petersen.Adj 1 6 by decide) (.cons (show Petersen.Adj 6 9 by decide) (.cons (show Petersen.Adj 9 4 by decide) (.cons (show Petersen.Adj 4 3 by decide) (.cons (show Petersen.Adj 3 8 by decide) (.cons (show Petersen.Adj 8 5 by decide) (.cons (show Petersen.Adj 5 0 by decide) .nil))))))))
def pC5 : Petersen.Walk 0 0 := (.cons (show Petersen.Adj 0 1 by decide) (.cons (show Petersen.Adj 1 6 by decide) (.cons (show Petersen.Adj 6 9 by decide) (.cons (show Petersen.Adj 9 7 by decide) (.cons (show Petersen.Adj 7 2 by decide) (.cons (show Petersen.Adj 2 3 by decide) (.cons (show Petersen.Adj 3 4 by decide) (.cons (show Petersen.Adj 4 0 by decide) .nil))))))))
def pC6 : Petersen.Walk 0 0 := (.cons (show Petersen.Adj 0 1 by decide) (.cons (show Petersen.Adj 1 2 by decide) (.cons (show Petersen.Adj 2 7 by decide) (.cons (show Petersen.Adj 7 9 by decide) (.cons (show Petersen.Adj 9 6 by decide) (.cons (show Petersen.Adj 6 8 by decide) (.cons (show Petersen.Adj 8 5 by decide) (.cons (show Petersen.Adj 5 0 by decide) .nil))))))))
def pC7 : Petersen.Walk 0 0 := (.cons (show Petersen.Adj 0 1 by decide) (.cons (show Petersen.Adj 1 2 by decide) (.cons (show Petersen.Adj 2 7 by decide) (.cons (show Petersen.Adj 7 5 by decide) (.cons (show Petersen.Adj 5 8 by decide) (.cons (show Petersen.Adj 8 3 by decide) (.cons (show Petersen.Adj 3 4 by decide) (.cons (show Petersen.Adj 4 0 by decide) .nil))))))))
def pC8 : Petersen.Walk 0 0 := (.cons (show Petersen.Adj 0 1 by decide) (.cons (show Petersen.Adj 1 2 by decide) (.cons (show Petersen.Adj 2 3 by decide) (.cons (show Petersen.Adj 3 8 by decide) (.cons (show Petersen.Adj 8 6 by decide) (.cons (show Petersen.Adj 6 9 by decide) (.cons (show Petersen.Adj 9 4 by decide) (.cons (show Petersen.Adj 4 0 by decide) .nil))))))))
def pC9 : Petersen.Walk 0 0 := (.cons (show Petersen.Adj 0 1 by decide) (.cons (show Petersen.Adj 1 2 by decide) (.cons (show Petersen.Adj 2 3 by decide) (.cons (show Petersen.Adj 3 4 by decide) (.cons (show Petersen.Adj 4 9 by decide) (.cons (show Petersen.Adj 9 7 by decide) (.cons (show Petersen.Adj 7 5 by decide) (.cons (show Petersen.Adj 5 0 by decide) .nil))))))))
def pC10 : Petersen.Walk 2 2 := (.cons (show Petersen.Adj 2 3 by decide) (.cons (show Petersen.Adj 3 4 by decide) (.cons (show Petersen.Adj 4 9 by decide) (.cons (show Petersen.Adj 9 6 by decide) (.cons (show Petersen.Adj 6 8 by decide) (.cons (show Petersen.Adj 8 5 by decide) (.cons (show Petersen.Adj 5 7 by decide) (.cons (show Petersen.Adj 7 2 by decide) .nil))))))))

lemma pT0_dich {Γ : Type*} [AddCommGroup Γ] (α : SkewVoltage (Fin 10) Γ) (hno : ¬HasPower (VoltageLift Petersen α)) :
    walkVoltage α pT0x = walkVoltage α pT0y ∨ walkVoltage α pT0y = walkVoltage α pT0z ∨ walkVoltage α pT0z = walkVoltage α pT0x := by
  by_contra h; push Not at h; rcases h with ⟨h1, h2, h3⟩
  obtain ⟨w, hwc, hwl⟩ := abelian_cover_theta_commutator_simple Petersen α pT0x pT0y pT0z
    (Walk.IsPath.mk' (by decide)) (Walk.IsPath.mk' (by decide)) (Walk.IsPath.mk' (by decide))
    (by decide) (by decide) (by decide)
    (by intro x; fin_cases x <;> decide) (by intro x; fin_cases x <;> decide) (by intro x; fin_cases x <;> decide) h1 h2 h3.symm
  exact hno ⟨4, (0, 0), w, by omega, hwc, by rw [hwl]; rfl⟩
lemma pT1_dich {Γ : Type*} [AddCommGroup Γ] (α : SkewVoltage (Fin 10) Γ) (hno : ¬HasPower (VoltageLift Petersen α)) :
    walkVoltage α pT1x = walkVoltage α pT1y ∨ walkVoltage α pT1y = walkVoltage α pT1z ∨ walkVoltage α pT1z = walkVoltage α pT1x := by
  by_contra h; push Not at h; rcases h with ⟨h1, h2, h3⟩
  obtain ⟨w, hwc, hwl⟩ := abelian_cover_theta_commutator_simple Petersen α pT1x pT1y pT1z
    (Walk.IsPath.mk' (by decide)) (Walk.IsPath.mk' (by decide)) (Walk.IsPath.mk' (by decide))
    (by decide) (by decide) (by decide)
    (by intro x; fin_cases x <;> decide) (by intro x; fin_cases x <;> decide) (by intro x; fin_cases x <;> decide) h1 h2 h3.symm
  exact hno ⟨4, (0, 0), w, by omega, hwc, by rw [hwl]; rfl⟩
lemma pT2_dich {Γ : Type*} [AddCommGroup Γ] (α : SkewVoltage (Fin 10) Γ) (hno : ¬HasPower (VoltageLift Petersen α)) :
    walkVoltage α pT2x = walkVoltage α pT2y ∨ walkVoltage α pT2y = walkVoltage α pT2z ∨ walkVoltage α pT2z = walkVoltage α pT2x := by
  by_contra h; push Not at h; rcases h with ⟨h1, h2, h3⟩
  obtain ⟨w, hwc, hwl⟩ := abelian_cover_theta_commutator_simple Petersen α pT2x pT2y pT2z
    (Walk.IsPath.mk' (by decide)) (Walk.IsPath.mk' (by decide)) (Walk.IsPath.mk' (by decide))
    (by decide) (by decide) (by decide)
    (by intro x; fin_cases x <;> decide) (by intro x; fin_cases x <;> decide) (by intro x; fin_cases x <;> decide) h1 h2 h3.symm
  exact hno ⟨4, (0, 0), w, by omega, hwc, by rw [hwl]; rfl⟩
lemma pT3_dich {Γ : Type*} [AddCommGroup Γ] (α : SkewVoltage (Fin 10) Γ) (hno : ¬HasPower (VoltageLift Petersen α)) :
    walkVoltage α pT3x = walkVoltage α pT3y ∨ walkVoltage α pT3y = walkVoltage α pT3z ∨ walkVoltage α pT3z = walkVoltage α pT3x := by
  by_contra h; push Not at h; rcases h with ⟨h1, h2, h3⟩
  obtain ⟨w, hwc, hwl⟩ := abelian_cover_theta_commutator_simple Petersen α pT3x pT3y pT3z
    (Walk.IsPath.mk' (by decide)) (Walk.IsPath.mk' (by decide)) (Walk.IsPath.mk' (by decide))
    (by decide) (by decide) (by decide)
    (by intro x; fin_cases x <;> decide) (by intro x; fin_cases x <;> decide) (by intro x; fin_cases x <;> decide) h1 h2 h3.symm
  exact hno ⟨4, (0, 0), w, by omega, hwc, by rw [hwl]; rfl⟩
lemma pT4_dich {Γ : Type*} [AddCommGroup Γ] (α : SkewVoltage (Fin 10) Γ) (hno : ¬HasPower (VoltageLift Petersen α)) :
    walkVoltage α pT4x = walkVoltage α pT4y ∨ walkVoltage α pT4y = walkVoltage α pT4z ∨ walkVoltage α pT4z = walkVoltage α pT4x := by
  by_contra h; push Not at h; rcases h with ⟨h1, h2, h3⟩
  obtain ⟨w, hwc, hwl⟩ := abelian_cover_theta_commutator_simple Petersen α pT4x pT4y pT4z
    (Walk.IsPath.mk' (by decide)) (Walk.IsPath.mk' (by decide)) (Walk.IsPath.mk' (by decide))
    (by decide) (by decide) (by decide)
    (by intro x; fin_cases x <;> decide) (by intro x; fin_cases x <;> decide) (by intro x; fin_cases x <;> decide) h1 h2 h3.symm
  exact hno ⟨4, (0, 0), w, by omega, hwc, by rw [hwl]; rfl⟩
lemma pT5_dich {Γ : Type*} [AddCommGroup Γ] (α : SkewVoltage (Fin 10) Γ) (hno : ¬HasPower (VoltageLift Petersen α)) :
    walkVoltage α pT5x = walkVoltage α pT5y ∨ walkVoltage α pT5y = walkVoltage α pT5z ∨ walkVoltage α pT5z = walkVoltage α pT5x := by
  by_contra h; push Not at h; rcases h with ⟨h1, h2, h3⟩
  obtain ⟨w, hwc, hwl⟩ := abelian_cover_theta_commutator_simple Petersen α pT5x pT5y pT5z
    (Walk.IsPath.mk' (by decide)) (Walk.IsPath.mk' (by decide)) (Walk.IsPath.mk' (by decide))
    (by decide) (by decide) (by decide)
    (by intro x; fin_cases x <;> decide) (by intro x; fin_cases x <;> decide) (by intro x; fin_cases x <;> decide) h1 h2 h3.symm
  exact hno ⟨4, (0, 0), w, by omega, hwc, by rw [hwl]; rfl⟩

theorem petersen_all_abelian_covers_hasPower {Γ : Type*} [AddCommGroup Γ] (α : SkewVoltage (Fin 10) Γ) : HasPower (VoltageLift Petersen α) := by
  by_contra hno
  have r0 : α.val 1 0 = -α.val 0 1 := α.skew 0 1
  have r1 : α.val 2 1 = -α.val 1 2 := α.skew 1 2
  have r2 : α.val 3 2 = -α.val 2 3 := α.skew 2 3
  have r3 : α.val 4 3 = -α.val 3 4 := α.skew 3 4
  have r4 : α.val 0 4 = -α.val 4 0 := α.skew 4 0
  have r5 : α.val 7 5 = -α.val 5 7 := α.skew 5 7
  have r6 : α.val 9 7 = -α.val 7 9 := α.skew 7 9
  have r7 : α.val 6 9 = -α.val 9 6 := α.skew 9 6
  have r8 : α.val 8 6 = -α.val 6 8 := α.skew 6 8
  have r9 : α.val 5 8 = -α.val 8 5 := α.skew 8 5
  have r10 : α.val 5 0 = -α.val 0 5 := α.skew 0 5
  have r11 : α.val 6 1 = -α.val 1 6 := α.skew 1 6
  have r12 : α.val 7 2 = -α.val 2 7 := α.skew 2 7
  have r13 : α.val 8 3 = -α.val 3 8 := α.skew 3 8
  have r14 : α.val 9 4 = -α.val 4 9 := α.skew 4 9
  rcases pT0_dich α hno with h0 | h0 | h0
  ·
    rcases pT2_dich α hno with h1 | h1 | h1
    ·
      rcases pT3_dich α hno with h2 | h2 | h2
      ·
        have hc : walkVoltage α pC0 = 0 := by
          have h1' := sub_eq_zero.mpr h1; have h2' := sub_eq_zero.mpr h2
          have heq : walkVoltage α pC0 = -(walkVoltage α pT2x - walkVoltage α pT2y) + -(walkVoltage α pT3x - walkVoltage α pT3y) := by simp only [walkVoltage,pC0,pT2x,pT2y,pT3x,pT3y,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14]; abel
          rw [heq,h1',h2']; abel
        obtain ⟨w, hwc, hwl⟩ := zero_voltage_cycle_lifts Petersen α pC0 (isCycle_of_length_ge_three_nodup (by decide) (by decide)) hc
        exact hno ⟨3, (0, 0), w, by omega, hwc, by rw [hwl]; rfl⟩
      ·
        have hc : walkVoltage α pC5 = 0 := by
          have h0' := sub_eq_zero.mpr h0; have h1' := sub_eq_zero.mpr h1; have h2' := sub_eq_zero.mpr h2
          have heq : walkVoltage α pC5 = (walkVoltage α pT0x - walkVoltage α pT0y) + (walkVoltage α pT2x - walkVoltage α pT2y) + -(walkVoltage α pT3y - walkVoltage α pT3z) := by simp only [walkVoltage,pC5,pT0x,pT0y,pT2x,pT2y,pT3y,pT3z,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14]; abel
          rw [heq,h0',h1',h2']; abel
        obtain ⟨w, hwc, hwl⟩ := zero_voltage_cycle_lifts Petersen α pC5 (isCycle_of_length_ge_three_nodup (by decide) (by decide)) hc
        exact hno ⟨3, (0, 0), w, by omega, hwc, by rw [hwl]; rfl⟩
      ·
        have hc : walkVoltage α pC9 = 0 := by
          have h0' := sub_eq_zero.mpr h0; have h2' := sub_eq_zero.mpr h2
          have heq : walkVoltage α pC9 = (walkVoltage α pT0x - walkVoltage α pT0y) + (walkVoltage α pT3z - walkVoltage α pT3x) := by simp only [walkVoltage,pC9,pT0x,pT0y,pT3x,pT3z,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14]; abel
          rw [heq,h0',h2']; abel
        obtain ⟨w, hwc, hwl⟩ := zero_voltage_cycle_lifts Petersen α pC9 (isCycle_of_length_ge_three_nodup (by decide) (by decide)) hc
        exact hno ⟨3, (0, 0), w, by omega, hwc, by rw [hwl]; rfl⟩
    ·
      rcases pT3_dich α hno with h2 | h2 | h2
      ·
        have hc : walkVoltage α pC10 = 0 := by
          have h0' := sub_eq_zero.mpr h0; have h1' := sub_eq_zero.mpr h1; have h2' := sub_eq_zero.mpr h2
          have heq : walkVoltage α pC10 = (walkVoltage α pT0x - walkVoltage α pT0y) + (walkVoltage α pT2y - walkVoltage α pT2z) + (walkVoltage α pT3x - walkVoltage α pT3y) := by simp only [walkVoltage,pC10,pT0x,pT0y,pT2y,pT2z,pT3x,pT3y,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14]; abel
          rw [heq,h0',h1',h2']; abel
        obtain ⟨w, hwc, hwl⟩ := zero_voltage_cycle_lifts Petersen α pC10 (isCycle_of_length_ge_three_nodup (by decide) (by decide)) hc
        exact hno ⟨3, (2, 0), w, by omega, hwc, by rw [hwl]; rfl⟩
      ·
        have hc : walkVoltage α pC6 = 0 := by
          have h1' := sub_eq_zero.mpr h1; have h2' := sub_eq_zero.mpr h2
          have heq : walkVoltage α pC6 = (walkVoltage α pT2y - walkVoltage α pT2z) + (walkVoltage α pT3y - walkVoltage α pT3z) := by simp only [walkVoltage,pC6,pT2y,pT2z,pT3y,pT3z,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14]; abel
          rw [heq,h1',h2']; abel
        obtain ⟨w, hwc, hwl⟩ := zero_voltage_cycle_lifts Petersen α pC6 (isCycle_of_length_ge_three_nodup (by decide) (by decide)) hc
        exact hno ⟨3, (0, 0), w, by omega, hwc, by rw [hwl]; rfl⟩
      ·
        have hc : walkVoltage α pC9 = 0 := by
          have h0' := sub_eq_zero.mpr h0; have h2' := sub_eq_zero.mpr h2
          have heq : walkVoltage α pC9 = (walkVoltage α pT0x - walkVoltage α pT0y) + (walkVoltage α pT3z - walkVoltage α pT3x) := by simp only [walkVoltage,pC9,pT0x,pT0y,pT3x,pT3z,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14]; abel
          rw [heq,h0',h2']; abel
        obtain ⟨w, hwc, hwl⟩ := zero_voltage_cycle_lifts Petersen α pC9 (isCycle_of_length_ge_three_nodup (by decide) (by decide)) hc
        exact hno ⟨3, (0, 0), w, by omega, hwc, by rw [hwl]; rfl⟩
    ·
      have hc : walkVoltage α pC1 = 0 := by
        have h0' := sub_eq_zero.mpr h0; have h1' := sub_eq_zero.mpr h1
        have heq : walkVoltage α pC1 = -(walkVoltage α pT0x - walkVoltage α pT0y) + -(walkVoltage α pT2z - walkVoltage α pT2x) := by simp only [walkVoltage,pC1,pT0x,pT0y,pT2x,pT2z,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14]; abel
        rw [heq,h0',h1']; abel
      obtain ⟨w, hwc, hwl⟩ := zero_voltage_cycle_lifts Petersen α pC1 (isCycle_of_length_ge_three_nodup (by decide) (by decide)) hc
      exact hno ⟨3, (0, 0), w, by omega, hwc, by rw [hwl]; rfl⟩
  ·
    rcases pT2_dich α hno with h1 | h1 | h1
    ·
      rcases pT4_dich α hno with h2 | h2 | h2
      ·
        have hc : walkVoltage α pC10 = 0 := by
          have h0' := sub_eq_zero.mpr h0; have h1' := sub_eq_zero.mpr h1; have h2' := sub_eq_zero.mpr h2
          have heq : walkVoltage α pC10 = -(walkVoltage α pT0y - walkVoltage α pT0z) + -(walkVoltage α pT2x - walkVoltage α pT2y) + -(walkVoltage α pT4x - walkVoltage α pT4y) := by simp only [walkVoltage,pC10,pT0y,pT0z,pT2x,pT2y,pT4x,pT4y,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14]; abel
          rw [heq,h0',h1',h2']; abel
        obtain ⟨w, hwc, hwl⟩ := zero_voltage_cycle_lifts Petersen α pC10 (isCycle_of_length_ge_three_nodup (by decide) (by decide)) hc
        exact hno ⟨3, (2, 0), w, by omega, hwc, by rw [hwl]; rfl⟩
      ·
        have hc : walkVoltage α pC2 = 0 := by
          have h0' := sub_eq_zero.mpr h0; have h2' := sub_eq_zero.mpr h2
          have heq : walkVoltage α pC2 = (walkVoltage α pT0y - walkVoltage α pT0z) + (walkVoltage α pT4y - walkVoltage α pT4z) := by simp only [walkVoltage,pC2,pT0y,pT0z,pT4y,pT4z,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14]; abel
          rw [heq,h0',h2']; abel
        obtain ⟨w, hwc, hwl⟩ := zero_voltage_cycle_lifts Petersen α pC2 (isCycle_of_length_ge_three_nodup (by decide) (by decide)) hc
        exact hno ⟨3, (0, 0), w, by omega, hwc, by rw [hwl]; rfl⟩
      ·
        have hc : walkVoltage α pC4 = 0 := by
          have h1' := sub_eq_zero.mpr h1; have h2' := sub_eq_zero.mpr h2
          have heq : walkVoltage α pC4 = (walkVoltage α pT2x - walkVoltage α pT2y) + (walkVoltage α pT4z - walkVoltage α pT4x) := by simp only [walkVoltage,pC4,pT2x,pT2y,pT4x,pT4z,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14]; abel
          rw [heq,h1',h2']; abel
        obtain ⟨w, hwc, hwl⟩ := zero_voltage_cycle_lifts Petersen α pC4 (isCycle_of_length_ge_three_nodup (by decide) (by decide)) hc
        exact hno ⟨3, (0, 0), w, by omega, hwc, by rw [hwl]; rfl⟩
    ·
      have hc : walkVoltage α pC10 = 0 := by
        have h0' := sub_eq_zero.mpr h0; have h1' := sub_eq_zero.mpr h1
        have heq : walkVoltage α pC10 = -(walkVoltage α pT0y - walkVoltage α pT0z) + (walkVoltage α pT2y - walkVoltage α pT2z) := by simp only [walkVoltage,pC10,pT0y,pT0z,pT2y,pT2z,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14]; abel
        rw [heq,h0',h1']; abel
      obtain ⟨w, hwc, hwl⟩ := zero_voltage_cycle_lifts Petersen α pC10 (isCycle_of_length_ge_three_nodup (by decide) (by decide)) hc
      exact hno ⟨3, (2, 0), w, by omega, hwc, by rw [hwl]; rfl⟩
    ·
      rcases pT5_dich α hno with h2 | h2 | h2
      ·
        have hc : walkVoltage α pC10 = 0 := by
          have h0' := sub_eq_zero.mpr h0; have h1' := sub_eq_zero.mpr h1; have h2' := sub_eq_zero.mpr h2
          have heq : walkVoltage α pC10 = -(walkVoltage α pT0y - walkVoltage α pT0z) + -(walkVoltage α pT2z - walkVoltage α pT2x) + (walkVoltage α pT5x - walkVoltage α pT5y) := by simp only [walkVoltage,pC10,pT0y,pT0z,pT2x,pT2z,pT5x,pT5y,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14]; abel
          rw [heq,h0',h1',h2']; abel
        obtain ⟨w, hwc, hwl⟩ := zero_voltage_cycle_lifts Petersen α pC10 (isCycle_of_length_ge_three_nodup (by decide) (by decide)) hc
        exact hno ⟨3, (2, 0), w, by omega, hwc, by rw [hwl]; rfl⟩
      ·
        have hc : walkVoltage α pC5 = 0 := by
          have h0' := sub_eq_zero.mpr h0; have h2' := sub_eq_zero.mpr h2
          have heq : walkVoltage α pC5 = -(walkVoltage α pT0y - walkVoltage α pT0z) + (walkVoltage α pT5y - walkVoltage α pT5z) := by simp only [walkVoltage,pC5,pT0y,pT0z,pT5y,pT5z,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14]; abel
          rw [heq,h0',h2']; abel
        obtain ⟨w, hwc, hwl⟩ := zero_voltage_cycle_lifts Petersen α pC5 (isCycle_of_length_ge_three_nodup (by decide) (by decide)) hc
        exact hno ⟨3, (0, 0), w, by omega, hwc, by rw [hwl]; rfl⟩
      ·
        have hc : walkVoltage α pC3 = 0 := by
          have h1' := sub_eq_zero.mpr h1; have h2' := sub_eq_zero.mpr h2
          have heq : walkVoltage α pC3 = -(walkVoltage α pT2z - walkVoltage α pT2x) + (walkVoltage α pT5z - walkVoltage α pT5x) := by simp only [walkVoltage,pC3,pT2x,pT2z,pT5x,pT5z,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14]; abel
          rw [heq,h1',h2']; abel
        obtain ⟨w, hwc, hwl⟩ := zero_voltage_cycle_lifts Petersen α pC3 (isCycle_of_length_ge_three_nodup (by decide) (by decide)) hc
        exact hno ⟨3, (0, 0), w, by omega, hwc, by rw [hwl]; rfl⟩
  ·
    rcases pT1_dich α hno with h1 | h1 | h1
    ·
      rcases pT2_dich α hno with h2 | h2 | h2
      ·
        have hc : walkVoltage α pC0 = 0 := by
          have h0' := sub_eq_zero.mpr h0; have h2' := sub_eq_zero.mpr h2
          have heq : walkVoltage α pC0 = -(walkVoltage α pT0z - walkVoltage α pT0x) + -(walkVoltage α pT2x - walkVoltage α pT2y) := by simp only [walkVoltage,pC0,pT0x,pT0z,pT2x,pT2y,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14]; abel
          rw [heq,h0',h2']; abel
        obtain ⟨w, hwc, hwl⟩ := zero_voltage_cycle_lifts Petersen α pC0 (isCycle_of_length_ge_three_nodup (by decide) (by decide)) hc
        exact hno ⟨3, (0, 0), w, by omega, hwc, by rw [hwl]; rfl⟩
      ·
        have hc : walkVoltage α pC10 = 0 := by
          have h0' := sub_eq_zero.mpr h0; have h1' := sub_eq_zero.mpr h1; have h2' := sub_eq_zero.mpr h2
          have heq : walkVoltage α pC10 = (walkVoltage α pT0z - walkVoltage α pT0x) + -(walkVoltage α pT1x - walkVoltage α pT1y) + (walkVoltage α pT2y - walkVoltage α pT2z) := by simp only [walkVoltage,pC10,pT0x,pT0z,pT1x,pT1y,pT2y,pT2z,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14]; abel
          rw [heq,h0',h1',h2']; abel
        obtain ⟨w, hwc, hwl⟩ := zero_voltage_cycle_lifts Petersen α pC10 (isCycle_of_length_ge_three_nodup (by decide) (by decide)) hc
        exact hno ⟨3, (2, 0), w, by omega, hwc, by rw [hwl]; rfl⟩
      ·
        have hc : walkVoltage α pC1 = 0 := by
          have h1' := sub_eq_zero.mpr h1; have h2' := sub_eq_zero.mpr h2
          have heq : walkVoltage α pC1 = (walkVoltage α pT1x - walkVoltage α pT1y) + -(walkVoltage α pT2z - walkVoltage α pT2x) := by simp only [walkVoltage,pC1,pT1x,pT1y,pT2x,pT2z,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14]; abel
          rw [heq,h1',h2']; abel
        obtain ⟨w, hwc, hwl⟩ := zero_voltage_cycle_lifts Petersen α pC1 (isCycle_of_length_ge_three_nodup (by decide) (by decide)) hc
        exact hno ⟨3, (0, 0), w, by omega, hwc, by rw [hwl]; rfl⟩
    ·
      rcases pT2_dich α hno with h2 | h2 | h2
      ·
        have hc : walkVoltage α pC0 = 0 := by
          have h0' := sub_eq_zero.mpr h0; have h2' := sub_eq_zero.mpr h2
          have heq : walkVoltage α pC0 = -(walkVoltage α pT0z - walkVoltage α pT0x) + -(walkVoltage α pT2x - walkVoltage α pT2y) := by simp only [walkVoltage,pC0,pT0x,pT0z,pT2x,pT2y,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14]; abel
          rw [heq,h0',h2']; abel
        obtain ⟨w, hwc, hwl⟩ := zero_voltage_cycle_lifts Petersen α pC0 (isCycle_of_length_ge_three_nodup (by decide) (by decide)) hc
        exact hno ⟨3, (0, 0), w, by omega, hwc, by rw [hwl]; rfl⟩
      ·
        have hc : walkVoltage α pC8 = 0 := by
          have h1' := sub_eq_zero.mpr h1; have h2' := sub_eq_zero.mpr h2
          have heq : walkVoltage α pC8 = (walkVoltage α pT1y - walkVoltage α pT1z) + -(walkVoltage α pT2y - walkVoltage α pT2z) := by simp only [walkVoltage,pC8,pT1y,pT1z,pT2y,pT2z,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14]; abel
          rw [heq,h1',h2']; abel
        obtain ⟨w, hwc, hwl⟩ := zero_voltage_cycle_lifts Petersen α pC8 (isCycle_of_length_ge_three_nodup (by decide) (by decide)) hc
        exact hno ⟨3, (0, 0), w, by omega, hwc, by rw [hwl]; rfl⟩
      ·
        have hc : walkVoltage α pC2 = 0 := by
          have h0' := sub_eq_zero.mpr h0; have h1' := sub_eq_zero.mpr h1; have h2' := sub_eq_zero.mpr h2
          have heq : walkVoltage α pC2 = -(walkVoltage α pT0z - walkVoltage α pT0x) + -(walkVoltage α pT1y - walkVoltage α pT1z) + -(walkVoltage α pT2z - walkVoltage α pT2x) := by simp only [walkVoltage,pC2,pT0x,pT0z,pT1y,pT1z,pT2x,pT2z,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14]; abel
          rw [heq,h0',h1',h2']; abel
        obtain ⟨w, hwc, hwl⟩ := zero_voltage_cycle_lifts Petersen α pC2 (isCycle_of_length_ge_three_nodup (by decide) (by decide)) hc
        exact hno ⟨3, (0, 0), w, by omega, hwc, by rw [hwl]; rfl⟩
    ·
      have hc : walkVoltage α pC7 = 0 := by
        have h0' := sub_eq_zero.mpr h0; have h1' := sub_eq_zero.mpr h1
        have heq : walkVoltage α pC7 = -(walkVoltage α pT0z - walkVoltage α pT0x) + (walkVoltage α pT1z - walkVoltage α pT1x) := by simp only [walkVoltage,pC7,pT0x,pT0z,pT1x,pT1z,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14]; abel
        rw [heq,h0',h1']; abel
      obtain ⟨w, hwc, hwl⟩ := zero_voltage_cycle_lifts Petersen α pC7 (isCycle_of_length_ge_three_nodup (by decide) (by decide)) hc
      exact hno ⟨3, (0, 0), w, by omega, hwc, by rw [hwl]; rfl⟩

end E64Wave8Agent5
