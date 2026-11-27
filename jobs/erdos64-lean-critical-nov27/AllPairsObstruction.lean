import Shadow

/-!
A finite, exact counterexample to the proposed all-pairs dyadic-path forcing
lemma. This graph is triangle-free and subcubic, but has six degree-two
vertices: it is NOT an Erdős–Gyárfás counterexample and is NOT Near.
Every verification below is kernel-reduced `decide`; no native decision
procedure, unproved axiom, or exhaustive-search assumption is used.
-/
namespace E64AllPairsObstruction
open SimpleGraph Erdos64Closure

set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev V := Fin 12

def edgeList : List (V × V) :=
  [(0, 1), (0, 4), (0, 8), (1, 11), (2, 6), (2, 9), (3, 5), (3, 6), (4, 6), (4, 10), (5, 8), (7, 8), (7, 9), (9, 11), (10, 11)]

def Adj (u v : V) : Prop := (u,v) ∈ edgeList ∨ (v,u) ∈ edgeList
instance adjDecidable : DecidableRel Adj := fun _ _ => inferInstance

def G : SimpleGraph V where
  Adj := Adj
  symm := by intro u v h; exact h.elim Or.inr Or.inl
  loopless := ⟨by intro u; fin_cases u <;> decide⟩

instance graphAdjDecidable : DecidableRel G.Adj := adjDecidable

def DyadicPath {W : Type*} (H : SimpleGraph W) (u v : W) : Prop :=
  ∃ (k : ℕ) (p : H.Walk u v), 2 ≤ k ∧ p.IsPath ∧ p.length = 2^k

theorem DyadicPath.symm {W : Type*} {H : SimpleGraph W} {u v : W}
    (h : DyadicPath H u v) : DyadicPath H v u := by
  obtain ⟨k,p,hk,hp,hlen⟩ := h
  exact ⟨k,p.reverse,hk,p.isPath_reverse_iff.mpr hp,by simpa using hlen⟩

theorem path_0_1 : DyadicPath G 0 1 := by
  refine ⟨3, (Walk.cons (show G.Adj 0 8 from by decide) (Walk.cons (show G.Adj 8 5 from by decide) (Walk.cons (show G.Adj 5 3 from by decide) (Walk.cons (show G.Adj 3 6 from by decide) (Walk.cons (show G.Adj 6 2 from by decide) (Walk.cons (show G.Adj 2 9 from by decide) (Walk.cons (show G.Adj 9 11 from by decide) (Walk.cons (show G.Adj 11 1 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_0_2 : DyadicPath G 0 2 := by
  refine ⟨2, (Walk.cons (show G.Adj 0 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 9 from by decide) (Walk.cons (show G.Adj 9 2 from by decide) Walk.nil)))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_0_3 : DyadicPath G 0 3 := by
  refine ⟨3, (Walk.cons (show G.Adj 0 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 9 from by decide) (Walk.cons (show G.Adj 9 11 from by decide) (Walk.cons (show G.Adj 11 10 from by decide) (Walk.cons (show G.Adj 10 4 from by decide) (Walk.cons (show G.Adj 4 6 from by decide) (Walk.cons (show G.Adj 6 3 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_0_4 : DyadicPath G 0 4 := by
  refine ⟨2, (Walk.cons (show G.Adj 0 1 from by decide) (Walk.cons (show G.Adj 1 11 from by decide) (Walk.cons (show G.Adj 11 10 from by decide) (Walk.cons (show G.Adj 10 4 from by decide) Walk.nil)))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_0_5 : DyadicPath G 0 5 := by
  refine ⟨3, (Walk.cons (show G.Adj 0 4 from by decide) (Walk.cons (show G.Adj 4 10 from by decide) (Walk.cons (show G.Adj 10 11 from by decide) (Walk.cons (show G.Adj 11 9 from by decide) (Walk.cons (show G.Adj 9 2 from by decide) (Walk.cons (show G.Adj 2 6 from by decide) (Walk.cons (show G.Adj 6 3 from by decide) (Walk.cons (show G.Adj 3 5 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_0_6 : DyadicPath G 0 6 := by
  refine ⟨2, (Walk.cons (show G.Adj 0 8 from by decide) (Walk.cons (show G.Adj 8 5 from by decide) (Walk.cons (show G.Adj 5 3 from by decide) (Walk.cons (show G.Adj 3 6 from by decide) Walk.nil)))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_0_7 : DyadicPath G 0 7 := by
  refine ⟨3, (Walk.cons (show G.Adj 0 1 from by decide) (Walk.cons (show G.Adj 1 11 from by decide) (Walk.cons (show G.Adj 11 10 from by decide) (Walk.cons (show G.Adj 10 4 from by decide) (Walk.cons (show G.Adj 4 6 from by decide) (Walk.cons (show G.Adj 6 2 from by decide) (Walk.cons (show G.Adj 2 9 from by decide) (Walk.cons (show G.Adj 9 7 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_0_8 : DyadicPath G 0 8 := by
  refine ⟨3, (Walk.cons (show G.Adj 0 1 from by decide) (Walk.cons (show G.Adj 1 11 from by decide) (Walk.cons (show G.Adj 11 10 from by decide) (Walk.cons (show G.Adj 10 4 from by decide) (Walk.cons (show G.Adj 4 6 from by decide) (Walk.cons (show G.Adj 6 3 from by decide) (Walk.cons (show G.Adj 3 5 from by decide) (Walk.cons (show G.Adj 5 8 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_0_9 : DyadicPath G 0 9 := by
  refine ⟨3, (Walk.cons (show G.Adj 0 8 from by decide) (Walk.cons (show G.Adj 8 5 from by decide) (Walk.cons (show G.Adj 5 3 from by decide) (Walk.cons (show G.Adj 3 6 from by decide) (Walk.cons (show G.Adj 6 4 from by decide) (Walk.cons (show G.Adj 4 10 from by decide) (Walk.cons (show G.Adj 10 11 from by decide) (Walk.cons (show G.Adj 11 9 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_0_10 : DyadicPath G 0 10 := by
  refine ⟨3, (Walk.cons (show G.Adj 0 8 from by decide) (Walk.cons (show G.Adj 8 5 from by decide) (Walk.cons (show G.Adj 5 3 from by decide) (Walk.cons (show G.Adj 3 6 from by decide) (Walk.cons (show G.Adj 6 2 from by decide) (Walk.cons (show G.Adj 2 9 from by decide) (Walk.cons (show G.Adj 9 11 from by decide) (Walk.cons (show G.Adj 11 10 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_0_11 : DyadicPath G 0 11 := by
  refine ⟨3, (Walk.cons (show G.Adj 0 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 9 from by decide) (Walk.cons (show G.Adj 9 2 from by decide) (Walk.cons (show G.Adj 2 6 from by decide) (Walk.cons (show G.Adj 6 4 from by decide) (Walk.cons (show G.Adj 4 10 from by decide) (Walk.cons (show G.Adj 10 11 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_1_2 : DyadicPath G 1 2 := by
  refine ⟨2, (Walk.cons (show G.Adj 1 0 from by decide) (Walk.cons (show G.Adj 0 4 from by decide) (Walk.cons (show G.Adj 4 6 from by decide) (Walk.cons (show G.Adj 6 2 from by decide) Walk.nil)))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_1_3 : DyadicPath G 1 3 := by
  refine ⟨2, (Walk.cons (show G.Adj 1 0 from by decide) (Walk.cons (show G.Adj 0 8 from by decide) (Walk.cons (show G.Adj 8 5 from by decide) (Walk.cons (show G.Adj 5 3 from by decide) Walk.nil)))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_1_4 : DyadicPath G 1 4 := by
  refine ⟨3, (Walk.cons (show G.Adj 1 11 from by decide) (Walk.cons (show G.Adj 11 9 from by decide) (Walk.cons (show G.Adj 9 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 5 from by decide) (Walk.cons (show G.Adj 5 3 from by decide) (Walk.cons (show G.Adj 3 6 from by decide) (Walk.cons (show G.Adj 6 4 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_1_5 : DyadicPath G 1 5 := by
  refine ⟨3, (Walk.cons (show G.Adj 1 0 from by decide) (Walk.cons (show G.Adj 0 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 9 from by decide) (Walk.cons (show G.Adj 9 2 from by decide) (Walk.cons (show G.Adj 2 6 from by decide) (Walk.cons (show G.Adj 6 3 from by decide) (Walk.cons (show G.Adj 3 5 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_1_6 : DyadicPath G 1 6 := by
  refine ⟨3, (Walk.cons (show G.Adj 1 0 from by decide) (Walk.cons (show G.Adj 0 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 9 from by decide) (Walk.cons (show G.Adj 9 11 from by decide) (Walk.cons (show G.Adj 11 10 from by decide) (Walk.cons (show G.Adj 10 4 from by decide) (Walk.cons (show G.Adj 4 6 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_1_7 : DyadicPath G 1 7 := by
  refine ⟨3, (Walk.cons (show G.Adj 1 0 from by decide) (Walk.cons (show G.Adj 0 8 from by decide) (Walk.cons (show G.Adj 8 5 from by decide) (Walk.cons (show G.Adj 5 3 from by decide) (Walk.cons (show G.Adj 3 6 from by decide) (Walk.cons (show G.Adj 6 2 from by decide) (Walk.cons (show G.Adj 2 9 from by decide) (Walk.cons (show G.Adj 9 7 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_1_8 : DyadicPath G 1 8 := by
  refine ⟨3, (Walk.cons (show G.Adj 1 11 from by decide) (Walk.cons (show G.Adj 11 10 from by decide) (Walk.cons (show G.Adj 10 4 from by decide) (Walk.cons (show G.Adj 4 6 from by decide) (Walk.cons (show G.Adj 6 2 from by decide) (Walk.cons (show G.Adj 2 9 from by decide) (Walk.cons (show G.Adj 9 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_1_9 : DyadicPath G 1 9 := by
  refine ⟨2, (Walk.cons (show G.Adj 1 0 from by decide) (Walk.cons (show G.Adj 0 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 9 from by decide) Walk.nil)))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_1_10 : DyadicPath G 1 10 := by
  refine ⟨3, (Walk.cons (show G.Adj 1 0 from by decide) (Walk.cons (show G.Adj 0 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 9 from by decide) (Walk.cons (show G.Adj 9 2 from by decide) (Walk.cons (show G.Adj 2 6 from by decide) (Walk.cons (show G.Adj 6 4 from by decide) (Walk.cons (show G.Adj 4 10 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_1_11 : DyadicPath G 1 11 := by
  refine ⟨3, (Walk.cons (show G.Adj 1 0 from by decide) (Walk.cons (show G.Adj 0 8 from by decide) (Walk.cons (show G.Adj 8 5 from by decide) (Walk.cons (show G.Adj 5 3 from by decide) (Walk.cons (show G.Adj 3 6 from by decide) (Walk.cons (show G.Adj 6 2 from by decide) (Walk.cons (show G.Adj 2 9 from by decide) (Walk.cons (show G.Adj 9 11 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_2_3 : DyadicPath G 2 3 := by
  refine ⟨3, (Walk.cons (show G.Adj 2 9 from by decide) (Walk.cons (show G.Adj 9 11 from by decide) (Walk.cons (show G.Adj 11 10 from by decide) (Walk.cons (show G.Adj 10 4 from by decide) (Walk.cons (show G.Adj 4 0 from by decide) (Walk.cons (show G.Adj 0 8 from by decide) (Walk.cons (show G.Adj 8 5 from by decide) (Walk.cons (show G.Adj 5 3 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_2_4 : DyadicPath G 2 4 := by
  refine ⟨2, (Walk.cons (show G.Adj 2 9 from by decide) (Walk.cons (show G.Adj 9 11 from by decide) (Walk.cons (show G.Adj 11 10 from by decide) (Walk.cons (show G.Adj 10 4 from by decide) Walk.nil)))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_2_5 : DyadicPath G 2 5 := by
  refine ⟨3, (Walk.cons (show G.Adj 2 9 from by decide) (Walk.cons (show G.Adj 9 11 from by decide) (Walk.cons (show G.Adj 11 1 from by decide) (Walk.cons (show G.Adj 1 0 from by decide) (Walk.cons (show G.Adj 0 4 from by decide) (Walk.cons (show G.Adj 4 6 from by decide) (Walk.cons (show G.Adj 6 3 from by decide) (Walk.cons (show G.Adj 3 5 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_2_6 : DyadicPath G 2 6 := by
  refine ⟨3, (Walk.cons (show G.Adj 2 9 from by decide) (Walk.cons (show G.Adj 9 11 from by decide) (Walk.cons (show G.Adj 11 1 from by decide) (Walk.cons (show G.Adj 1 0 from by decide) (Walk.cons (show G.Adj 0 8 from by decide) (Walk.cons (show G.Adj 8 5 from by decide) (Walk.cons (show G.Adj 5 3 from by decide) (Walk.cons (show G.Adj 3 6 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_2_7 : DyadicPath G 2 7 := by
  refine ⟨3, (Walk.cons (show G.Adj 2 6 from by decide) (Walk.cons (show G.Adj 6 4 from by decide) (Walk.cons (show G.Adj 4 10 from by decide) (Walk.cons (show G.Adj 10 11 from by decide) (Walk.cons (show G.Adj 11 1 from by decide) (Walk.cons (show G.Adj 1 0 from by decide) (Walk.cons (show G.Adj 0 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_2_8 : DyadicPath G 2 8 := by
  refine ⟨3, (Walk.cons (show G.Adj 2 9 from by decide) (Walk.cons (show G.Adj 9 11 from by decide) (Walk.cons (show G.Adj 11 10 from by decide) (Walk.cons (show G.Adj 10 4 from by decide) (Walk.cons (show G.Adj 4 6 from by decide) (Walk.cons (show G.Adj 6 3 from by decide) (Walk.cons (show G.Adj 3 5 from by decide) (Walk.cons (show G.Adj 5 8 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_2_9 : DyadicPath G 2 9 := by
  refine ⟨3, (Walk.cons (show G.Adj 2 6 from by decide) (Walk.cons (show G.Adj 6 3 from by decide) (Walk.cons (show G.Adj 3 5 from by decide) (Walk.cons (show G.Adj 5 8 from by decide) (Walk.cons (show G.Adj 8 0 from by decide) (Walk.cons (show G.Adj 0 1 from by decide) (Walk.cons (show G.Adj 1 11 from by decide) (Walk.cons (show G.Adj 11 9 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_2_10 : DyadicPath G 2 10 := by
  refine ⟨3, (Walk.cons (show G.Adj 2 9 from by decide) (Walk.cons (show G.Adj 9 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 5 from by decide) (Walk.cons (show G.Adj 5 3 from by decide) (Walk.cons (show G.Adj 3 6 from by decide) (Walk.cons (show G.Adj 6 4 from by decide) (Walk.cons (show G.Adj 4 10 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_2_11 : DyadicPath G 2 11 := by
  refine ⟨3, (Walk.cons (show G.Adj 2 6 from by decide) (Walk.cons (show G.Adj 6 3 from by decide) (Walk.cons (show G.Adj 3 5 from by decide) (Walk.cons (show G.Adj 5 8 from by decide) (Walk.cons (show G.Adj 8 0 from by decide) (Walk.cons (show G.Adj 0 4 from by decide) (Walk.cons (show G.Adj 4 10 from by decide) (Walk.cons (show G.Adj 10 11 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_3_4 : DyadicPath G 3 4 := by
  refine ⟨2, (Walk.cons (show G.Adj 3 5 from by decide) (Walk.cons (show G.Adj 5 8 from by decide) (Walk.cons (show G.Adj 8 0 from by decide) (Walk.cons (show G.Adj 0 4 from by decide) Walk.nil)))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_3_5 : DyadicPath G 3 5 := by
  refine ⟨3, (Walk.cons (show G.Adj 3 6 from by decide) (Walk.cons (show G.Adj 6 2 from by decide) (Walk.cons (show G.Adj 2 9 from by decide) (Walk.cons (show G.Adj 9 11 from by decide) (Walk.cons (show G.Adj 11 1 from by decide) (Walk.cons (show G.Adj 1 0 from by decide) (Walk.cons (show G.Adj 0 8 from by decide) (Walk.cons (show G.Adj 8 5 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_3_6 : DyadicPath G 3 6 := by
  refine ⟨3, (Walk.cons (show G.Adj 3 5 from by decide) (Walk.cons (show G.Adj 5 8 from by decide) (Walk.cons (show G.Adj 8 0 from by decide) (Walk.cons (show G.Adj 0 1 from by decide) (Walk.cons (show G.Adj 1 11 from by decide) (Walk.cons (show G.Adj 11 10 from by decide) (Walk.cons (show G.Adj 10 4 from by decide) (Walk.cons (show G.Adj 4 6 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_3_7 : DyadicPath G 3 7 := by
  refine ⟨3, (Walk.cons (show G.Adj 3 5 from by decide) (Walk.cons (show G.Adj 5 8 from by decide) (Walk.cons (show G.Adj 8 0 from by decide) (Walk.cons (show G.Adj 0 4 from by decide) (Walk.cons (show G.Adj 4 10 from by decide) (Walk.cons (show G.Adj 10 11 from by decide) (Walk.cons (show G.Adj 11 9 from by decide) (Walk.cons (show G.Adj 9 7 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_3_8 : DyadicPath G 3 8 := by
  refine ⟨3, (Walk.cons (show G.Adj 3 6 from by decide) (Walk.cons (show G.Adj 6 2 from by decide) (Walk.cons (show G.Adj 2 9 from by decide) (Walk.cons (show G.Adj 9 11 from by decide) (Walk.cons (show G.Adj 11 10 from by decide) (Walk.cons (show G.Adj 10 4 from by decide) (Walk.cons (show G.Adj 4 0 from by decide) (Walk.cons (show G.Adj 0 8 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_3_9 : DyadicPath G 3 9 := by
  refine ⟨2, (Walk.cons (show G.Adj 3 5 from by decide) (Walk.cons (show G.Adj 5 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 9 from by decide) Walk.nil)))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_3_10 : DyadicPath G 3 10 := by
  refine ⟨3, (Walk.cons (show G.Adj 3 5 from by decide) (Walk.cons (show G.Adj 5 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 9 from by decide) (Walk.cons (show G.Adj 9 2 from by decide) (Walk.cons (show G.Adj 2 6 from by decide) (Walk.cons (show G.Adj 6 4 from by decide) (Walk.cons (show G.Adj 4 10 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_3_11 : DyadicPath G 3 11 := by
  refine ⟨3, (Walk.cons (show G.Adj 3 5 from by decide) (Walk.cons (show G.Adj 5 8 from by decide) (Walk.cons (show G.Adj 8 0 from by decide) (Walk.cons (show G.Adj 0 4 from by decide) (Walk.cons (show G.Adj 4 6 from by decide) (Walk.cons (show G.Adj 6 2 from by decide) (Walk.cons (show G.Adj 2 9 from by decide) (Walk.cons (show G.Adj 9 11 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_4_5 : DyadicPath G 4 5 := by
  refine ⟨3, (Walk.cons (show G.Adj 4 0 from by decide) (Walk.cons (show G.Adj 0 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 9 from by decide) (Walk.cons (show G.Adj 9 2 from by decide) (Walk.cons (show G.Adj 2 6 from by decide) (Walk.cons (show G.Adj 6 3 from by decide) (Walk.cons (show G.Adj 3 5 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_4_6 : DyadicPath G 4 6 := by
  refine ⟨3, (Walk.cons (show G.Adj 4 10 from by decide) (Walk.cons (show G.Adj 10 11 from by decide) (Walk.cons (show G.Adj 11 1 from by decide) (Walk.cons (show G.Adj 1 0 from by decide) (Walk.cons (show G.Adj 0 8 from by decide) (Walk.cons (show G.Adj 8 5 from by decide) (Walk.cons (show G.Adj 5 3 from by decide) (Walk.cons (show G.Adj 3 6 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_4_7 : DyadicPath G 4 7 := by
  refine ⟨3, (Walk.cons (show G.Adj 4 0 from by decide) (Walk.cons (show G.Adj 0 8 from by decide) (Walk.cons (show G.Adj 8 5 from by decide) (Walk.cons (show G.Adj 5 3 from by decide) (Walk.cons (show G.Adj 3 6 from by decide) (Walk.cons (show G.Adj 6 2 from by decide) (Walk.cons (show G.Adj 2 9 from by decide) (Walk.cons (show G.Adj 9 7 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_4_8 : DyadicPath G 4 8 := by
  refine ⟨3, (Walk.cons (show G.Adj 4 10 from by decide) (Walk.cons (show G.Adj 10 11 from by decide) (Walk.cons (show G.Adj 11 9 from by decide) (Walk.cons (show G.Adj 9 2 from by decide) (Walk.cons (show G.Adj 2 6 from by decide) (Walk.cons (show G.Adj 6 3 from by decide) (Walk.cons (show G.Adj 3 5 from by decide) (Walk.cons (show G.Adj 5 8 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_4_9 : DyadicPath G 4 9 := by
  refine ⟨2, (Walk.cons (show G.Adj 4 0 from by decide) (Walk.cons (show G.Adj 0 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 9 from by decide) Walk.nil)))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_4_10 : DyadicPath G 4 10 := by
  refine ⟨2, (Walk.cons (show G.Adj 4 0 from by decide) (Walk.cons (show G.Adj 0 1 from by decide) (Walk.cons (show G.Adj 1 11 from by decide) (Walk.cons (show G.Adj 11 10 from by decide) Walk.nil)))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_4_11 : DyadicPath G 4 11 := by
  refine ⟨3, (Walk.cons (show G.Adj 4 0 from by decide) (Walk.cons (show G.Adj 0 8 from by decide) (Walk.cons (show G.Adj 8 5 from by decide) (Walk.cons (show G.Adj 5 3 from by decide) (Walk.cons (show G.Adj 3 6 from by decide) (Walk.cons (show G.Adj 6 2 from by decide) (Walk.cons (show G.Adj 2 9 from by decide) (Walk.cons (show G.Adj 9 11 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_5_6 : DyadicPath G 5 6 := by
  refine ⟨3, (Walk.cons (show G.Adj 5 8 from by decide) (Walk.cons (show G.Adj 8 0 from by decide) (Walk.cons (show G.Adj 0 4 from by decide) (Walk.cons (show G.Adj 4 10 from by decide) (Walk.cons (show G.Adj 10 11 from by decide) (Walk.cons (show G.Adj 11 9 from by decide) (Walk.cons (show G.Adj 9 2 from by decide) (Walk.cons (show G.Adj 2 6 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_5_7 : DyadicPath G 5 7 := by
  refine ⟨3, (Walk.cons (show G.Adj 5 3 from by decide) (Walk.cons (show G.Adj 3 6 from by decide) (Walk.cons (show G.Adj 6 4 from by decide) (Walk.cons (show G.Adj 4 0 from by decide) (Walk.cons (show G.Adj 0 1 from by decide) (Walk.cons (show G.Adj 1 11 from by decide) (Walk.cons (show G.Adj 11 9 from by decide) (Walk.cons (show G.Adj 9 7 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_5_8 : DyadicPath G 5 8 := by
  refine ⟨3, (Walk.cons (show G.Adj 5 3 from by decide) (Walk.cons (show G.Adj 3 6 from by decide) (Walk.cons (show G.Adj 6 2 from by decide) (Walk.cons (show G.Adj 2 9 from by decide) (Walk.cons (show G.Adj 9 11 from by decide) (Walk.cons (show G.Adj 11 1 from by decide) (Walk.cons (show G.Adj 1 0 from by decide) (Walk.cons (show G.Adj 0 8 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_5_9 : DyadicPath G 5 9 := by
  refine ⟨2, (Walk.cons (show G.Adj 5 3 from by decide) (Walk.cons (show G.Adj 3 6 from by decide) (Walk.cons (show G.Adj 6 2 from by decide) (Walk.cons (show G.Adj 2 9 from by decide) Walk.nil)))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_5_10 : DyadicPath G 5 10 := by
  refine ⟨2, (Walk.cons (show G.Adj 5 8 from by decide) (Walk.cons (show G.Adj 8 0 from by decide) (Walk.cons (show G.Adj 0 4 from by decide) (Walk.cons (show G.Adj 4 10 from by decide) Walk.nil)))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_5_11 : DyadicPath G 5 11 := by
  refine ⟨2, (Walk.cons (show G.Adj 5 8 from by decide) (Walk.cons (show G.Adj 8 0 from by decide) (Walk.cons (show G.Adj 0 1 from by decide) (Walk.cons (show G.Adj 1 11 from by decide) Walk.nil)))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_6_7 : DyadicPath G 6 7 := by
  refine ⟨3, (Walk.cons (show G.Adj 6 2 from by decide) (Walk.cons (show G.Adj 2 9 from by decide) (Walk.cons (show G.Adj 9 11 from by decide) (Walk.cons (show G.Adj 11 10 from by decide) (Walk.cons (show G.Adj 10 4 from by decide) (Walk.cons (show G.Adj 4 0 from by decide) (Walk.cons (show G.Adj 0 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_6_8 : DyadicPath G 6 8 := by
  refine ⟨2, (Walk.cons (show G.Adj 6 2 from by decide) (Walk.cons (show G.Adj 2 9 from by decide) (Walk.cons (show G.Adj 9 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) Walk.nil)))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_6_9 : DyadicPath G 6 9 := by
  refine ⟨3, (Walk.cons (show G.Adj 6 3 from by decide) (Walk.cons (show G.Adj 3 5 from by decide) (Walk.cons (show G.Adj 5 8 from by decide) (Walk.cons (show G.Adj 8 0 from by decide) (Walk.cons (show G.Adj 0 4 from by decide) (Walk.cons (show G.Adj 4 10 from by decide) (Walk.cons (show G.Adj 10 11 from by decide) (Walk.cons (show G.Adj 11 9 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_6_10 : DyadicPath G 6 10 := by
  refine ⟨2, (Walk.cons (show G.Adj 6 2 from by decide) (Walk.cons (show G.Adj 2 9 from by decide) (Walk.cons (show G.Adj 9 11 from by decide) (Walk.cons (show G.Adj 11 10 from by decide) Walk.nil)))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_6_11 : DyadicPath G 6 11 := by
  refine ⟨3, (Walk.cons (show G.Adj 6 2 from by decide) (Walk.cons (show G.Adj 2 9 from by decide) (Walk.cons (show G.Adj 9 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 0 from by decide) (Walk.cons (show G.Adj 0 4 from by decide) (Walk.cons (show G.Adj 4 10 from by decide) (Walk.cons (show G.Adj 10 11 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_7_8 : DyadicPath G 7 8 := by
  refine ⟨3, (Walk.cons (show G.Adj 7 9 from by decide) (Walk.cons (show G.Adj 9 11 from by decide) (Walk.cons (show G.Adj 11 10 from by decide) (Walk.cons (show G.Adj 10 4 from by decide) (Walk.cons (show G.Adj 4 6 from by decide) (Walk.cons (show G.Adj 6 3 from by decide) (Walk.cons (show G.Adj 3 5 from by decide) (Walk.cons (show G.Adj 5 8 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_7_9 : DyadicPath G 7 9 := by
  refine ⟨3, (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 5 from by decide) (Walk.cons (show G.Adj 5 3 from by decide) (Walk.cons (show G.Adj 3 6 from by decide) (Walk.cons (show G.Adj 6 4 from by decide) (Walk.cons (show G.Adj 4 10 from by decide) (Walk.cons (show G.Adj 10 11 from by decide) (Walk.cons (show G.Adj 11 9 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_7_10 : DyadicPath G 7 10 := by
  refine ⟨2, (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 0 from by decide) (Walk.cons (show G.Adj 0 4 from by decide) (Walk.cons (show G.Adj 4 10 from by decide) Walk.nil)))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_7_11 : DyadicPath G 7 11 := by
  refine ⟨2, (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 0 from by decide) (Walk.cons (show G.Adj 0 1 from by decide) (Walk.cons (show G.Adj 1 11 from by decide) Walk.nil)))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_8_9 : DyadicPath G 8 9 := by
  refine ⟨3, (Walk.cons (show G.Adj 8 0 from by decide) (Walk.cons (show G.Adj 0 1 from by decide) (Walk.cons (show G.Adj 1 11 from by decide) (Walk.cons (show G.Adj 11 10 from by decide) (Walk.cons (show G.Adj 10 4 from by decide) (Walk.cons (show G.Adj 4 6 from by decide) (Walk.cons (show G.Adj 6 2 from by decide) (Walk.cons (show G.Adj 2 9 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_8_10 : DyadicPath G 8 10 := by
  refine ⟨2, (Walk.cons (show G.Adj 8 0 from by decide) (Walk.cons (show G.Adj 0 1 from by decide) (Walk.cons (show G.Adj 1 11 from by decide) (Walk.cons (show G.Adj 11 10 from by decide) Walk.nil)))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_8_11 : DyadicPath G 8 11 := by
  refine ⟨2, (Walk.cons (show G.Adj 8 0 from by decide) (Walk.cons (show G.Adj 0 4 from by decide) (Walk.cons (show G.Adj 4 10 from by decide) (Walk.cons (show G.Adj 10 11 from by decide) Walk.nil)))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_9_10 : DyadicPath G 9 10 := by
  refine ⟨3, (Walk.cons (show G.Adj 9 2 from by decide) (Walk.cons (show G.Adj 2 6 from by decide) (Walk.cons (show G.Adj 6 3 from by decide) (Walk.cons (show G.Adj 3 5 from by decide) (Walk.cons (show G.Adj 5 8 from by decide) (Walk.cons (show G.Adj 8 0 from by decide) (Walk.cons (show G.Adj 0 4 from by decide) (Walk.cons (show G.Adj 4 10 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_9_11 : DyadicPath G 9 11 := by
  refine ⟨3, (Walk.cons (show G.Adj 9 2 from by decide) (Walk.cons (show G.Adj 2 6 from by decide) (Walk.cons (show G.Adj 6 3 from by decide) (Walk.cons (show G.Adj 3 5 from by decide) (Walk.cons (show G.Adj 5 8 from by decide) (Walk.cons (show G.Adj 8 0 from by decide) (Walk.cons (show G.Adj 0 1 from by decide) (Walk.cons (show G.Adj 1 11 from by decide) Walk.nil)))))))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem path_10_11 : DyadicPath G 10 11 := by
  refine ⟨2, (Walk.cons (show G.Adj 10 4 from by decide) (Walk.cons (show G.Adj 4 0 from by decide) (Walk.cons (show G.Adj 0 1 from by decide) (Walk.cons (show G.Adj 1 11 from by decide) Walk.nil)))), by decide, ?_, rfl⟩
  apply Walk.IsPath.mk'
  decide

theorem all_pairs_dyadic : ∀ u v : V, u ≠ v → DyadicPath G u v := by
  intro u v h
  fin_cases u <;> fin_cases v
  · exact (h rfl).elim
  · exact path_0_1
  · exact path_0_2
  · exact path_0_3
  · exact path_0_4
  · exact path_0_5
  · exact path_0_6
  · exact path_0_7
  · exact path_0_8
  · exact path_0_9
  · exact path_0_10
  · exact path_0_11
  · exact path_0_1.symm
  · exact (h rfl).elim
  · exact path_1_2
  · exact path_1_3
  · exact path_1_4
  · exact path_1_5
  · exact path_1_6
  · exact path_1_7
  · exact path_1_8
  · exact path_1_9
  · exact path_1_10
  · exact path_1_11
  · exact path_0_2.symm
  · exact path_1_2.symm
  · exact (h rfl).elim
  · exact path_2_3
  · exact path_2_4
  · exact path_2_5
  · exact path_2_6
  · exact path_2_7
  · exact path_2_8
  · exact path_2_9
  · exact path_2_10
  · exact path_2_11
  · exact path_0_3.symm
  · exact path_1_3.symm
  · exact path_2_3.symm
  · exact (h rfl).elim
  · exact path_3_4
  · exact path_3_5
  · exact path_3_6
  · exact path_3_7
  · exact path_3_8
  · exact path_3_9
  · exact path_3_10
  · exact path_3_11
  · exact path_0_4.symm
  · exact path_1_4.symm
  · exact path_2_4.symm
  · exact path_3_4.symm
  · exact (h rfl).elim
  · exact path_4_5
  · exact path_4_6
  · exact path_4_7
  · exact path_4_8
  · exact path_4_9
  · exact path_4_10
  · exact path_4_11
  · exact path_0_5.symm
  · exact path_1_5.symm
  · exact path_2_5.symm
  · exact path_3_5.symm
  · exact path_4_5.symm
  · exact (h rfl).elim
  · exact path_5_6
  · exact path_5_7
  · exact path_5_8
  · exact path_5_9
  · exact path_5_10
  · exact path_5_11
  · exact path_0_6.symm
  · exact path_1_6.symm
  · exact path_2_6.symm
  · exact path_3_6.symm
  · exact path_4_6.symm
  · exact path_5_6.symm
  · exact (h rfl).elim
  · exact path_6_7
  · exact path_6_8
  · exact path_6_9
  · exact path_6_10
  · exact path_6_11
  · exact path_0_7.symm
  · exact path_1_7.symm
  · exact path_2_7.symm
  · exact path_3_7.symm
  · exact path_4_7.symm
  · exact path_5_7.symm
  · exact path_6_7.symm
  · exact (h rfl).elim
  · exact path_7_8
  · exact path_7_9
  · exact path_7_10
  · exact path_7_11
  · exact path_0_8.symm
  · exact path_1_8.symm
  · exact path_2_8.symm
  · exact path_3_8.symm
  · exact path_4_8.symm
  · exact path_5_8.symm
  · exact path_6_8.symm
  · exact path_7_8.symm
  · exact (h rfl).elim
  · exact path_8_9
  · exact path_8_10
  · exact path_8_11
  · exact path_0_9.symm
  · exact path_1_9.symm
  · exact path_2_9.symm
  · exact path_3_9.symm
  · exact path_4_9.symm
  · exact path_5_9.symm
  · exact path_6_9.symm
  · exact path_7_9.symm
  · exact path_8_9.symm
  · exact (h rfl).elim
  · exact path_9_10
  · exact path_9_11
  · exact path_0_10.symm
  · exact path_1_10.symm
  · exact path_2_10.symm
  · exact path_3_10.symm
  · exact path_4_10.symm
  · exact path_5_10.symm
  · exact path_6_10.symm
  · exact path_7_10.symm
  · exact path_8_10.symm
  · exact path_9_10.symm
  · exact (h rfl).elim
  · exact path_10_11
  · exact path_0_11.symm
  · exact path_1_11.symm
  · exact path_2_11.symm
  · exact path_3_11.symm
  · exact path_4_11.symm
  · exact path_5_11.symm
  · exact path_6_11.symm
  · exact path_7_11.symm
  · exact path_8_11.symm
  · exact path_9_11.symm
  · exact path_10_11.symm
  · exact (h rfl).elim

/-- These are bounded walk enumerations supplied by Mathlib, not axioms
asserting a separate executable's result. Their exact finite scope is 4/8. -/
theorem no_four : ∀ (v : V) (p : G.Walk v v), p.length = 4 → ¬p.IsCycle := by
  have checked : ∀ v : V, ∀ p ∈ G.finsetWalkLength 4 v v,
      ¬p.support.tail.Nodup := by decide
  intro v p hlen hc
  exact checked v p (mem_finsetWalkLength_iff.mpr hlen) hc.support_nodup

theorem no_eight : ∀ (v : V) (p : G.Walk v v), p.length = 8 → ¬p.IsCycle := by
  have checked : ∀ v : V, ∀ p ∈ G.finsetWalkLength 8 v v,
      ¬p.support.tail.Nodup := by decide
  intro v p hlen hc
  exact checked v p (mem_finsetWalkLength_iff.mpr hlen) hc.support_nodup

/-- The order bound connects the two finite checks to the exact, unbounded
HasPower predicate: every simple cycle has length at most twelve. -/
theorem no_power : ¬HasPower G := by
  rintro ⟨k,v,p,hk,hc,hlen⟩
  have hbound : p.length ≤ 12 := by simpa using hc.length_le_natCard
  have hklt : k < 4 := by
    by_contra h
    have hge : 4 ≤ k := by omega
    have hp : (2 : ℕ)^4 ≤ 2^k := Nat.pow_le_pow_right (by omega) hge
    norm_num at hp
    omega
  have hcases : k = 2 ∨ k = 3 := by omega
  rcases hcases with h | h
  · subst k
    exact no_four v p (by simpa using hlen) hc
  · subst k
    exact no_eight v p (by simpa using hlen) hc

theorem triangle_free : ¬∃ a b c : V, G.Adj a b ∧ G.Adj b c ∧ G.Adj c a := by
  decide

theorem degrees : ∀ v : V, 2 ≤ G.degree v ∧ G.degree v ≤ 3 := by decide

theorem not_near : ¬Near G := by decide

/-- Exact refutation of the proposed global forcing lemma. The minimum
cardinality guard excludes empty/singleton vacuity. -/
theorem counterexample :
    2 ≤ Fintype.card V ∧
    (∀ u v : V, u ≠ v → DyadicPath G u v) ∧
    (∀ v : V, 2 ≤ G.degree v ∧ G.degree v ≤ 3) ∧
    (¬∃ a b c : V, G.Adj a b ∧ G.Adj b c ∧ G.Adj c a) ∧
    ¬HasPower G ∧ ¬Near G := by
  exact ⟨by decide,all_pairs_dyadic,degrees,triangle_free,no_power,not_near⟩

#print axioms all_pairs_dyadic
#print axioms no_four
#print axioms no_eight
#print axioms no_power
#print axioms counterexample
end E64AllPairsObstruction
