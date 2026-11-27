import Shadow

/-!
Exact fourteen-vertex obstruction to using the known dyadic-path consequences
alone. The graph is triangle-free, subcubic, and NOT Near. All pairs have
power-length paths; distant pairs have two exits; every induced P3 is on
both a 9-cycle and a 6- or 10-cycle. Nevertheless there is no power cycle.
This is not an original Erdős–Gyárfás counterexample or a terminal exclusion.
All finite facts use ordinary kernel reduction, with actual SimpleGraph.Walk
witnesses and the original unbounded HasPower predicate.
-/
namespace E64AllPairsObstruction
open SimpleGraph Erdos64Closure
open scoped Sym2
set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev V := Fin 14

def edgeList : List (V × V) :=
  [(0, 3), (0, 6), (0, 11), (1, 4), (1, 7), (1, 10), (2, 4), (2, 11), (2, 13), (3, 7), (3, 12), (5, 10), (5, 12), (6, 9), (6, 10), (7, 8), (8, 13), (9, 13)]

def Adj (u v : V) : Prop := (u,v) ∈ edgeList ∨ (v,u) ∈ edgeList
instance adjDecidable : DecidableRel Adj := fun u v =>
  inferInstanceAs (Decidable ((u,v) ∈ edgeList ∨ (v,u) ∈ edgeList))

def G : SimpleGraph V where
  Adj := Adj
  symm := ⟨by intro u v h; exact h.elim Or.inr Or.inl⟩
  loopless := ⟨by intro u; fin_cases u <;> decide⟩
instance graphAdjDecidable : DecidableRel G.Adj := adjDecidable

def DyadicPath {W : Type*} (H : SimpleGraph W) (u v : W) : Prop :=
  ∃ (k : ℕ) (p : H.Walk u v), 2 ≤ k ∧ p.IsPath ∧ p.length = 2^k

structure PathCert where
  start : V
  stop : V
  exit : V
  exponent : ℕ
  walk : G.Walk start stop
  exponent_ge : 2 ≤ exponent
  path : walk.IsPath
  len : walk.length = 2^exponent
  first : walk.snd = exit

def pc0 : PathCert := by
  refine ⟨0,10,3,2,(Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc1 : PathCert := by
  refine ⟨0,11,3,3,(Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc2 : PathCert := by
  refine ⟨0,13,3,3,(Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc3 : PathCert := by
  refine ⟨0,8,3,3,(Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc4 : PathCert := by
  refine ⟨0,2,3,3,(Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc5 : PathCert := by
  refine ⟨0,1,3,3,(Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc6 : PathCert := by
  refine ⟨0,5,3,3,(Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc7 : PathCert := by
  refine ⟨0,4,3,2,(Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc8 : PathCert := by
  refine ⟨0,6,3,3,(Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc9 : PathCert := by
  refine ⟨0,1,11,2,(Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc10 : PathCert := by
  refine ⟨0,3,11,3,(Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc11 : PathCert := by
  refine ⟨0,13,11,3,(Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc12 : PathCert := by
  refine ⟨0,9,11,3,(Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc13 : PathCert := by
  refine ⟨0,5,11,3,(Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc14 : PathCert := by
  refine ⟨0,8,11,2,(Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc15 : PathCert := by
  refine ⟨0,6,11,3,(Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc16 : PathCert := by
  refine ⟨0,4,11,3,(Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc17 : PathCert := by
  refine ⟨0,7,11,3,(Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc18 : PathCert := by
  refine ⟨0,12,11,3,(Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc19 : PathCert := by
  refine ⟨0,8,6,2,(Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc20 : PathCert := by
  refine ⟨0,5,6,3,(Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc21 : PathCert := by
  refine ⟨0,2,6,3,(Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc22 : PathCert := by
  refine ⟨0,3,6,3,(Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc23 : PathCert := by
  refine ⟨0,4,6,2,(Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc24 : PathCert := by
  refine ⟨0,7,6,3,(Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc25 : PathCert := by
  refine ⟨0,11,6,3,(Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc26 : PathCert := by
  refine ⟨0,12,6,2,(Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc27 : PathCert := by
  refine ⟨0,13,6,3,(Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc28 : PathCert := by
  refine ⟨1,3,10,2,(Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc29 : PathCert := by
  refine ⟨1,4,10,3,(Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc30 : PathCert := by
  refine ⟨1,13,10,3,(Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc31 : PathCert := by
  refine ⟨1,9,10,3,(Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc32 : PathCert := by
  refine ⟨1,2,10,3,(Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc33 : PathCert := by
  refine ⟨1,11,10,2,(Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc34 : PathCert := by
  refine ⟨1,7,10,3,(Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc35 : PathCert := by
  refine ⟨1,0,10,3,(Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc36 : PathCert := by
  refine ⟨1,12,10,3,(Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc37 : PathCert := by
  refine ⟨1,0,4,2,(Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc38 : PathCert := by
  refine ⟨1,10,4,3,(Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc39 : PathCert := by
  refine ⟨1,13,4,3,(Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc40 : PathCert := by
  refine ⟨1,8,4,3,(Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc41 : PathCert := by
  refine ⟨1,12,4,3,(Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc42 : PathCert := by
  refine ⟨1,11,4,3,(Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc43 : PathCert := by
  refine ⟨1,6,4,3,(Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc44 : PathCert := by
  refine ⟨1,5,4,3,(Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc45 : PathCert := by
  refine ⟨1,9,4,2,(Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc46 : PathCert := by
  refine ⟨1,7,4,3,(Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc47 : PathCert := by
  refine ⟨1,9,7,2,(Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc48 : PathCert := by
  refine ⟨1,12,7,3,(Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc49 : PathCert := by
  refine ⟨1,2,7,3,(Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc50 : PathCert := by
  refine ⟨1,10,7,3,(Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc51 : PathCert := by
  refine ⟨1,11,7,2,(Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc52 : PathCert := by
  refine ⟨1,6,7,3,(Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc53 : PathCert := by
  refine ⟨1,4,7,3,(Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc54 : PathCert := by
  refine ⟨1,5,7,2,(Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc55 : PathCert := by
  refine ⟨1,13,7,3,(Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc56 : PathCert := by
  refine ⟨2,12,11,2,(Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc57 : PathCert := by
  refine ⟨2,4,11,3,(Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc58 : PathCert := by
  refine ⟨2,7,11,3,(Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc59 : PathCert := by
  refine ⟨2,9,11,3,(Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc60 : PathCert := by
  refine ⟨2,6,11,3,(Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc61 : PathCert := by
  refine ⟨2,1,11,3,(Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc62 : PathCert := by
  refine ⟨2,3,11,3,(Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc63 : PathCert := by
  refine ⟨2,10,11,2,(Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc64 : PathCert := by
  refine ⟨2,13,11,3,(Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc65 : PathCert := by
  refine ⟨2,5,4,2,(Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc66 : PathCert := by
  refine ⟨2,11,4,3,(Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc67 : PathCert := by
  refine ⟨2,6,4,3,(Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc68 : PathCert := by
  refine ⟨2,8,4,3,(Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc69 : PathCert := by
  refine ⟨2,7,4,3,(Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc70 : PathCert := by
  refine ⟨2,0,4,3,(Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc71 : PathCert := by
  refine ⟨2,10,4,3,(Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc72 : PathCert := by
  refine ⟨2,3,4,2,(Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc73 : PathCert := by
  refine ⟨2,13,4,3,(Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc74 : PathCert := by
  refine ⟨2,1,13,2,(Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc75 : PathCert := by
  refine ⟨2,3,13,3,(Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc76 : PathCert := by
  refine ⟨2,11,13,3,(Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc77 : PathCert := by
  refine ⟨2,5,13,3,(Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc78 : PathCert := by
  refine ⟨2,6,13,3,(Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc79 : PathCert := by
  refine ⟨2,0,13,2,(Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc80 : PathCert := by
  refine ⟨2,10,13,3,(Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc81 : PathCert := by
  refine ⟨2,4,13,3,(Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc82 : PathCert := by
  refine ⟨2,12,13,3,(Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc83 : PathCert := by
  refine ⟨2,7,13,3,(Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc84 : PathCert := by
  refine ⟨3,4,0,2,(Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc85 : PathCert := by
  refine ⟨3,12,0,3,(Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc86 : PathCert := by
  refine ⟨3,9,0,3,(Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc87 : PathCert := by
  refine ⟨3,13,0,3,(Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc88 : PathCert := by
  refine ⟨3,10,0,3,(Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc89 : PathCert := by
  refine ⟨3,1,0,3,(Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc90 : PathCert := by
  refine ⟨3,5,0,3,(Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc91 : PathCert := by
  refine ⟨3,7,0,3,(Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc92 : PathCert := by
  refine ⟨3,8,0,3,(Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc93 : PathCert := by
  refine ⟨3,2,0,3,(Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc94 : PathCert := by
  refine ⟨3,1,12,2,(Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc95 : PathCert := by
  refine ⟨3,0,12,3,(Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc96 : PathCert := by
  refine ⟨3,8,12,3,(Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc97 : PathCert := by
  refine ⟨3,9,12,3,(Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc98 : PathCert := by
  refine ⟨3,2,12,3,(Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc99 : PathCert := by
  refine ⟨3,6,12,2,(Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc100 : PathCert := by
  refine ⟨3,4,12,3,(Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc101 : PathCert := by
  refine ⟨3,13,12,3,(Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc102 : PathCert := by
  refine ⟨3,7,12,3,(Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc103 : PathCert := by
  refine ⟨3,11,12,3,(Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc104 : PathCert := by
  refine ⟨3,9,7,2,(Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc105 : PathCert := by
  refine ⟨3,2,7,3,(Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc106 : PathCert := by
  refine ⟨3,4,7,3,(Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc107 : PathCert := by
  refine ⟨3,12,7,3,(Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc108 : PathCert := by
  refine ⟨3,10,7,3,(Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc109 : PathCert := by
  refine ⟨3,5,7,3,(Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc110 : PathCert := by
  refine ⟨3,6,7,3,(Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc111 : PathCert := by
  refine ⟨3,13,7,3,(Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc112 : PathCert := by
  refine ⟨3,11,7,3,(Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc113 : PathCert := by
  refine ⟨3,0,7,3,(Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc114 : PathCert := by
  refine ⟨4,12,1,2,(Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc115 : PathCert := by
  refine ⟨4,2,1,3,(Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc116 : PathCert := by
  refine ⟨4,9,1,3,(Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc117 : PathCert := by
  refine ⟨4,13,1,3,(Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc118 : PathCert := by
  refine ⟨4,0,1,2,(Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc119 : PathCert := by
  refine ⟨4,8,1,3,(Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc120 : PathCert := by
  refine ⟨4,3,1,3,(Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc121 : PathCert := by
  refine ⟨4,11,1,3,(Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc122 : PathCert := by
  refine ⟨4,5,1,3,(Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc123 : PathCert := by
  refine ⟨4,6,1,3,(Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc124 : PathCert := by
  refine ⟨4,3,2,2,(Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc125 : PathCert := by
  refine ⟨4,1,2,3,(Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc126 : PathCert := by
  refine ⟨4,6,2,3,(Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc127 : PathCert := by
  refine ⟨4,9,2,3,(Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc128 : PathCert := by
  refine ⟨4,5,2,3,(Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc129 : PathCert := by
  refine ⟨4,7,2,3,(Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc130 : PathCert := by
  refine ⟨4,8,2,3,(Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc131 : PathCert := by
  refine ⟨4,12,2,3,(Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc132 : PathCert := by
  refine ⟨4,0,2,3,(Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc133 : PathCert := by
  refine ⟨4,10,2,3,(Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc134 : PathCert := by
  refine ⟨5,2,10,2,(Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc135 : PathCert := by
  refine ⟨5,12,10,3,(Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc136 : PathCert := by
  refine ⟨5,7,10,3,(Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc137 : PathCert := by
  refine ⟨5,9,10,3,(Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc138 : PathCert := by
  refine ⟨5,3,10,3,(Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc139 : PathCert := by
  refine ⟨5,0,10,3,(Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc140 : PathCert := by
  refine ⟨5,8,10,2,(Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc141 : PathCert := by
  refine ⟨5,4,10,3,(Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc142 : PathCert := by
  refine ⟨5,13,10,3,(Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc143 : PathCert := by
  refine ⟨5,11,10,2,(Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc144 : PathCert := by
  refine ⟨5,11,12,2,(Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc145 : PathCert := by
  refine ⟨5,10,12,3,(Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc146 : PathCert := by
  refine ⟨5,7,12,3,(Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc147 : PathCert := by
  refine ⟨5,6,12,3,(Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc148 : PathCert := by
  refine ⟨5,4,12,3,(Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc149 : PathCert := by
  refine ⟨5,2,12,3,(Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc150 : PathCert := by
  refine ⟨5,8,12,3,(Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc151 : PathCert := by
  refine ⟨5,0,12,3,(Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc152 : PathCert := by
  refine ⟨5,1,12,3,(Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc153 : PathCert := by
  refine ⟨5,13,12,3,(Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc154 : PathCert := by
  refine ⟨5,9,12,3,(Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc155 : PathCert := by
  refine ⟨6,5,0,2,(Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc156 : PathCert := by
  refine ⟨6,2,0,3,(Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc157 : PathCert := by
  refine ⟨6,8,0,3,(Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc158 : PathCert := by
  refine ⟨6,1,0,3,(Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc159 : PathCert := by
  refine ⟨6,9,0,3,(Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc160 : PathCert := by
  refine ⟨6,4,0,2,(Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc161 : PathCert := by
  refine ⟨6,12,0,3,(Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc162 : PathCert := by
  refine ⟨6,13,0,3,(Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc163 : PathCert := by
  refine ⟨6,10,0,3,(Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc164 : PathCert := by
  refine ⟨6,7,9,2,(Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc165 : PathCert := by
  refine ⟨6,12,9,3,(Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc166 : PathCert := by
  refine ⟨6,11,9,3,(Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc167 : PathCert := by
  refine ⟨6,2,9,3,(Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc168 : PathCert := by
  refine ⟨6,10,9,3,(Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc169 : PathCert := by
  refine ⟨6,5,9,3,(Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc170 : PathCert := by
  refine ⟨6,8,9,3,(Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc171 : PathCert := by
  refine ⟨6,1,9,3,(Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc172 : PathCert := by
  refine ⟨6,4,9,2,(Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc173 : PathCert := by
  refine ⟨6,0,9,3,(Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc174 : PathCert := by
  refine ⟨6,2,10,2,(Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc175 : PathCert := by
  refine ⟨6,12,10,3,(Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc176 : PathCert := by
  refine ⟨6,7,10,3,(Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc177 : PathCert := by
  refine ⟨6,3,10,3,(Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc178 : PathCert := by
  refine ⟨6,8,10,2,(Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc179 : PathCert := by
  refine ⟨6,0,10,3,(Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc180 : PathCert := by
  refine ⟨6,4,10,3,(Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc181 : PathCert := by
  refine ⟨6,13,10,3,(Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc182 : PathCert := by
  refine ⟨6,9,10,3,(Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc183 : PathCert := by
  refine ⟨7,6,8,2,(Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc184 : PathCert := by
  refine ⟨7,5,8,3,(Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc185 : PathCert := by
  refine ⟨7,4,8,3,(Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc186 : PathCert := by
  refine ⟨7,2,8,3,(Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc187 : PathCert := by
  refine ⟨7,3,8,3,(Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc188 : PathCert := by
  refine ⟨7,11,8,2,(Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc189 : PathCert := by
  refine ⟨7,1,8,3,(Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc190 : PathCert := by
  refine ⟨7,12,8,3,(Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc191 : PathCert := by
  refine ⟨7,0,8,3,(Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc192 : PathCert := by
  refine ⟨7,9,8,3,(Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc193 : PathCert := by
  refine ⟨7,12,1,2,(Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc194 : PathCert := by
  refine ⟨7,2,1,3,(Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc195 : PathCert := by
  refine ⟨7,9,1,3,(Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc196 : PathCert := by
  refine ⟨7,0,1,2,(Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc197 : PathCert := by
  refine ⟨7,8,1,3,(Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc198 : PathCert := by
  refine ⟨7,11,1,2,(Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc199 : PathCert := by
  refine ⟨7,5,1,3,(Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc200 : PathCert := by
  refine ⟨7,13,1,3,(Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc201 : PathCert := by
  refine ⟨7,3,1,3,(Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc202 : PathCert := by
  refine ⟨7,2,3,2,(Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc203 : PathCert := by
  refine ⟨7,5,3,3,(Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc204 : PathCert := by
  refine ⟨7,6,3,3,(Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc205 : PathCert := by
  refine ⟨7,10,3,3,(Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc206 : PathCert := by
  refine ⟨7,9,3,2,(Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc207 : PathCert := by
  refine ⟨7,1,3,3,(Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc208 : PathCert := by
  refine ⟨7,11,3,3,(Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc209 : PathCert := by
  refine ⟨7,13,3,3,(Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc210 : PathCert := by
  refine ⟨7,8,3,3,(Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc211 : PathCert := by
  refine ⟨8,0,13,2,(Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc212 : PathCert := by
  refine ⟨8,10,13,3,(Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc213 : PathCert := by
  refine ⟨8,4,13,3,(Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc214 : PathCert := by
  refine ⟨8,1,13,3,(Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc215 : PathCert := by
  refine ⟨8,11,13,3,(Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc216 : PathCert := by
  refine ⟨8,12,13,3,(Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc217 : PathCert := by
  refine ⟨8,7,13,3,(Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc218 : PathCert := by
  refine ⟨8,3,13,3,(Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc219 : PathCert := by
  refine ⟨8,6,13,3,(Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc220 : PathCert := by
  refine ⟨8,5,13,3,(Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc221 : PathCert := by
  refine ⟨8,5,7,2,(Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc222 : PathCert := by
  refine ⟨8,11,7,3,(Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc223 : PathCert := by
  refine ⟨8,6,7,3,(Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc224 : PathCert := by
  refine ⟨8,4,7,3,(Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc225 : PathCert := by
  refine ⟨8,13,7,3,(Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc226 : PathCert := by
  refine ⟨8,2,7,2,(Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc227 : PathCert := by
  refine ⟨8,12,7,3,(Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc228 : PathCert := by
  refine ⟨8,9,7,3,(Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc229 : PathCert := by
  refine ⟨8,10,7,3,(Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc230 : PathCert := by
  refine ⟨8,0,7,3,(Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc231 : PathCert := by
  refine ⟨9,1,13,2,(Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc232 : PathCert := by
  refine ⟨9,3,13,3,(Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc233 : PathCert := by
  refine ⟨9,11,13,3,(Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc234 : PathCert := by
  refine ⟨9,0,13,3,(Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc235 : PathCert := by
  refine ⟨9,4,13,3,(Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc236 : PathCert := by
  refine ⟨9,5,13,3,(Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc237 : PathCert := by
  refine ⟨9,6,13,3,(Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc238 : PathCert := by
  refine ⟨9,10,13,3,(Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc239 : PathCert := by
  refine ⟨9,7,13,3,(Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc240 : PathCert := by
  refine ⟨9,12,13,3,(Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc241 : PathCert := by
  refine ⟨9,12,6,2,(Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc242 : PathCert := by
  refine ⟨9,4,6,3,(Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc243 : PathCert := by
  refine ⟨9,7,6,3,(Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc244 : PathCert := by
  refine ⟨9,11,6,3,(Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc245 : PathCert := by
  refine ⟨9,13,6,3,(Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc246 : PathCert := by
  refine ⟨9,2,6,2,(Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc247 : PathCert := by
  refine ⟨9,5,6,3,(Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc248 : PathCert := by
  refine ⟨9,8,6,3,(Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc249 : PathCert := by
  refine ⟨9,3,6,3,(Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc250 : PathCert := by
  refine ⟨9,1,6,3,(Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc251 : PathCert := by
  refine ⟨10,11,1,2,(Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc252 : PathCert := by
  refine ⟨10,5,1,3,(Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc253 : PathCert := by
  refine ⟨10,8,1,3,(Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc254 : PathCert := by
  refine ⟨10,13,1,3,(Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc255 : PathCert := by
  refine ⟨10,0,1,3,(Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc256 : PathCert := by
  refine ⟨10,12,1,3,(Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc257 : PathCert := by
  refine ⟨10,3,1,3,(Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc258 : PathCert := by
  refine ⟨10,6,1,3,(Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc259 : PathCert := by
  refine ⟨10,9,1,3,(Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc260 : PathCert := by
  refine ⟨10,2,1,3,(Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc261 : PathCert := by
  refine ⟨10,0,5,2,(Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc262 : PathCert := by
  refine ⟨10,1,5,3,(Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc263 : PathCert := by
  refine ⟨10,8,5,3,(Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc264 : PathCert := by
  refine ⟨10,9,5,3,(Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc265 : PathCert := by
  refine ⟨10,2,5,3,(Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc266 : PathCert := by
  refine ⟨10,7,5,2,(Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc267 : PathCert := by
  refine ⟨10,6,5,3,(Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc268 : PathCert := by
  refine ⟨10,11,5,3,(Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc269 : PathCert := by
  refine ⟨10,4,5,3,(Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc270 : PathCert := by
  refine ⟨10,13,5,3,(Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc271 : PathCert := by
  refine ⟨10,12,6,2,(Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc272 : PathCert := by
  refine ⟨10,7,6,2,(Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc273 : PathCert := by
  refine ⟨10,11,6,3,(Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc274 : PathCert := by
  refine ⟨10,4,6,3,(Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc275 : PathCert := by
  refine ⟨10,13,6,3,(Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc276 : PathCert := by
  refine ⟨10,2,6,2,(Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc277 : PathCert := by
  refine ⟨10,8,6,3,(Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc278 : PathCert := by
  refine ⟨10,3,6,3,(Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc279 : PathCert := by
  refine ⟨10,1,6,3,(Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc280 : PathCert := by
  refine ⟨10,5,6,3,(Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc281 : PathCert := by
  refine ⟨11,5,0,2,(Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc282 : PathCert := by
  refine ⟨11,2,0,3,(Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc283 : PathCert := by
  refine ⟨11,8,0,3,(Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc284 : PathCert := by
  refine ⟨11,13,0,3,(Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc285 : PathCert := by
  refine ⟨11,10,0,3,(Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc286 : PathCert := by
  refine ⟨11,1,0,3,(Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc287 : PathCert := by
  refine ⟨11,9,0,3,(Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc288 : PathCert := by
  refine ⟨11,4,0,3,(Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc289 : PathCert := by
  refine ⟨11,12,0,3,(Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc290 : PathCert := by
  refine ⟨11,7,0,3,(Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc291 : PathCert := by
  refine ⟨11,10,2,2,(Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc292 : PathCert := by
  refine ⟨11,0,2,3,(Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc293 : PathCert := by
  refine ⟨11,7,2,3,(Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc294 : PathCert := by
  refine ⟨11,12,2,3,(Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc295 : PathCert := by
  refine ⟨11,8,2,3,(Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc296 : PathCert := by
  refine ⟨11,6,2,3,(Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc297 : PathCert := by
  refine ⟨11,9,2,3,(Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc298 : PathCert := by
  refine ⟨11,5,2,3,(Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc299 : PathCert := by
  refine ⟨11,1,2,3,(Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc300 : PathCert := by
  refine ⟨11,3,2,3,(Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc301 : PathCert := by
  refine ⟨12,2,3,2,(Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc302 : PathCert := by
  refine ⟨12,5,3,3,(Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc303 : PathCert := by
  refine ⟨12,6,3,3,(Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc304 : PathCert := by
  refine ⟨12,8,3,3,(Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc305 : PathCert := by
  refine ⟨12,1,3,3,(Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc306 : PathCert := by
  refine ⟨12,10,3,3,(Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc307 : PathCert := by
  refine ⟨12,9,3,2,(Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc308 : PathCert := by
  refine ⟨12,11,3,3,(Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc309 : PathCert := by
  refine ⟨12,13,3,3,(Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc310 : PathCert := by
  refine ⟨12,4,3,2,(Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc311 : PathCert := by
  refine ⟨12,4,5,2,(Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc312 : PathCert := by
  refine ⟨12,3,5,3,(Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc313 : PathCert := by
  refine ⟨12,6,5,3,(Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc314 : PathCert := by
  refine ⟨12,7,5,3,(Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc315 : PathCert := by
  refine ⟨12,11,5,3,(Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc316 : PathCert := by
  refine ⟨12,2,5,3,(Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc317 : PathCert := by
  refine ⟨12,9,5,3,(Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc318 : PathCert := by
  refine ⟨12,0,5,2,(Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc319 : PathCert := by
  refine ⟨12,13,5,3,(Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc320 : PathCert := by
  refine ⟨12,1,5,3,(Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc321 : PathCert := by
  refine ⟨12,8,5,3,(Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc322 : PathCert := by
  refine ⟨13,10,8,2,(Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc323 : PathCert := by
  refine ⟨13,0,8,3,(Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc324 : PathCert := by
  refine ⟨13,12,8,3,(Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc325 : PathCert := by
  refine ⟨13,2,8,3,(Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc326 : PathCert := by
  refine ⟨13,4,8,2,(Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc327 : PathCert := by
  refine ⟨13,3,8,3,(Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc328 : PathCert := by
  refine ⟨13,6,8,3,(Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc329 : PathCert := by
  refine ⟨13,1,8,3,(Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc330 : PathCert := by
  refine ⟨13,9,8,3,(Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc331 : PathCert := by
  refine ⟨13,3,9,2,(Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc332 : PathCert := by
  refine ⟨13,1,9,3,(Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc333 : PathCert := by
  refine ⟨13,5,9,3,(Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc334 : PathCert := by
  refine ⟨13,2,9,3,(Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc335 : PathCert := by
  refine ⟨13,11,9,2,(Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc336 : PathCert := by
  refine ⟨13,10,9,3,(Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc337 : PathCert := by
  refine ⟨13,7,9,3,(Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 11 from by decide) (Walk.cons (show G.Adj 11 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc338 : PathCert := by
  refine ⟨13,0,9,3,(Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc339 : PathCert := by
  refine ⟨13,8,9,3,(Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc340 : PathCert := by
  refine ⟨13,3,2,2,(Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc341 : PathCert := by
  refine ⟨13,1,2,3,(Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc342 : PathCert := by
  refine ⟨13,6,2,3,(Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc343 : PathCert := by
  refine ⟨13,5,2,3,(Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc344 : PathCert := by
  refine ⟨13,8,2,3,(Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc345 : PathCert := by
  refine ⟨13,10,2,2,(Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) Walk.nil)))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc346 : PathCert := by
  refine ⟨13,0,2,3,(Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc347 : PathCert := by
  refine ⟨13,7,2,3,(Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc348 : PathCert := by
  refine ⟨13,12,2,3,(Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) (Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pc349 : PathCert := by
  refine ⟨13,9,2,3,(Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 0 from by decide) (Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) Walk.nil)))))))),by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

def pathData : Array PathCert := #[
  pc0, pc1, pc2, pc3, pc4, pc5, pc6, pc7, pc8, pc9, pc10, pc11, pc12, pc13, pc14, pc15, pc16, pc17, pc18, pc19, pc20, pc21, pc22, pc23, pc24, pc25, pc26, pc27, pc28, pc29, pc30, pc31, pc32, pc33, pc34, pc35, pc36, pc37, pc38, pc39, pc40, pc41, pc42, pc43, pc44, pc45, pc46, pc47, pc48, pc49, pc50, pc51, pc52, pc53, pc54, pc55, pc56, pc57, pc58, pc59, pc60, pc61, pc62, pc63, pc64, pc65, pc66, pc67, pc68, pc69, pc70, pc71, pc72, pc73, pc74, pc75, pc76, pc77, pc78, pc79, pc80, pc81, pc82, pc83, pc84, pc85, pc86, pc87, pc88, pc89, pc90, pc91, pc92, pc93, pc94, pc95, pc96, pc97, pc98, pc99, pc100, pc101, pc102, pc103, pc104, pc105, pc106, pc107, pc108, pc109, pc110, pc111, pc112, pc113, pc114, pc115, pc116, pc117, pc118, pc119, pc120, pc121, pc122, pc123, pc124, pc125, pc126, pc127, pc128, pc129, pc130, pc131, pc132, pc133, pc134, pc135, pc136, pc137, pc138, pc139, pc140, pc141, pc142, pc143, pc144, pc145, pc146, pc147, pc148, pc149, pc150, pc151, pc152, pc153, pc154, pc155, pc156, pc157, pc158, pc159, pc160, pc161, pc162, pc163, pc164, pc165, pc166, pc167, pc168, pc169, pc170, pc171, pc172, pc173, pc174, pc175, pc176, pc177, pc178, pc179, pc180, pc181, pc182, pc183, pc184, pc185, pc186, pc187, pc188, pc189, pc190, pc191, pc192, pc193, pc194, pc195, pc196, pc197, pc198, pc199, pc200, pc201, pc202, pc203, pc204, pc205, pc206, pc207, pc208, pc209, pc210, pc211, pc212, pc213, pc214, pc215, pc216, pc217, pc218, pc219, pc220, pc221, pc222, pc223, pc224, pc225, pc226, pc227, pc228, pc229, pc230, pc231, pc232, pc233, pc234, pc235, pc236, pc237, pc238, pc239, pc240, pc241, pc242, pc243, pc244, pc245, pc246, pc247, pc248, pc249, pc250, pc251, pc252, pc253, pc254, pc255, pc256, pc257, pc258, pc259, pc260, pc261, pc262, pc263, pc264, pc265, pc266, pc267, pc268, pc269, pc270, pc271, pc272, pc273, pc274, pc275, pc276, pc277, pc278, pc279, pc280, pc281, pc282, pc283, pc284, pc285, pc286, pc287, pc288, pc289, pc290, pc291, pc292, pc293, pc294, pc295, pc296, pc297, pc298, pc299, pc300, pc301, pc302, pc303, pc304, pc305, pc306, pc307, pc308, pc309, pc310, pc311, pc312, pc313, pc314, pc315, pc316, pc317, pc318, pc319, pc320, pc321, pc322, pc323, pc324, pc325, pc326, pc327, pc328, pc329, pc330, pc331, pc332, pc333, pc334, pc335, pc336, pc337, pc338, pc339, pc340, pc341, pc342, pc343, pc344, pc345, pc346, pc347, pc348, pc349
]
def pathAt (i : Fin 350) : PathCert :=
  pathData[i.val]'(by simp [pathData])

def firstIndex (u v : V) : Fin 350 :=
  ((#[
    #[0, 5, 4, 10, 7, 6, 8, 17, 3, 12, 0, 1, 18, 2],
    #[35, 0, 32, 28, 29, 44, 43, 34, 40, 31, 38, 33, 36, 30],
    #[70, 61, 0, 62, 57, 65, 60, 58, 68, 59, 63, 66, 56, 64],
    #[95, 89, 93, 0, 84, 90, 99, 91, 92, 86, 88, 103, 85, 87],
    #[118, 125, 115, 120, 0, 122, 123, 129, 119, 116, 133, 121, 114, 117],
    #[139, 152, 134, 138, 141, 0, 147, 136, 140, 137, 145, 143, 135, 142],
    #[173, 158, 156, 177, 160, 155, 0, 164, 157, 159, 163, 166, 161, 162],
    #[191, 189, 186, 187, 185, 184, 183, 0, 197, 192, 205, 188, 190, 200],
    #[211, 214, 226, 218, 213, 220, 219, 217, 0, 228, 212, 215, 216, 225],
    #[234, 231, 246, 232, 235, 236, 237, 239, 248, 0, 238, 233, 240, 245],
    #[255, 262, 260, 257, 269, 252, 258, 266, 253, 259, 0, 251, 256, 254],
    #[292, 286, 282, 300, 288, 281, 296, 290, 283, 287, 285, 0, 289, 284],
    #[318, 305, 301, 312, 310, 302, 303, 314, 304, 307, 306, 308, 0, 309],
    #[323, 329, 325, 327, 326, 333, 328, 337, 339, 330, 322, 335, 324, 0]
  ] : Array (Array (Fin 350)))[u.val]!)[v.val]!

def secondIndex (u v : V) : Fin 350 :=
  ((#[
    #[0, 9, 21, 22, 16, 13, 15, 24, 14, 12, 0, 25, 26, 11],
    #[37, 0, 49, 28, 53, 54, 52, 46, 40, 45, 50, 42, 41, 39],
    #[79, 74, 0, 72, 81, 77, 67, 69, 68, 59, 71, 76, 82, 73],
    #[113, 94, 98, 0, 100, 109, 110, 102, 96, 97, 108, 112, 107, 101],
    #[132, 125, 115, 124, 0, 128, 126, 129, 130, 127, 133, 121, 131, 117],
    #[151, 152, 149, 138, 148, 0, 147, 146, 150, 154, 145, 144, 135, 153],
    #[179, 171, 167, 177, 172, 169, 0, 176, 170, 182, 168, 166, 165, 181],
    #[196, 207, 194, 201, 185, 199, 204, 0, 210, 195, 205, 198, 193, 209],
    #[230, 214, 226, 218, 224, 221, 223, 217, 0, 228, 229, 222, 227, 225],
    #[234, 250, 246, 249, 242, 247, 237, 243, 248, 0, 238, 244, 241, 245],
    #[261, 279, 265, 278, 274, 280, 267, 272, 263, 264, 0, 268, 271, 270],
    #[292, 299, 282, 300, 288, 298, 296, 293, 295, 297, 291, 0, 294, 284],
    #[318, 320, 316, 312, 311, 302, 313, 314, 321, 317, 306, 315, 0, 319],
    #[338, 332, 334, 331, 326, 343, 342, 347, 344, 349, 336, 335, 348, 0]
  ] : Array (Array (Fin 350)))[u.val]!)[v.val]!

theorem first_checked : ∀ u v : V, u ≠ v →
    (pathAt (firstIndex u v)).start = u ∧ (pathAt (firstIndex u v)).stop = v := by
  decide

#print axioms first_checked

theorem all_pairs_dyadic : ∀ u v : V, u ≠ v → DyadicPath G u v := by
  intro u v h
  obtain ⟨hs,ht⟩ := first_checked u v h
  have hp : DyadicPath G (pathAt (firstIndex u v)).start (pathAt (firstIndex u v)).stop :=
    ⟨_,_,(pathAt (firstIndex u v)).exponent_ge,
      (pathAt (firstIndex u v)).path,(pathAt (firstIndex u v)).len⟩
  simpa only [hs,ht] using hp

def TwoExitProperty : Prop :=
  ∀ u v : V, u ≠ v → ¬G.Adj u v → (∀ z : V, ¬(G.Adj u z ∧ G.Adj z v)) →
    ∃ (k l : ℕ) (p q : G.Walk u v),
      2 ≤ k ∧ 2 ≤ l ∧ p.IsPath ∧ q.IsPath ∧
      p.length = 2^k ∧ q.length = 2^l ∧ p.snd ≠ q.snd

theorem exits_checked : ∀ u v : V, u ≠ v → ¬G.Adj u v →
    (∀ z : V, ¬(G.Adj u z ∧ G.Adj z v)) →
    (pathAt (secondIndex u v)).start = u ∧
    (pathAt (secondIndex u v)).stop = v ∧
    (pathAt (firstIndex u v)).exit ≠ (pathAt (secondIndex u v)).exit := by decide

#print axioms exits_checked

theorem two_path_certs (A B : PathCert) (u v : V)
    (hs : A.start = u) (ht : A.stop = v)
    (hs' : B.start = u) (ht' : B.stop = v) (he : A.exit ≠ B.exit) :
    ∃ (k l : ℕ) (p q : G.Walk u v),
      2 ≤ k ∧ 2 ≤ l ∧ p.IsPath ∧ q.IsPath ∧
      p.length = 2^k ∧ q.length = 2^l ∧ p.snd ≠ q.snd := by
  rcases A with ⟨s,t,e,k,p,hk,hp,hlen,hfirst⟩
  rcases B with ⟨s',t',e',l,q,hl,hq,hqlen,hqfirst⟩
  change s = u at hs
  change t = v at ht
  change s' = u at hs'
  change t' = v at ht'
  change e ≠ e' at he
  subst u
  subst v
  subst s'
  subst t'
  refine ⟨k,l,p,q,hk,hl,hp,hq,hlen,hqlen,?_⟩
  simpa only [hfirst,hqfirst] using he

theorem two_distinct_exits : TwoExitProperty := by
  intro u v hne hnadj hcommon
  obtain ⟨hs,ht⟩ := first_checked u v hne
  obtain ⟨hs',ht',he⟩ := exits_checked u v hne hnadj hcommon
  exact two_path_certs (pathAt (firstIndex u v)) (pathAt (secondIndex u v))
    u v hs ht hs' ht' he

structure CycleCert where
  base : V
  length : ℕ
  walk : G.Walk base base
  cycle : walk.IsCycle
  len : walk.length = length

def cc0 : CycleCert := by
  refine ⟨0,9,(Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) Walk.nil))))))))),?_,rfl⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · apply Walk.IsPath.mk'
    decide
  · decide

def cc1 : CycleCert := by
  refine ⟨0,11,(Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) Walk.nil))))))))))),?_,rfl⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · apply Walk.IsPath.mk'
    decide
  · decide

def cc2 : CycleCert := by
  refine ⟨0,11,(Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) Walk.nil))))))))))),?_,rfl⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · apply Walk.IsPath.mk'
    decide
  · decide

def cc3 : CycleCert := by
  refine ⟨0,11,(Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) Walk.nil))))))))))),?_,rfl⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · apply Walk.IsPath.mk'
    decide
  · decide

def cc4 : CycleCert := by
  refine ⟨0,6,(Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) Walk.nil)))))),?_,rfl⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · apply Walk.IsPath.mk'
    decide
  · decide

def cc5 : CycleCert := by
  refine ⟨0,14,(Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) Walk.nil)))))))))))))),?_,rfl⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · apply Walk.IsPath.mk'
    decide
  · decide

def cc6 : CycleCert := by
  refine ⟨0,10,(Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) Walk.nil)))))))))),?_,rfl⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · apply Walk.IsPath.mk'
    decide
  · decide

def cc7 : CycleCert := by
  refine ⟨0,7,(Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) Walk.nil))))))),?_,rfl⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · apply Walk.IsPath.mk'
    decide
  · decide

def cc8 : CycleCert := by
  refine ⟨0,12,(Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) Walk.nil)))))))))))),?_,rfl⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · apply Walk.IsPath.mk'
    decide
  · decide

def cc9 : CycleCert := by
  refine ⟨0,7,(Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) Walk.nil))))))),?_,rfl⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · apply Walk.IsPath.mk'
    decide
  · decide

def cc10 : CycleCert := by
  refine ⟨0,10,(Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 4 from by decide) (Walk.cons (show G.Adj 4 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) Walk.nil)))))))))),?_,rfl⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · apply Walk.IsPath.mk'
    decide
  · decide

def cc11 : CycleCert := by
  refine ⟨0,6,(Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) Walk.nil)))))),?_,rfl⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · apply Walk.IsPath.mk'
    decide
  · decide

def cc12 : CycleCert := by
  refine ⟨0,10,(Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 10 from by decide) (Walk.cons (show G.Adj 10 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) Walk.nil)))))))))),?_,rfl⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · apply Walk.IsPath.mk'
    decide
  · decide

def cc13 : CycleCert := by
  refine ⟨0,7,(Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) Walk.nil))))))),?_,rfl⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · apply Walk.IsPath.mk'
    decide
  · decide

def cc14 : CycleCert := by
  refine ⟨0,9,(Walk.cons (show G.Adj 0 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 0 from by decide) Walk.nil))))))))),?_,rfl⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · apply Walk.IsPath.mk'
    decide
  · decide

def cc15 : CycleCert := by
  refine ⟨0,10,(Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) Walk.nil)))))))))),?_,rfl⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · apply Walk.IsPath.mk'
    decide
  · decide

def cc16 : CycleCert := by
  refine ⟨0,14,(Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) Walk.nil)))))))))))))),?_,rfl⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · apply Walk.IsPath.mk'
    decide
  · decide

def cc17 : CycleCert := by
  refine ⟨0,6,(Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 9 from by decide) (Walk.cons (show G.Adj 9 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) Walk.nil)))))),?_,rfl⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · apply Walk.IsPath.mk'
    decide
  · decide

def cc18 : CycleCert := by
  refine ⟨0,7,(Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) Walk.nil))))))),?_,rfl⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · apply Walk.IsPath.mk'
    decide
  · decide

def cc19 : CycleCert := by
  refine ⟨0,9,(Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) (Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) Walk.nil))))))))),?_,rfl⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · apply Walk.IsPath.mk'
    decide
  · decide

def cc20 : CycleCert := by
  refine ⟨0,11,(Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) Walk.nil))))))))))),?_,rfl⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · apply Walk.IsPath.mk'
    decide
  · decide

def cc21 : CycleCert := by
  refine ⟨0,11,(Walk.cons (show G.Adj 0 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) (Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 11 from by decide) (Walk.cons (show G.Adj 11 0 from by decide) Walk.nil))))))))))),?_,rfl⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · apply Walk.IsPath.mk'
    decide
  · decide

def cc22 : CycleCert := by
  refine ⟨1,6,(Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) Walk.nil)))))),?_,rfl⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · apply Walk.IsPath.mk'
    decide
  · decide

def cc23 : CycleCert := by
  refine ⟨1,10,(Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 8 from by decide) (Walk.cons (show G.Adj 8 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) Walk.nil)))))))))),?_,rfl⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · apply Walk.IsPath.mk'
    decide
  · decide

def cc24 : CycleCert := by
  refine ⟨1,7,(Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) Walk.nil))))))),?_,rfl⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · apply Walk.IsPath.mk'
    decide
  · decide

def cc25 : CycleCert := by
  refine ⟨1,11,(Walk.cons (show G.Adj 1 4 from by decide) (Walk.cons (show G.Adj 4 2 from by decide) (Walk.cons (show G.Adj 2 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) (Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 1 from by decide) Walk.nil))))))))))),?_,rfl⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · apply Walk.IsPath.mk'
    decide
  · decide

def cc26 : CycleCert := by
  refine ⟨1,7,(Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) Walk.nil))))))),?_,rfl⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · apply Walk.IsPath.mk'
    decide
  · decide

def cc27 : CycleCert := by
  refine ⟨1,6,(Walk.cons (show G.Adj 1 7 from by decide) (Walk.cons (show G.Adj 7 3 from by decide) (Walk.cons (show G.Adj 3 12 from by decide) (Walk.cons (show G.Adj 12 5 from by decide) (Walk.cons (show G.Adj 5 10 from by decide) (Walk.cons (show G.Adj 10 1 from by decide) Walk.nil)))))),?_,rfl⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · apply Walk.IsPath.mk'
    decide
  · decide

def cc28 : CycleCert := by
  refine ⟨3,9,(Walk.cons (show G.Adj 3 7 from by decide) (Walk.cons (show G.Adj 7 8 from by decide) (Walk.cons (show G.Adj 8 13 from by decide) (Walk.cons (show G.Adj 13 9 from by decide) (Walk.cons (show G.Adj 9 6 from by decide) (Walk.cons (show G.Adj 6 10 from by decide) (Walk.cons (show G.Adj 10 5 from by decide) (Walk.cons (show G.Adj 5 12 from by decide) (Walk.cons (show G.Adj 12 3 from by decide) Walk.nil))))))))),?_,rfl⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · apply Walk.IsPath.mk'
    decide
  · decide

def cycleData : Array CycleCert := #[
  cc0, cc1, cc2, cc3, cc4, cc5, cc6, cc7, cc8, cc9, cc10, cc11, cc12, cc13, cc14, cc15, cc16, cc17, cc18, cc19, cc20, cc21, cc22, cc23, cc24, cc25, cc26, cc27, cc28
]
def cycleAt (i : Fin 29) : CycleCert :=
  cycleData[i.val]'(by simp [cycleData])

def fermatIndex (x a b : V) : Fin 29 :=
  match x.val,a.val,b.val with
  | 0,3,6 => 14
  | 0,3,11 => 0
  | 0,6,3 => 14
  | 0,6,11 => 19
  | 0,11,3 => 0
  | 0,11,6 => 19
  | 1,4,7 => 14
  | 1,4,10 => 0
  | 1,7,4 => 14
  | 1,7,10 => 19
  | 1,10,4 => 0
  | 1,10,7 => 19
  | 2,4,11 => 0
  | 2,4,13 => 14
  | 2,11,4 => 0
  | 2,11,13 => 19
  | 2,13,4 => 14
  | 2,13,11 => 19
  | 3,0,7 => 14
  | 3,0,12 => 0
  | 3,7,0 => 14
  | 3,7,12 => 28
  | 3,12,0 => 0
  | 3,12,7 => 28
  | 4,1,2 => 0
  | 4,2,1 => 0
  | 5,10,12 => 0
  | 5,12,10 => 0
  | 6,0,9 => 14
  | 6,0,10 => 19
  | 6,9,0 => 14
  | 6,9,10 => 28
  | 6,10,0 => 19
  | 6,10,9 => 28
  | 7,1,3 => 14
  | 7,1,8 => 19
  | 7,3,1 => 14
  | 7,3,8 => 28
  | 7,8,1 => 19
  | 7,8,3 => 28
  | 8,7,13 => 19
  | 8,13,7 => 19
  | 9,6,13 => 14
  | 9,13,6 => 14
  | 10,1,5 => 0
  | 10,1,6 => 19
  | 10,5,1 => 0
  | 10,5,6 => 28
  | 10,6,1 => 19
  | 10,6,5 => 28
  | 11,0,2 => 0
  | 11,2,0 => 0
  | 12,3,5 => 0
  | 12,5,3 => 0
  | 13,2,8 => 19
  | 13,2,9 => 14
  | 13,8,2 => 19
  | 13,8,9 => 28
  | 13,9,2 => 14
  | 13,9,8 => 28
  | _,_,_ => 0

def plusTwoIndex (x a b : V) : Fin 29 :=
  match x.val,a.val,b.val with
  | 0,3,6 => 4
  | 0,3,11 => 6
  | 0,6,3 => 4
  | 0,6,11 => 15
  | 0,11,3 => 6
  | 0,11,6 => 15
  | 1,4,7 => 15
  | 1,4,10 => 10
  | 1,7,4 => 15
  | 1,7,10 => 11
  | 1,10,4 => 10
  | 1,10,7 => 11
  | 2,4,11 => 15
  | 2,4,13 => 10
  | 2,11,4 => 15
  | 2,11,13 => 6
  | 2,13,4 => 10
  | 2,13,11 => 6
  | 3,0,7 => 10
  | 3,0,12 => 4
  | 3,7,0 => 10
  | 3,7,12 => 23
  | 3,12,0 => 4
  | 3,12,7 => 23
  | 4,1,2 => 10
  | 4,2,1 => 10
  | 5,10,12 => 4
  | 5,12,10 => 4
  | 6,0,9 => 15
  | 6,0,10 => 4
  | 6,9,0 => 15
  | 6,9,10 => 6
  | 6,10,0 => 4
  | 6,10,9 => 6
  | 7,1,3 => 11
  | 7,1,8 => 15
  | 7,3,1 => 11
  | 7,3,8 => 10
  | 7,8,1 => 15
  | 7,8,3 => 10
  | 8,7,13 => 10
  | 8,13,7 => 10
  | 9,6,13 => 6
  | 9,13,6 => 6
  | 10,1,5 => 23
  | 10,1,6 => 10
  | 10,5,1 => 23
  | 10,5,6 => 4
  | 10,6,1 => 10
  | 10,6,5 => 4
  | 11,0,2 => 6
  | 11,2,0 => 6
  | 12,3,5 => 4
  | 12,5,3 => 4
  | 13,2,8 => 10
  | 13,2,9 => 6
  | 13,8,2 => 10
  | 13,8,9 => 15
  | 13,9,2 => 6
  | 13,9,8 => 15
  | _,_,_ => 0

theorem fermat_checked : ∀ x a b : V, a ≠ b → G.Adj x a → G.Adj x b →
    (cycleAt (fermatIndex x a b)).length = 9 ∧
    s(x,a) ∈ (cycleAt (fermatIndex x a b)).walk.edges ∧
    s(x,b) ∈ (cycleAt (fermatIndex x a b)).walk.edges := by decide

#print axioms fermat_checked

theorem plus_two_checked : ∀ x a b : V, a ≠ b → G.Adj x a → G.Adj x b →
    ((cycleAt (plusTwoIndex x a b)).length = 6 ∨
      (cycleAt (plusTwoIndex x a b)).length = 10) ∧
    s(x,a) ∈ (cycleAt (plusTwoIndex x a b)).walk.edges ∧
    s(x,b) ∈ (cycleAt (plusTwoIndex x a b)).walk.edges := by decide

#print axioms plus_two_checked

def P3FermatProperty : Prop :=
  ∀ x a b : V, a ≠ b → G.Adj x a → G.Adj x b →
    ∃ (r : V) (c : G.Walk r r), c.IsCycle ∧ c.length = 9 ∧
      s(x,a) ∈ c.edges ∧ s(x,b) ∈ c.edges

def P3PlusTwoProperty : Prop :=
  ∀ x a b : V, a ≠ b → G.Adj x a → G.Adj x b →
    ∃ (r : V) (c : G.Walk r r), c.IsCycle ∧ (c.length = 6 ∨ c.length = 10) ∧
      s(x,a) ∈ c.edges ∧ s(x,b) ∈ c.edges

theorem p3_fermat : P3FermatProperty := by
  intro x a b hne hxa hxb
  obtain ⟨hlen,ha,hb⟩ := fermat_checked x a b hne hxa hxb
  refine ⟨_,(cycleAt (fermatIndex x a b)).walk,
    (cycleAt (fermatIndex x a b)).cycle,?_,ha,hb⟩
  exact (cycleAt (fermatIndex x a b)).len.trans hlen

theorem p3_plus_two : P3PlusTwoProperty := by
  intro x a b hne hxa hxb
  obtain ⟨hlen,ha,hb⟩ := plus_two_checked x a b hne hxa hxb
  refine ⟨_,(cycleAt (plusTwoIndex x a b)).walk,
    (cycleAt (plusTwoIndex x a b)).cycle,?_,ha,hb⟩
  rcases hlen with hlen | hlen
  · exact Or.inl ((cycleAt (plusTwoIndex x a b)).len.trans hlen)
  · exact Or.inr ((cycleAt (plusTwoIndex x a b)).len.trans hlen)

def neighbors (v : V) : List V :=
  match v.val with
  | 0 => [3, 6, 11]
  | 1 => [4, 7, 10]
  | 2 => [4, 11, 13]
  | 3 => [0, 7, 12]
  | 4 => [1, 2]
  | 5 => [10, 12]
  | 6 => [0, 9, 10]
  | 7 => [1, 3, 8]
  | 8 => [7, 13]
  | 9 => [6, 13]
  | 10 => [1, 5, 6]
  | 11 => [0, 2]
  | 12 => [3, 5]
  | _ => [2, 8, 9]

theorem neighbors_correct : ∀ u v : V, v ∈ neighbors u ↔ G.Adj u v := by decide

def simpleReach : ℕ → V → V → List V → Bool
  | 0, u, v, seen => decide (u = v ∧ u ∉ seen)
  | n+1, u, v, seen =>
      if u ∈ seen then false
      else (neighbors u).any fun w => simpleReach n w v (u::seen)

/-- Every genuine simple walk avoiding the already-used vertices is
accepted by the explicit adjacency-list search. -/
theorem simpleReach_of_path {u v : V} (p : G.Walk u v) :
    p.IsPath → ∀ (seen : List V), (∀ x ∈ p.support, x ∉ seen) →
      simpleReach p.length u v seen = true := by
  induction p with
  | @nil z =>
    intro _ seen havoid
    have hnot : z ∉ seen := havoid z (by simp)
    simp [simpleReach,hnot]
  | @cons a b c hab q ih =>
    intro hp seen havoid
    have hanot : a ∉ seen := havoid a (by simp)
    change (if a ∈ seen then false else
      (neighbors a).any fun w => simpleReach q.length w c (a::seen)) = true
    rw [ite_eq_right hanot]
    apply List.any_eq_true.mpr
    refine ⟨b, (neighbors_correct a b).mpr hab, ?_⟩
    apply ih (Walk.IsPath.of_cons hp) (a::seen)
    intro x hx
    simp only [List.mem_cons, not_or]
    constructor
    · intro hxa
      subst x
      exact ((Walk.cons_isPath_iff hab q).mp hp).2 hx
    · exact havoid x (by simp [hx])

def cycleSearch (n : ℕ) (u : V) : Bool :=
  (neighbors u).any fun v => simpleReach (n-1) v u []

theorem no_cycle_of_search (n : ℕ) (hcheck : ∀ v : V, cycleSearch n v = false)
    (v : V) (p : G.Walk v v) (hlen : p.length = n) : ¬p.IsCycle := by
  intro hc
  cases p with
  | nil => exact hc.ne_nil rfl
  | cons hab q =>
    have hqpath : q.IsPath := Walk.IsPath.mk' (by simpa using hc.support_nodup)
    have hq := simpleReach_of_path q hqpath [] (by simp)
    have hqn : q.length = n-1 := by simp only [Walk.length_cons] at hlen; omega
    rw [hqn] at hq
    have hcsearch : cycleSearch n v = true := by
      unfold cycleSearch
      apply List.any_eq_true.mpr
      exact ⟨_, (neighbors_correct _ _).mpr hab, hq⟩
    have := hcheck v
    rw [hcsearch] at this
    contradiction

theorem no_four : ∀ (v : V) (p : G.Walk v v), p.length = 4 → ¬p.IsCycle :=
  no_cycle_of_search 4 (by decide)

#print axioms no_four

theorem no_eight : ∀ (v : V) (p : G.Walk v v), p.length = 8 → ¬p.IsCycle :=
  no_cycle_of_search 8 (by decide)

#print axioms no_eight

/-- Exact original power predicate: the graph order bounds all simple
cycle lengths, so there are no unexamined larger exponents. -/
theorem no_power : ¬HasPower G := by
  rintro ⟨k,v,p,hk,hc,hlen⟩
  have hbound : p.length ≤ 14 := by simpa using hc.length_le_natCard
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

theorem triangle_free : ¬∃ a b c : V, G.Adj a b ∧ G.Adj b c ∧ G.Adj c a := by decide

theorem degrees : ∀ v : V, 2 ≤ G.degree v ∧ G.degree v ≤ 3 := by decide

theorem not_near : ¬Near G := by
  unfold Near
  decide

/-- The combined, unconditional counterexample to the proposed path-only
closure implication, including every tested structural path consequence. -/
theorem counterexample :
    2 ≤ Fintype.card V ∧
    (∀ u v : V, u ≠ v → DyadicPath G u v) ∧
    TwoExitProperty ∧ P3FermatProperty ∧ P3PlusTwoProperty ∧
    (∀ v : V, 2 ≤ G.degree v ∧ G.degree v ≤ 3) ∧
    (¬∃ a b c : V, G.Adj a b ∧ G.Adj b c ∧ G.Adj c a) ∧
    ¬HasPower G ∧ ¬Near G := by
  exact ⟨by decide,all_pairs_dyadic,two_distinct_exits,p3_fermat,p3_plus_two,
    degrees,triangle_free,no_power,not_near⟩

#print axioms all_pairs_dyadic
#print axioms two_distinct_exits
#print axioms p3_fermat
#print axioms p3_plus_two
#print axioms no_four
#print axioms no_eight
#print axioms no_power
#print axioms counterexample
end E64AllPairsObstruction
