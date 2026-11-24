import Witness

namespace Hadamard2396.Diagonal

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Every Boolean check on the first n indices follows from the range computation. -/
theorem checked {n : Nat} {test : Nat → Bool}
    (h : (List.range n).all test = true) (i : Fin n) : test i.val = true :=
  List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)

private abbrev Block (test : Nat → Bool) (start size : Nat) :=
  ∀ i : Fin size, test (start+i.val) = true

private theorem joinBlocks {t : Nat → Bool} {start left right : Nat}
    (a : Block t start left) (b : Block t (start+left) right) :
    Block t start (left+right) := by
  intro i
  by_cases h : i.val < left
  · exact a ⟨i.val,h⟩
  · have w := b ⟨i.val-left, by have := i.isLt; omega⟩
    change t (start+left+(i.val-left)) = true at w
    rwa [show start+left+(i.val-left) = start+i.val by omega] at w

def a : Nat := 0xbbeb64a35ef19e8620e7f4237b1fe5349060b3f5f372ee25605ffa708dc0b86980cbd537cf032363abf52d865289f2c75264fe08fe60b3cb6a290c748a25682b5bf9af46fd185ccb972f86f73a0cc6a22157ff53a5753c9498d214a6d4d7185a63340e141a8fbe6962eb2f72b5e30d401a357b5b4374ad8d4dd402119e872acb8366c9f8ab4d4f4139ca870c5781b861b2cb6b72020
def b : Nat := 0x1073dc745c7e380f494728196589955a9746a1815df0d1c9d174850fa59048fa2911c688699f2b5c6e10d4785e75ba7f0d9c8eced98b7c3e6405daffb113b02d6dec37e2d09d73433a014735c02671949ef12e00199d375e6677d922a6d007a9e985a5a59d5d575b2deb7525545849e79b088e811e1d7c5d396637fba11537e34268970bd11859f81781f3821ebda555fa5f76a9785e

private def fixedAt (i : Nat) : Bool := decide
  (signWord a i = signWord a (463*i%1197) ∧ signWord b i = signWord b (463*i%1197))

theorem multiplier (i : Fin 1197) :
    signWord a i.val = signWord a (463*i.val%1197) ∧
    signWord b i.val = signWord b (463*i.val%1197) :=
  of_decide_eq_true (checked (test := fixedAt) (by decide +kernel) i)

theorem normalized :
    sumAt 1197 (fun i => sign (signWord a i)) = 1 ∧
    sumAt 1197 (fun i => sign (signWord b i)) = 1 := by decide +kernel

def a57 : Array Int := #[-11, 1, -1, -5, 1, 1, 9, 1, -1, 9, -3, 1, -5, -3, -1, -5, 1, 1, -5, -3, 1, -5, -3, 1, 9, 1, 1, -5, 1, -1, 9, -3, -1, -5, -3, 1, 9, -3, -3, 9, -3, -1, 9, 1, 1, 9, -3, 1, -5, 1, -1, -5, -3, -1, 9, 1, -1]
def b57 : Array Int := #[19, -1, 1, 1, -1, 3, -5, -1, 1, -5, 1, 3, 1, 1, 1, 1, -1, 3, 1, 3, 3, 1, 1, 3, -5, -1, 3, 1, -1, 1, -5, 1, 1, 1, 1, 3, -5, 1, -21, -5, 1, 1, -5, -1, 3, -5, 1, 3, 1, -1, 1, 1, 1, 1, -5, -1, 1]

private def margins57At (i : Nat) : Bool := decide
  (compress a 57 i = a57.getD i 0 ∧ compress b 57 i = b57.getD i 0)

theorem margins57 (i : Fin 57) :
    compress a 57 i.val = a57.getD i.val 0 ∧ compress b 57 i.val = b57.getD i.val 0 :=
  of_decide_eq_true (checked (test := margins57At) (by decide +kernel) i)

private def exact57At (i : Nat) : Bool := decide
  (projectedPaf a57 b57 57 i = (if i = 0 then 2354 else -42))

private theorem exact57_0 : Block exact57At 0 5 := by decide +kernel
private theorem exact57_5 : Block exact57At 5 5 := by decide +kernel
private theorem exact57_10 : Block exact57At 10 5 := by decide +kernel
private theorem exact57_15 : Block exact57At 15 5 := by decide +kernel
private theorem exact57_20 : Block exact57At 20 5 := by decide +kernel
private theorem exact57_25 : Block exact57At 25 5 := by decide +kernel
private theorem exact57_30 : Block exact57At 30 5 := by decide +kernel
private theorem exact57_35 : Block exact57At 35 5 := by decide +kernel
private theorem exact57_40 : Block exact57At 40 5 := by decide +kernel
private theorem exact57_45 : Block exact57At 45 5 := by decide +kernel
private theorem exact57_50 : Block exact57At 50 5 := by decide +kernel
private theorem exact57_55 : Block exact57At 55 2 := by decide +kernel
theorem exact57 (i : Fin 57) : projectedPaf a57 b57 57 i.val = (if i.val = 0 then 2354 else -42) := by
  have h : Block exact57At 0 57 := (joinBlocks (joinBlocks (joinBlocks (joinBlocks exact57_0 exact57_5) (joinBlocks exact57_10 exact57_15)) (joinBlocks (joinBlocks exact57_20 exact57_25) (joinBlocks exact57_30 exact57_35))) (joinBlocks (joinBlocks exact57_40 exact57_45) (joinBlocks exact57_50 exact57_55)))
  have hi := h i
  rw [Nat.zero_add] at hi
  exact of_decide_eq_true hi

def a63 : Array Int := #[1, -1, 3, 11, -1, -3, 1, -7, 3, -7, 1, 3, 11, 1, -1, 11, -1, -3, -7, 1, -3, -11, -1, 3, 1, -1, -3, -1, -7, 3, -1, 1, 3, 1, 1, -1, -7, -1, -3, -1, 1, -3, -7, -1, 3, -1, -1, -3, 11, -7, 3, 11, 1, 3, -1, 1, -1, -1, -1, -3, 11, 1, -3]
def b63 : Array Int := #[-17, 1, -1, 1, 1, 3, -5, 1, -1, 7, -1, -1, 1, -1, -1, 1, 1, 3, 7, -1, 3, 5, 1, -1, -5, 1, 3, -5, 1, -1, -5, -1, -1, -5, -1, -1, 7, 1, 3, -5, -1, 3, 13, 1, -1, -5, 1, 3, 1, 1, -1, 1, -1, -1, -5, -1, -1, -5, 1, 3, 1, -1, 3]

private def margins63At (i : Nat) : Bool := decide
  (compress a 63 i = a63.getD i 0 ∧ compress b 63 i = b63.getD i 0)

theorem margins63 (i : Fin 63) :
    compress a 63 i.val = a63.getD i.val 0 ∧ compress b 63 i.val = b63.getD i.val 0 :=
  of_decide_eq_true (checked (test := margins63At) (by decide +kernel) i)

private def exact63At (i : Nat) : Bool := decide
  (projectedPaf a63 b63 63 i = (if i = 0 then 2358 else -38))

private theorem exact63_0 : Block exact63At 0 5 := by decide +kernel
private theorem exact63_5 : Block exact63At 5 5 := by decide +kernel
private theorem exact63_10 : Block exact63At 10 5 := by decide +kernel
private theorem exact63_15 : Block exact63At 15 5 := by decide +kernel
private theorem exact63_20 : Block exact63At 20 5 := by decide +kernel
private theorem exact63_25 : Block exact63At 25 5 := by decide +kernel
private theorem exact63_30 : Block exact63At 30 5 := by decide +kernel
private theorem exact63_35 : Block exact63At 35 5 := by decide +kernel
private theorem exact63_40 : Block exact63At 40 5 := by decide +kernel
private theorem exact63_45 : Block exact63At 45 5 := by decide +kernel
private theorem exact63_50 : Block exact63At 50 5 := by decide +kernel
private theorem exact63_55 : Block exact63At 55 5 := by decide +kernel
private theorem exact63_60 : Block exact63At 60 3 := by decide +kernel
theorem exact63 (i : Fin 63) : projectedPaf a63 b63 63 i.val = (if i.val = 0 then 2358 else -38) := by
  have h : Block exact63At 0 63 := (joinBlocks (joinBlocks (joinBlocks (joinBlocks exact63_0 exact63_5) (joinBlocks exact63_10 exact63_15)) (joinBlocks (joinBlocks exact63_20 exact63_25) (joinBlocks exact63_30 exact63_35))) (joinBlocks (joinBlocks (joinBlocks exact63_40 exact63_45) (joinBlocks exact63_50 exact63_55)) exact63_60))
  have hi := h i
  rw [Nat.zero_add] at hi
  exact of_decide_eq_true hi

def a133 : Array Int := #[-5, 5, 1, -1, 3, 3, -3, 1, -3, 1, -1, 3, -3, 3, -5, -3, 1, 1, -1, 5, -3, -5, -3, 1, 1, 3, 3, 3, 1, -3, 1, -1, -1, -3, 3, 1, 5, 1, 5, 3, -3, 3, 1, 5, 1, 1, -1, 3, 3, 1, -3, 1, -1, -1, 3, -3, -5, -9, 1, -1, -1, 3, -3, 1, 5, 1, 1, -1, 3, 3, -5, -3, 1, 1, 3, -3, 5, 1, -3, 1, 1, 3, 3, -3, -5, 5, 1, 1, -1, -3, 3, -5, 5, 1, -1, -9, 3, 3, -5, 5, 1, 1, 3, -3, -3, -5, 5, 1, -1, -1, -3, -3, 1, -3, -9, 1, -1, -3, -3, 1, 5, 1, -1, 3, -3, -3, -5, -3, 1, -1, 3, 3, 3]
def b133 : Array Int := #[1, -5, 3, 1, 1, 3, -1, 3, 5, -3, 1, 1, -3, 1, -3, 5, -3, -1, -1, -3, -1, -3, 5, -3, -1, 1, 3, 1, 3, 5, -3, 1, -1, -3, 1, 3, -5, 3, -3, 1, -3, 1, 3, -5, -3, -1, -1, 3, 1, 3, 5, 3, 1, -1, 3, -1, -3, 3, -3, 1, -1, 3, -1, 3, -5, 3, -1, -1, 3, 1, -3, 5, 3, -1, 1, -3, -3, 3, 5, 3, -1, 1, 3, -1, -3, -5, 3, -1, -1, -3, 1, -3, -5, -3, 1, 3, 3, 1, -3, -5, -3, -1, 1, -3, -1, -3, -5, 3, 1, -1, -3, -1, 3, 5, 3, -1, -1, -3, -1, 3, -5, -3, 1, 1, -3, -1, -3, 5, 3, 1, 1, 3, 1]

private def margins133At (i : Nat) : Bool := decide
  (compress a 133 i = a133.getD i 0 ∧ compress b 133 i = b133.getD i 0)

theorem margins133 (i : Fin 133) :
    compress a 133 i.val = a133.getD i.val 0 ∧ compress b 133 i.val = b133.getD i.val 0 :=
  of_decide_eq_true (checked (test := margins133At) (by decide +kernel) i)

private def exact133At (i : Nat) : Bool := decide
  (projectedPaf a133 b133 133 i = (if i = 0 then 2378 else -18))

private theorem exact133_0 : Block exact133At 0 5 := by decide +kernel
private theorem exact133_5 : Block exact133At 5 5 := by decide +kernel
private theorem exact133_10 : Block exact133At 10 5 := by decide +kernel
private theorem exact133_15 : Block exact133At 15 5 := by decide +kernel
private theorem exact133_20 : Block exact133At 20 5 := by decide +kernel
private theorem exact133_25 : Block exact133At 25 5 := by decide +kernel
private theorem exact133_30 : Block exact133At 30 5 := by decide +kernel
private theorem exact133_35 : Block exact133At 35 5 := by decide +kernel
private theorem exact133_40 : Block exact133At 40 5 := by decide +kernel
private theorem exact133_45 : Block exact133At 45 5 := by decide +kernel
private theorem exact133_50 : Block exact133At 50 5 := by decide +kernel
private theorem exact133_55 : Block exact133At 55 5 := by decide +kernel
private theorem exact133_60 : Block exact133At 60 5 := by decide +kernel
private theorem exact133_65 : Block exact133At 65 5 := by decide +kernel
private theorem exact133_70 : Block exact133At 70 5 := by decide +kernel
private theorem exact133_75 : Block exact133At 75 5 := by decide +kernel
private theorem exact133_80 : Block exact133At 80 5 := by decide +kernel
private theorem exact133_85 : Block exact133At 85 5 := by decide +kernel
private theorem exact133_90 : Block exact133At 90 5 := by decide +kernel
private theorem exact133_95 : Block exact133At 95 5 := by decide +kernel
private theorem exact133_100 : Block exact133At 100 5 := by decide +kernel
private theorem exact133_105 : Block exact133At 105 5 := by decide +kernel
private theorem exact133_110 : Block exact133At 110 5 := by decide +kernel
private theorem exact133_115 : Block exact133At 115 5 := by decide +kernel
private theorem exact133_120 : Block exact133At 120 5 := by decide +kernel
private theorem exact133_125 : Block exact133At 125 5 := by decide +kernel
private theorem exact133_130 : Block exact133At 130 3 := by decide +kernel
theorem exact133 (i : Fin 133) : projectedPaf a133 b133 133 i.val = (if i.val = 0 then 2378 else -18) := by
  have h : Block exact133At 0 133 := (joinBlocks (joinBlocks (joinBlocks (joinBlocks (joinBlocks exact133_0 exact133_5) (joinBlocks exact133_10 exact133_15)) (joinBlocks (joinBlocks exact133_20 exact133_25) (joinBlocks exact133_30 exact133_35))) (joinBlocks (joinBlocks (joinBlocks exact133_40 exact133_45) (joinBlocks exact133_50 exact133_55)) (joinBlocks (joinBlocks exact133_60 exact133_65) (joinBlocks exact133_70 exact133_75)))) (joinBlocks (joinBlocks (joinBlocks (joinBlocks exact133_80 exact133_85) (joinBlocks exact133_90 exact133_95)) (joinBlocks (joinBlocks exact133_100 exact133_105) (joinBlocks exact133_110 exact133_115))) (joinBlocks (joinBlocks exact133_120 exact133_125) exact133_130)))
  have hi := h i
  rw [Nat.zero_add] at hi
  exact of_decide_eq_true hi

def combinedPaf (s : Nat) : Int := paf 1197 (signWord a) s + paf 1197 (signWord b) s

private def s0 : List Nat := [19, 38, 57, 63, 76, 95, 114, 126]
private theorem good0 : s0.all (fun s => decide (combinedPaf s = -2)) = true := by decide +kernel
private def s8 : List Nat := [133, 152, 171, 189, 190, 209, 228, 247]
private theorem good8 : s8.all (fun s => decide (combinedPaf s = -2)) = true := by decide +kernel
private def s16 : List Nat := [252, 266, 285, 304, 315, 323, 342, 361]
private theorem good16 : s16.all (fun s => decide (combinedPaf s = -2)) = true := by decide +kernel
private def s24 : List Nat := [378, 380, 399, 418, 437, 441, 456, 475]
private theorem good24 : s24.all (fun s => decide (combinedPaf s = -2)) = true := by decide +kernel
private def s32 : List Nat := [494, 504, 513, 532, 551, 567, 570, 589]
private theorem good32 : s32.all (fun s => decide (combinedPaf s = -2)) = true := by decide +kernel
private def s40 : List Nat := [608, 627, 630, 646, 665, 684, 693, 703]
private theorem good40 : s40.all (fun s => decide (combinedPaf s = -2)) = true := by decide +kernel
private def s48 : List Nat := [722, 741, 756, 760, 779, 798, 817, 819]
private theorem good48 : s48.all (fun s => decide (combinedPaf s = -2)) = true := by decide +kernel
private def s56 : List Nat := [836, 855, 874, 882, 893, 912, 931, 945]
private theorem good56 : s56.all (fun s => decide (combinedPaf s = -2)) = true := by decide +kernel
private def s64 : List Nat := [950, 969, 988, 1007, 1008, 1026, 1045, 1064]
private theorem good64 : s64.all (fun s => decide (combinedPaf s = -2)) = true := by decide +kernel
private def s72 : List Nat := [1071, 1083, 1102, 1121, 1134, 1140, 1159, 1178]
private theorem good72 : s72.all (fun s => decide (combinedPaf s = -2)) = true := by decide +kernel

private def shifts : List Nat := s0 ++ s8 ++ s16 ++ s24 ++ s32 ++ s40 ++ s48 ++ s56 ++ s64 ++ s72
private def covered (s : Nat) : Bool := decide
  (s ≠ 0 → (19*s%1197 = 0 ∨ 63*s%1197 = 0) → s ∈ shifts)

theorem exact_subgroups (s : Fin 1197) (h₀ : s.val ≠ 0)
    (h : 19*s.val%1197 = 0 ∨ 63*s.val%1197 = 0) : combinedPaf s.val = -2 := by
  have hs : s.val ∈ shifts := of_decide_eq_true (checked (test := covered) (by decide +kernel) s) h₀ h
  have hgood : shifts.all (fun t => decide (combinedPaf t = -2)) = true := by
    simp only [shifts, List.all_append, good0, good8, good16, good24, good32, good40, good48, good56, good64, good72, Bool.and_self]
  exact of_decide_eq_true (List.all_eq_true.mp hgood s.val hs)

theorem shift_one : combinedPaf 1 = -22 := by decide +kernel

#print axioms multiplier
#print axioms normalized
#print axioms margins57
#print axioms exact57
#print axioms margins63
#print axioms exact63
#print axioms margins133
#print axioms exact133
#print axioms exact_subgroups
#print axioms shift_one
end Hadamard2396.Diagonal
