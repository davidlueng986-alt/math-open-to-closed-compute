import Witness

namespace Hadamard2396.Diagonal

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Every Boolean check on the first n indices follows from the range computation. -/
private theorem checked {n : Nat} {test : Nat → Bool}
    (h : (List.range n).all test = true) (i : Fin n) : test i.val = true :=
  List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)

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

theorem exact57 (i : Fin 57) :
    projectedPaf a57 b57 57 i.val = (if i.val = 0 then 2354 else -42) :=
  of_decide_eq_true (checked (test := exact57At) (by decide +kernel) i)

def a63 : Array Int := #[1, -1, 3, 11, -1, -3, 1, -7, 3, -7, 1, 3, 11, 1, -1, 11, -1, -3, -7, 1, -3, -11, -1, 3, 1, -1, -3, -1, -7, 3, -1, 1, 3, 1, 1, -1, -7, -1, -3, -1, 1, -3, -7, -1, 3, -1, -1, -3, 11, -7, 3, 11, 1, 3, -1, 1, -1, -1, -1, -3, 11, 1, -3]
def b63 : Array Int := #[-17, 1, -1, 1, 1, 3, -5, 1, -1, 7, -1, -1, 1, -1, -1, 1, 1, 3, 7, -1, 3, 5, 1, -1, -5, 1, 3, -5, 1, -1, -5, -1, -1, -5, -1, -1, 7, 1, 3, -5, -1, 3, 13, 1, -1, -5, 1, 3, 1, 1, -1, 1, -1, -1, -5, -1, -1, -5, 1, 3, 1, -1, 3]

private def margins63At (i : Nat) : Bool := decide
  (compress a 63 i = a63.getD i 0 ∧ compress b 63 i = b63.getD i 0)

theorem margins63 (i : Fin 63) :
    compress a 63 i.val = a63.getD i.val 0 ∧ compress b 63 i.val = b63.getD i.val 0 :=
  of_decide_eq_true (checked (test := margins63At) (by decide +kernel) i)

private def exact63At (i : Nat) : Bool := decide
  (projectedPaf a63 b63 63 i = (if i = 0 then 2358 else -38))

theorem exact63 (i : Fin 63) :
    projectedPaf a63 b63 63 i.val = (if i.val = 0 then 2358 else -38) :=
  of_decide_eq_true (checked (test := exact63At) (by decide +kernel) i)

def a133 : Array Int := #[-5, 5, 1, -1, 3, 3, -3, 1, -3, 1, -1, 3, -3, 3, -5, -3, 1, 1, -1, 5, -3, -5, -3, 1, 1, 3, 3, 3, 1, -3, 1, -1, -1, -3, 3, 1, 5, 1, 5, 3, -3, 3, 1, 5, 1, 1, -1, 3, 3, 1, -3, 1, -1, -1, 3, -3, -5, -9, 1, -1, -1, 3, -3, 1, 5, 1, 1, -1, 3, 3, -5, -3, 1, 1, 3, -3, 5, 1, -3, 1, 1, 3, 3, -3, -5, 5, 1, 1, -1, -3, 3, -5, 5, 1, -1, -9, 3, 3, -5, 5, 1, 1, 3, -3, -3, -5, 5, 1, -1, -1, -3, -3, 1, -3, -9, 1, -1, -3, -3, 1, 5, 1, -1, 3, -3, -3, -5, -3, 1, -1, 3, 3, 3]
def b133 : Array Int := #[1, -5, 3, 1, 1, 3, -1, 3, 5, -3, 1, 1, -3, 1, -3, 5, -3, -1, -1, -3, -1, -3, 5, -3, -1, 1, 3, 1, 3, 5, -3, 1, -1, -3, 1, 3, -5, 3, -3, 1, -3, 1, 3, -5, -3, -1, -1, 3, 1, 3, 5, 3, 1, -1, 3, -1, -3, 3, -3, 1, -1, 3, -1, 3, -5, 3, -1, -1, 3, 1, -3, 5, 3, -1, 1, -3, -3, 3, 5, 3, -1, 1, 3, -1, -3, -5, 3, -1, -1, -3, 1, -3, -5, -3, 1, 3, 3, 1, -3, -5, -3, -1, 1, -3, -1, -3, -5, 3, 1, -1, -3, -1, 3, 5, 3, -1, -1, -3, -1, 3, -5, -3, 1, 1, -3, -1, -3, 5, 3, 1, 1, 3, 1]

private def margins133At (i : Nat) : Bool := decide
  (compress a 133 i = a133.getD i 0 ∧ compress b 133 i = b133.getD i 0)

theorem margins133 (i : Fin 133) :
    compress a 133 i.val = a133.getD i.val 0 ∧ compress b 133 i.val = b133.getD i.val 0 :=
  of_decide_eq_true (checked (test := margins133At) (by decide +kernel) i)

private def exact133At (i : Nat) : Bool := decide
  (projectedPaf a133 b133 133 i = (if i = 0 then 2378 else -18))

theorem exact133 (i : Fin 133) :
    projectedPaf a133 b133 133 i.val = (if i.val = 0 then 2378 else -18) :=
  of_decide_eq_true (checked (test := exact133At) (by decide +kernel) i)

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
