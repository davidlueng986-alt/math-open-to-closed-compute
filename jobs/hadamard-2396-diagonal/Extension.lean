import Diagonal

namespace Hadamard2396.Extension

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Hadamard2396.Diagonal (a57 b57 a63 b63 a133 b133 checked)

def wordA : Nat := 0x1bbc348317bd9968c85b1c688a7dff534d16db3f862702b056155fbe38780b269e0cb9e5b4f8399673af72e02d63dbacfe6e4be43f76ad90b0aafc4fe8a24740b4beca130dcab1dcb054d1c7bb826e1e061f74f37a7333d0458dd1616b0f65954c1342cd259b9b02922ebbe5315824c480c64711b4cb8debd4d353015872fce02a74ee9b1238c07d7b9deff0e1e04ba65414d2f42440
def wordB : Nat := 0x333c761f52b98be9c73577f3949647b342218b7fc2b3c9c1e8e01ed912c9fb3d0403c82b17278427dcdd780f35816f0f069ee6dd0bdc526014a2ff3733a4e56ff4b7a7e49d3a53b72d42658406b9dcd6a9260059d85fdfde778926c65406ace586a527d955d553f9eebd10144e8be15e2a8d431ebd395c420477278908368166883727c1c75bd84788fd863bcfa559704b62c95052

private def fixedAt (i : Nat) : Bool := decide
  (signWord wordA i = signWord wordA (463*i%1197) ∧ signWord wordB i = signWord wordB (463*i%1197))

theorem multiplier (i : Fin 1197) :
    signWord wordA i.val = signWord wordA (463*i.val%1197) ∧
    signWord wordB i.val = signWord wordB (463*i.val%1197) :=
  of_decide_eq_true (checked (test := fixedAt) (by decide +kernel) i)

theorem normalized :
    sumAt 1197 (fun i => sign (signWord wordA i)) = 1 ∧
    sumAt 1197 (fun i => sign (signWord wordB i)) = 1 := by decide +kernel

private def margins57At (i : Nat) : Bool := decide
  (compress wordA 57 i = a57.getD i 0 ∧ compress wordB 57 i = b57.getD i 0)

theorem margins57 (i : Fin 57) :
    compress wordA 57 i.val = a57.getD i.val 0 ∧ compress wordB 57 i.val = b57.getD i.val 0 :=
  of_decide_eq_true (checked (test := margins57At) (by decide +kernel) i)

private def margins63At (i : Nat) : Bool := decide
  (compress wordA 63 i = a63.getD i 0 ∧ compress wordB 63 i = b63.getD i 0)

theorem margins63 (i : Fin 63) :
    compress wordA 63 i.val = a63.getD i.val 0 ∧ compress wordB 63 i.val = b63.getD i.val 0 :=
  of_decide_eq_true (checked (test := margins63At) (by decide +kernel) i)

private def margins133At (i : Nat) : Bool := decide
  (compress wordA 133 i = a133.getD i 0 ∧ compress wordB 133 i = b133.getD i 0)

theorem margins133 (i : Fin 133) :
    compress wordA 133 i.val = a133.getD i.val 0 ∧ compress wordB 133 i.val = b133.getD i.val 0 :=
  of_decide_eq_true (checked (test := margins133At) (by decide +kernel) i)

def combinedPaf (s : Nat) : Int :=
  paf 1197 (signWord wordA) s + paf 1197 (signWord wordB) s

private def s0 : List Nat := [19, 21, 38, 42, 57, 63, 76, 84]
private theorem good0 : s0.all (fun s => decide (combinedPaf s = -2)) = true := by decide +kernel
private def s8 : List Nat := [95, 105, 114, 126, 133, 147, 152, 168]
private theorem good8 : s8.all (fun s => decide (combinedPaf s = -2)) = true := by decide +kernel
private def s16 : List Nat := [171, 189, 190, 209, 210, 228, 231, 247]
private theorem good16 : s16.all (fun s => decide (combinedPaf s = -2)) = true := by decide +kernel
private def s24 : List Nat := [252, 266, 273, 285, 294, 304, 315, 323]
private theorem good24 : s24.all (fun s => decide (combinedPaf s = -2)) = true := by decide +kernel
private def s32 : List Nat := [336, 342, 357, 361, 378, 380, 399, 418]
private theorem good32 : s32.all (fun s => decide (combinedPaf s = -2)) = true := by decide +kernel
private def s40 : List Nat := [420, 437, 441, 456, 462, 475, 483, 494]
private theorem good40 : s40.all (fun s => decide (combinedPaf s = -2)) = true := by decide +kernel
private def s48 : List Nat := [504, 513, 525, 532, 546, 551, 567, 570]
private theorem good48 : s48.all (fun s => decide (combinedPaf s = -2)) = true := by decide +kernel
private def s56 : List Nat := [588, 589, 608, 609, 627, 630, 646, 651]
private theorem good56 : s56.all (fun s => decide (combinedPaf s = -2)) = true := by decide +kernel
private def s64 : List Nat := [665, 672, 684, 693, 703, 714, 722, 735]
private theorem good64 : s64.all (fun s => decide (combinedPaf s = -2)) = true := by decide +kernel
private def s72 : List Nat := [741, 756, 760, 777, 779, 798, 817, 819]
private theorem good72 : s72.all (fun s => decide (combinedPaf s = -2)) = true := by decide +kernel
private def s80 : List Nat := [836, 840, 855, 861, 874, 882, 893, 903]
private theorem good80 : s80.all (fun s => decide (combinedPaf s = -2)) = true := by decide +kernel
private def s88 : List Nat := [912, 924, 931, 945, 950, 966, 969, 987]
private theorem good88 : s88.all (fun s => decide (combinedPaf s = -2)) = true := by decide +kernel
private def s96 : List Nat := [988, 1007, 1008, 1026, 1029, 1045, 1050, 1064]
private theorem good96 : s96.all (fun s => decide (combinedPaf s = -2)) = true := by decide +kernel
private def s104 : List Nat := [1071, 1083, 1092, 1102, 1113, 1121, 1134, 1140]
private theorem good104 : s104.all (fun s => decide (combinedPaf s = -2)) = true := by decide +kernel
private def s112 : List Nat := [1155, 1159, 1176, 1178]
private theorem good112 : s112.all (fun s => decide (combinedPaf s = -2)) = true := by decide +kernel

private def shifts : List Nat := s0 ++ s8 ++ s16 ++ s24 ++ s32 ++ s40 ++ s48 ++ s56 ++ s64 ++ s72 ++ s80 ++ s88 ++ s96 ++ s104 ++ s112
private def covered (s : Nat) : Bool := decide
  (s ≠ 0 → (57*s%1197 = 0 ∨ 63*s%1197 = 0) → s ∈ shifts)

theorem exact_subgroups (s : Fin 1197) (h₀ : s.val ≠ 0)
    (h : 57*s.val%1197 = 0 ∨ 63*s.val%1197 = 0) : combinedPaf s.val = -2 := by
  have hs : s.val ∈ shifts := of_decide_eq_true (checked (test := covered) (by decide +kernel) s) h₀ h
  have hgood : shifts.all (fun t => decide (combinedPaf t = -2)) = true := by
    simp only [shifts, List.all_append, good0, good8, good16, good24, good32, good40, good48, good56, good64, good72, good80, good88, good96, good104, good112, Bool.and_self]
  exact of_decide_eq_true (List.all_eq_true.mp hgood s.val hs)

theorem shift_one : combinedPaf 1 = 46 := by decide +kernel

#print axioms multiplier
#print axioms normalized
#print axioms margins57
#print axioms margins63
#print axioms margins133
#print axioms exact_subgroups
#print axioms shift_one
end Hadamard2396.Extension
