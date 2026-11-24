import Diagonal

namespace Hadamard2396.Quotient399

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Hadamard2396.Diagonal (checked)

def wordA : Nat := 0x37404a935a908485a4b5c508e759bc14d12daffa63d42b0565ddcb4208d13068e8cb8719cf939d673af76f17dead1bcc6666b757d64adb932bba84e6cc24351f8beca9b07c8b9fd2010cc80bb167e30165d72df7b72e3d0458df071699f280f5c53720d279bdb0e123ffbc5b15a20e4a8d54ddb34cb8ceb4499738d60defde0285c2e9b5860c43f7b98eaf0a3c04ea08f05da34a560
def wordB : Nat := 0x1b373c479e62b302e52fb979f3d8b652f3627a0f7b8297c9c16a470658026ffa5b00078a1746f75c0cd049481b1440cf13029ca6f8e9dc167894d2ee0c31a42d07d2bf36d7953bc3b72d40e10431bbec12f168c911e853ee5f450f73ee5c0a6fa1c69c2bd1c59e51fde63634474e4bfd5aaacd5a8c1e115c5126c7278b0ba2b5642a2716c045dbb0aea4bda79b5f85e9715fecc9725a

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
  (compress wordA 57 i = Diagonal.a57.getD i 0 ∧ compress wordB 57 i = Diagonal.b57.getD i 0)

theorem margins57 (i : Fin 57) :
    compress wordA 57 i.val = Diagonal.a57.getD i.val 0 ∧ compress wordB 57 i.val = Diagonal.b57.getD i.val 0 :=
  of_decide_eq_true (checked (test := margins57At) (by decide +kernel) i)

private def margins63At (i : Nat) : Bool := decide
  (compress wordA 63 i = Diagonal.a63.getD i 0 ∧ compress wordB 63 i = Diagonal.b63.getD i 0)

theorem margins63 (i : Fin 63) :
    compress wordA 63 i.val = Diagonal.a63.getD i.val 0 ∧ compress wordB 63 i.val = Diagonal.b63.getD i.val 0 :=
  of_decide_eq_true (checked (test := margins63At) (by decide +kernel) i)

private def margins133At (i : Nat) : Bool := decide
  (compress wordA 133 i = Diagonal.a133.getD i 0 ∧ compress wordB 133 i = Diagonal.b133.getD i 0)

theorem margins133 (i : Fin 133) :
    compress wordA 133 i.val = Diagonal.a133.getD i.val 0 ∧ compress wordB 133 i.val = Diagonal.b133.getD i.val 0 :=
  of_decide_eq_true (checked (test := margins133At) (by decide +kernel) i)

def combinedPaf (s : Nat) : Int :=
  paf 1197 (signWord wordA) s + paf 1197 (signWord wordB) s

private def s0 : List Nat := [1, 2, 3, 19, 21, 38, 42, 48]
private theorem good0 : s0.all (fun t => decide (combinedPaf t = -2)) = true := by decide +kernel
private def s8 : List Nat := [49, 56, 57, 63, 64, 71, 72, 76]
private theorem good8 : s8.all (fun t => decide (combinedPaf t = -2)) = true := by decide +kernel
private def s16 : List Nat := [84, 95, 105, 106, 109, 114, 126, 133]
private theorem good16 : s16.all (fun t => decide (combinedPaf t = -2)) = true := by decide +kernel
private def s24 : List Nat := [147, 149, 152, 168, 171, 180, 189, 190]
private theorem good24 : s24.all (fun t => decide (combinedPaf t = -2)) = true := by decide +kernel
private def s32 : List Nat := [192, 193, 195, 209, 210, 212, 228, 231]
private theorem good32 : s32.all (fun t => decide (combinedPaf t = -2)) = true := by decide +kernel
private def s40 : List Nat := [233, 247, 252, 265, 266, 271, 273, 285]
private theorem good40 : s40.all (fun t => decide (combinedPaf t = -2)) = true := by decide +kernel
private def s48 : List Nat := [293, 294, 300, 304, 315, 318, 321, 323]
private theorem good48 : s48.all (fun t => decide (combinedPaf t = -2)) = true := by decide +kernel
private def s56 : List Nat := [335, 336, 342, 344, 357, 361, 378, 380]
private theorem good56 : s56.all (fun t => decide (combinedPaf t = -2)) = true := by decide +kernel
private def s64 : List Nat := [398, 399, 400, 406, 416, 418, 420, 437]
private theorem good64 : s64.all (fun t => decide (combinedPaf t = -2)) = true := by decide +kernel
private def s72 : List Nat := [439, 441, 446, 450, 456, 462, 463, 475]
private theorem good72 : s72.all (fun t => decide (combinedPaf t = -2)) = true := by decide +kernel
private def s80 : List Nat := [483, 494, 504, 505, 510, 513, 519, 525]
private theorem good80 : s80.all (fun t => decide (combinedPaf t = -2)) = true := by decide +kernel
private def s88 : List Nat := [532, 546, 551, 554, 559, 567, 570, 583]
private theorem good88 : s88.all (fun t => decide (combinedPaf t = -2)) = true := by decide +kernel
private def s96 : List Nat := [588, 589, 593, 596, 601, 604, 608, 609]
private theorem good96 : s96.all (fun t => decide (combinedPaf t = -2)) = true := by decide +kernel
private def s104 : List Nat := [614, 627, 630, 638, 643, 646, 651, 665]
private theorem good104 : s104.all (fun t => decide (combinedPaf t = -2)) = true := by decide +kernel
private def s112 : List Nat := [672, 678, 684, 687, 692, 693, 703, 714]
private theorem good112 : s112.all (fun t => decide (combinedPaf t = -2)) = true := by decide +kernel
private def s120 : List Nat := [722, 734, 735, 741, 747, 751, 756, 758]
private theorem good120 : s120.all (fun t => decide (combinedPaf t = -2)) = true := by decide +kernel
private def s128 : List Nat := [760, 777, 779, 781, 791, 797, 798, 799]
private theorem good128 : s128.all (fun t => decide (combinedPaf t = -2)) = true := by decide +kernel
private def s136 : List Nat := [817, 819, 836, 840, 853, 855, 861, 862]
private theorem good136 : s136.all (fun t => decide (combinedPaf t = -2)) = true := by decide +kernel
private def s144 : List Nat := [874, 876, 879, 882, 893, 897, 903, 904]
private theorem good144 : s144.all (fun t => decide (combinedPaf t = -2)) = true := by decide +kernel
private def s152 : List Nat := [912, 924, 926, 931, 932, 945, 950, 964]
private theorem good152 : s152.all (fun t => decide (combinedPaf t = -2)) = true := by decide +kernel
private def s160 : List Nat := [966, 969, 985, 987, 988, 1002, 1004, 1005]
private theorem good160 : s160.all (fun t => decide (combinedPaf t = -2)) = true := by decide +kernel
private def s168 : List Nat := [1007, 1008, 1017, 1026, 1029, 1045, 1048, 1050]
private theorem good168 : s168.all (fun t => decide (combinedPaf t = -2)) = true := by decide +kernel
private def s176 : List Nat := [1064, 1071, 1083, 1088, 1091, 1092, 1102, 1113]
private theorem good176 : s176.all (fun t => decide (combinedPaf t = -2)) = true := by decide +kernel
private def s184 : List Nat := [1121, 1125, 1126, 1133, 1134, 1140, 1141, 1148]
private theorem good184 : s184.all (fun t => decide (combinedPaf t = -2)) = true := by decide +kernel
private def s192 : List Nat := [1149, 1155, 1159, 1176, 1178, 1194, 1195, 1196]
private theorem good192 : s192.all (fun t => decide (combinedPaf t = -2)) = true := by decide +kernel

/-- All 200 listed shifts are tested against the original two sign words. -/
def exactShifts : List Nat := s0 ++ s8 ++ s16 ++ s24 ++ s32 ++ s40 ++ s48 ++ s56 ++ s64 ++ s72 ++ s80 ++ s88 ++ s96 ++ s104 ++ s112 ++ s120 ++ s128 ++ s136 ++ s144 ++ s152 ++ s160 ++ s168 ++ s176 ++ s184 ++ s192
theorem exact_on_list (t : Nat) (ht : t ∈ exactShifts) : combinedPaf t = -2 := by
  have h : exactShifts.all (fun u => decide (combinedPaf u = -2)) = true := by
    simp only [exactShifts, List.all_append, good0, good8, good16, good24, good32, good40, good48, good56, good64, good72, good80, good88, good96, good104, good112, good120, good128, good136, good144, good152, good160, good168, good176, good184, good192, Bool.and_self]
  exact of_decide_eq_true (List.all_eq_true.mp h t ht)

/-- The 57- and 63-order subgroups, the three lifts of the multiplier orbit of
    residue 1 mod 399, and the original multiplier orbits of 2 and 3. -/
def prescribed (s : Nat) : Bool :=
  s != 0 && (57*s%1197 == 0 || 63*s%1197 == 0 ||
    [1, 64, 106, 293, 335, 398].contains (s%399) ||
    [2, 3, 192, 212, 271, 318, 879, 926, 985, 1005, 1194, 1195].contains s)

private def covered (s : Nat) : Bool := decide (prescribed s = true → s ∈ exactShifts)

theorem exact_prescribed (s : Fin 1197) (hs : prescribed s.val = true) : combinedPaf s.val = -2 :=
  exact_on_list _ (of_decide_eq_true (checked (test := covered) (by decide +kernel) s) hs)

theorem count_prescribed : ((List.range 1197).filter prescribed).length = 146 := by decide +kernel

theorem count_listed : exactShifts.length = 200 ∧ exactShifts.Nodup := by decide +kernel

theorem shift_four : combinedPaf 4 = -50 := by decide +kernel

#print axioms multiplier
#print axioms normalized
#print axioms margins57
#print axioms margins63
#print axioms margins133
#print axioms exact_on_list
#print axioms exact_prescribed
#print axioms count_prescribed
#print axioms count_listed
#print axioms shift_four
end Hadamard2396.Quotient399
