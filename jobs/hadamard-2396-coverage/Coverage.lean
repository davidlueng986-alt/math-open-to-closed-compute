import SquareAction

namespace Hadamard2396.Coverage
open SquareAction
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace MinimumEnergy
def maskA : Nat := 0x18dd10f2b8fe0c44740b78535acaddee203a2b932ef308b0d619ddabeeb7a70b98f6dd8ff5b45b0d575ed7c986f27ba8f70b85a7c8a22ffd2502902d2228099bc0c8930bf27b25faa7488edcd16d2966224570232f6b0b5a6ebc2540867acd81461af9ed5a98110b3f6c45f183f546c6d603be786159e54bc18df5439305e881467d3b2ffd3e52243f96323260f12719c94772a1873b
private def colsA : Array Nat := #[5, 3, 3, 4, 3, 2, 4, 5, 4, 3, 4, 4, 3, 2, 2, 4,
  3, 5, 2, 4, 5, 4, 2, 3, 5, 3, 5, 3, 2, 7, 3, 3,
  4, 5, 4, 5, 5, 2, 5, 4, 4, 2, 4, 3, 4, 4, 5, 2,
  4, 4, 3, 5, 4, 3, 4, 1, 4, 5, 2, 2, 1, 6, 5]
def maskB : Nat := 0x13578fe7b5e09397e31c467940f7ea4b0f9057c71a8d77fe0b4d3503864359df205f2edfa45d8634220d3569253181fa1dac48e48f05da58e04d1aabad6760d04a57a60eeca4f76df277e4c6ec528a4888b9a407551645073a458d687284593befeba9bc3365287a6c8ee5525007342c71cedf3fc6ad408e8e0773ccdceca32bd1683e3162edc53501fca80f4f560933b59366d3f875
private def colsB : Array Nat := #[5, 4, 6, 2, 2, 3, 3, 5, 2, 5, 2, 2, 5, 4, 5, 4,
  2, 3, 3, 2, 2, 2, 5, 3, 5, 3, 2, 3, 4, 4, 3, 3,
  5, 4, 3, 5, 2, 2, 2, 6, 4, 3, 3, 5, 3, 2, 2, 3,
  4, 3, 2, 3, 4, 4, 4, 4, 5, 2, 5, 5, 1, 1, 4]
private def table : Array Int := #[2394, 6, 6, 22, -2, -2, -30, -2, 2, -2, -2, 2, 14, -14, -6, -26,
  6, -2, -2, -14, -6, 22, -2, 2, -34, 2, 2, 2, -2, -2, -26, 2,
  -6, -18, -6, 6, -26, -2, 2, -6, -2, 2, 22, 2, -2, 54, -10, 2,
  26, 2, -2, -14, -2, -2, 30, 6, -6, 10, -10, -2, -6, -2, -10, 22,
  -10, -14, -10, -10, -6, 2, 6, -2, 10, -2, -2, -2, -2, -2, -38, 2,
  -6, 14, 2, -10, -6, -2, 2, -6, -2, -2, -10, 2, -2, -14, 2, 2,
  -14, 2, 2, -10, -2, 2, -6, -2, -2, -6, 2, -2, 14, -10, 2, -38,
  -6, 2, -2, -2, -2, 10, -2, -2, 2, -2, 6, -10, -6, -10, 22, -14,
  -10, -6, -10, -2, 10, -2, -10, 30, -6, 6, -14, -2, -2, 26, -2, 2,
  54, 2, -10, 22, -2, 2, -6, 2, -2, -26, 2, -2, -18, 6, -6, -26,
  -6, 2, 2, -2, -2, -34, 2, 2, 22, 2, -2, -2, -6, -14, -26, -2,
  6, 14, -6, -14, -2, 2, -2, -30, 2, -2, 22, -2, -2]
def combined (s : Nat) := paf 1197 (word maskA) s + paf 1197 (word maskB) s

private def certAAt := representsAt maskA colsA
private theorem certA0 : Block certAAt 0 133 := by decide +kernel
private theorem certA133 : Block certAAt 133 133 := by decide +kernel
private theorem certA266 : Block certAAt 266 133 := by decide +kernel
private theorem certA399 : Block certAAt 399 133 := by decide +kernel
private theorem certA532 : Block certAAt 532 133 := by decide +kernel
private theorem certA665 : Block certAAt 665 133 := by decide +kernel
private theorem certA798 : Block certAAt 798 133 := by decide +kernel
private theorem certA931 : Block certAAt 931 133 := by decide +kernel
private theorem certA1064 : Block certAAt 1064 133 := by decide +kernel
private theorem certA : Represents maskA colsA :=
  check_representation (join (join (join (join certA0 certA133) (join certA266 certA399)) (join (join certA532 certA665) (join certA798 certA931))) certA1064)

private def certBAt := representsAt maskB colsB
private theorem certB0 : Block certBAt 0 133 := by decide +kernel
private theorem certB133 : Block certBAt 133 133 := by decide +kernel
private theorem certB266 : Block certBAt 266 133 := by decide +kernel
private theorem certB399 : Block certBAt 399 133 := by decide +kernel
private theorem certB532 : Block certBAt 532 133 := by decide +kernel
private theorem certB665 : Block certBAt 665 133 := by decide +kernel
private theorem certB798 : Block certBAt 798 133 := by decide +kernel
private theorem certB931 : Block certBAt 931 133 := by decide +kernel
private theorem certB1064 : Block certBAt 1064 133 := by decide +kernel
private theorem certB : Represents maskB colsB :=
  check_representation (join (join (join (join certB0 certB133) (join certB266 certB399)) (join (join certB532 certB665) (join certB798 certB931))) certB1064)

private def scoresAt := tableAt colsA colsB table
private theorem scores0 : Block scoresAt 0 7 := by decide +kernel
private theorem scores7 : Block scoresAt 7 7 := by decide +kernel
private theorem scores14 : Block scoresAt 14 7 := by decide +kernel
private theorem scores21 : Block scoresAt 21 7 := by decide +kernel
private theorem scores28 : Block scoresAt 28 7 := by decide +kernel
private theorem scores35 : Block scoresAt 35 7 := by decide +kernel
private theorem scores42 : Block scoresAt 42 7 := by decide +kernel
private theorem scores49 : Block scoresAt 49 7 := by decide +kernel
private theorem scores56 : Block scoresAt 56 7 := by decide +kernel
private theorem scores63 : Block scoresAt 63 7 := by decide +kernel
private theorem scores70 : Block scoresAt 70 7 := by decide +kernel
private theorem scores77 : Block scoresAt 77 7 := by decide +kernel
private theorem scores84 : Block scoresAt 84 7 := by decide +kernel
private theorem scores91 : Block scoresAt 91 7 := by decide +kernel
private theorem scores98 : Block scoresAt 98 7 := by decide +kernel
private theorem scores105 : Block scoresAt 105 7 := by decide +kernel
private theorem scores112 : Block scoresAt 112 7 := by decide +kernel
private theorem scores119 : Block scoresAt 119 7 := by decide +kernel
private theorem scores126 : Block scoresAt 126 7 := by decide +kernel
private theorem scores133 : Block scoresAt 133 7 := by decide +kernel
private theorem scores140 : Block scoresAt 140 7 := by decide +kernel
private theorem scores147 : Block scoresAt 147 7 := by decide +kernel
private theorem scores154 : Block scoresAt 154 7 := by decide +kernel
private theorem scores161 : Block scoresAt 161 7 := by decide +kernel
private theorem scores168 : Block scoresAt 168 7 := by decide +kernel
private theorem scores175 : Block scoresAt 175 7 := by decide +kernel
private theorem scores182 : Block scoresAt 182 7 := by decide +kernel
private theorem scores : ModelTable colsA colsB table :=
  check_table (join (join (join (join (join scores0 scores7) (join scores14 scores21)) (join (join scores28 scores35) (join scores42 scores49))) (join (join (join scores56 scores63) (join scores70 scores77)) (join (join scores84 scores91) (join scores98 scores105)))) (join (join (join (join scores112 scores119) (join scores126 scores133)) (join (join scores140 scores147) (join scores154 scores161))) (join (join scores168 scores175) scores182)))


theorem all_correlations : combined = tableValue table := pair_table certA certB scores

theorem normalized : sumAt 1197 (fun i => sign (word maskA i)) = 1 ∧
    sumAt 1197 (fun i => sign (word maskB i)) = 1 := by decide +kernel

theorem original_statistics : exactPairs combined = 228 ∧ energy combined = 27328 ∧
    combined 1 = -2 ∧ combined 399 = 22 := by rw [all_correlations]; decide +kernel

#print axioms all_correlations
#print axioms original_statistics
end MinimumEnergy

namespace MaximumMatches
def maskA : Nat := 0x18dd10f2b8fe0c44740b78535acaddee213a2b932ef308b0d619ddabeeb7a74b98f6dd8ef5b45b0d575ed74986f27ba8f70b85a7c8a22ffd2502902d2228899bc0c8930bf27b25faa7488edcf16d2966224570232f6b0b5a2ebc2540877acd81461af9edda98110b3f6c45b183f546c6d6039e786159e5cbc18df5439305e8814e7d3b2ffd3e52203f96323260f12519c90772a1873b
private def colsA : Array Nat := #[5, 3, 3, 4, 3, 3, 4, 5, 4, 3, 5, 4, 3, 2, 2, 5,
  3, 5, 2, 4, 5, 5, 3, 3, 5, 3, 5, 2, 2, 7, 2, 3,
  4, 4, 4, 5, 4, 2, 4, 4, 4, 2, 4, 3, 4, 5, 5, 2,
  4, 4, 3, 4, 4, 2, 4, 1, 5, 4, 3, 2, 1, 6, 5]
def maskB : Nat := 0x13578fe7b5e09397e31c467940f7ea4b0f9057c71a8977fe0b4d3503864359df205f2edfa45d8634220d3569253181fa1dac48e48f05da58e04d1aabad67e0d05a57a40eeca4f76df276e4c6ec528a4888b9a407551445073a458d687284593befefa9bc3365287a6c8ee552500f342d71cedf3fc6ad400e8e0773ccdceca32bd1683e3162cdc53501fca80f4f560b33b59366d3f875
private def colsB : Array Nat := #[5, 4, 6, 2, 2, 3, 3, 4, 3, 4, 3, 2, 5, 4, 5, 4,
  2, 3, 2, 2, 2, 2, 5, 3, 5, 3, 2, 3, 4, 4, 3, 3,
  5, 4, 3, 4, 2, 2, 2, 6, 5, 2, 3, 5, 3, 2, 2, 3,
  4, 3, 2, 3, 5, 4, 5, 4, 5, 3, 4, 5, 1, 1, 4]
private def table : Array Int := #[2394, 6, 6, 22, -6, -2, -18, -2, 2, -2, -10, 14, 26, -22, -14, -18,
  6, -2, 18, -18, -2, 2, -2, -2, -26, 6, -2, 2, -2, -2, -22, -2,
  -10, -22, -2, 6, -22, 6, -2, -14, -2, -2, 30, 6, -2, 70, -6, -2,
  18, 6, -2, -6, 6, -2, 18, -2, -2, 10, -2, -2, 14, -2, -6, 26,
  -2, -26, -2, 2, -14, 10, -2, 2, -2, -2, -2, 2, 2, -2, -74, 2,
  -2, -6, -2, 2, -14, -2, -2, -22, -2, -2, -2, 2, -6, -22, -6, 6,
  -22, 6, -6, -2, -6, 2, -22, -2, -2, -14, -2, -2, -6, 2, -2, -74,
  -2, 2, 2, -2, 2, -2, -2, -2, 10, 2, -2, -2, -14, 2, 26, -26,
  -2, 14, -6, -2, 10, -2, -2, 18, -2, -2, -6, -2, 6, 18, -2, 6,
  70, -2, -6, 30, -2, 6, -14, -2, -2, -22, -2, 6, -22, 6, -2, -22,
  -10, -2, 2, -2, -2, -26, -2, 6, 2, -2, -2, 18, -2, -18, -18, -2,
  6, 26, -14, -22, -2, 14, -10, -18, 2, -2, 22, -2, -6]
def combined (s : Nat) := paf 1197 (word maskA) s + paf 1197 (word maskB) s

private def certAAt := representsAt maskA colsA
private theorem certA0 : Block certAAt 0 133 := by decide +kernel
private theorem certA133 : Block certAAt 133 133 := by decide +kernel
private theorem certA266 : Block certAAt 266 133 := by decide +kernel
private theorem certA399 : Block certAAt 399 133 := by decide +kernel
private theorem certA532 : Block certAAt 532 133 := by decide +kernel
private theorem certA665 : Block certAAt 665 133 := by decide +kernel
private theorem certA798 : Block certAAt 798 133 := by decide +kernel
private theorem certA931 : Block certAAt 931 133 := by decide +kernel
private theorem certA1064 : Block certAAt 1064 133 := by decide +kernel
private theorem certA : Represents maskA colsA :=
  check_representation (join (join (join (join certA0 certA133) (join certA266 certA399)) (join (join certA532 certA665) (join certA798 certA931))) certA1064)

private def certBAt := representsAt maskB colsB
private theorem certB0 : Block certBAt 0 133 := by decide +kernel
private theorem certB133 : Block certBAt 133 133 := by decide +kernel
private theorem certB266 : Block certBAt 266 133 := by decide +kernel
private theorem certB399 : Block certBAt 399 133 := by decide +kernel
private theorem certB532 : Block certBAt 532 133 := by decide +kernel
private theorem certB665 : Block certBAt 665 133 := by decide +kernel
private theorem certB798 : Block certBAt 798 133 := by decide +kernel
private theorem certB931 : Block certBAt 931 133 := by decide +kernel
private theorem certB1064 : Block certBAt 1064 133 := by decide +kernel
private theorem certB : Represents maskB colsB :=
  check_representation (join (join (join (join certB0 certB133) (join certB266 certB399)) (join (join certB532 certB665) (join certB798 certB931))) certB1064)

private def scoresAt := tableAt colsA colsB table
private theorem scores0 : Block scoresAt 0 7 := by decide +kernel
private theorem scores7 : Block scoresAt 7 7 := by decide +kernel
private theorem scores14 : Block scoresAt 14 7 := by decide +kernel
private theorem scores21 : Block scoresAt 21 7 := by decide +kernel
private theorem scores28 : Block scoresAt 28 7 := by decide +kernel
private theorem scores35 : Block scoresAt 35 7 := by decide +kernel
private theorem scores42 : Block scoresAt 42 7 := by decide +kernel
private theorem scores49 : Block scoresAt 49 7 := by decide +kernel
private theorem scores56 : Block scoresAt 56 7 := by decide +kernel
private theorem scores63 : Block scoresAt 63 7 := by decide +kernel
private theorem scores70 : Block scoresAt 70 7 := by decide +kernel
private theorem scores77 : Block scoresAt 77 7 := by decide +kernel
private theorem scores84 : Block scoresAt 84 7 := by decide +kernel
private theorem scores91 : Block scoresAt 91 7 := by decide +kernel
private theorem scores98 : Block scoresAt 98 7 := by decide +kernel
private theorem scores105 : Block scoresAt 105 7 := by decide +kernel
private theorem scores112 : Block scoresAt 112 7 := by decide +kernel
private theorem scores119 : Block scoresAt 119 7 := by decide +kernel
private theorem scores126 : Block scoresAt 126 7 := by decide +kernel
private theorem scores133 : Block scoresAt 133 7 := by decide +kernel
private theorem scores140 : Block scoresAt 140 7 := by decide +kernel
private theorem scores147 : Block scoresAt 147 7 := by decide +kernel
private theorem scores154 : Block scoresAt 154 7 := by decide +kernel
private theorem scores161 : Block scoresAt 161 7 := by decide +kernel
private theorem scores168 : Block scoresAt 168 7 := by decide +kernel
private theorem scores175 : Block scoresAt 175 7 := by decide +kernel
private theorem scores182 : Block scoresAt 182 7 := by decide +kernel
private theorem scores : ModelTable colsA colsB table :=
  check_table (join (join (join (join (join scores0 scores7) (join scores14 scores21)) (join (join scores28 scores35) (join scores42 scores49))) (join (join (join scores56 scores63) (join scores70 scores77)) (join (join scores84 scores91) (join scores98 scores105)))) (join (join (join (join scores112 scores119) (join scores126 scores133)) (join (join scores140 scores147) (join scores154 scores161))) (join (join scores168 scores175) scores182)))


theorem all_correlations : combined = tableValue table := pair_table certA certB scores

theorem normalized : sumAt 1197 (fun i => sign (word maskA i)) = 1 ∧
    sumAt 1197 (fun i => sign (word maskB i)) = 1 := by decide +kernel

theorem original_statistics : exactPairs combined = 310 ∧ energy combined = 42784 ∧
    combined 1 = -6 ∧ combined 399 = 26 := by rw [all_correlations]; decide +kernel

#print axioms all_correlations
#print axioms original_statistics
end MaximumMatches

namespace EnergyBudget
def maskA : Nat := 0x18dd10f2b8fe0c44740b78535acaddee213a2b932ef308b0d619ddabeeb7a74b98f6dd8ef5b45b0d575ed74986f27ba8f70b85a7c8a22ffd2502902d2228899bc0c8930bf27b25faa7488edcf16d2966224570232f6b0b5a2ebc2540877acd81461af9edda98110b3f6c45b183f546c6d6039e786159e5cbc18df5439305e8814e7d3b2ffd1e52203f96323260f12719c90772a1873b
private def colsA : Array Nat := #[5, 3, 3, 4, 3, 3, 4, 4, 4, 3, 5, 4, 3, 2, 2, 5,
  3, 5, 2, 4, 5, 5, 3, 3, 5, 3, 5, 2, 2, 7, 2, 3,
  4, 4, 4, 5, 4, 2, 4, 4, 4, 2, 4, 3, 4, 5, 5, 2,
  4, 4, 3, 4, 4, 2, 4, 1, 5, 5, 3, 2, 1, 6, 5]
def maskB : Nat := 0x13578fe7b5e09397e31c467940f7ea4b0f9057c71a8977fe0b4d3503864359df205f2edfa45d8634220d3569253181fa1dac48e48f05da58e04d1aabad67e0d05a57a60eeca4f76df276e4c6ec528a4888b9a407551445073a4585687284593befefa9bc3365287a6c8ee552500f342d71cedf3fc6ad400e8e0773ccdceca32bd1683e3162cdc53501fca80f4f560b33b59366d3f875
private def colsB : Array Nat := #[5, 4, 6, 2, 2, 3, 3, 4, 3, 4, 3, 2, 5, 4, 5, 4,
  2, 3, 2, 2, 2, 2, 5, 3, 5, 3, 2, 3, 4, 4, 3, 3,
  5, 4, 2, 5, 2, 2, 2, 6, 5, 2, 3, 5, 3, 2, 2, 3,
  4, 3, 2, 3, 5, 4, 5, 4, 5, 3, 4, 5, 1, 1, 4]
private def table : Array Int := #[2394, 6, 6, 30, -2, -6, -26, -2, -2, -6, -2, 2, 26, -22, -6, -14,
  -2, 2, 14, -14, -6, 6, -2, -2, -26, 6, -2, -6, -2, -6, -30, -2,
  -6, -14, 6, -2, -18, 6, -2, -18, -2, -2, 30, 6, -2, 62, -2, -2,
  22, -2, 6, -14, 6, -2, 18, -2, -2, 10, -2, -2, 2, -2, -6, 38,
  -6, -22, -2, 6, -22, 14, -2, 2, -10, -2, -2, 2, -2, -2, -70, 2,
  -2, -6, -6, 10, -10, 6, -6, -22, 2, -6, 6, -2, 2, -14, -2, -2,
  -14, -2, -2, 6, 2, -2, -22, -6, 2, -10, -6, 6, -6, 10, -6, -70,
  -2, 2, 2, -2, -2, -10, -2, -2, 14, 2, -2, -2, -22, 6, 38, -22,
  -6, 2, -6, -2, 10, -2, -2, 18, -2, -2, -14, -2, 6, 22, 6, -2,
  62, -2, -2, 30, -2, 6, -18, -2, -2, -18, -2, 6, -14, -2, 6, -30,
  -6, -2, -6, -6, -2, -26, -2, 6, 6, -2, -2, 14, -6, -14, -14, 2,
  -2, 26, -6, -22, -6, 2, -2, -26, -2, -2, 30, -6, -2]
def combined (s : Nat) := paf 1197 (word maskA) s + paf 1197 (word maskB) s

private def certAAt := representsAt maskA colsA
private theorem certA0 : Block certAAt 0 133 := by decide +kernel
private theorem certA133 : Block certAAt 133 133 := by decide +kernel
private theorem certA266 : Block certAAt 266 133 := by decide +kernel
private theorem certA399 : Block certAAt 399 133 := by decide +kernel
private theorem certA532 : Block certAAt 532 133 := by decide +kernel
private theorem certA665 : Block certAAt 665 133 := by decide +kernel
private theorem certA798 : Block certAAt 798 133 := by decide +kernel
private theorem certA931 : Block certAAt 931 133 := by decide +kernel
private theorem certA1064 : Block certAAt 1064 133 := by decide +kernel
private theorem certA : Represents maskA colsA :=
  check_representation (join (join (join (join certA0 certA133) (join certA266 certA399)) (join (join certA532 certA665) (join certA798 certA931))) certA1064)

private def certBAt := representsAt maskB colsB
private theorem certB0 : Block certBAt 0 133 := by decide +kernel
private theorem certB133 : Block certBAt 133 133 := by decide +kernel
private theorem certB266 : Block certBAt 266 133 := by decide +kernel
private theorem certB399 : Block certBAt 399 133 := by decide +kernel
private theorem certB532 : Block certBAt 532 133 := by decide +kernel
private theorem certB665 : Block certBAt 665 133 := by decide +kernel
private theorem certB798 : Block certBAt 798 133 := by decide +kernel
private theorem certB931 : Block certBAt 931 133 := by decide +kernel
private theorem certB1064 : Block certBAt 1064 133 := by decide +kernel
private theorem certB : Represents maskB colsB :=
  check_representation (join (join (join (join certB0 certB133) (join certB266 certB399)) (join (join certB532 certB665) (join certB798 certB931))) certB1064)

private def scoresAt := tableAt colsA colsB table
private theorem scores0 : Block scoresAt 0 7 := by decide +kernel
private theorem scores7 : Block scoresAt 7 7 := by decide +kernel
private theorem scores14 : Block scoresAt 14 7 := by decide +kernel
private theorem scores21 : Block scoresAt 21 7 := by decide +kernel
private theorem scores28 : Block scoresAt 28 7 := by decide +kernel
private theorem scores35 : Block scoresAt 35 7 := by decide +kernel
private theorem scores42 : Block scoresAt 42 7 := by decide +kernel
private theorem scores49 : Block scoresAt 49 7 := by decide +kernel
private theorem scores56 : Block scoresAt 56 7 := by decide +kernel
private theorem scores63 : Block scoresAt 63 7 := by decide +kernel
private theorem scores70 : Block scoresAt 70 7 := by decide +kernel
private theorem scores77 : Block scoresAt 77 7 := by decide +kernel
private theorem scores84 : Block scoresAt 84 7 := by decide +kernel
private theorem scores91 : Block scoresAt 91 7 := by decide +kernel
private theorem scores98 : Block scoresAt 98 7 := by decide +kernel
private theorem scores105 : Block scoresAt 105 7 := by decide +kernel
private theorem scores112 : Block scoresAt 112 7 := by decide +kernel
private theorem scores119 : Block scoresAt 119 7 := by decide +kernel
private theorem scores126 : Block scoresAt 126 7 := by decide +kernel
private theorem scores133 : Block scoresAt 133 7 := by decide +kernel
private theorem scores140 : Block scoresAt 140 7 := by decide +kernel
private theorem scores147 : Block scoresAt 147 7 := by decide +kernel
private theorem scores154 : Block scoresAt 154 7 := by decide +kernel
private theorem scores161 : Block scoresAt 161 7 := by decide +kernel
private theorem scores168 : Block scoresAt 168 7 := by decide +kernel
private theorem scores175 : Block scoresAt 175 7 := by decide +kernel
private theorem scores182 : Block scoresAt 182 7 := by decide +kernel
private theorem scores : ModelTable colsA colsB table :=
  check_table (join (join (join (join (join scores0 scores7) (join scores14 scores21)) (join (join scores28 scores35) (join scores42 scores49))) (join (join (join scores56 scores63) (join scores70 scores77)) (join (join scores84 scores91) (join scores98 scores105)))) (join (join (join (join scores112 scores119) (join scores126 scores133)) (join (join scores140 scores147) (join scores154 scores161))) (join (join scores168 scores175) scores182)))


theorem all_correlations : combined = tableValue table := pair_table certA certB scores

theorem normalized : sumAt 1197 (fun i => sign (word maskA i)) = 1 ∧
    sumAt 1197 (fun i => sign (word maskB i)) = 1 := by decide +kernel

theorem original_statistics : exactPairs combined = 298 ∧ energy combined = 39424 ∧
    combined 1 = -2 ∧ combined 399 = 38 := by rw [all_correlations]; decide +kernel

#print axioms all_correlations
#print axioms original_statistics
end EnergyBudget

end Hadamard2396.Coverage
