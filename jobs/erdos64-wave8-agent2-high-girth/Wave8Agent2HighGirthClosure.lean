import Shadow
import NonBacktrackingGirth
import Wave5Agent5GirthTripling
import Wave5Agent6ChebyshevGirth
import ChebTraceEngine
import NonSimpleHelpers
import NonSimpleDecomp
import NonSimpleBarbell
import NonSimpleTheta

/-!
# Wave 8 Agent #2 — Unconditional High-Girth Closure for Erdős Problem #64

Combines:
1. `ChebTraceEngine`: Pure-2-square integer Chebyshev-polynomial SOS trace certificates over `ℚ`
   (zero eigenvalues, zero spectral gap, zero floating-point arithmetic).
2. `NonSimpleHelpers` / `NonSimpleDecomp` / `NonSimpleBarbell` / `NonSimpleTheta`:
   Exact trace-coupled non-simple CNB walk upper bound
   `nonSimpleTaillessCount G (2^k) ≤ ∑ r < 2^k, alphaCoeff g (2^k) r * taillessCount G r`
   valid for all cubic, power-free graphs of girth `g ≥ 6` and `2^k < 3 * g`.

Closes EVERY previously uncovered high girth `g ∈ {6, 7, 11, 12, 13, 14, 15}` (plus `g = 8` via
girth-9 upgrade) unconditionally at or strictly above the cubic Moore bound `M(3, g)`, including
the **first-ever unconditional closures** at `g = 13` (`n ≤ 215`, `1.13x` Moore `190`) and
`g = 14` (`n ≤ 274`, `1.08x` Moore `254`), and a `2.76x` improvement at `g = 15` (`n ≤ 1483`,
`3.88x` Moore `382`, vs Wave 5's `537`).
-/

namespace E64Wave8Agent2
open SimpleGraph Erdos64Closure E64NonBacktrackingGirth E64Wave5Agent5 E64Wave5Agent6

section HighGirthClosure

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Master Unconditional Certificate Closure Theorem**:
If `checkCert g (2^k) N p q alpha = true` and `alpha` dominates `alphaCoeff g (2^k)` on all
`r < 2^k`, then EVERY cubic simple graph `G` of girth `≥ g` (`g ≥ 6`, `4 ≤ k ≤ 6`, `2^k < 3*g`)
and order `0 < |V| ≤ N` unconditionally satisfies `Erdos64Closure.HasPower G`. -/
theorem hasPower_of_cert (G : SimpleGraph V) [DecidableRel G.Adj]
    {g k N : ℕ} (p q : List ℤ) (alpha : List (ℕ × ℕ))
    (hreg : ∀ v : V, G.degree v = 3) (hn : 0 < Fintype.card V) (hle : Fintype.card V ≤ N)
    (hg : GirthAtLeast G g) (hg6 : 6 ≤ g) (hk4 : 4 ≤ k) (hk6 : k ≤ 6) (hLt : 2 ^ k < 3 * g)
    (hcert : checkCert g (2 ^ k) N p q alpha = true)
    (hdom : (List.range (2 ^ k)).all (fun r => decide (alphaCoeff g (2 ^ k) r ≤ lookupAlpha alpha r)) = true) :
    HasPower G := by
  by_contra hnp
  have hsurp := cert_trace_surplus_of_two_square G hreg hn hle hg hnp hcert
  have hns := nonSimpleTaillessCount_le_sum_alpha G hreg hg hg6 hnp hk4 hk6 hLt
  have hdom_sum : (∑ r ∈ Finset.range (2 ^ k), alphaCoeff g (2 ^ k) r * taillessCount G r) ≤
      ∑ r ∈ Finset.range (2 ^ k), lookupAlpha alpha r * taillessCount G r := by
    refine Finset.sum_le_sum fun r hr => ?_
    simp only [Finset.mem_range] at hr
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hdom
    exact Nat.mul_le_mul_right _ (hdom r hr)
  have hlt : nonSimpleTaillessCount G (2 ^ k) < taillessCount G (2 ^ k) :=
    lt_of_le_of_lt (le_trans hns hdom_sum) hsurp
  unfold nonSimpleTaillessCount taillessCount at hlt
  have hex : ∃ v : V,
      ((nbWalks G (2 ^ k) v v).filter fun w => IsCyclicallyNonBacktracking w.1 ∧ ¬ w.1.IsCycle).card <
      ((nbWalks G (2 ^ k) v v).filter fun w => IsCyclicallyNonBacktracking w.1).card := by
    by_contra hall
    push_neg at hall
    have hle_sum := Finset.sum_le_sum fun v (_ : v ∈ Finset.univ) => hall v
    omega
  obtain ⟨v, hv⟩ := hex
  have hsub : ¬ (((nbWalks G (2 ^ k) v v).filter fun w => IsCyclicallyNonBacktracking w.1) ⊆
      ((nbWalks G (2 ^ k) v v).filter fun w => IsCyclicallyNonBacktracking w.1 ∧ ¬ w.1.IsCycle)) := by
    intro hss
    have := Finset.card_le_card hss
    omega
  rw [Finset.not_subset] at hsub
  obtain ⟨⟨w, hw⟩, hmem, hnotmem⟩ := hsub
  simp only [Finset.mem_filter, not_and, not_not] at hmem hnotmem
  exact hnp ⟨k, v, w, by omega, hnotmem hmem.1 hmem.2, hw⟩

def certP_g6 : List ℤ := [11331613, 10373866, -4185405, -751550, 8624268, 275790, -1080225, -5000, 10000]
def certQ_g6 : List ℤ := [11896001, 7487874, 5797807, 7475905, -630944, 4571031, 56012, -146559, 0]
def certAlpha_g6 : List (ℕ × ℕ) := [(6, 1056), (7, 592)]
def certP_g7 : List ℤ := [-106633, 41374, -120040, -2532, -9682, 7256, -30791, -500, 1000]
def certQ_g7 : List ℤ := [156727, 457144, 70628, 255844, -5397, 59952, 2981, -7767, 0]
def certAlpha_g7 : List (ℕ × ℕ) := [(7, 288)]
def certP_g11 : List ℤ := [175895297, 17917239, 35543370, 78557505, 469489962, 16394496, 94462606, -8608691, -984910, 28231, 14606354, -849, 23547199, 16301, -4472973, -500, 100000]
def certQ_g11 : List ℤ := [-109042795, -727460373, -107697245, 353819101, 16749299, -150982860, 17903812, -57675084, -2108555, -46182635, -127595, -19551584, -32366, 13067047, 4141, -945777, 0]
def certAlpha_g11 : List (ℕ × ℕ) := [(11, 1021440), (12, 432896), (13, 236928), (14, 73408), (15, 40800)]
def certP_g12 : List ℤ := [164820796, 349544546, -6941198, 83737050, 244659008, 34093757, 64917041, 8523623, 9940004, -5939694, 13948399, 269146, 12443366, 32734, -3395292, -500, 100000]
def certQ_g12 : List ℤ := [-187329447, -333409094, -31884247, 287265577, -3361172, -24442074, 11669897, -19316765, 10995709, -20970517, -1869155, -5682808, -46809, 8505444, 6094, -823989, 0]
def certAlpha_g12 : List (ℕ × ℕ) := [(12, 432896), (13, 236928), (14, 73408), (15, 40800)]
def certP_g13 : List ℤ := [532358198, 222111571, 118912475, 46131916, 192641118, 14912708, 66664999, 1237556, 19550421, -3783279, 3663510, 477530, 6492378, 704, -2526656, -500, 100000]
def certQ_g13 : List ℤ := [-61789187, -16855420, 13289070, 176469698, 9854778, 18802859, 9832469, 6859249, 5141849, 4031526, -1661231, -2018867, 74984, 5404201, 1947, -710796, 0]
def certAlpha_g13 : List (ℕ × ℕ) := [(13, 118400), (14, 36672), (15, 20384)]
def certP_g14 : List ℤ := [97664513, 85520773, 28042996, 20305886, 9963911, 7100478, 4165855, 2988095, 1850488, 1254023, 709543, 322344, -147751, -558674, -611660, -500, 100000]
def certQ_g14 : List ℤ := [44822401, 485518, -25559549, -15312809, -6876935, -3066365, -1027190, 62244, 541586, 806699, 863354, 932249, 829359, 529791, -158778, -349617, 0]
def certAlpha_g14 : List (ℕ × ℕ) := [(14, 36672), (15, 20384)]
def certP_g15 : List ℤ := [-19137176, 35850405, -26728078, 5595014, -5751122, 1429047, -2166820, 685855, -1141394, 480363, -654176, 385459, -395170, 346622, -343686, -500, 100000]
def certQ_g15 : List ℤ := [-352744, 18147276, -37808929, 20616107, -13487429, 8141545, -4982546, 3076356, -1922518, 1131860, -748351, 391744, -251770, 107961, 133152, -261986, 0]
def certAlpha_g15 : List (ℕ × ℕ) := [(15, 10176)]

/-- Unconditional cubic girth `≥ 6` closure up to `n ≤ 14` (1.00x Moore bound `M(3,6) = 14`,
length `L = 16 = 2^4`, pure 2-square integer Chebyshev SOS certificate). -/
theorem cubic_girth6_le_14_hasPower (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : ∀ v : V, G.degree v = 3) (hn : 0 < Fintype.card V) (hle : Fintype.card V ≤ 14)
    (hg : GirthAtLeast G 6) : HasPower G :=
  hasPower_of_cert G (g := 6) (k := 4) (N := 14) certP_g6 certQ_g6 certAlpha_g6
    hreg hn hle hg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Unconditional cubic girth `≥ 7` closure up to `n ≤ 33` (1.50x Moore bound `M(3,7) = 22`,
length `L = 16 = 2^4`, pure 2-square integer Chebyshev SOS certificate). -/
theorem cubic_girth7_le_33_hasPower (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : ∀ v : V, G.degree v = 3) (hn : 0 < Fintype.card V) (hle : Fintype.card V ≤ 33)
    (hg : GirthAtLeast G 7) : HasPower G :=
  hasPower_of_cert G (g := 7) (k := 4) (N := 33) certP_g7 certQ_g7 certAlpha_g7
    hreg hn hle hg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Unconditional cubic girth `≥ 11` closure up to `n ≤ 143` (1.52x Moore bound `M(3,11) = 94`,
length `L = 32 = 2^5`, pure 2-square integer Chebyshev SOS certificate). -/
theorem cubic_girth11_le_143_hasPower (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : ∀ v : V, G.degree v = 3) (hn : 0 < Fintype.card V) (hle : Fintype.card V ≤ 143)
    (hg : GirthAtLeast G 11) : HasPower G :=
  hasPower_of_cert G (g := 11) (k := 5) (N := 143) certP_g11 certQ_g11 certAlpha_g11
    hreg hn hle hg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Unconditional cubic girth `≥ 12` closure up to `n ≤ 149` (1.18x Moore bound `M(3,12) = 126`,
length `L = 32 = 2^5`, pure 2-square integer Chebyshev SOS certificate). -/
theorem cubic_girth12_le_149_hasPower (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : ∀ v : V, G.degree v = 3) (hn : 0 < Fintype.card V) (hle : Fintype.card V ≤ 149)
    (hg : GirthAtLeast G 12) : HasPower G :=
  hasPower_of_cert G (g := 12) (k := 5) (N := 149) certP_g12 certQ_g12 certAlpha_g12
    hreg hn hle hg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Unconditional cubic girth `≥ 13` closure up to `n ≤ 215` (1.13x Moore bound `M(3,13) = 190`,
length `L = 32 = 2^5`, pure 2-square integer Chebyshev SOS certificate). -/
theorem cubic_girth13_le_215_hasPower (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : ∀ v : V, G.degree v = 3) (hn : 0 < Fintype.card V) (hle : Fintype.card V ≤ 215)
    (hg : GirthAtLeast G 13) : HasPower G :=
  hasPower_of_cert G (g := 13) (k := 5) (N := 215) certP_g13 certQ_g13 certAlpha_g13
    hreg hn hle hg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Unconditional cubic girth `≥ 14` closure up to `n ≤ 274` (1.08x Moore bound `M(3,14) = 254`,
length `L = 32 = 2^5`, pure 2-square integer Chebyshev SOS certificate). -/
theorem cubic_girth14_le_274_hasPower (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : ∀ v : V, G.degree v = 3) (hn : 0 < Fintype.card V) (hle : Fintype.card V ≤ 274)
    (hg : GirthAtLeast G 14) : HasPower G :=
  hasPower_of_cert G (g := 14) (k := 5) (N := 274) certP_g14 certQ_g14 certAlpha_g14
    hreg hn hle hg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Unconditional cubic girth `≥ 15` closure up to `n ≤ 1483` (3.88x Moore bound `M(3,15) = 382`,
length `L = 32 = 2^5`, pure 2-square integer Chebyshev SOS certificate). -/
theorem cubic_girth15_le_1483_hasPower (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : ∀ v : V, G.degree v = 3) (hn : 0 < Fintype.card V) (hle : Fintype.card V ≤ 1483)
    (hg : GirthAtLeast G 15) : HasPower G :=
  hasPower_of_cert G (g := 15) (k := 5) (N := 1483) certP_g15 certQ_g15 certAlpha_g15
    hreg hn hle hg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Unconditional cubic girth `≥ 8` closure up to `n ≤ 131` (4.37x Moore bound `M(3,8) = 30`):
any power-free girth-8 graph has no `C_8`, hence girth `≥ 9`, closing by Wave 5 Agent #6. -/
theorem cubic_girth8_le_131_hasPower (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : ∀ v : V, G.degree v = 3) (hn : 0 < Fintype.card V) (hle : Fintype.card V ≤ 131)
    (hg : GirthAtLeast G 8) : HasPower G := by
  by_contra hnp
  have hg9 : GirthAtLeast G 9 := by
    intro v p hp
    have hge8 := hg v p hp
    have hne8 : p.length ≠ 8 := fun h8 => hnp ⟨3, v, p, by decide, hp, by simpa using h8⟩
    omega
  exact hnp (cubic_girth9_le_131_hasPower G hreg hn hle hg9)

/-- **Unified Wave 8 High-Girth Window Closure (`g ∈ {9, 10, 11, 12, 13, 14}`)**:
Every cubic simple graph of girth `g ∈ {9, 10, 11, 12, 13, 14}` and order strictly above the
corresponding cubic Moore bound (`n ≤ 131` for `g = 9, 10`; `n ≤ 143` for `g = 11`;
`n ≤ 149` for `g = 12`; `n ≤ 215` for `g = 13`; `n ≤ 274` for `g = 14`) satisfies `HasPower G`. -/
theorem cubic_girth9_to_14_above_moore_hasPower (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : ∀ v : V, G.degree v = 3) (hn : 0 < Fintype.card V) :
    (GirthAtLeast G 9 → Fintype.card V ≤ 131 → HasPower G) ∧
    (GirthAtLeast G 10 → Fintype.card V ≤ 131 → HasPower G) ∧
    (GirthAtLeast G 11 → Fintype.card V ≤ 143 → HasPower G) ∧
    (GirthAtLeast G 12 → Fintype.card V ≤ 149 → HasPower G) ∧
    (GirthAtLeast G 13 → Fintype.card V ≤ 215 → HasPower G) ∧
    (GirthAtLeast G 14 → Fintype.card V ≤ 274 → HasPower G) :=
  ⟨fun hg hle => cubic_girth9_le_131_hasPower G hreg hn hle hg,
   fun hg hle => cubic_girth9_le_131_hasPower G hreg hn hle
     (fun v p hp => le_trans (by decide : 9 ≤ 10) (hg v p hp)),
   fun hg hle => cubic_girth11_le_143_hasPower G hreg hn hle hg,
   fun hg hle => cubic_girth12_le_149_hasPower G hreg hn hle hg,
   fun hg hle => cubic_girth13_le_215_hasPower G hreg hn hle hg,
   fun hg hle => cubic_girth14_le_274_hasPower G hreg hn hle hg⟩

end HighGirthClosure

#print axioms chebMat_mul_cubic
#print axioms two_square_cheb_trace_lb
#print axioms cert_trace_surplus_of_two_square
#print axioms nonSimpleTaillessCount_le_sum_alpha
#print axioms hasPower_of_cert
#print axioms cubic_girth6_le_14_hasPower
#print axioms cubic_girth7_le_33_hasPower
#print axioms cubic_girth11_le_143_hasPower
#print axioms cubic_girth12_le_149_hasPower
#print axioms cubic_girth13_le_215_hasPower
#print axioms cubic_girth14_le_274_hasPower
#print axioms cubic_girth15_le_1483_hasPower
#print axioms cubic_girth8_le_131_hasPower
#print axioms cubic_girth9_to_14_above_moore_hasPower

end E64Wave8Agent2
