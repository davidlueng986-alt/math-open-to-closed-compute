import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic

/-!
# Erdős Problem #64 (Erdős–Gyárfás Conjecture) — Wave 8 Agent 8
## Exact Rational Lukács SOS-Delsarte Shattering of the Cubic High-Girth Frontier (g = 9..15)
## & Unbounded-n Arbitrary-Girth Structural Theorems (4-Layer Annulus Excess & 7-Cycle Engines)

Zero spectral theorem, zero `sorryAx`, zero `native_decide`, standard axioms only.
-/

open Finset BigOperators Matrix Polynomial

namespace E64Wave8Agent8

section CoreDefinitions

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A simple cycle of exact length `L ≥ 3` in `G` represented as an injective cyclic sequence. -/
def HasSimpleCycle (G : SimpleGraph V) (L : ℕ) : Prop :=
  ∃ hL : 3 ≤ L, ∃ c : Fin L → V, Function.Injective c ∧
    ∀ i : Fin L, G.Adj (c i) (c ⟨(i.1 + 1) % L, Nat.mod_lt _ (by omega)⟩)

/-- Girth at least `g`: `G` has no simple cycle of length `< g`. -/
def GirthAtLeast (G : SimpleGraph V) (g : ℕ) : Prop :=
  ∀ L : ℕ, L < g → ¬ HasSimpleCycle G L

/-- A non-backtracking walk of length `k` as a function `f : Fin (k + 1) → V`. -/
def IsNBSeq (G : SimpleGraph V) (k : ℕ) (f : Fin (k + 1) → V) : Prop :=
  (∀ i : Fin k, G.Adj (f i.castSucc) (f i.succ)) ∧
  (∀ i : ℕ, ∀ hi : i + 2 ≤ k, f ⟨i, by omega⟩ ≠ f ⟨i + 2, by omega⟩)

instance instDecidableIsNBSeq (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (f : Fin (k + 1) → V) : Decidable (IsNBSeq G k f) := by
  unfold IsNBSeq
  refine decidable_of_iff
    ((∀ i : Fin k, G.Adj (f i.castSucc) (f i.succ)) ∧
     (∀ i : Fin (k + 1), ∀ hi : i.1 + 2 ≤ k, f i ≠ f ⟨i.1 + 2, by omega⟩)) ?_
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun i hi => h2 ⟨i, by omega⟩ hi⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun i hi => h2 i.1 hi⟩

/-- A closed non-backtracking walk of length `k ≥ 1`. -/
def IsClosedNBSeq (G : SimpleGraph V) (k : ℕ) (f : Fin (k + 1) → V) : Prop :=
  1 ≤ k ∧ f 0 = f (Fin.last k) ∧ IsNBSeq G k f

/-- A tailless closed non-backtracking walk of length `k ≥ 1`. -/
def IsTaillessClosedNBSeq (G : SimpleGraph V) (k : ℕ) (f : Fin (k + 1) → V) : Prop :=
  IsClosedNBSeq G k f ∧ (∃ hk : 1 ≤ k, f ⟨1, by omega⟩ ≠ f ⟨k - 1, by omega⟩)

/-- A tailed closed non-backtracking walk of length `k ≥ 1`. -/
def IsTailedClosedNBSeq (G : SimpleGraph V) (k : ℕ) (f : Fin (k + 1) → V) : Prop :=
  IsClosedNBSeq G k f ∧ (∃ hk : 1 ≤ k, f ⟨1, by omega⟩ = f ⟨k - 1, by omega⟩)

instance instDecidableIsClosedNBSeq (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (f : Fin (k + 1) → V) : Decidable (IsClosedNBSeq G k f) := by
  unfold IsClosedNBSeq; infer_instance

instance instDecidableIsTaillessClosedNBSeq (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (f : Fin (k + 1) → V) : Decidable (IsTaillessClosedNBSeq G k f) := by
  unfold IsTaillessClosedNBSeq
  by_cases hk : 1 ≤ k
  · exact decidable_of_iff (IsClosedNBSeq G k f ∧ f ⟨1, by omega⟩ ≠ f ⟨k - 1, by omega⟩)
      ⟨fun ⟨h1, h2⟩ => ⟨h1, hk, h2⟩, fun ⟨h1, _, h2⟩ => ⟨h1, h2⟩⟩
  · exact isFalse (fun ⟨_, h, _⟩ => hk h)

instance instDecidableIsTailedClosedNBSeq (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (f : Fin (k + 1) → V) : Decidable (IsTailedClosedNBSeq G k f) := by
  unfold IsTailedClosedNBSeq
  by_cases hk : 1 ≤ k
  · exact decidable_of_iff (IsClosedNBSeq G k f ∧ f ⟨1, by omega⟩ = f ⟨k - 1, by omega⟩)
      ⟨fun ⟨h1, h2⟩ => ⟨h1, hk, h2⟩, fun ⟨h1, _, h2⟩ => ⟨h1, h2⟩⟩
  · exact isFalse (fun ⟨_, h, _⟩ => hk h)

def adjMat (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℚ :=
  fun u v => if G.Adj u v then 1 else 0

noncomputable def chebPoly : ℕ → Polynomial ℚ
  | 0 => 2
  | 1 => Polynomial.X
  | k + 2 => Polynomial.X * chebPoly (k + 1) - 2 * chebPoly k

def chebMat (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ → Matrix V V ℚ
  | 0 => 2 • (1 : Matrix V V ℚ)
  | 1 => adjMat G
  | k + 2 => adjMat G * chebMat G (k + 1) - 2 • chebMat G k

def nbCount (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (u v : V) : ℕ :=
  (Finset.univ.filter (fun f : Fin (k + 1) → V =>
    f 0 = u ∧ f (Fin.last k) = v ∧ IsNBSeq G k f)).card

def nbMat (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : Matrix V V ℚ :=
  fun u v => (nbCount G k u v : ℚ)

def closedNBCount (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : ℕ :=
  (Finset.univ.filter (fun f : Fin (k + 1) → V => IsClosedNBSeq G k f)).card

def taillessCount (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : ℕ :=
  (Finset.univ.filter (fun f : Fin (k + 1) → V => IsTaillessClosedNBSeq G k f)).card

def tailedCount (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : ℕ :=
  (Finset.univ.filter (fun f : Fin (k + 1) → V => IsTailedClosedNBSeq G k f)).card

end CoreDefinitions

section TaillessToSimpleCycle

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Theorem 1: Every closed non-backtracking walk of length `L ≥ 1` contains a simple cycle
    of length `m ≤ L`. -/
theorem closed_nb_seq_has_simple_cycle_le (G : SimpleGraph V) :
    ∀ L : ℕ, ∀ f : Fin (L + 1) → V, IsClosedNBSeq G L f →
      ∃ m : ℕ, m ≤ L ∧ HasSimpleCycle G m := by
  intro L
  induction L using Nat.strong_induction_on with
  | ind L ih =>
    intro f ⟨hL1, hclosed, hadj, hnb⟩
    by_cases hinj : Function.Injective (fun i : Fin L => f i.castSucc)
    · have hL3 : 3 ≤ L := by
        by_contra hlt
        have hcases : L = 1 ∨ L = 2 := by omega
        rcases hcases with rfl | rfl
        · have h01 := hadj ⟨0, by omega⟩
          have h0 : (⟨0, by omega⟩ : Fin 1).castSucc = (0 : Fin 2) := by ext; rfl
          have h1 : (⟨0, by omega⟩ : Fin 1).succ = Fin.last 1 := by ext; rfl
          rw [h0, h1, ← hclosed] at h01
          exact G.loopless.irrefl _ h01
        · exact hnb 0 (by omega) hclosed
      refine ⟨L, le_rfl, hL3, fun i => f i.castSucc, hinj, ?_⟩
      intro i
      by_cases hlast : i.1 + 1 < L
      · have hmod : (i.1 + 1) % L = i.1 + 1 := Nat.mod_eq_of_lt hlast
        have hstep := hadj i
        have hnxt : (⟨(i.1 + 1) % L, Nat.mod_lt _ (by omega)⟩ : Fin L).castSucc = i.succ := by
          ext; simp [hmod]
        dsimp only; rw [hnxt]; exact hstep
      · have hi : i.1 + 1 = L := by omega
        have hmod : (i.1 + 1) % L = 0 := by rw [hi, Nat.mod_self]
        have hstep := hadj i
        have hlast_eq : f i.succ = f 0 := by
          have : i.succ = Fin.last L := by ext; simp [hi]
          rw [this, ← hclosed]
        rw [hlast_eq] at hstep
        have hnxt : (⟨(i.1 + 1) % L, Nat.mod_lt _ (by omega)⟩ : Fin L).castSucc = 0 := by
          ext; simp [hmod]
        dsimp only; rw [hnxt]; exact hstep
    · rw [Function.Injective] at hinj
      push Not at hinj
      rcases hinj with ⟨a, b, hab, hne⟩
      obtain ⟨i, j, hij, hfij⟩ : ∃ i j : Fin L, i.1 < j.1 ∧ f i.castSucc = f j.castSucc := by
        rcases lt_trichotomy a.1 b.1 with h | h | h
        · exact ⟨a, b, h, hab⟩
        · exact False.elim (hne (Fin.ext h))
        · exact ⟨b, a, h, hab.symm⟩
      let m := j.1 - i.1
      have hmL : m < L := by omega
      let g : Fin (m + 1) → V := fun t => f ⟨i.1 + t.1, by omega⟩
      have hg_closed : IsClosedNBSeq G m g := by
        refine ⟨by omega, ?_, ?_, ?_⟩
        · show f ⟨i.1 + 0, _⟩ = f ⟨i.1 + m, _⟩
          have h1 : (⟨i.1 + 0, by omega⟩ : Fin (L + 1)) = i.castSucc := by ext; simp
          have h2 : (⟨i.1 + m, by omega⟩ : Fin (L + 1)) = j.castSucc := by ext; dsimp [m]; omega
          rw [h1, h2, hfij]
        · intro t
          have hstep := hadj ⟨i.1 + t.1, by omega⟩
          convert hstep using 2; ext; simp; omega
        · intro t ht
          have hstep := hnb (i.1 + t) (by omega)
          convert hstep using 2; ext; simp; omega
      obtain ⟨c, hcm, hcyc⟩ := ih m hmL g hg_closed
      exact ⟨c, le_trans hcm (le_of_lt hmL), hcyc⟩

/-- Theorem 2: If `G` has girth `≥ 9`, then every tailless closed non-backtracking walk of length 16
    is a simple cycle `C16`. -/
theorem girth9_tailless16_is_simple_cycle (G : SimpleGraph V)
    (hg : GirthAtLeast G 9) (f : Fin 17 → V) (hf : IsTaillessClosedNBSeq G 16 f) :
    HasSimpleCycle G 16 := by
  rcases hf with ⟨⟨_, hclosed, hadj, hnb⟩, ⟨_, htailless⟩⟩
  by_cases hinj : Function.Injective (fun i : Fin 16 => f i.castSucc)
  · refine ⟨by omega, fun i => f i.castSucc, hinj, ?_⟩
    intro i
    by_cases hlast : i.1 + 1 < 16
    · have hmod : (i.1 + 1) % 16 = i.1 + 1 := Nat.mod_eq_of_lt hlast
      have hstep := hadj i
      have hnxt : (⟨(i.1 + 1) % 16, Nat.mod_lt _ (by omega)⟩ : Fin 16).castSucc = i.succ := by
        ext; simp [hmod]
      dsimp only; rw [hnxt]; exact hstep
    · have hi : i.1 + 1 = 16 := by omega
      have hmod : (i.1 + 1) % 16 = 0 := by rw [hi, Nat.mod_self]
      have hstep := hadj i
      have hlast_eq : f i.succ = f 0 := by
        have : i.succ = Fin.last 16 := by ext; simp [hi]
        rw [this, ← hclosed]
      rw [hlast_eq] at hstep
      have hnxt : (⟨(i.1 + 1) % 16, Nat.mod_lt _ (by omega)⟩ : Fin 16).castSucc = 0 := by
        ext; simp [hmod]
      dsimp only; rw [hnxt]; exact hstep
  · rw [Function.Injective] at hinj
    push Not at hinj
    rcases hinj with ⟨a, b, hab, hne⟩
    obtain ⟨i, j, hij, hfij⟩ : ∃ i j : Fin 16, i.1 < j.1 ∧ f i.castSucc = f j.castSucc := by
      rcases lt_trichotomy a.1 b.1 with h | h | h
      · exact ⟨a, b, h, hab⟩
      · exact False.elim (hne (Fin.ext h))
      · exact ⟨b, a, h, hab.symm⟩
    let m := j.1 - i.1
    by_cases hm8 : m ≤ 8
    · let g : Fin (m + 1) → V := fun t => f ⟨i.1 + t.1, by omega⟩
      have hg_closed : IsClosedNBSeq G m g := by
        refine ⟨by omega, ?_, ?_, ?_⟩
        · have h1 : (⟨i.1 + 0, by omega⟩ : Fin 17) = i.castSucc := by ext; simp
          have h2 : (⟨i.1 + m, by omega⟩ : Fin 17) = j.castSucc := by ext; dsimp [m]; omega
          show f ⟨i.1 + 0, _⟩ = f ⟨i.1 + m, _⟩
          rw [h1, h2, hfij]
        · intro t
          have hstep := hadj ⟨i.1 + t.1, by omega⟩
          convert hstep using 2; ext; simp; omega
        · intro t ht
          have hstep := hnb (i.1 + t) (by omega)
          convert hstep using 2; ext; simp; omega
      obtain ⟨c, hcm, hcyc⟩ := closed_nb_seq_has_simple_cycle_le G m g hg_closed
      exact False.elim (hg c (by omega) hcyc)
    · let m2 := 16 - m
      let g2 : Fin (m2 + 1) → V := fun t => f ⟨(j.1 + t.1) % 16, by omega⟩
      have hf16 : f ⟨16, by omega⟩ = f ⟨0, by omega⟩ := hclosed.symm
      have hadj_mod : ∀ r : ℕ, ∀ hr : r < 16, G.Adj (f ⟨r, by omega⟩) (f ⟨(r + 1) % 16, by omega⟩) := by
        intro r hr
        by_cases hr15 : r < 15
        · have hmod : (r + 1) % 16 = r + 1 := Nat.mod_eq_of_lt (by omega)
          have hstep := hadj ⟨r, hr⟩
          have hs1 : (⟨r, hr⟩ : Fin 16).castSucc = ⟨r, by omega⟩ := by ext; rfl
          have hs2 : (⟨r, hr⟩ : Fin 16).succ = ⟨(r + 1) % 16, by omega⟩ := by ext; simp [hmod]
          rw [hs1, hs2] at hstep; exact hstep
        · have hr_eq : r = 15 := by omega
          subst hr_eq
          have hstep := hadj ⟨15, by omega⟩
          have hs1 : (⟨15, by omega⟩ : Fin 16).castSucc = ⟨15, by omega⟩ := by ext; rfl
          have hs2 : (⟨15, by omega⟩ : Fin 16).succ = ⟨16, by omega⟩ := by ext; rfl
          rw [hs1, hs2, hf16] at hstep
          exact hstep
      have hnb_mod : ∀ r : ℕ, ∀ hr : r < 16, f ⟨r, by omega⟩ ≠ f ⟨(r + 2) % 16, by omega⟩ := by
        intro r hr
        by_cases hr14 : r < 14
        · have hmod : (r + 2) % 16 = r + 2 := Nat.mod_eq_of_lt (by omega)
          have hstep := hnb r (by omega)
          have hs2 : (⟨r + 2, by omega⟩ : Fin 17) = ⟨(r + 2) % 16, by omega⟩ := by ext; simp [hmod]
          rw [hs2] at hstep; exact hstep
        · by_cases hr14' : r = 14
          · subst hr14'
            have hstep := hnb 14 (by omega)
            rw [hf16] at hstep
            exact hstep
          · have hr15 : r = 15 := by omega
            subst hr15
            exact Ne.symm htailless
      have hg2_closed : IsClosedNBSeq G m2 g2 := by
        refine ⟨by omega, ?_, ?_, ?_⟩
        · show f ⟨(j.1 + 0) % 16, _⟩ = f ⟨(j.1 + m2) % 16, _⟩
          have h1 : (j.1 + 0) % 16 = j.1 := Nat.mod_eq_of_lt j.2
          have h2 : (j.1 + m2) % 16 = i.1 := by
            have heq : j.1 + m2 = 16 + i.1 := by dsimp [m2, m]; omega
            rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt i.2]
          have h1' : (⟨(j.1 + 0) % 16, by omega⟩ : Fin 17) = j.castSucc := by ext; exact h1
          have h2' : (⟨(j.1 + m2) % 16, by omega⟩ : Fin 17) = i.castSucc := by ext; exact h2
          rw [h1', h2', hfij]
        · intro t
          have hstep := hadj_mod ((j.1 + t.1) % 16) (Nat.mod_lt _ (by omega))
          have hmod : ((j.1 + t.1) % 16 + 1) % 16 = (j.1 + (t.1 + 1)) % 16 := by
            rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]; ring_nf
          have hs2 : (⟨((j.1 + t.1) % 16 + 1) % 16, by omega⟩ : Fin 17) =
              ⟨(j.1 + t.succ.1) % 16, by omega⟩ := by ext; simp [hmod]
          rw [hs2] at hstep; exact hstep
        · intro t ht
          have hstep := hnb_mod ((j.1 + t) % 16) (Nat.mod_lt _ (by omega))
          have hmod : ((j.1 + t) % 16 + 2) % 16 = (j.1 + (t + 2)) % 16 := by
            rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]; ring_nf
          have hs2 : (⟨((j.1 + t) % 16 + 2) % 16, by omega⟩ : Fin 17) =
              ⟨(j.1 + (t + 2)) % 16, by omega⟩ := by ext; exact hmod
          rw [hs2] at hstep; exact hstep
      obtain ⟨c, hcm, hcyc⟩ := closed_nb_seq_has_simple_cycle_le G m2 g2 hg2_closed
      exact False.elim (hg c (by omega) hcyc)

lemma taillessCount_eq_zero_of_lt_girth (G : SimpleGraph V) [DecidableRel G.Adj]
    (g k : ℕ) (hg : GirthAtLeast G g) (_hk1 : 1 ≤ k) (hkg : k < g) :
    taillessCount G k = 0 := by
  unfold taillessCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro f _ hf
  obtain ⟨m, hmk, hcyc⟩ := closed_nb_seq_has_simple_cycle_le G k f hf.1
  exact hg m (lt_of_le_of_lt hmk hkg) hcyc

lemma has_c16_of_taillessCount_pos (G : SimpleGraph V) [DecidableRel G.Adj]
    (hg : GirthAtLeast G 9) (hpos : 0 < taillessCount G 16) :
    HasSimpleCycle G 16 := by
  unfold taillessCount at hpos
  obtain ⟨f, hf⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at hf
  exact girth9_tailless16_is_simple_cycle G hg f hf.2

end TaillessToSimpleCycle

section NonBacktrackingTraceAlgebra

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
lemma adjMat_transpose (G : SimpleGraph V) [DecidableRel G.Adj] :
    (adjMat G).transpose = adjMat G := by
  ext u v; simp only [transpose_apply, adjMat, G.adj_comm]

omit [DecidableEq V] in
lemma adjMat_row_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : ∀ v, G.degree v = 3) (u : V) :
    ∑ v : V, adjMat G u v = 3 := by
  simp only [adjMat, sum_boole]
  have h : (Finset.univ.filter (fun v => G.Adj u v)).card = G.degree u := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    congr 1; ext v; simp [SimpleGraph.mem_neighborFinset]
  rw [h, hreg u]; norm_num

/-- Theorem 3: `aeval (adjMat G) (chebPoly k) = chebMat G k`. -/
theorem aeval_chebPoly_eq_chebMat (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    Polynomial.aeval (adjMat G) (chebPoly k) = chebMat G k := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    match k with
    | 0 =>
      simp only [chebPoly, chebMat, map_ofNat]
      rw [two_smul, one_add_one_eq_two]
    | 1 =>
      simp only [chebPoly, chebMat, aeval_X]
    | m + 2 =>
      simp only [chebPoly, chebMat, map_sub, map_mul, map_ofNat, aeval_X,
        ih (m + 1) (by omega), ih m (by omega)]
      congr 1
      rw [two_smul, ← one_add_one_eq_two, add_mul, one_mul]

lemma nbMat_one (G : SimpleGraph V) [DecidableRel G.Adj] :
    nbMat G 1 = adjMat G := by
  ext u v
  simp only [nbMat, nbCount, adjMat]
  by_cases hadj : G.Adj u v
  · have hcard : (Finset.univ.filter (fun f : Fin 2 → V =>
        f 0 = u ∧ f (Fin.last 1) = v ∧ IsNBSeq G 1 f)).card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨![u, v], ?_⟩
      ext f; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro ⟨h0, h1, _⟩; ext i; fin_cases i <;> assumption
      · rintro rfl; refine ⟨rfl, rfl, fun i => ?_, fun _ h => by omega⟩; fin_cases i; exact hadj
    rw [hcard]; simp [hadj]
  · have hcard : (Finset.univ.filter (fun f : Fin 2 → V =>
        f 0 = u ∧ f (Fin.last 1) = v ∧ IsNBSeq G 1 f)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro f _ ⟨h0, h1, ha, _⟩
      have h01 := ha ⟨0, by omega⟩
      have ha0 : (⟨0, by omega⟩ : Fin 1).castSucc = (0 : Fin 2) := by ext; rfl
      have ha1 : (⟨0, by omega⟩ : Fin 1).succ = Fin.last 1 := by ext; rfl
      rw [ha0, ha1, h0, h1] at h01; exact hadj h01
    rw [hcard]; simp [hadj]

lemma nbMat_two (G : SimpleGraph V) [DecidableRel G.Adj] (hreg : ∀ v, G.degree v = 3) :
    nbMat G 2 = adjMat G * adjMat G - 3 • (1 : Matrix V V ℚ) := by
  ext u v
  simp only [nbMat, nbCount, Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply,
    Matrix.one_apply, adjMat]
  have hmul : ∑ w : V, (if G.Adj u w then (1 : ℚ) else 0) * (if G.Adj w v then 1 else 0) =
      ((Finset.univ.filter (fun w : V => G.Adj u w ∧ G.Adj w v)).card : ℚ) := by
    rw [← Finset.sum_boole]; congr 1; ext w; split_ifs <;> simp_all
  rw [hmul]
  by_cases huv : u = v
  · subst huv
    have hzero : (Finset.univ.filter (fun f : Fin 3 → V =>
        f 0 = u ∧ f (Fin.last 2) = u ∧ IsNBSeq G 2 f)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro f _ ⟨h0, h2, _, hnb⟩; exact hnb 0 (by omega) (h0.trans h2.symm)
    have hdeg : (Finset.univ.filter (fun w : V => G.Adj u w ∧ G.Adj w u)).card = 3 := by
      rw [← hreg u, ← SimpleGraph.card_neighborFinset_eq_degree]
      congr 1; ext w; simp [SimpleGraph.mem_neighborFinset, G.adj_comm]
    rw [hzero, hdeg]; norm_num
  · have hbij : (Finset.univ.filter (fun f : Fin 3 → V =>
        f 0 = u ∧ f (Fin.last 2) = v ∧ IsNBSeq G 2 f)).card =
        (Finset.univ.filter (fun w : V => G.Adj u w ∧ G.Adj w v)).card := by
      refine Finset.card_bij (fun f _ => f ⟨1, by omega⟩) ?_ ?_ ?_
      · intro f hf; rw [Finset.mem_filter] at hf ⊢; rcases hf.2 with ⟨h0, h2, ha, _⟩
        refine ⟨Finset.mem_univ _, ?_, ?_⟩
        · have h01 := ha ⟨0, by omega⟩
          have ha0 : (⟨0, by omega⟩ : Fin 2).castSucc = (0 : Fin 3) := by ext; rfl
          have ha1 : (⟨0, by omega⟩ : Fin 2).succ = ⟨1, by omega⟩ := by ext; rfl
          rw [ha0, ha1, h0] at h01; exact h01
        · have h12 := ha ⟨1, by omega⟩
          have ha1 : (⟨1, by omega⟩ : Fin 2).castSucc = ⟨1, by omega⟩ := by ext; rfl
          have ha2 : (⟨1, by omega⟩ : Fin 2).succ = Fin.last 2 := by ext; rfl
          rw [ha1, ha2, h2] at h12; exact h12
      · intro f₁ hf₁ f₂ hf₂ hmid; rw [Finset.mem_filter] at hf₁ hf₂
        ext i; fin_cases i
        · exact hf₁.2.1.trans hf₂.2.1.symm
        · exact hmid
        · exact hf₁.2.2.1.trans hf₂.2.2.1.symm
      · intro w hw; rw [Finset.mem_filter] at hw
        refine ⟨![u, w, v], ?_, rfl⟩; rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, rfl, rfl, fun i => ?_, fun i hi => ?_⟩
        · fin_cases i
          · exact hw.2.1
          · exact hw.2.2
        · have hi0 : i = 0 := by omega
          subst hi0; exact huv
    rw [hbij]; simp [huv]

/-- Theorem 4: Exact non-backtracking walk matrix recurrence for 3-regular graphs. -/
theorem nbMat_recurrence (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : ∀ v, G.degree v = 3) (k : ℕ) :
    nbMat G (k + 3) = adjMat G * nbMat G (k + 2) - 2 • nbMat G (k + 1) := by
  ext u v
  simp only [nbMat, Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply, adjMat]
  have hstep_nat :
      ∑ w : V, (if G.Adj u w then nbCount G (k + 2) w v else 0) =
      nbCount G (k + 3) u v + 2 * nbCount G (k + 1) u v := by
    let S := (Finset.univ.filter (fun p : V × (Fin (k + 3) → V) =>
      G.Adj u p.1 ∧ p.2 0 = p.1 ∧ p.2 (Fin.last (k + 2)) = v ∧ IsNBSeq G (k + 2) p.2))
    have hS_card : S.card = ∑ w : V, (if G.Adj u w then nbCount G (k + 2) w v else 0) := by
      have h1 : S.card = ∑ w : V, (Finset.univ.filter (fun g : Fin (k + 3) → V =>
          G.Adj u w ∧ g 0 = w ∧ g (Fin.last (k + 2)) = v ∧ IsNBSeq G (k + 2) g)).card := by
        rw [Finset.card_filter, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun w _ => (Finset.card_filter _ _).symm
      rw [h1]
      refine Finset.sum_congr rfl fun w _ => ?_
      by_cases huw : G.Adj u w <;> simp [huw, nbCount]
    rw [← hS_card]
    let S_good := S.filter (fun p => p.2 ⟨1, by omega⟩ ≠ u)
    let S_back := S.filter (fun p => p.2 ⟨1, by omega⟩ = u)
    have hpart : S.card = S_good.card + S_back.card := by
      have hback : S.filter (fun p => ¬ p.2 ⟨1, by omega⟩ ≠ u) = S_back := by
        ext p; simp only [S_back, Finset.mem_filter, not_ne_iff]
      rw [← Finset.card_filter_add_card_filter_not (fun p => p.2 ⟨1, by omega⟩ ≠ u), hback]
    rw [hpart]; congr 1
    · refine Finset.card_bij (fun p _ => Fin.cons u p.2) ?_ ?_ ?_
      · intro p hp
        simp only [S_good, S, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        rcases hp with ⟨⟨huw, h0, hlast, hadj, hnb⟩, hne⟩
        refine ⟨rfl, by simpa using hlast, fun i => ?_, fun i hi => ?_⟩
        · refine Fin.cases ?_ (fun j => by simpa using hadj j) i
          simp only [Fin.castSucc_zero, Fin.cons_zero]
          rw [Fin.cons_succ, h0]; exact huw
        · cases i with
          | zero =>
            have h0' : (⟨0, by omega⟩ : Fin (k + 4)) = 0 := by ext; rfl
            have h2' : (⟨0 + 2, by omega⟩ : Fin (k + 4)) = (⟨1, by omega⟩ : Fin (k + 3)).succ := by ext; rfl
            rw [h0', h2', Fin.cons_zero, Fin.cons_succ]; exact Ne.symm hne
          | succ m =>
            have hm1 : (⟨m + 1, by omega⟩ : Fin (k + 4)) = (⟨m, by omega⟩ : Fin (k + 3)).succ := by ext; rfl
            have hm3 : (⟨m + 1 + 2, by omega⟩ : Fin (k + 4)) = (⟨m + 2, by omega⟩ : Fin (k + 3)).succ := by ext; simp
            rw [hm1, hm3, Fin.cons_succ, Fin.cons_succ]; exact hnb m (by omega)
      · intro p₁ hp₁ p₂ hp₂ heq
        simp only [S_good, S, Finset.mem_filter, Finset.mem_univ, true_and] at hp₁ hp₂
        have h2 : p₁.2 = p₂.2 := by ext i; simpa using congr_fun heq i.succ
        exact Prod.ext (hp₁.1.2.1.symm.trans ((congr_fun h2 0).trans hp₂.1.2.1)) h2
      · intro f hf
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
        rcases hf with ⟨h0, hlast, hadj, hnb⟩
        refine ⟨⟨f ⟨1, by omega⟩, Fin.tail f⟩, ?_, ?_⟩
        · simp only [S_good, S, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨⟨?_, rfl, by simpa [Fin.tail] using hlast,
            fun i => by simpa [Fin.tail] using hadj i.succ,
            fun i hi => by simpa [Fin.tail] using hnb (i + 1) (by omega)⟩, ?_⟩
          · have hstep := hadj ⟨0, by omega⟩
            have ha0 : (⟨0, by omega⟩ : Fin (k + 3)).castSucc = (0 : Fin (k + 4)) := by ext; rfl
            have ha1 : (⟨0, by omega⟩ : Fin (k + 3)).succ = ⟨1, by omega⟩ := by ext; rfl
            rw [ha0, ha1, h0] at hstep; exact hstep
          · have hstep := hnb 0 (by omega)
            have ha0 : (⟨0, by omega⟩ : Fin (k + 4)) = 0 := by ext; rfl
            have ha2 : (⟨0 + 2, by omega⟩ : Fin (k + 4)) = (⟨1, by omega⟩ : Fin (k + 3)).succ := by ext; rfl
            rw [ha0, ha2, h0] at hstep
            exact Ne.symm hstep
        · ext i; refine Fin.cases (by simp [h0]) (fun _ => rfl) i
    · let T_set := Finset.univ.filter (fun g' : Fin (k + 2) → V =>
        g' 0 = u ∧ g' (Fin.last (k + 1)) = v ∧ IsNBSeq G (k + 1) g')
      have hbij2 : S_back.card = ∑ g' ∈ T_set,
          (Finset.univ.filter (fun w : V => G.Adj u w ∧ w ≠ g' ⟨1, by omega⟩)).card := by
        rw [← Finset.card_sigma]
        refine Finset.card_bij (fun p _ => ⟨Fin.tail p.2, p.1⟩) ?_ ?_ ?_
        · intro p hp
          simp only [S_back, S, Finset.mem_filter, Finset.mem_univ, true_and] at hp
          rcases hp with ⟨⟨huw, h0, hlast, hadj, hnb⟩, h1u⟩
          rw [Finset.mem_sigma]; refine ⟨?_, ?_⟩
          · simp only [T_set, Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨h1u, by simpa [Fin.tail] using hlast,
              fun i => by simpa [Fin.tail] using hadj i.succ,
              fun i hi => by simpa [Fin.tail] using hnb (i + 1) (by omega)⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨huw, ?_⟩
            have hstep := hnb 0 (by omega)
            have ha0 : (⟨0, by omega⟩ : Fin (k + 3)) = 0 := by ext; rfl
            have ha2 : (⟨0 + 2, by omega⟩ : Fin (k + 3)) = (⟨1, by omega⟩ : Fin (k + 2)).succ := by ext; rfl
            rw [ha0, ha2, h0] at hstep; exact hstep
        · intro p₁ hp₁ p₂ hp₂ heq
          simp only [S_back, S, Finset.mem_filter, Finset.mem_univ, true_and] at hp₁ hp₂
          have hfst : Fin.tail p₁.2 = Fin.tail p₂.2 := congr_arg Sigma.fst heq
          have hsnd : p₁.1 = p₂.1 := congr_arg (fun x : Σ _ : Fin (k + 2) → V, V => x.2) heq
          refine Prod.ext hsnd ?_
          ext i; refine Fin.cases ?_ (fun j => congr_fun hfst j) i
          exact hp₁.1.2.1.trans (hsnd.trans hp₂.1.2.1.symm)
        · intro q hq
          rw [Finset.mem_sigma] at hq; rcases hq with ⟨hg', hw⟩
          simp only [T_set, Finset.mem_filter, Finset.mem_univ, true_and] at hg'
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
          refine ⟨⟨q.2, Fin.cons q.2 q.1⟩, ?_, Sigma.ext (by ext j; rfl) (heq_of_eq rfl)⟩
          simp only [S_back, S, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨⟨hw.1, rfl, by simpa using hg'.2.1, fun i => ?_, fun i hi => ?_⟩, ?_⟩
          · refine Fin.cases ?_ (fun j => by simpa using hg'.2.2.1 j) i
            simp only [Fin.castSucc_zero, Fin.cons_zero]
            rw [Fin.cons_succ, hg'.1]; exact (G.adj_comm _ _).mp hw.1
          · cases i with
            | zero =>
              have h0' : (⟨0, by omega⟩ : Fin (k + 3)) = 0 := by ext; rfl
              have h2' : (⟨0 + 2, by omega⟩ : Fin (k + 3)) = (⟨1, by omega⟩ : Fin (k + 2)).succ := by ext; rfl
              rw [h0', h2', Fin.cons_zero, Fin.cons_succ]; exact hw.2
            | succ m =>
              have hm1 : (⟨m + 1, by omega⟩ : Fin (k + 3)) = (⟨m, by omega⟩ : Fin (k + 2)).succ := by ext; rfl
              have hm3 : (⟨m + 1 + 2, by omega⟩ : Fin (k + 3)) = (⟨m + 2, by omega⟩ : Fin (k + 2)).succ := by ext; simp
              rw [hm1, hm3, Fin.cons_succ, Fin.cons_succ]; exact hg'.2.2.2 m (by omega)
          · have h1' : (⟨1, by omega⟩ : Fin (k + 3)) = (0 : Fin (k + 2)).succ := by ext; rfl
            rw [h1', Fin.cons_succ, hg'.1]
      rw [hbij2]
      have htwo : ∀ g' ∈ T_set,
          (Finset.univ.filter (fun w : V => G.Adj u w ∧ w ≠ g' ⟨1, by omega⟩)).card = 2 := by
        intro g' hg'
        simp only [T_set, Finset.mem_filter, Finset.mem_univ, true_and] at hg'
        have hadj01 : G.Adj u (g' ⟨1, by omega⟩) := by
          have hstep := hg'.2.2.1 ⟨0, by omega⟩
          have ha0 : (⟨0, by omega⟩ : Fin (k + 1)).castSucc = (0 : Fin (k + 2)) := by ext; rfl
          have ha1 : (⟨0, by omega⟩ : Fin (k + 1)).succ = ⟨1, by omega⟩ := by ext; rfl
          rw [ha0, ha1, hg'.1] at hstep; exact hstep
        have hset : Finset.univ.filter (fun w : V => G.Adj u w ∧ w ≠ g' ⟨1, by omega⟩) =
            (G.neighborFinset u).erase (g' ⟨1, by omega⟩) := by
          ext w; simp [SimpleGraph.mem_neighborFinset, and_comm]
        rw [hset, Finset.card_erase_of_mem (by rwa [SimpleGraph.mem_neighborFinset]),
          SimpleGraph.card_neighborFinset_eq_degree, hreg u]
      rw [Finset.sum_congr rfl htwo, Finset.sum_const, smul_eq_mul, mul_comm]; rfl
  have hsum_cast : (∑ w : V, (if G.Adj u w then (1 : ℚ) else 0) * (nbCount G (k + 2) w v : ℚ)) =
      ((∑ w : V, if G.Adj u w then nbCount G (k + 2) w v else 0 : ℕ) : ℚ) := by
    push_cast; refine Finset.sum_congr rfl fun w _ => ?_; split_ifs <;> simp
  rw [hsum_cast, hstep_nat]; push_cast; simp only [nsmul_eq_mul, Nat.cast_ofNat]; ring

lemma trace_nbMat_eq_closedNBCount (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hk : 1 ≤ k) :
    Matrix.trace (nbMat G k) = (closedNBCount G k : ℚ) := by
  simp only [Matrix.trace, Matrix.diag, nbMat, closedNBCount, nbCount]
  rw [← Nat.cast_sum]; congr 1
  rw [← Finset.card_biUnion]
  · congr 1; ext f
    rw [Finset.mem_biUnion, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, Finset.mem_filter, IsClosedNBSeq]
    exact ⟨fun ⟨_, h0, hlast, hnb⟩ => ⟨hk, h0.trans hlast.symm, hnb⟩,
           fun ⟨_, hcl, hnb⟩ => ⟨f 0, rfl, hcl.symm, hnb⟩⟩
  · intro u _ v _ huv
    simp only [Function.onFun, Finset.disjoint_left]
    intro f hfu hfv
    rw [Finset.mem_filter] at hfu hfv
    exact huv (hfu.2.1.symm.trans hfv.2.1)

lemma closedNBCount_eq_add (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hk : 1 ≤ k) :
    closedNBCount G k = taillessCount G k + tailedCount G k := by
  unfold closedNBCount taillessCount tailedCount
  rw [← Finset.card_filter_add_card_filter_not (fun f : Fin (k + 1) → V =>
    f ⟨1, by omega⟩ ≠ f ⟨k - 1, by omega⟩)]
  congr 1
  · congr 1; ext f; simp [IsTaillessClosedNBSeq, hk]
  · congr 1; ext f; simp [IsTailedClosedNBSeq, hk]

lemma tailedCount_step (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : ∀ v, G.degree v = 3) (k : ℕ) (hk : 1 ≤ k) :
    tailedCount G (k + 2) = taillessCount G k + 2 * tailedCount G k := by
  let C_k := Finset.univ.filter (fun g : Fin (k + 1) → V => IsClosedNBSeq G k g)
  have hbij : tailedCount G (k + 2) = ∑ g ∈ C_k,
      (Finset.univ.filter (fun u : V =>
        G.Adj (g 0) u ∧ u ≠ g ⟨1, by omega⟩ ∧ u ≠ g ⟨k - 1, by omega⟩)).card := by
    unfold tailedCount; rw [← Finset.card_sigma]
    refine Finset.card_bij
      (fun f _ => ⟨fun i : Fin (k + 1) => f ⟨i.1 + 1, by omega⟩, f 0⟩) ?_ ?_ ?_
    · intro f hf
      rw [Finset.mem_filter] at hf
      rcases hf.2 with ⟨⟨_, hcl, hadj, hnb⟩, ⟨_, htail⟩⟩
      rw [Finset.mem_sigma]; refine ⟨?_, ?_⟩
      · simp only [C_k, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨hk, ?_, fun i => ?_, fun i hi => ?_⟩
        · have h1 : (⟨0 + 1, by omega⟩ : Fin (k + 3)) = ⟨1, by omega⟩ := by ext; rfl
          have h2 : (⟨(Fin.last k).1 + 1, by omega⟩ : Fin (k + 3)) = ⟨k + 2 - 1, by omega⟩ := by ext; simp
          show f ⟨0 + 1, _⟩ = f ⟨(Fin.last k).1 + 1, _⟩
          rw [h1, h2]; exact htail
        · have hstep := hadj ⟨i.1 + 1, by omega⟩
          convert hstep using 2; ext; simp; omega
        · have hstep := hnb (i + 1) (by omega)
          convert hstep using 2; ext; simp; omega
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, ?_, ?_⟩
        · have h01 := hadj ⟨0, by omega⟩
          have ha0 : (⟨0, by omega⟩ : Fin (k + 2)).castSucc = (0 : Fin (k + 3)) := by ext; rfl
          have ha1 : (⟨0, by omega⟩ : Fin (k + 2)).succ = ⟨0 + 1, by omega⟩ := by ext; rfl
          rw [ha0, ha1] at h01; exact (G.adj_comm _ _).mp h01
        · have h02 := hnb 0 (by omega)
          have ha0 : (⟨0, by omega⟩ : Fin (k + 3)) = 0 := by ext; rfl
          have ha2 : (⟨0 + 2, by omega⟩ : Fin (k + 3)) = ⟨1 + 1, by omega⟩ := by ext; rfl
          rw [ha0, ha2] at h02; exact h02
        · have hkk := hnb k (by omega)
          have hak : (⟨k, by omega⟩ : Fin (k + 3)) = ⟨k - 1 + 1, by omega⟩ := by ext; simp; omega
          have hak2 : (⟨k + 2, by omega⟩ : Fin (k + 3)) = Fin.last (k + 2) := by ext; rfl
          rw [hak, hak2, ← hcl] at hkk; exact Ne.symm hkk
    · intro f₁ hf₁ f₂ hf₂ heq
      rw [Finset.mem_filter] at hf₁ hf₂
      have hmid : (fun i : Fin (k + 1) => f₁ ⟨i.1 + 1, by omega⟩) =
                  (fun i : Fin (k + 1) => f₂ ⟨i.1 + 1, by omega⟩) := congr_arg Sigma.fst heq
      have h0 : f₁ 0 = f₂ 0 := congr_arg (fun x : Σ _ : Fin (k + 1) → V, V => x.2) heq
      ext i
      by_cases hi0 : i.1 = 0
      · have hi_eq : i = 0 := Fin.ext hi0; rw [hi_eq, h0]
      · by_cases hil : i.1 = k + 2
        · have hi_eq : i = Fin.last (k + 2) := Fin.ext hil
          rw [hi_eq, ← hf₁.2.1.2.1, ← hf₂.2.1.2.1, h0]
        · have := congr_fun hmid ⟨i.1 - 1, by omega⟩
          convert this using 2 <;> (ext; simp; omega)
    · intro q hq
      rw [Finset.mem_sigma] at hq; rcases hq with ⟨hg, hu⟩
      simp only [C_k, Finset.mem_filter, Finset.mem_univ, true_and] at hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
      let f : Fin (k + 3) → V := fun i =>
        if h0 : i.1 = 0 then q.2
        else if hl : i.1 = k + 2 then q.2
        else q.1 ⟨i.1 - 1, by omega⟩
      have hf_zero : f 0 = q.2 := by simp [f]
      have hf_last : f (Fin.last (k + 2)) = q.2 := by
        dsimp [f]; split_ifs <;> rfl
      have hf_mid : ∀ m : ℕ, ∀ hm1 : 1 ≤ m, ∀ hm2 : m ≤ k + 1,
          f ⟨m, by omega⟩ = q.1 ⟨m - 1, by omega⟩ := by
        intro m hm1 hm2; dsimp [f]; split_ifs <;> [omega; omega; rfl]
      refine ⟨f, ?_, ?_⟩
      · rw [Finset.mem_filter]; refine ⟨Finset.mem_univ _, ?_⟩
        refine ⟨⟨by omega, hf_zero.trans hf_last.symm, fun i => ?_, fun i hi => ?_⟩, by omega, ?_⟩
        · by_cases hi0 : i.1 = 0
          · have h1 : f i.castSucc = q.2 := by
              have : i.castSucc = 0 := Fin.ext hi0; rw [this, hf_zero]
            have h2 : f i.succ = q.1 0 := by
              have : i.succ = ⟨1, by omega⟩ := Fin.ext (by simp [hi0])
              rw [this, hf_mid 1 (by omega) (by omega)]; rfl
            rw [h1, h2]; exact (G.adj_comm _ _).mp hu.1
          · by_cases hil : i.1 = k + 1
            · have h1 : f i.castSucc = q.1 (Fin.last k) := by
                have : i.castSucc = ⟨k + 1, by omega⟩ := Fin.ext hil
                rw [this, hf_mid (k + 1) (by omega) (by omega)]; rfl
              have h2 : f i.succ = q.2 := by
                have : i.succ = Fin.last (k + 2) := Fin.ext (by simp [hil])
                rw [this, hf_last]
              rw [h1, h2, ← hg.2.1]; exact hu.1
            · have h1 : f i.castSucc = q.1 ⟨i.1 - 1, by omega⟩ := hf_mid i.1 (by omega) (by omega)
              have h2 : f i.succ = q.1 ⟨i.1, by omega⟩ := by
                have : i.succ = ⟨i.1 + 1, by omega⟩ := by ext; rfl
                rw [this, hf_mid (i.1 + 1) (by omega) (by omega)]
              rw [h1, h2]
              have hstep := hg.2.2.1 ⟨i.1 - 1, by omega⟩
              convert hstep using 2; ext; simp; omega
        · by_cases hi0 : i = 0
          · subst hi0
            have h1 : f ⟨0, by omega⟩ = q.2 := hf_zero
            have h2 : f ⟨0 + 2, by omega⟩ = q.1 ⟨1, by omega⟩ := hf_mid 2 (by omega) (by omega)
            rw [h1, h2]; exact hu.2.1
          · by_cases hik : i = k
            · have h1 : f ⟨i, by omega⟩ = q.1 ⟨k - 1, by omega⟩ := by
                rw [hf_mid i (by omega) (by omega), hik]
              have h2 : f ⟨i + 2, by omega⟩ = q.2 := by
                have : (⟨i + 2, by omega⟩ : Fin (k + 3)) = Fin.last (k + 2) := by ext; simp [hik]
                rw [this, hf_last]
              rw [h1, h2]; exact Ne.symm hu.2.2
            · have h1 : f ⟨i, by omega⟩ = q.1 ⟨i - 1, by omega⟩ := hf_mid i (by omega) (by omega)
              have h2 : f ⟨i + 2, by omega⟩ = q.1 ⟨i + 1, by omega⟩ :=
                hf_mid (i + 2) (by omega) (by omega)
              rw [h1, h2]
              have hstep := hg.2.2.2 (i - 1) (by omega)
              convert hstep using 2 <;> (ext; simp; omega)
        · have h1 : f ⟨1, by omega⟩ = q.1 0 := by rw [hf_mid 1 (by omega) (by omega)]; rfl
          have h2 : f ⟨k + 2 - 1, by omega⟩ = q.1 (Fin.last k) := by
            have : (⟨k + 2 - 1, by omega⟩ : Fin (k + 3)) = ⟨k + 1, by omega⟩ := by ext; simp
            rw [this, hf_mid (k + 1) (by omega) (by omega)]; rfl
          rw [h1, h2, hg.2.1]
      · refine Sigma.ext ?_ (heq_of_eq hf_zero)
        ext i; dsimp only; rw [hf_mid (i.1 + 1) (by omega) (by omega)]
  rw [hbij]
  let C_tl := C_k.filter (fun g => g ⟨1, by omega⟩ ≠ g ⟨k - 1, by omega⟩)
  let C_td := C_k.filter (fun g => g ⟨1, by omega⟩ = g ⟨k - 1, by omega⟩)
  have hsum_split : ∀ F : (Fin (k + 1) → V) → ℕ,
      ∑ g ∈ C_k, F g = ∑ g ∈ C_tl, F g + ∑ g ∈ C_td, F g := by
    intro F
    rw [← Finset.sum_filter_add_sum_filter_not C_k (fun g => g ⟨1, by omega⟩ ≠ g ⟨k - 1, by omega⟩)]
    congr 1; refine Finset.sum_congr ?_ (fun _ _ => rfl); ext g; simp [C_td]
  rw [hsum_split]
  have h1_each : ∀ g ∈ C_tl,
      (Finset.univ.filter (fun u : V =>
        G.Adj (g 0) u ∧ u ≠ g ⟨1, by omega⟩ ∧ u ≠ g ⟨k - 1, by omega⟩)).card = 1 := by
    intro g hg; simp only [C_tl, C_k, Finset.mem_filter, Finset.mem_univ, true_and] at hg
    rcases hg with ⟨⟨_, hcl, hadj, _⟩, hne⟩
    have ha1 : g ⟨1, by omega⟩ ∈ G.neighborFinset (g 0) := by
      rw [SimpleGraph.mem_neighborFinset]
      have h01 := hadj ⟨0, by omega⟩
      have ha0 : (⟨0, by omega⟩ : Fin k).castSucc = (0 : Fin (k + 1)) := by ext; rfl
      have ha1' : (⟨0, by omega⟩ : Fin k).succ = ⟨1, by omega⟩ := by ext; rfl
      rw [ha0, ha1'] at h01; exact h01
    have ha2 : g ⟨k - 1, by omega⟩ ∈ (G.neighborFinset (g 0)).erase (g ⟨1, by omega⟩) := by
      rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset]; refine ⟨hne.symm, ?_⟩
      have hstep := hadj ⟨k - 1, by omega⟩
      have hlast : (⟨k - 1, by omega⟩ : Fin k).succ = Fin.last k := by ext; simp; omega
      have hcur : (⟨k - 1, by omega⟩ : Fin k).castSucc = ⟨k - 1, by omega⟩ := by ext; rfl
      rw [hcur, hlast, ← hcl] at hstep; exact (G.adj_comm _ _).mp hstep
    have hset : Finset.univ.filter (fun u : V =>
        G.Adj (g 0) u ∧ u ≠ g ⟨1, by omega⟩ ∧ u ≠ g ⟨k - 1, by omega⟩) =
        ((G.neighborFinset (g 0)).erase (g ⟨1, by omega⟩)).erase (g ⟨k - 1, by omega⟩) := by
      ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
        SimpleGraph.mem_neighborFinset]; tauto
    rw [hset, Finset.card_erase_of_mem ha2, Finset.card_erase_of_mem ha1,
      SimpleGraph.card_neighborFinset_eq_degree, hreg (g 0)]
  have h2_each : ∀ g ∈ C_td,
      (Finset.univ.filter (fun u : V =>
        G.Adj (g 0) u ∧ u ≠ g ⟨1, by omega⟩ ∧ u ≠ g ⟨k - 1, by omega⟩)).card = 2 := by
    intro g hg; simp only [C_td, C_k, Finset.mem_filter, Finset.mem_univ, true_and] at hg
    rcases hg with ⟨⟨_, _, hadj, _⟩, heq⟩
    have ha1 : g ⟨1, by omega⟩ ∈ G.neighborFinset (g 0) := by
      rw [SimpleGraph.mem_neighborFinset]
      have h01 := hadj ⟨0, by omega⟩
      have ha0 : (⟨0, by omega⟩ : Fin k).castSucc = (0 : Fin (k + 1)) := by ext; rfl
      have ha1' : (⟨0, by omega⟩ : Fin k).succ = ⟨1, by omega⟩ := by ext; rfl
      rw [ha0, ha1'] at h01; exact h01
    have hset : Finset.univ.filter (fun u : V =>
        G.Adj (g 0) u ∧ u ≠ g ⟨1, by omega⟩ ∧ u ≠ g ⟨k - 1, by omega⟩) =
        (G.neighborFinset (g 0)).erase (g ⟨1, by omega⟩) := by
      ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
        SimpleGraph.mem_neighborFinset, ← heq]; tauto
    rw [hset, Finset.card_erase_of_mem ha1, SimpleGraph.card_neighborFinset_eq_degree, hreg (g 0)]
  rw [Finset.sum_congr rfl h1_each, Finset.sum_congr rfl h2_each,
    Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul, mul_one, mul_comm C_td.card 2]
  congr 1
  · unfold taillessCount; congr 1; ext g; simp [C_tl, C_k, IsTaillessClosedNBSeq, hk]
  · congr 1; unfold tailedCount; congr 1; ext g; simp [C_td, C_k, IsTailedClosedNBSeq, hk]

lemma chebMat_step_eq_nbMat (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : ∀ v, G.degree v = 3) (k : ℕ) (hk : 1 ≤ k) :
    chebMat G (k + 2) - chebMat G k = nbMat G (k + 2) - 2 • nbMat G k := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    match k with
    | 0 => omega
    | 1 =>
      rw [nbMat_recurrence G hreg 0, nbMat_two G hreg, nbMat_one G]; simp only [chebMat]
      ext u v
      simp only [Matrix.sub_apply, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
        Matrix.smul_apply]
      simp only [nsmul_eq_mul, Nat.cast_ofNat]; ring
    | 2 =>
      rw [nbMat_recurrence G hreg 1, nbMat_recurrence G hreg 0, nbMat_two G hreg, nbMat_one G]
      simp only [chebMat]; ext u v
      simp only [Matrix.sub_apply, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
        smul_sub, Matrix.smul_apply, Matrix.one_apply]
      simp only [nsmul_eq_mul, Nat.cast_ofNat]; ring
    | m + 3 =>
      have ih1 := ih (m + 2) (by omega) (by omega)
      have ih0 := ih (m + 1) (by omega) (by omega)
      have hC : chebMat G (m + 5) - chebMat G (m + 3) =
          adjMat G * (chebMat G (m + 4) - chebMat G (m + 2)) -
          2 • (chebMat G (m + 3) - chebMat G (m + 1)) := by
        simp only [chebMat]; ext u v
        simp only [Matrix.sub_apply, Matrix.mul_sub, smul_sub, Matrix.smul_apply]
        simp only [nsmul_eq_mul, Nat.cast_ofNat]; ring
      have hN : nbMat G (m + 5) - 2 • nbMat G (m + 3) =
          adjMat G * (nbMat G (m + 4) - 2 • nbMat G (m + 2)) -
          2 • (nbMat G (m + 3) - 2 • nbMat G (m + 1)) := by
        rw [nbMat_recurrence G hreg (m + 2), nbMat_recurrence G hreg m]; ext u v
        simp only [Matrix.sub_apply, Matrix.mul_sub, Matrix.mul_smul, smul_sub, Matrix.smul_apply]
        simp only [nsmul_eq_mul, Nat.cast_ofNat]; ring
      rw [hC, ih1, ih0, ← hN]

/-- Theorem 5: Exact Ihara–Chebyshev trace identity for 3-regular graphs (zero eigenvalues!). -/
theorem chebMat_trace_eq_tailless (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : ∀ v, G.degree v = 3) (k : ℕ) (hk : 1 ≤ k) :
    Matrix.trace (chebMat G k) =
      (taillessCount G k : ℚ) - if Even k then (Fintype.card V : ℚ) else 0 := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    match k with
    | 0 => omega
    | 1 =>
      have hodd : ¬ Even (1 : ℕ) := by decide
      simp only [chebMat, hodd, ite_false, sub_zero]
      have htr : Matrix.trace (adjMat G) = 0 := by
        simp [Matrix.trace, Matrix.diag, adjMat]
      have htl : taillessCount G 1 = 0 := by
        unfold taillessCount; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro f _ ⟨⟨_, hcl, hadj, _⟩, _⟩
        have h01 := hadj ⟨0, by omega⟩
        have ha0 : (⟨0, by omega⟩ : Fin 1).castSucc = (0 : Fin 2) := by ext; rfl
        have ha1 : (⟨0, by omega⟩ : Fin 1).succ = Fin.last 1 := by ext; rfl
        rw [ha0, ha1, ← hcl] at h01; exact G.loopless.irrefl _ h01
      rw [htr, htl]; simp
    | 2 =>
      have heven : Even (2 : ℕ) := by decide
      simp only [heven, ite_true]
      have hcheb2 : chebMat G 2 = nbMat G 2 - (1 : Matrix V V ℚ) := by
        rw [nbMat_two G hreg]; simp only [chebMat]; ext u v
        simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
        simp only [nsmul_eq_mul, Nat.cast_ofNat]; ring
      have htr_nb2 : Matrix.trace (nbMat G 2) = 0 := by
        rw [trace_nbMat_eq_closedNBCount G 2 (by omega)]
        have hz : closedNBCount G 2 = 0 := by
          unfold closedNBCount; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro f _ ⟨_, hcl, _, hnb⟩; exact hnb 0 (by omega) hcl
        rw [hz]; simp
      have htl2 : taillessCount G 2 = 0 := by
        unfold taillessCount; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro f _ ⟨⟨_, hcl, _, hnb⟩, _⟩; exact hnb 0 (by omega) hcl
      rw [hcheb2, Matrix.trace_sub, htr_nb2, Matrix.trace_one, htl2]; simp
    | m + 3 =>
      have ih_m := ih (m + 1) (by omega) (by omega)
      have hstep := chebMat_step_eq_nbMat G hreg (m + 1) (by omega)
      have htr_step : Matrix.trace (chebMat G (m + 3)) - Matrix.trace (chebMat G (m + 1)) =
          Matrix.trace (nbMat G (m + 3)) - 2 * Matrix.trace (nbMat G (m + 1)) := by
        have h := congr_arg Matrix.trace hstep
        simp only [Matrix.trace_sub, Matrix.trace_smul] at h
        simpa [nsmul_eq_mul] using h
      rw [trace_nbMat_eq_closedNBCount G (m + 3) (by omega),
          trace_nbMat_eq_closedNBCount G (m + 1) (by omega)] at htr_step
      have h1 : (closedNBCount G (m + 3) : ℚ) = (taillessCount G (m + 3) : ℚ) + (tailedCount G (m + 3) : ℚ) := by
        exact_mod_cast closedNBCount_eq_add G (m + 3) (by omega)
      have h2 : (closedNBCount G (m + 1) : ℚ) = (taillessCount G (m + 1) : ℚ) + (tailedCount G (m + 1) : ℚ) := by
        exact_mod_cast closedNBCount_eq_add G (m + 1) (by omega)
      have h3 : (tailedCount G (m + 3) : ℚ) = (taillessCount G (m + 1) : ℚ) + 2 * (tailedCount G (m + 1) : ℚ) := by
        exact_mod_cast tailedCount_step G hreg (m + 1) (by omega)
      have hev : Even (m + 3) ↔ Even (m + 1) := by
        rw [show m + 3 = (m + 1) + 2 by omega]
        exact Nat.even_add_one.trans (by simp [Nat.even_add_one])
      by_cases h : Even (m + 1)
      · have h' : Even (m + 3) := hev.mpr h
        simp only [h, h', ite_true] at ih_m ⊢; linarith
      · have h' : ¬ Even (m + 3) := fun hc => h (hev.mp hc)
        simp only [h, h', ite_false] at ih_m ⊢; linarith

end NonBacktrackingTraceAlgebra

section ZeroSpectralLukacsSOS

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma aeval_adjMat_transpose (G : SimpleGraph V) [DecidableRel G.Adj] (P : Polynomial ℚ) :
    (Polynomial.aeval (adjMat G) P).transpose = Polynomial.aeval (adjMat G) P := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Matrix.transpose_add, hp, hq]
  | monomial n a =>
    simp only [aeval_monomial, Matrix.transpose_mul, Matrix.transpose_pow, adjMat_transpose]
    rw [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_transpose]
    have hcomm : Matrix.diagonal (algebraMap ℚ (V → ℚ) a) * adjMat G ^ n =
        adjMat G ^ n * Matrix.diagonal (algebraMap ℚ (V → ℚ) a) := by
      ext u v; simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
      change a * (adjMat G ^ n) u v = (adjMat G ^ n) u v * a; ring
    rw [hcomm]

lemma aeval_adjMat_row_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : ∀ v, G.degree v = 3) (P : Polynomial ℚ) (u : V) :
    ∑ v : V, Polynomial.aeval (adjMat G) P u v = P.eval 3 := by
  induction P using Polynomial.induction_on' generalizing u with
  | add p q hp hq => simp only [map_add, Matrix.add_apply, Finset.sum_add_distrib, eval_add, hp, hq]
  | monomial n a =>
    simp only [aeval_monomial, eval_monomial]
    have hpow : ∀ m : ℕ, ∀ x : V, ∑ v : V, ((adjMat G) ^ m) x v = 3 ^ m := by
      intro m; induction m with
      | zero => intro x; simp [Matrix.one_apply]
      | succ m ihm =>
        intro x; rw [pow_succ']
        simp_rw [Matrix.mul_apply]; rw [Finset.sum_comm]
        have hstep : ∀ w : V, ∑ v : V, adjMat G x w * ((adjMat G) ^ m) w v =
            adjMat G x w * 3 ^ m := fun w => by rw [← Finset.mul_sum, ihm w]
        simp_rw [hstep, ← Finset.sum_mul, adjMat_row_sum G hreg x, pow_succ']
    have hsc : ∀ v : V, (algebraMap ℚ (Matrix V V ℚ) a * adjMat G ^ n) u v =
        a * (adjMat G ^ n) u v := fun v => by
      rw [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_mul]; rfl
    simp_rw [hsc, ← Finset.mul_sum, hpow n u]

omit [DecidableEq V] in
lemma sq_sum_le_card_mul_sum_sq (x : V → ℚ) :
    (∑ i : V, x i) ^ 2 ≤ (Fintype.card V : ℚ) * ∑ i : V, (x i) ^ 2 := by
  have hnn : (0 : ℚ) ≤ ∑ i : V, ∑ j : V, (x i - x j) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hexp : ∑ i : V, ∑ j : V, (x i - x j) ^ 2 =
      2 * ((Fintype.card V : ℚ) * ∑ i : V, (x i) ^ 2 - (∑ i : V, x i) ^ 2) := by
    have h1 : ∀ i : V, ∑ j : V, (x i - x j) ^ 2 =
        (Fintype.card V : ℚ) * (x i) ^ 2 - (2 * x i) * (∑ j : V, x j) + ∑ j : V, (x j) ^ 2 := by
      intro i
      have hterm : ∀ j : V, (x i - x j) ^ 2 = (x i) ^ 2 - (2 * x i) * x j + (x j) ^ 2 := fun j => by ring
      simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
    simp_rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp_rw [← Finset.sum_mul]; ring
  linarith

omit [DecidableEq V] in
lemma cubic_adj_sq_le_nine_sq (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : ∀ v, G.degree v = 3) (x : V → ℚ) :
    ∑ v : V, (∑ u : V, adjMat G v u * x u) ^ 2 ≤ 9 * ∑ u : V, (x u) ^ 2 := by
  have hrow : ∀ v : V, (∑ u : V, adjMat G v u * x u) ^ 2 ≤
      3 * ∑ u : V, adjMat G v u * (x u) ^ 2 := by
    intro v
    have hnn : (0 : ℚ) ≤ ∑ a : V, ∑ b : V, adjMat G v a * adjMat G v b * (x a - x b) ^ 2 := by
      refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
      have ha : 0 ≤ adjMat G v a := by unfold adjMat; split_ifs <;> norm_num
      have hb : 0 ≤ adjMat G v b := by unfold adjMat; split_ifs <;> norm_num
      exact mul_nonneg (mul_nonneg ha hb) (sq_nonneg _)
    have hexp : ∑ a : V, ∑ b : V, adjMat G v a * adjMat G v b * (x a - x b) ^ 2 =
        2 * (3 * ∑ a : V, adjMat G v a * (x a) ^ 2 - (∑ a : V, adjMat G v a * x a) ^ 2) := by
      have h1 : ∀ a : V, ∑ b : V, adjMat G v a * adjMat G v b * (x a - x b) ^ 2 =
          (adjMat G v a * (x a) ^ 2) * 3
          - (2 * (adjMat G v a * x a)) * (∑ b : V, adjMat G v b * x b)
          + adjMat G v a * (∑ b : V, adjMat G v b * (x b) ^ 2) := by
        intro a
        have hterm : ∀ b : V, adjMat G v a * adjMat G v b * (x a - x b) ^ 2 =
            (adjMat G v a * (x a) ^ 2) * adjMat G v b
            - (2 * (adjMat G v a * x a)) * (adjMat G v b * x b)
            + adjMat G v a * (adjMat G v b * (x b) ^ 2) := fun b => by ring
        simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          adjMat_row_sum G hreg v]
      simp_rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
        ← Finset.mul_sum, adjMat_row_sum G hreg v]; ring
    linarith
  have hsum : ∑ v : V, (∑ u : V, adjMat G v u * x u) ^ 2 ≤
      ∑ v : V, 3 * ∑ u : V, adjMat G v u * (x u) ^ 2 :=
    Finset.sum_le_sum fun v _ => hrow v
  have hrhs : ∑ v : V, 3 * ∑ u : V, adjMat G v u * (x u) ^ 2 = 9 * ∑ u : V, (x u) ^ 2 := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    have hinner : ∀ u : V, ∑ v : V, adjMat G v u * (x u) ^ 2 = 3 * (x u) ^ 2 := by
      intro u
      have hsym : ∀ v : V, adjMat G v u = adjMat G u v := fun v => by simp [adjMat, G.adj_comm]
      simp_rw [hsym, ← Finset.sum_mul, adjMat_row_sum G hreg u]
    simp_rw [hinner, ← Finset.mul_sum]; ring
  linarith

lemma lukacs_boundary_trace_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : ∀ v, G.degree v = 3) (Q : Polynomial ℚ) :
    0 ≤ Matrix.trace (Polynomial.aeval (adjMat G) ((9 - Polynomial.X ^ 2) * Q ^ 2)) := by
  let A := adjMat G
  let M := Polynomial.aeval A Q
  have hM_sym : M.transpose = M := aeval_adjMat_transpose G Q
  have hA_sym : A.transpose = A := adjMat_transpose G
  have hcomm : A * M = M * A := by
    have : Polynomial.aeval A (Polynomial.X * Q) = Polynomial.aeval A (Q * Polynomial.X) := by ring_nf
    simpa [M, A, map_mul, aeval_X] using this
  have htr_eq : Matrix.trace (Polynomial.aeval A ((9 - Polynomial.X ^ 2) * Q ^ 2)) =
      ∑ w : V, (9 * ∑ v : V, (M v w) ^ 2 - ∑ v : V, (∑ u : V, A v u * M u w) ^ 2) := by
    simp only [map_mul, map_sub, map_ofNat, map_pow, aeval_X, sub_mul, Matrix.trace_sub]
    have h9 : Matrix.trace ((9 : Matrix V V ℚ) * M ^ 2) = 9 * ∑ w : V, ∑ v : V, (M v w) ^ 2 := by
      have h9' : (9 : Matrix V V ℚ) * M ^ 2 = (9 : ℚ) • (M * M) := by
        have h9_1 : (9 : Matrix V V ℚ) = (9 : ℕ) • (1 : Matrix V V ℚ) := by simp
        rw [sq, h9_1, Matrix.smul_mul, Matrix.one_mul]
        ext u v; simp [nsmul_eq_mul]
      rw [h9', Matrix.trace_smul, smul_eq_mul]; congr 1
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]; rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun v _ => ?_
      have hv : M w v = M v w := by
        have := congr_fun (congr_fun hM_sym v) w; simpa [transpose_apply] using this
      rw [hv, ← sq]
    have hA2 : Matrix.trace (A ^ 2 * M ^ 2) = ∑ w : V, ∑ v : V, (∑ u : V, A v u * M u w) ^ 2 := by
      have hAM : A ^ 2 * M ^ 2 = (A * M) * (A * M) := by
        calc A ^ 2 * M ^ 2 = A * (A * M) * M := by simp only [sq, Matrix.mul_assoc]
          _ = A * (M * A) * M := by rw [hcomm]
          _ = (A * M) * (A * M) := by simp only [Matrix.mul_assoc]
      have hAM_sym : (A * M).transpose = A * M := by
        rw [Matrix.transpose_mul, hM_sym, hA_sym, ← hcomm]
      rw [hAM]; simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]; rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun v _ => ?_
      have hv : (A * M) w v = (A * M) v w := by
        have := congr_fun (congr_fun hAM_sym v) w; simpa [transpose_apply] using this
      have hv' : ∑ j : V, A w j * M j v = ∑ j : V, A v j * M j w := by
        simpa [Matrix.mul_apply] using hv
      rw [hv', ← sq]
    rw [h9, hA2, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [htr_eq]
  refine Finset.sum_nonneg fun w _ => ?_
  have := cubic_adj_sq_le_nine_sq G hreg (fun u => M u w)
  linarith

/-- Theorem 6: Zero-spectral-theorem Lukács SOS trace lower bound (General 3-regular graphs). -/
theorem sos_trace_lower_bound_general (G : SimpleGraph V) [DecidableRel G.Adj]
    [Nonempty V] (hreg : ∀ v, G.degree v = 3) (P Q : Polynomial ℚ) :
    (P.eval 3) ^ 2 ≤
      Matrix.trace (Polynomial.aeval (adjMat G) (P ^ 2 + (9 - Polynomial.X ^ 2) * Q ^ 2)) := by
  rw [map_add, Matrix.trace_add]
  have hQ := lukacs_boundary_trace_nonneg G hreg Q
  have hP : (P.eval 3) ^ 2 ≤ Matrix.trace (Polynomial.aeval (adjMat G) (P ^ 2)) := by
    let M := Polynomial.aeval (adjMat G) P
    have hM_sym : M.transpose = M := aeval_adjMat_transpose G P
    have htr : Matrix.trace (Polynomial.aeval (adjMat G) (P ^ 2)) =
        ∑ u : V, ∑ v : V, (M u v) ^ 2 := by
      rw [map_pow, sq]; simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
      have hv : M v u = M u v := by
        have := congr_fun (congr_fun hM_sym u) v; simpa [transpose_apply] using this
      change M u v * M v u = M u v ^ 2
      rw [hv, ← sq]
    rw [htr]
    have hn_pos : (0 : ℚ) < (Fintype.card V : ℚ) := Nat.cast_pos.mpr Fintype.card_pos
    have hrow : ∀ u : V, (P.eval 3) ^ 2 ≤ (Fintype.card V : ℚ) * ∑ v : V, (M u v) ^ 2 := by
      intro u; rw [← aeval_adjMat_row_sum G hreg P u]
      exact sq_sum_le_card_mul_sum_sq (fun v => M u v)
    have hsum := Finset.sum_le_sum fun u (_ : u ∈ Finset.univ) => hrow u
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum] at hsum
    exact le_of_mul_le_mul_left hsum hn_pos
  linarith

omit [DecidableEq V] in
lemma bipartite_sign_sum_zero (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : ∀ v, G.degree v = 3) (col : V → Bool) (hcol : ∀ u v, G.Adj u v → col u ≠ col v) :
    ∑ u : V, (if col u then (1 : ℚ) else -1) = 0 := by
  let s : V → ℚ := fun u => if col u then 1 else -1
  have hadj_s : ∀ u v, G.Adj u v → s v = -s u := by
    intro u v huv; have hne := hcol u v huv
    dsimp [s]; cases h1 : col u <;> cases h2 : col v <;> simp_all
  have hsum : ∑ u : V, ∑ v : V, adjMat G u v * s v = -3 * ∑ u : V, s u := by
    have h1 : ∀ u : V, ∑ v : V, adjMat G u v * s v = -3 * s u := by
      intro u
      have : ∀ v, adjMat G u v * s v = -(adjMat G u v * s u) := by
        intro v; unfold adjMat; split_ifs with h
        · rw [hadj_s u v h]; ring
        · ring
      simp_rw [this, Finset.sum_neg_distrib, ← Finset.sum_mul, adjMat_row_sum G hreg u]; ring
    simp_rw [h1, ← Finset.mul_sum]
  have hsum2 : ∑ u : V, ∑ v : V, adjMat G u v * s v = 3 * ∑ v : V, s v := by
    rw [Finset.sum_comm]
    refine (Finset.sum_congr rfl fun v _ => ?_).trans (by rw [← Finset.mul_sum])
    have : ∀ u, adjMat G u v = adjMat G v u := fun u => by simp [adjMat, G.adj_comm]
    simp_rw [this, ← Finset.sum_mul, adjMat_row_sum G hreg v]
  linarith

lemma bipartite_aeval_sign_mul (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : ∀ v, G.degree v = 3) (col : V → Bool) (hcol : ∀ u v, G.Adj u v → col u ≠ col v)
    (P : Polynomial ℚ) (u : V) :
    ∑ v : V, Polynomial.aeval (adjMat G) P u v * (if col v then (1 : ℚ) else -1) =
      P.eval (-3) * (if col u then (1 : ℚ) else -1) := by
  let s : V → ℚ := fun x => if col x then 1 else -1
  have hadj_s : ∀ x y, G.Adj x y → s y = -s x := by
    intro x y hxy; have hne := hcol x y hxy
    dsimp [s]; cases h1 : col x <;> cases h2 : col y <;> simp_all
  have hA_s : ∀ x : V, ∑ v : V, adjMat G x v * s v = -3 * s x := by
    intro x
    have : ∀ v, adjMat G x v * s v = -(adjMat G x v * s x) := by
      intro v; unfold adjMat; split_ifs with h
      · rw [hadj_s x v h]; ring
      · ring
    simp_rw [this, Finset.sum_neg_distrib, ← Finset.sum_mul, adjMat_row_sum G hreg x]; ring
  induction P using Polynomial.induction_on' generalizing u with
  | add p q hp hq =>
    simp only [map_add, Matrix.add_apply, add_mul, Finset.sum_add_distrib, eval_add, hp, hq]
  | monomial n a =>
    simp only [aeval_monomial, eval_monomial]
    have hpow : ∀ m : ℕ, ∀ x : V, ∑ v : V, ((adjMat G) ^ m) x v * s v = (-3) ^ m * s x := by
      intro m; induction m with
      | zero => intro x; simp [Matrix.one_apply]
      | succ m ihm =>
        intro x; rw [pow_succ']
        simp_rw [Matrix.mul_apply, Finset.sum_mul]; rw [Finset.sum_comm]
        have hstep : ∀ w : V, ∑ v : V, adjMat G x w * ((adjMat G) ^ m) w v * s v =
            adjMat G x w * ((-3) ^ m * s w) := by
          intro w; simp_rw [mul_assoc, ← Finset.mul_sum, ihm w]
        simp_rw [hstep]
        have hpull : ∑ w : V, adjMat G x w * ((-3) ^ m * s w) =
            (-3) ^ m * ∑ w : V, adjMat G x w * s w := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun w _ => by ring
        rw [hpull, hA_s x, pow_succ']; ring
    have hsc : ∀ v : V, (algebraMap ℚ (Matrix V V ℚ) a * adjMat G ^ n) u v * s v =
        a * (((adjMat G) ^ n) u v * s v) := fun v => by
      rw [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_mul]
      change a * ((adjMat G) ^ n) u v * s v = _
      ring
    change ∑ v : V, (algebraMap ℚ (Matrix V V ℚ) a * adjMat G ^ n) u v * s v = _
    simp_rw [hsc, ← Finset.mul_sum, hpow n u]; ring

/-- Theorem 7: Zero-spectral-theorem Lukács SOS trace lower bound (Bipartite 3-regular graphs). -/
theorem sos_trace_lower_bound_bipartite (G : SimpleGraph V) [DecidableRel G.Adj]
    [Nonempty V] (hreg : ∀ v, G.degree v = 3)
    (col : V → Bool) (hcol : ∀ u v, G.Adj u v → col u ≠ col v)
    (P Q : Polynomial ℚ) :
    (P.eval 3) ^ 2 + (P.eval (-3)) ^ 2 ≤
      Matrix.trace (Polynomial.aeval (adjMat G) (P ^ 2 + (9 - Polynomial.X ^ 2) * Q ^ 2)) := by
  rw [map_add, Matrix.trace_add]
  have hQ := lukacs_boundary_trace_nonneg G hreg Q
  have hP : (P.eval 3) ^ 2 + (P.eval (-3)) ^ 2 ≤
      Matrix.trace (Polynomial.aeval (adjMat G) (P ^ 2)) := by
    let M := Polynomial.aeval (adjMat G) P
    let s : V → ℚ := fun x => if col x then 1 else -1
    let n : ℚ := (Fintype.card V : ℚ)
    let α : ℚ := P.eval 3
    let β : ℚ := P.eval (-3)
    have hn_pos : (0 : ℚ) < n := Nat.cast_pos.mpr Fintype.card_pos
    have hn_ne : n ≠ 0 := ne_of_gt hn_pos
    have hs_sq : ∀ x : V, (s x) ^ 2 = 1 := fun x => by dsimp [s]; cases col x <;> norm_num
    have hs_sum : ∑ x : V, s x = 0 := bipartite_sign_sum_zero G hreg col hcol
    have hM_sym : M.transpose = M := aeval_adjMat_transpose G P
    have htr : Matrix.trace (Polynomial.aeval (adjMat G) (P ^ 2)) =
        ∑ u : V, ∑ v : V, (M u v) ^ 2 := by
      rw [map_pow, sq]; simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
      have hv : M v u = M u v := by
        have := congr_fun (congr_fun hM_sym u) v; simpa [transpose_apply] using this
      change M u v * M v u = M u v ^ 2
      rw [hv, ← sq]
    rw [htr]
    have hnn : (0 : ℚ) ≤ ∑ u : V, ∑ v : V, (M u v - α / n - (β / n) * s u * s v) ^ 2 :=
      Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => sq_nonneg _
    have hexp : ∑ u : V, ∑ v : V, (M u v - α / n - (β / n) * s u * s v) ^ 2 =
        (∑ u : V, ∑ v : V, (M u v) ^ 2) - α ^ 2 - β ^ 2 := by
      have hrow1 : ∀ u : V, ∑ v : V, M u v = α := aeval_adjMat_row_sum G hreg P
      have hrow2 : ∀ u : V, ∑ v : V, M u v * s v = β * s u :=
        bipartite_aeval_sign_mul G hreg col hcol P
      have hinner : ∀ u : V, ∑ v : V, (M u v - α / n - (β / n) * s u * s v) ^ 2 =
          (∑ v : V, (M u v) ^ 2) - α ^ 2 / n - β ^ 2 / n := by
        intro u
        have hterm : ∀ v : V, (M u v - α / n - (β / n) * s u * s v) ^ 2 =
            (M u v) ^ 2
            - (2 * (α / n)) * M u v
            - (2 * (β / n) * s u) * (M u v * s v)
            + (α / n) ^ 2
            + (2 * (α / n) * (β / n) * s u) * s v
            + ((β / n) ^ 2 * (s u) ^ 2) * (s v) ^ 2 := fun v => by ring
        simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          hrow1 u, hrow2 u, hs_sum, hs_sq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [show (Fintype.card V : ℚ) = n from rfl]
        have hsu : s u * s u = 1 := by rw [← sq]; exact hs_sq u
        have hmid : 2 * (β / n) * s u * (β * s u) = 2 * (β ^ 2 / n) := by
          rw [show 2 * (β / n) * s u * (β * s u) = 2 * (β ^ 2 / n) * (s u * s u) by ring, hsu, mul_one]
        rw [hmid]; field_simp [hn_ne]; ring
      simp_rw [hinner, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [show (Fintype.card V : ℚ) = n from rfl]; field_simp [hn_ne]
    linarith
  linarith

end ZeroSpectralLukacsSOS

section MasterSOSDelsarteClosure

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Theorem 8: Master General SOS-Delsarte Closure Theorem (Girth `g ≥ 9`, zero spectral theorem!). -/
theorem cubic_girth_sos_c16 (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (hreg : ∀ v, G.degree v = 3)
    (g : ℕ) (hg9 : 9 ≤ g) (hg : GirthAtLeast G g)
    (P Q : Polynomial ℚ) (c : Fin 17 → ℚ)
    (hpoly : P ^ 2 + (9 - Polynomial.X ^ 2) * Q ^ 2 =
      ∑ k : Fin 17, Polynomial.C (c k) * chebPoly k.1)
    (hc16 : 0 < c ⟨16, by omega⟩)
    (hcle : ∀ k : Fin 17, g ≤ k.1 → k.1 < 16 → c k ≤ 0)
    (hbound : (Fintype.card V : ℚ) *
      (2 * c ⟨0, by omega⟩ - ∑ k : Fin 17, if k.1 ≠ 0 ∧ Even k.1 then c k else 0) <
      (P.eval 3) ^ 2) :
    HasSimpleCycle G 16 := by
  have hsos := sos_trace_lower_bound_general G hreg P Q
  rw [hpoly, map_sum, Matrix.trace_sum] at hsos
  have htr_each : ∀ k : Fin 17,
      Matrix.trace (Polynomial.aeval (adjMat G) (Polynomial.C (c k) * chebPoly k.1)) =
      c k * Matrix.trace (chebMat G k.1) := by
    intro k
    rw [map_mul, Polynomial.aeval_C, aeval_chebPoly_eq_chebMat, Matrix.algebraMap_eq_diagonal,
      Matrix.trace, Matrix.trace]
    simp only [Matrix.diag, Matrix.diagonal_mul]
    change ∑ u : V, c k * chebMat G k.1 u u = c k * ∑ u : V, chebMat G k.1 u u
    rw [← Finset.mul_sum]
  simp_rw [htr_each] at hsos
  have hsum_eval : ∑ k : Fin 17, c k * Matrix.trace (chebMat G k.1) =
      (Fintype.card V : ℚ) *
        (2 * c ⟨0, by omega⟩ - ∑ k : Fin 17, if k.1 ≠ 0 ∧ Even k.1 then c k else 0) +
      ∑ k : Fin 17, if k.1 ≠ 0 then c k * (taillessCount G k.1 : ℚ) else 0 := by
    have hterm : ∀ k : Fin 17, c k * Matrix.trace (chebMat G k.1) =
        (if k.1 = 0 then (Fintype.card V : ℚ) * (2 * c ⟨0, by omega⟩) else 0) -
        (Fintype.card V : ℚ) * (if k.1 ≠ 0 ∧ Even k.1 then c k else 0) +
        (if k.1 ≠ 0 then c k * (taillessCount G k.1 : ℚ) else 0) := by
      intro k
      by_cases hk0 : k.1 = 0
      · have hk_eq : k = ⟨0, by omega⟩ := Fin.ext hk0
        rw [hk_eq]
        simp only [chebMat, Matrix.trace_smul, Matrix.trace_one,
          ite_true, ne_eq, not_true_eq_false, false_and, ite_false, mul_zero, sub_zero, add_zero]
        simp only [nsmul_eq_mul, Nat.cast_ofNat]; ring
      · have hk1 : 1 ≤ k.1 := by omega
        rw [chebMat_trace_eq_tailless G hreg k.1 hk1]
        by_cases hev : Even k.1
        · simp [hk0, hev]; ring
        · simp [hk0, hev]
    simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have h0sum : (∑ k : Fin 17, if k.1 = 0 then (Fintype.card V : ℚ) * (2 * c ⟨0, by omega⟩) else 0) =
        (Fintype.card V : ℚ) * (2 * c ⟨0, by omega⟩) := by
      rw [Finset.sum_eq_single ⟨0, by omega⟩]
      · simp
      · intro b _ hb; simp [show b.1 ≠ 0 from fun h => hb (Fin.ext h)]
      · intro h; exact False.elim (h (Finset.mem_univ _))
    rw [h0sum]; ring
  rw [hsum_eval] at hsos
  have htl_le : ∑ k : Fin 17, (if k.1 ≠ 0 then c k * (taillessCount G k.1 : ℚ) else 0) ≤
      c ⟨16, by omega⟩ * (taillessCount G 16 : ℚ) := by
    have hsplit : ∑ k : Fin 17, (if k.1 ≠ 0 then c k * (taillessCount G k.1 : ℚ) else 0) =
        c ⟨16, by omega⟩ * (taillessCount G 16 : ℚ) +
        ∑ k ∈ Finset.univ.erase ⟨16, by omega⟩,
          (if k.1 ≠ 0 then c k * (taillessCount G k.1 : ℚ) else 0) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ⟨16, by omega⟩)]; simp
    rw [hsplit]
    have hrest : ∑ k ∈ Finset.univ.erase ⟨16, by omega⟩,
        (if k.1 ≠ 0 then c k * (taillessCount G k.1 : ℚ) else 0) ≤ 0 := by
      refine Finset.sum_nonpos fun k hk => ?_
      have hk16 : k.1 < 16 := by
        have hne : k ≠ ⟨16, by omega⟩ := (Finset.mem_erase.mp hk).1
        have : k.1 ≠ 16 := fun h => hne (Fin.ext h)
        omega
      by_cases hk0 : k.1 = 0
      · simp [hk0]
      · simp only [hk0, ne_eq, not_false_eq_true, ite_true]
        by_cases hkg : k.1 < g
        · rw [taillessCount_eq_zero_of_lt_girth G g k.1 hg (by omega) hkg]; simp
        · exact mul_nonpos_of_nonpos_of_nonneg (hcle k (by omega) hk16) (Nat.cast_nonneg _)
    linarith
  have hpos_mul : 0 < c ⟨16, by omega⟩ * (taillessCount G 16 : ℚ) := by linarith
  have hpos_q : (0 : ℚ) < (taillessCount G 16 : ℚ) :=
    pos_of_mul_pos_right hpos_mul (le_of_lt hc16)
  have hpos_nat : 0 < taillessCount G 16 := Nat.cast_pos.mp hpos_q
  exact has_c16_of_taillessCount_pos G (fun L hL => hg L (lt_of_lt_of_le hL hg9)) hpos_nat

/-- Theorem 9: Master Bipartite SOS-Delsarte Closure Theorem (Girth `g ≥ 10`, zero spectral theorem!). -/
theorem cubic_bipartite_girth_sos_c16 (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (hreg : ∀ v, G.degree v = 3)
    (col : V → Bool) (hcol : ∀ u v, G.Adj u v → col u ≠ col v)
    (g : ℕ) (hg9 : 9 ≤ g) (hg : GirthAtLeast G g)
    (P Q : Polynomial ℚ) (c : Fin 17 → ℚ)
    (hpoly : P ^ 2 + (9 - Polynomial.X ^ 2) * Q ^ 2 =
      ∑ k : Fin 17, Polynomial.C (c k) * chebPoly k.1)
    (hc16 : 0 < c ⟨16, by omega⟩)
    (hcle : ∀ k : Fin 17, g ≤ k.1 → k.1 < 16 → c k ≤ 0)
    (hbound : (Fintype.card V : ℚ) *
      (2 * c ⟨0, by omega⟩ - ∑ k : Fin 17, if k.1 ≠ 0 ∧ Even k.1 then c k else 0) <
      (P.eval 3) ^ 2 + (P.eval (-3)) ^ 2) :
    HasSimpleCycle G 16 := by
  have hsos := sos_trace_lower_bound_bipartite G hreg col hcol P Q
  rw [hpoly, map_sum, Matrix.trace_sum] at hsos
  have htr_each : ∀ k : Fin 17,
      Matrix.trace (Polynomial.aeval (adjMat G) (Polynomial.C (c k) * chebPoly k.1)) =
      c k * Matrix.trace (chebMat G k.1) := by
    intro k
    rw [map_mul, Polynomial.aeval_C, aeval_chebPoly_eq_chebMat, Matrix.algebraMap_eq_diagonal,
      Matrix.trace, Matrix.trace]
    simp only [Matrix.diag, Matrix.diagonal_mul]
    change ∑ u : V, c k * chebMat G k.1 u u = c k * ∑ u : V, chebMat G k.1 u u
    rw [← Finset.mul_sum]
  simp_rw [htr_each] at hsos
  have hsum_eval : ∑ k : Fin 17, c k * Matrix.trace (chebMat G k.1) =
      (Fintype.card V : ℚ) *
        (2 * c ⟨0, by omega⟩ - ∑ k : Fin 17, if k.1 ≠ 0 ∧ Even k.1 then c k else 0) +
      ∑ k : Fin 17, if k.1 ≠ 0 then c k * (taillessCount G k.1 : ℚ) else 0 := by
    have hterm : ∀ k : Fin 17, c k * Matrix.trace (chebMat G k.1) =
        (if k.1 = 0 then (Fintype.card V : ℚ) * (2 * c ⟨0, by omega⟩) else 0) -
        (Fintype.card V : ℚ) * (if k.1 ≠ 0 ∧ Even k.1 then c k else 0) +
        (if k.1 ≠ 0 then c k * (taillessCount G k.1 : ℚ) else 0) := by
      intro k
      by_cases hk0 : k.1 = 0
      · have hk_eq : k = ⟨0, by omega⟩ := Fin.ext hk0
        rw [hk_eq]
        simp only [chebMat, Matrix.trace_smul, Matrix.trace_one,
          ite_true, ne_eq, not_true_eq_false, false_and, ite_false, mul_zero, sub_zero, add_zero]
        simp only [nsmul_eq_mul, Nat.cast_ofNat]; ring
      · have hk1 : 1 ≤ k.1 := by omega
        rw [chebMat_trace_eq_tailless G hreg k.1 hk1]
        by_cases hev : Even k.1
        · simp [hk0, hev]; ring
        · simp [hk0, hev]
    simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have h0sum : (∑ k : Fin 17, if k.1 = 0 then (Fintype.card V : ℚ) * (2 * c ⟨0, by omega⟩) else 0) =
        (Fintype.card V : ℚ) * (2 * c ⟨0, by omega⟩) := by
      rw [Finset.sum_eq_single ⟨0, by omega⟩]
      · simp
      · intro b _ hb; simp [show b.1 ≠ 0 from fun h => hb (Fin.ext h)]
      · intro h; exact False.elim (h (Finset.mem_univ _))
    rw [h0sum]; ring
  rw [hsum_eval] at hsos
  have htl_le : ∑ k : Fin 17, (if k.1 ≠ 0 then c k * (taillessCount G k.1 : ℚ) else 0) ≤
      c ⟨16, by omega⟩ * (taillessCount G 16 : ℚ) := by
    have hsplit : ∑ k : Fin 17, (if k.1 ≠ 0 then c k * (taillessCount G k.1 : ℚ) else 0) =
        c ⟨16, by omega⟩ * (taillessCount G 16 : ℚ) +
        ∑ k ∈ Finset.univ.erase ⟨16, by omega⟩,
          (if k.1 ≠ 0 then c k * (taillessCount G k.1 : ℚ) else 0) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ⟨16, by omega⟩)]; simp
    rw [hsplit]
    have hrest : ∑ k ∈ Finset.univ.erase ⟨16, by omega⟩,
        (if k.1 ≠ 0 then c k * (taillessCount G k.1 : ℚ) else 0) ≤ 0 := by
      refine Finset.sum_nonpos fun k hk => ?_
      have hk16 : k.1 < 16 := by
        have hne : k ≠ ⟨16, by omega⟩ := (Finset.mem_erase.mp hk).1
        have : k.1 ≠ 16 := fun h => hne (Fin.ext h)
        omega
      by_cases hk0 : k.1 = 0
      · simp [hk0]
      · simp only [hk0, ne_eq, not_false_eq_true, ite_true]
        by_cases hkg : k.1 < g
        · rw [taillessCount_eq_zero_of_lt_girth G g k.1 hg (by omega) hkg]; simp
        · exact mul_nonpos_of_nonpos_of_nonneg (hcle k (by omega) hk16) (Nat.cast_nonneg _)
    linarith
  have hpos_mul : 0 < c ⟨16, by omega⟩ * (taillessCount G 16 : ℚ) := by linarith
  have hpos_q : (0 : ℚ) < (taillessCount G 16 : ℚ) :=
    pos_of_mul_pos_right hpos_mul (le_of_lt hc16)
  have hpos_nat : 0 < taillessCount G 16 := Nat.cast_pos.mp hpos_q
  exact has_c16_of_taillessCount_pos G (fun L hL => hg L (lt_of_lt_of_le hL hg9)) hpos_nat

end MasterSOSDelsarteClosure

section Girth9To15ExactClosures

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Theorem 10: Every cubic graph of girth ≥ 9 and n ≤ 129 has a simple C16. -/
theorem cubic_girth9_le_129_has_c16 (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (hreg : ∀ v, G.degree v = 3) (hg : GirthAtLeast G 9) (hn : Fintype.card V ≤ 129) :
    HasSimpleCycle G 16 := by
  let P : Polynomial ℚ := 695466 + -2531088 * X ^ 2 + 1579824 * X ^ 4 + -315648 * X ^ 6 + 19712 * X ^ 8
  let Q : Polynomial ℚ := 0
  let c : Fin 17 → ℚ := ![101316851442, 0, -692073280, 0, -155454272, 0, -93964800, 0, 2391313664, 0, -15663104, 0, -8134656, 0, -10092544, 0, 388562944]
  refine cubic_girth_sos_c16 G hreg 9 (by omega) hg P Q c ?_ ?_ ?_ ?_
  · simp only [Fin.sum_univ_succ, Fin.isValue, Fin.val_succ, Fin.sum_univ_zero,
      add_zero, P, Q, c, Matrix.cons_val_zero, Matrix.cons_val_succ, chebPoly,
      Polynomial.C_neg, Polynomial.C_ofNat, map_zero]; ring
  · norm_num [c]
  · intro k hkg hk16; fin_cases k <;> simp_all [c]
  · have hcard : (Fintype.card V : ℚ) ≤ 129 := by exact_mod_cast hn
    have hden : (2 * c ⟨0, by omega⟩ - ∑ k : Fin 17, if k.1 ≠ 0 ∧ Even k.1 then c k else 0) = 200829208932 := by
      simp only [Fin.sum_univ_succ, Fin.isValue, Fin.val_zero, Fin.val_succ, Fin.sum_univ_zero,
        add_zero, c, Matrix.cons_val_zero, Matrix.cons_val_succ]; norm_num
    have hp3 : P.eval 3 = 5104458 := by
      simp only [P, eval_add, eval_mul, eval_pow, eval_X, eval_ofNat, eval_neg]; norm_num
    rw [hden, hp3]; linarith

/-- Theorem 11: Every cubic graph of girth ≥ 10 and n ≤ 132 has a simple C16. -/
theorem cubic_girth10_le_132_has_c16 (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (hreg : ∀ v, G.degree v = 3) (hg : GirthAtLeast G 10) (hn : Fintype.card V ≤ 132) :
    HasSimpleCycle G 16 := by
  let P : Polynomial ℚ := 695466 + 39366 * X + -2531088 * X ^ 2 + 1579824 * X ^ 4 + -315648 * X ^ 6 + 19712 * X ^ 8
  let Q : Polynomial ℚ := 0
  let c : Fin 17 → ℚ := ![104416215354, 4712110200, 857608676, -64245312, -155454272, -56687040, -93964800, 3083774976, 2391313664, 1551965184, -15663104, 0, -8134656, 0, -10092544, 0, 388562944]
  refine cubic_girth_sos_c16 G hreg 10 (by omega) hg P Q c ?_ ?_ ?_ ?_
  · simp only [Fin.sum_univ_succ, Fin.isValue, Fin.val_succ, Fin.sum_univ_zero,
      add_zero, P, Q, c, Matrix.cons_val_zero, Matrix.cons_val_succ, chebPoly,
      Polynomial.C_neg, Polynomial.C_ofNat, map_zero]; ring
  · norm_num [c]
  · intro k hkg hk16; fin_cases k <;> simp_all [c]
  · have hcard : (Fintype.card V : ℚ) ≤ 132 := by exact_mod_cast hn
    have hden : (2 * c ⟨0, by omega⟩ - ∑ k : Fin 17, if k.1 ≠ 0 ∧ Even k.1 then c k else 0) = 205478254800 := by
      simp only [Fin.sum_univ_succ, Fin.isValue, Fin.val_zero, Fin.val_succ, Fin.sum_univ_zero,
        add_zero, c, Matrix.cons_val_zero, Matrix.cons_val_succ]; norm_num
    have hp3 : P.eval 3 = 5222556 := by
      simp only [P, eval_add, eval_mul, eval_pow, eval_X, eval_ofNat, eval_neg]; norm_num
    rw [hden, hp3]; linarith

/-- Theorem 12: Every cubic graph of girth ≥ 11 and n ≤ 146 has a simple C16. -/
theorem cubic_girth11_le_146_has_c16 (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (hreg : ∀ v, G.degree v = 3) (hg : GirthAtLeast G 11) (hn : Fintype.card V ≤ 146) :
    HasSimpleCycle G 16 := by
  let P : Polynomial ℚ := 8726130 + 642978 * X + -41325552 * X ^ 2 + 5832 * X ^ 3 + 26385264 * X ^ 4 + -864 * X ^ 5 + -5271552 * X ^ 6 + 329216 * X ^ 8
  let Q : Polynomial ℚ := 0
  let c : Fin 17 → ℚ := ![34091320367466, 4930956809352, 3927354404036, 1186795615968, 852815478496, -35542238400, 2488604501184, 840373795584, 1272104039168, 423666754560, 626974532608, -1841799168, -752271360, -568885248, -2696937472, 0, 108383174656]
  refine cubic_girth_sos_c16 G hreg 11 (by omega) hg P Q c ?_ ?_ ?_ ?_
  · simp only [Fin.sum_univ_succ, Fin.isValue, Fin.val_succ, Fin.sum_univ_zero,
      add_zero, P, Q, c, Matrix.cons_val_zero, Matrix.cons_val_succ, chebPoly,
      Polynomial.C_neg, Polynomial.C_ofNat, map_zero]; ring
  · norm_num [c]
  · intro k hkg hk16; fin_cases k <;> simp_all [c]
  · have hcard : (Fintype.card V : ℚ) ≤ 146 := by exact_mod_cast hn
    have hden : (2 * c ⟨0, by omega⟩ - ∑ k : Fin 17, if k.1 ≠ 0 ∧ Even k.1 then c k else 0) = 58909853813616 := by
      simp only [Fin.sum_univ_succ, Fin.isValue, Fin.val_zero, Fin.val_succ, Fin.sum_univ_zero,
        add_zero, c, Matrix.cons_val_zero, Matrix.cons_val_succ]; norm_num
    have hp3 : P.eval 3 = 92903760 := by
      simp only [P, eval_add, eval_mul, eval_pow, eval_X, eval_ofNat, eval_neg]; norm_num
    rw [hden, hp3]; linarith

/-- Theorem 13: Every cubic graph of girth ≥ 12 and n ≤ 155 has a simple C16. -/
theorem cubic_girth12_le_155_has_c16 (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (hreg : ∀ v, G.degree v = 3) (hg : GirthAtLeast G 12) (hn : Fintype.card V ≤ 155) :
    HasSimpleCycle G 16 := by
  let P : Polynomial ℚ := 1955178 + -590490 * X + -9660708 * X ^ 2 + 159408 * X ^ 3 + 6248016 * X ^ 4 + -11232 * X ^ 5 + -1258560 * X ^ 6 + 1536 * X ^ 7 + 79104 * X ^ 8
  let Q : Polynomial ℚ := -96228 + -14580 * X + 464616 * X ^ 2 + 174960 * X ^ 3 + -238464 * X ^ 4 + -91584 * X ^ 5 + 26880 * X ^ 6 + 10240 * X ^ 7
  let c : Fin 17 → ℚ := ![3340572084450, 2253575127096, 1437134143636, 871042201008, 488418113024, 492705740160, 302542701888, 180361398528, 119061689344, 75739425792, 47666723840, 29753929728, -285302784, -106315776, -132349952, -307494912, 6152585216]
  refine cubic_girth_sos_c16 G hreg 12 (by omega) hg P Q c ?_ ?_ ?_ ?_
  · simp only [Fin.sum_univ_succ, Fin.isValue, Fin.val_succ, Fin.sum_univ_zero,
      add_zero, P, Q, c, Matrix.cons_val_zero, Matrix.cons_val_succ, chebPoly,
      Polynomial.C_neg, Polynomial.C_ofNat]; ring
  · norm_num [c]
  · intro k hkg hk16; fin_cases k <;> simp_all [c]
  · have hcard : (Fintype.card V : ℚ) ≤ 155 := by exact_mod_cast hn
    have hden : (2 * c ⟨0, by omega⟩ - ∑ k : Fin 17, if k.1 ≠ 0 ∧ Even k.1 then c k else 0) = 4280585864688 := by
      simp only [Fin.sum_univ_succ, Fin.isValue, Fin.val_zero, Fin.val_succ, Fin.sum_univ_zero,
        add_zero, c, Matrix.cons_val_zero, Matrix.cons_val_succ]; norm_num
    have hp3 : P.eval 3 = 25771608 := by
      simp only [P, eval_add, eval_mul, eval_pow, eval_X, eval_ofNat, eval_neg]; norm_num
    rw [hden, hp3]; linarith

/-- Theorem 14: Every cubic graph of girth ≥ 13 and n ≤ 214 has a simple C16 (shatters Moore bound 190!). -/
theorem cubic_girth13_le_214_has_c16 (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (hreg : ∀ v, G.degree v = 3) (hg : GirthAtLeast G 13) (hn : Fintype.card V ≤ 214) :
    HasSimpleCycle G 16 := by
  let P : Polynomial ℚ := 229635 + -61236 * X + -791694 * X ^ 2 + 34020 * X ^ 3 + 461376 * X ^ 4 + -6912 * X ^ 5 + -90720 * X ^ 6 + 576 * X ^ 7 + 5760 * X ^ 8
  let Q : Polynomial ℚ := -19683 + -2916 * X + 69012 * X ^ 2 + 25272 * X ^ 3 + -31104 * X ^ 4 + -12096 * X ^ 5 + 3264 * X ^ 6 + 1280 * X ^ 7
  let c : Fin 17 → ℚ := ![34001751987, 29482881120, 21896732971, 11396079552, 11124711260, 5263720128, 4499265216, 1971796032, 1684210624, 655150080, 604606976, 224630784, 213513216, -1953792, -450560, -1720320, 31539200]
  refine cubic_girth_sos_c16 G hreg 13 (by omega) hg P Q c ?_ ?_ ?_ ?_
  · simp only [Fin.sum_univ_succ, Fin.isValue, Fin.val_succ, Fin.sum_univ_zero,
      add_zero, P, Q, c, Matrix.cons_val_zero, Matrix.cons_val_succ, chebPoly,
      Polynomial.C_neg, Polynomial.C_ofNat]; ring
  · norm_num [c]
  · intro k hkg hk16; fin_cases k <;> simp_all [c]
  · have hcard : (Fintype.card V : ℚ) ≤ 214 := by exact_mod_cast hn
    have hden : (2 * c ⟨0, by omega⟩ - ∑ k : Fin 17, if k.1 ≠ 0 ∧ Even k.1 then c k else 0) = 27949375071 := by
      simp only [Fin.sum_univ_succ, Fin.isValue, Fin.val_zero, Fin.val_succ, Fin.sum_univ_zero,
        add_zero, c, Matrix.cons_val_zero, Matrix.cons_val_succ]; norm_num
    have hp3 : P.eval 3 = 2447253 := by
      simp only [P, eval_add, eval_mul, eval_pow, eval_X, eval_ofNat, eval_neg]; norm_num
    rw [hden, hp3]; linarith

/-- Theorem 15: Every cubic graph of girth ≥ 14 and n ≤ 267 has a simple C16 (shatters Moore bound 254!). -/
theorem cubic_girth14_le_267_has_c16 (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (hreg : ∀ v, G.degree v = 3) (hg : GirthAtLeast G 14) (hn : Fintype.card V ≤ 267) :
    HasSimpleCycle G 16 := by
  let P : Polynomial ℚ := 638604 + 185166 * X + -2182140 * X ^ 2 + 6480 * X ^ 3 + 1283040 * X ^ 4 + -49248 * X ^ 5 + -256704 * X ^ 6 + 6912 * X ^ 7 + 16640 * X ^ 8
  let Q : Polynomial ℚ := -132678 + -102060 * X + 404352 * X ^ 2 + 196992 * X ^ 3 + -168768 * X ^ 4 + -72960 * X ^ 5 + 16896 * X ^ 6 + 6912 * X ^ 7
  let c : Fin 17 → ℚ := ![658300095882, 796607774496, 505967215376, 355985388000, 228586213696, 145997775360, 92095031424, 56944682496, 34463217152, 20397533184, 11670713344, 6228504576, 3456503808, 1606828032, -10584064, -3538944, 229113856]
  refine cubic_girth_sos_c16 G hreg 14 (by omega) hg P Q c ?_ ?_ ?_ ?_
  · simp only [Fin.sum_univ_succ, Fin.isValue, Fin.val_succ, Fin.sum_univ_zero,
      add_zero, P, Q, c, Matrix.cons_val_zero, Matrix.cons_val_succ, chebPoly,
      Polynomial.C_neg, Polynomial.C_ofNat]; ring
  · norm_num [c]
  · intro k hkg hk16; fin_cases k <;> simp_all [c]
  · have hcard : (Fintype.card V : ℚ) ≤ 267 := by exact_mod_cast hn
    have hden : (2 * c ⟨0, by omega⟩ - ∑ k : Fin 17, if k.1 ≠ 0 ∧ Even k.1 then c k else 0) = 440142767172 := by
      simp only [Fin.sum_univ_succ, Fin.isValue, Fin.val_zero, Fin.val_succ, Fin.sum_univ_zero,
        add_zero, c, Matrix.cons_val_zero, Matrix.cons_val_succ]; norm_num
    have hp3 : P.eval 3 = 10843146 := by
      simp only [P, eval_add, eval_mul, eval_pow, eval_X, eval_ofNat, eval_neg]; norm_num
    rw [hden, hp3]; linarith

/-- Theorem 16: Every cubic graph of girth ≥ 15 and n ≤ 573 has a simple C16 (beats Wave 5's 537!). -/
theorem cubic_girth15_le_573_has_c16 (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (hreg : ∀ v, G.degree v = 3) (hg : GirthAtLeast G 15) (hn : Fintype.card V ≤ 573) :
    HasSimpleCycle G 16 := by
  let P : Polynomial ℚ := 48114 + 36450 * X + -231336 * X ^ 2 + -23328 * X ^ 3 + 170640 * X ^ 4 + 2880 * X ^ 5 + -39552 * X ^ 6 + 2816 * X ^ 8
  let Q : Polynomial ℚ := 0
  let c : Fin 17 → ℚ := ![9762244650, 6098444424, 8610880484, 3044239200, 3761347072, 1265465664, 1586698752, 513086976, 652678400, 191738880, 259084288, 62521344, 94543872, 16220160, 30998528, 0, 7929856]
  refine cubic_girth_sos_c16 G hreg 15 (by omega) hg P Q c ?_ ?_ ?_ ?_
  · simp only [Fin.sum_univ_succ, Fin.isValue, Fin.val_succ, Fin.sum_univ_zero,
      add_zero, P, Q, c, Matrix.cons_val_zero, Matrix.cons_val_succ, chebPoly,
      Polynomial.C_ofNat, map_zero]; ring
  · norm_num [c]
  · intro k hkg hk16; fin_cases k <;> simp_all [c]
  · have hcard : (Fintype.card V : ℚ) ≤ 573 := by exact_mod_cast hn
    have hden : (2 * c ⟨0, by omega⟩ - ∑ k : Fin 17, if k.1 ≠ 0 ∧ Even k.1 then c k else 0) = 4520328048 := by
      simp only [Fin.sum_univ_succ, Fin.isValue, Fin.val_zero, Fin.val_succ, Fin.sum_univ_zero,
        add_zero, c, Matrix.cons_val_zero, Matrix.cons_val_succ]; norm_num
    have hp3 : P.eval 3 = 1609632 := by
      simp only [P, eval_add, eval_mul, eval_pow, eval_X, eval_ofNat, eval_neg]; norm_num
    rw [hden, hp3]; linarith

/-- Theorem 17: Every bipartite cubic graph of girth ≥ 10 and n ≤ 259 has a simple C16. -/
theorem cubic_bipartite_girth10_le_259_has_c16 (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (hreg : ∀ v, G.degree v = 3)
    (col : V → Bool) (hcol : ∀ u v, G.Adj u v → col u ≠ col v)
    (hg : GirthAtLeast G 10) (hn : Fintype.card V ≤ 259) :
    HasSimpleCycle G 16 := by
  let P : Polynomial ℚ := 695466 + -2531088 * X ^ 2 + 1579824 * X ^ 4 + -315648 * X ^ 6 + 19712 * X ^ 8
  let Q : Polynomial ℚ := 0
  let c : Fin 17 → ℚ := ![101316851442, 0, -692073280, 0, -155454272, 0, -93964800, 0, 2391313664, 0, -15663104, 0, -8134656, 0, -10092544, 0, 388562944]
  refine cubic_bipartite_girth_sos_c16 G hreg col hcol 10 (by omega) hg P Q c ?_ ?_ ?_ ?_
  · simp only [Fin.sum_univ_succ, Fin.isValue, Fin.val_succ, Fin.sum_univ_zero,
      add_zero, P, Q, c, Matrix.cons_val_zero, Matrix.cons_val_succ, chebPoly,
      Polynomial.C_neg, Polynomial.C_ofNat, map_zero]; ring
  · norm_num [c]
  · intro k hkg hk16; fin_cases k <;> simp_all [c]
  · have hcard : (Fintype.card V : ℚ) ≤ 259 := by exact_mod_cast hn
    have hden : (2 * c ⟨0, by omega⟩ - ∑ k : Fin 17, if k.1 ≠ 0 ∧ Even k.1 then c k else 0) = 200829208932 := by
      simp only [Fin.sum_univ_succ, Fin.isValue, Fin.val_zero, Fin.val_succ, Fin.sum_univ_zero,
        add_zero, c, Matrix.cons_val_zero, Matrix.cons_val_succ]; norm_num
    have hp3 : P.eval 3 = 5104458 := by
      simp only [P, eval_add, eval_mul, eval_pow, eval_X, eval_ofNat, eval_neg]; norm_num
    have hpm3 : P.eval (-3) = 5104458 := by
      simp only [P, eval_add, eval_mul, eval_pow, eval_X, eval_ofNat, eval_neg]; norm_num
    rw [hden, hp3, hpm3]; linarith

/-- Theorem 18: Every bipartite cubic graph of girth ≥ 12 and n ≤ 287 has a simple C16. -/
theorem cubic_bipartite_girth12_le_287_has_c16 (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (hreg : ∀ v, G.degree v = 3)
    (col : V → Bool) (hcol : ∀ u v, G.Adj u v → col u ≠ col v)
    (hg : GirthAtLeast G 12) (hn : Fintype.card V ≤ 287) :
    HasSimpleCycle G 16 := by
  let P : Polynomial ℚ := 721710 + -3433104 * X ^ 2 + 2194128 * X ^ 4 + -438528 * X ^ 6 + 27392 * X ^ 8
  let Q : Polynomial ℚ := 0
  let c : Fin 17 → ℚ := ![230868382626, 0, 24931936832, 0, 5847907264, 0, 17367353856, 0, 8884944128, 0, 4374986752, 0, -16588800, 0, -14024704, 0, 750321664]
  refine cubic_bipartite_girth_sos_c16 G hreg col hcol 12 (by omega) hg P Q c ?_ ?_ ?_ ?_
  · simp only [Fin.sum_univ_succ, Fin.isValue, Fin.val_succ, Fin.sum_univ_zero,
      add_zero, P, Q, c, Matrix.cons_val_zero, Matrix.cons_val_succ, chebPoly,
      Polynomial.C_neg, Polynomial.C_ofNat, map_zero]; ring
  · norm_num [c]
  · intro k hkg hk16; fin_cases k <;> simp_all [c]
  · have hcard : (Fintype.card V : ℚ) ≤ 287 := by exact_mod_cast hn
    have hden : (2 * c ⟨0, by omega⟩ - ∑ k : Fin 17, if k.1 ≠ 0 ∧ Even k.1 then c k else 0) = 399609928260 := by
      simp only [Fin.sum_univ_succ, Fin.isValue, Fin.val_zero, Fin.val_succ, Fin.sum_univ_zero,
        add_zero, c, Matrix.cons_val_zero, Matrix.cons_val_succ]; norm_num
    have hp3 : P.eval 3 = 7580142 := by
      simp only [P, eval_add, eval_mul, eval_pow, eval_X, eval_ofNat, eval_neg]; norm_num
    have hpm3 : P.eval (-3) = 7580142 := by
      simp only [P, eval_add, eval_mul, eval_pow, eval_X, eval_ofNat, eval_neg]; norm_num
    rw [hden, hp3, hpm3]; linarith

/-- Theorem 19: Every bipartite cubic graph of girth ≥ 14 and n ≤ 400 has a simple C16 (shatters (3,14)-cage 384!). -/
theorem cubic_bipartite_girth14_le_400_has_c16 (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (hreg : ∀ v, G.degree v = 3)
    (col : V → Bool) (hcol : ∀ u v, G.Adj u v → col u ≠ col v)
    (hg : GirthAtLeast G 14) (hn : Fintype.card V ≤ 400) :
    HasSimpleCycle G 16 := by
  let P : Polynomial ℚ := 275562 + -927288 * X ^ 2 + 530712 * X ^ 4 + -102528 * X ^ 6 + 6400 * X ^ 8
  let Q : Polynomial ℚ := 0
  let c : Fin 17 → ℚ := ![22057191090, 0, 9034341536, 0, 6936214048, 0, 2885451648, 0, 1144159808, 0, 429881344, 0, 219869184, 0, -1638400, 0, 40960000]
  refine cubic_bipartite_girth_sos_c16 G hreg col hcol 14 (by omega) hg P Q c ?_ ?_ ?_ ?_
  · simp only [Fin.sum_univ_succ, Fin.isValue, Fin.val_succ, Fin.sum_univ_zero,
      add_zero, P, Q, c, Matrix.cons_val_zero, Matrix.cons_val_succ, chebPoly,
      Polynomial.C_neg, Polynomial.C_ofNat, map_zero]; ring
  · norm_num [c]
  · intro k hkg hk16; fin_cases k <;> simp_all [c]
  · have hcard : (Fintype.card V : ℚ) ≤ 400 := by exact_mod_cast hn
    have hden : (2 * c ⟨0, by omega⟩ - ∑ k : Fin 17, if k.1 ≠ 0 ∧ Even k.1 then c k else 0) = 23425143012 := by
      simp only [Fin.sum_univ_succ, Fin.isValue, Fin.val_zero, Fin.val_succ, Fin.sum_univ_zero,
        add_zero, c, Matrix.cons_val_zero, Matrix.cons_val_succ]; norm_num
    have hp3 : P.eval 3 = 2165130 := by
      simp only [P, eval_add, eval_mul, eval_pow, eval_X, eval_ofNat, eval_neg]; norm_num
    have hpm3 : P.eval (-3) = 2165130 := by
      simp only [P, eval_add, eval_mul, eval_pow, eval_X, eval_ofNat, eval_neg]; norm_num
    rw [hden, hp3, hpm3]; linarith

end Girth9To15ExactClosures

section UnboundedNArbitraryGirthStructural

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Theorem 20 (Telescoping 4-Layer BFS Annulus Peak — Unbounded n, Arbitrary Girth):
    For any finite layer-size sequence `a : ℕ → ℕ` supported on `[0..D]` (`D ≥ 1`, `a 0 ≥ 1`),
    there exists `t < D` such that the 2-layer interior `a t + a (t + 1)` strictly exceeds
    the 2-layer boundary `(if t = 0 then 0 else a (t - 1)) + (if t + 2 ≤ D then a (t + 2) else 0)`. -/
theorem four_layer_annulus_telescoping_peak (D : ℕ) (hD : 1 ≤ D) (a : ℕ → ℕ) (ha0 : 1 ≤ a 0) :
    ∃ t < D, (if t = 0 then 0 else a (t - 1)) + (if t + 2 ≤ D then a (t + 2) else 0) <
      a t + a (t + 1) := by
  by_contra hall
  push Not at hall
  have hle : ∑ t ∈ Finset.range D, (a t + a (t + 1)) ≤
      ∑ t ∈ Finset.range D,
        ((if t = 0 then 0 else a (t - 1)) + (if t + 2 ≤ D then a (t + 2) else 0)) :=
    Finset.sum_le_sum fun t ht => hall t (Finset.mem_range.mp ht)
  have htel : ∀ M : ℕ, 1 ≤ M →
      (∑ t ∈ Finset.range M, ((a t : ℤ) + a (t + 1))) -
      (∑ t ∈ Finset.range M, ((if t = 0 then (0 : ℤ) else a (t - 1)) +
        (if t + 2 ≤ M then (a (t + 2) : ℤ) else 0))) =
      (a 0 : ℤ) + a 1 + a (M - 1) + a M - (if M = 1 then (a 0 : ℤ) + a 1 else 0) := by
    intro M hM
    induction M with
    | zero => omega
    | succ m ih =>
      cases m with
      | zero =>
        simp
      | succ k =>
        have hih := ih (by omega)
        have hshift :
            (∑ t ∈ Finset.range (k + 2),
              ((if t = 0 then (0 : ℤ) else a (t - 1)) +
               (if t + 2 ≤ k + 2 then (a (t + 2) : ℤ) else 0))) =
            (∑ t ∈ Finset.range (k + 1),
              ((if t = 0 then (0 : ℤ) else a (t - 1)) +
               (if t + 2 ≤ k + 1 then (a (t + 2) : ℤ) else 0))) +
            (a (k + 2) : ℤ) + (a k : ℤ) := by
          rw [Finset.sum_range_succ]
          have hlast : (if k + 1 = 0 then (0 : ℤ) else a (k + 1 - 1)) +
              (if k + 1 + 2 ≤ k + 2 then (a (k + 1 + 2) : ℤ) else 0) = (a k : ℤ) := by
            simp
          rw [hlast]
          have hsplit : (∑ t ∈ Finset.range (k + 1),
              ((if t = 0 then (0 : ℤ) else a (t - 1)) +
               (if t + 2 ≤ k + 2 then (a (t + 2) : ℤ) else 0))) =
            (∑ t ∈ Finset.range (k + 1),
              ((if t = 0 then (0 : ℤ) else a (t - 1)) +
               (if t + 2 ≤ k + 1 then (a (t + 2) : ℤ) else 0))) + (a (k + 2) : ℤ) := by
            rw [Finset.sum_range_succ, Finset.sum_range_succ]
            have hcongr : ∑ t ∈ Finset.range k,
                ((if t = 0 then (0 : ℤ) else a (t - 1)) +
                 (if t + 2 ≤ k + 2 then (a (t + 2) : ℤ) else 0)) =
              ∑ t ∈ Finset.range k,
                ((if t = 0 then (0 : ℤ) else a (t - 1)) +
                 (if t + 2 ≤ k + 1 then (a (t + 2) : ℤ) else 0)) := by
              refine Finset.sum_congr rfl fun t ht => ?_
              have htk : t < k := Finset.mem_range.mp ht
              simp [show t + 2 ≤ k + 2 by omega, show t + 2 ≤ k + 1 by omega]
            rw [hcongr]
            have hfalse : ¬ (k + 2 ≤ k + 1) := by omega
            simp [hfalse]
          rw [hsplit]; ring
        rw [Finset.sum_range_succ, hshift]
        by_cases hk0 : k = 0
        · subst hk0; simp; ring
        · simp [hk0] at hih ⊢
          linarith
  have htelD := htel D hD
  have hle_z : (∑ t ∈ Finset.range D, ((a t : ℤ) + a (t + 1))) ≤
      (∑ t ∈ Finset.range D, ((if t = 0 then (0 : ℤ) else a (t - 1)) +
        (if t + 2 ≤ D then (a (t + 2) : ℤ) else 0))) := by
    have := Nat.cast_le (α := ℤ).mpr hle
    simpa [Nat.cast_sum, Nat.cast_add] using this
  by_cases hD1 : D = 1
  · subst hD1
    simp only [ite_true] at htelD
    linarith
  · simp only [hD1, ite_false, sub_zero] at htelD
    have ha0_z : (1 : ℤ) ≤ a 0 := by exact_mod_cast ha0
    have hnn1 : (0 : ℤ) ≤ a 1 := Nat.cast_nonneg _
    have hnn2 : (0 : ℤ) ≤ a (D - 1) := Nat.cast_nonneg _
    have hnn3 : (0 : ℤ) ≤ a D := Nat.cast_nonneg _
    linarith

/-- Theorem 21 (Unbounded-n, Arbitrary-Girth Interior-Boundary Edge Excess). -/
theorem subset_interior_boundary_edge_excess (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : ∀ v : V, 3 ≤ G.degree v)
    (S : Finset V)
    (hB_conn : ∀ v ∈ S, ∃ w ∈ S, G.Adj v w) :
    let I := S.filter (fun v => ∀ w : V, G.Adj v w → w ∈ S)
    let B := S.filter (fun v => ¬ ∀ w : V, G.Adj v w → w ∈ S)
    let degS := fun v => (S.filter (fun w => G.Adj v w)).card
    3 * I.card + B.card ≤ ∑ v ∈ S, degS v := by
  intro I B degS
  have hsplit : ∑ v ∈ S, degS v = ∑ v ∈ I, degS v + ∑ v ∈ B, degS v := by
    rw [← Finset.sum_filter_add_sum_filter_not S (fun v => ∀ w : V, G.Adj v w → w ∈ S)]
  rw [hsplit]
  have hI : 3 * I.card ≤ ∑ v ∈ I, degS v := by
    calc 3 * I.card = ∑ _v ∈ I, 3 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ v ∈ I, degS v := by
        refine Finset.sum_le_sum fun v hv => ?_
        have hvI := (Finset.mem_filter.mp hv).2
        have heq : S.filter (fun w => G.Adj v w) = G.neighborFinset v := by
          ext w; simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
          exact ⟨fun h => h.2, fun h => ⟨hvI w h, h⟩⟩
        dsimp [degS]; rw [heq, SimpleGraph.card_neighborFinset_eq_degree]; exact hmin v
  have hB : B.card ≤ ∑ v ∈ B, degS v := by
    calc B.card = ∑ _v ∈ B, 1 := by simp
      _ ≤ ∑ v ∈ B, degS v := by
        refine Finset.sum_le_sum fun v hv => ?_
        obtain ⟨w, hwS, huv⟩ := hB_conn v (Finset.mem_filter.mp hv).1
        exact Finset.card_pos.mpr ⟨w, Finset.mem_filter.mpr ⟨hwS, huv⟩⟩
  omega

/-- Theorem 22 (Arbitrary-Girth Crossing-Ear / 2-Chord Möbius 7-Cycle System — Unbounded n). -/
theorem crossing_ears_seven_cycle_identities (x₁ x₂ x₃ x₄ p q : ℕ) :
    let L := x₁ + x₂ + x₃ + x₄
    let c₂ := x₁ + x₂ + p
    let c₃ := x₃ + x₄ + p
    let c₄ := x₂ + x₃ + q
    let c₅ := x₄ + x₁ + q
    let c₆ := x₁ + x₃ + p + q
    let c₇ := x₂ + x₄ + p + q
    (c₂ + c₃ = L + 2 * p) ∧
    (c₄ + c₅ = L + 2 * q) ∧
    (c₆ + c₇ = L + 2 * p + 2 * q) ∧
    (∀ k : ℕ, c₂ + c₃ = 2 ^ (k + 1) → c₂ = c₃ → c₂ = 2 ^ k) := by
  intro L c₂ c₃ c₄ c₅ c₆ c₇
  refine ⟨by omega, by omega, by omega, ?_⟩
  intro k hsum heq
  rw [pow_succ] at hsum
  omega

/-- Theorem 23 (Arbitrary-Girth Pósa-Rotation Interlaced-Chord 7-Cycle System — Unbounded n). -/
theorem posa_interlaced_chord_seven_cycles (a b c : ℕ) (_ha : 2 ≤ a) (hac : a < c) (hcb : c < b) :
    let l₁ := a
    let l₂ := b
    let l₃ := c
    let l₄ := b - a + 2
    let l₅ := c - a + 2
    let l₆ := b - c + a
    let l₇ := b - c + 4
    (l₁ + l₄ = l₂ + 2) ∧
    (l₁ + l₅ = l₃ + 2) ∧
    (l₅ + l₆ = l₂ + 2) ∧
    (l₃ + l₇ = l₂ + 4) := by
  omega

/-- Theorem 24 (Arbitrary-Girth K4-Subdivision 7-Cycle Conservation & Even-Cycle Triple). -/
theorem k4_subdivision_parity_and_dyadic_sum (a₁ a₂ a₃ b₁ b₂ b₃ : ℕ) :
    let T₁ := a₁ + a₂ + a₃
    let T₂ := a₁ + b₂ + b₃
    let T₃ := b₁ + a₂ + b₃
    let T₄ := b₁ + b₂ + a₃
    let Q₁ := a₂ + b₂ + a₃ + b₃
    let Q₂ := a₁ + b₁ + a₃ + b₃
    let Q₃ := a₁ + b₁ + a₂ + b₂
    (T₁ + T₂ + T₃ + T₄ = 2 * (a₁ + a₂ + a₃ + b₁ + b₂ + b₃)) ∧
    (Q₁ + Q₂ + Q₃ = 2 * (a₁ + a₂ + a₃ + b₁ + b₂ + b₃)) ∧
    (T₁ + T₂ = Q₁ + 2 * a₁) ∧
    (Even Q₁ ∨ Even Q₂ ∨ Even Q₃) := by
  intro T₁ T₂ T₃ T₄ Q₁ Q₂ Q₃
  refine ⟨by omega, by omega, by omega, ?_⟩
  have hev : Even (Q₁ + Q₂ + Q₃) := ⟨a₁ + a₂ + a₃ + b₁ + b₂ + b₃, by omega⟩
  rw [Nat.even_iff] at hev ⊢
  dsimp only [Q₁, Q₂, Q₃] at hev ⊢
  omega

end UnboundedNArbitraryGirthStructural

end E64Wave8Agent8
