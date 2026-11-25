import Core

namespace E64Leaves
open SimpleGraph Erdos64Closure E64Core
universe u

def Cubic {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop := ∀ v, G.degree v=3
def SubcubicDefect {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop :=
  ∃ w, G.degree w=2 ∧ ∀ v, v≠w → G.degree v=3
def HighDefect {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop :=
  ∃ w, G.degree w=2 ∧ (∀ v, v≠w → 3≤G.degree v) ∧ ∃ a, 4≤G.degree a

def Bip {V : Type u} (G : SimpleGraph V) : Prop :=
  ∃ color : V → Bool, ∀ a b, G.Adj a b → color a ≠ color b

def Triangle {V : Type u} (G : SimpleGraph V) : Prop :=
  ∃ a b c, G.Adj a b ∧ G.Adj b c ∧ G.Adj c a

-- Count each undirected crossing edge once, oriented from S to its complement.
-- Both sides must contain at least two vertices; singleton cuts do not count.
def SmallCut {V : Type u} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ S : Set V, 2 ≤ Nat.card S ∧ 2 ≤ Nat.card (Sᶜ : Set V) ∧
    Nat.card {e : V × V // e.1 ∈ S ∧ e.2 ∉ S ∧ G.Adj e.1 e.2} ≤ k

inductive Separation where
  | low2 | low3 | core
  deriving DecidableEq, Repr

inductive HighSeparation where
  | low2 | low3 | core4 | core5
  deriving DecidableEq, Repr

def SepCase {V : Type u} (G : SimpleGraph V) : Separation → Prop
  | .low2 => SmallCut G 2
  | .low3 => ¬SmallCut G 2 ∧ SmallCut G 3
  | .core => ¬SmallCut G 2 ∧ ¬SmallCut G 3

def HighSepCase {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : HighSeparation → Prop
  | .low2 => SmallCut G 2
  | .low3 => ¬SmallCut G 2 ∧ SmallCut G 3
  | .core4 => ¬SmallCut G 2 ∧ ¬SmallCut G 3 ∧ ∀ v, G.degree v≤4
  | .core5 => ¬SmallCut G 2 ∧ ¬SmallCut G 3 ∧ ∃ v, 5≤G.degree v

-- Exactly 2+4*3+3*4=26 terminal cases. The cases describe actual
-- minimal counterexamples, not prescribed proof methods.
inductive Leaf where
  | cb | sb
  | ct (s : Separation) | cn (s : Separation)
  | st (s : Separation) | sn (s : Separation)
  | hb (s : HighSeparation) | ht (s : HighSeparation)
  | hn (s : HighSeparation)
  deriving DecidableEq, Repr

def InLeaf {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Leaf → Prop
  | .cb => Cubic G ∧ Bip G
  | .sb => SubcubicDefect G ∧ Bip G
  | .ct s => Cubic G ∧ ¬Bip G ∧ Triangle G ∧ SepCase G s
  | .cn s => Cubic G ∧ ¬Bip G ∧ ¬Triangle G ∧ SepCase G s
  | .st s => SubcubicDefect G ∧ ¬Bip G ∧ Triangle G ∧ SepCase G s
  | .sn s => SubcubicDefect G ∧ ¬Bip G ∧ ¬Triangle G ∧ SepCase G s
  | .hb s => HighDefect G ∧ Bip G ∧ HighSepCase G s
  | .ht s => HighDefect G ∧ ¬Bip G ∧ Triangle G ∧ HighSepCase G s
  | .hn s => HighDefect G ∧ ¬Bip G ∧ ¬Triangle G ∧ HighSepCase G s

theorem separation_cover {V : Type u} (G : SimpleGraph V) :
    ∃ s, SepCase G s := by
  classical
  by_cases h2 : SmallCut G 2
  · exact ⟨.low2,h2⟩
  by_cases h3 : SmallCut G 3
  · exact ⟨.low3,h2,h3⟩
  · exact ⟨.core,h2,h3⟩

theorem high_separation_cover {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ∃ s, HighSepCase G s := by
  classical
  by_cases h2 : SmallCut G 2
  · exact ⟨.low2,h2⟩
  by_cases h3 : SmallCut G 3
  · exact ⟨.low3,h2,h3⟩
  by_cases h4 : ∀ v, G.degree v≤4
  · exact ⟨.core4,h2,h3,h4⟩
  · push Not at h4
    obtain ⟨v,hv⟩ := h4
    exact ⟨.core5,h2,h3,v,by omega⟩

theorem cover {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hm : MinimalBad G) : ∃ l, InLeaf G l := by
  classical
  rcases degree_partition G hm with hC | hS | hH
  · by_cases hB : Bip G
    · exact ⟨.cb,hC,hB⟩
    obtain ⟨s,hs⟩ := separation_cover G
    by_cases hT : Triangle G
    · exact ⟨.ct s,hC,hB,hT,hs⟩
    · exact ⟨.cn s,hC,hB,hT,hs⟩
  · by_cases hB : Bip G
    · exact ⟨.sb,hS,hB⟩
    obtain ⟨s,hs⟩ := separation_cover G
    by_cases hT : Triangle G
    · exact ⟨.st s,hS,hB,hT,hs⟩
    · exact ⟨.sn s,hS,hB,hT,hs⟩
  · obtain ⟨s,hs⟩ := high_separation_cover G
    by_cases hB : Bip G
    · exact ⟨.hb s,hH,hB,hs⟩
    by_cases hT : Triangle G
    · exact ⟨.ht s,hH,hB,hT,hs⟩
    · exact ⟨.hn s,hH,hB,hT,hs⟩

def Exclude (l : Leaf) : Prop :=
  ∀ (V : Type u) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    MinimalBad G → InLeaf G l → False

-- Exact AND gate. The converse ensures none of the leaf statements
-- is a stronger unrelated conjecture: the near theorem entails them all.
theorem closure_iff :
    (∀ l : Leaf, Exclude.{u} l) ↔
      (∀ (V : Type u) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
        Near G → HasPower G) := by
  constructor
  · intro h
    apply near_from_core_exclusion
    intro V G f d hm
    obtain ⟨l,hl⟩ := cover G hm
    exact h l V G hm hl
  · intro h l V G f d hm _
    exact hm.2.1 (h V G hm.1)

theorem original_of_all_leaves (h : ∀ l : Leaf, Exclude.{u} l) :
    ∀ (V : Type u) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
      G.minDegree ≥ 3 → ∃ (k : ℕ) (v : V) (c : G.Walk v v),
        k ≥ 2 ∧ c.IsCycle ∧ c.length = 2 ^ k := by
  apply erdos64_of_global_descent
  intro V G f d hn hp
  exact False.elim (hp ((closure_iff.mp h) V G hn))

#print axioms separation_cover
#print axioms high_separation_cover
#print axioms cover
#print axioms closure_iff
#print axioms original_of_all_leaves
end E64Leaves
