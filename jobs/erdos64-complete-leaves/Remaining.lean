import ClosedBipartite
import ClosedTriangle
import ClosedDefectCore
import ClosedBipartiteDefect

namespace E64Remaining
open SimpleGraph Erdos64Closure E64Core E64Leaves
universe u

/-- The exact original 26-leaf partition is retained. Thirteen whole
classes are excluded; false marks the thirteen genuinely unresolved leaves. -/
def isClosed : Leaf → Bool
  | .cb | .sb | .ct .core | .st .core | .sn .core | .hb _ => true
  | .ht .core4 | .ht .core5 | .hn .core4 | .hn .core5 => true
  | _ => false

theorem exclude_closed (l : Leaf) (hc : isClosed l = true) : Exclude.{u} l := by
  cases l with
  | cb => exact E64Closed.exclude_cb
  | sb => exact E64Closed.exclude_sb
  | ct s =>
    cases s with
    | low2 => simp [isClosed] at hc
    | low3 => simp [isClosed] at hc
    | core => exact E64Closed.exclude_ct_core
  | cn s => cases s <;> simp [isClosed] at hc
  | st s =>
    cases s with
    | low2 => simp [isClosed] at hc
    | low3 => simp [isClosed] at hc
    | core => exact E64DefectCore.exclude_st_core
  | sn s =>
    cases s with
    | low2 => simp [isClosed] at hc
    | low3 => simp [isClosed] at hc
    | core => exact E64DefectCore.exclude_sn_core
  | hb s => exact E64BipartiteDefect.exclude_hb s
  | ht s =>
    cases s with
    | low2 => simp [isClosed] at hc
    | low3 => simp [isClosed] at hc
    | core4 => exact E64DefectCore.exclude_ht_core4
    | core5 => exact E64DefectCore.exclude_ht_core5
  | hn s =>
    cases s with
    | low2 => simp [isClosed] at hc
    | low3 => simp [isClosed] at hc
    | core4 => exact E64DefectCore.exclude_hn_core4
    | core5 => exact E64DefectCore.exclude_hn_core5

/-- Explicit remaining proof obligation; this is not an unconditional
answer to Erdős #64. All previously closed leaves are supplied by proofs. -/
theorem original_of_remaining
    (h : ∀ l : Leaf, isClosed l = false → Exclude.{u} l) :
    ∀ (V : Type u) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
      G.minDegree ≥ 3 → ∃ (k : ℕ) (v : V) (c : G.Walk v v),
        k ≥ 2 ∧ c.IsCycle ∧ c.length = 2 ^ k := by
  apply original_of_all_leaves
  intro l
  cases hc : isClosed l with
  | false => exact h l hc
  | true => exact exclude_closed l hc

#print axioms exclude_closed
#print axioms original_of_remaining
end E64Remaining
