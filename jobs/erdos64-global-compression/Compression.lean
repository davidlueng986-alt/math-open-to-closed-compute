import Mathlib

namespace GlobalCompression

-- Each slot records the smaller cycle's contribution (including its
-- outgoing external edge) and whether the original block has unit slack
-- after doubling. An unchanged singleton has contribution 1.
abbrev Slot := ℕ × Bool

def reduced : List Slot → ℕ
  | [] => 0
  | (q, _) :: xs => q + reduced xs

def blocks : List Slot → ℕ
  | [] => 0
  | (_, true) :: xs => 1 + blocks xs
  | (_, false) :: xs => blocks xs

def singles : List Slot → ℕ
  | [] => 0
  | (_, true) :: xs => singles xs
  | (_, false) :: xs => 1 + singles xs

def Valid : List Slot → Prop
  | [] => True
  | (q, true) :: xs => Valid xs
  | (q, false) :: xs => q = 1 ∧ Valid xs

inductive LiftLength : List Slot → ℕ → Prop
  | nil : LiftLength [] 0
  | single {xs n} : LiftLength xs n → LiftLength ((1, false) :: xs) (n + 1)
  | block0 {xs n q} : LiftLength xs n → LiftLength ((q, true) :: xs) (n + 2*q)
  | block1 {xs n q} : LiftLength xs n → LiftLength ((q, true) :: xs) (n + 2*q + 1)

/-- All integer slack budgets up to the number of compressed blocks
are exactly realizable, with no bound on the list or contributions. -/
theorem lift_budget (xs : List Slot) (hv : Valid xs) (t : ℕ)
    (ht : t ≤ blocks xs) :
    ∃ n : ℕ, LiftLength xs n ∧ n + singles xs = 2 * reduced xs + t := by
  induction xs generalizing t with
  | nil =>
      have hz : t = 0 := by simpa [blocks] using ht
      subst t
      exact ⟨0, .nil, rfl⟩
  | cons p xs ih =>
      obtain ⟨q, b⟩ := p
      cases b with
      | false =>
          change q = 1 ∧ Valid xs at hv
          obtain ⟨rfl, hv⟩ := hv
          have ht' : t ≤ blocks xs := ht
          obtain ⟨n, hn, he⟩ := ih hv t ht'
          refine ⟨n + 1, .single hn, ?_⟩
          simp only [singles, reduced]
          omega
      | true =>
          have hv' : Valid xs := hv
          by_cases h : t ≤ blocks xs
          · obtain ⟨n, hn, he⟩ := ih hv' t h
            refine ⟨n + 2*q, .block0 hn, ?_⟩
            simp only [singles, reduced]
            omega
          · have ht' : t - 1 ≤ blocks xs := by
              change t ≤ 1 + blocks xs at ht
              omega
            obtain ⟨n, hn, he⟩ := ih hv' (t - 1) ht'
            refine ⟨n + 2*q + 1, .block1 hn, ?_⟩
            simp only [singles, reduced]
            omega

theorem exact_double (xs : List Slot) (hv : Valid xs)
    (h : singles xs ≤ blocks xs) :
    LiftLength xs (2 * reduced xs) := by
  obtain ⟨n, hn, he⟩ := lift_budget xs hv (singles xs) h
  have heq : n = 2 * reduced xs := by omega
  simpa only [heq] using hn

theorem power_lift (xs : List Slot) (hv : Valid xs)
    (h : singles xs ≤ blocks xs) (k : ℕ)
    (hp : reduced xs = 2^k) :
    LiftLength xs (2^(k+1)) := by
  have hl := exact_double xs hv h
  rw [hp] at hl
  rw [pow_succ, Nat.mul_comm]
  exact hl

-- Independent singleton sets on cycles give an injection from singleton
-- positions into block positions via the cyclic successor. The following
-- theorem verifies that combinatorial counting interface.
theorem count_from_injection {S B : Type*} [Fintype S] [Fintype B]
    (f : S → B) (hf : Function.Injective f) :
    Fintype.card S ≤ Fintype.card B :=
  Fintype.card_le_of_injective f hf

-- Exact interval domination for the three replacement types.
theorem triangle_slot (l : ℕ) (hl : l = 0) :
    1 ≤ 2*l+1 ∧ 2*l+2 ≤ 2 := by omega
theorem seven_slot (l : ℕ) (hl : 1 ≤ l ∧ l ≤ 2) :
    3 ≤ 2*l+1 ∧ 2*l+2 ≤ 6 := by omega
theorem fifteen_slot (l : ℕ) (hl : 2 ≤ l ∧ l ≤ 6) :
    5 ≤ 2*l+1 ∧ 2*l+2 ≤ 14 := by omega

#print axioms lift_budget
#print axioms exact_double
#print axioms power_lift
#print axioms count_from_injection
#print axioms triangle_slot
#print axioms seven_slot
#print axioms fifteen_slot
end GlobalCompression
