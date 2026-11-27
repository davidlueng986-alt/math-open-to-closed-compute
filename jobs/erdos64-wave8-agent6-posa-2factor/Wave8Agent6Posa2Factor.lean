import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace E64Wave8Agent6

/-- A cycle length is a power of 2 with exponent ≥ 2 (i.e. 4, 8, 16, 32, ...). -/
def IsPow2Len (L : ℕ) : Prop := ∃ k : ℕ, 2 ≤ k ∧ L = 2 ^ k

/-- A simple cycle of length `L ≥ 3` in a simple graph `G`. -/
structure SimpleCycle {V : Type*} (G : SimpleGraph V) (L : ℕ) where
  hL : 3 ≤ L
  vert : Fin L → V
  inj : Function.Injective vert
  adj : ∀ i : Fin L, G.Adj (vert i) (vert ⟨(i.val + 1) % L, Nat.mod_lt _ (by omega)⟩)

/-- A simple path of edge-length `len ≥ 1` from `x` to `y` in `G`. -/
structure SimplePath {V : Type*} (G : SimpleGraph V) (len : ℕ) (x y : V) where
  hlen : 1 ≤ len
  vert : Fin (len + 1) → V
  inj : Function.Injective vert
  start_eq : vert ⟨0, by omega⟩ = x
  end_eq : vert ⟨len, by omega⟩ = y
  adj : ∀ i : Fin len, G.Adj (vert ⟨i.val, by omega⟩) (vert ⟨i.val + 1, by omega⟩)

def HasPow2Cycle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ L : ℕ, IsPow2Len L ∧ Nonempty (SimpleCycle G L)

def PowerFree {V : Type*} (G : SimpleGraph V) : Prop := ¬ HasPow2Cycle G

/-- Minimum degree ≥ 3 on `Fin n` (first-order, requiring no decidability). -/
def MinDegAtLeast3 {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ u : Fin n, ∃ a b c : Fin n, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ G.Adj u a ∧ G.Adj u b ∧ G.Adj u c

/-- A vertex has degree ≤ 3 (subcubic). -/
def CubicVertex {V : Type*} (G : SimpleGraph V) (v : V) : Prop :=
  ∀ w₁ w₂ w₃ w₄ : V, G.Adj v w₁ → G.Adj v w₂ → G.Adj v w₃ → G.Adj v w₄ →
    w₁ = w₂ ∨ w₁ = w₃ ∨ w₁ = w₄ ∨ w₂ = w₃ ∨ w₂ = w₄ ∨ w₃ = w₄

/-- A vertex-minimal counterexample to the Erdős–Gyárfás conjecture on `Fin n`. -/
def MinimalCounterexample {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  MinDegAtLeast3 G ∧ PowerFree G ∧
    ∀ (t : ℕ), t < n → ∀ (H : SimpleGraph (Fin t)), MinDegAtLeast3 H → HasPow2Cycle H

private lemma ite_pos {α : Sort*} {p : Prop} [inst : Decidable p] {a b : α} (h : p) :
    (if p then a else b) = a := by
  cases inst with
  | isTrue _ => rfl
  | isFalse hn => exact absurd h hn

private lemma ite_neg {α : Sort*} {p : Prop} [inst : Decidable p] {a b : α} (h : ¬ p) :
    (if p then a else b) = b := by
  cases inst with
  | isTrue hp => exact absurd hp h
  | isFalse _ => rfl

lemma isPow2Len_four : IsPow2Len 4 := ⟨2, le_rfl, by norm_num⟩
lemma isPow2Len_eight : IsPow2Len 8 := ⟨3, by omega, by norm_num⟩

private lemma mod_pred_succ {N i : ℕ} (hN : 3 ≤ N) (hi : i < N) :
    ((i + N - 1) % N + 1) % N = i := by
  by_cases h0 : i = 0
  · subst h0
    have h0' : 0 + N - 1 = N - 1 := by omega
    have h1 : (0 + N - 1) % N = N - 1 := by rw [h0']; exact Nat.mod_eq_of_lt (by omega)
    rw [h1]
    have h2 : N - 1 + 1 = N := by omega
    rw [h2, Nat.mod_self]
  · have h1 : i + N - 1 = (i - 1) + N := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : i - 1 < N)]
    have h2 : i - 1 + 1 = i := by omega
    rw [h2, Nat.mod_eq_of_lt hi]

private lemma mod_succ_pred {N i : ℕ} (hN : 3 ≤ N) (hi : i < N) :
    ((i + 1) % N + N - 1) % N = i := by
  by_cases hlt : i + 1 < N
  · rw [Nat.mod_eq_of_lt hlt]
    have h1 : i + 1 + N - 1 = i + N := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
  · have heq : i + 1 = N := by omega
    rw [heq, Nat.mod_self]
    have h1 : 0 + N - 1 = i := by omega
    rw [h1, Nat.mod_eq_of_lt hi]

private lemma mod_pred_ne {N i : ℕ} (hN : 3 ≤ N) (hi : i < N) :
    (i + N - 1) % N ≠ i := by
  by_cases h0 : i = 0
  · subst h0; rw [Nat.mod_eq_of_lt (by omega)]; omega
  · have h1 : i + N - 1 = (i - 1) + N := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : i - 1 < N)]; omega

private lemma mod_succ_ne {N i : ℕ} (hN : 3 ≤ N) (hi : i < N) :
    (i + 1) % N ≠ i := by
  by_cases hlt : i + 1 < N
  · rw [Nat.mod_eq_of_lt hlt]; omega
  · have heq : i + 1 = N := by omega
    rw [heq, Nat.mod_self]; omega

private lemma mod_pred_ne_succ {N i : ℕ} (hN : 3 ≤ N) (hi : i < N) :
    (i + N - 1) % N ≠ (i + 1) % N := by
  by_cases h0 : i = 0
  · subst h0
    rw [Nat.mod_eq_of_lt (by omega : 0 + N - 1 < N), Nat.mod_eq_of_lt (by omega : 0 + 1 < N)]
    omega
  · have h1 : i + N - 1 = (i - 1) + N := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : i - 1 < N)]
    by_cases hlt : i + 1 < N
    · rw [Nat.mod_eq_of_lt hlt]; omega
    · have heq : i + 1 = N := by omega
      rw [heq, Nat.mod_self]; omega

/-! ### Helper: Converting a `Nodup` cyclic vertex list into a `SimpleCycle` -/

lemma simpleCycle_of_list {V : Type*} {G : SimpleGraph V} (vs : List V)
    (hlen : 3 ≤ vs.length)
    (hnd : vs.Nodup)
    (hchain : ∀ k (hk : k + 1 < vs.length), G.Adj vs[k] vs[k + 1])
    (hwrap : G.Adj (vs[vs.length - 1]'(by omega)) (vs[0]'(by omega))) :
    Nonempty (SimpleCycle G vs.length) := by
  let f : Fin vs.length → V := fun i => vs[i.val]
  have hinj : Function.Injective f := fun i j hij =>
    (List.nodup_iff_injective_getElem.mp hnd) hij
  have hadj : ∀ i : Fin vs.length,
      G.Adj (f i) (f ⟨(i.val + 1) % vs.length, Nat.mod_lt _ (by omega)⟩) := by
    intro i
    by_cases hlt : i.val + 1 < vs.length
    · have hm : (i.val + 1) % vs.length = i.val + 1 := Nat.mod_eq_of_lt hlt
      dsimp only [f]
      have h := hchain i.val hlt
      have heq : vs[(i.val + 1) % vs.length]'(Nat.mod_lt _ (by omega)) = vs[i.val + 1] := by
        congr 1
      rw [heq]; exact h
    · have hlast : i.val = vs.length - 1 := by omega
      have hm : (i.val + 1) % vs.length = 0 := by
        have : i.val + 1 = vs.length := by omega
        rw [this, Nat.mod_self]
      dsimp only [f]
      have h1 : vs[i.val] = vs[vs.length - 1]'(by omega) := by congr 1
      have h2 : vs[(i.val + 1) % vs.length]'(Nat.mod_lt _ (by omega)) = vs[0]'(by omega) := by congr 1
      rw [h1, h2]; exact hwrap
  exact ⟨⟨hlen, f, hinj, hadj⟩⟩

/-! ### Helper: Gluing two internally disjoint paths into a simple cycle -/

lemma two_paths_form_simple_cycle {V : Type*} {G : SimpleGraph V}
    {a b : ℕ} {x y : V}
    (hab : 3 ≤ a + b)
    (P : SimplePath G a x y)
    (Q : SimplePath G b x y)
    (hint : ∀ (i : Fin (a + 1)) (j : Fin (b + 1)),
      0 < i.val → i.val < a → 0 < j.val → j.val < b → P.vert i ≠ Q.vert j)
    (_hxy : x ≠ y) :
    Nonempty (SimpleCycle G (a + b)) := by
  let f : Fin (a + b) → V := fun k =>
    if hk : k.val < a then P.vert ⟨k.val, by omega⟩
    else Q.vert ⟨a + b - k.val, by omega⟩
  have hQ_not_x : ∀ j : Fin (b + 1), 0 < j.val → Q.vert j ≠ x := by
    intro j hj h
    have heq := Q.inj (h.trans Q.start_eq.symm)
    have : j.val = 0 := congrArg Fin.val heq
    omega
  have hQ_not_y : ∀ j : Fin (b + 1), j.val < b → Q.vert j ≠ y := by
    intro j hj h
    have heq := Q.inj (h.trans Q.end_eq.symm)
    have : j.val = b := congrArg Fin.val heq
    omega
  have hP_not_y : ∀ i : Fin (a + 1), i.val < a → P.vert i ≠ y := by
    intro i hi h
    have heq := P.inj (h.trans P.end_eq.symm)
    have : i.val = a := congrArg Fin.val heq
    omega
  have hinj : Function.Injective f := by
    intro i j hij
    dsimp [f] at hij
    split_ifs at hij with hi hj hj
    · have hv := congrArg Fin.val (P.inj hij); dsimp only at hv; exact Fin.ext hv
    · exfalso
      by_cases hi0 : i.val = 0
      · have hpi : P.vert ⟨i.val, by omega⟩ = x := by
          convert P.start_eq using 2; exact Fin.ext hi0
        rw [hpi] at hij
        exact hQ_not_x ⟨a + b - j.val, by omega⟩ (by dsimp only; omega) hij.symm
      · by_cases hja : j.val = a
        · have hqj : Q.vert ⟨a + b - j.val, by omega⟩ = y := by
            convert Q.end_eq using 2; exact Fin.ext (by first | (dsimp only; omega) | omega)
          rw [hqj] at hij
          exact hP_not_y ⟨i.val, by omega⟩ hi hij
        · exact hint ⟨i.val, by omega⟩ ⟨a + b - j.val, by omega⟩
            (by dsimp only; omega) (by dsimp only; exact hi) (by dsimp only; omega) (by dsimp only; omega) hij
    · exfalso
      by_cases hj0 : j.val = 0
      · have hpj : P.vert ⟨j.val, by omega⟩ = x := by
          convert P.start_eq using 2; exact Fin.ext hj0
        rw [hpj] at hij
        exact hQ_not_x ⟨a + b - i.val, by omega⟩ (by dsimp only; omega) hij
      · by_cases hia : i.val = a
        · have hqi : Q.vert ⟨a + b - i.val, by omega⟩ = y := by
            convert Q.end_eq using 2; exact Fin.ext (by first | (dsimp only; omega) | omega)
          rw [hqi] at hij
          exact hP_not_y ⟨j.val, by omega⟩ hj hij.symm
        · exact hint ⟨j.val, by omega⟩ ⟨a + b - i.val, by omega⟩
            (by dsimp only; omega) (by dsimp only; exact hj) (by dsimp only; omega) (by dsimp only; omega) hij.symm
    · have hv : a + b - i.val = a + b - j.val := congrArg Fin.val (Q.inj hij)
      exact Fin.ext (by first | (dsimp only; omega) | omega)
  have hadj : ∀ k : Fin (a + b),
      G.Adj (f k) (f ⟨(k.val + 1) % (a + b), Nat.mod_lt _ (by omega)⟩) := by
    intro k
    by_cases hk1 : k.val + 1 < a
    · have hlt : k.val < a := by omega
      have hm : (k.val + 1) % (a + b) = k.val + 1 := Nat.mod_eq_of_lt (by omega)
      have hc2 : (k.val + 1) % (a + b) < a := by rw [hm]; omega
      dsimp only [f]
      simp only [hlt, hc2, ↓reduceDIte]
      have h := P.adj ⟨k.val, hlt⟩
      convert h using 2
      exact Fin.ext hm
    · by_cases hk2 : k.val < a
      · have hka : k.val + 1 = a := by omega
        have hm : (k.val + 1) % (a + b) = a := by rw [hka]; exact Nat.mod_eq_of_lt (by have := Q.hlen; omega)
        have hc2 : ¬ (k.val + 1) % (a + b) < a := by rw [hm]; omega
        dsimp only [f]
        simp only [hk2, hc2, ↓reduceDIte]
        have hpa := P.adj ⟨k.val, hk2⟩
        have hpend : P.vert ⟨k.val + 1, by omega⟩ = y := by
          convert P.end_eq using 2; exact Fin.ext hka
        have hqend : Q.vert ⟨a + b - (k.val + 1) % (a + b), by omega⟩ = y := by
          convert Q.end_eq using 2; exact Fin.ext (by first | (dsimp only; omega) | omega)
        rw [hpend] at hpa
        rw [hqend]
        exact hpa
      · by_cases hk3 : k.val + 1 < a + b
        · have hm : (k.val + 1) % (a + b) = k.val + 1 := Nat.mod_eq_of_lt hk3
          have hc2 : ¬ (k.val + 1) % (a + b) < a := by rw [hm]; omega
          dsimp only [f]
          simp only [hk2, hc2, ↓reduceDIte]
          have hq := (Q.adj ⟨a + b - k.val - 1, by omega⟩).symm
          have h1 : Q.vert ⟨a + b - k.val, by omega⟩ = Q.vert ⟨a + b - k.val - 1 + 1, by omega⟩ := by
            congr 1; exact Fin.ext (by first | (dsimp only; omega) | omega)
          have h2 : Q.vert ⟨a + b - (k.val + 1) % (a + b), by omega⟩ = Q.vert ⟨a + b - k.val - 1, by omega⟩ := by
            congr 1; exact Fin.ext (by first | (dsimp only; omega) | omega)
          rw [h1, h2]
          exact hq
        · have hklast : k.val + 1 = a + b := by omega
          have hm : (k.val + 1) % (a + b) = 0 := by rw [hklast, Nat.mod_self]
          have ha_pos : 0 < a := P.hlen
          have hc2 : (k.val + 1) % (a + b) < a := by rw [hm]; omega
          dsimp only [f]
          simp only [hk2, hc2, ↓reduceDIte]
          have hq0 := (Q.adj ⟨0, Q.hlen⟩).symm
          rw [Q.start_eq] at hq0
          have hpstart : P.vert ⟨(k.val + 1) % (a + b), by omega⟩ = x := by
            convert P.start_eq using 2; exact Fin.ext hm
          have hq1 : Q.vert ⟨a + b - k.val, by omega⟩ = Q.vert ⟨1, by omega⟩ := by
            congr 1; exact Fin.ext (by first | (dsimp only; omega) | omega)
          rw [hpstart, hq1]
          exact hq0
  exact ⟨⟨hab, f, hinj, hadj⟩⟩

/-! ============================================================================
    PILLAR I: UNCONDITIONAL ALL-ORDER C5-QUOTIENT & 2-FACTOR REDUCTION
    ============================================================================ -/

/-- Theorem 1: Any chord of a 5-cycle in a simple graph forces a simple 4-cycle. -/
theorem c5_chord_forces_c4 {V : Type*} {G : SimpleGraph V}
    (v : Fin 5 → V) (hv : Function.Injective v)
    (hc5 : ∀ i : Fin 5, G.Adj (v i) (v (i + 1)))
    (a b : Fin 5) (hchord : b = a + 2 ∨ b = a + 3)
    (hadj : G.Adj (v a) (v b)) :
    Nonempty (SimpleCycle G 4) := by
  have mk4 : ∀ x : Fin 5, G.Adj (v x) (v (x + 2)) → Nonempty (SimpleCycle G 4) := by
    intro x hx
    let f : Fin 4 → V := fun j =>
      match j.val with
      | 0 => v x
      | 1 => v (x + 2)
      | 2 => v (x + 3)
      | _ => v (x + 4)
    refine ⟨⟨by omega, f, ?_, ?_⟩⟩
    · intro p q hpq
      fin_cases p <;> fin_cases q <;> dsimp [f] at hpq
      all_goals try rfl
      all_goals (have h := hv hpq; revert h; fin_cases x <;> decide)
    · intro p
      fin_cases p <;> dsimp [f]
      · exact hx
      · have h := hc5 (x + 2)
        have heq : (x + 2 : Fin 5) + 1 = x + 3 := by fin_cases x <;> decide
        rw [heq] at h; exact h
      · have h := hc5 (x + 3)
        have heq : (x + 3 : Fin 5) + 1 = x + 4 := by fin_cases x <;> decide
        rw [heq] at h; exact h
      · have h := hc5 (x + 4)
        have heq : (x + 4 : Fin 5) + 1 = x := by fin_cases x <;> decide
        rw [heq] at h; exact h
  rcases hchord with rfl | rfl
  · exact mk4 a hadj
  · have heq : (a + 3 : Fin 5) + 2 = a := by fin_cases a <;> decide
    have hx : G.Adj (v (a + 3)) (v ((a + 3) + 2)) := by rw [heq]; exact hadj.symm
    exact mk4 (a + 3) hx

/-- Theorem 2: Any vertex outside a 5-cycle with two distinct neighbors on the 5-cycle
    forces a triangle `C_3` or a 4-cycle `C_4`. -/
theorem c5_two_edges_sharing_vertex_forces_c3_or_c4 {V : Type*} {G : SimpleGraph V}
    (v : Fin 5 → V) (hv : Function.Injective v)
    (hc5 : ∀ i : Fin 5, G.Adj (v i) (v (i + 1)))
    (u : V) (hu : ∀ i : Fin 5, u ≠ v i)
    (a b : Fin 5) (hab : a ≠ b)
    (ha : G.Adj u (v a)) (hb : G.Adj u (v b)) :
    Nonempty (SimpleCycle G 3) ∨ Nonempty (SimpleCycle G 4) := by
  have mk3 : ∀ x : Fin 5, G.Adj u (v x) → G.Adj u (v (x + 1)) → Nonempty (SimpleCycle G 3) := by
    intro x h1 h2
    let f : Fin 3 → V := fun j =>
      match j.val with | 0 => u | 1 => v x | _ => v (x + 1)
    refine ⟨⟨le_rfl, f, ?_, ?_⟩⟩
    · intro p q hpq
      fin_cases p <;> fin_cases q <;> dsimp [f] at hpq
      all_goals try rfl
      all_goals try exact False.elim (hu _ hpq)
      all_goals try exact False.elim (hu _ hpq.symm)
      all_goals (have h := hv hpq; revert h; fin_cases x <;> decide)
    · intro p
      fin_cases p <;> dsimp [f]
      · exact h1
      · exact hc5 x
      · exact h2.symm
  have mk4 : ∀ x : Fin 5, G.Adj u (v x) → G.Adj u (v (x + 2)) → Nonempty (SimpleCycle G 4) := by
    intro x h1 h2
    let f : Fin 4 → V := fun j =>
      match j.val with | 0 => u | 1 => v x | 2 => v (x + 1) | _ => v (x + 2)
    refine ⟨⟨by omega, f, ?_, ?_⟩⟩
    · intro p q hpq
      fin_cases p <;> fin_cases q <;> dsimp [f] at hpq
      all_goals try rfl
      all_goals try exact False.elim (hu _ hpq)
      all_goals try exact False.elim (hu _ hpq.symm)
      all_goals (have h := hv hpq; revert h; fin_cases x <;> decide)
    · intro p
      fin_cases p <;> dsimp [f]
      · exact h1
      · exact hc5 x
      · have h := hc5 (x + 1)
        have heq : (x + 1 : Fin 5) + 1 = x + 2 := by fin_cases x <;> decide
        rw [heq] at h; exact h
      · exact h2.symm
  have hdiff : b = a + 1 ∨ b = a + 2 ∨ b = a + 3 ∨ b = a + 4 := by
    revert hab; fin_cases a <;> fin_cases b <;> decide
  rcases hdiff with rfl | rfl | rfl | rfl
  · exact Or.inl (mk3 a ha hb)
  · exact Or.inr (mk4 a ha hb)
  · have heq : (a + 3 : Fin 5) + 2 = a := by fin_cases a <;> decide
    exact Or.inr (mk4 (a + 3) hb (by rw [heq]; exact ha))
  · have heq : (a + 4 : Fin 5) + 1 = a := by fin_cases a <;> decide
    exact Or.inl (mk3 (a + 4) hb (by rw [heq]; exact ha))

/-- Theorem 3: Split dichotomy on a 5-cycle — any two distinct indices on `Fin 5`
    have clockwise/counterclockwise arc lengths `{1, 4}` or `{2, 3}`. -/
theorem c5_split_dichotomy (a b : Fin 5) (hab : a ≠ b) :
    let d := (b.val + 5 - a.val) % 5
    (d = 1 ∧ 5 - d = 4) ∨ (d = 4 ∧ 5 - d = 1) ∨
    (d = 2 ∧ 5 - d = 3) ∨ (d = 3 ∧ 5 - d = 2) := by
  dsimp
  have : a.val ≠ b.val := fun h => hab (Fin.ext h)
  omega

/-- Extract a clockwise arc of length `d` (`1 ≤ d < L`) on a cycle `C : SimpleCycle G L`. -/
def cycleArcFwd {V : Type*} {G : SimpleGraph V} {L : ℕ} (C : SimpleCycle G L)
    (a : Fin L) (d : ℕ) (hd1 : 1 ≤ d) (hd2 : d < L) :
    SimplePath G d (C.vert a) (C.vert ⟨(a.val + d) % L, Nat.mod_lt _ (by omega)⟩) where
  hlen := hd1
  vert := fun i => C.vert ⟨(a.val + i.val) % L, Nat.mod_lt _ (by omega)⟩
  inj := by
    intro i j hij
    have h : (a.val + i.val) % L = (a.val + j.val) % L := congrArg Fin.val (C.inj hij)
    have hi : i.val < L := by omega
    have hj : j.val < L := by omega
    have ha : a.val < L := a.isLt
    have hmod : ∀ x : ℕ, x < L → (a.val + x) % L = if a.val + x < L then a.val + x else a.val + x - L := by
      intro x hx
      split_ifs with hlt
      · exact Nat.mod_eq_of_lt hlt
      · have h1 : a.val + x - L < L := by omega
        have h2 : a.val + x = (a.val + x - L) + L := by omega
        conv_lhs => rw [h2]
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt h1]
    rw [hmod i.val hi, hmod j.val hj] at h
    split_ifs at h <;> exact Fin.ext (by first | (dsimp only; omega) | omega)
  start_eq := by
    congr 1; apply Fin.ext; dsimp only; simp [Nat.mod_eq_of_lt a.isLt]
  end_eq := rfl
  adj := by
    intro i
    have h := C.adj ⟨(a.val + i.val) % L, Nat.mod_lt _ (by omega)⟩
    convert h using 2
    apply Fin.ext
    dsimp only
    rw [Nat.mod_add_mod, Nat.add_assoc]

/-- Reverse a simple path from `x` to `y` into one from `y` to `x`. -/
def SimplePath.rev {V : Type*} {G : SimpleGraph V} {len : ℕ} {x y : V}
    (P : SimplePath G len x y) : SimplePath G len y x where
  hlen := P.hlen
  vert := fun i => P.vert ⟨len - i.val, by omega⟩
  inj := by
    intro i j hij
    have hv : len - i.val = len - j.val := congrArg Fin.val (P.inj hij)
    exact Fin.ext (by first | (dsimp only; omega) | omega)
  start_eq := by simpa using P.end_eq
  end_eq := by simpa using P.start_eq
  adj := by
    intro i
    have h := (P.adj ⟨len - i.val - 1, by omega⟩).symm
    have h1 : P.vert ⟨len - i.val, by omega⟩ = P.vert ⟨len - i.val - 1 + 1, by omega⟩ := by
      congr 1; exact Fin.ext (by dsimp only; omega)
    have h2 : P.vert ⟨len - (i.val + 1), by omega⟩ = P.vert ⟨len - i.val - 1, by omega⟩ := rfl
    rw [h1, h2]
    exact h

/-- Rewrite the start endpoint of a simple path without changing its vertex map. -/
def SimplePath.castStart {V : Type*} {G : SimpleGraph V} {len : ℕ} {x x' y : V}
    (P : SimplePath G len x y) (hx : x = x') : SimplePath G len x' y where
  hlen := P.hlen
  vert := P.vert
  inj := P.inj
  start_eq := P.start_eq.trans hx
  end_eq := P.end_eq
  adj := P.adj

/-- Concatenate two vertex-disjoint (except at join `y`) simple paths `x → y` and `y → z`. -/
def SimplePath.concat {V : Type*} {G : SimpleGraph V} {a b : ℕ} {x y z : V}
    (P : SimplePath G a x y) (Q : SimplePath G b y z)
    (hdisj : ∀ (i : Fin (a + 1)) (j : Fin (b + 1)), i.val < a → 0 < j.val → P.vert i ≠ Q.vert j)
    (_hxz : x ≠ z) :
    SimplePath G (a + b) x z where
  hlen := by have := P.hlen; omega
  vert := fun k =>
    if hk : k.val ≤ a then P.vert ⟨k.val, by omega⟩
    else Q.vert ⟨k.val - a, by omega⟩
  inj := by
    intro i j hij
    dsimp only at hij
    split_ifs at hij with hi hj hj
    · have hv := congrArg Fin.val (P.inj hij); dsimp only at hv; exact Fin.ext hv
    · exfalso
      by_cases hia : i.val = a
      · have hpi : P.vert ⟨i.val, by omega⟩ = y := by
          convert P.end_eq using 2; exact Fin.ext hia
        rw [hpi] at hij
        have heq := Q.inj (hij.symm.trans Q.start_eq.symm)
        have : j.val - a = 0 := congrArg Fin.val heq
        omega
      · exact hdisj ⟨i.val, by omega⟩ ⟨j.val - a, by omega⟩ (by dsimp only; omega) (by dsimp only; omega) hij
    · exfalso
      by_cases hja : j.val = a
      · have hpj : P.vert ⟨j.val, by omega⟩ = y := by
          convert P.end_eq using 2; exact Fin.ext hja
        rw [hpj] at hij
        have heq := Q.inj (hij.trans Q.start_eq.symm)
        have : i.val - a = 0 := congrArg Fin.val heq
        omega
      · exact hdisj ⟨j.val, by omega⟩ ⟨i.val - a, by omega⟩ (by dsimp only; omega) (by dsimp only; omega) hij.symm
    · have hv : i.val - a = j.val - a := congrArg Fin.val (Q.inj hij)
      exact Fin.ext (by first | (dsimp only; omega) | omega)
  start_eq := by
    dsimp only
    have h0 : (0 : ℕ) ≤ a := Nat.zero_le a
    simp only [h0, ↓reduceDIte]
    exact P.start_eq
  end_eq := by
    dsimp only
    have hb : 1 ≤ b := Q.hlen
    have hne : ¬ (a + b ≤ a) := by omega
    simp only [hne, ↓reduceDIte]
    convert Q.end_eq using 2; exact Fin.ext (by first | (dsimp only; omega) | omega)
  adj := by
    intro k
    dsimp only
    by_cases hk1 : k.val + 1 ≤ a
    · have hk0 : k.val ≤ a := by omega
      simp only [hk0, hk1, ↓reduceDIte]
      exact P.adj ⟨k.val, by omega⟩
    · by_cases hk2 : k.val ≤ a
      · have hka : k.val = a := by omega
        simp only [hk2, hk1, ↓reduceDIte]
        have hpa : P.vert ⟨k.val, by omega⟩ = y := by
          convert P.end_eq using 2; exact Fin.ext hka
        have hq0 := Q.adj ⟨0, Q.hlen⟩
        rw [Q.start_eq] at hq0
        have hq1 : Q.vert ⟨k.val + 1 - a, by omega⟩ = Q.vert ⟨1, by omega⟩ := by
          congr 1; exact Fin.ext (by first | (dsimp only; omega) | omega)
        rw [hpa, hq1]
        exact hq0
      · have hk3 : ¬ (k.val + 1 ≤ a) := by omega
        simp only [hk2, hk3, ↓reduceDIte]
        have hq := Q.adj ⟨k.val - a, by omega⟩
        have hq1 : Q.vert ⟨k.val + 1 - a, by omega⟩ = Q.vert ⟨k.val - a + 1, by omega⟩ := by
          congr 1; exact Fin.ext (by first | (dsimp only; omega) | omega)
        rw [hq1]
        exact hq

/-- Build a simple cycle from two vertex-disjoint cycles `C₁, C₂` joined by two independent
    paths `P₁` (from `C₁(a₁)` to `C₂(a₂)`) and `P₂` (from `C₁(b₁)` to `C₂(b₂)`), choosing
    either clockwise or counterclockwise arc on each cycle. -/
lemma two_cycle_bridge_single {V : Type*} {G : SimpleGraph V}
    {L₁ L₂ p₁ p₂ : ℕ}
    (C₁ : SimpleCycle G L₁) (C₂ : SimpleCycle G L₂)
    (hdisjC : ∀ i j, C₁.vert i ≠ C₂.vert j)
    (a₁ b₁ : Fin L₁) (a₂ b₂ : Fin L₂)
    (d₁ d₂ : ℕ)
    (A₁ : SimplePath G d₁ (C₁.vert a₁) (C₁.vert b₁))
    (A₂ : SimplePath G d₂ (C₂.vert a₂) (C₂.vert b₂))
    (hA₁_in : ∀ i, ∃ x, A₁.vert i = C₁.vert x)
    (hA₂_in : ∀ i, ∃ x, A₂.vert i = C₂.vert x)
    (P₁ : SimplePath G p₁ (C₁.vert a₁) (C₂.vert a₂))
    (P₂ : SimplePath G p₂ (C₁.vert b₁) (C₂.vert b₂))
    (hP₁_int : ∀ i : Fin (p₁ + 1), 0 < i.val → i.val < p₁ →
      (∀ x, P₁.vert i ≠ C₁.vert x) ∧ (∀ y, P₁.vert i ≠ C₂.vert y))
    (hP₂_int : ∀ i : Fin (p₂ + 1), 0 < i.val → i.val < p₂ →
      (∀ x, P₂.vert i ≠ C₁.vert x) ∧ (∀ y, P₂.vert i ≠ C₂.vert y))
    (hP₁₂ : ∀ (i : Fin (p₁ + 1)) (j : Fin (p₂ + 1)), P₁.vert i ≠ P₂.vert j) :
    Nonempty (SimpleCycle G (d₁ + d₂ + p₁ + p₂)) := by
  -- Path Q₁: C₁(a₁) --A₁--> C₁(b₁) --P₂--> C₂(b₂) (length d₁ + p₂)
  have hQ₁_disj : ∀ (i : Fin (d₁ + 1)) (j : Fin (p₂ + 1)),
      i.val < d₁ → 0 < j.val → A₁.vert i ≠ P₂.vert j := by
    intro i j hi hj h
    by_cases hjp : j.val < p₂
    · rcases hA₁_in i with ⟨x, hx⟩
      rw [hx] at h
      exact (hP₂_int j hj hjp).1 x h.symm
    · have hjeq : j.val = p₂ := by omega
      have hp2 : P₂.vert j = C₂.vert b₂ := by convert P₂.end_eq using 2; exact Fin.ext hjeq
      rcases hA₁_in i with ⟨x, hx⟩
      rw [hx, hp2] at h
      exact hdisjC x b₂ h
  let Q₁ : SimplePath G (d₁ + p₂) (C₁.vert a₁) (C₂.vert b₂) :=
    A₁.concat P₂ hQ₁_disj (hdisjC a₁ b₂)
  -- Path Q₂: C₁(a₁) --P₁--> C₂(a₂) --A₂--> C₂(b₂) (length p₁ + d₂)
  have hQ₂_disj : ∀ (i : Fin (p₁ + 1)) (j : Fin (d₂ + 1)),
      i.val < p₁ → 0 < j.val → P₁.vert i ≠ A₂.vert j := by
    intro i j hi hj h
    by_cases hi0 : 0 < i.val
    · rcases hA₂_in j with ⟨y, hy⟩
      rw [hy] at h
      exact (hP₁_int i hi0 hi).2 y h
    · have hieq : i.val = 0 := by omega
      have hp1 : P₁.vert i = C₁.vert a₁ := by convert P₁.start_eq using 2; exact Fin.ext hieq
      rcases hA₂_in j with ⟨y, hy⟩
      rw [hp1, hy] at h
      exact hdisjC a₁ y h
  let Q₂ : SimplePath G (p₁ + d₂) (C₁.vert a₁) (C₂.vert b₂) :=
    P₁.concat A₂ hQ₂_disj (hdisjC a₁ b₂)
  have hint : ∀ (i : Fin (d₁ + p₂ + 1)) (j : Fin (p₁ + d₂ + 1)),
      0 < i.val → i.val < d₁ + p₂ → 0 < j.val → j.val < p₁ + d₂ → Q₁.vert i ≠ Q₂.vert j := by
    intro i j hi0 hi1 hj0 hj1 h
    dsimp [Q₁, Q₂, SimplePath.concat] at h
    split_ifs at h with hi_le hj_le hj_le
    · -- A₁[i] = P₁[j] with 0 < i ≤ d₁ and 0 < j ≤ p₁
      by_cases hjp : j.val < p₁
      · rcases hA₁_in ⟨i.val, by omega⟩ with ⟨x, hx⟩
        rw [hx] at h
        exact (hP₁_int ⟨j.val, by omega⟩ hj0 hjp).1 x h.symm
      · have hjeq : j.val = p₁ := by omega
        have hp1 : P₁.vert ⟨j.val, by omega⟩ = C₂.vert a₂ := by
          convert P₁.end_eq using 2; exact Fin.ext hjeq
        rcases hA₁_in ⟨i.val, by omega⟩ with ⟨x, hx⟩
        rw [hx, hp1] at h
        exact hdisjC x a₂ h
    · -- A₁[i] = A₂[j - p₁]
      rcases hA₁_in ⟨i.val, by omega⟩ with ⟨x, hx⟩
      rcases hA₂_in ⟨j.val - p₁, by omega⟩ with ⟨y, hy⟩
      rw [hx, hy] at h
      exact hdisjC x y h
    · -- P₂[i - d₁] = P₁[j]
      exact hP₁₂ ⟨j.val, by omega⟩ ⟨i.val - d₁, by omega⟩ h.symm
    · -- P₂[i - d₁] = A₂[j - p₁] with 0 < i - d₁ < p₂
      rcases hA₂_in ⟨j.val - p₁, by omega⟩ with ⟨y, hy⟩
      rw [hy] at h
      exact (hP₂_int ⟨i.val - d₁, by omega⟩ (by dsimp only; omega) (by dsimp only; omega)).2 y h
  have hcyc := two_paths_form_simple_cycle (by have := A₁.hlen; have := A₂.hlen; have := P₁.hlen; have := P₂.hlen; omega)
    Q₁ Q₂ hint (hdisjC a₁ b₂)
  have hlen_eq : (d₁ + p₂) + (p₁ + d₂) = d₁ + d₂ + p₁ + p₂ := by omega
  rw [hlen_eq] at hcyc
  exact hcyc

/-- Theorem 4: Two vertex-disjoint cycles `C₁` (length `L₁`) and `C₂` (length `L₂`) joined
    by two independent paths of lengths `p₁, p₂` unconditionally produce all four merge cycles
    `a₁ + a₂ + p₁ + p₂`, `a₁ + (L₂ - a₂) + p₁ + p₂`, `(L₁ - a₁) + a₂ + p₁ + p₂`, and
    `(L₁ - a₁) + (L₂ - a₂) + p₁ + p₂`. -/
theorem two_cycle_double_bridge_four_cycles {V : Type*} {G : SimpleGraph V}
    {L₁ L₂ p₁ p₂ : ℕ}
    (C₁ : SimpleCycle G L₁) (C₂ : SimpleCycle G L₂)
    (hdisjC : ∀ i j, C₁.vert i ≠ C₂.vert j)
    (a₁ : Fin L₁) (d₁ : ℕ) (hd₁_pos : 1 ≤ d₁) (hd₁_lt : d₁ < L₁)
    (a₂ : Fin L₂) (d₂ : ℕ) (hd₂_pos : 1 ≤ d₂) (hd₂_lt : d₂ < L₂)
    (P₁ : SimplePath G p₁ (C₁.vert a₁) (C₂.vert a₂))
    (P₂ : SimplePath G p₂ (C₁.vert ⟨(a₁.val + d₁) % L₁, Nat.mod_lt _ (by omega)⟩)
                          (C₂.vert ⟨(a₂.val + d₂) % L₂, Nat.mod_lt _ (by omega)⟩))
    (hP₁_int : ∀ i : Fin (p₁ + 1), 0 < i.val → i.val < p₁ →
      (∀ x, P₁.vert i ≠ C₁.vert x) ∧ (∀ y, P₁.vert i ≠ C₂.vert y))
    (hP₂_int : ∀ i : Fin (p₂ + 1), 0 < i.val → i.val < p₂ →
      (∀ x, P₂.vert i ≠ C₁.vert x) ∧ (∀ y, P₂.vert i ≠ C₂.vert y))
    (hP₁₂ : ∀ (i : Fin (p₁ + 1)) (j : Fin (p₂ + 1)), P₁.vert i ≠ P₂.vert j) :
    Nonempty (SimpleCycle G (d₁ + d₂ + p₁ + p₂)) ∧
    Nonempty (SimpleCycle G (d₁ + (L₂ - d₂) + p₁ + p₂)) ∧
    Nonempty (SimpleCycle G ((L₁ - d₁) + d₂ + p₁ + p₂)) ∧
    Nonempty (SimpleCycle G ((L₁ - d₁) + (L₂ - d₂) + p₁ + p₂)) := by
  let b₁ : Fin L₁ := ⟨(a₁.val + d₁) % L₁, Nat.mod_lt _ (by omega)⟩
  let b₂ : Fin L₂ := ⟨(a₂.val + d₂) % L₂, Nat.mod_lt _ (by omega)⟩
  let A₁f := cycleArcFwd C₁ a₁ d₁ hd₁_pos hd₁_lt
  let A₂f := cycleArcFwd C₂ a₂ d₂ hd₂_pos hd₂_lt
  have hb₁_wrap : ⟨(b₁.val + (L₁ - d₁)) % L₁, Nat.mod_lt _ (by omega)⟩ = a₁ := by
    apply Fin.ext
    dsimp [b₁]
    rw [Nat.mod_add_mod]
    have : a₁.val + d₁ + (L₁ - d₁) = a₁.val + L₁ := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt a₁.isLt]
  have hb₂_wrap : ⟨(b₂.val + (L₂ - d₂)) % L₂, Nat.mod_lt _ (by omega)⟩ = a₂ := by
    apply Fin.ext
    dsimp [b₂]
    rw [Nat.mod_add_mod]
    have : a₂.val + d₂ + (L₂ - d₂) = a₂.val + L₂ := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt a₂.isLt]
  let A₁b : SimplePath G (L₁ - d₁) (C₁.vert a₁) (C₁.vert b₁) :=
    (cycleArcFwd C₁ b₁ (L₁ - d₁) (by omega) (by omega)).rev.castStart (congrArg C₁.vert hb₁_wrap)
  let A₂b : SimplePath G (L₂ - d₂) (C₂.vert a₂) (C₂.vert b₂) :=
    (cycleArcFwd C₂ b₂ (L₂ - d₂) (by omega) (by omega)).rev.castStart (congrArg C₂.vert hb₂_wrap)
  have hA₁f_in : ∀ i, ∃ x, A₁f.vert i = C₁.vert x := fun i => ⟨_, rfl⟩
  have hA₂f_in : ∀ i, ∃ x, A₂f.vert i = C₂.vert x := fun i => ⟨_, rfl⟩
  have hA₁b_in : ∀ i, ∃ x, A₁b.vert i = C₁.vert x := fun i => ⟨_, rfl⟩
  have hA₂b_in : ∀ i, ∃ x, A₂b.vert i = C₂.vert x := fun i => ⟨_, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact two_cycle_bridge_single C₁ C₂ hdisjC a₁ b₁ a₂ b₂ d₁ d₂ A₁f A₂f hA₁f_in hA₂f_in P₁ P₂ hP₁_int hP₂_int hP₁₂
  · exact two_cycle_bridge_single C₁ C₂ hdisjC a₁ b₁ a₂ b₂ d₁ (L₂ - d₂) A₁f A₂b hA₁f_in hA₂b_in P₁ P₂ hP₁_int hP₂_int hP₁₂
  · exact two_cycle_bridge_single C₁ C₂ hdisjC a₁ b₁ a₂ b₂ (L₁ - d₁) d₂ A₁b A₂f hA₁b_in hA₂f_in P₁ P₂ hP₁_int hP₂_int hP₁₂
  · exact two_cycle_bridge_single C₁ C₂ hdisjC a₁ b₁ a₂ b₂ (L₁ - d₁) (L₂ - d₂) A₁b A₂b hA₁b_in hA₂b_in P₁ P₂ hP₁_int hP₂_int hP₁₂

/-- Build a length-1 simple path from a single edge `G.Adj x y`. -/
def edgePath {V : Type*} {G : SimpleGraph V} {x y : V} (h : G.Adj x y) :
    SimplePath G 1 x y where
  hlen := le_rfl
  vert := fun i => if i.val = 0 then x else y
  inj := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> dsimp at hij
    · rfl
    · exact False.elim (G.ne_of_adj h hij)
    · exact False.elim (G.ne_of_adj h hij.symm)
    · rfl
  start_eq := rfl
  end_eq := rfl
  adj := by intro i; fin_cases i; exact h

/-- Theorem 5: Any two vertex-disjoint 5-cycles joined by ANY two independent edges
    unconditionally force `C_4` or `C_8` (`HasPow2Cycle G`). -/
theorem disjoint_c5_double_edge_forces_pow2 {V : Type*} {G : SimpleGraph V}
    (C₁ C₂ : SimpleCycle G 5)
    (hdisj : ∀ i j, C₁.vert i ≠ C₂.vert j)
    (a₁ b₁ a₂ b₂ : Fin 5) (h₁ : a₁ ≠ b₁) (h₂ : a₂ ≠ b₂)
    (he₁ : G.Adj (C₁.vert a₁) (C₂.vert a₂))
    (he₂ : G.Adj (C₁.vert b₁) (C₂.vert b₂)) :
    HasPow2Cycle G := by
  let d₁ := (b₁.val + 5 - a₁.val) % 5
  let d₂ := (b₂.val + 5 - a₂.val) % 5
  have hd₁_pos : 1 ≤ d₁ := by
    have : a₁.val ≠ b₁.val := fun h => h₁ (Fin.ext h)
    omega
  have hd₁_lt : d₁ < 5 := Nat.mod_lt _ (by omega)
  have hd₂_pos : 1 ≤ d₂ := by
    have : a₂.val ≠ b₂.val := fun h => h₂ (Fin.ext h)
    omega
  have hd₂_lt : d₂ < 5 := Nat.mod_lt _ (by omega)
  have hb₁_eq : ⟨(a₁.val + d₁) % 5, Nat.mod_lt _ (by omega)⟩ = b₁ := by
    apply Fin.ext; dsimp [d₁]; omega
  have hb₂_eq : ⟨(a₂.val + d₂) % 5, Nat.mod_lt _ (by omega)⟩ = b₂ := by
    apply Fin.ext; dsimp [d₂]; omega
  have he₂' : G.Adj (C₁.vert ⟨(a₁.val + d₁) % 5, Nat.mod_lt _ (by omega)⟩)
                    (C₂.vert ⟨(a₂.val + d₂) % 5, Nat.mod_lt _ (by omega)⟩) := by
    rw [hb₁_eq, hb₂_eq]; exact he₂
  let P₁ := edgePath he₁
  let P₂ := edgePath he₂'
  have hP₁_int : ∀ i : Fin 2, 0 < i.val → i.val < 1 →
      (∀ x, P₁.vert i ≠ C₁.vert x) ∧ (∀ y, P₁.vert i ≠ C₂.vert y) := fun i h0 h1 => by omega
  have hP₂_int : ∀ i : Fin 2, 0 < i.val → i.val < 1 →
      (∀ x, P₂.vert i ≠ C₁.vert x) ∧ (∀ y, P₂.vert i ≠ C₂.vert y) := fun i h0 h1 => by omega
  have hP₁₂ : ∀ i j : Fin 2, P₁.vert i ≠ P₂.vert j := by
    intro i j h
    fin_cases i <;> fin_cases j <;> dsimp [P₁, P₂, edgePath] at h
    · rw [hb₁_eq] at h; exact h₁ (C₁.inj h)
    · exact hdisj a₁ _ h
    · exact (hdisj _ a₂ h.symm)
    · rw [hb₂_eq] at h; exact h₂ (C₂.inj h)
  rcases two_cycle_double_bridge_four_cycles C₁ C₂ hdisj a₁ d₁ hd₁_pos hd₁_lt a₂ d₂ hd₂_pos hd₂_lt
      P₁ P₂ hP₁_int hP₂_int hP₁₂ with ⟨hc1, hc2, hc3, hc4⟩
  rcases c5_split_dichotomy a₁ b₁ h₁ with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩ <;>
  rcases c5_split_dichotomy a₂ b₂ h₂ with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩
  · exact ⟨4, isPow2Len_four, by have heq : d₁ + d₂ + 1 + 1 = 4 := (by omega); rw [heq] at hc1; exact hc1⟩
  · exact ⟨4, isPow2Len_four, by have heq : d₁ + (5 - d₂) + 1 + 1 = 4 := (by omega); rw [heq] at hc2; exact hc2⟩
  · exact ⟨8, isPow2Len_eight, by have heq : (5 - d₁) + d₂ + 1 + 1 = 8 := (by omega); rw [heq] at hc3; exact hc3⟩
  · exact ⟨8, isPow2Len_eight, by have heq : (5 - d₁) + (5 - d₂) + 1 + 1 = 8 := (by omega); rw [heq] at hc4; exact hc4⟩
  · exact ⟨4, isPow2Len_four, by have heq : (5 - d₁) + d₂ + 1 + 1 = 4 := (by omega); rw [heq] at hc3; exact hc3⟩
  · exact ⟨4, isPow2Len_four, by have heq : (5 - d₁) + (5 - d₂) + 1 + 1 = 4 := (by omega); rw [heq] at hc4; exact hc4⟩
  · exact ⟨8, isPow2Len_eight, by have heq : d₁ + d₂ + 1 + 1 = 8 := (by omega); rw [heq] at hc1; exact hc1⟩
  · exact ⟨8, isPow2Len_eight, by have heq : d₁ + (5 - d₂) + 1 + 1 = 8 := (by omega); rw [heq] at hc2; exact hc2⟩
  · exact ⟨8, isPow2Len_eight, by have heq : d₁ + (5 - d₂) + 1 + 1 = 8 := (by omega); rw [heq] at hc2; exact hc2⟩
  · exact ⟨8, isPow2Len_eight, by have heq : d₁ + d₂ + 1 + 1 = 8 := (by omega); rw [heq] at hc1; exact hc1⟩
  · exact ⟨8, isPow2Len_eight, by have heq : (5 - d₁) + (5 - d₂) + 1 + 1 = 8 := (by omega); rw [heq] at hc4; exact hc4⟩
  · exact ⟨8, isPow2Len_eight, by have heq : (5 - d₁) + d₂ + 1 + 1 = 8 := (by omega); rw [heq] at hc3; exact hc3⟩
  · exact ⟨8, isPow2Len_eight, by have heq : (5 - d₁) + (5 - d₂) + 1 + 1 = 8 := (by omega); rw [heq] at hc4; exact hc4⟩
  · exact ⟨8, isPow2Len_eight, by have heq : (5 - d₁) + d₂ + 1 + 1 = 8 := (by omega); rw [heq] at hc3; exact hc3⟩
  · exact ⟨8, isPow2Len_eight, by have heq : d₁ + (5 - d₂) + 1 + 1 = 8 := (by omega); rw [heq] at hc2; exact hc2⟩
  · exact ⟨8, isPow2Len_eight, by have heq : d₁ + d₂ + 1 + 1 = 8 := (by omega); rw [heq] at hc1; exact hc1⟩

/-- Theorem 6: Pure arithmetic core of the `C_5` `2^m`-ring theorem — for EVERY `m ≥ 1`
    (`k = 2^m`) and EVERY split profile `p + q = k`, there exist `u ≤ p` and `v ≤ q`
    such that `2k + q + 3u + v ∈ {2^(m+1), 2^(m+2)}`. -/
theorem c5_pow2_ring_arithmetic (m p q : ℕ) (hm : 1 ≤ m) (hpq : p + q = 2 ^ m) :
    ∃ u v : ℕ, u ≤ p ∧ v ≤ q ∧ IsPow2Len (2 * 2 ^ m + q + 3 * u + v) := by
  let k := 2 ^ m
  have hk_ge2 : 2 ≤ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hm
  by_cases hq0 : q = 0
  · refine ⟨0, 0, Nat.zero_le p, Nat.zero_le q, m + 1, by omega, ?_⟩
    have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    omega
  · by_cases hq1 : q = 1
    · -- Want 2k + 1 + 3u + v = 4k, i.e., 3u + v = 2k - 1 with v ∈ {0, 1}, u ≤ k - 1
      have hrem : (2 * k - 1) % 3 = 0 ∨ (2 * k - 1) % 3 = 1 := by
        have hmod : k % 3 = 1 ∨ k % 3 = 2 := by
          clear hq0 hq1 hpq hk_ge2
          induction m with
          | zero => omega
          | succ m' ih =>
            cases m' with
            | zero => right; decide
            | succ m'' =>
              have hih := ih (by omega)
              have h2 : 2 ^ (m'' + 2) = 2 * 2 ^ (m'' + 1) := by ring
              dsimp [k] at hih ⊢
              rw [h2]; omega
        omega
      rcases hrem with h0 | h1
      · refine ⟨(2 * k - 1) / 3, 0, by omega, by omega, m + 2, by omega, ?_⟩
        have hpow : 2 ^ (m + 2) = 4 * 2 ^ m := by ring
        omega
      · refine ⟨(2 * k - 2) / 3, 1, by omega, by omega, m + 2, by omega, ?_⟩
        have hpow : 2 ^ (m + 2) = 4 * 2 ^ m := by ring
        omega
    · -- q ≥ 2: target 4k = 2k + q + (2k - q); write 2k - q = 3u + v with v ∈ {0, 1, 2}
      have hq2 : 2 ≤ q := by omega
      let target := 2 * k - q
      by_cases hfit : target / 3 ≤ p
      · refine ⟨target / 3, target % 3, hfit, by omega, m + 2, by omega, ?_⟩
        have hpow : 2 ^ (m + 2) = 4 * 2 ^ m := by ring
        omega
      · refine ⟨p, target - 3 * p, le_rfl, by omega, m + 2, by omega, ?_⟩
        have hpow : 2 ^ (m + 2) = 4 * 2 ^ m := by ring
        omega

/-- A ring of `k ≥ 2` pairwise vertex-disjoint 5-cycles joined in a `k`-cycle by `k` edges,
    with distinct entry and exit vertices on each 5-cycle. -/
structure C5Ring {V : Type*} (G : SimpleGraph V) (k : ℕ) where
  hk : 2 ≤ k
  cyc : Fin k → SimpleCycle G 5
  disj : ∀ i j : Fin k, i ≠ j → ∀ a b : Fin 5, (cyc i).vert a ≠ (cyc j).vert b
  entry : Fin k → Fin 5
  exit : Fin k → Fin 5
  hne : ∀ i : Fin k, entry i ≠ exit i
  bridge : ∀ i : Fin k,
    G.Adj ((cyc i).vert (exit i))
          ((cyc ⟨(i.val + 1) % k, Nat.mod_lt _ (by omega)⟩).vert (entry ⟨(i.val + 1) % k, Nat.mod_lt _ (by omega)⟩))

/-- Clockwise distance `d ∈ {1, 2, 3, 4}` from `entry i` to `exit i` on the `i`-th 5-cycle. -/
def C5Ring.cwDist {V : Type*} {G : SimpleGraph V} {k : ℕ} (R : C5Ring G k) (i : Fin k) : ℕ :=
  ((R.exit i).val + 5 - (R.entry i).val) % 5

/-- Whether the `i`-th 5-cycle has a `(2, 3)` split (as opposed to `(1, 4)`). -/
def C5Ring.isType23 {V : Type*} {G : SimpleGraph V} {k : ℕ} (R : C5Ring G k) (i : Fin k) : Bool :=
  decide (R.cwDist i = 2 ∨ R.cwDist i = 3)

/-- Direction helper: whether `arcList` walks clockwise on the `i`-th 5-cycle. -/
def C5Ring.goCw {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (R : C5Ring G k) (i : Fin k) (useLong : Bool) : Bool :=
  if R.cwDist i ≤ 2 then !useLong else useLong

/-- Number of edges in the chosen arc (`1 ≤ steps ≤ 4`). -/
def C5Ring.steps {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (R : C5Ring G k) (i : Fin k) (useLong : Bool) : ℕ :=
  if R.goCw i useLong then R.cwDist i else 5 - R.cwDist i

/-- Arc vertex list from `entry i` to `exit i` along `cyc i`, inclusive of both endpoints. -/
def C5Ring.arcList {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (R : C5Ring G k) (i : Fin k) (useLong : Bool) : List V :=
  List.ofFn (fun j : Fin (R.steps i useLong + 1) =>
    if R.goCw i useLong then
      (R.cyc i).vert ⟨((R.entry i).val + j.val) % 5, Nat.mod_lt _ (by omega)⟩
    else
      (R.cyc i).vert ⟨((R.entry i).val + 5 - j.val) % 5, Nat.mod_lt _ (by omega)⟩)

lemma C5Ring.cwDist_bounds {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (R : C5Ring G k) (i : Fin k) : 1 ≤ R.cwDist i ∧ R.cwDist i ≤ 4 := by
  have hne : (R.entry i).val ≠ (R.exit i).val := fun h => R.hne i (Fin.ext h)
  unfold cwDist
  omega

lemma C5Ring.steps_bounds {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (R : C5Ring G k) (i : Fin k) (useLong : Bool) :
    1 ≤ R.steps i useLong ∧ R.steps i useLong ≤ 4 := by
  have hb := R.cwDist_bounds i
  unfold steps
  split_ifs <;> omega

lemma C5Ring.arcList_length {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (R : C5Ring G k) (i : Fin k) (useLong : Bool) :
    (R.arcList i useLong).length =
      if R.isType23 i then (if useLong then 4 else 3)
      else (if useLong then 5 else 2) := by
  have hb := R.cwDist_bounds i
  unfold arcList steps goCw isType23
  simp only [List.length_ofFn]
  cases useLong <;>
  · by_cases h1 : R.cwDist i = 1
    · simp [h1]
    · by_cases h2 : R.cwDist i = 2
      · simp [h2]
      · by_cases h3 : R.cwDist i = 3
        · simp [h3]
        · have h4 : R.cwDist i = 4 := by omega
          simp [h4]

lemma C5Ring.arcList_ne_nil {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (R : C5Ring G k) (i : Fin k) (useLong : Bool) :
    R.arcList i useLong ≠ [] := by
  intro h
  have hl := congrArg List.length h
  rw [R.arcList_length i useLong] at hl
  cases ht : R.isType23 i <;> cases useLong <;> simp [ht] at hl

lemma C5Ring.arcList_mem_cyc {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (R : C5Ring G k) (i : Fin k) (useLong : Bool) (v : V)
    (hv : v ∈ R.arcList i useLong) : ∃ a : Fin 5, v = (R.cyc i).vert a := by
  unfold arcList at hv
  rcases List.mem_ofFn.mp hv with ⟨j, rfl⟩
  split_ifs <;> exact ⟨_, rfl⟩

lemma C5Ring.arcList_nodup {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (R : C5Ring G k) (i : Fin k) (useLong : Bool) :
    (R.arcList i useLong).Nodup := by
  have hs := R.steps_bounds i useLong
  have he := (R.entry i).isLt
  unfold arcList
  rw [List.nodup_ofFn]
  intro a b hab
  have ha := a.isLt; have hb' := b.isLt
  dsimp only at hab
  split_ifs at hab with hcw
  · have h : ((R.entry i).val + a.val) % 5 = ((R.entry i).val + b.val) % 5 :=
      congrArg Fin.val ((R.cyc i).inj hab)
    exact Fin.ext (by first | (dsimp only; omega) | omega)
  · have h : ((R.entry i).val + 5 - a.val) % 5 = ((R.entry i).val + 5 - b.val) % 5 :=
      congrArg Fin.val ((R.cyc i).inj hab)
    exact Fin.ext (by first | (dsimp only; omega) | omega)

lemma C5Ring.arcList_head {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (R : C5Ring G k) (i : Fin k) (useLong : Bool) :
    (R.arcList i useLong).head (R.arcList_ne_nil i useLong) = (R.cyc i).vert (R.entry i) := by
  rw [List.head_eq_getElem]
  unfold arcList
  simp only [List.getElem_ofFn]
  have he := (R.entry i).isLt
  split_ifs
  · congr 1; apply Fin.ext; dsimp only; omega
  · congr 1; apply Fin.ext; dsimp only; omega

lemma C5Ring.arcList_getLast {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (R : C5Ring G k) (i : Fin k) (useLong : Bool) :
    (R.arcList i useLong).getLast (R.arcList_ne_nil i useLong) = (R.cyc i).vert (R.exit i) := by
  rw [List.getLast_eq_getElem]
  have hb := R.cwDist_bounds i
  have he := (R.entry i).isLt
  have hx := (R.exit i).isLt
  have hcw_def : R.cwDist i = ((R.exit i).val + 5 - (R.entry i).val) % 5 := rfl
  unfold arcList
  simp only [List.length_ofFn, List.getElem_ofFn]
  by_cases hcw : R.goCw i useLong = true
  · have hst : R.steps i useLong = R.cwDist i := by simp [steps, hcw]
    simp only [hcw, ↓reduceIte]
    congr 1; apply Fin.ext; dsimp only; omega
  · have hcw_f : R.goCw i useLong = false := Bool.eq_false_iff.mpr hcw
    have hst : R.steps i useLong = 5 - R.cwDist i := by simp [steps, hcw_f]
    simp only [hcw_f, Bool.false_eq_true, ↓reduceIte]
    congr 1; apply Fin.ext; dsimp only; omega

lemma C5Ring.arcList_adj {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (R : C5Ring G k) (i : Fin k) (useLong : Bool)
    (j : ℕ) (hj : j + 1 < (R.arcList i useLong).length) :
    G.Adj ((R.arcList i useLong)[j]) ((R.arcList i useLong)[j + 1]) := by
  have hs := R.steps_bounds i useLong
  have he := (R.entry i).isLt
  unfold arcList at hj ⊢
  simp only [List.length_ofFn, List.getElem_ofFn] at hj ⊢
  split_ifs with hcw
  · have h := (R.cyc i).adj ⟨((R.entry i).val + j) % 5, Nat.mod_lt _ (by omega)⟩
    convert h using 2
    apply Fin.ext; dsimp only; omega
  · have h := ((R.cyc i).adj ⟨((R.entry i).val + 5 - (j + 1)) % 5, Nat.mod_lt _ (by omega)⟩).symm
    convert h using 2
    apply Fin.ext; dsimp only; omega

lemma list_chain_adj_append {V : Type*} {G : SimpleGraph V}
    (l1 l2 : List V) (h1 : l1 ≠ []) (h2 : l2 ≠ [])
    (ha1 : ∀ k (hk : k + 1 < l1.length), G.Adj l1[k] l1[k + 1])
    (ha2 : ∀ k (hk : k + 1 < l2.length), G.Adj l2[k] l2[k + 1])
    (hjoin : G.Adj (l1.getLast h1) (l2.head h2)) :
    ∀ k (hk : k + 1 < (l1 ++ l2).length), G.Adj (l1 ++ l2)[k] (l1 ++ l2)[k + 1] := by
  intro k hk
  rw [List.length_append] at hk
  by_cases hlt : k + 1 < l1.length
  · rw [List.getElem_append_left (by omega), List.getElem_append_left hlt]
    exact ha1 k hlt
  · by_cases hlt2 : k < l1.length
    · rw [List.getElem_append_left hlt2, List.getElem_append_right (by omega)]
      have hsub : k + 1 - l1.length = 0 := by omega
      simp only [hsub]
      have hlast : l1[k] = l1.getLast h1 := by rw [List.getLast_eq_getElem]; congr 1; omega
      have hhead : l2[0]'(List.length_pos_iff.mpr h2) = l2.head h2 := by rw [List.head_eq_getElem]
      rw [hlast, hhead]; exact hjoin
    · rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
      have hsub : k + 1 - l1.length = (k - l1.length) + 1 := by omega
      simp only [hsub]
      exact ha2 (k - l1.length) (by omega)

lemma flatten_ofFn_chain_adj {V : Type*} {G : SimpleGraph V} :
    ∀ (r : ℕ) (s : Fin r → List V)
      (_hne : ∀ i, s i ≠ [])
      (_hadj : ∀ i k (hk : k + 1 < (s i).length), G.Adj (s i)[k] (s i)[k + 1])
      (_hjoin : ∀ (i : Fin r) (hi : i.val + 1 < r),
        G.Adj ((s i).getLast (_hne i)) ((s ⟨i.val + 1, hi⟩).head (_hne _))),
      ∀ k (hk : k + 1 < (List.ofFn s).flatten.length),
        G.Adj (List.ofFn s).flatten[k] (List.ofFn s).flatten[k + 1]
  | 0, _, _, _, _, k, hk => by simp at hk
  | 1, s, _, hadj, _, k, hk => by
      simp only [List.ofFn_succ, List.ofFn_zero, List.flatten_cons, List.flatten_nil,
        List.append_nil] at hk ⊢
      exact hadj 0 k hk
  | r + 2, s, hne, hadj, hjoin, k, hk => by
      have ih := flatten_ofFn_chain_adj (r + 1) (fun i => s i.succ)
        (fun i => hne i.succ) (fun i => hadj i.succ) (fun i hi => hjoin i.succ (by simp [Fin.val_succ]; omega))
      have hfl : (List.ofFn s).flatten = s 0 ++ (List.ofFn (fun i : Fin (r + 1) => s i.succ)).flatten := by
        simp [List.ofFn_succ]
      have htail_ne : (List.ofFn (fun i : Fin (r + 1) => s i.succ)).flatten ≠ [] := by
        intro h
        simp only [List.ofFn_succ, List.flatten_cons, List.append_eq_nil_iff] at h
        exact hne 1 h.1
      have hhead_eq : (List.ofFn (fun i : Fin (r + 1) => s i.succ)).flatten.head htail_ne =
          (s 1).head (hne 1) := by
        have hfl2 : (List.ofFn (fun i : Fin (r + 1) => s i.succ)).flatten =
            s 1 ++ (List.ofFn (fun i : Fin r => s i.succ.succ)).flatten := by
          simp [List.ofFn_succ]
        rw [List.head_eq_getElem, List.head_eq_getElem]
        simp only [hfl2, List.getElem_append_left (List.length_pos_iff.mpr (hne 1))]
      have hcomb := list_chain_adj_append (s 0) (List.ofFn (fun i : Fin (r + 1) => s i.succ)).flatten
        (hne 0) htail_ne (hadj 0) ih (by rw [hhead_eq]; exact hjoin 0 (by simp))
      simp only [hfl] at hk ⊢
      exact hcomb k hk

lemma flatten_ofFn_getLast {V : Type*} :
    ∀ (r : ℕ) (hr : 0 < r) (s : Fin r → List V) (hne : ∀ i, s i ≠ [])
      (hfl : (List.ofFn s).flatten ≠ []),
      (List.ofFn s).flatten.getLast hfl = (s ⟨r - 1, by omega⟩).getLast (hne _)
  | 0, hr, _, _, _ => by omega
  | 1, _, s, hne, hfl => by simp [List.ofFn_succ]
  | r + 2, _, s, hne, hfl => by
      have hfl_eq : (List.ofFn s).flatten = s 0 ++ (List.ofFn (fun i : Fin (r + 1) => s i.succ)).flatten := by
        simp [List.ofFn_succ]
      have htail_ne : (List.ofFn (fun i : Fin (r + 1) => s i.succ)).flatten ≠ [] := by
        intro h
        simp only [List.ofFn_succ, List.flatten_cons, List.append_eq_nil_iff] at h
        exact hne 1 h.1
      have ih := flatten_ofFn_getLast (r + 1) (by omega) (fun i => s i.succ)
        (fun i => hne i.succ) htail_ne
      calc (List.ofFn s).flatten.getLast hfl
          = (s 0 ++ (List.ofFn (fun i : Fin (r + 1) => s i.succ)).flatten).getLast (by rw [← hfl_eq]; exact hfl) := by
            congr 1
        _ = (List.ofFn (fun i : Fin (r + 1) => s i.succ)).flatten.getLast htail_ne :=
            List.getLast_append_of_ne_nil _ htail_ne
        _ = (s ⟨r + 1, by omega⟩).getLast (hne _) := ih

lemma flatten_ofFn_head {V : Type*} {r : ℕ} (hr : 0 < r) (s : Fin r → List V)
    (hne : ∀ i, s i ≠ []) (hfl : (List.ofFn s).flatten ≠ []) :
    (List.ofFn s).flatten.head hfl = (s ⟨0, hr⟩).head (hne ⟨0, hr⟩) := by
  cases r with
  | zero => omega
  | succ r' =>
    have hfl_eq : (List.ofFn s).flatten = s 0 ++ (List.ofFn (fun i : Fin r' => s i.succ)).flatten := by
      simp [List.ofFn_succ]
    rw [List.head_eq_getElem, List.head_eq_getElem]
    simp only [hfl_eq, List.getElem_append_left (List.length_pos_iff.mpr (hne 0))]; rfl

/-- Theorem 7: Every boolean arc-orientation choice `choice : Fin k → Bool` on a `C5Ring G k`
    realizes a genuine `SimpleCycle G` of exact length `∑_i (arcList i (choice i)).length`. -/
theorem c5_ring_realize_simple_cycle {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (R : C5Ring G k) (choice : Fin k → Bool) :
    Nonempty (SimpleCycle G (List.ofFn (fun i : Fin k => (R.arcList i (choice i)).length)).sum) := by
  let s : Fin k → List V := fun i => R.arcList i (choice i)
  let vs : List V := (List.ofFn s).flatten
  have hlen_eq : vs.length = (List.ofFn (fun i : Fin k => (s i).length)).sum := by
    unfold vs; rw [List.length_flatten, List.map_ofFn]; rfl
  have hge2 : ∀ i : Fin k, 2 ≤ (s i).length := by
    intro i; dsimp [s]; rw [R.arcList_length]; cases h1 : R.isType23 i <;> cases h2 : choice i <;> simp
  have hlen3 : 3 ≤ vs.length := by
    rw [hlen_eq]
    have hk := R.hk
    have hsum : ∀ (m : ℕ) (a : Fin m → ℕ), (∀ i, 2 ≤ a i) → 2 * m ≤ (List.ofFn a).sum := by
      intro m; induction m with
      | zero => intro _ _; simp
      | succ m ih =>
        intro a ha
        simp only [List.ofFn_succ, List.sum_cons]
        have h0 := ha 0
        have h1 := ih (fun i => a i.succ) (fun i => ha i.succ)
        omega
    have := hsum k (fun i => (s i).length) hge2
    omega
  have hnd : vs.Nodup := by
    unfold vs
    rw [List.nodup_flatten]
    refine ⟨?_, ?_⟩
    · intro l hl
      rcases List.mem_ofFn.mp hl with ⟨i, rfl⟩
      exact R.arcList_nodup i (choice i)
    · rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      rw [List.length_ofFn] at hi hj
      simp only [List.getElem_ofFn]
      intro v hvi hvj
      rcases R.arcList_mem_cyc ⟨i, hi⟩ (choice ⟨i, hi⟩) v hvi with ⟨a, ha⟩
      rcases R.arcList_mem_cyc ⟨j, hj⟩ (choice ⟨j, hj⟩) v hvj with ⟨b, hb⟩
      have hne_ij : (⟨i, hi⟩ : Fin k) ≠ ⟨j, hj⟩ := by intro h; have hv := congrArg Fin.val h; dsimp only at hv; omega
      exact R.disj ⟨i, hi⟩ ⟨j, hj⟩ hne_ij a b (ha.symm.trans hb)
  have hne : ∀ i : Fin k, s i ≠ [] := fun i => R.arcList_ne_nil i (choice i)
  have hchain : ∀ idx (hidx : idx + 1 < vs.length), G.Adj vs[idx] vs[idx + 1] := by
    refine flatten_ofFn_chain_adj k s hne (fun i => R.arcList_adj i (choice i)) ?_
    intro i hi
    dsimp [s]
    rw [R.arcList_getLast, R.arcList_head]
    have hbr := R.bridge i
    have hidx : (⟨(i.val + 1) % k, Nat.mod_lt _ (by omega)⟩ : Fin k) = ⟨i.val + 1, hi⟩ :=
      Fin.ext (Nat.mod_eq_of_lt hi)
    rw [hidx] at hbr
    exact hbr
  have hvs_ne : vs ≠ [] := by intro h; rw [h] at hlen3; simp at hlen3
  have hkpos : 0 < k := by have := R.hk; omega
  have hwrap : G.Adj (vs[vs.length - 1]'(by omega)) (vs[0]'(by omega)) := by
    have h1 : vs[vs.length - 1]'(by omega) = vs.getLast hvs_ne := (List.getLast_eq_getElem hvs_ne).symm
    have h2 : vs[0]'(by omega) = vs.head hvs_ne := (List.head_eq_getElem hvs_ne).symm
    rw [h1, h2]
    rw [flatten_ofFn_getLast k hkpos s hne hvs_ne, flatten_ofFn_head hkpos s hne hvs_ne]
    dsimp [s]
    rw [R.arcList_getLast, R.arcList_head]
    have hbr := R.bridge ⟨k - 1, by omega⟩
    have hidx : (⟨((⟨k - 1, by omega⟩ : Fin k).val + 1) % k, Nat.mod_lt _ (by omega)⟩ : Fin k) = ⟨0, hkpos⟩ := by
      apply Fin.ext; dsimp only
      have : k - 1 + 1 = k := by omega
      rw [this, Nat.mod_self]
    rw [hidx] at hbr
    exact hbr
  have hcyc := simpleCycle_of_list vs hlen3 hnd hchain hwrap
  rw [hlen_eq] at hcyc
  exact hcyc

/-- Exact subset-choice sum lemma: given `t : Fin k → Bool` with `p` false entries and `q` true
    entries, and any `u ≤ p`, `v ≤ q`, there exists `choice : Fin k → Bool` whose weighted sum
    equals `2*k + q + 3*u + v`. -/
private lemma exists_choice_for_uv :
    ∀ (k : ℕ) (t : Fin k → Bool),
      let q := (List.ofFn (fun i : Fin k => if t i then 1 else 0)).sum
      let p := k - q
      ∀ u v : ℕ, u ≤ p → v ≤ q →
        ∃ choice : Fin k → Bool,
          (List.ofFn (fun i : Fin k =>
            if t i then (if choice i then 4 else 3)
            else (if choice i then 5 else 2))).sum = 2 * k + q + 3 * u + v
  | 0, t, u, v, hu, hv => by
      simp only [List.ofFn_zero, List.sum_nil] at hu hv ⊢
      have : u = 0 := by omega
      have : v = 0 := by omega
      exact ⟨fun i => Fin.elim0 i, by omega⟩
  | k + 1, t, u, v, hu, hv => by
      have hq_split : (List.ofFn (fun i : Fin (k + 1) => if t i then 1 else 0)).sum =
          (if t 0 then 1 else 0) + (List.ofFn (fun i : Fin k => if t i.succ then 1 else 0)).sum := by
        simp [List.ofFn_succ]
      let q' := (List.ofFn (fun i : Fin k => if t i.succ then 1 else 0)).sum
      have hq'_le : q' ≤ k := by
        have hle : ∀ (m : ℕ) (f : Fin m → Bool),
            (List.ofFn (fun i => if f i then 1 else 0)).sum ≤ m := by
          intro m; induction m with
          | zero => intro _; simp
          | succ m ih =>
            intro f; simp only [List.ofFn_succ, List.sum_cons]
            have := ih (fun i => f i.succ); cases f 0 <;> simp <;> omega
        exact hle k (fun i => t i.succ)
      cases ht0 : t 0
      · -- t 0 = false: this slot is Type (1,4), contributes 2 (choice=false) or 5 (choice=true)
        have hq_eq : (List.ofFn (fun i : Fin (k + 1) => if t i then 1 else 0)).sum = q' := by
          rw [hq_split, ht0]; simp [q']
        rw [hq_eq] at hu hv
        by_cases hu0 : u = 0
        · rcases exists_choice_for_uv k (fun i => t i.succ) 0 v (Nat.zero_le _) hv with ⟨ch', hch'⟩
          refine ⟨Fin.cases false ch', ?_⟩
          rw [List.ofFn_succ, List.sum_cons]
          have hhead : (if t 0 then (if (Fin.cases false ch' : Fin (k + 1) → Bool) 0 then 4 else 3)
              else (if (Fin.cases false ch' : Fin (k + 1) → Bool) 0 then 5 else 2)) = 2 := by
            simp [ht0]
          have htail : (List.ofFn (fun i : Fin k =>
              if t i.succ then (if (Fin.cases false ch' : Fin (k + 1) → Bool) i.succ then 4 else 3)
              else (if (Fin.cases false ch' : Fin (k + 1) → Bool) i.succ then 5 else 2))) =
            (List.ofFn (fun i : Fin k =>
              if t i.succ then (if ch' i then 4 else 3)
              else (if ch' i then 5 else 2))) := by congr 1
          rw [hhead, htail, hch', hq_eq]; dsimp only [q']; omega
        · rcases exists_choice_for_uv k (fun i => t i.succ) (u - 1) v (by omega) hv with ⟨ch', hch'⟩
          refine ⟨Fin.cases true ch', ?_⟩
          rw [List.ofFn_succ, List.sum_cons]
          have hhead : (if t 0 then (if (Fin.cases true ch' : Fin (k + 1) → Bool) 0 then 4 else 3)
              else (if (Fin.cases true ch' : Fin (k + 1) → Bool) 0 then 5 else 2)) = 5 := by
            simp [ht0]
          have htail : (List.ofFn (fun i : Fin k =>
              if t i.succ then (if (Fin.cases true ch' : Fin (k + 1) → Bool) i.succ then 4 else 3)
              else (if (Fin.cases true ch' : Fin (k + 1) → Bool) i.succ then 5 else 2))) =
            (List.ofFn (fun i : Fin k =>
              if t i.succ then (if ch' i then 4 else 3)
              else (if ch' i then 5 else 2))) := by congr 1
          rw [hhead, htail, hch', hq_eq]; dsimp only [q']; omega
      · -- t 0 = true: this slot is Type (2,3), contributes 3 (choice=false) or 4 (choice=true)
        have hq_eq : (List.ofFn (fun i : Fin (k + 1) => if t i then 1 else 0)).sum = 1 + q' := by
          rw [hq_split, ht0]; simp [q']
        rw [hq_eq] at hu hv
        by_cases hv0 : v = 0
        · rcases exists_choice_for_uv k (fun i => t i.succ) u 0 (by omega) (Nat.zero_le _) with ⟨ch', hch'⟩
          refine ⟨Fin.cases false ch', ?_⟩
          rw [List.ofFn_succ, List.sum_cons]
          have hhead : (if t 0 then (if (Fin.cases false ch' : Fin (k + 1) → Bool) 0 then 4 else 3)
              else (if (Fin.cases false ch' : Fin (k + 1) → Bool) 0 then 5 else 2)) = 3 := by
            simp [ht0]
          have htail : (List.ofFn (fun i : Fin k =>
              if t i.succ then (if (Fin.cases false ch' : Fin (k + 1) → Bool) i.succ then 4 else 3)
              else (if (Fin.cases false ch' : Fin (k + 1) → Bool) i.succ then 5 else 2))) =
            (List.ofFn (fun i : Fin k =>
              if t i.succ then (if ch' i then 4 else 3)
              else (if ch' i then 5 else 2))) := by congr 1
          rw [hhead, htail, hch', hq_eq]; dsimp only [q']; omega
        · rcases exists_choice_for_uv k (fun i => t i.succ) u (v - 1) (by omega) (by omega) with ⟨ch', hch'⟩
          refine ⟨Fin.cases true ch', ?_⟩
          rw [List.ofFn_succ, List.sum_cons]
          have hhead : (if t 0 then (if (Fin.cases true ch' : Fin (k + 1) → Bool) 0 then 4 else 3)
              else (if (Fin.cases true ch' : Fin (k + 1) → Bool) 0 then 5 else 2)) = 4 := by
            simp [ht0]
          have htail : (List.ofFn (fun i : Fin k =>
              if t i.succ then (if (Fin.cases true ch' : Fin (k + 1) → Bool) i.succ then 4 else 3)
              else (if (Fin.cases true ch' : Fin (k + 1) → Bool) i.succ then 5 else 2))) =
            (List.ofFn (fun i : Fin k =>
              if t i.succ then (if ch' i then 4 else 3)
              else (if ch' i then 5 else 2))) := by congr 1
          rw [hhead, htail, hch', hq_eq]; dsimp only [q']; omega

/-- Theorem 8 (MAIN RING THEOREM): For EVERY `m ≥ 1`, ANY `2^m`-ring of vertex-disjoint
    5-cycles joined by `2^m` independent edges in ANY simple graph `G` unconditionally forces
    a simple cycle of length `2^(m+1)` or `2^(m+2)` (`HasPow2Cycle G`). -/
theorem c5_pow2_ring_forces_pow2_cycle {V : Type*} {G : SimpleGraph V} {m : ℕ}
    (hm : 1 ≤ m) (R : C5Ring G (2 ^ m)) :
    HasPow2Cycle G := by
  let q := (List.ofFn (fun i : Fin (2 ^ m) => if R.isType23 i then 1 else 0)).sum
  have hq_le : q ≤ 2 ^ m := by
    have hle : ∀ (r : ℕ) (f : Fin r → Bool),
        (List.ofFn (fun i => if f i then 1 else 0)).sum ≤ r := by
      intro r; induction r with
      | zero => intro _; simp
      | succ r ih =>
        intro f; simp only [List.ofFn_succ, List.sum_cons]
        have := ih (fun i => f i.succ); cases f 0 <;> simp <;> omega
    exact hle (2 ^ m) R.isType23
  let p := 2 ^ m - q
  have hpq : p + q = 2 ^ m := by omega
  rcases c5_pow2_ring_arithmetic m p q hm hpq with ⟨u, v, hu, hv, hpow⟩
  rcases exists_choice_for_uv (2 ^ m) R.isType23 u v hu hv with ⟨choice, hsum⟩
  have hcyc := c5_ring_realize_simple_cycle R choice
  have hfun : (fun i : Fin (2 ^ m) => (R.arcList i (choice i)).length) =
      (fun i : Fin (2 ^ m) =>
        if R.isType23 i then (if choice i then 4 else 3)
        else (if choice i then 5 else 2)) := by
    funext i; exact R.arcList_length i (choice i)
  rw [hfun, hsum] at hcyc
  exact ⟨2 * 2 ^ m + q + 3 * u + v, hpow, hcyc⟩

/-- A family of `t` pairwise vertex-disjoint cubic 5-cycles in a simple graph `G`. -/
structure CubicC5Family {V : Type*} (G : SimpleGraph V) (t : ℕ) where
  cyc : Fin t → SimpleCycle G 5
  disj : ∀ i j : Fin t, i ≠ j → ∀ a b : Fin 5, (cyc i).vert a ≠ (cyc j).vert b
  cubic : ∀ (i : Fin t) (a : Fin 5), CubicVertex G ((cyc i).vert a)

/-- The simple quotient graph `H = G / F` on `Fin t` whose edges join distinct 5-cycles
    connected by at least one edge of `G`. -/
def c5Quotient {V : Type*} (G : SimpleGraph V) {t : ℕ} (F : CubicC5Family G t) :
    SimpleGraph (Fin t) where
  Adj i j := i ≠ j ∧ ∃ a b : Fin 5, G.Adj ((F.cyc i).vert a) ((F.cyc j).vert b)
  symm := ⟨fun _ _ ⟨hne, a, b, h⟩ => ⟨hne.symm, b, a, h.symm⟩⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

/-- On a cubic 5-cycle, a vertex already has 2 neighbors inside the 5-cycle, so it can have
    at most 1 neighbor outside the 5-cycle. -/
lemma cubic_c5_unique_external_neighbor {V : Type*} {G : SimpleGraph V}
    (C : SimpleCycle G 5) (a : Fin 5) (hcubic : CubicVertex G (C.vert a))
    {w₁ w₂ : V} (hw₁ : ∀ x : Fin 5, w₁ ≠ C.vert x) (hw₂ : ∀ x : Fin 5, w₂ ≠ C.vert x)
    (hadj₁ : G.Adj (C.vert a) w₁) (hadj₂ : G.Adj (C.vert a) w₂) :
    w₁ = w₂ := by
  let a_next : Fin 5 := ⟨(a.val + 1) % 5, Nat.mod_lt _ (by omega)⟩
  let a_prev : Fin 5 := ⟨(a.val + 4) % 5, Nat.mod_lt _ (by omega)⟩
  have h1 : G.Adj (C.vert a) (C.vert a_next) := C.adj a
  have h2 : G.Adj (C.vert a) (C.vert a_prev) := by
    have h := (C.adj a_prev).symm
    have heq : (⟨(a_prev.val + 1) % 5, Nat.mod_lt _ (by omega)⟩ : Fin 5) = a := by
      apply Fin.ext; dsimp [a_prev]; omega
    rw [heq] at h; exact h
  have hnp : C.vert a_next ≠ C.vert a_prev := by
    intro h
    have hv := congrArg Fin.val (C.inj h)
    dsimp [a_next, a_prev] at hv; omega
  have hcases := hcubic (C.vert a_next) (C.vert a_prev) w₁ w₂ h1 h2 hadj₁ hadj₂
  rcases hcases with h | h | h | h | h | h
  · exact False.elim (hnp h)
  · exact False.elim (hw₁ a_next h.symm)
  · exact False.elim (hw₂ a_next h.symm)
  · exact False.elim (hw₁ a_prev h.symm)
  · exact False.elim (hw₂ a_prev h.symm)
  · exact h

/-- Theorem 9: If the quotient graph `c5Quotient G F` of a family of pairwise vertex-disjoint
    cubic 5-cycles contains a power-of-2 cycle, then `G` itself contains a power-of-2 cycle. -/
theorem cubic_c5_quotient_pow2_cycle_lifts {V : Type*} {G : SimpleGraph V} {t : ℕ}
    (F : CubicC5Family G t) (hH : HasPow2Cycle (c5Quotient G F)) :
    HasPow2Cycle G := by
  rcases hH with ⟨L, ⟨m, hm, rfl⟩, ⟨Q⟩⟩
  have hm1 : 1 ≤ m := by omega
  have hk2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hm1
  have hL4 : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hm
  -- For each step i in Q, pick an edge between F.cyc (Q.vert i) and F.cyc (Q.vert (i+1))
  have hex : ∀ i : Fin (2 ^ m),
      ∃ p : Fin 5 × Fin 5,
        G.Adj ((F.cyc (Q.vert i)).vert p.1)
              ((F.cyc (Q.vert ⟨(i.val + 1) % 2 ^ m, Nat.mod_lt _ (by omega)⟩)).vert p.2) := by
    intro i
    rcases (Q.adj i).2 with ⟨a, b, hab⟩
    exact ⟨(a, b), hab⟩
  choose edgeF hedgeF using hex
  let exitF : Fin (2 ^ m) → Fin 5 := fun i => (edgeF i).1
  let entryF : Fin (2 ^ m) → Fin 5 := fun i =>
    (edgeF ⟨(i.val + 2 ^ m - 1) % 2 ^ m, Nat.mod_lt _ (by omega)⟩).2
  have hprev_succ : ∀ i : Fin (2 ^ m),
      (⟨(((i.val + 2 ^ m - 1) % 2 ^ m) + 1) % 2 ^ m, Nat.mod_lt _ (by omega)⟩ : Fin (2 ^ m)) = i := by
    intro i; apply Fin.ext; dsimp only; exact mod_pred_succ (by omega) i.isLt
  have hne : ∀ i : Fin (2 ^ m), entryF i ≠ exitF i := by
    intro i hEq
    let iprev : Fin (2 ^ m) := ⟨(i.val + 2 ^ m - 1) % 2 ^ m, Nat.mod_lt _ (by omega)⟩
    let inext : Fin (2 ^ m) := ⟨(i.val + 1) % 2 ^ m, Nat.mod_lt _ (by omega)⟩
    have hiprev_ne_i : iprev ≠ i := by
      intro h; exact mod_pred_ne (by omega) i.isLt (congrArg Fin.val h)
    have hinext_ne_i : inext ≠ i := by
      intro h; exact mod_succ_ne (by omega) i.isLt (congrArg Fin.val h)
    have hiprev_ne_inext : iprev ≠ inext := by
      intro h; exact mod_pred_ne_succ (by omega) i.isLt (congrArg Fin.val h)
    have hadj_prev : G.Adj ((F.cyc (Q.vert i)).vert (entryF i))
                           ((F.cyc (Q.vert iprev)).vert (edgeF iprev).1) := by
      have h := (hedgeF iprev).symm
      rw [hprev_succ i] at h
      exact h
    have hadj_next : G.Adj ((F.cyc (Q.vert i)).vert (entryF i))
                           ((F.cyc (Q.vert inext)).vert (edgeF i).2) := by
      rw [hEq]; exact hedgeF i
    have hw1 : ∀ x : Fin 5, (F.cyc (Q.vert iprev)).vert (edgeF iprev).1 ≠ (F.cyc (Q.vert i)).vert x :=
      fun x => F.disj _ _ (fun h => hiprev_ne_i (Q.inj h)) _ x
    have hw2 : ∀ x : Fin 5, (F.cyc (Q.vert inext)).vert (edgeF i).2 ≠ (F.cyc (Q.vert i)).vert x :=
      fun x => F.disj _ _ (fun h => hinext_ne_i (Q.inj h)) _ x
    have heq_w := cubic_c5_unique_external_neighbor (F.cyc (Q.vert i)) (entryF i)
      (F.cubic (Q.vert i) (entryF i)) hw1 hw2 hadj_prev hadj_next
    exact F.disj _ _ (fun h => hiprev_ne_inext (Q.inj h)) _ _ heq_w
  let R : C5Ring G (2 ^ m) := {
    hk := hk2
    cyc := fun i => F.cyc (Q.vert i)
    disj := fun i j hij => F.disj (Q.vert i) (Q.vert j) (fun h => hij (Q.inj h))
    entry := entryF
    exit := exitF
    hne := hne
    bridge := fun i => by
      have h := hedgeF i
      have hstep : (⟨((((i.val + 1) % 2 ^ m) + 2 ^ m - 1) % 2 ^ m), Nat.mod_lt _ (by omega)⟩ : Fin (2 ^ m)) = i := by
        apply Fin.ext; dsimp only; exact mod_succ_pred (by omega) i.isLt
      dsimp [entryF, exitF]
      rw [hstep]
      exact h
  }
  exact c5_pow2_ring_forces_pow2_cycle hm1 R

/-- Theorem 10 (MAIN WHOLE-PROBLEM CLOSURE): In ANY vertex-minimal counterexample `G` to the
    Erdős–Gyárfás conjecture on `Fin n`, NO nonempty family of pairwise vertex-disjoint cubic
    5-cycles can have a quotient graph of minimum degree ≥ 3 (i.e. every cubic `C_5`-quotient
    is 2-degenerate). -/
theorem minimal_counterexample_no_cubic_c5_quotient_delta3 {n t : ℕ}
    {G : SimpleGraph (Fin n)} (hmin : MinimalCounterexample G)
    (F : CubicC5Family G t) (ht : 1 ≤ t) :
    ¬ MinDegAtLeast3 (c5Quotient G F) := by
  intro hdeg
  -- Inject Fin t × Fin 5 into Fin n to prove 5 * t ≤ n, hence t < n
  let emb : Fin t × Fin 5 → Fin n := fun p => (F.cyc p.1).vert p.2
  have hinj : Function.Injective emb := by
    intro ⟨i₁, a₁⟩ ⟨i₂, a₂⟩ h
    by_cases hi : i₁ = i₂
    · subst hi
      have ha := (F.cyc i₁).inj h
      exact Prod.ext rfl ha
    · exact False.elim (F.disj i₁ i₂ hi a₁ a₂ h)
  have hcard : Fintype.card (Fin t × Fin 5) ≤ Fintype.card (Fin n) :=
    Fintype.card_le_of_injective emb hinj
  simp only [Fintype.card_prod, Fintype.card_fin] at hcard
  have ht_lt : t < n := by omega
  have hH : HasPow2Cycle (c5Quotient G F) := hmin.2.2 t ht_lt (c5Quotient G F) hdeg
  exact hmin.2.1 (cubic_c5_quotient_pow2_cycle_lifts F hH)

/-- Theorem 11 (UNCONDITIONAL C5-FACTOR CLOSURE): No cubic graph on `Fin n` admitting a
    spanning `C_5`-factor can be a minimal counterexample to the Erdős–Gyárfás conjecture. -/
theorem c5_factor_minimal_counterexample_impossible {n t : ℕ}
    {G : SimpleGraph (Fin n)} (hmin : MinimalCounterexample G)
    (F : CubicC5Family G t) (ht : 1 ≤ t)
    (hcover : ∀ v : Fin n, ∃ (i : Fin t) (a : Fin 5), (F.cyc i).vert a = v) :
    False := by
  apply minimal_counterexample_no_cubic_c5_quotient_delta3 hmin F ht
  intro i
  -- Every vertex a ∈ Fin 5 on C_i has a neighbor outside C_i
  have hext : ∀ a : Fin 5, ∃ (j : Fin t) (b : Fin 5), j ≠ i ∧ G.Adj ((F.cyc i).vert a) ((F.cyc j).vert b) := by
    intro a
    rcases hmin.1 ((F.cyc i).vert a) with ⟨w₁, w₂, w₃, h12, h13, h23, ha1, ha2, ha3⟩
    let anext : Fin 5 := ⟨(a.val + 1) % 5, Nat.mod_lt _ (by omega)⟩
    let aprev : Fin 5 := ⟨(a.val + 4) % 5, Nat.mod_lt _ (by omega)⟩
    have hnot_both : ∃ w : Fin n, G.Adj ((F.cyc i).vert a) w ∧
        w ≠ (F.cyc i).vert anext ∧ w ≠ (F.cyc i).vert aprev := by
      by_cases h1 : w₁ ≠ (F.cyc i).vert anext ∧ w₁ ≠ (F.cyc i).vert aprev
      · exact ⟨w₁, ha1, h1.1, h1.2⟩
      · by_cases h2 : w₂ ≠ (F.cyc i).vert anext ∧ w₂ ≠ (F.cyc i).vert aprev
        · exact ⟨w₂, ha2, h2.1, h2.2⟩
        · by_cases h3 : w₃ ≠ (F.cyc i).vert anext ∧ w₃ ≠ (F.cyc i).vert aprev
          · exact ⟨w₃, ha3, h3.1, h3.2⟩
          · push Not at h1 h2 h3
            by_cases h1n : w₁ = (F.cyc i).vert anext
            · have h2p : w₂ = (F.cyc i).vert aprev := by
                by_cases h2n : w₂ = (F.cyc i).vert anext
                · exact False.elim (h12 (h1n.trans h2n.symm))
                · exact h2 h2n
              by_cases h3n : w₃ = (F.cyc i).vert anext
              · exact False.elim (h13 (h1n.trans h3n.symm))
              · exact False.elim (h23 (h2p.trans (h3 h3n).symm))
            · have h1p : w₁ = (F.cyc i).vert aprev := h1 h1n
              by_cases h2n : w₂ = (F.cyc i).vert anext
              · by_cases h3n : w₃ = (F.cyc i).vert anext
                · exact False.elim (h23 (h2n.trans h3n.symm))
                · exact False.elim (h13 (h1p.trans (h3 h3n).symm))
              · exact False.elim (h12 (h1p.trans (h2 h2n).symm))
    rcases hnot_both with ⟨w, haw, hwn, hwp⟩
    rcases hcover w with ⟨j, b, rfl⟩
    by_cases hji : j = i
    · subst hji
      have hba : b ≠ a := fun h => G.ne_of_adj haw (congrArg (F.cyc j).vert h.symm)
      have hbn : b ≠ anext := fun h => hwn (congrArg (F.cyc j).vert h)
      have hbp : b ≠ aprev := fun h => hwp (congrArg (F.cyc j).vert h)
      have hchord : b = a + 2 ∨ b = a + 3 := by
        have h1 : b.val ≠ a.val := fun h => hba (Fin.ext h)
        have h2 : b.val ≠ (a.val + 1) % 5 := fun h => hbn (Fin.ext h)
        have h3 : b.val ≠ (a.val + 4) % 5 := fun h => hbp (Fin.ext h)
        revert h1 h2 h3; fin_cases a <;> fin_cases b <;> decide
      have hc5 : ∀ x : Fin 5, G.Adj ((F.cyc j).vert x) ((F.cyc j).vert (x + 1)) := by
        intro x
        have h := (F.cyc j).adj x
        have heq : x + 1 = ⟨(x.val + 1) % 5, Nat.mod_lt _ (by omega)⟩ := by fin_cases x <;> rfl
        rw [heq]; exact h
      exact False.elim (hmin.2.1 ⟨4, isPow2Len_four, c5_chord_forces_c4 (F.cyc j).vert (F.cyc j).inj hc5 a b hchord haw⟩)
    · exact ⟨j, b, hji, haw⟩
  choose nbrC nbrV hnbrNe hnbrAdj using hext
  -- Any two distinct vertices a₁ ≠ a₂ on C_i must map to distinct cycles nbrC a₁ ≠ nbrC a₂!
  have hnbrInj : Function.Injective nbrC := by
    intro a₁ a₂ hEq
    by_contra hne
    have hvne : nbrV a₁ ≠ nbrV a₂ := by
      intro hveq
      have heq_v : (F.cyc (nbrC a₁)).vert (nbrV a₁) = (F.cyc (nbrC a₂)).vert (nbrV a₂) := by
        rw [hEq, hveq]
      have h2 : G.Adj ((F.cyc (nbrC a₁)).vert (nbrV a₁)) ((F.cyc i).vert a₂) := by
        rw [heq_v]; exact (hnbrAdj a₂).symm
      -- A cubic vertex on C_j cannot have 2 neighbors in C_i!
      have heq_a := cubic_c5_unique_external_neighbor (F.cyc (nbrC a₁)) (nbrV a₁)
        (F.cubic (nbrC a₁) (nbrV a₁))
        (fun x => F.disj i (nbrC a₁) (hnbrNe a₁).symm a₁ x)
        (fun x => F.disj i (nbrC a₁) (hnbrNe a₁).symm a₂ x)
        (hnbrAdj a₁).symm h2
      exact hne ((F.cyc i).inj heq_a)
    have hadj₂ : G.Adj ((F.cyc i).vert a₂) ((F.cyc (nbrC a₁)).vert (nbrV a₂)) := by
      rw [hEq]; exact hnbrAdj a₂
    exact hmin.2.1 (disjoint_c5_double_edge_forces_pow2 (F.cyc i) (F.cyc (nbrC a₁))
      (F.disj i (nbrC a₁) (hnbrNe a₁).symm) a₁ a₂ (nbrV a₁) (nbrV a₂) hne hvne
      (hnbrAdj a₁) hadj₂)
  refine ⟨nbrC 0, nbrC 1, nbrC 2,
    fun h => absurd (hnbrInj h) (by decide),
    fun h => absurd (hnbrInj h) (by decide),
    fun h => absurd (hnbrInj h) (by decide),
    ⟨(hnbrNe 0).symm, 0, nbrV 0, hnbrAdj 0⟩,
    ⟨(hnbrNe 1).symm, 1, nbrV 1, hnbrAdj 1⟩,
    ⟨(hnbrNe 2).symm, 2, nbrV 2, hnbrAdj 2⟩⟩

/-! ============================================================================
    PILLAR II: UNIVERSAL ARBITRARY-GIRTH PÓSA ROTATION & ENDPOINT-CHORD THEORY
    ============================================================================ -/

/-- Helper: extract a simple cycle from a subpath `v[lo..hi]` plus chord `G.Adj v[lo] v[hi]`. -/
lemma path_chord_simple_cycle {V : Type*} {G : SimpleGraph V} {ℓ : ℕ}
    (v : Fin (ℓ + 1) → V) (hv : Function.Injective v)
    (hpath : ∀ i : Fin ℓ, G.Adj (v ⟨i.val, by omega⟩) (v ⟨i.val + 1, by omega⟩))
    {lo hi : ℕ} (hlo : lo + 2 ≤ hi) (hhi : hi ≤ ℓ)
    (hchord : G.Adj (v ⟨lo, by omega⟩) (v ⟨hi, by omega⟩)) :
    Nonempty (SimpleCycle G (hi - lo + 1)) := by
  let L := hi - lo + 1
  let f : Fin L → V := fun i => v ⟨lo + i.val, by omega⟩
  have hinj : Function.Injective f := by
    intro i j hij
    have h := congrArg Fin.val (hv hij); dsimp only at h
    exact Fin.ext (by omega)
  have hadj : ∀ i : Fin L, G.Adj (f i) (f ⟨(i.val + 1) % L, Nat.mod_lt _ (by omega)⟩) := by
    intro i
    by_cases hlt : i.val + 1 < L
    · have hm : (i.val + 1) % L = i.val + 1 := Nat.mod_eq_of_lt hlt
      dsimp [f]
      have h := hpath ⟨lo + i.val, by omega⟩
      convert h using 2
      exact Fin.ext (by first | (dsimp only; omega) | omega)
    · have hlast : i.val = L - 1 := by omega
      have hm : (i.val + 1) % L = 0 := by
        have : i.val + 1 = L := by omega
        rw [this, Nat.mod_self]
      dsimp [f]
      convert hchord.symm using 2
      · exact Fin.ext (by first | (dsimp only; omega) | omega)
      · exact Fin.ext (by first | (dsimp only; omega) | omega)
  exact ⟨⟨by omega, f, hinj, hadj⟩⟩

/-- Theorem 12: Endpoint-Chord Three-Cycle Theorem — on ANY simple path `v₀, ..., v_ℓ`
    with two endpoint chords `{v₀, v_a}` and `{v₀, v_b}` (`2 ≤ a < b ≤ ℓ`), `G` contains
    simple cycles of lengths `a + 1`, `b + 1`, and `b - a + 2`. -/
theorem endpoint_chords_three_cycles {V : Type*} {G : SimpleGraph V} {ℓ a b : ℕ}
    (v : Fin (ℓ + 1) → V) (hv : Function.Injective v)
    (hpath : ∀ i : Fin ℓ, G.Adj (v ⟨i.val, by omega⟩) (v ⟨i.val + 1, by omega⟩))
    (ha : 2 ≤ a) (hab : a < b) (hb : b ≤ ℓ)
    (hca : G.Adj (v ⟨0, by omega⟩) (v ⟨a, by omega⟩))
    (hcb : G.Adj (v ⟨0, by omega⟩) (v ⟨b, by omega⟩)) :
    Nonempty (SimpleCycle G (a + 1)) ∧
    Nonempty (SimpleCycle G (b + 1)) ∧
    Nonempty (SimpleCycle G (b - a + 2)) := by
  refine ⟨?_, ?_, ?_⟩
  · have h := path_chord_simple_cycle v hv hpath (lo := 0) (hi := a) (by omega) (by omega) hca
    simpa using h
  · have h := path_chord_simple_cycle v hv hpath (lo := 0) (hi := b) (by omega) (by omega) hcb
    simpa using h
  · let L := b - a + 2
    let f : Fin L → V := fun i =>
      if h0 : i.val = 0 then v ⟨0, by omega⟩
      else v ⟨a + i.val - 1, by omega⟩
    have hinj : Function.Injective f := by
      intro i j hij
      dsimp only [f] at hij
      split_ifs at hij with hi hj hj
      · exact Fin.ext (by first | (dsimp only; omega) | omega)
      · have h := congrArg Fin.val (hv hij); dsimp only at h; omega
      · have h := congrArg Fin.val (hv hij); dsimp only at h; omega
      · have h := congrArg Fin.val (hv hij); dsimp only at h; exact Fin.ext (by first | (dsimp only; omega) | omega)
    have hadj : ∀ i : Fin L, G.Adj (f i) (f ⟨(i.val + 1) % L, Nat.mod_lt _ (by omega)⟩) := by
      intro i
      by_cases hi0 : i.val = 0
      · have hm : (i.val + 1) % L = 1 := by rw [hi0]; exact Nat.mod_eq_of_lt (by omega)
        dsimp only [f]; simp only [hm, hi0, Nat.one_ne_zero, ↓reduceDIte]
        have heq : (⟨a + 1 - 1, by omega⟩ : Fin (ℓ + 1)) = ⟨a, by omega⟩ := Fin.ext (by dsimp only; omega)
        rw [heq]; exact hca
      · by_cases hlt : i.val + 1 < L
        · have hm : (i.val + 1) % L = i.val + 1 := Nat.mod_eq_of_lt hlt
          have hc2 : (i.val + 1) % L ≠ 0 := by omega
          dsimp only [f]; simp only [hi0, hc2, ↓reduceDIte]
          have h := hpath ⟨a + i.val - 1, by omega⟩
          convert h using 2; exact Fin.ext (by first | (dsimp only; omega) | omega)
        · have hlast : i.val = L - 1 := by omega
          have hm : (i.val + 1) % L = 0 := by
            have : i.val + 1 = L := by omega
            rw [this, Nat.mod_self]
          dsimp only [f]; simp only [hi0, hm, ↓reduceDIte]
          convert hcb.symm using 2; exact Fin.ext (by first | (dsimp only; omega) | omega)
    exact ⟨⟨by omega, f, hinj, hadj⟩⟩

/-- Theorem 13: In any power-free graph, endpoint chords of a path cannot have dyadic gap
    `b - a = 2^k - 2` (for any `k ≥ 2`), nor `a = 2^k - 1` or `b = 2^k - 1`. -/
theorem endpoint_chords_forbid_dyadic_gaps {V : Type*} {G : SimpleGraph V} {ℓ a b k : ℕ}
    (hpf : PowerFree G)
    (v : Fin (ℓ + 1) → V) (hv : Function.Injective v)
    (hpath : ∀ i : Fin ℓ, G.Adj (v ⟨i.val, by omega⟩) (v ⟨i.val + 1, by omega⟩))
    (ha : 2 ≤ a) (hab : a < b) (hb : b ≤ ℓ) (hk : 2 ≤ k)
    (hca : G.Adj (v ⟨0, by omega⟩) (v ⟨a, by omega⟩))
    (hcb : G.Adj (v ⟨0, by omega⟩) (v ⟨b, by omega⟩)) :
    a + 1 ≠ 2 ^ k ∧ b + 1 ≠ 2 ^ k ∧ b - a + 2 ≠ 2 ^ k := by
  rcases endpoint_chords_three_cycles v hv hpath ha hab hb hca hcb with ⟨h1, h2, h3⟩
  refine ⟨?_, ?_, ?_⟩
  · intro heq; rw [heq] at h1; exact hpf ⟨2 ^ k, ⟨k, hk, rfl⟩, h1⟩
  · intro heq; rw [heq] at h2; exact hpf ⟨2 ^ k, ⟨k, hk, rfl⟩, h2⟩
  · intro heq; rw [heq] at h3; exact hpf ⟨2 ^ k, ⟨k, hk, rfl⟩, h3⟩

/-- Theorem 14: 1-Step Pósa Pivot Common-Neighbor `C_4` — if `v₀` has chords to `v_a, v_b`
    and the Pósa-rotated endpoint `v_{a-1}` is adjacent to `v_b`, then `G` contains `C_4`. -/
theorem posa_pivot_common_neighbor_c4 {V : Type*} {G : SimpleGraph V} {ℓ a b : ℕ}
    (v : Fin (ℓ + 1) → V) (hv : Function.Injective v)
    (hpath : ∀ i : Fin ℓ, G.Adj (v ⟨i.val, by omega⟩) (v ⟨i.val + 1, by omega⟩))
    (ha : 2 ≤ a) (hab : a < b) (hb : b ≤ ℓ)
    (hca : G.Adj (v ⟨0, by omega⟩) (v ⟨a, by omega⟩))
    (hcb : G.Adj (v ⟨0, by omega⟩) (v ⟨b, by omega⟩))
    (hpb : G.Adj (v ⟨a - 1, by omega⟩) (v ⟨b, by omega⟩)) :
    Nonempty (SimpleCycle G 4) := by
  let f : Fin 4 → V := fun i =>
    match i.val with
    | 0 => v ⟨0, by omega⟩
    | 1 => v ⟨a, by omega⟩
    | 2 => v ⟨a - 1, by omega⟩
    | _ => v ⟨b, by omega⟩
  refine ⟨⟨by omega, f, ?_, ?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [f] at hij
    all_goals try rfl
    all_goals (have h := congrArg Fin.val (hv hij); simp only at h; omega)
  · intro i
    fin_cases i <;> simp only [f]
    · exact hca
    · have h := (hpath ⟨a - 1, by omega⟩).symm
      convert h using 2; exact Fin.ext (by first | (dsimp only; omega) | omega)
    · exact hpb
    · exact hcb.symm

/-- Helper: build a cycle from a list of strictly distinct indices in `Fin (ℓ + 1)`. -/
lemma simpleCycle_of_idx_fn {V : Type*} {G : SimpleGraph V} {ℓ L : ℕ}
    (v : Fin (ℓ + 1) → V) (hv : Function.Injective v)
    (hL : 3 ≤ L) (idx : Fin L → Fin (ℓ + 1))
    (hidx_inj : Function.Injective idx)
    (hadj : ∀ i : Fin L, G.Adj (v (idx i)) (v (idx ⟨(i.val + 1) % L, Nat.mod_lt _ (by omega)⟩))) :
    Nonempty (SimpleCycle G L) :=
  ⟨⟨hL, fun i => v (idx i), hv.comp hidx_inj, hadj⟩⟩

/-- Theorem 15: 1-Step Pósa Pivot Inner Spectrum (`1 ≤ c ≤ a - 3`) — forces simple cycles of
    lengths `a - c`, `c + 3`, and `b - a + c + 3`. -/
theorem posa_pivot_inner_cycles {V : Type*} {G : SimpleGraph V} {ℓ a b c : ℕ}
    (v : Fin (ℓ + 1) → V) (hv : Function.Injective v)
    (hpath : ∀ i : Fin ℓ, G.Adj (v ⟨i.val, by omega⟩) (v ⟨i.val + 1, by omega⟩))
    (hc1 : 1 ≤ c) (hca3 : c + 3 ≤ a) (hab : a < b) (hb : b ≤ ℓ)
    (hca : G.Adj (v ⟨0, by omega⟩) (v ⟨a, by omega⟩))
    (hcb : G.Adj (v ⟨0, by omega⟩) (v ⟨b, by omega⟩))
    (hpc : G.Adj (v ⟨a - 1, by omega⟩) (v ⟨c, by omega⟩)) :
    Nonempty (SimpleCycle G (a - c)) ∧
    Nonempty (SimpleCycle G (c + 3)) ∧
    Nonempty (SimpleCycle G (b - a + c + 3)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Cycle 1: v_c .. v_{a-1} .. v_c (length a - c)
    have h := path_chord_simple_cycle v hv hpath (lo := c) (hi := a - 1) (by omega) (by omega) hpc.symm
    have heq : a - 1 - c + 1 = a - c := by omega
    rw [heq] at h; exact h
  · -- Cycle 2: v_0 → v_1 → ... → v_c → v_{a-1} → v_a → v_0 (length c + 3)
    let L := c + 3
    let idx : Fin L → Fin (ℓ + 1) := fun i =>
      if i.val ≤ c then ⟨i.val, by omega⟩
      else if i.val = c + 1 then ⟨a - 1, by omega⟩
      else ⟨a, by omega⟩
    refine simpleCycle_of_idx_fn v hv (by omega) idx ?_ ?_
    · intro i j hij
      have h := congrArg Fin.val hij
      dsimp [idx] at h
      split_ifs at h <;> (simp only [Fin.val_mk, Fin.val_zero] at h; exact Fin.ext (by omega))
    · intro i
      by_cases h1 : i.val < c
      · have hm : (i.val + 1) % L = i.val + 1 := Nat.mod_eq_of_lt (by omega)
        dsimp only [idx]; rw [hm]; rw [ite_pos (by omega), ite_pos (by omega)]
        have h := hpath ⟨i.val, by omega⟩
        convert h using 2; exact Fin.ext (by first | (dsimp only; omega) | omega)
      · by_cases h2 : i.val = c
        · have hm : (i.val + 1) % L = c + 1 := by rw [h2]; exact Nat.mod_eq_of_lt (by omega)
          dsimp only [idx]; rw [hm]; rw [ite_pos (by omega), ite_neg (by omega), ite_pos rfl]
          convert hpc.symm using 2; exact Fin.ext h2
        · by_cases h3 : i.val = c + 1
          · have hm : (i.val + 1) % L = c + 2 := by rw [h3]; exact Nat.mod_eq_of_lt (by omega)
            dsimp only [idx]; rw [hm]; rw [ite_neg (by omega), ite_pos h3, ite_neg (by omega), ite_neg (by omega)]
            have h := hpath ⟨a - 1, by omega⟩
            convert h using 2; exact Fin.ext (by first | (dsimp only; omega) | omega)
          · have hlast : i.val = c + 2 := by omega
            have hm : (i.val + 1) % L = 0 := by
              have : i.val + 1 = L := by omega
              rw [this, Nat.mod_self]
            dsimp only [idx]; rw [hm]; rw [ite_neg (by omega), ite_neg (by omega), ite_pos (by omega)]
            convert hca.symm using 2
  · -- Cycle 3: v_0 → ... → v_c → v_{a-1} → v_a → ... → v_b → v_0 (length b - a + c + 3)
    let L := b - a + c + 3
    let idx : Fin L → Fin (ℓ + 1) := fun i =>
      if i.val ≤ c then ⟨i.val, by omega⟩
      else ⟨a - 1 + (i.val - (c + 1)), by omega⟩
    refine simpleCycle_of_idx_fn v hv (by omega) idx ?_ ?_
    · intro i j hij
      have h := congrArg Fin.val hij
      dsimp [idx] at h
      split_ifs at h <;> (simp only [Fin.val_mk, Fin.val_zero] at h; exact Fin.ext (by omega))
    · intro i
      by_cases h1 : i.val < c
      · have hm : (i.val + 1) % L = i.val + 1 := Nat.mod_eq_of_lt (by omega)
        dsimp only [idx]; rw [hm]; rw [ite_pos (by omega), ite_pos (by omega)]
        have h := hpath ⟨i.val, by omega⟩
        convert h using 2; exact Fin.ext (by first | (dsimp only; omega) | omega)
      · by_cases h2 : i.val = c
        · have hm : (i.val + 1) % L = c + 1 := by rw [h2]; exact Nat.mod_eq_of_lt (by omega)
          dsimp only [idx]; rw [hm]; rw [ite_pos (by omega), ite_neg (by omega)]
          convert hpc.symm using 2
          · exact Fin.ext h2
          · exact Fin.ext (by first | (dsimp only; omega) | omega)
        · by_cases h3 : i.val + 1 < L
          · have hm : (i.val + 1) % L = i.val + 1 := Nat.mod_eq_of_lt h3
            dsimp only [idx]; rw [hm]; rw [ite_neg (by omega), ite_neg (by omega)]
            have h := hpath ⟨a - 1 + (i.val - (c + 1)), by omega⟩
            convert h using 2; exact Fin.ext (by first | (dsimp only; omega) | omega)
          · have hlast : i.val = L - 1 := by omega
            have hm : (i.val + 1) % L = 0 := by
              have : i.val + 1 = L := by omega
              rw [this, Nat.mod_self]
            dsimp only [idx]; rw [hm]; rw [ite_neg (by omega), ite_pos (by omega)]
            convert hcb.symm using 2
            exact Fin.ext (by first | (dsimp only; omega) | omega)

/-- Theorem 16: 1-Step Pósa Pivot Between Spectrum (`a < c < b`) — forces FOUR simple cycles
    of lengths `c - a + 2`, `c + 1`, `a + b - c + 1`, and `b - c + 4`. -/
theorem posa_pivot_between_cycles {V : Type*} {G : SimpleGraph V} {ℓ a b c : ℕ}
    (v : Fin (ℓ + 1) → V) (hv : Function.Injective v)
    (hpath : ∀ i : Fin ℓ, G.Adj (v ⟨i.val, by omega⟩) (v ⟨i.val + 1, by omega⟩))
    (ha : 2 ≤ a) (hac : a < c) (hcb_lt : c < b) (hb : b ≤ ℓ)
    (hca : G.Adj (v ⟨0, by omega⟩) (v ⟨a, by omega⟩))
    (hcb : G.Adj (v ⟨0, by omega⟩) (v ⟨b, by omega⟩))
    (hpc : G.Adj (v ⟨a - 1, by omega⟩) (v ⟨c, by omega⟩)) :
    Nonempty (SimpleCycle G (c - a + 2)) ∧
    Nonempty (SimpleCycle G (c + 1)) ∧
    Nonempty (SimpleCycle G (a + b - c + 1)) ∧
    Nonempty (SimpleCycle G (b - c + 4)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Cycle 1: v_{a-1} .. v_c .. v_{a-1} (length c - a + 2)
    have h := path_chord_simple_cycle v hv hpath (lo := a - 1) (hi := c) (by omega) (by omega) hpc
    have heq : c - (a - 1) + 1 = c - a + 2 := by omega
    rw [heq] at h; exact h
  · -- Cycle 2: v_0 → ... → v_{a-1} → v_c → v_{c-1} → ... → v_a → v_0 (length c + 1)
    let L := c + 1
    let idx : Fin L → Fin (ℓ + 1) := fun i =>
      if i.val < a then ⟨i.val, by omega⟩
      else ⟨c - (i.val - a), by omega⟩
    refine simpleCycle_of_idx_fn v hv (by omega) idx ?_ ?_
    · intro i j hij
      have h := congrArg Fin.val hij
      dsimp [idx] at h
      split_ifs at h <;> (simp only [Fin.val_mk, Fin.val_zero] at h; exact Fin.ext (by omega))
    · intro i
      by_cases h1 : i.val + 1 < a
      · have hm : (i.val + 1) % L = i.val + 1 := Nat.mod_eq_of_lt (by omega)
        dsimp only [idx]; rw [hm]; rw [ite_pos (by omega), ite_pos (by omega)]
        have h := hpath ⟨i.val, by omega⟩
        convert h using 2; exact Fin.ext (by first | (dsimp only; omega) | omega)
      · by_cases h2 : i.val < a
        · have hia : i.val = a - 1 := by omega
          have hm : (i.val + 1) % L = a := by
            have : i.val + 1 = a := by omega
            rw [this]; exact Nat.mod_eq_of_lt (by omega)
          dsimp only [idx]; rw [hm]; rw [ite_pos h2, ite_neg (by omega)]
          convert hpc using 2
          · exact Fin.ext hia
          · exact Fin.ext (by first | (dsimp only; omega) | omega)
        · by_cases h3 : i.val + 1 < L
          · have hm : (i.val + 1) % L = i.val + 1 := Nat.mod_eq_of_lt h3
            dsimp only [idx]; rw [hm]; rw [ite_neg h2, ite_neg (by omega)]
            have h := (hpath ⟨c - (i.val - a) - 1, by omega⟩).symm
            convert h using 2
            · exact Fin.ext (by first | (dsimp only; omega) | omega)
            · exact Fin.ext (by first | (dsimp only; omega) | omega)
          · have hlast : i.val = c := by omega
            have hm : (i.val + 1) % L = 0 := by
              have : i.val + 1 = L := by omega
              rw [this, Nat.mod_self]
            dsimp only [idx]; rw [hm]; rw [ite_neg h2, ite_pos (by omega)]
            convert hca.symm using 2
            exact Fin.ext (by first | (dsimp only; omega) | omega)
  · -- Cycle 3: v_0 → ... → v_{a-1} → v_c → v_{c+1} → ... → v_b → v_0 (length a + b - c + 1)
    let L := a + b - c + 1
    let idx : Fin L → Fin (ℓ + 1) := fun i =>
      if i.val < a then ⟨i.val, by omega⟩
      else ⟨c + (i.val - a), by omega⟩
    refine simpleCycle_of_idx_fn v hv (by omega) idx ?_ ?_
    · intro i j hij
      have h := congrArg Fin.val hij
      dsimp [idx] at h
      split_ifs at h <;> (simp only [Fin.val_mk, Fin.val_zero] at h; exact Fin.ext (by omega))
    · intro i
      by_cases h1 : i.val + 1 < a
      · have hm : (i.val + 1) % L = i.val + 1 := Nat.mod_eq_of_lt (by omega)
        dsimp only [idx]; rw [hm]; rw [ite_pos (by omega), ite_pos (by omega)]
        have h := hpath ⟨i.val, by omega⟩
        convert h using 2; exact Fin.ext (by first | (dsimp only; omega) | omega)
      · by_cases h2 : i.val < a
        · have hia : i.val = a - 1 := by omega
          have hm : (i.val + 1) % L = a := by
            have : i.val + 1 = a := by omega
            rw [this]; exact Nat.mod_eq_of_lt (by omega)
          dsimp only [idx]; rw [hm]; rw [ite_pos h2, ite_neg (by omega)]
          convert hpc using 2
          · exact Fin.ext hia
          · exact Fin.ext (by first | (dsimp only; omega) | omega)
        · by_cases h3 : i.val + 1 < L
          · have hm : (i.val + 1) % L = i.val + 1 := Nat.mod_eq_of_lt h3
            dsimp only [idx]; rw [hm]; rw [ite_neg h2, ite_neg (by omega)]
            have h := hpath ⟨c + (i.val - a), by omega⟩
            convert h using 2; exact Fin.ext (by first | (dsimp only; omega) | omega)
          · have hlast : i.val = L - 1 := by omega
            have hm : (i.val + 1) % L = 0 := by
              have : i.val + 1 = L := by omega
              rw [this, Nat.mod_self]
            dsimp only [idx]; rw [hm]; rw [ite_neg h2, ite_pos (by omega)]
            convert hcb.symm using 2
            exact Fin.ext (by first | (dsimp only; omega) | omega)
  · -- Cycle 4: v_0 → v_a → v_{a-1} → v_c → v_{c+1} → ... → v_b → v_0 (length b - c + 4)
    let L := b - c + 4
    let idx : Fin L → Fin (ℓ + 1) := fun i =>
      if i.val = 0 then ⟨0, by omega⟩
      else if i.val = 1 then ⟨a, by omega⟩
      else if i.val = 2 then ⟨a - 1, by omega⟩
      else ⟨c + (i.val - 3), by omega⟩
    refine simpleCycle_of_idx_fn v hv (by omega) idx ?_ ?_
    · intro i j hij
      have h := congrArg Fin.val hij
      dsimp [idx] at h
      split_ifs at h <;> (simp only [Fin.val_mk, Fin.val_zero] at h; exact Fin.ext (by omega))
    · intro i
      by_cases h0 : i.val = 0
      · have hm : (i.val + 1) % L = 1 := by rw [h0]; exact Nat.mod_eq_of_lt (by omega)
        dsimp only [idx]; rw [hm]; rw [ite_pos h0, ite_neg (by omega), ite_pos rfl]
        exact hca
      · by_cases h1 : i.val = 1
        · have hm : (i.val + 1) % L = 2 := by rw [h1]; exact Nat.mod_eq_of_lt (by omega)
          dsimp only [idx]; rw [hm]; rw [ite_neg h0, ite_pos h1, ite_neg (by omega), ite_neg (by omega), ite_pos rfl]
          have h := (hpath ⟨a - 1, by omega⟩).symm
          convert h using 2; exact Fin.ext (by first | (dsimp only; omega) | omega)
        · by_cases h2 : i.val = 2
          · have hm : (i.val + 1) % L = 3 := by rw [h2]; exact Nat.mod_eq_of_lt (by omega)
            dsimp only [idx]; rw [hm]; rw [ite_neg h0, ite_neg h1, ite_pos h2, ite_neg (by omega), ite_neg (by omega), ite_neg (by omega)]
            convert hpc using 2; exact Fin.ext (by first | (dsimp only; omega) | omega)
          · by_cases h3 : i.val + 1 < L
            · have hm : (i.val + 1) % L = i.val + 1 := Nat.mod_eq_of_lt h3
              dsimp only [idx]; rw [hm]; rw [ite_neg h0, ite_neg h1, ite_neg h2, ite_neg (by omega), ite_neg (by omega), ite_neg (by omega)]
              have h := hpath ⟨c + (i.val - 3), by omega⟩
              convert h using 2; exact Fin.ext (by first | (dsimp only; omega) | omega)
            · have hlast : i.val = L - 1 := by omega
              have hm : (i.val + 1) % L = 0 := by
                have : i.val + 1 = L := by omega
                rw [this, Nat.mod_self]
              dsimp only [idx]; rw [hm]; rw [ite_neg h0, ite_neg h1, ite_neg h2, ite_pos rfl]
              convert hcb.symm using 2; exact Fin.ext (by first | (dsimp only; omega) | omega)

/-- Theorem 17: 1-Step Pósa Pivot Beyond Spectrum (`a < b < c`) — forces FOUR simple cycles
    of lengths `c - a + 2`, `c + 1`, `a + c - b + 1`, and `c - b + 4`. -/
theorem posa_pivot_beyond_cycles {V : Type*} {G : SimpleGraph V} {ℓ a b c : ℕ}
    (v : Fin (ℓ + 1) → V) (hv : Function.Injective v)
    (hpath : ∀ i : Fin ℓ, G.Adj (v ⟨i.val, by omega⟩) (v ⟨i.val + 1, by omega⟩))
    (ha : 2 ≤ a) (hab : a < b) (hbc : b < c) (hc : c ≤ ℓ)
    (hca : G.Adj (v ⟨0, by omega⟩) (v ⟨a, by omega⟩))
    (hcb : G.Adj (v ⟨0, by omega⟩) (v ⟨b, by omega⟩))
    (hpc : G.Adj (v ⟨a - 1, by omega⟩) (v ⟨c, by omega⟩)) :
    Nonempty (SimpleCycle G (c - a + 2)) ∧
    Nonempty (SimpleCycle G (c + 1)) ∧
    Nonempty (SimpleCycle G (a + c - b + 1)) ∧
    Nonempty (SimpleCycle G (c - b + 4)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Cycle 1: v_{a-1} .. v_c .. v_{a-1}
    have h := path_chord_simple_cycle v hv hpath (lo := a - 1) (hi := c) (by omega) (by omega) hpc
    have heq : c - (a - 1) + 1 = c - a + 2 := by omega
    rw [heq] at h; exact h
  · -- Cycle 2: v_0 → ... → v_{a-1} → v_c → v_{c-1} → ... → v_a → v_0 (length c + 1)
    let L := c + 1
    let idx : Fin L → Fin (ℓ + 1) := fun i =>
      if i.val < a then ⟨i.val, by omega⟩
      else ⟨c - (i.val - a), by omega⟩
    refine simpleCycle_of_idx_fn v hv (by omega) idx ?_ ?_
    · intro i j hij
      have h := congrArg Fin.val hij
      dsimp [idx] at h
      split_ifs at h <;> (simp only [Fin.val_mk, Fin.val_zero] at h; exact Fin.ext (by omega))
    · intro i
      by_cases h1 : i.val + 1 < a
      · have hm : (i.val + 1) % L = i.val + 1 := Nat.mod_eq_of_lt (by omega)
        dsimp only [idx]; rw [hm]; rw [ite_pos (by omega), ite_pos (by omega)]
        have h := hpath ⟨i.val, by omega⟩
        convert h using 2; exact Fin.ext (by first | (dsimp only; omega) | omega)
      · by_cases h2 : i.val < a
        · have hia : i.val = a - 1 := by omega
          have hm : (i.val + 1) % L = a := by
            have : i.val + 1 = a := by omega
            rw [this]; exact Nat.mod_eq_of_lt (by omega)
          dsimp only [idx]; rw [hm]; rw [ite_pos h2, ite_neg (by omega)]
          convert hpc using 2
          · exact Fin.ext hia
          · exact Fin.ext (by first | (dsimp only; omega) | omega)
        · by_cases h3 : i.val + 1 < L
          · have hm : (i.val + 1) % L = i.val + 1 := Nat.mod_eq_of_lt h3
            dsimp only [idx]; rw [hm]; rw [ite_neg h2, ite_neg (by omega)]
            have h := (hpath ⟨c - (i.val - a) - 1, by omega⟩).symm
            convert h using 2
            · exact Fin.ext (by first | (dsimp only; omega) | omega)
            · exact Fin.ext (by first | (dsimp only; omega) | omega)
          · have hlast : i.val = c := by omega
            have hm : (i.val + 1) % L = 0 := by
              have : i.val + 1 = L := by omega
              rw [this, Nat.mod_self]
            dsimp only [idx]; rw [hm]; rw [ite_neg h2, ite_pos (by omega)]
            convert hca.symm using 2
            exact Fin.ext (by first | (dsimp only; omega) | omega)
  · -- Cycle 3: v_0 → ... → v_{a-1} → v_c → v_{c-1} → ... → v_b → v_0 (length a + c - b + 1)
    let L := a + c - b + 1
    let idx : Fin L → Fin (ℓ + 1) := fun i =>
      if i.val < a then ⟨i.val, by omega⟩
      else ⟨c - (i.val - a), by omega⟩
    refine simpleCycle_of_idx_fn v hv (by omega) idx ?_ ?_
    · intro i j hij
      have h := congrArg Fin.val hij
      dsimp [idx] at h
      split_ifs at h <;> (simp only [Fin.val_mk, Fin.val_zero] at h; exact Fin.ext (by omega))
    · intro i
      by_cases h1 : i.val + 1 < a
      · have hm : (i.val + 1) % L = i.val + 1 := Nat.mod_eq_of_lt (by omega)
        dsimp only [idx]; rw [hm]; rw [ite_pos (by omega), ite_pos (by omega)]
        have h := hpath ⟨i.val, by omega⟩
        convert h using 2; exact Fin.ext (by first | (dsimp only; omega) | omega)
      · by_cases h2 : i.val < a
        · have hia : i.val = a - 1 := by omega
          have hm : (i.val + 1) % L = a := by
            have : i.val + 1 = a := by omega
            rw [this]; exact Nat.mod_eq_of_lt (by omega)
          dsimp only [idx]; rw [hm]; rw [ite_pos h2, ite_neg (by omega)]
          convert hpc using 2
          · exact Fin.ext hia
          · exact Fin.ext (by first | (dsimp only; omega) | omega)
        · by_cases h3 : i.val + 1 < L
          · have hm : (i.val + 1) % L = i.val + 1 := Nat.mod_eq_of_lt h3
            dsimp only [idx]; rw [hm]; rw [ite_neg h2, ite_neg (by omega)]
            have h := (hpath ⟨c - (i.val - a) - 1, by omega⟩).symm
            convert h using 2
            · exact Fin.ext (by first | (dsimp only; omega) | omega)
            · exact Fin.ext (by first | (dsimp only; omega) | omega)
          · have hlast : i.val = L - 1 := by omega
            have hm : (i.val + 1) % L = 0 := by
              have : i.val + 1 = L := by omega
              rw [this, Nat.mod_self]
            dsimp only [idx]; rw [hm]; rw [ite_neg h2, ite_pos (by omega)]
            convert hcb.symm using 2
            exact Fin.ext (by first | (dsimp only; omega) | omega)
  · -- Cycle 4: v_0 → v_a → v_{a-1} → v_c → v_{c-1} → ... → v_b → v_0 (length c - b + 4)
    let L := c - b + 4
    let idx : Fin L → Fin (ℓ + 1) := fun i =>
      if i.val = 0 then ⟨0, by omega⟩
      else if i.val = 1 then ⟨a, by omega⟩
      else if i.val = 2 then ⟨a - 1, by omega⟩
      else ⟨c - (i.val - 3), by omega⟩
    refine simpleCycle_of_idx_fn v hv (by omega) idx ?_ ?_
    · intro i j hij
      have h := congrArg Fin.val hij
      dsimp [idx] at h
      split_ifs at h <;> (simp only [Fin.val_mk, Fin.val_zero] at h; exact Fin.ext (by omega))
    · intro i
      by_cases h0 : i.val = 0
      · have hm : (i.val + 1) % L = 1 := by rw [h0]; exact Nat.mod_eq_of_lt (by omega)
        dsimp only [idx]; rw [hm]; rw [ite_pos h0, ite_neg (by omega), ite_pos rfl]
        exact hca
      · by_cases h1 : i.val = 1
        · have hm : (i.val + 1) % L = 2 := by rw [h1]; exact Nat.mod_eq_of_lt (by omega)
          dsimp only [idx]; rw [hm]; rw [ite_neg h0, ite_pos h1, ite_neg (by omega), ite_neg (by omega), ite_pos rfl]
          have h := (hpath ⟨a - 1, by omega⟩).symm
          convert h using 2; exact Fin.ext (by first | (dsimp only; omega) | omega)
        · by_cases h2 : i.val = 2
          · have hm : (i.val + 1) % L = 3 := by rw [h2]; exact Nat.mod_eq_of_lt (by omega)
            dsimp only [idx]; rw [hm]; rw [ite_neg h0, ite_neg h1, ite_pos h2, ite_neg (by omega), ite_neg (by omega), ite_neg (by omega)]
            convert hpc using 2; exact Fin.ext (by first | (dsimp only; omega) | omega)
          · by_cases h3 : i.val + 1 < L
            · have hm : (i.val + 1) % L = i.val + 1 := Nat.mod_eq_of_lt h3
              dsimp only [idx]; rw [hm]; rw [ite_neg h0, ite_neg h1, ite_neg h2, ite_neg (by omega), ite_neg (by omega), ite_neg (by omega)]
              have h := (hpath ⟨c - (i.val - 3) - 1, by omega⟩).symm
              convert h using 2
              · exact Fin.ext (by first | (dsimp only; omega) | omega)
              · exact Fin.ext (by first | (dsimp only; omega) | omega)
            · have hlast : i.val = L - 1 := by omega
              have hm : (i.val + 1) % L = 0 := by
                have : i.val + 1 = L := by omega
                rw [this, Nat.mod_self]
              dsimp only [idx]; rw [hm]; rw [ite_neg h0, ite_neg h1, ite_neg h2, ite_pos rfl]
              convert hcb.symm using 2; exact Fin.ext (by first | (dsimp only; omega) | omega)

/-! ============================================================================
    PILLAR III: CROSSING-CHORD SPECTRUM, CUBIC CYCLE-SPACE & GIRTH-9 SIMPLICITY
    ============================================================================ -/

/-- Helper: extract a simple cycle from an arc of length `d ≥ 2` on `C` plus a chord
    joining its endpoints. -/
lemma cycle_arc_chord_cycle {V : Type*} {G : SimpleGraph V} {L d : ℕ}
    (C : SimpleCycle G L) (a : Fin L) (hd2 : 2 ≤ d) (hdL : d < L)
    (hchord : G.Adj (C.vert a) (C.vert ⟨(a.val + d) % L, Nat.mod_lt _ (by omega)⟩)) :
    Nonempty (SimpleCycle G (d + 1)) := by
  let P := cycleArcFwd C a d (by omega) hdL
  let Q := edgePath hchord
  have hint : ∀ (i : Fin (d + 1)) (j : Fin 2), 0 < i.val → i.val < d → 0 < j.val → j.val < 1 →
      P.vert i ≠ Q.vert j := fun _ _ _ _ h1 h2 => by omega
  have hxy : C.vert a ≠ C.vert ⟨(a.val + d) % L, Nat.mod_lt _ (by omega)⟩ :=
    G.ne_of_adj hchord
  exact two_paths_form_simple_cycle (by omega) P Q hint hxy

/-- Theorem 18: Crossing-Chord Six-Cycle Spectrum — on ANY cycle `C` of length
    `L = s₁ + s₂ + s₃ + s₄` with two crossing chords `{v_0, v_{s₁+s₂}}` and
    `{v_{s₁}, v_{s₁+s₂+s₃}}`, `G` contains simple cycles of ALL SIX chorded lengths:
    `s₁+s₂+1`, `s₃+s₄+1`, `s₂+s₃+1`, `s₄+s₁+1`, `s₁+s₃+2`, and `s₂+s₄+2`. -/
theorem crossing_chords_six_cycle_spectrum {V : Type*} {G : SimpleGraph V}
    {s₁ s₂ s₃ s₄ : ℕ} (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂) (hs₃ : 1 ≤ s₃) (hs₄ : 1 ≤ s₄)
    (C : SimpleCycle G (s₁ + s₂ + s₃ + s₄))
    (hc1 : G.Adj (C.vert ⟨0, by omega⟩) (C.vert ⟨s₁ + s₂, by omega⟩))
    (hc2 : G.Adj (C.vert ⟨s₁, by omega⟩) (C.vert ⟨s₁ + s₂ + s₃, by omega⟩)) :
    Nonempty (SimpleCycle G (s₁ + s₂ + 1)) ∧
    Nonempty (SimpleCycle G (s₃ + s₄ + 1)) ∧
    Nonempty (SimpleCycle G (s₂ + s₃ + 1)) ∧
    Nonempty (SimpleCycle G (s₄ + s₁ + 1)) ∧
    Nonempty (SimpleCycle G (s₁ + s₃ + 2)) ∧
    Nonempty (SimpleCycle G (s₂ + s₄ + 2)) := by
  let L := s₁ + s₂ + s₃ + s₄
  have h1 : Nonempty (SimpleCycle G (s₁ + s₂ + 1)) := by
    refine cycle_arc_chord_cycle C ⟨0, by omega⟩ (by omega) (by omega) ?_
    convert hc1 using 2; apply Fin.ext; dsimp only; rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega : s₁ + s₂ < L)]
  have h2 : Nonempty (SimpleCycle G (s₃ + s₄ + 1)) := by
    refine cycle_arc_chord_cycle C ⟨s₁ + s₂, by omega⟩ (by omega) (by omega) ?_
    convert hc1.symm using 2; apply Fin.ext; dsimp only
    have : s₁ + s₂ + (s₃ + s₄) = L := by omega
    rw [this, Nat.mod_self]
  have h3 : Nonempty (SimpleCycle G (s₂ + s₃ + 1)) := by
    refine cycle_arc_chord_cycle C ⟨s₁, by omega⟩ (by omega) (by omega) ?_
    convert hc2 using 2; apply Fin.ext; dsimp only
    have : s₁ + (s₂ + s₃) = s₁ + s₂ + s₃ := by omega
    rw [this, Nat.mod_eq_of_lt (by omega : s₁ + s₂ + s₃ < L)]
  have h4 : Nonempty (SimpleCycle G (s₄ + s₁ + 1)) := by
    refine cycle_arc_chord_cycle C ⟨s₁ + s₂ + s₃, by omega⟩ (by omega) (by omega) ?_
    convert hc2.symm using 2; apply Fin.ext; dsimp only
    have : (s₁ + s₂ + s₃) + (s₄ + s₁) = s₁ + L := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : s₁ < L)]
  -- 2-chord crossing cycle 1: 0 → ... → s₁ (arc s₁) --hc2--> s₁+s₂+s₃ → ... → s₁+s₂ (rev arc s₃) --hc1--> 0
  have h5 : Nonempty (SimpleCycle G (s₁ + s₃ + 2)) := by
    let M := s₁ + s₃ + 2
    let idx : Fin M → Fin L := fun i =>
      if i.val ≤ s₁ then ⟨i.val, by omega⟩
      else ⟨s₁ + s₂ + s₃ - (i.val - (s₁ + 1)), by omega⟩
    have hinj : Function.Injective (fun i => C.vert (idx i)) := by
      intro i j hij
      have h := congrArg Fin.val (C.inj hij)
      dsimp [idx] at h
      split_ifs at h <;> (simp only [Fin.val_mk, Fin.val_zero] at h; exact Fin.ext (by omega))
    have hadj : ∀ i : Fin M,
        G.Adj (C.vert (idx i)) (C.vert (idx ⟨(i.val + 1) % M, Nat.mod_lt _ (by omega)⟩)) := by
      intro i
      by_cases hlt1 : i.val < s₁
      · have hm : (i.val + 1) % M = i.val + 1 := Nat.mod_eq_of_lt (by omega)
        dsimp only [idx]; rw [hm]; rw [ite_pos (by omega), ite_pos (by omega)]
        have h := C.adj ⟨i.val, by omega⟩
        convert h using 2; apply Fin.ext; dsimp only; rw [Nat.mod_eq_of_lt (by omega)]
      · by_cases heq1 : i.val = s₁
        · have hm : (i.val + 1) % M = s₁ + 1 := by rw [heq1]; exact Nat.mod_eq_of_lt (by omega)
          dsimp only [idx]; rw [hm]; rw [ite_pos (by omega), ite_neg (by omega)]
          convert hc2 using 2
          · exact Fin.ext heq1
          · exact Fin.ext (by first | (dsimp only; omega) | omega)
        · by_cases hlt2 : i.val + 1 < M
          · have hm : (i.val + 1) % M = i.val + 1 := Nat.mod_eq_of_lt hlt2
            dsimp only [idx]; rw [hm]; rw [ite_neg (by omega), ite_neg (by omega)]
            have h := (C.adj ⟨s₁ + s₂ + s₃ - (i.val - (s₁ + 1)) - 1, by omega⟩).symm
            convert h using 2
            · apply Fin.ext; dsimp only; rw [Nat.mod_eq_of_lt (by omega)]; omega
            · exact Fin.ext (by first | (dsimp only; omega) | omega)
          · have hlast : i.val = M - 1 := by omega
            have hm : (i.val + 1) % M = 0 := by
              have : i.val + 1 = M := by omega
              rw [this, Nat.mod_self]
            dsimp only [idx]; rw [hm]; rw [ite_neg (by omega), ite_pos (by omega)]
            convert hc1.symm using 2
            exact Fin.ext (by first | (dsimp only; omega) | omega)
    exact ⟨⟨by omega, fun i => C.vert (idx i), hinj, hadj⟩⟩
  -- 2-chord crossing cycle 2: s₁ → ... → s₁+s₂ (arc s₂) --hc1--> 0 → L-1 → ... → s₁+s₂+s₃ (rev arc s₄) --hc2--> s₁
  have h6 : Nonempty (SimpleCycle G (s₂ + s₄ + 2)) := by
    let M := s₂ + s₄ + 2
    let idx : Fin M → Fin L := fun i =>
      if i.val ≤ s₂ then ⟨s₁ + i.val, by omega⟩
      else if i.val = s₂ + 1 then ⟨0, by omega⟩
      else ⟨L - (i.val - (s₂ + 1)), by omega⟩
    have hinj : Function.Injective (fun i => C.vert (idx i)) := by
      intro i j hij
      have h := congrArg Fin.val (C.inj hij)
      dsimp [idx] at h
      split_ifs at h <;> (simp only [Fin.val_mk, Fin.val_zero] at h; exact Fin.ext (by omega))
    have hadj : ∀ i : Fin M,
        G.Adj (C.vert (idx i)) (C.vert (idx ⟨(i.val + 1) % M, Nat.mod_lt _ (by omega)⟩)) := by
      intro i
      by_cases hlt1 : i.val < s₂
      · have hm : (i.val + 1) % M = i.val + 1 := Nat.mod_eq_of_lt (by omega)
        dsimp only [idx]; rw [hm]; rw [ite_pos (by omega), ite_pos (by omega)]
        have h := C.adj ⟨s₁ + i.val, by omega⟩
        convert h using 2; apply Fin.ext; dsimp only; rw [Nat.mod_eq_of_lt (by omega)]
      · by_cases heq1 : i.val = s₂
        · have hm : (i.val + 1) % M = s₂ + 1 := by rw [heq1]; exact Nat.mod_eq_of_lt (by omega)
          dsimp only [idx]; rw [hm]; rw [ite_pos (by omega), ite_neg (by omega), ite_pos rfl]
          convert hc1.symm using 2; exact Fin.ext (by first | (dsimp only; omega) | omega)
        · by_cases heq2 : i.val = s₂ + 1
          · have hm : (i.val + 1) % M = s₂ + 2 := by rw [heq2]; exact Nat.mod_eq_of_lt (by omega)
            dsimp only [idx]; rw [hm]; rw [ite_neg (by omega), ite_pos heq2, ite_neg (by omega), ite_neg (by omega)]
            have h := (C.adj ⟨L - 1, by omega⟩).symm
            convert h using 2
            · apply Fin.ext; dsimp only; have : L - 1 + 1 = L := by omega; rw [this, Nat.mod_self]
            · exact Fin.ext (by first | (dsimp only; omega) | omega)
          · by_cases hlt2 : i.val + 1 < M
            · have hm : (i.val + 1) % M = i.val + 1 := Nat.mod_eq_of_lt hlt2
              dsimp only [idx]; rw [hm]; rw [ite_neg (by omega), ite_neg heq2, ite_neg (by omega), ite_neg (by omega)]
              have h := (C.adj ⟨L - (i.val - (s₂ + 1)) - 1, by omega⟩).symm
              convert h using 2
              · apply Fin.ext; dsimp only; rw [Nat.mod_eq_of_lt (by omega)]; omega
              · exact Fin.ext (by first | (dsimp only; omega) | omega)
            · have hlast : i.val = M - 1 := by omega
              have hm : (i.val + 1) % M = 0 := by
                have : i.val + 1 = M := by omega
                rw [this, Nat.mod_self]
              dsimp only [idx]; rw [hm]; rw [ite_neg (by omega), ite_neg heq2, ite_pos (by omega)]
              convert hc2.symm using 2
              · exact Fin.ext (by first | (dsimp only; omega) | omega)
              · exact Fin.ext (by first | (dsimp only; omega) | omega)
    exact ⟨⟨by omega, fun i => C.vert (idx i), hinj, hadj⟩⟩
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- Theorem 19: Crossing-chord dyadic forcing — if two crossing chords on any cycle satisfy
    `s₁ + s₃ = 2^k - 2` or `s₂ + s₄ = 2^k - 2` (`k ≥ 2`), then `G` has a power-of-2 cycle. -/
theorem crossing_chords_pow2_forcing {V : Type*} {G : SimpleGraph V}
    {s₁ s₂ s₃ s₄ k : ℕ} (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂) (hs₃ : 1 ≤ s₃) (hs₄ : 1 ≤ s₄)
    (hk : 2 ≤ k)
    (C : SimpleCycle G (s₁ + s₂ + s₃ + s₄))
    (hc1 : G.Adj (C.vert ⟨0, by omega⟩) (C.vert ⟨s₁ + s₂, by omega⟩))
    (hc2 : G.Adj (C.vert ⟨s₁, by omega⟩) (C.vert ⟨s₁ + s₂ + s₃, by omega⟩))
    (hsum : s₁ + s₃ + 2 = 2 ^ k ∨ s₂ + s₄ + 2 = 2 ^ k) :
    HasPow2Cycle G := by
  rcases crossing_chords_six_cycle_spectrum hs₁ hs₂ hs₃ hs₄ C hc1 hc2 with ⟨_, _, _, _, h5, h6⟩
  rcases hsum with h5eq | h6eq
  · exact ⟨2 ^ k, ⟨k, hk, rfl⟩, by rw [← h5eq]; exact h5⟩
  · exact ⟨2 ^ k, ⟨k, hk, rfl⟩, by rw [← h6eq]; exact h6⟩

/-- Theorem 20: Cubic Cycle-Space Rigidity — in ANY graph `G`, if two simple cycles `C₁, C₂`
    both pass through a subcubic vertex `v` (`CubicVertex G v`), then `C₁` and `C₂` MUST
    share an edge incident to `v`. -/
theorem cubic_shared_vertex_cycles_share_edge {V : Type*} {G : SimpleGraph V}
    {L₁ L₂ : ℕ} (C₁ : SimpleCycle G L₁) (C₂ : SimpleCycle G L₂)
    (i : Fin L₁) (j : Fin L₂) (hv : C₁.vert i = C₂.vert j)
    (hcubic : CubicVertex G (C₁.vert i)) :
    ∃ w : V, G.Adj (C₁.vert i) w ∧
      (w = C₁.vert ⟨(i.val + 1) % L₁, Nat.mod_lt _ (by have := C₁.hL; omega)⟩ ∨
       w = C₁.vert ⟨(i.val + L₁ - 1) % L₁, Nat.mod_lt _ (by have := C₁.hL; omega)⟩) ∧
      (w = C₂.vert ⟨(j.val + 1) % L₂, Nat.mod_lt _ (by have := C₂.hL; omega)⟩ ∨
       w = C₂.vert ⟨(j.val + L₂ - 1) % L₂, Nat.mod_lt _ (by have := C₂.hL; omega)⟩) := by
  have hL1 := C₁.hL
  have hL2 := C₂.hL
  let n1 : Fin L₁ := ⟨(i.val + 1) % L₁, Nat.mod_lt _ (by omega)⟩
  let p1 : Fin L₁ := ⟨(i.val + L₁ - 1) % L₁, Nat.mod_lt _ (by omega)⟩
  let n2 : Fin L₂ := ⟨(j.val + 1) % L₂, Nat.mod_lt _ (by omega)⟩
  let p2 : Fin L₂ := ⟨(j.val + L₂ - 1) % L₂, Nat.mod_lt _ (by omega)⟩
  have ha1 : G.Adj (C₁.vert i) (C₁.vert n1) := C₁.adj i
  have hb1 : G.Adj (C₁.vert i) (C₁.vert p1) := by
    have h := (C₁.adj p1).symm
    have heq : (⟨(p1.val + 1) % L₁, Nat.mod_lt _ (by omega)⟩ : Fin L₁) = i := by
      apply Fin.ext; dsimp only [p1]; exact mod_pred_succ hL1 i.isLt
    rw [heq] at h; exact h
  have ha2 : G.Adj (C₁.vert i) (C₂.vert n2) := by rw [hv]; exact C₂.adj j
  have hb2 : G.Adj (C₁.vert i) (C₂.vert p2) := by
    rw [hv]
    have h := (C₂.adj p2).symm
    have heq : (⟨(p2.val + 1) % L₂, Nat.mod_lt _ (by omega)⟩ : Fin L₂) = j := by
      apply Fin.ext; dsimp only [p2]; exact mod_pred_succ hL2 j.isLt
    rw [heq] at h; exact h
  have hne1 : C₁.vert n1 ≠ C₁.vert p1 := by
    intro h
    exact mod_pred_ne_succ hL1 i.isLt (congrArg Fin.val (C₁.inj h)).symm
  have hne2 : C₂.vert n2 ≠ C₂.vert p2 := by
    intro h
    exact mod_pred_ne_succ hL2 j.isLt (congrArg Fin.val (C₂.inj h)).symm
  rcases hcubic (C₁.vert n1) (C₁.vert p1) (C₂.vert n2) (C₂.vert p2) ha1 hb1 ha2 hb2 with
    h | h | h | h | h | h
  · exact False.elim (hne1 h)
  · exact ⟨C₁.vert n1, ha1, Or.inl rfl, Or.inl h⟩
  · exact ⟨C₁.vert n1, ha1, Or.inl rfl, Or.inr h⟩
  · exact ⟨C₁.vert p1, hb1, Or.inr rfl, Or.inl h⟩
  · exact ⟨C₁.vert p1, hb1, Or.inr rfl, Or.inr h⟩
  · exact False.elim (hne2 h)

/-- Theorem 21: Girth-9 Non-Backtracking Walk-16 Simplicity Criterion — in any graph of
    girth `g ≥ 9`, no closed walk of length 16 can decompose into two non-trivial closed
    walks of lengths `L₁, L₂ ≥ g`, explaining why `Tr(B^16) = 32 · #C_16` is exact on `g ≥ 9`. -/
theorem girth9_closed_walk16_no_split (g L₁ L₂ : ℕ) (hg : 9 ≤ g)
    (h1 : g ≤ L₁) (h2 : g ≤ L₂) : L₁ + L₂ ≠ 16 := by
  omega

end E64Wave8Agent6
