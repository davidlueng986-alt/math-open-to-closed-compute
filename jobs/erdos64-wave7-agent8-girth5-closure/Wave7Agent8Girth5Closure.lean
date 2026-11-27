import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace E64Wave7Agent8

def IsPow2Len (L : ℕ) : Prop := ∃ k : ℕ, 2 ≤ k ∧ L = 2 ^ k

structure SimpleCycle {V : Type*} (G : SimpleGraph V) (L : ℕ) where
  hL : 3 ≤ L
  vert : Fin L → V
  inj : Function.Injective vert
  adj : ∀ i : Fin L, G.Adj (vert i) (vert ⟨(i.val + 1) % L, Nat.mod_lt _ (by omega)⟩)

def HasPow2Cycle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ L : ℕ, IsPow2Len L ∧ Nonempty (SimpleCycle G L)

def PowerFree {V : Type*} (G : SimpleGraph V) : Prop := ¬ HasPow2Cycle G

lemma isPow2Len_four : IsPow2Len 4 := ⟨2, le_rfl, by norm_num⟩
lemma isPow2Len_eight : IsPow2Len 8 := ⟨3, by omega, by norm_num⟩

/-! ### Pillar A: Exact C5-Star-Covered Girth-5+ Closure -/

theorem pentagram_p3_closes_c8 {V : Type*} {G : SimpleGraph V}
    (v u : Fin 5 → V)
    (hv_inj : Function.Injective v)
    (hu_inj : Function.Injective u)
    (hdisj : ∀ a b : Fin 5, v a ≠ u b)
    (hc5 : ∀ i : Fin 5, G.Adj (v i) (v (i + 1)))
    (hext : ∀ i : Fin 5, G.Adj (v i) (u i))
    (i : Fin 5)
    (hp1 : G.Adj (u (i + 3)) (u i))
    (hp2 : G.Adj (u i) (u (i + 2))) :
    Nonempty (SimpleCycle G 8) := by
  let f : Fin 8 → V := fun j =>
    match j.val with
    | 0 => v (i + 3)
    | 1 => u (i + 3)
    | 2 => u i
    | 3 => u (i + 2)
    | 4 => v (i + 2)
    | 5 => v (i + 1)
    | 6 => v i
    | _ => v (i + 4)
  have hinj : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> dsimp [f] at hab
    all_goals try rfl
    all_goals try exact False.elim (hdisj _ _ hab)
    all_goals try exact False.elim (hdisj _ _ hab.symm)
    all_goals try (have h := hv_inj hab; revert h; fin_cases i <;> decide)
    all_goals try (have h := hu_inj hab; revert h; fin_cases i <;> decide)
  have hadj : ∀ j : Fin 8, G.Adj (f j) (f ⟨(j.val + 1) % 8, Nat.mod_lt _ (by omega)⟩) := by
    intro j
    fin_cases j <;> dsimp [f]
    · exact hext (i + 3)
    · exact hp1
    · exact hp2
    · exact (hext (i + 2)).symm
    · have h := hc5 (i + 1)
      have heq : (i + 1 : Fin 5) + 1 = i + 2 := by fin_cases i <;> decide
      rw [heq] at h
      exact h.symm
    · exact (hc5 i).symm
    · have h := hc5 (i + 4)
      have heq : (i + 4 : Fin 5) + 1 = i := by fin_cases i <;> decide
      rw [heq] at h
      exact h.symm
    · have h := hc5 (i + 3)
      have heq : (i + 3 : Fin 5) + 1 = i + 4 := by fin_cases i <;> decide
      rw [heq] at h
      exact h.symm
  exact ⟨⟨by omega, f, hinj, hadj⟩⟩

theorem pentagram_cover_forces_p3 (R : Fin 5 → Fin 5 → Prop)
    (hsym : ∀ x y, R x y → R y x)
    (hpent : ∀ x y, R x y → y = x + 2 ∨ y = x + 3)
    (hcov : ∀ x : Fin 5, ∃ y : Fin 5, R x y) :
    ∃ i : Fin 5, R (i + 3) i ∧ R i (i + 2) := by
  by_contra hno
  push Not at hno
  have h1 : ∀ x : Fin 5, R x (x + 2) ∨ R x (x + 3) := by
    intro x
    rcases hcov x with ⟨y, hxy⟩
    rcases hpent x y hxy with rfl | rfl
    · exact Or.inl hxy
    · exact Or.inr hxy
  have h2 : ∀ x : Fin 5, ¬ (R x (x + 2) ∧ R x (x + 3)) := by
    intro x ⟨h2, h3⟩
    exact hno x (hsym _ _ h3) h2
  have hstep : ∀ x : Fin 5, R x (x + 2) → R (x + 4) (x + 1) := by
    intro x hx
    have h0 : R (x + 2) x := hsym _ _ hx
    have hneq : (x + 2 : Fin 5) + 3 = x := by fin_cases x <;> decide
    have hno2 : ¬ R (x + 2) ((x + 2) + 2) := by
      intro hc
      have h0' : R (x + 2) ((x + 2) + 3) := by rw [hneq]; exact h0
      exact h2 (x + 2) ⟨hc, h0'⟩
    have h3 : R (x + 4) (x + 1) ∨ R (x + 4) (x + 2) := by
      have ha := h1 (x + 4)
      have e1 : (x + 4 : Fin 5) + 2 = x + 1 := by fin_cases x <;> decide
      have e2 : (x + 4 : Fin 5) + 3 = x + 2 := by fin_cases x <;> decide
      rw [e1, e2] at ha
      exact ha
    rcases h3 with hok | hbad
    · exact hok
    · exfalso
      have hs := hsym _ _ hbad
      have e3 : (x + 2 : Fin 5) + 2 = x + 4 := by fin_cases x <;> decide
      rw [← e3] at hs
      exact hno2 hs
  have h0_cases := h1 0
  rcases h0_cases with h02 | h03
  · have h41 := hstep 0 h02
    have h30 : R (3 : Fin 5) 0 := hstep 4 h41
    have h03' : R (0 : Fin 5) 3 := hsym _ _ h30
    exact h2 0 ⟨h02, h03'⟩
  · have h30 : R (3 : Fin 5) 0 := hsym _ _ h03
    have h32 : R (3 : Fin 5) (3 + 2) := h30
    have h24 : R (2 : Fin 5) 4 := hstep 3 h32
    have h13 : R (1 : Fin 5) 3 := hstep 2 h24
    have h31 : R (3 : Fin 5) 1 := hsym _ _ h13
    exact h2 3 ⟨h32, h31⟩

theorem c5_star_covered_has_c8 {V : Type*} {G : SimpleGraph V}
    (v u : Fin 5 → V)
    (hv_inj : Function.Injective v)
    (hu_inj : Function.Injective u)
    (hdisj : ∀ a b : Fin 5, v a ≠ u b)
    (hc5 : ∀ i : Fin 5, G.Adj (v i) (v (i + 1)))
    (hext : ∀ i : Fin 5, G.Adj (v i) (u i))
    (hstar : ∀ i : Fin 5, G.Adj (u i) (u (i + 2)) ∨ G.Adj (u i) (u (i + 3))) :
    Nonempty (SimpleCycle G 8) := by
  let R : Fin 5 → Fin 5 → Prop := fun x y => (y = x + 2 ∨ y = x + 3) ∧ G.Adj (u x) (u y)
  have hsym : ∀ x y, R x y → R y x := by
    intro x y ⟨hp, ha⟩
    refine ⟨?_, ha.symm⟩
    rcases hp with rfl | rfl
    · right; fin_cases x <;> decide
    · left; fin_cases x <;> decide
  have hpent : ∀ x y, R x y → y = x + 2 ∨ y = x + 3 := fun _ _ h => h.1
  have hcov : ∀ x : Fin 5, ∃ y : Fin 5, R x y := by
    intro x
    rcases hstar x with h2 | h3
    · exact ⟨x + 2, Or.inl rfl, h2⟩
    · exact ⟨x + 3, Or.inr rfl, h3⟩
  rcases pentagram_cover_forces_p3 R hsym hpent hcov with ⟨i, hp1, hp2⟩
  exact pentagram_p3_closes_c8 v u hv_inj hu_inj hdisj hc5 hext i hp1.2 hp2.2

theorem c5_external_neighbors_distinct_of_girth5 {V : Type*} {G : SimpleGraph V}
    (hno3 : IsEmpty (SimpleCycle G 3))
    (hno4 : IsEmpty (SimpleCycle G 4))
    (v u : Fin 5 → V)
    (hv_inj : Function.Injective v)
    (hdisj : ∀ a b : Fin 5, v a ≠ u b)
    (hc5 : ∀ i : Fin 5, G.Adj (v i) (v (i + 1)))
    (hext : ∀ i : Fin 5, G.Adj (v i) (u i)) :
    Function.Injective u := by
  intro a b hab
  by_contra hne
  have hdiff : b = a + 1 ∨ b = a + 2 ∨ b = a + 3 ∨ b = a + 4 := by
    revert hne; fin_cases a <;> fin_cases b <;> decide
  have mk_c3 : ∀ x : Fin 5, u x = u (x + 1) → SimpleCycle G 3 := by
    intro x hx
    let f : Fin 3 → V := fun j => match j.val with | 0 => v x | 1 => v (x + 1) | _ => u x
    refine ⟨le_rfl, f, ?_, ?_⟩
    · intro p q hpq
      fin_cases p <;> fin_cases q <;> dsimp [f] at hpq
      all_goals try rfl
      all_goals try exact False.elim (hdisj _ _ hpq)
      all_goals try exact False.elim (hdisj _ _ hpq.symm)
      all_goals try (have h := hv_inj hpq; revert h; fin_cases x <;> decide)
    · intro p
      fin_cases p <;> dsimp [f]
      · exact hc5 x
      · rw [hx]; exact hext (x + 1)
      · exact (hext x).symm
  have mk_c4 : ∀ x : Fin 5, u x = u (x + 2) → SimpleCycle G 4 := by
    intro x hx
    let f : Fin 4 → V := fun j =>
      match j.val with | 0 => v x | 1 => v (x + 1) | 2 => v (x + 2) | _ => u x
    refine ⟨by omega, f, ?_, ?_⟩
    · intro p q hpq
      fin_cases p <;> fin_cases q <;> dsimp [f] at hpq
      all_goals try rfl
      all_goals try exact False.elim (hdisj _ _ hpq)
      all_goals try exact False.elim (hdisj _ _ hpq.symm)
      all_goals try (have h := hv_inj hpq; revert h; fin_cases x <;> decide)
    · intro p
      fin_cases p <;> dsimp [f]
      · exact hc5 x
      · have h := hc5 (x + 1)
        have heq : (x + 1 : Fin 5) + 1 = x + 2 := by fin_cases x <;> decide
        rw [heq] at h; exact h
      · rw [hx]; exact hext (x + 2)
      · exact (hext x).symm
  rcases hdiff with rfl | rfl | rfl | rfl
  · exact hno3.false (mk_c3 a hab)
  · exact hno4.false (mk_c4 a hab)
  · have e3 : (a + 3 : Fin 5) + 2 = a := by fin_cases a <;> decide
    have hx : u (a + 3) = u ((a + 3) + 2) := by rw [e3]; exact hab.symm
    exact hno4.false (mk_c4 (a + 3) hx)
  · have e4 : (a + 4 : Fin 5) + 1 = a := by fin_cases a <;> decide
    have hx : u (a + 4) = u ((a + 4) + 1) := by rw [e4]; exact hab.symm
    exact hno3.false (mk_c3 (a + 4) hx)

theorem c5_star_covered_girth5_has_pow2_cycle {V : Type*} {G : SimpleGraph V}
    (hno3 : IsEmpty (SimpleCycle G 3))
    (v u : Fin 5 → V)
    (hv_inj : Function.Injective v)
    (hdisj : ∀ a b : Fin 5, v a ≠ u b)
    (hc5 : ∀ i : Fin 5, G.Adj (v i) (v (i + 1)))
    (hext : ∀ i : Fin 5, G.Adj (v i) (u i))
    (hstar : ∀ i : Fin 5, G.Adj (u i) (u (i + 2)) ∨ G.Adj (u i) (u (i + 3))) :
    HasPow2Cycle G := by
  by_cases hc4 : Nonempty (SimpleCycle G 4)
  · exact ⟨4, isPow2Len_four, hc4⟩
  · have hno4 : IsEmpty (SimpleCycle G 4) := not_nonempty_iff.mp hc4
    have hu_inj := c5_external_neighbors_distinct_of_girth5 hno3 hno4 v u hv_inj hdisj hc5 hext
    exact ⟨8, isPow2Len_eight, c5_star_covered_has_c8 v u hv_inj hu_inj hdisj hc5 hext hstar⟩

/-! ### Pillar B: Exact Same-Scale & Cross-Scale (2^k + 1)-Cycle Overlap Obstructions -/

structure SimplePath {V : Type*} (G : SimpleGraph V) (len : ℕ) (x y : V) where
  hlen : 1 ≤ len
  vert : Fin (len + 1) → V
  inj : Function.Injective vert
  start_eq : vert ⟨0, by omega⟩ = x
  end_eq : vert ⟨len, by omega⟩ = y
  adj : ∀ i : Fin len, G.Adj (vert ⟨i.val, by omega⟩) (vert ⟨i.val + 1, by omega⟩)

theorem two_paths_form_simple_cycle {V : Type*} {G : SimpleGraph V}
    {a b : ℕ} {x y : V}
    (hab : 3 ≤ a + b)
    (P : SimplePath G a x y)
    (Q : SimplePath G b x y)
    (hint : ∀ (i : Fin (a + 1)) (j : Fin (b + 1)),
      0 < i.val → i.val < a → 0 < j.val → j.val < b → P.vert i ≠ Q.vert j)
    (_hxy : x ≠ y) :
    Nonempty (SimpleCycle G (a + b)) := by
  have ha1 : 1 ≤ a := P.hlen
  have hb1 : 1 ≤ b := Q.hlen
  let f : Fin (a + b) → V := fun k =>
    if hk : k.val < a then P.vert ⟨k.val, by omega⟩
    else Q.vert ⟨a + b - k.val, by omega⟩
  have hQ_not_x : ∀ j : Fin (b + 1), 0 < j.val → Q.vert j ≠ x := by
    intro j hj h
    have h0 : Q.vert ⟨0, by omega⟩ = x := Q.start_eq
    have heq := Q.inj (h.trans h0.symm)
    have : j.val = 0 := congrArg Fin.val heq
    omega
  have hP_not_y : ∀ i : Fin (a + 1), i.val < a → P.vert i ≠ y := by
    intro i hi h
    have ha : P.vert ⟨a, by omega⟩ = y := P.end_eq
    have heq := P.inj (h.trans ha.symm)
    have : i.val = a := congrArg Fin.val heq
    omega
  have hinj : Function.Injective f := by
    intro i j hij
    have hi_lt : i.val < a + b := i.isLt
    have hj_lt : j.val < a + b := j.isLt
    dsimp [f] at hij
    split_ifs at hij with hi hj hj
    · have h : (⟨i.val, by omega⟩ : Fin (a + 1)) = ⟨j.val, by omega⟩ := P.inj hij
      have hv : i.val = j.val := congrArg Fin.val h
      exact Fin.ext hv
    · exfalso
      by_cases hi0 : i.val = 0
      · have hpi : P.vert ⟨i.val, by omega⟩ = x := by
          have : (⟨i.val, by omega⟩ : Fin (a + 1)) = ⟨0, by omega⟩ := Fin.ext hi0
          rw [this]; exact P.start_eq
        rw [hpi] at hij
        exact hQ_not_x ⟨a + b - j.val, by omega⟩ (by omega) hij.symm
      · by_cases hja : j.val = a
        · have hqj : Q.vert ⟨a + b - j.val, by omega⟩ = y := by
            have : (⟨a + b - j.val, by omega⟩ : Fin (b + 1)) = ⟨b, by omega⟩ := Fin.ext (by omega)
            rw [this]; exact Q.end_eq
          rw [hqj] at hij
          exact hP_not_y ⟨i.val, by omega⟩ hi hij
        · exact hint ⟨i.val, by omega⟩ ⟨a + b - j.val, by omega⟩ (by omega) hi (by omega) (by omega) hij
    · exfalso
      by_cases hj0 : j.val = 0
      · have hpj : P.vert ⟨j.val, by omega⟩ = x := by
          have : (⟨j.val, by omega⟩ : Fin (a + 1)) = ⟨0, by omega⟩ := Fin.ext hj0
          rw [this]; exact P.start_eq
        rw [hpj] at hij
        exact hQ_not_x ⟨a + b - i.val, by omega⟩ (by omega) hij
      · by_cases hia : i.val = a
        · have hqi : Q.vert ⟨a + b - i.val, by omega⟩ = y := by
            have : (⟨a + b - i.val, by omega⟩ : Fin (b + 1)) = ⟨b, by omega⟩ := Fin.ext (by omega)
            rw [this]; exact Q.end_eq
          rw [hqi] at hij
          exact hP_not_y ⟨j.val, by omega⟩ hj hij.symm
        · exact hint ⟨j.val, by omega⟩ ⟨a + b - i.val, by omega⟩ (by omega) hj (by omega) (by omega) hij.symm
    · have h : (⟨a + b - i.val, by omega⟩ : Fin (b + 1)) = ⟨a + b - j.val, by omega⟩ := Q.inj hij
      have hv : a + b - i.val = a + b - j.val := congrArg Fin.val h
      exact Fin.ext (by omega)
  have hadj : ∀ k : Fin (a + b), G.Adj (f k) (f ⟨(k.val + 1) % (a + b), Nat.mod_lt _ (by omega)⟩) := by
    intro k
    have hk_lt : k.val < a + b := k.isLt
    by_cases hk1 : k.val + 1 < a
    · have hm : (k.val + 1) % (a + b) = k.val + 1 := Nat.mod_eq_of_lt (by omega)
      dsimp only [f]
      rw [dite_eq_left (by omega), dite_eq_left (by omega)]
      have hpa := P.adj ⟨k.val, by omega⟩
      have heq : (⟨(k.val + 1) % (a + b), by omega⟩ : Fin (a + 1)) = ⟨k.val + 1, by omega⟩ := Fin.ext hm
      rw [heq]
      exact hpa
    · by_cases hk2 : k.val < a
      · have hka : k.val + 1 = a := by omega
        have hm : (k.val + 1) % (a + b) = a := by rw [hka]; exact Nat.mod_eq_of_lt (by omega)
        dsimp only [f]
        rw [dite_eq_left hk2, dite_eq_right (by omega)]
        have hpa := P.adj ⟨k.val, hk2⟩
        have hpend : P.vert ⟨k.val + 1, by omega⟩ = y := by
          have : (⟨k.val + 1, by omega⟩ : Fin (a + 1)) = ⟨a, by omega⟩ := Fin.ext hka
          rw [this]; exact P.end_eq
        have hqend : Q.vert ⟨a + b - (k.val + 1) % (a + b), by omega⟩ = y := by
          have : (⟨a + b - (k.val + 1) % (a + b), by omega⟩ : Fin (b + 1)) = ⟨b, by omega⟩ := Fin.ext (by omega)
          rw [this]; exact Q.end_eq
        rw [hpend] at hpa
        rw [hqend]
        exact hpa
      · by_cases hk3 : k.val + 1 < a + b
        · have hm : (k.val + 1) % (a + b) = k.val + 1 := Nat.mod_eq_of_lt hk3
          dsimp only [f]
          rw [dite_eq_right hk2, dite_eq_right (by omega)]
          have hq := (Q.adj ⟨a + b - k.val - 1, by omega⟩).symm
          have heq1 : (⟨a + b - k.val - 1 + 1, by omega⟩ : Fin (b + 1)) = ⟨a + b - k.val, by omega⟩ :=
            Fin.ext (by omega)
          have heq2 : (⟨a + b - (k.val + 1) % (a + b), by omega⟩ : Fin (b + 1)) = ⟨a + b - k.val - 1, by omega⟩ :=
            Fin.ext (by omega)
          rw [heq1] at hq
          rw [heq2]
          exact hq
        · have hklast : k.val + 1 = a + b := by omega
          have hm : (k.val + 1) % (a + b) = 0 := by rw [hklast, Nat.mod_self]
          dsimp only [f]
          rw [dite_eq_right hk2, dite_eq_left (by omega)]
          have hq0 := (Q.adj ⟨0, hb1⟩).symm
          have hqstart : Q.vert ⟨0, by omega⟩ = x := Q.start_eq
          have hpstart : P.vert ⟨(k.val + 1) % (a + b), by omega⟩ = x := by
            have : (⟨(k.val + 1) % (a + b), by omega⟩ : Fin (a + 1)) = ⟨0, by omega⟩ := Fin.ext hm
            rw [this]; exact P.start_eq
          have hq1 : Q.vert ⟨a + b - k.val, by omega⟩ = Q.vert ⟨1, by omega⟩ := by
            congr 1; exact Fin.ext (by omega)
          rw [hqstart] at hq0
          rw [hpstart, hq1]
          exact hq0
  exact ⟨⟨hab, f, hinj, hadj⟩⟩

theorem same_scale_fermat_no_single_edge_overlap {V : Type*} {G : SimpleGraph V}
    (hpf : PowerFree G) {k : ℕ} (hk : 2 ≤ k) {x y : V} (hxy : x ≠ y)
    (P Q : SimplePath G (2 ^ k) x y)
    (hint : ∀ (i j : Fin (2 ^ k + 1)),
      0 < i.val → i.val < 2 ^ k → 0 < j.val → j.val < 2 ^ k → P.vert i ≠ Q.vert j) :
    False := by
  have hpow : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
  have hcyc := two_paths_form_simple_cycle (by omega) P Q hint hxy
  have hlen : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by ring
  rw [hlen] at hcyc
  exact hpf ⟨2 ^ (k + 1), ⟨k + 1, by omega, rfl⟩, hcyc⟩

theorem same_scale_fermat_forbidden_overlaps {V : Type*} {G : SimpleGraph V}
    (hpf : PowerFree G) {k j p : ℕ} (_hk : 2 ≤ k) (hj1 : 2 ≤ j) (hj2 : j ≤ k + 1)
    (hp : p = 2 ^ k + 1 - 2 ^ (j - 1))
    (_hplen : p < 2 ^ k + 1)
    {x y : V} (hxy : x ≠ y)
    (P Q : SimplePath G (2 ^ k + 1 - p) x y)
    (hint : ∀ (i1 i2 : Fin (2 ^ k + 1 - p + 1)),
      0 < i1.val → i1.val < 2 ^ k + 1 - p → 0 < i2.val → i2.val < 2 ^ k + 1 - p →
      P.vert i1 ≠ Q.vert i2) :
    False := by
  have h2j : 2 ^ (j - 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
  have hsum : (2 ^ k + 1 - p) + (2 ^ k + 1 - p) = 2 ^ j := by
    have h2 : 2 ^ (j - 1) + 2 ^ (j - 1) = 2 ^ j := by
      cases j with
      | zero => omega
      | succ j' => simp [Nat.pow_succ]; ring
    omega
  have hge4 : 4 ≤ 2 ^ j := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) hj1
  have hcyc := two_paths_form_simple_cycle (by omega) P Q hint hxy
  rw [hsum] at hcyc
  exact hpf ⟨2 ^ j, ⟨j, hj1, rfl⟩, hcyc⟩

theorem cross_scale_fermat_forbidden_overlap {V : Type*} {G : SimpleGraph V}
    (hpf : PowerFree G) {k1 k2 p : ℕ} (hk1 : 2 ≤ k1) (h12 : k1 < k2)
    (hp : p = 2 ^ (k1 - 1) + 1)
    {x y : V} (hxy : x ≠ y)
    (P : SimplePath G (2 ^ k1 + 1 - p) x y)
    (Q : SimplePath G (2 ^ k2 + 1 - p) x y)
    (hint : ∀ (i1 : Fin (2 ^ k1 + 1 - p + 1)) (i2 : Fin (2 ^ k2 + 1 - p + 1)),
      0 < i1.val → i1.val < 2 ^ k1 + 1 - p → 0 < i2.val → i2.val < 2 ^ k2 + 1 - p →
      P.vert i1 ≠ Q.vert i2) :
    False := by
  have h2k1 : 2 ^ (k1 - 1) + 2 ^ (k1 - 1) = 2 ^ k1 := by
    cases k1 with
    | zero => omega
    | succ m => simp [Nat.pow_succ]; ring
  have hpow12 : 2 ^ k1 ≤ 2 ^ k2 := Nat.pow_le_pow_right (by omega) (by omega)
  have hge4 : 4 ≤ 2 ^ k1 := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k1 := Nat.pow_le_pow_right (by omega) hk1
  have hsum : (2 ^ k1 + 1 - p) + (2 ^ k2 + 1 - p) = 2 ^ k2 := by omega
  have hcyc := two_paths_form_simple_cycle (by omega) P Q hint hxy
  rw [hsum] at hcyc
  exact hpf ⟨2 ^ k2, ⟨k2, by omega, rfl⟩, hcyc⟩

theorem disjoint_fermat_two_bridge_sum_obstruction {a1 a2 j : ℕ}
    (hj : 2 ≤ j) (hsum : a1 + a2 = 2 ^ j - 2) :
    IsPow2Len (2 + a1 + a2) := by
  have h4 : 4 ≤ 2 ^ j := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) hj
  exact ⟨j, hj, by omega⟩

theorem disjoint_fermat_two_bridge_diff3_obstruction {k a1 a2 : ℕ}
    (hk : 2 ≤ k) (ha2 : a2 ≤ 2 ^ k) (hdiff : a2 = a1 + 3) :
    IsPow2Len (2 + a1 + (2 ^ k + 1 - a2)) := by
  exact ⟨k, hk, by omega⟩

/-! ### Pillar C: Arbitrary-Girth Odd-Cycle (Δ=1) & Even-Cycle (Δ=2) Adjuster Necklace Closure -/

structure AdjusterNecklace {V : Type*} (G : SimpleGraph V) (r : ℕ) where
  base : List V
  short : Fin r → List V
  long : Fin r → List V
  h_base_ne : base ≠ []
  h_short_ne : ∀ i, short i ≠ []
  h_long_ne : ∀ i, long i ≠ []
  h_base_nodup : base.Nodup
  h_short_nodup : ∀ i, (short i).Nodup
  h_long_nodup : ∀ i, (long i).Nodup
  h_disj_base_short : ∀ i v, v ∈ base → v ∉ short i
  h_disj_base_long : ∀ i v, v ∈ base → v ∉ long i
  h_disj_slots : ∀ i j, i ≠ j → ∀ v,
    (v ∈ short i ∨ v ∈ long i) → v ∉ short j ∧ v ∉ long j
  h_base_adj : ∀ k : ℕ, (hk : k + 1 < base.length) → G.Adj (base[k]) (base[k + 1])
  h_short_adj : ∀ i (k : ℕ), (hk : k + 1 < (short i).length) → G.Adj ((short i)[k]) ((short i)[k + 1])
  h_long_adj : ∀ i (k : ℕ), (hk : k + 1 < (long i).length) → G.Adj ((long i)[k]) ((long i)[k + 1])
  h_join_slot : ∀ (i : Fin r) (hi : i.val + 1 < r) (b1 b2 : Bool),
    let s1 := if b1 then long i else short i
    let s2 := if b2 then long ⟨i.val + 1, hi⟩ else short ⟨i.val + 1, hi⟩
    G.Adj (s1.getLast (by cases b1 <;> simp [s1, h_short_ne, h_long_ne]))
          (s2.head (by cases b2 <;> simp [s2, h_short_ne, h_long_ne]))
  h_join_base_start : ∀ (hr : 0 < r) (b : Bool),
    let s0 := if b then long ⟨0, hr⟩ else short ⟨0, hr⟩
    G.Adj (base.getLast h_base_ne) (s0.head (by cases b <;> simp [s0, h_short_ne, h_long_ne]))
  h_join_end_base : ∀ (hr : 0 < r) (b : Bool),
    let sl := if b then long ⟨r - 1, by omega⟩ else short ⟨r - 1, by omega⟩
    G.Adj (sl.getLast (by cases b <;> simp [sl, h_short_ne, h_long_ne])) (base.head h_base_ne)
  h_base_cycle_if_zero : r = 0 → G.Adj (base.getLast h_base_ne) (base.head h_base_ne)
  h_min_len : 3 ≤ base.length + (List.ofFn (fun i => (short i).length)).sum

def AdjusterNecklace.seg {V : Type*} {G : SimpleGraph V} {r : ℕ}
    (N : AdjusterNecklace G r) (choice : Fin r → Bool) (i : Fin r) : List V :=
  if choice i then N.long i else N.short i

def AdjusterNecklace.realize {V : Type*} {G : SimpleGraph V} {r : ℕ}
    (N : AdjusterNecklace G r) (choice : Fin r → Bool) : List V :=
  N.base ++ (List.ofFn (N.seg choice)).flatten

lemma AdjusterNecklace.seg_ne_nil {V : Type*} {G : SimpleGraph V} {r : ℕ}
    (N : AdjusterNecklace G r) (choice : Fin r → Bool) (i : Fin r) :
    N.seg choice i ≠ [] := by
  unfold seg
  split
  · exact N.h_long_ne i
  · exact N.h_short_ne i

lemma AdjusterNecklace.seg_nodup {V : Type*} {G : SimpleGraph V} {r : ℕ}
    (N : AdjusterNecklace G r) (choice : Fin r → Bool) (i : Fin r) :
    (N.seg choice i).Nodup := by
  unfold seg
  split
  · exact N.h_long_nodup i
  · exact N.h_short_nodup i

lemma AdjusterNecklace.seg_adj {V : Type*} {G : SimpleGraph V} {r : ℕ}
    (N : AdjusterNecklace G r) (choice : Fin r → Bool) (i : Fin r)
    (k : ℕ) (hk : k + 1 < (N.seg choice i).length) :
    G.Adj ((N.seg choice i)[k]) ((N.seg choice i)[k + 1]) := by
  unfold seg at hk ⊢
  split at hk ⊢
  · exact N.h_long_adj i k hk
  · exact N.h_short_adj i k hk

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
    · have hkeq : k = l1.length - 1 := by omega
      rw [List.getElem_append_left hlt2, List.getElem_append_right (by omega)]
      have hsub : k + 1 - l1.length = 0 := by omega
      simp only [hsub]
      have hlast : l1[k] = l1.getLast h1 := by
        rw [List.getLast_eq_getElem]
        congr 1
      have hhead : l2[0]'(List.length_pos_iff.mpr h2) = l2.head h2 := by
        rw [List.head_eq_getElem]
      rw [hlast, hhead]
      exact hjoin
    · rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
      have hsub : k + 1 - l1.length = (k - l1.length) + 1 := by omega
      simp only [hsub]
      exact ha2 (k - l1.length) (by omega)

lemma nodup_flatten_ofFn {V : Type*} {r : ℕ} (s : Fin r → List V)
    (hnd : ∀ i, (s i).Nodup)
    (hdisj : ∀ i j, i ≠ j → ∀ v, v ∈ s i → v ∉ s j) :
    (List.ofFn s).flatten.Nodup := by
  rw [List.nodup_flatten]
  refine ⟨?_, ?_⟩
  · intro l hl
    rcases List.mem_ofFn.mp hl with ⟨i, rfl⟩
    exact hnd i
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    rw [List.length_ofFn] at hi hj
    simp only [List.getElem_ofFn]
    intro v hvi hvj
    exact hdisj ⟨i, hi⟩ ⟨j, hj⟩ (by intro h; have hv : i = j := congrArg Fin.val h; omega) v hvi hvj

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
        (fun i => hne i.succ)
        (fun i => hadj i.succ)
        (fun i hi => by
          have h1 : i.succ.val + 1 < r + 2 := by
            show i.val + 1 + 1 < r + 2; omega
          exact hjoin i.succ h1)
      have hfl : (List.ofFn s).flatten = s 0 ++ (List.ofFn (fun i : Fin (r + 1) => s i.succ)).flatten := by
        simp [List.ofFn_succ]
      have htail_ne : (List.ofFn (fun i : Fin (r + 1) => s i.succ)).flatten ≠ [] := by
        intro h
        have h0 : s 1 = [] := by
          simp only [List.ofFn_succ, List.flatten_cons, List.append_eq_nil_iff] at h
          exact h.1
        exact hne 1 h0
      have hhead_eq : (List.ofFn (fun i : Fin (r + 1) => s i.succ)).flatten.head htail_ne =
          (s 1).head (hne 1) := by
        have hfl2 : (List.ofFn (fun i : Fin (r + 1) => s i.succ)).flatten =
            s 1 ++ (List.ofFn (fun i : Fin r => s i.succ.succ)).flatten := by
          simp [List.ofFn_succ]
        rw [List.head_eq_getElem, List.head_eq_getElem]
        simp only [hfl2, List.getElem_append_left (List.length_pos_iff.mpr (hne 1))]
      have h0lt : (0 : Fin (r + 2)).val + 1 < r + 2 := by show 0 + 1 < r + 2; omega
      have hcomb := list_chain_adj_append (s 0) (List.ofFn (fun i : Fin (r + 1) => s i.succ)).flatten
        (hne 0) htail_ne (hadj 0) ih (by rw [hhead_eq]; exact hjoin 0 h0lt)
      simp only [hfl] at hk ⊢
      exact hcomb k hk

lemma flatten_ofFn_getLast {V : Type*} :
    ∀ (r : ℕ) (hr : 0 < r) (s : Fin r → List V) (hne : ∀ i, s i ≠ [])
      (hfl : (List.ofFn s).flatten ≠ []),
      (List.ofFn s).flatten.getLast hfl = (s ⟨r - 1, by omega⟩).getLast (hne _)
  | 0, hr, _, _, _ => by omega
  | 1, _, s, hne, hfl => by
      simp [List.ofFn_succ]
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
    simp only [hfl_eq, List.getElem_append_left (List.length_pos_iff.mpr (hne 0))]
    rfl

lemma AdjusterNecklace.realize_length {V : Type*} {G : SimpleGraph V} {r : ℕ}
    (N : AdjusterNecklace G r) (choice : Fin r → Bool) :
    (N.realize choice).length =
      N.base.length + (List.ofFn (fun i => (N.seg choice i).length)).sum := by
  unfold realize
  rw [List.length_append, List.length_flatten, List.map_ofFn]
  rfl

theorem AdjusterNecklace.realize_simple_cycle {V : Type*} {G : SimpleGraph V} {r : ℕ}
    (N : AdjusterNecklace G r)
    (hgrow : ∀ i, (N.short i).length ≤ (N.long i).length)
    (choice : Fin r → Bool) :
    Nonempty (SimpleCycle G (N.realize choice).length) := by
  let vs := N.realize choice
  have hlen3 : 3 ≤ vs.length := by
    have h1 : vs.length = N.base.length + (List.ofFn (fun i => (N.seg choice i).length)).sum :=
      N.realize_length choice
    have h2 : (List.ofFn (fun i => (N.short i).length)).sum ≤
              (List.ofFn (fun i => (N.seg choice i).length)).sum := by
      have hle : ∀ i : Fin r, (N.short i).length ≤ (N.seg choice i).length := by
        intro i; unfold seg; split
        · exact hgrow i
        · exact le_rfl
      have hzip : ∀ (m : ℕ) (a b : Fin m → ℕ), (∀ i, a i ≤ b i) →
          (List.ofFn a).sum ≤ (List.ofFn b).sum := by
        intro m
        induction m with
        | zero => intro _ _ _; simp
        | succ m ih =>
          intro a b hab
          simp only [List.ofFn_succ, List.sum_cons]
          exact Nat.add_le_add (hab 0) (ih (fun i => a i.succ) (fun i => b i.succ) (fun i => hab i.succ))
      exact hzip r _ _ hle
    have hmin := N.h_min_len
    omega
  have hnd : vs.Nodup := by
    unfold vs AdjusterNecklace.realize
    rw [List.nodup_append]
    refine ⟨N.h_base_nodup, ?_, ?_⟩
    · apply nodup_flatten_ofFn
      · exact N.seg_nodup choice
      · intro i j hij v hvi hvj
        have h1 : v ∈ N.short i ∨ v ∈ N.long i := by
          unfold seg at hvi
          split at hvi
          · exact Or.inr hvi
          · exact Or.inl hvi
        have h2 := N.h_disj_slots i j hij v h1
        unfold seg at hvj
        split at hvj
        · exact h2.2 hvj
        · exact h2.1 hvj
    · intro v hvb w hwf hvw
      subst hvw
      rw [List.mem_flatten] at hwf
      rcases hwf with ⟨l, hl, hvl⟩
      rcases List.mem_ofFn.mp hl with ⟨i, rfl⟩
      unfold seg at hvl
      split at hvl
      · exact N.h_disj_base_long i v hvb hvl
      · exact N.h_disj_base_short i v hvb hvl
  have hchain : ∀ k (hk : k + 1 < vs.length), G.Adj vs[k] vs[k + 1] := by
    by_cases hr : r = 0
    · subst hr
      intro k hk
      simp only [vs, AdjusterNecklace.realize, List.ofFn_zero, List.flatten_nil, List.append_nil] at hk ⊢
      exact N.h_base_adj k hk
    · have hrpos : 0 < r := by omega
      have hfl_ne : (List.ofFn (N.seg choice)).flatten ≠ [] := by
        cases r with
        | zero => omega
        | succ r' =>
          intro h
          simp only [List.ofFn_succ, List.flatten_cons, List.append_eq_nil_iff] at h
          exact N.seg_ne_nil choice 0 h.1
      have hfl_adj := flatten_ofFn_chain_adj r (N.seg choice) (N.seg_ne_nil choice)
        (N.seg_adj choice) (fun i hi => by
          simpa [AdjusterNecklace.seg] using N.h_join_slot i hi (choice i) (choice ⟨i.val + 1, hi⟩))
      have hhead := flatten_ofFn_head hrpos (N.seg choice) (N.seg_ne_nil choice) hfl_ne
      have hjoin : G.Adj (N.base.getLast N.h_base_ne) ((List.ofFn (N.seg choice)).flatten.head hfl_ne) := by
        rw [hhead]
        simpa [AdjusterNecklace.seg] using N.h_join_base_start hrpos (choice ⟨0, hrpos⟩)
      exact list_chain_adj_append N.base (List.ofFn (N.seg choice)).flatten
        N.h_base_ne hfl_ne N.h_base_adj hfl_adj hjoin
  have hvs_ne : vs ≠ [] := by intro h; rw [h] at hlen3; simp at hlen3
  have hwrap : G.Adj (vs.getLast hvs_ne) (vs.head hvs_ne) := by
    by_cases hr : r = 0
    · subst hr
      simp only [vs, AdjusterNecklace.realize, List.ofFn_zero, List.flatten_nil, List.append_nil]
      exact N.h_base_cycle_if_zero rfl
    · have hrpos : 0 < r := by omega
      have hfl_ne : (List.ofFn (N.seg choice)).flatten ≠ [] := by
        cases r with
        | zero => omega
        | succ r' =>
          intro h
          simp only [List.ofFn_succ, List.flatten_cons, List.append_eq_nil_iff] at h
          exact N.seg_ne_nil choice 0 h.1
      have hlast : vs.getLast hvs_ne = (N.seg choice ⟨r - 1, by omega⟩).getLast (N.seg_ne_nil choice _) := by
        calc vs.getLast hvs_ne
            = (List.ofFn (N.seg choice)).flatten.getLast hfl_ne :=
              List.getLast_append_of_ne_nil _ hfl_ne
          _ = (N.seg choice ⟨r - 1, by omega⟩).getLast (N.seg_ne_nil choice _) :=
              flatten_ofFn_getLast r hrpos (N.seg choice) (N.seg_ne_nil choice) hfl_ne
      have hhead : vs.head hvs_ne = N.base.head N.h_base_ne := by
        rw [List.head_eq_getElem, List.head_eq_getElem]
        simp only [vs, AdjusterNecklace.realize, List.getElem_append_left (List.length_pos_iff.mpr N.h_base_ne)]
      rw [hlast, hhead]
      simpa [AdjusterNecklace.seg] using N.h_join_end_base hrpos (choice ⟨r - 1, by omega⟩)
  let f : Fin vs.length → V := fun i => vs[i]
  have hinj : Function.Injective f := by
    intro i j hij
    exact List.nodup_iff_injective_getElem.mp hnd hij
  have hadj : ∀ i : Fin vs.length, G.Adj (f i) (f ⟨(i.val + 1) % vs.length, Nat.mod_lt _ (by omega)⟩) := by
    intro i
    by_cases hlt : i.val + 1 < vs.length
    · have hm : (i.val + 1) % vs.length = i.val + 1 := Nat.mod_eq_of_lt hlt
      dsimp [f]
      have h := hchain i.val hlt
      have heq : vs[(i.val + 1) % vs.length]'(Nat.mod_lt _ (by omega)) = vs[i.val + 1]'hlt := by
        congr 1
      rw [heq]
      exact h
    · have hlast_idx : i.val = vs.length - 1 := by omega
      have hm : (i.val + 1) % vs.length = 0 := by
        have : i.val + 1 = vs.length := by omega
        rw [this, Nat.mod_self]
      dsimp [f]
      have h1 : vs[i.val] = vs.getLast hvs_ne := by
        rw [List.getLast_eq_getElem]; congr 1
      have h2 : vs[(i.val + 1) % vs.length]'(Nat.mod_lt _ (by omega)) = vs.head hvs_ne := by
        rw [List.head_eq_getElem]; congr 1
      rw [h1, h2]
      exact hwrap
  exact ⟨⟨hlen3, f, hinj, hadj⟩⟩

private lemma sum_ofFn_prefix_jump (r t Δ : ℕ) (ht : t ≤ r) (a : Fin r → ℕ) :
    (List.ofFn (fun i : Fin r => if decide (i.val < t) then a i + Δ else a i)).sum =
      (List.ofFn a).sum + t * Δ := by
  induction r generalizing t with
  | zero =>
    have : t = 0 := by omega
    subst this; simp
  | succ r ih =>
    simp only [List.ofFn_succ, List.sum_cons]
    cases t with
    | zero =>
      simp only [Nat.not_lt_zero, decide_false, Bool.false_eq_true, ↓reduceIte, zero_mul, add_zero]
      have hsub : (fun i : Fin r => if decide (i.succ.val < 0) then a i.succ + Δ else a i.succ) =
                  (fun i : Fin r => a i.succ) := by
        funext i; simp
      rw [hsub]
    | succ t' =>
      have h0 : decide ((0 : Fin (r + 1)).val < t' + 1) = true := by simp
      simp only [h0, ↓reduceIte]
      have hsub : (fun i : Fin r => if decide (i.succ.val < t' + 1) then a i.succ + Δ else a i.succ) =
                  (fun i : Fin r => if decide (i.val < t') then a i.succ + Δ else a i.succ) := by
        funext i
        have : (i.succ.val < t' + 1) ↔ (i.val < t') := by
          show i.val + 1 < t' + 1 ↔ i.val < t'; omega
        simp [this]
      rw [hsub, ih t' (by omega) (fun i => a i.succ)]
      ring

theorem odd_cycle_adjuster_realizes_unit_interval {V : Type*} {G : SimpleGraph V} {r : ℕ}
    (N : AdjusterNecklace G r)
    (hodd : ∀ i : Fin r, (N.long i).length = (N.short i).length + 1)
    (t : ℕ) (ht : t ≤ r) :
    Nonempty (SimpleCycle G (N.base.length + (List.ofFn (fun i => (N.short i).length)).sum + t)) := by
  let choice : Fin r → Bool := fun i => decide (i.val < t)
  have hcyc := N.realize_simple_cycle (fun i => by rw [hodd i]; omega) choice
  have hlen : (N.realize choice).length =
      N.base.length + (List.ofFn (fun i => (N.short i).length)).sum + t := by
    rw [N.realize_length choice]
    have hseg : (fun i : Fin r => (N.seg choice i).length) =
        (fun i : Fin r => if decide (i.val < t) then (N.short i).length + 1 else (N.short i).length) := by
      funext i
      unfold AdjusterNecklace.seg choice
      split_ifs <;> simp [hodd]
    rw [hseg, sum_ofFn_prefix_jump r t 1 ht (fun i => (N.short i).length)]
    ring
  rw [hlen] at hcyc
  exact hcyc

private lemma exists_pow2_in_unit_interval (L : ℕ) (hL : 3 ≤ L) :
    ∃ k : ℕ, 2 ≤ k ∧ L ≤ 2 ^ k ∧ 2 ^ k ≤ 2 * L - 2 := by
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    by_cases h4 : L ≤ 4
    · exact ⟨2, le_rfl, h4, by omega⟩
    · have hhalf_ge : 3 ≤ (L + 1) / 2 := by omega
      have hhalf_lt : (L + 1) / 2 < L := by omega
      rcases ih ((L + 1) / 2) hhalf_lt hhalf_ge with ⟨k, hk, h1, h2⟩
      refine ⟨k + 1, by omega, ?_, ?_⟩
      · have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
        omega
      · have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
        omega

theorem odd_cycle_adjuster_necklace_closes_pow2 {V : Type*} {G : SimpleGraph V} {r : ℕ}
    (N : AdjusterNecklace G r)
    (hodd : ∀ i : Fin r, (N.long i).length = (N.short i).length + 1)
    (hr : N.base.length + (List.ofFn (fun i => (N.short i).length)).sum - 2 ≤ r) :
    HasPow2Cycle G := by
  let L := N.base.length + (List.ofFn (fun i => (N.short i).length)).sum
  rcases exists_pow2_in_unit_interval L N.h_min_len with ⟨k, hk, h1, h2⟩
  have ht : 2 ^ k - L ≤ r := by omega
  have hcyc := odd_cycle_adjuster_realizes_unit_interval N hodd (2 ^ k - L) ht
  have heq : L + (2 ^ k - L) = 2 ^ k := by omega
  change Nonempty (SimpleCycle G (L + (2 ^ k - L))) at hcyc
  rw [heq] at hcyc
  exact ⟨2 ^ k, ⟨k, hk, rfl⟩, hcyc⟩

theorem even_cycle_adjuster_realizes_even_interval {V : Type*} {G : SimpleGraph V} {r : ℕ}
    (N : AdjusterNecklace G r)
    (heven : ∀ i : Fin r, (N.long i).length = (N.short i).length + 2)
    (t : ℕ) (ht : t ≤ r) :
    Nonempty (SimpleCycle G (N.base.length + (List.ofFn (fun i => (N.short i).length)).sum + 2 * t)) := by
  let choice : Fin r → Bool := fun i => decide (i.val < t)
  have hcyc := N.realize_simple_cycle (fun i => by rw [heven i]; omega) choice
  have hlen : (N.realize choice).length =
      N.base.length + (List.ofFn (fun i => (N.short i).length)).sum + 2 * t := by
    rw [N.realize_length choice]
    have hseg : (fun i : Fin r => (N.seg choice i).length) =
        (fun i : Fin r => if decide (i.val < t) then (N.short i).length + 2 else (N.short i).length) := by
      funext i
      unfold AdjusterNecklace.seg choice
      split_ifs <;> simp [heven]
    rw [hseg, sum_ofFn_prefix_jump r t 2 ht (fun i => (N.short i).length)]
    ring
  rw [hlen] at hcyc
  exact hcyc

theorem even_cycle_adjuster_necklace_closes_pow2 {V : Type*} {G : SimpleGraph V} {r a : ℕ}
    (N : AdjusterNecklace G r)
    (hL : N.base.length + (List.ofFn (fun i => (N.short i).length)).sum = 2 * a)
    (heven : ∀ i : Fin r, (N.long i).length = (N.short i).length + 2)
    (hr : a - 2 ≤ r) :
    HasPow2Cycle G := by
  have ha : 2 ≤ a := by have := N.h_min_len; omega
  by_cases ha2 : a = 2
  · have hcyc := even_cycle_adjuster_realizes_even_interval N heven 0 (Nat.zero_le r)
    rw [hL, ha2] at hcyc
    exact ⟨4, isPow2Len_four, hcyc⟩
  · have ha3 : 3 ≤ a := by omega
    rcases exists_pow2_in_unit_interval a ha3 with ⟨k, hk, h1, h2⟩
    have ht : 2 ^ k - a ≤ r := by omega
    have hcyc := even_cycle_adjuster_realizes_even_interval N heven (2 ^ k - a) ht
    rw [hL] at hcyc
    have heq : 2 * a + 2 * (2 ^ k - a) = 2 ^ (k + 1) := by
      have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      omega
    rw [heq] at hcyc
    exact ⟨2 ^ (k + 1), ⟨k + 1, by omega, rfl⟩, hcyc⟩

end E64Wave7Agent8
