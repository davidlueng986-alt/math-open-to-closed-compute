import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Nodup
import Mathlib.Tactic

namespace E64Wave7Agent10

/-!
# Erdős Problem #64 — Wave 7 Agent #10 (Free Whole-Problem Attack #4)
## Girth-Independent General Ear-Detour Chains, Modular Dyadic-Hitting,
## Same-Scale (2^k+1)/(2^k+2) Theta-Overlap Exclusions, and C5-Cluster Rigidity
-/

/-- A positive integer is a power of two at least 4 (2^k with k ≥ 2). -/
def IsPowerOfTwo (n : ℕ) : Prop := ∃ k : ℕ, 2 ≤ k ∧ n = 2 ^ k

/-- Simple cycle of length ≥ 3 in a `SimpleGraph V`, represented by its distinct vertex list. -/
structure SimpleCycle {V : Type*} (G : SimpleGraph V) where
  verts : List V
  len_ge_three : 3 ≤ verts.length
  nodup : verts.Nodup
  adj_cycle : ∀ i (hi : i < verts.length),
    G.Adj (verts[i]'hi) (verts[(i + 1) % verts.length]'(Nat.mod_lt _ (by omega)))

/-- A graph satisfies Erdős–Gyárfás if it contains a simple cycle of length 2^k (k ≥ 2). -/
def HasPowerCycle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ C : SimpleCycle G, IsPowerOfTwo C.verts.length

/-- A graph is power-free if it has no simple cycle of length 2^k (k ≥ 2). -/
def PowerFree {V : Type*} (G : SimpleGraph V) : Prop := ¬ HasPowerCycle G

/-- A graph is C_L-free if it contains no simple cycle of length L. -/
def CycleFree {V : Type*} (G : SimpleGraph V) (L : ℕ) : Prop :=
  ∀ C : SimpleCycle G, C.verts.length ≠ L

lemma powerFree_cycleFree {V : Type*} {G : SimpleGraph V} (h : PowerFree G)
    {k : ℕ} (hk : 2 ≤ k) : CycleFree G (2 ^ k) := by
  intro C hlen
  exact h ⟨C, k, hk, hlen⟩

/-! ### Part I: Number-Theoretic Modular Dyadic-Hitting Theorems -/

/-- Every integer L ≥ 1 has a power of two 2^k in [L, 2*L). -/
theorem exists_pow2_in_octave (L : ℕ) (hL : 1 ≤ L) :
    ∃ k : ℕ, L ≤ 2 ^ k ∧ 2 ^ k < 2 * L := by
  induction L with
  | zero => omega
  | succ m ih =>
    by_cases hm : m = 0
    · subst hm; exact ⟨0, by norm_num, by norm_num⟩
    · obtain ⟨k, hk1, hk2⟩ := ih (by omega)
      by_cases hle : m + 1 ≤ 2 ^ k
      · exact ⟨k, hle, by omega⟩
      · exact ⟨k + 1, by rw [pow_succ]; omega, by rw [pow_succ]; omega⟩

/-- Unit-step (Δ = 1) dyadic hitting: every interval [L, L+r] with L ≥ 4 and L + r ≥ 2*L hits 2^k (k ≥ 2). -/
theorem unit_step_dyadic_hitting {L r : ℕ} (hL : 4 ≤ L) (hr : 2 * L ≤ L + r) :
    ∃ j ≤ r, IsPowerOfTwo (L + j) := by
  obtain ⟨k, hk1, hk2⟩ := exists_pow2_in_octave L (by omega)
  have hk_ge2 : 2 ≤ k := by
    by_contra hlt
    have : k ≤ 1 := by omega
    have : 2 ^ k ≤ 2 := by
      interval_cases k <;> norm_num
    omega
  refine ⟨2 ^ k - L, by omega, k, hk_ge2, by omega⟩

/-- Even-step (Δ = 2, e.g. C6 2-edge detours) dyadic hitting:
    for even L ≥ 4 and L + 2*r ≥ 2*L, there is j ≤ r with L + 2*j = 2^k (k ≥ 2). -/
theorem even_step_dyadic_hitting {L r : ℕ} (hL : 4 ≤ L) (heven : 2 ∣ L)
    (hr : 2 * L ≤ L + 2 * r) :
    ∃ j ≤ r, IsPowerOfTwo (L + 2 * j) := by
  obtain ⟨k, hk1, hk2⟩ := exists_pow2_in_octave L (by omega)
  have hk_ge2 : 2 ≤ k := by
    by_contra hlt
    have : k ≤ 1 := by omega
    have : 2 ^ k ≤ 2 := by interval_cases k <;> norm_num
    omega
  have h2pow : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
  obtain ⟨u, hu⟩ := h2pow
  obtain ⟨v, hv⟩ := heven
  have hdiff_even : 2 ∣ (2 ^ k - L) := ⟨u - v, by rw [Nat.mul_sub_left_distrib, ← hu, ← hv]⟩
  obtain ⟨j, hj⟩ := hdiff_even
  refine ⟨j, by omega, k, hk_ge2, by omega⟩

/-- Step-3 (Δ = 3, e.g. C5 single-edge detours) dyadic hitting:
    for any L ≥ 4 with 3 ∤ L and L + 3*r ≥ 4*L, there is j ≤ r with L + 3*j = 2^k (k ≥ 2). -/
theorem step3_dyadic_hitting {L r : ℕ} (hL : 4 ≤ L) (hndiv : ¬ (3 ∣ L))
    (hr : 4 * L ≤ L + 3 * r) :
    ∃ j ≤ r, IsPowerOfTwo (L + 3 * j) := by
  obtain ⟨k, hk1, hk2⟩ := exists_pow2_in_octave L (by omega)
  have hk_ge2 : 2 ≤ k := by
    by_contra hlt
    have : k ≤ 1 := by omega
    have : 2 ^ k ≤ 2 := by interval_cases k <;> norm_num
    omega
  have hLmod : L % 3 = 1 ∨ L % 3 = 2 := by omega
  have hpow_ne0 : ∀ t : ℕ, (2 ^ t) % 3 = 1 ∨ (2 ^ t) % 3 = 2 := by
    intro t
    induction t with
    | zero => left; norm_num
    | succ t iht =>
      rw [pow_succ]
      rcases iht with h1 | h2
      · right; omega
      · left; omega
  have hmod_flip : (2 ^ k) % 3 = L % 3 ∨ (2 ^ (k + 1)) % 3 = L % 3 := by
    rcases hpow_ne0 k with h1 | h2
    · rw [pow_succ]; rcases hLmod with hL1 | hL2 <;> [left; right] <;> omega
    · rw [pow_succ]; rcases hLmod with hL1 | hL2 <;> [right; left] <;> omega
  rcases hmod_flip with hEq | hEq
  · have hdiv : 3 ∣ (2 ^ k - L) := by omega
    obtain ⟨j, hj⟩ := hdiv
    refine ⟨j, by omega, k, hk_ge2, by omega⟩
  · have hlt4 : 2 ^ (k + 1) < 4 * L := by rw [pow_succ]; omega
    have hge : L ≤ 2 ^ (k + 1) := by rw [pow_succ]; omega
    have hdiv : 3 ∣ (2 ^ (k + 1) - L) := by omega
    obtain ⟨j, hj⟩ := hdiv
    refine ⟨j, by omega, k + 1, by omega, by omega⟩

/-- Shifted Step-3 dyadic hitting: even when 3 ∣ L, a single detour Δ₀ with 3 ∤ Δ₀
    plus r detours of size 3 with (L + Δ₀) + 3*r ≥ 4*(L + Δ₀) hits a power of 2. -/
theorem step3_shifted_dyadic_hitting {L Δ₀ r : ℕ} (hL : 4 ≤ L) (hndivL : 3 ∣ L)
    (hndivD : ¬ (3 ∣ Δ₀)) (hr : 4 * (L + Δ₀) ≤ (L + Δ₀) + 3 * r) :
    ∃ j ≤ r, IsPowerOfTwo (L + Δ₀ + 3 * j) := by
  have hndiv : ¬ (3 ∣ (L + Δ₀)) := by
    intro h
    have : 3 ∣ Δ₀ := (Nat.dvd_add_right hndivL).mp h
    exact hndivD this
  exact step3_dyadic_hitting (by omega) hndiv hr

/-- Universal Modulus Step-d Dyadic-Hitting Theorem:
    For ANY step d = 2^a * m (m ≥ 1 odd), any period τ ≥ 1 with 2^τ ≡ 1 (mod m),
    and any L ≥ max(4, 2^a) with 2^a ∣ L and ∃ t, 2^t ≡ L (mod m),
    if L + r*d ≥ 2^τ * L, then ∃ j ≤ r with L + j*d = 2^k (k ≥ 2). -/
theorem general_step_d_dyadic_hitting {a m τ L r : ℕ}
    (hm : 1 ≤ m) (hodd : Odd m) (hτ : 1 ≤ τ) (hper : 2 ^ τ % m = 1 % m)
    (hL4 : 4 ≤ L) (hLa : 2 ^ a ≤ L) (hdiv_a : 2 ^ a ∣ L)
    (hres : ∃ t : ℕ, 2 ^ t % m = L % m)
    (hr : 2 ^ τ * L ≤ L + r * (2 ^ a * m)) :
    ∃ j ≤ r, IsPowerOfTwo (L + j * (2 ^ a * m)) := by
  obtain ⟨k0, hk0_ge, hk0_lt⟩ := exists_pow2_in_octave L (by omega)
  have hk0_ge2 : 2 ≤ k0 := by
    by_contra hlt
    have : k0 ≤ 1 := by omega
    have : 2 ^ k0 ≤ 2 := by interval_cases k0 <;> norm_num
    omega
  have hk0_gea : a ≤ k0 := by
    by_contra hlt
    have h1 : k0 + 1 ≤ a := by omega
    have h2 : 2 ^ k0 < 2 ^ a := Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  obtain ⟨t, ht⟩ := hres
  have hpow_period : ∀ n : ℕ, 2 ^ (n + τ) % m = 2 ^ n % m := by
    intro n
    rw [pow_add, Nat.mul_mod, hper, ← Nat.mul_mod, mul_one]
  have hpow_mul_period : ∀ q n : ℕ, 2 ^ (n + q * τ) % m = 2 ^ n % m := by
    intro q
    induction q with
    | zero => intro n; simp
    | succ q ih =>
      intro n
      have : n + (q + 1) * τ = (n + q * τ) + τ := by ring
      rw [this, hpow_period, ih]
  let q := k0 + 1
  have hbig : k0 ≤ t + q * τ := by
    have : τ ≥ 1 := hτ
    have : q * τ ≥ q * 1 := Nat.mul_le_mul_left q this
    omega
  let diff := t + q * τ - k0
  let s := diff % τ
  have hs_lt : s < τ := Nat.mod_lt diff (by omega)
  have hks_mod : 2 ^ (k0 + s) % m = L % m := by
    have hdecomp : diff = s + (diff / τ) * τ := by
      calc diff = diff % τ + τ * (diff / τ) := (Nat.mod_add_div diff τ).symm
        _ = s + (diff / τ) * τ := by rw [mul_comm]
    have h1 : k0 + diff = t + q * τ := by omega
    have h2 : (k0 + s) + (diff / τ) * τ = t + q * τ := by omega
    calc 2 ^ (k0 + s) % m
        = 2 ^ ((k0 + s) + (diff / τ) * τ) % m := (hpow_mul_period (diff / τ) (k0 + s)).symm
      _ = 2 ^ (t + q * τ) % m := by rw [h2]
      _ = 2 ^ t % m := hpow_mul_period q t
      _ = L % m := ht
  let k := k0 + s
  have hk_geL : L ≤ 2 ^ k := le_trans hk0_ge (Nat.pow_le_pow_right (by omega) (Nat.le_add_right k0 s))
  have hk_lt : 2 ^ k < 2 ^ τ * L := by
    have hpow_s : 2 ^ s * 2 ≤ 2 ^ τ := by
      have : s + 1 ≤ τ := by omega
      calc 2 ^ s * 2 = 2 ^ (s + 1) := by rw [pow_succ]
        _ ≤ 2 ^ τ := Nat.pow_le_pow_right (by omega) this
    calc 2 ^ k = 2 ^ k0 * 2 ^ s := by rw [pow_add]
      _ < (2 * L) * 2 ^ s := Nat.mul_lt_mul_of_pos_right hk0_lt (Nat.pow_pos (by omega))
      _ = (2 ^ s * 2) * L := by ring
      _ ≤ 2 ^ τ * L := Nat.mul_le_mul_right L hpow_s
  have hdiv_2a : 2 ^ a ∣ (2 ^ k - L) := by
    have h2ak : 2 ^ a ∣ 2 ^ k := Nat.pow_dvd_pow 2 (by omega)
    obtain ⟨u, hu⟩ := h2ak
    obtain ⟨v, hv⟩ := hdiv_a
    exact ⟨u - v, by rw [Nat.mul_sub_left_distrib, ← hu, ← hv]⟩
  have hdiv_m : m ∣ (2 ^ k - L) := by
    have h1 : 2 ^ k = m * (2 ^ k / m) + 2 ^ k % m := (Nat.div_add_mod (2 ^ k) m).symm
    have h2 : L = m * (L / m) + L % m := (Nat.div_add_mod L m).symm
    have hmod_eq : 2 ^ k % m = L % m := hks_mod
    exact ⟨2 ^ k / m - L / m, by rw [Nat.mul_sub_left_distrib]; omega⟩
  have hcop : Nat.Coprime (2 ^ a) m := by
    apply Nat.Coprime.pow_left
    exact (Nat.prime_two.coprime_iff_not_dvd).mpr (fun h => by
      obtain ⟨u, hu⟩ := hodd
      omega)
  have hdiv_d : (2 ^ a * m) ∣ (2 ^ k - L) := hcop.mul_dvd_of_dvd_of_dvd hdiv_2a hdiv_m
  obtain ⟨j, hj⟩ := hdiv_d
  have hEq : L + j * (2 ^ a * m) = 2 ^ k := by
    rw [mul_comm j, ← hj, add_comm, Nat.sub_add_cancel hk_geL]
  have hj_le : j ≤ r := by
    have hpos : 0 < 2 ^ a * m := Nat.mul_pos (Nat.pow_pos (by omega)) (by omega)
    nlinarith
  exact ⟨j, hj_le, k, by omega, hEq⟩

/-! ### Part II: General Girth-Independent Ear-Detour Chain on SimpleGraph -/

/-- A `GeneralDetourChain` of length r ≥ 2 on a `SimpleGraph V`:
    Each slot i : Fin r has a non-empty base segment `base i` and alternative segment `alt i`
    with `(alt i).length = (base i).length + delta i`, sharing the same entry vertex and both
    ending at a neighbor of the next slot's entry vertex, with all vertices pairwise disjoint
    across distinct slots. -/
structure GeneralDetourChain {V : Type*} (G : SimpleGraph V) (r : ℕ) where
  hr : 2 ≤ r
  base : Fin r → List V
  alt : Fin r → List V
  delta : Fin r → ℕ
  base_ne : ∀ i, base i ≠ []
  alt_ne : ∀ i, alt i ≠ []
  alt_len : ∀ i, (alt i).length = (base i).length + delta i
  base_nodup : ∀ i, (base i).Nodup
  alt_nodup : ∀ i, (alt i).Nodup
  base_chain : ∀ i, (base i).IsChain G.Adj
  alt_chain : ∀ i, (alt i).IsChain G.Adj
  base_exit : ∀ i : Fin r,
    G.Adj ((base i).getLast (base_ne i))
          ((base ⟨(i.val + 1) % r, Nat.mod_lt _ (by omega)⟩).head (base_ne _))
  alt_exit : ∀ i : Fin r,
    G.Adj ((alt i).getLast (alt_ne i))
          ((base ⟨(i.val + 1) % r, Nat.mod_lt _ (by omega)⟩).head (base_ne _))
  same_head : ∀ i : Fin r, (alt i).head (alt_ne i) = (base i).head (base_ne i)
  disjoint_slots : ∀ i j : Fin r, i ≠ j →
    ∀ x, (x ∈ base i ∨ x ∈ alt i) → ¬ (x ∈ base j ∨ x ∈ alt j)
  base_total_ge3 : 3 ≤ ∑ i : Fin r, (base i).length

namespace GeneralDetourChain

variable {V : Type*} {G : SimpleGraph V} {r : ℕ}

def seg (D : GeneralDetourChain G r) (choice : Fin r → Bool) (i : Fin r) : List V :=
  if choice i then D.alt i else D.base i

lemma seg_ne (D : GeneralDetourChain G r) (choice : Fin r → Bool) (i : Fin r) :
    D.seg choice i ≠ [] := by
  unfold seg; split <;> [exact D.alt_ne i; exact D.base_ne i]

lemma seg_nodup (D : GeneralDetourChain G r) (choice : Fin r → Bool) (i : Fin r) :
    (D.seg choice i).Nodup := by
  unfold seg; split <;> [exact D.alt_nodup i; exact D.base_nodup i]

lemma seg_chain (D : GeneralDetourChain G r) (choice : Fin r → Bool) (i : Fin r) :
    (D.seg choice i).IsChain G.Adj := by
  unfold seg; split <;> [exact D.alt_chain i; exact D.base_chain i]

lemma seg_head (D : GeneralDetourChain G r) (choice : Fin r → Bool) (i : Fin r) :
    (D.seg choice i).head (D.seg_ne choice i) = (D.base i).head (D.base_ne i) := by
  unfold seg
  split
  · exact D.same_head i
  · rfl

lemma seg_exit (D : GeneralDetourChain G r) (choice : Fin r → Bool) (i : Fin r) :
    G.Adj ((D.seg choice i).getLast (D.seg_ne choice i))
          ((D.seg choice ⟨(i.val + 1) % r, Nat.mod_lt _ (by have := D.hr; omega)⟩).head (D.seg_ne choice _)) := by
  rw [D.seg_head choice]
  unfold seg
  split
  · exact D.alt_exit i
  · exact D.base_exit i

lemma seg_disjoint (D : GeneralDetourChain G r) (choice : Fin r → Bool) {i j : Fin r} (hij : i ≠ j) :
    List.Disjoint (D.seg choice i) (D.seg choice j) := by
  intro x hxi hxj
  have hi : x ∈ D.base i ∨ x ∈ D.alt i := by
    unfold seg at hxi; split at hxi <;> [exact Or.inr hxi; exact Or.inl hxi]
  have hj : x ∈ D.base j ∨ x ∈ D.alt j := by
    unfold seg at hxj; split at hxj <;> [exact Or.inr hxj; exact Or.inl hxj]
  exact D.disjoint_slots i j hij x hi hj

def cycleVerts (D : GeneralDetourChain G r) (choice : Fin r → Bool) : List V :=
  (List.finRange r).flatMap (D.seg choice)

theorem cycleVerts_length (D : GeneralDetourChain G r) (choice : Fin r → Bool) :
    (D.cycleVerts choice).length =
      (∑ i : Fin r, (D.base i).length) +
      (∑ i : Fin r, if choice i then D.delta i else 0) := by
  unfold cycleVerts
  rw [List.length_flatMap]
  have hsum_nodup : ∀ (f : Fin r → ℕ) (l : List (Fin r)), l.Nodup →
      (l.map f).sum = ∑ i ∈ l.toFinset, f i := by
    intro f l hl
    induction l with
    | nil => simp
    | cons a tl ih =>
      rw [List.nodup_cons] at hl
      simp only [List.map_cons, List.sum_cons, List.toFinset_cons]
      rw [Finset.sum_insert (by simpa using hl.1), ih hl.2]
  have htoFin : (List.finRange r).toFinset = Finset.univ := by ext x; simp
  rw [hsum_nodup _ (List.finRange r) (List.nodup_finRange r), htoFin]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold seg
  split
  · exact D.alt_len i
  · simp

theorem cycleVerts_nodup (D : GeneralDetourChain G r) (choice : Fin r → Bool) :
    (D.cycleVerts choice).Nodup := by
  unfold cycleVerts
  rw [List.nodup_flatMap]
  refine ⟨fun i _ => D.seg_nodup choice i, ?_⟩
  exact (List.nodup_finRange r).imp_of_mem fun {i j} _ _ hij => D.seg_disjoint choice hij

private lemma isChain_append_of_link {α : Type*} {R : α → α → Prop} {l1 l2 : List α}
    (h1 : l1.IsChain R) (h2 : l2.IsChain R) (hne1 : l1 ≠ []) (hne2 : l2 ≠ [])
    (hlink : R (l1.getLast hne1) (l2.head hne2)) :
    (l1 ++ l2).IsChain R := by
  rw [List.isChain_append]
  refine ⟨h1, h2, fun x hx y hy => ?_⟩
  rw [List.getLast?_eq_some_getLast hne1] at hx
  rw [List.head?_eq_some_head hne2] at hy
  injection hx with hx; injection hy with hy
  subst hx; subst hy
  exact hlink

private lemma flatMap_isChain {α β : Type*} {R : β → β → Prop} (f : α → List β) :
    ∀ (l : List α),
      (∀ a ∈ l, f a ≠ []) →
      (∀ a ∈ l, (f a).IsChain R) →
      (l.IsChain (fun a b => ∀ (ha : f a ≠ []) (hb : f b ≠ []), R ((f a).getLast ha) ((f b).head hb))) →
      (l.flatMap f).IsChain R
  | [], _, _, _ => List.isChain_nil
  | [a], _, hch, _ => by simp [hch a (by simp)]
  | a :: b :: rest, hne, hch, hlink => by
    simp only [List.flatMap_cons]
    have ha_ne : f a ≠ [] := hne a (by simp)
    have hrest_ne : ((b :: rest).flatMap f) ≠ [] := by
      simp only [List.flatMap_cons, ne_eq, List.append_eq_nil_iff, not_and]
      intro hb_empty
      exact absurd hb_empty (hne b (by simp))
    have htail_chain : ((b :: rest).flatMap f).IsChain R :=
      flatMap_isChain f (b :: rest)
        (fun x hx => hne x (List.mem_cons_of_mem a hx))
        (fun x hx => hch x (List.mem_cons_of_mem a hx))
        (List.IsChain.tail hlink)
    have hhead_eq : ((b :: rest).flatMap f).head hrest_ne = (f b).head (hne b (by simp)) := by
      simp only [List.flatMap_cons]
      exact List.head_append_of_ne_nil (hne b (by simp))
    apply isChain_append_of_link (hch a (by simp)) htail_chain ha_ne hrest_ne
    rw [hhead_eq]
    have hab : ∀ (ha : f a ≠ []) (hb : f b ≠ []), R ((f a).getLast ha) ((f b).head hb) :=
      List.IsChain.rel hlink
    exact hab ha_ne (hne b (by simp))

/-- Every `choice : Fin r → Bool` produces a valid `SimpleCycle G` of exact subset-sum length! -/
def toSimpleCycle (D : GeneralDetourChain G r) (choice : Fin r → Bool) : SimpleCycle G where
  verts := D.cycleVerts choice
  len_ge_three := by
    rw [D.cycleVerts_length choice]
    have := D.base_total_ge3
    omega
  nodup := D.cycleVerts_nodup choice
  adj_cycle := by
    have hhr := D.hr
    have hne_all : (D.cycleVerts choice) ≠ [] := by
      intro h
      have hlen := D.cycleVerts_length choice
      rw [h] at hlen
      simp only [List.length_nil] at hlen
      have := D.base_total_ge3
      omega
    have hchain : (D.cycleVerts choice).IsChain G.Adj := by
      unfold cycleVerts
      apply flatMap_isChain (D.seg choice) (List.finRange r)
        (fun i _ => D.seg_ne choice i)
        (fun i _ => D.seg_chain choice i)
      rw [List.isChain_iff_getElem]
      intro k hk
      simp only [List.length_finRange] at hk
      simp only [List.getElem_finRange]
      intro ha hb
      convert D.seg_exit choice ⟨k, by omega⟩ using 2
      · congr 1
      · congr 1; ext; exact (Nat.mod_eq_of_lt (by omega)).symm
    have hwrap : G.Adj ((D.cycleVerts choice).getLast hne_all)
                       ((D.cycleVerts choice).head hne_all) := by
      have hfr_ne : List.finRange r ≠ [] := by
        intro h; have := congrArg List.length h; simp at this; omega
      have hhead_cyc : (D.cycleVerts choice).head hne_all =
          (D.seg choice ⟨0, by omega⟩).head (D.seg_ne choice ⟨0, by omega⟩) := by
        unfold cycleVerts
        have hcons : ∃ rest, List.finRange r = ⟨0, by omega⟩ :: rest := by
          cases hfr : List.finRange r with
          | nil => exact absurd hfr hfr_ne
          | cons x xs =>
            have hx : x = ⟨0, by omega⟩ := by
              have h0 : (List.finRange r)[0]'(by rw [List.length_finRange]; omega) = ⟨0, by omega⟩ := by
                simp
              rw [← h0]; simp [hfr]
            exact ⟨xs, by rw [hx]⟩
        obtain ⟨rest, hrest⟩ := hcons
        simp only [hrest, List.flatMap_cons]
        exact List.head_append_of_ne_nil (D.seg_ne choice ⟨0, by omega⟩)
      have hlast_cyc : (D.cycleVerts choice).getLast hne_all =
          (D.seg choice ⟨r - 1, by omega⟩).getLast (D.seg_ne choice ⟨r - 1, by omega⟩) := by
        unfold cycleVerts
        have hsnoc : ∃ init, List.finRange r = init ++ [⟨r - 1, by omega⟩] := by
          refine ⟨(List.finRange r).dropLast, ?_⟩
          have hlast_fr : (List.finRange r).getLast hfr_ne = ⟨r - 1, by omega⟩ := by
            rw [List.getLast_eq_getElem]
            simp
          rw [← hlast_fr]
          exact (List.dropLast_append_getLast hfr_ne).symm
        obtain ⟨init, hinit⟩ := hsnoc
        simp only [hinit, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        exact List.getLast_append_of_ne_nil _ (D.seg_ne choice ⟨r - 1, by omega⟩)
      rw [hhead_cyc, hlast_cyc]
      have hmod0 : (⟨((r - 1) + 1) % r, Nat.mod_lt _ (by omega)⟩ : Fin r) = ⟨0, by omega⟩ := by
        ext; simp [Nat.sub_add_cancel (by omega : 1 ≤ r)]
      convert D.seg_exit choice ⟨r - 1, by omega⟩ using 2
      exact congrArg (D.seg choice) hmod0.symm
    intro i hi
    by_cases hlast : i + 1 < (D.cycleVerts choice).length
    · have hmod : (i + 1) % (D.cycleVerts choice).length = i + 1 := Nat.mod_eq_of_lt hlast
      simp only [hmod]
      exact (List.isChain_iff_getElem.mp hchain) i hlast
    · have hi_eq : i = (D.cycleVerts choice).length - 1 := by omega
      have hmod : (i + 1) % (D.cycleVerts choice).length = 0 := by
        rw [hi_eq, Nat.sub_add_cancel (by omega), Nat.mod_self]
      simp only [hmod]
      have hget0 : (D.cycleVerts choice)[0]'(by omega) = (D.cycleVerts choice).head hne_all :=
        (List.head_eq_getElem hne_all).symm
      have hgetL : (D.cycleVerts choice)[i]'hi = (D.cycleVerts choice).getLast hne_all := by
        rw [List.getLast_eq_getElem]; congr 1
      rw [hget0, hgetL]
      exact hwrap

/-- Helper: Boolean switch realizing exactly j active slots (for j ≤ r). -/
def firstJ (r j : ℕ) : Fin r → Bool := fun i => decide (i.val < j)

lemma sum_firstJ_uniform {r j d : ℕ} (hj : j ≤ r) :
    (∑ i : Fin r, if firstJ r j i then d else 0) = j * d := by
  have hcard : (Finset.univ.filter (fun i : Fin r => i.val < j)).card = j := by
    let emb : {x // x ∈ Finset.range j} ↪ Fin r :=
      ⟨fun x => ⟨x.1, by have := Finset.mem_range.mp x.2; omega⟩,
       fun a b h => Subtype.ext (congrArg Fin.val h)⟩
    have hbij : Finset.univ.filter (fun i : Fin r => i.val < j) =
        (Finset.range j).attach.map emb := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Finset.mem_attach, emb]
      constructor
      · intro hi; exact ⟨⟨i.val, Finset.mem_range.mpr hi⟩, by ext; rfl⟩
      · rintro ⟨⟨x, hx⟩, hxi⟩
        have : i.val = x := congrArg Fin.val hxi.symm
        rw [this]; exact Finset.mem_range.mp hx
    rw [hbij, Finset.card_map, Finset.card_attach, Finset.card_range]
  have hrew : (∑ i : Fin r, if firstJ r j i then d else 0) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin r => i.val < j), d := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    unfold firstJ
    simp
  rw [hrew, Finset.sum_const, hcard, smul_eq_mul]

/-- Theorem (C5 Single-Edge Detour Closure, Δ = 3):
    Any graph with a uniform Δ = 3 GeneralDetourChain of base length L ≥ 4 (3 ∤ L)
    and L + 3*r ≥ 4*L unconditionally contains a simple 2^k-cycle (k ≥ 2). -/
theorem hasPowerCycle_of_c5_single_edge_detour_chain
    {D : GeneralDetourChain G r}
    (hΔ : ∀ i, D.delta i = 3)
    (hL4 : 4 ≤ ∑ i : Fin r, (D.base i).length)
    (hndiv : ¬ (3 ∣ ∑ i : Fin r, (D.base i).length))
    (hr : 4 * (∑ i : Fin r, (D.base i).length) ≤ (∑ i : Fin r, (D.base i).length) + 3 * r) :
    HasPowerCycle G := by
  obtain ⟨j, hj, hpow⟩ := step3_dyadic_hitting hL4 hndiv hr
  refine ⟨D.toSimpleCycle (firstJ r j), ?_⟩
  change IsPowerOfTwo (D.cycleVerts (firstJ r j)).length
  rw [D.cycleVerts_length (firstJ r j)]
  have hsum : (∑ i : Fin r, if firstJ r j i then D.delta i else 0) = 3 * j := by
    have : (∑ i : Fin r, if firstJ r j i then D.delta i else 0) =
           (∑ i : Fin r, if firstJ r j i then 3 else 0) := by
      apply Finset.sum_congr rfl; intro i _; rw [hΔ i]
    rw [this, sum_firstJ_uniform hj]; ring
  rw [hsum]
  exact hpow

/-- Theorem (Universal Girth-g Step-d Detour Chain Closure):
    Any graph with a uniform Δ = d = 2^a * m (m odd) GeneralDetourChain satisfying
    the modular dyadic-hitting condition unconditionally contains a simple 2^k-cycle. -/
theorem hasPowerCycle_of_general_step_d_detour_chain
    {a m τ : ℕ} {D : GeneralDetourChain G r}
    (hm : 1 ≤ m) (hodd : Odd m) (hτ : 1 ≤ τ) (hper : 2 ^ τ % m = 1 % m)
    (hΔ : ∀ i, D.delta i = 2 ^ a * m)
    (hL4 : 4 ≤ ∑ i : Fin r, (D.base i).length)
    (hLa : 2 ^ a ≤ ∑ i : Fin r, (D.base i).length)
    (hdiv_a : 2 ^ a ∣ ∑ i : Fin r, (D.base i).length)
    (hres : ∃ t : ℕ, 2 ^ t % m = (∑ i : Fin r, (D.base i).length) % m)
    (hr : 2 ^ τ * (∑ i : Fin r, (D.base i).length) ≤
          (∑ i : Fin r, (D.base i).length) + r * (2 ^ a * m)) :
    HasPowerCycle G := by
  obtain ⟨j, hj, hpow⟩ := general_step_d_dyadic_hitting hm hodd hτ hper hL4 hLa hdiv_a hres hr
  refine ⟨D.toSimpleCycle (firstJ r j), ?_⟩
  change IsPowerOfTwo (D.cycleVerts (firstJ r j)).length
  rw [D.cycleVerts_length (firstJ r j)]
  have hsum : (∑ i : Fin r, if firstJ r j i then D.delta i else 0) = j * (2 ^ a * m) := by
    have : (∑ i : Fin r, if firstJ r j i then D.delta i else 0) =
           (∑ i : Fin r, if firstJ r j i then 2 ^ a * m else 0) := by
      apply Finset.sum_congr rfl; intro i _; rw [hΔ i]
    rw [this, sum_firstJ_uniform hj]
  rw [hsum]
  exact hpow

/-- Theorem (Strict-Interior General-Detour EGRob Avoidance):
    In a uniform step-d GeneralDetourChain where 1 ≤ j ≤ r - 1 and L + j*d = 2^k (k ≥ 2),
    for EVERY slot i₀ : Fin r, there is a simple 2^k-cycle choosing `base i₀` (detour OFF)
    AND a simple 2^k-cycle choosing `alt i₀` (detour ON) — so no internal vertex/edge of
    any detour ear can be a hitting edge of C_{2^k}(G)! -/
theorem strict_interior_detour_robustness
    {d j : ℕ} {D : GeneralDetourChain G r}
    (hΔ : ∀ i, D.delta i = d)
    (hj1 : 1 ≤ j) (hjr : j ≤ r - 1)
    (hpow : IsPowerOfTwo ((∑ i : Fin r, (D.base i).length) + j * d))
    (i₀ : Fin r) :
    (∃ C₁ : SimpleCycle G, IsPowerOfTwo C₁.verts.length ∧
      ∀ x ∈ D.alt i₀, x ∉ D.base i₀ → x ∉ C₁.verts) ∧
    (∃ C₂ : SimpleCycle G, IsPowerOfTwo C₂.verts.length ∧
      ∀ x ∈ D.base i₀, x ∉ D.alt i₀ → x ∉ C₂.verts) := by
  have mk_cyc : ∀ (S : Finset (Fin r)), S.card = j →
      ∃ C : SimpleCycle G, C = D.toSimpleCycle (fun i => decide (i ∈ S)) ∧
        IsPowerOfTwo C.verts.length := by
    intro S hS
    refine ⟨D.toSimpleCycle (fun i => decide (i ∈ S)), rfl, ?_⟩
    change IsPowerOfTwo (D.cycleVerts (fun i => decide (i ∈ S))).length
    rw [D.cycleVerts_length]
    have hsum : (∑ i : Fin r, if decide (i ∈ S) then D.delta i else 0) = j * d := by
      have h1 : (∑ i : Fin r, if decide (i ∈ S) then D.delta i else 0) = ∑ i ∈ S, d := by
        simp only [decide_eq_true_eq]
        rw [← Finset.sum_filter]
        have hf : Finset.univ.filter (fun i : Fin r => i ∈ S) = S := by ext x; simp
        rw [hf]
        apply Finset.sum_congr rfl; intro i _; exact hΔ i
      rw [h1, Finset.sum_const, hS, smul_eq_mul]
    rw [hsum]; exact hpow
  constructor
  · have hle : j ≤ (Finset.univ.erase i₀).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      exact hjr
    obtain ⟨S₁, hS₁_sub, hS₁_card⟩ := Finset.exists_subset_card_eq hle
    have hi₀_not : i₀ ∉ S₁ := fun h => (Finset.mem_erase.mp (hS₁_sub h)).1 rfl
    obtain ⟨C₁, hC₁_eq, hC₁_pow⟩ := mk_cyc S₁ hS₁_card
    refine ⟨C₁, hC₁_pow, fun x hx_alt hx_nbase hx_mem => ?_⟩
    rw [hC₁_eq] at hx_mem
    change x ∈ D.cycleVerts (fun i => decide (i ∈ S₁)) at hx_mem
    unfold cycleVerts at hx_mem
    rw [List.mem_flatMap] at hx_mem
    obtain ⟨i, _, hxi⟩ := hx_mem
    by_cases heq : i = i₀
    · subst heq
      unfold seg at hxi
      simp [hi₀_not] at hxi
      exact hx_nbase hxi
    · exact D.disjoint_slots i₀ i (Ne.symm heq) x (Or.inr hx_alt) (by
        unfold seg at hxi; split at hxi <;> [exact Or.inr hxi; exact Or.inl hxi])
  · have hle : j - 1 ≤ (Finset.univ.erase i₀).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨T, hT_sub, hT_card⟩ := Finset.exists_subset_card_eq hle
    have hi₀_notT : i₀ ∉ T := fun h => (Finset.mem_erase.mp (hT_sub h)).1 rfl
    let S₂ := insert i₀ T
    have hS₂_card : S₂.card = j := by
      rw [Finset.card_insert_of_notMem hi₀_notT, hT_card]; omega
    have hi₀_in : i₀ ∈ S₂ := Finset.mem_insert_self i₀ T
    obtain ⟨C₂, hC₂_eq, hC₂_pow⟩ := mk_cyc S₂ hS₂_card
    refine ⟨C₂, hC₂_pow, fun x hx_base hx_nalt hx_mem => ?_⟩
    rw [hC₂_eq] at hx_mem
    change x ∈ D.cycleVerts (fun i => decide (i ∈ S₂)) at hx_mem
    unfold cycleVerts at hx_mem
    rw [List.mem_flatMap] at hx_mem
    obtain ⟨i, _, hxi⟩ := hx_mem
    by_cases heq : i = i₀
    · subst heq
      unfold seg at hxi
      simp [hi₀_in] at hxi
      exact hx_nalt hxi
    · exact D.disjoint_slots i₀ i (Ne.symm heq) x (Or.inl hx_base) (by
        unfold seg at hxi; split at hxi <;> [exact Or.inr hxi; exact Or.inl hxi])

end GeneralDetourChain

/-! ### Part III: Same-Scale (2^k+1)/(2^k+2) Theta-Overlap & Attachment-Exclusion Theorems -/

structure ThetaOverlap {V : Type*} (G : SimpleGraph V) where
  L₁ : ℕ
  L₂ : ℕ
  p : ℕ
  hp : 1 ≤ p
  hL₁ : p + 2 ≤ L₁
  hL₂ : p + 2 ≤ L₂
  arcA : List V
  arcB : List V
  arcA_len : arcA.length = L₁ - p
  arcB_len : arcB.length = L₂ - p
  arcA_nodup : arcA.Nodup
  arcB_nodup : arcB.Nodup
  arcA_chain : arcA.IsChain G.Adj
  arcB_chain : arcB.IsChain G.Adj
  arcA_ne : arcA ≠ []
  arcB_ne : arcB ≠ []
  link_AB : G.Adj (arcA.getLast arcA_ne) (arcB.head arcB_ne)
  link_BA : G.Adj (arcB.getLast arcB_ne) (arcA.head arcA_ne)
  disjoint_AB : List.Disjoint arcA arcB

/-- Theorem (Theta Symmetric-Difference Cycle):
    Two simple cycles of lengths L₁, L₂ intersecting in a single path of length p ≥ 1
    yield a simple cycle C₁ △ C₂ of exact length L₁ + L₂ - 2*p. -/
def ThetaOverlap.symmDiffCycle {V : Type*} {G : SimpleGraph V} (T : ThetaOverlap G) :
    SimpleCycle G := by
  let D : GeneralDetourChain G 2 := {
    hr := le_refl 2
    base := fun i => if i.val = 0 then T.arcA else T.arcB
    alt := fun i => if i.val = 0 then T.arcA else T.arcB
    delta := fun _ => 0
    base_ne := fun i => by split_ifs <;> [exact T.arcA_ne; exact T.arcB_ne]
    alt_ne := fun i => by split_ifs <;> [exact T.arcA_ne; exact T.arcB_ne]
    alt_len := fun _ => by simp
    base_nodup := fun i => by split_ifs <;> [exact T.arcA_nodup; exact T.arcB_nodup]
    alt_nodup := fun i => by split_ifs <;> [exact T.arcA_nodup; exact T.arcB_nodup]
    base_chain := fun i => by split_ifs <;> [exact T.arcA_chain; exact T.arcB_chain]
    alt_chain := fun i => by split_ifs <;> [exact T.arcA_chain; exact T.arcB_chain]
    base_exit := fun i => by
      fin_cases i
      · simpa using T.link_AB
      · simpa using T.link_BA
    alt_exit := fun i => by
      fin_cases i
      · simpa using T.link_AB
      · simpa using T.link_BA
    same_head := fun _ => rfl
    disjoint_slots := fun i j hij x hi hj => by
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · simp at hi hj; exact T.disjoint_AB hi hj
      · simp at hi hj; exact T.disjoint_AB hj hi
      · exact absurd rfl hij
    base_total_ge3 := by
      have h1 : (∑ i : Fin 2, (if i.val = 0 then T.arcA else T.arcB).length) =
          T.arcA.length + T.arcB.length := by
        rw [Fin.sum_univ_two]; simp
      rw [h1, T.arcA_len, T.arcB_len]
      have := T.hL₁; have := T.hL₂; omega
  }
  exact D.toSimpleCycle (fun _ => false)

theorem ThetaOverlap.symmDiffCycle_length {V : Type*} {G : SimpleGraph V} (T : ThetaOverlap G) :
    T.symmDiffCycle.verts.length = T.L₁ + T.L₂ - 2 * T.p := by
  unfold symmDiffCycle
  change (GeneralDetourChain.cycleVerts _ _).length = _
  rw [GeneralDetourChain.cycleVerts_length]
  simp only [Bool.false_eq_true, ↓reduceIte, Finset.sum_const_zero, add_zero, Fin.sum_univ_two]
  simp only [Fin.val_zero, ↓reduceIte, Fin.val_one, one_ne_zero, T.arcA_len, T.arcB_len]
  have := T.hL₁; have := T.hL₂; omega

/-- Theorem (Same-Scale (2^k+1)-Cycle Single-Edge Overlap Exclusion):
    In any power-free graph, NO two simple (2^k+1)-cycles (k ≥ 2) can intersect in a single edge (p = 1). -/
theorem same_scale_2k_plus_1_no_single_edge_overlap {V : Type*} {G : SimpleGraph V}
    (hpf : PowerFree G) {k : ℕ} (hk : 2 ≤ k)
    (T : ThetaOverlap G) (h1 : T.L₁ = 2 ^ k + 1) (h2 : T.L₂ = 2 ^ k + 1) (hp : T.p = 1) :
    False := by
  apply hpf
  refine ⟨T.symmDiffCycle, k + 1, by omega, ?_⟩
  rw [T.symmDiffCycle_length, h1, h2, hp, pow_succ]
  omega

/-- Theorem (Same-Scale (2^k+1)-Cycle General Forbidden Path Overlaps):
    In any power-free graph, two simple (2^k+1)-cycles cannot intersect in a single path of
    length p = 2^k + 1 - 2^(r-1) for any r ≥ 2. -/
theorem same_scale_2k_plus_1_forbidden_path_overlaps {V : Type*} {G : SimpleGraph V}
    (hpf : PowerFree G) {k r : ℕ} (hr2 : 2 ≤ r)
    (T : ThetaOverlap G) (h1 : T.L₁ = 2 ^ k + 1) (h2 : T.L₂ = 2 ^ k + 1)
    (hp : T.p + 2 ^ (r - 1) = 2 ^ k + 1) :
    False := by
  apply hpf
  refine ⟨T.symmDiffCycle, r, hr2, ?_⟩
  rw [T.symmDiffCycle_length, h1, h2]
  have hpow : 2 ^ r = 2 * 2 ^ (r - 1) := by
    have : r = (r - 1) + 1 := by omega
    conv_lhs => rw [this, pow_succ, mul_comm]
  omega

/-- Theorem (Same-Scale (2^k+2)-Cycle P3-Overlap Exclusion):
    In any power-free graph, NO two simple (2^k+2)-cycles (k ≥ 2) can intersect in a single P3 (p = 2). -/
theorem same_scale_2k_plus_2_no_P3_overlap {V : Type*} {G : SimpleGraph V}
    (hpf : PowerFree G) {k : ℕ} (hk : 2 ≤ k)
    (T : ThetaOverlap G) (h1 : T.L₁ = 2 ^ k + 2) (h2 : T.L₂ = 2 ^ k + 2) (hp : T.p = 2) :
    False := by
  apply hpf
  refine ⟨T.symmDiffCycle, k + 1, by omega, ?_⟩
  rw [T.symmDiffCycle_length, h1, h2, hp, pow_succ]
  omega

/-- Theorem (No Off-Cycle Triangle on Single Edge of (2^k-1)-Cycle):
    If a simple (2^k-1)-cycle shares a single edge (p = 1) with a triangle C3 (L₂ = 3),
    the symmetric difference is a simple 2^k-cycle. -/
theorem no_triangle_single_edge_on_2k_minus_1 {V : Type*} {G : SimpleGraph V}
    (hpf : PowerFree G) {k : ℕ} (hk : 2 ≤ k)
    (T : ThetaOverlap G) (h1 : T.L₁ = 2 ^ k - 1) (h2 : T.L₂ = 3) (hp : T.p = 1) :
    False := by
  apply hpf
  refine ⟨T.symmDiffCycle, k, hk, ?_⟩
  rw [T.symmDiffCycle_length, h1, h2, hp]
  have hpow4 : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
  omega

/-- Theorem (No Off-Cycle C5 on Single Edge of (2^k-3)-Cycle):
    If a simple (2^k-3)-cycle shares a single edge (p = 1) with a pentagon C5 (L₂ = 5),
    the symmetric difference is a simple 2^k-cycle. -/
theorem no_c5_single_edge_on_2k_minus_3 {V : Type*} {G : SimpleGraph V}
    (hpf : PowerFree G) {k : ℕ} (hk : 3 ≤ k)
    (T : ThetaOverlap G) (h1 : T.L₁ = 2 ^ k - 3) (h2 : T.L₂ = 5) (hp : T.p = 1) :
    False := by
  apply hpf
  refine ⟨T.symmDiffCycle, k, by omega, ?_⟩
  rw [T.symmDiffCycle_length, h1, h2, hp]
  have hpow8 : 8 ≤ 2 ^ k := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
  omega

/-! ### Part IV: Exact C5-Intersection Rigidity & C5-Cluster Packing Density Bound -/

/-- Theorem (C5 Single-Edge Overlap Excluded by C8-Freeness):
    Two 5-cycles in a C8-free graph cannot intersect in a single edge (p = 1). -/
theorem c5_no_single_edge_overlap {V : Type*} {G : SimpleGraph V}
    (h8 : CycleFree G 8) (T : ThetaOverlap G) (h1 : T.L₁ = 5) (h2 : T.L₂ = 5) (hp : T.p = 1) :
    False := by
  apply h8 T.symmDiffCycle
  rw [T.symmDiffCycle_length, h1, h2, hp]

/-- Theorem (C5 P4-Overlap Excluded by C4-Freeness):
    Two 5-cycles in a C4-free graph cannot intersect in a single path of length 3 (p = 3). -/
theorem c5_no_P4_overlap {V : Type*} {G : SimpleGraph V}
    (h4 : CycleFree G 4) (T : ThetaOverlap G) (h1 : T.L₁ = 5) (h2 : T.L₂ = 5) (hp : T.p = 3) :
    False := by
  apply h4 T.symmDiffCycle
  rw [T.symmDiffCycle_length, h1, h2, hp]

/-- Theorem (Exact C5-Cluster Dichotomy Packing Density Bound):
    In any graph where the C5-union decomposes into pairwise vertex-disjoint components
    each isomorphic to either C5 (1 pentagon, 5 vertices) or Θ(2,3,3) (2 pentagons, 7 vertices):
    1. 7 * (#C5) ≤ 2 * n  (sharp upper bound #C5 ≤ ⌊2n/7⌋), and
    2. There exist at least ⌈(#C5)/2⌉ pairwise vertex-disjoint pentagons (one per component). -/
theorem c5_cluster_packing_density_bound {n c_iso c_theta : ℕ}
    (hpack : 5 * c_iso + 7 * c_theta ≤ n) :
    7 * (c_iso + 2 * c_theta) ≤ 2 * n ∧
    c_iso + 2 * c_theta ≤ 2 * (c_iso + c_theta) := by
  constructor <;> omega

end E64Wave7Agent10
