import Std

namespace Hadamard2396

def sumAt (n : Nat) (f : Nat → Int) : Int := ((List.range n).map f).sum

theorem sumAt_succ (n : Nat) (f : Nat → Int) :
    sumAt (n + 1) f = sumAt n f + f n := by
  simp [sumAt, List.range_succ]

theorem sumAt_split (n m : Nat) (f : Nat → Int) :
    sumAt (n + m) f = sumAt n f + sumAt m (fun i => f (n+i)) := by
  simp [sumAt, List.range_add, List.map_map, Function.comp_def]

theorem sumAt_add (n : Nat) (f g : Nat → Int) :
    sumAt n (fun i => f i + g i) = sumAt n f + sumAt n g := by
  induction n with
  | zero => simp [sumAt]
  | succ n ih => simp only [sumAt_succ, ih]; omega

theorem sumAt_congr (n : Nat) {f g : Nat → Int}
    (h : ∀ i, i < n → f i = g i) : sumAt n f = sumAt n g := by
  induction n with
  | zero => simp [sumAt]
  | succ n ih =>
    rw [sumAt_succ, sumAt_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem sumAt_le (n : Nat) {f g : Nat → Int}
    (h : ∀ i, i < n → f i ≤ g i) : sumAt n f ≤ sumAt n g := by
  induction n with
  | zero => simp [sumAt]
  | succ n ih =>
    have h₁ := ih (fun i hi => h i (by omega))
    have h₂ := h n (by omega)
    simp only [sumAt_succ]
    omega

def sign (x : Bool) : Int := if x then -1 else 1
def mono (x y z : Bool) : Int := if x = y ∧ y = z then 1 else 0
def count (d : Nat) (a : Nat → Bool) : Int :=
  sumAt d fun i => mono (a i) (a (d+i)) (a (d+d+i))

def paf (n : Nat) (a : Nat → Bool) (s : Nat) : Int :=
  sumAt n fun i => sign (a i) * sign (a ((i+s)%n))

theorem localTriple (x y z : Bool) :
    sign x * sign y + sign y * sign z + sign z * sign x = 4 * mono x y z - 1 := by
  cases x <;> cases y <;> cases z <;> decide

theorem sumAt_four_sub_one (n : Nat) (f : Nat → Int) :
    sumAt n (fun i => 4 * f i - 1) = 4 * sumAt n f - (n : Int) := by
  induction n with
  | zero => simp [sumAt]
  | succ n ih => simp only [sumAt_succ, ih, Int.natCast_succ]; omega

/-- The ordinary cyclic autocorrelation at the order-three shift counts constant fibres. -/
theorem paf_triples (d : Nat) (a : Nat → Bool) :
    paf (d+d+d) a d = 4 * count d a - (d : Int) := by
  unfold paf count
  rw [sumAt_split (d+d) d, sumAt_split d d, ← sumAt_add, ← sumAt_add, ← sumAt_four_sub_one]
  apply sumAt_congr
  intro i hi
  have h₁ : (i+d)%(d+d+d) = d+i := by
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have h₂ : (d+i+d)%(d+d+d) = d+d+i := by
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have h₃ : (d+d+i+d)%(d+d+d) = i := by
    rw [show d+d+i+d = i+(d+d+d) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  simp only [h₁, h₂, h₃]
  exact localTriple _ _ _

theorem count_nonneg (d : Nat) (a : Nat → Bool) : 0 ≤ count d a := by
  have hz : sumAt d (fun _ => 0) = 0 := by
    induction d with
    | zero => rfl
    | succ n ih => simp [sumAt_succ, ih]
  rw [← hz]
  apply sumAt_le
  intro i _
  simp only [mono]; split <;> decide

/-- Every pair meeting the genuine shift 399 has 199 constant triples in total. -/
theorem count_1197 (a b : Nat → Bool) (h : paf 1197 a 399 + paf 1197 b 399 = -2) :
    count 399 a + count 399 b = 199 := by
  have h₁ := paf_triples 399 a
  have h₂ := paf_triples 399 b
  change paf 1197 a 399 = 4 * count 399 a - 399 at h₁
  change paf 1197 b 399 = 4 * count 399 b - 399 at h₂
  omega

def fixedBy400 (a : Nat → Bool) : Prop := ∀ i, i < 1197 → a ((400*i)%1197) = a i

private theorem orbitTable : ∀ i : Fin 399, i.val % 3 ≠ 0 →
    ((400*i.val)%1197 = 399+i.val ∧ (400*(399+i.val))%1197 = 798+i.val) ∨
    ((400*i.val)%1197 = 798+i.val ∧ (400*(798+i.val))%1197 = 399+i.val) := by
  decide +kernel

theorem fixed_count (a : Nat → Bool) (h : fixedBy400 a) : 266 ≤ count 399 a := by
  have nh : sumAt 399 (fun i => if i % 3 = 0 then 0 else 1) = 266 := by decide +kernel
  rw [← nh]
  apply sumAt_le
  intro i hi
  by_cases he : i % 3 = 0
  · simp only [he, ite_true, mono]; split <;> decide
  · simp only [he, ite_false]
    have h₁ := h i (by omega)
    rcases orbitTable ⟨i, hi⟩ he with ⟨u,v⟩ | ⟨u,v⟩
    · have h₂ := h (399+i) (by omega)
      rw [u] at h₁
      rw [v] at h₂
      simp [mono, h₂, h₁]
    · have h₂ := h (798+i) (by omega)
      rw [u] at h₁
      rw [v] at h₂
      simp [mono, h₂, h₁]

theorem cannot_fix_either_word (a b : Nat → Bool)
    (h : paf 1197 a 399 + paf 1197 b 399 = -2) : ¬fixedBy400 a ∧ ¬fixedBy400 b := by
  have ht := count_1197 a b h
  have ha := count_nonneg 399 a
  have hb := count_nonneg 399 b
  constructor
  · intro fixed
    have := fixed_count a fixed
    omega
  · intro fixed
    have := fixed_count b fixed
    omega

#print axioms paf_triples
#print axioms cannot_fix_either_word

end Hadamard2396
