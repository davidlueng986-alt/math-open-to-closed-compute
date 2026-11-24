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

theorem twice_count (d : Nat) (a b : Nat → Bool)
    (h : paf (d+d+d) a d + paf (d+d+d) b d = -2) :
    2 * (count d a + count d b) = (d : Int) - 1 := by
  rw [paf_triples, paf_triples] at h
  omega

/-- Every pair meeting the genuine shift 399 has 199 constant triples in total. -/
theorem count_1197 (a b : Nat → Bool) (h : paf 1197 a 399 + paf 1197 b 399 = -2) :
    count 399 a + count 399 b = 199 := by
  have h₁ := paf_triples 399 a
  have h₂ := paf_triples 399 b
  change paf 1197 a 399 = 4 * count 399 a - 399 at h₁
  change paf 1197 b 399 = 4 * count 399 b - 399 at h₂
  omega

def FixedPrincipal (d : Nat) (a : Nat → Bool) : Prop :=
  ∀ i, i < 3*d → a (((1+d)*i)%(3*d)) = a i

private theorem principal_image (d i : Nat) :
    ((1+d)*i)%(3*d) = (i+d*(i%3))%(3*d) := by
  have hd : i%3 + 3*(i/3) = i := Nat.mod_add_div i 3
  have hmul : d*(3*(i/3)) = (3*d)*(i/3) := by ac_rfl
  have hprod : d*i = d*(i%3) + (3*d)*(i/3) := by
    calc
      d*i = d*(i%3 + 3*(i/3)) := congrArg (d * ·) hd.symm
      _ = _ := by rw [Nat.mul_add,hmul]
  rw [Nat.add_mul, Nat.one_mul, hprod, ← Nat.add_assoc, Nat.add_mul_mod_self_left]

private def active (i : Nat) : Int := if i%3 = 0 then 0 else 1

private theorem active_count (m : Nat) : sumAt (3*m) active = 2*(m : Int) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Nat.mul_succ, sumAt_split, ih]
    have h : sumAt 3 (fun i => active (3*m+i)) = 2 := by
      change active (3*m+0) + (active (3*m+1) + (active (3*m+2) + 0)) = 2
      simp [active, Nat.mul_add_mod_self_left]
    rw [h, Int.natCast_succ]
    omega

private theorem active_mono (m : Nat) (a : Nat → Bool) (fixed : FixedPrincipal (3*m) a)
    (i : Nat) (hi : i < 3*m) :
    active i ≤ mono (a i) (a (3*m+i)) (a (3*m+3*m+i)) := by
  let d := 3*m
  change i < d at hi
  change FixedPrincipal d a at fixed
  change active i ≤ mono (a i) (a (d+i)) (a (d+d+i))
  have hd : d%3 = 0 := Nat.mul_mod_right 3 m
  have d2 : (d+d)%3 = 0 := by rw [Nat.add_mod,hd]
  by_cases z : i%3 = 0
  · simp only [active, z, ite_true, mono]; split <;> decide
  · simp only [active, z, ite_false]
    have f₁ := fixed i (by omega)
    rw [principal_image] at f₁
    rcases (show i%3 = 1 ∨ i%3 = 2 by omega) with h | h
    · have f₂ := fixed (d+i) (by omega)
      have r : (d+i)%3 = 1 := by rw [Nat.add_mod, hd, h]
      rw [h, Nat.mul_one, Nat.mod_eq_of_lt (by omega), show i+d=d+i by omega] at f₁
      rw [principal_image, r, Nat.mul_one, Nat.mod_eq_of_lt (by omega),
          show d+i+d=d+d+i by omega] at f₂
      simp [mono,f₂,f₁]
    · have f₂ := fixed (d+d+i) (by omega)
      have r : (d+d+i)%3 = 2 := by rw [Nat.add_mod, d2, h]
      rw [h, Nat.mod_eq_of_lt (by omega), show i+d*2=d+d+i by omega] at f₁
      rw [principal_image, r, show d+d+i+d*2 = (d+i)+3*d by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at f₂
      simp [mono,f₂,f₁]

theorem fixed_principal_lower (m : Nat) (a : Nat → Bool) (h : FixedPrincipal (3*m) a) :
    2*(m : Int) ≤ count (3*m) a := by
  rw [← active_count]
  exact sumAt_le (3*m) (active_mono m a h)

/-- On every cyclic length 9m, even the one shift 3m rules out this multiplier on either word. -/
theorem no_principal (m : Nat) (a b : Nat → Bool)
    (h : paf (9*m) a (3*m) + paf (9*m) b (3*m) = -2) :
    ¬FixedPrincipal (3*m) a ∧ ¬FixedPrincipal (3*m) b := by
  rw [show 9*m = 3*m+3*m+3*m by omega] at h
  have ht := twice_count (3*m) a b h
  have ha := count_nonneg (3*m) a
  have hb := count_nonneg (3*m) b
  simp only [Int.natCast_mul] at ht
  constructor
  · intro fixed
    have := fixed_principal_lower m a fixed
    omega
  · intro fixed
    have := fixed_principal_lower m b fixed
    omega

def fixedBy400 (a : Nat → Bool) : Prop := FixedPrincipal 399 a
theorem cannot_fix_either_word (a b : Nat → Bool)
    (h : paf 1197 a 399 + paf 1197 b 399 = -2) : ¬fixedBy400 a ∧ ¬fixedBy400 b :=
  no_principal 133 a b h

#print axioms paf_triples
#print axioms no_principal
#print axioms cannot_fix_either_word

end Hadamard2396
