import Triples

namespace Hadamard2396
namespace PrimeCycles

private theorem sum_const (n : Nat) (z : Int) : sumAt n (fun _ => z) = (n : Int)*z := by
  induction n with
  | zero => simp [sumAt]
  | succ n ih => rw [sumAt_succ, ih, Int.natCast_succ, Int.add_mul, Int.one_mul]

private theorem grid (h w : Nat) (f : Nat → Int) :
    sumAt (h*w) f = sumAt h (fun j => sumAt w (fun i => f (j*w+i))) := by
  induction h with
  | zero => simp [sumAt]
  | succ h ih => rw [Nat.succ_mul, sumAt_split, ih, sumAt_succ]

private theorem swap (h w : Nat) (f : Nat → Nat → Int) :
    sumAt h (fun j => sumAt w (f j)) = sumAt w (fun i => sumAt h (fun j => f j i)) := by
  induction h with
  | zero =>
    change (0:Int) = sumAt w (fun _ => 0)
    rw [sum_const,Int.mul_zero]
  | succ h ih =>
    rw [sumAt_succ, ih, ←sumAt_add]
    apply sumAt_congr
    intro i _
    rw [sumAt_succ]

private def bitAgree (b c : Bool) : Int := if b = c then 1 else 0

private theorem odd_cycle_match (p : Nat) (odd : p%2=1) (x : Nat → Bool) (closes : x p=x 0) :
    ∃ i, i<p ∧ x i = x (i+1) := by
  apply Classical.byContradiction
  intro none
  have flip (i : Nat) (hi : i<p) : x (i+1) = !(x i) := by
    have ne : x i ≠ x (i+1) := fun h => none ⟨i,hi,h⟩
    cases a : x i <;> cases b : x (i+1) <;> simp_all
  have alt (i : Nat) (hi : i≤p) : x i = (if i%2=0 then x 0 else !(x 0)) := by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [flip i (by omega), ih (by omega)]
      rcases Nat.mod_two_eq_zero_or_one i with h | h
      · have n : (i+1)%2 = 1 := by omega
        simp [h,n]
      · have n : (i+1)%2 = 0 := by omega
        simp [h,n]
  have endBit := alt p (by omega)
  rw [closes,odd] at endBit
  cases hx : x 0 <;> simp [hx] at endBit

private theorem one_indicator (n i : Nat) (hi : i < n) :
    sumAt n (fun k => if k=i then (1:Int) else 0) = 1 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [sumAt_succ]
    by_cases e : i=n
    · subst i
      have hz : sumAt n (fun k => if k=n then (1:Int) else 0) = sumAt n (fun _ => 0) := by
        apply sumAt_congr
        intro k hk
        simp [show k≠n by omega]
      rw [hz,sum_const]
      simp
    · rw [ih (by omega)]
      simp [Ne.symm e]

private theorem cycle_lower (p : Nat) (odd : p%2=1) (x : Nat → Bool) (closes : x p=x 0) :
    2-(p:Int) ≤ sumAt p (fun k => sign (x k)*sign (x (k+1))) := by
  obtain ⟨i,hi,e⟩ := odd_cycle_match p odd x closes
  have bound : sumAt p (fun k => if k=i then (1:Int) else 0)
      ≤ sumAt p (fun k => bitAgree (x k) (x (k+1))) := by
    apply sumAt_le
    intro k _
    by_cases h : k=i
    · subst k; simp [bitAgree,e]
    · simp [bitAgree,h]; split <;> decide
  rw [one_indicator _ _ hi] at bound
  have formula (n : Nat) : sumAt n (fun k => sign (x k)*sign (x (k+1))) =
      2 * sumAt n (fun k => bitAgree (x k) (x (k+1))) - (n:Int) := by
    induction n with
    | zero => simp [sumAt]
    | succ n ih =>
      rw [sumAt_succ, sumAt_succ, ih, Int.natCast_succ]
      have term : sign (x n)*sign (x (n+1)) = 2*bitAgree (x n) (x (n+1))-1 := by
        cases x n <;> cases x (n+1) <;> decide
      omega
  rw [formula]; omega

private def cyclic (a : Nat → Bool) (n i : Nat) := a (i%n)
private def fibre (a : Nat → Bool) (p d i k : Nat) := cyclic a (p*d) (i+k*d)

private theorem fibre_period (p d i j k : Nat) (a : Nat → Bool) :
    fibre a p d i (j+k*p) = fibre a p d i j := by
  unfold fibre cyclic
  rw [Nat.add_mul, ← Nat.add_assoc,
    show k*p*d = k*(p*d) by ac_rfl, Nat.add_mul_mod_self_right]

private theorem paf_fibres (a : Nat → Bool) (p d : Nat) :
    paf (p*d) a d = sumAt d (fun i =>
        sumAt p (fun j => sign (fibre a p d i j)*sign (fibre a p d i (j+1)))) := by
  unfold paf
  have convert := sumAt_congr (p*d) (f := fun t => sign (a t)*sign (a ((t+d)%(p*d))))
      (g := fun t => sign (cyclic a (p*d) t)*sign (cyclic a (p*d) (t+d)))
      (fun t ht => by simp [cyclic,Nat.mod_eq_of_lt ht])
  rw [convert,grid,swap]
  apply sumAt_congr
  intro i _
  apply sumAt_congr
  intro j _
  simp only [fibre, Nat.add_mul, Nat.one_mul]
  rw [Nat.add_comm (j*d) i, Nat.add_assoc]

/-- Standard inverse property of the nonzero residues of a prime field. -/
def UnitsMod (p : Nat) : Prop := ∀ i, i%p ≠ 0 → ∃ k, k*i%p=1

private theorem invariant_fibre (p m : Nat) (u : UnitsMod p)
    (a : Nat → Bool) (nz : 0 < p*(p*m))
    (fixed : ∀ t, t < p*(p*m) → a (((1+p*m)*t)%(p*(p*m))) = a t)
    (i : Nat) (nonzero : i%p≠0) (j : Nat) :
    fibre a p (p*m) i (j+1) = fibre a p (p*m) i j := by
  let d := p*m
  let n := p*d
  change 0<n at nz
  change ∀ t, t<n → a (((1+d)*t)%n) = a t at fixed
  have act (t : Nat) : cyclic a n ((1+d)*t) = cyclic a n t := by
    have h := fixed (t%n) (Nat.mod_lt _ nz)
    unfold cyclic
    rw [Nat.mul_mod, Nat.mod_mod] at h
    rwa [Nat.mul_mod]
  have step (k : Nat) : fibre a p d i (k+i) = fibre a p d i k := by
    have h := act (i+k*d)
    have identity : (1+d)*(i+k*d) = (i+(k+i)*d) + n*(k*m) := by
      dsimp [n,d]
      grind
    rw [identity] at h
    unfold cyclic at h
    rw [Nat.add_mul_mod_self_left] at h
    exact h
  have iter (r : Nat) : fibre a p d i (j+r*i) = fibre a p d i j := by
    induction r with
    | zero => simp
    | succ r ih => rw [Nat.succ_mul, ←Nat.add_assoc, step, ih]
  obtain ⟨r,hr⟩ := u i nonzero
  have counts := Nat.mod_add_div (r*i) p
  rw [hr, Nat.mul_comm p] at counts
  have h := iter r
  rw [←counts, ←Nat.add_assoc, fibre_period] at h
  exact h

/-- Lower bound on one original shift if a single word is fixed by 1+p*m.
The residue-inverse hypothesis holds for every prime p. -/
theorem principal_bound (p m : Nat) (odd : p%2=1) (positive : 0<m) (units : UnitsMod p)
    (a b : Nat → Bool) (fixed : ∀ t, t<p*(p*m) → a (((1+p*m)*t)%(p*(p*m)))=a t) :
    2*(m:Int) ≤ paf (p*(p*m)) a (p*m) + paf (p*(p*m)) b (p*m) := by
  let d := p*m
  let layer (w : Nat → Bool) (i : Nat) := sumAt p fun j =>
      sign (fibre w p d i j)*sign (fibre w p d i (j+1))
  have hp : 0<p := by omega
  have nz := Nat.mul_pos hp (Nat.mul_pos hp positive)
  have low (w : Nat → Bool) (i : Nat) : 2-(p:Int) ≤ layer w i := by
    apply cycle_lower p odd
    simpa using fibre_period p d i 0 1 w
  have const (i : Nat) (h : i%p≠0) : layer a i = (p:Int) := by
    have comp : layer a i = sumAt p (fun _ => (1:Int)) := by
      apply sumAt_congr
      intro j _
      rw [invariant_fibre p m units a nz fixed i h j]
      cases fibre a p d i j <;> decide
    rw [comp,sum_const,Int.mul_one]
  let baseline (i : Nat) : Int := if i%p=0 then 4-2*(p:Int) else 2
  have localBound (i : Nat) : baseline i ≤ layer a i + layer b i := by
    have ha := low a i
    have hb := low b i
    by_cases zero : i%p = 0
    · simp [baseline,zero]; omega
    · rw [const i zero]; simp [baseline,zero]; omega
  have block (j : Nat) : sumAt p (fun i => baseline (j*p+i)) = 2 := by
    obtain ⟨k,hk⟩ : ∃ k, p = 1+k := ⟨p-1, by omega⟩
    have splitSize := congrArg (fun q => sumAt q (fun i => baseline (j*p+i))) hk
    rw [splitSize,sumAt_split]
    have tail : sumAt k (fun i => baseline (j*p+(1+i))) = sumAt k (fun _ => (2:Int)) := by
      apply sumAt_congr
      intro i hi
      simp [baseline,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt (show 1+i<p by omega)]
    rw [tail,sum_const]
    have first : sumAt 1 (fun i => baseline (j*p+i)) = 4-2*(p:Int) := by
      simp [sumAt,baseline]
    rw [first]
    omega
  have total : sumAt d baseline = 2*(m:Int) := by
    change sumAt (p*m) baseline = _
    rw [Nat.mul_comm p m, grid, sumAt_congr m (fun j _ => block j), sum_const, Int.mul_comm]
  rw [paf_fibres,paf_fibres,←sumAt_add,←total]
  exact sumAt_le d (fun i _ => localBound i)

private theorem bezout (a b : Nat) : ∃ x y : Int, x*(a:Int) + y*(b:Int) = (Nat.gcd a b:Int) := by
  by_cases zero : a=0
  · subst a; exact ⟨0,1,by simp⟩
  · have decrease : b%a < a := Nat.mod_lt b (by omega)
    obtain ⟨x,y,e⟩ := bezout (b%a) a
    refine ⟨y - x*(b/a : Nat), x, ?_⟩
    rw [Nat.gcd_rec a b]
    have divSum := congrArg (fun n : Nat => (n:Int)) (Nat.mod_add_div b a)
    simp only [Int.natCast_add,Int.natCast_mul] at divSum
    calc
      _ = y*(a:Int) + x*((b:Int) - (a:Int)*(b/a : Nat)) := by grind
      _ = x*(b%a : Nat) + y*(a:Int) := by rw [show (b:Int) - (a:Int)*(b/a : Nat) = (b%a : Nat) by omega,Int.add_comm]
      _ = _ := e
termination_by a

private theorem units_of_prime (p : Nat) (hp : 1<p)
    (prime : ∀ e, e ∣ p → e=1 ∨ e=p) : UnitsMod p := by
  intro i nonzero
  have g : Nat.gcd i p = 1 := by
    rcases prime (Nat.gcd i p) (Nat.gcd_dvd_right i p) with g|g
    · exact g
    · have h := Nat.gcd_dvd_left i p
      rw [g] at h
      exact False.elim (nonzero (Nat.mod_eq_zero_of_dvd h))
  obtain ⟨x,y,bez⟩ := bezout i p
  rw [g] at bez
  let k := (x%(p:Int)).toNat
  refine ⟨k, Int.ofNat_inj.mp ?_⟩
  have pk0 : (p:Int) ≠ 0 := by omega
  have cast : (k:Int) = x%(p:Int) := Int.toNat_of_nonneg (Int.emod_nonneg _ pk0)
  have reduced := congrArg (fun t : Int => t%(p:Int)) bez
  change (x*(i:Int) + y*(p:Int))%(p:Int) = 1%(p:Int) at reduced
  rw [Int.add_mul_emod_self_right,show (1:Int)%(p:Int) = 1 from Int.emod_eq_of_lt (by decide) (by omega)] at reduced
  rw [Int.natCast_emod,Int.natCast_mul,cast,Int.mul_emod,Int.emod_emod]
  rwa [Int.mul_emod] at reduced

/-- At length p²m the order-p multiplier 1+pm cannot fix either word of a pair
meeting the original shift pm. Primality uses the usual positive-divisor definition. -/
theorem odd_prime_square (p m : Nat) (hp : 1<p) (odd : p%2=1)
    (prime : ∀ e, e ∣ p → e=1 ∨ e=p) (positive : 0<m) (a b : Nat → Bool)
    (target : paf (p*(p*m)) a (p*m) + paf (p*(p*m)) b (p*m) = -2) :
    (¬∀ t, t<p*(p*m) → a (((1+p*m)*t)%(p*(p*m)))=a t) ∧
    (¬∀ t, t<p*(p*m) → b (((1+p*m)*t)%(p*(p*m)))=b t) := by
  have units := units_of_prime p hp prime
  constructor
  · intro fixed
    have bound := principal_bound p m odd positive units a b fixed
    omega
  · intro fixed
    have bound := principal_bound p m odd positive units b a fixed
    omega

/-- Fixed coordinate multiplication as used in Table A1 of Ramos–Hulak–de Queiroz (v2). -/
def fixes333 (u : Nat) (a : Nat → Bool) : Prop :=
  ∀ t, t<333 → a ((u*t)%333) = a t

theorem bound_333 (a b : Nat → Bool) (fixed : fixes333 112 a) :
    74 ≤ paf 333 a 111 + paf 333 b 111 := by
  have units : UnitsMod 3 := by
    intro i hi
    rcases (show i%3=1 ∨ i%3=2 by omega) with h|h
    · exact ⟨1,by simp [h]⟩
    · refine ⟨2,?_⟩
      rw [Nat.mul_mod,h]
  exact principal_bound 3 37 (by decide) (by decide) units a b fixed

def commonGenerators333 (generators : List Nat) (a b : Nat → Bool) : Prop :=
  ∀ u ∈ generators, fixes333 u a ∧ fixes333 u b

/-- In Table A1, ID 2 has generators [112], and ID 7 has generators [73,112].
Both are impossible even under just the one original shift equation. -/
theorem excludes_table_A1_rows_2_and_7 (a b : Nat → Bool)
    (target : paf 333 a 111 + paf 333 b 111 = -2) :
    ¬commonGenerators333 [112] a b ∧ ¬commonGenerators333 [73,112] a b := by
  have excludes (fixed : fixes333 112 a) : False := by
    have lower := bound_333 a b fixed
    omega
  exact ⟨fun both => excludes (both 112 (by decide)).1,
         fun both => excludes (both 112 (by decide)).1⟩

#print axioms bound_333
#print axioms excludes_table_A1_rows_2_and_7

#print axioms odd_prime_square

#print axioms principal_bound
end PrimeCycles
end Hadamard2396
