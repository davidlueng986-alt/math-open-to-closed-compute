import Mathlib

/-!
Decisive finite core of the bounded-gcd-overlap reduction for Erdős #25.

This file does NOT assert Erdős #25.  It proves actual prime-factor-signature
injectivity under a bounded gcd-rank assumption, and the finite reciprocal
comparison used in the paper proof.  The infinite prime-series estimate and the
natural-density theorem are ordinary proofs in bounded-gcd-overlap.md.
-/

namespace Erdos25BoundedGcd

open scoped BigOperators

/-- Number of prime factors, counted with multiplicity. -/
def totalPrimeRank (n : ℕ) : ℕ := n.primeFactorsList.length

/-- Product of the first `k+1` entries of the sorted prime factor list. -/
def signature (k n : ℕ) : ℕ := (n.primeFactorsList.take (k + 1)).prod

theorem signature_dvd (k n : ℕ) (hn : n ≠ 0) : signature k n ∣ n := by
  refine ⟨(n.primeFactorsList.drop (k + 1)).prod, ?_⟩
  change n = (n.primeFactorsList.take (k + 1)).prod *
    (n.primeFactorsList.drop (k + 1)).prod
  rw [List.prod_take_mul_prod_drop, Nat.prod_primeFactorsList hn]

theorem signature_rank (k n : ℕ) (h : k + 1 ≤ totalPrimeRank n) :
    totalPrimeRank (signature k n) = k + 1 := by
  have hp : ∀ p ∈ n.primeFactorsList.take (k + 1), Nat.Prime p := by
    intro p hp
    exact Nat.prime_of_mem_primeFactorsList (List.take_subset _ _ hp)
  have hperm := Nat.primeFactorsList_unique
    (n := signature k n) (l := n.primeFactorsList.take (k + 1)) rfl hp
  calc
    totalPrimeRank (signature k n) = (n.primeFactorsList.take (k + 1)).length :=
      hperm.length_eq.symm
    _ = k + 1 := by
      rw [List.length_take, Nat.min_eq_left h]

theorem totalPrimeRank_mono_of_dvd {a b : ℕ} (h : a ∣ b) (hb : b ≠ 0) :
    totalPrimeRank a ≤ totalPrimeRank b :=
  (Nat.primeFactorsList_sublist_of_dvd h hb).length_le

/-- A common signature would force at least `k+1` prime factors in the gcd. -/
theorem signature_injective_on
    (F : Finset ℕ) (k : ℕ)
    (hpos : ∀ n ∈ F, 0 < n)
    (hrank : ∀ n ∈ F, k + 1 ≤ totalPrimeRank n)
    (hoverlap : ∀ n ∈ F, ∀ m ∈ F, n ≠ m → totalPrimeRank (Nat.gcd n m) ≤ k) :
    ∀ n ∈ F, ∀ m ∈ F, signature k n = signature k m → n = m := by
  intro n hn m hm heq
  by_contra hne
  have hd1 : signature k n ∣ n := signature_dvd k n (Nat.ne_of_gt (hpos n hn))
  have hd2 : signature k n ∣ m := by
    rw [heq]
    exact signature_dvd k m (Nat.ne_of_gt (hpos m hm))
  have hdg : signature k n ∣ Nat.gcd n m := Nat.dvd_gcd hd1 hd2
  have hgpos : 0 < Nat.gcd n m := Nat.gcd_pos_of_pos_left m (hpos n hn)
  have hmono := totalPrimeRank_mono_of_dvd hdg (Nat.ne_of_gt hgpos)
  have hsig := signature_rank k n (hrank n hn)
  have hupper := hoverlap n hn m hm hne
  omega

/--
The reciprocal comparison is factored at the exact elementary arithmetic
assumption used by the infinite proof: `sig n * weight (sig n) ≤ n`.
For the sorted prime-factor signature, the ordinary proof takes `weight` to be
the largest prime factor and uses the next factor of `n`.
-/
theorem finite_reciprocal_domination
    (F : Finset ℕ) (sig weight : ℕ → ℕ)
    (hinj : ∀ n ∈ F, ∀ m ∈ F, sig n = sig m → n = m)
    (hpositive : ∀ n ∈ F, 0 < sig n * weight (sig n))
    (hbound : ∀ n ∈ F, sig n * weight (sig n) ≤ n) :
    (∑ n ∈ F, (1 : ℝ) / (n : ℝ)) ≤
      ∑ d ∈ F.image sig, (1 : ℝ) / ((d * weight d : ℕ) : ℝ) := by
  calc
    (∑ n ∈ F, (1 : ℝ) / (n : ℝ)) ≤
        ∑ n ∈ F, (1 : ℝ) / ((sig n * weight (sig n) : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      apply one_div_le_one_div_of_le
      · exact_mod_cast hpositive n hn
      · exact_mod_cast hbound n hn
    _ = ∑ d ∈ F.image sig, (1 : ℝ) / ((d * weight d : ℕ) : ℝ) :=
      (Finset.sum_image hinj).symm

theorem signature_reciprocal_domination
    (F : Finset ℕ) (k : ℕ) (weight : ℕ → ℕ)
    (hpos : ∀ n ∈ F, 0 < n)
    (hrank : ∀ n ∈ F, k + 1 ≤ totalPrimeRank n)
    (hoverlap : ∀ n ∈ F, ∀ m ∈ F, n ≠ m → totalPrimeRank (Nat.gcd n m) ≤ k)
    (hpositive : ∀ n ∈ F, 0 < signature k n * weight (signature k n))
    (hbound : ∀ n ∈ F, signature k n * weight (signature k n) ≤ n) :
    (∑ n ∈ F, (1 : ℝ) / (n : ℝ)) ≤
      ∑ d ∈ F.image (signature k), (1 : ℝ) / ((d * weight d : ℕ) : ℝ) := by
  exact finite_reciprocal_domination F (signature k) weight
    (signature_injective_on F k hpos hrank hoverlap) hpositive hbound

#print axioms signature_dvd
#print axioms signature_rank
#print axioms totalPrimeRank_mono_of_dvd
#print axioms signature_injective_on
#print axioms finite_reciprocal_domination
#print axioms signature_reciprocal_domination

end Erdos25BoundedGcd
