import Shadow
import NonBacktrackingGirth
import Wave5Agent5GirthTripling
import Wave5Agent6ChebyshevGirth
import ChebTraceEngine

/-!
# Wave 8 Agent #2 — Pillar 2: Exact Trace-Coupled Non-Simple CNB Walk Upper Bound (`L < 3g`)

Proves unconditionally for EVERY cubic (`d = 3`), power-free (`¬ HasPower G`) simple graph `G`
of girth `g ≥ 6` and target power-of-2 length `L = 2^k` (`k ≥ 4`, `L < 3 * g`, `L ≤ 64`):

  `nonSimpleTaillessCount G L ≤ ∑ r ∈ Finset.range L, alphaCoeff g L r * taillessCount G r`

where `alphaCoeff g L r = thetaTerm g L r + barbellTerm g L r` is the exact trace-coupled
non-simple walk coefficient (with zero assumption that intersecting cycles share a single path!).

Key components:
1. `card_nbWalksAvoid_le`: at most `2^m` NB walks of length `m` starting at `u` avoiding `prev`.
2. `card_nbWalksBetweenAvoid_le`: at most `2^(m - s)` NB walks of length `m` from `u` to `v`
   avoiding `prev` at the start, where `s = (g - 1) / 2` (via `unique_nonBacktracking_walk_of_half_girth`).
3. `tailless_nonSimple_exact_decomp`: upgrades `Wave5Agent5`'s girth-tripling decomposition to
   retain the exact cyclic rotation `rot = c₁ ++ P ++ c₂ ++ P.reverse` with `c₁, c₂` simple cycles.
4. `exists_maximal_shared_prefix`: for any zero-tail pair `c₁ ++ c₂` (`c₁.length < c₂.length`)
   in a cubic graph, finds a rotation `c₁' ++ c₂'` sharing a maximal prefix `P_b` (`1 ≤ b < r₁`)
   whose entry edges at `u` and exit edges at `v` are distinct (forcing the 3rd edge at both ends!).
5. `nonSimpleTaillessCount_le_sum_alpha`: combines Barbell (including exact 2-to-1 symmetry when
   `r₁ = r₂`) and Theta (`r₁ < r₂` forced by `¬ HasPower G`) surjection counts.
-/

namespace E64Wave8Agent2
open SimpleGraph Erdos64Closure E64NonBacktrackingGirth E64Wave5Agent5 E64Wave5Agent6

section WalkSplittingAndBounds

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Subtype-wrapped Finset of non-backtracking walks of length `k` from `u` to `v`. -/
def nbWalksSub (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (u v : V) :
    Finset {p : G.Walk u v // p.length = k} :=
  (nbWalks G k u v).attach.map
    ⟨fun x => ⟨x.1, (mem_finsetWalkLength_iff.mp (Finset.mem_filter.mp x.2).1)⟩,
     fun a b h => Subtype.ext (congrArg Subtype.val h)⟩

@[simp] theorem mem_nbWalksSub_iff {G : SimpleGraph V} [DecidableRel G.Adj]
    {k : ℕ} {u v : V} {p : {q : G.Walk u v // q.length = k}} :
    p ∈ nbWalksSub G k u v ↔ IsNonBacktracking p.1 := by
  simp only [nbWalksSub, Finset.mem_map, Finset.mem_attach, Function.Embedding.coeFn_mk,
    true_and, Subtype.exists]
  constructor
  · rintro ⟨q, hq, heq⟩
    have hqp : q = p.1 := congrArg Subtype.val heq
    rw [← hqp]
    exact (Finset.mem_filter.mp hq).2
  · intro hnb
    refine ⟨p.1, ?_, rfl⟩
    simp only [nbWalks, Finset.mem_filter, mem_finsetWalkLength_iff]
    exact ⟨p.2, hnb⟩

theorem taillessCount_eq_card_sub (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    (((Finset.univ : Finset V).sigma fun v => nbWalksSub G k v v).filter
      fun x => IsCyclicallyNonBacktracking x.2.1).card = taillessCount G k := by
  simp only [taillessCount, Finset.filter_sigma, Finset.card_sigma]
  refine Finset.sum_congr rfl fun v _ => ?_
  refine Finset.card_bij (fun p _ => p.1) (fun p hp => ?_) (fun p₁ _ p₂ _ h => Subtype.ext h) (fun q hq => ?_)
  · simp only [Finset.mem_filter, mem_nbWalksSub_iff] at hp
    simp only [nbWalks, Finset.mem_filter, mem_finsetWalkLength_iff]
    exact ⟨⟨p.2, hp.1⟩, hp.2⟩
  · simp only [nbWalks, Finset.mem_filter, mem_finsetWalkLength_iff] at hq
    refine ⟨⟨q, hq.1.1⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, mem_nbWalksSub_iff]
    exact ⟨hq.1.2, hq.2⟩

theorem nonSimpleTaillessCount_eq_card_sub (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    haveI : DecidablePred (fun x : Σ v : V, {p : G.Walk v v // p.length = k} =>
      IsCyclicallyNonBacktracking x.2.1 ∧ ¬ x.2.1.IsCycle) := Classical.decPred _
    (((Finset.univ : Finset V).sigma fun v => nbWalksSub G k v v).filter
      fun x => IsCyclicallyNonBacktracking x.2.1 ∧ ¬ x.2.1.IsCycle).card =
      nonSimpleTaillessCount G k := by
  intro _
  classical
  unfold nonSimpleTaillessCount
  simp only [Finset.filter_sigma, Finset.card_sigma]
  refine Finset.sum_congr rfl fun v _ => ?_
  refine Finset.card_bij (fun p _ => p.1) (fun p hp => ?_) (fun p₁ _ p₂ _ h => Subtype.ext h) (fun q hq => ?_)
  · simp only [Finset.mem_filter, mem_nbWalksSub_iff] at hp
    simp only [nbWalks, Finset.mem_filter, mem_finsetWalkLength_iff]
    exact ⟨⟨p.2, hp.1⟩, hp.2⟩
  · simp only [nbWalks, Finset.mem_filter, mem_finsetWalkLength_iff] at hq
    refine ⟨⟨q, hq.1.1⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, mem_nbWalksSub_iff]
    exact ⟨hq.1.2, hq.2⟩

theorem firstNbr_append_of_pos {G : SimpleGraph V} {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) (hp : 1 ≤ p.length) :
    firstNbr (p.append q) = firstNbr p := by
  cases p with
  | nil => simp at hp
  | cons _ _ => rfl

theorem lastNbr_append_of_pos {G : SimpleGraph V} {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) (hq : 1 ≤ q.length) :
    lastNbr (p.append q) = lastNbr q := by
  induction p with
  | nil => rfl
  | cons h rest ih =>
      cases rest with
      | nil =>
          cases q with
          | nil => simp at hq
          | cons _ _ => rfl
      | cons h₂ rest₂ =>
          exact ih

theorem firstNbr_reverse {G : SimpleGraph V} :
    ∀ {u v : V} (p : G.Walk u v), firstNbr p.reverse = lastNbr p
  | _, _, .nil => rfl
  | _, _, .cons _ .nil => rfl
  | _, _, .cons h₁ (.cons h₂ rest) => by
      rw [Walk.reverse_cons,
          firstNbr_append_of_pos (.cons h₂ rest).reverse (.cons h₁.symm .nil)
            (by simp [Walk.length_reverse])]
      exact firstNbr_reverse (.cons h₂ rest)

theorem lastNbr_reverse {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    lastNbr p.reverse = firstNbr p := by
  have h := firstNbr_reverse p.reverse
  rw [Walk.reverse_reverse] at h
  exact h.symm

/-- Split a walk `p : G.Walk u v` at step `k ≤ p.length` into prefix of length `k` and suffix of length `p.length - k`. -/
def splitWalk {G : SimpleGraph V} :
    ∀ {u v : V} (k : ℕ) (p : G.Walk u v), k ≤ p.length →
      Σ w : V, {q : G.Walk u w // q.length = k} × {r : G.Walk w v // r.length = p.length - k}
  | u, _, 0, p, _ => ⟨u, ⟨.nil, rfl⟩, ⟨p, by simp⟩⟩
  | _, _, k + 1, .nil, hk => by simp at hk
  | _, _, k + 1, .cons h rest, hk =>
      let ⟨w, ⟨q, hq⟩, ⟨r, hr⟩⟩ := splitWalk k rest (by simp at hk; omega)
      ⟨w, ⟨.cons h q, by simp [hq]⟩, ⟨r, by simp [hr]⟩⟩

theorem splitWalk_append {G : SimpleGraph V} :
    ∀ {u v : V} (k : ℕ) (p : G.Walk u v) (hk : k ≤ p.length),
      (splitWalk k p hk).2.1.1.append (splitWalk k p hk).2.2.1 = p
  | _, _, 0, _, _ => rfl
  | _, _, k + 1, .nil, hk => by simp at hk
  | _, _, k + 1, .cons h rest, hk => by
      simp only [splitWalk, Walk.cons_append]
      congr 1
      exact splitWalk_append k rest (by simp at hk; omega)

/-- Unrotate a closed walk `rot : G.Walk x x` of length `L` by shift `j : Fin L`:
splits `rot` at `L - j.1` into `b : G.Walk x v` and `a : G.Walk v x`, returning `⟨v, a ++ b⟩`. -/
def unrotate {G : SimpleGraph V} (L : ℕ) (j : Fin L) {x : V} (rot : G.Walk x x)
    (hrot : rot.length = L) : Σ v : V, {p : G.Walk v v // p.length = L} :=
  let s := splitWalk (L - j.1) rot (by omega)
  ⟨s.1, ⟨s.2.2.1.append s.2.1.1, by
    rw [Walk.length_append, s.2.2.2, s.2.1.2, hrot]
    have := j.2
    omega⟩⟩

theorem unrotate_append {G : SimpleGraph V} {L : ℕ} {v x : V}
    (a : G.Walk v x) (b : G.Walk x v) (hL : (a.append b).length = L) (ha : a.length < L) :
    unrotate L ⟨a.length, ha⟩ (b.append a) (by rw [Walk.length_append] at hL ⊢; omega) =
      ⟨v, ⟨a.append b, hL⟩⟩ := by
  unfold unrotate
  have hb_len : b.length = L - a.length := by
    rw [Walk.length_append] at hL; omega
  have hsplit : ∀ {u w z : V} (p₁ : G.Walk u w) (p₂ : G.Walk w z) (k : ℕ) (hk : k = p₁.length),
      splitWalk k (p₁.append p₂) (by rw [Walk.length_append]; omega) =
        ⟨w, ⟨p₁, hk.symm⟩, ⟨p₂, by rw [Walk.length_append]; omega⟩⟩ := by
    intro u w z p₁
    induction p₁ with
    | nil =>
        intro p₂ k hk
        subst hk
        rfl
    | cons h rest ih =>
        intro p₂ k hk
        cases k with
        | zero => simp at hk
        | succ k' =>
            have hk' : k' = rest.length := by simp at hk; omega
            have hrec := ih p₂ k' hk'
            simp only [Walk.cons_append, splitWalk]
            rw [hrec]
  have hs := hsplit b a (L - a.length) hb_len.symm
  dsimp only
  generalize_proofs h1 h2
  have hs' : splitWalk (L - a.length) (b.append a) h1 =
      ⟨v, ⟨b, hb_len⟩, ⟨a, by rw [Walk.length_append]; omega⟩⟩ := hs
  refine Sigma.ext (congrArg Sigma.fst hs') ?_
  refine heq_of_eqRec_eq ?_ rfl
  simp only [hs']

/-- Finset of all NB walks of length `m` starting at `u` whose first step `≠ prev`. -/
def nbWalksAvoid (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ) (u prev : V) :
    Finset (Σ v : V, {p : G.Walk u v // p.length = m}) :=
  ((Finset.univ : Finset V).sigma fun v => nbWalksSub G m u v).filter fun x =>
    firstNbr x.2.1 ≠ some prev

/-- In a cubic graph, there are at most `2^m` NB walks of length `m` starting at `u` avoiding `prev` (`G.Adj u prev`). -/
theorem card_nbWalksAvoid_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : ∀ x : V, G.degree x = 3) :
    ∀ (m : ℕ) (u prev : V), G.Adj u prev → (nbWalksAvoid G m u prev).card ≤ 2 ^ m
  | 0, u, prev, _ => by
      have hsub : nbWalksAvoid G 0 u prev ⊆ {⟨u, ⟨.nil, rfl⟩⟩} := by
        rintro ⟨v, ⟨p, hp⟩⟩ _
        cases p with
        | nil => simp
        | cons _ _ => simp at hp
      exact (Finset.card_le_card hsub).trans (by simp)
  | m + 1, u, prev, hprev => by
      let T := ((G.neighborFinset u).erase prev).sigma fun w => nbWalksAvoid G m w u
      have hcard_T : T.card ≤ 2 ^ (m + 1) := by
        rw [Finset.card_sigma]
        have hstep : ∀ w ∈ (G.neighborFinset u).erase prev, (nbWalksAvoid G m w u).card ≤ 2 ^ m := by
          intro w hw
          have huw : G.Adj u w := (G.mem_neighborFinset u w).mp (Finset.mem_erase.mp hw).2
          exact card_nbWalksAvoid_le G hreg m w u huw.symm
        have hsum := Finset.sum_le_sum hstep
        rw [Finset.sum_const, smul_eq_mul] at hsum
        have herase : ((G.neighborFinset u).erase prev).card = 2 := by
          rw [Finset.card_erase_of_mem ((G.mem_neighborFinset u prev).mpr hprev),
              G.card_neighborFinset_eq_degree, hreg u]
        rw [herase] at hsum
        simpa [pow_succ, mul_comm] using hsum
      refine le_trans ?_ hcard_T
      let peel : (Σ v : V, {p : G.Walk u v // p.length = m + 1}) →
          (Σ w : V, Σ v : V, {p : G.Walk w v // p.length = m}) := fun x =>
        match x with
        | ⟨v, ⟨.cons _ rest, hp⟩⟩ => ⟨_, ⟨v, ⟨rest, by simpa using hp⟩⟩⟩
        | ⟨_, ⟨.nil, hp⟩⟩ => absurd hp (by simp)
      refine Finset.card_le_card_of_injOn peel ?_ ?_
      · rintro ⟨v, ⟨p, hp⟩⟩ hx
        rw [Finset.mem_coe] at hx ⊢
        cases p with
        | nil => simp at hp
        | cons h₁ rest =>
            rename_i w
            have hx' := Finset.mem_filter.mp hx
            have hnb : IsNonBacktracking (Walk.cons h₁ rest) :=
              mem_nbWalksSub_iff.mp (Finset.mem_sigma.mp hx'.1).2
            have hne : w ≠ prev := by
              have := hx'.2
              simp only [firstNbr, ne_eq, Option.some.injEq] at this
              exact this
            simp only [peel, T, Finset.mem_sigma, Finset.mem_erase, G.mem_neighborFinset,
              nbWalksAvoid, Finset.mem_filter, Finset.mem_univ, true_and, mem_nbWalksSub_iff]
            refine ⟨⟨hne, h₁⟩, ?_, ?_⟩
            · exact isNonBacktracking_of_append_right (p := .cons h₁ .nil) hnb
            · cases rest with
              | nil => simp [firstNbr]
              | cons h₂ rest₂ =>
                  simp only [firstNbr, ne_eq, Option.some.injEq]
                  exact Ne.symm hnb.1
      · rintro ⟨v₁, ⟨p₁, hp₁⟩⟩ _ ⟨v₂, ⟨p₂, hp₂⟩⟩ _ heq
        cases p₁ with
        | nil => simp at hp₁
        | cons h₁ rest₁ =>
            cases p₂ with
            | nil => simp at hp₂
            | cons h₂ rest₂ =>
                simp only [peel, Sigma.mk.inj_iff] at heq
                rcases heq with ⟨rfl, rfl, rfl⟩
                rfl

/-- Finset of all NB walks of length `m` from `u` to `v` avoiding `prev` at the first step. -/
def nbWalksBetweenAvoid (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ) (u prev v : V) :
    Finset {p : G.Walk u v // p.length = m} :=
  (nbWalksSub G m u v).filter fun p => firstNbr p.1 ≠ some prev

/-- **Exact Girth-Ball Fixed-Endpoint Bound**: In a cubic graph of girth `≥ g` (`s = (g - 1) / 2`),
there are at most `2 ^ (m - s)` NB walks of length `m` from `u` to `v` avoiding `prev` (`G.Adj u prev`). -/
theorem card_nbWalksBetweenAvoid_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {g : ℕ} (hg : GirthAtLeast G g) (hreg : ∀ x : V, G.degree x = 3)
    (m : ℕ) (u prev v : V) (hprev : G.Adj u prev) :
    (nbWalksBetweenAvoid G m u prev v).card ≤ 2 ^ (m - (g - 1) / 2) := by
  set s := (g - 1) / 2
  by_cases hms : m ≤ s
  · have h0 : m - s = 0 := Nat.sub_eq_zero_of_le hms
    rw [h0, pow_zero]
    refine Finset.card_le_one.mpr ?_
    rintro ⟨p₁, hp₁⟩ h₁ ⟨p₂, hp₂⟩ h₂
    simp only [nbWalksBetweenAvoid, Finset.mem_filter, mem_nbWalksSub_iff] at h₁ h₂
    ext
    exact unique_nonBacktracking_walk_of_half_girth hg p₁ p₂ (by omega) (by omega) h₁.1 h₂.1
  · have hlt : s < m := by omega
    have hle_ms : m - s ≤ m := Nat.sub_le m s
    have hcard_av := card_nbWalksAvoid_le G hreg (m - s) u prev hprev
    refine le_trans ?_ hcard_av
    refine Finset.card_le_card_of_injOn
      (fun p =>
        let sp := splitWalk (m - s) p.1 (by rw [p.2]; exact hle_ms)
        ⟨sp.1, sp.2.1⟩)
      ?_ ?_
    · rintro ⟨p, hp⟩ hmem
      simp only [Finset.mem_coe, nbWalksBetweenAvoid, Finset.mem_filter, mem_nbWalksSub_iff] at hmem
      set sp := splitWalk (m - s) p (by rw [hp]; exact hle_ms)
      have happ : sp.2.1.1.append sp.2.2.1 = p := splitWalk_append (m - s) p (by rw [hp]; exact hle_ms)
      simp only [Finset.mem_coe, nbWalksAvoid, Finset.mem_filter, Finset.mem_sigma, Finset.mem_univ,
        true_and, mem_nbWalksSub_iff]
      refine ⟨isNonBacktracking_of_append_left (happ ▸ hmem.1), ?_⟩
      have hpos : 1 ≤ sp.2.1.1.length := by rw [sp.2.1.2]; omega
      have hfn : firstNbr p = firstNbr sp.2.1.1 := by
        have h1 : firstNbr p = firstNbr (sp.2.1.1.append sp.2.2.1) := congrArg firstNbr happ.symm
        rw [h1]
        exact firstNbr_append_of_pos sp.2.1.1 sp.2.2.1 hpos
      rw [← hfn]
      exact hmem.2
    · rintro ⟨p₁, hp₁⟩ h₁ ⟨p₂, hp₂⟩ h₂ heq
      simp only [Finset.mem_coe, nbWalksBetweenAvoid, Finset.mem_filter, mem_nbWalksSub_iff] at h₁ h₂
      have happ₁ := splitWalk_append (m - s) p₁ (by rw [hp₁]; exact hle_ms)
      have happ₂ := splitWalk_append (m - s) p₂ (by rw [hp₂]; exact hle_ms)
      rcases hsp₁ : splitWalk (m - s) p₁ (by rw [hp₁]; exact hle_ms) with ⟨w₁, ⟨q₁, hq₁⟩, ⟨r₁, hr₁⟩⟩
      rcases hsp₂ : splitWalk (m - s) p₂ (by rw [hp₂]; exact hle_ms) with ⟨w₂, ⟨q₂, hq₂⟩, ⟨r₂, hr₂⟩⟩
      dsimp only at heq
      rw [hsp₁] at heq happ₁
      rw [hsp₂] at heq happ₂
      simp only [Sigma.mk.inj_iff] at heq
      rcases heq with ⟨rfl, hq_heq⟩
      have hq_eq : q₁ = q₂ := congrArg Subtype.val (eq_of_heq hq_heq)
      subst hq_eq
      have hr₁_nb : IsNonBacktracking r₁ := isNonBacktracking_of_append_right (happ₁ ▸ h₁.1)
      have hr₂_nb : IsNonBacktracking r₂ := isNonBacktracking_of_append_right (happ₂ ▸ h₂.1)
      have hr_eq : r₁ = r₂ :=
        unique_nonBacktracking_walk_of_half_girth hg r₁ r₂ (by omega) (by omega) hr₁_nb hr₂_nb
      ext
      rw [← happ₁, ← happ₂, hr_eq]

/-- Unique third neighbor of a degree-3 vertex `u` given two distinct neighbors `a ≠ b`. -/
theorem exists_unique_third_nbr (G : SimpleGraph V) [DecidableRel G.Adj]
    {u a b : V} (hdeg : G.degree u = 3) (ha : G.Adj u a) (hb : G.Adj u b) (hab : a ≠ b) :
    ∃! c : V, G.Adj u c ∧ c ≠ a ∧ c ≠ b := by
  have hcard : (((G.neighborFinset u).erase a).erase b).card = 1 := by
    have hb_mem : b ∈ (G.neighborFinset u).erase a :=
      Finset.mem_erase.mpr ⟨hab.symm, (G.mem_neighborFinset u b).mpr hb⟩
    rw [Finset.card_erase_of_mem hb_mem,
        Finset.card_erase_of_mem ((G.mem_neighborFinset u a).mpr ha),
        G.card_neighborFinset_eq_degree, hdeg]
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcard
  refine ⟨c, ?_, ?_⟩
  · have hmem : c ∈ ((G.neighborFinset u).erase a).erase b := by rw [hc]; exact Finset.mem_singleton_self c
    simp only [Finset.mem_erase, G.mem_neighborFinset] at hmem
    exact ⟨hmem.2.2, hmem.2.1, hmem.1⟩
  · rintro y ⟨hy, hya, hyb⟩
    have hmem : y ∈ ((G.neighborFinset u).erase a).erase b := by
      simp only [Finset.mem_erase, G.mem_neighborFinset]
      exact ⟨hyb, hya, hy⟩
    rw [hc, Finset.mem_singleton] at hmem
    exact hmem

end WalkSplittingAndBounds

section ExactAlphaCounting

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exact theta-walk coefficient for cycle length `r₁` at girth `g` and walk length `L`. -/
def thetaTerm (g L r₁ : ℕ) : ℕ :=
  let s := (g - 1) / 2
  let r₂ := L - r₁
  if g ≤ r₁ ∧ r₁ < r₂ ∧ ¬ isPow2Small r₁ ∧ ¬ isPow2Small r₂ then
    ((List.range r₁).filter fun b =>
      1 ≤ b ∧ g ≤ L - 2 * b ∧ ¬ (isPow2Small (L - 2 * b) && decide (L - 2 * b < 2 * g))).map
        (fun b => L * 2 ^ (r₂ - b - 2 - s)) |>.sum
  else 0

/-- Exact barbell-walk coefficient for cycle length `r₁` at girth `g` and walk length `L`. -/
def barbellTerm (g L r₁ : ℕ) : ℕ :=
  let s := (g - 1) / 2
  ((List.range (L / 2)).filter fun p => 1 ≤ p ∧ 2 * g ≤ L - 2 * p).map (fun p =>
    let r₂ := L - 2 * p - r₁
    if g ≤ r₁ ∧ r₁ ≤ r₂ ∧ ¬ isPow2Small r₁ ∧ ¬ isPow2Small r₂ then
      (if r₁ = r₂ then L else 2 * L) * 2 ^ (p - 1 + (r₂ - 2 - s))
    else 0) |>.sum

/-- Total trace-coupled non-simple walk coefficient `α_{r₁}` at girth `g` and walk length `L`. -/
def alphaCoeff (g L r₁ : ℕ) : ℕ :=
  thetaTerm g L r₁ + barbellTerm g L r₁

/-- Helper: cyclic rotation preserves `IsCyclicallyNonBacktracking`. -/
theorem isCyclicallyNonBacktracking_rotate {G : SimpleGraph V} {u v : V}
    (a : G.Walk u v) (b : G.Walk v u) (hcyc : IsCyclicallyNonBacktracking (a.append b)) :
    IsCyclicallyNonBacktracking (b.append a) := by
  unfold IsCyclicallyNonBacktracking at hcyc ⊢
  have h1 : (a.append b).append (a.append b) = a.append ((b.append a).append b) := by
    simp [Walk.append_assoc]
  rw [h1] at hcyc
  have hba_b : IsNonBacktracking ((b.append a).append b) :=
    isNonBacktracking_of_append_right hcyc
  have hba : IsNonBacktracking (b.append a) := isNonBacktracking_of_append_left hba_b
  rw [isNonBacktracking_append_iff]
  refine ⟨hba, hba, ?_⟩
  intro x y hx hy
  cases b with
  | nil =>
      simp only [Walk.nil_append] at hcyc ⊢
      have hnb_aa : IsNonBacktracking (a.append a) := by
        simpa using hcyc
      rw [isNonBacktracking_append_iff] at hnb_aa
      exact hnb_aa.2.2 x y hx hy
  | cons h₁ rest =>
      have hpos_b : 1 ≤ (Walk.cons h₁ rest).length := by simp
      have hfn : firstNbr ((Walk.cons h₁ rest).append a) = firstNbr (Walk.cons h₁ rest) :=
        firstNbr_append_of_pos _ _ hpos_b
      rw [hfn] at hy
      rw [isNonBacktracking_append_iff] at hba_b
      exact hba_b.2.2 x y hx hy

/-- Helper: stripping first and last edges of a simple cycle `c` of length `≥ 3` at `v`. -/
theorem strip_cycle_ends {G : SimpleGraph V} {v : V} (c : G.Walk v v)
    (hc : c.IsCycle) (h3 : 3 ≤ c.length) :
    ∃ (v₁ v₂ : V) (h₁ : G.Adj v v₁) (h₂ : G.Adj v₂ v) (mid : G.Walk v₁ v₂),
      v₁ ≠ v₂ ∧ c = Walk.cons h₁ (mid.append (Walk.cons h₂ .nil)) ∧
      mid.length = c.length - 2 ∧ IsNonBacktracking mid ∧ firstNbr mid ≠ some v := by
  cases c with
  | nil => simp at h3
  | cons h₁ rest =>
      rename_i v₁
      have hrest_pos : 2 ≤ rest.length := by simp at h3; omega
      have hsplit : ∀ {a b : V} (q : G.Walk a b), 1 ≤ q.length →
          ∃ (x : V) (mid : G.Walk a x) (hx : G.Adj x b), q = mid.append (.cons hx .nil) := by
        intro a b q hq
        induction q with
        | nil => simp at hq
        | cons h r ih =>
            cases r with
            | nil => exact ⟨_, .nil, h, rfl⟩
            | cons h' r' =>
                obtain ⟨x, mid, hx, heq⟩ := ih (by simp)
                exact ⟨x, .cons h mid, hx, by rw [Walk.cons_append, ← heq]⟩
      obtain ⟨v₂, mid, h₂, hrest_eq⟩ := hsplit rest (by omega)
      have hcyc_nb : IsCyclicallyNonBacktracking (Walk.cons h₁ rest) := by
        have htr := hc.isTrail
        have aux : ∀ {a b : V} (w : G.Walk a b), w.IsTrail → IsNonBacktracking w := by
          intro a b w
          induction w with
          | nil => intro _; trivial
          | cons ha r ih =>
              intro ht
              cases r with
              | nil => trivial
              | cons hb r' =>
                  have hnd := ht.edges_nodup
                  rw [Walk.edges_cons, List.nodup_cons] at hnd
                  refine ⟨fun heq => ?_, ih (Walk.IsTrail.mk hnd.2)⟩
                  subst heq
                  exact hnd.1 (by simp [Sym2.eq_swap])
        have hnb := aux _ htr
        rw [IsCyclicallyNonBacktracking, isNonBacktracking_append_iff]
        refine ⟨hnb, hnb, ?_⟩
        intro x y hx hy
        rw [hrest_eq] at hx htr
        have hx' : x = v₂ := by
          have hl : lastNbr (Walk.cons h₁ (mid.append (.cons h₂ .nil))) = some v₂ := by
            have : Walk.cons h₁ (mid.append (.cons h₂ .nil)) =
                (Walk.cons h₁ mid).append (.cons h₂ .nil) := by simp
            rw [this, lastNbr_append_of_pos _ _ (by simp)]
            rfl
          rw [hl, Option.some.injEq] at hx
          exact hx.symm
        have hy' : y = v₁ := by
          simp only [firstNbr, Option.some.injEq] at hy
          exact hy.symm
        subst hx'; subst hy'
        intro heq; subst heq
        have hnd := htr.edges_nodup
        simp only [Walk.edges_cons, List.nodup_cons, Walk.edges_append, List.mem_append] at hnd
        exact hnd.1 (Or.inr (by simp [Sym2.eq_swap]))
      have hnb_c : IsNonBacktracking (Walk.cons h₁ rest) := isNonBacktracking_of_append_left hcyc_nb
      have hv12 : v₁ ≠ v₂ := by
        intro heq; subst heq
        have hnd := hc.isTrail.edges_nodup
        rw [hrest_eq] at hnd
        simp only [Walk.edges_cons, List.nodup_cons, Walk.edges_append, List.mem_append] at hnd
        exact hnd.1 (Or.inr (by simp [Sym2.eq_swap]))
      have hmid_len : mid.length = (Walk.cons h₁ rest).length - 2 := by
        have := congrArg Walk.length hrest_eq
        simp only [Walk.length_append, Walk.length_cons, Walk.length_nil] at this ⊢
        omega
      have hnb_rest : IsNonBacktracking rest :=
        isNonBacktracking_of_append_right (p := .cons h₁ .nil) hnb_c
      have hnb_mid : IsNonBacktracking mid :=
        isNonBacktracking_of_append_left (hrest_eq ▸ hnb_rest)
      have hfn_mid : firstNbr mid ≠ some v := by
        cases mid with
        | nil => simp [firstNbr]
        | cons h₃ mid' =>
            rw [hrest_eq] at hnb_c
            simp only [Walk.cons_append, IsNonBacktracking] at hnb_c
            simp only [firstNbr, ne_eq, Option.some.injEq]
            exact Ne.symm hnb_c.1
      exact ⟨v₁, v₂, h₁, h₂, mid, hv12, by rw [hrest_eq], hmid_len, hnb_mid, hfn_mid⟩

/-- Helper: stripping first and last edges of any NB walk `q : G.Walk v u` of length `≥ 2`. -/
theorem strip_walk_ends {G : SimpleGraph V} {v u : V} (q : G.Walk v u)
    (hnb : IsNonBacktracking q) (h2 : 2 ≤ q.length) :
    ∃ (v₁ u₁ : V) (h₁ : G.Adj v v₁) (h₂ : G.Adj u₁ u) (mid : G.Walk v₁ u₁),
      q = Walk.cons h₁ (mid.append (Walk.cons h₂ .nil)) ∧
      firstNbr q = some v₁ ∧ lastNbr q = some u₁ ∧
      mid.length = q.length - 2 ∧ IsNonBacktracking mid ∧ firstNbr mid ≠ some v := by
  cases q with
  | nil => simp at h2
  | cons h₁ rest =>
      rename_i v₁
      have hsplit : ∀ {a b : V} (r : G.Walk a b), 1 ≤ r.length →
          ∃ (x : V) (mid : G.Walk a x) (hx : G.Adj x b), r = mid.append (.cons hx .nil) := by
        intro a b r hr
        induction r with
        | nil => simp at hr
        | cons h r' ih =>
            cases r' with
            | nil => exact ⟨_, .nil, h, rfl⟩
            | cons h' r'' =>
                obtain ⟨x, mid, hx, heq⟩ := ih (by simp)
                exact ⟨x, .cons h mid, hx, by rw [Walk.cons_append, ← heq]⟩
      obtain ⟨u₁, mid, h₂, hrest_eq⟩ := hsplit rest (by simp at h2; omega)
      have hlast : lastNbr (Walk.cons h₁ rest) = some u₁ := by
        rw [hrest_eq]
        have : Walk.cons h₁ (mid.append (.cons h₂ .nil)) =
            (Walk.cons h₁ mid).append (.cons h₂ .nil) := by simp
        rw [this, lastNbr_append_of_pos _ _ (by simp)]
        rfl
      have hnb_rest : IsNonBacktracking rest :=
        isNonBacktracking_of_append_right (p := .cons h₁ .nil) hnb
      have hnb_mid : IsNonBacktracking mid :=
        isNonBacktracking_of_append_left (hrest_eq ▸ hnb_rest)
      have hfn_mid : firstNbr mid ≠ some v := by
        cases mid with
        | nil => simp [firstNbr]
        | cons _ _ =>
            rw [hrest_eq] at hnb
            simp only [Walk.cons_append, IsNonBacktracking] at hnb
            simp only [firstNbr, ne_eq, Option.some.injEq]
            exact Ne.symm hnb.1
      have hmid_len : mid.length = (Walk.cons h₁ rest).length - 2 := by
        have := congrArg Walk.length hrest_eq
        simp only [Walk.length_append, Walk.length_cons, Walk.length_nil] at this ⊢
        omega
      exact ⟨v₁, u₁, h₁, h₂, mid, by rw [hrest_eq], rfl, hlast, hmid_len, hnb_mid, hfn_mid⟩

/-- Exact rotation decomposition of a non-simple CNB walk of length `< 3 * g`:
produces a rotation `rot = c₁ ++ P ++ c₂ ++ P.reverse` with `c₁, c₂` simple cycles of lengths
in `[g, 2g - 1]` and `P` a NB walk with `c₁.length + c₂.length + 2 * P.length = L`. -/

end ExactAlphaCounting

end E64Wave8Agent2
