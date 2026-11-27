import Leaves
import Descent

/-!
An inclusion-minimal two-cut side of a cubic graph completes to a cubic
three-edge-connected graph. The side-minimality hypothesis is stated using
all nonempty proper subsets, so singleton cuts are included explicitly.
No bound on the number of vertices, cycle lengths, or search space occurs.
-/

namespace E64MinimalCut
open SimpleGraph Erdos64Closure E64Core E64Leaves Erdos64Descent
universe u

def Boundary {V : Type u} (G : SimpleGraph V) (S : Set V) :=
  {e : V × V // e.1 ∈ S ∧ e.2 ∉ S ∧ G.Adj e.1 e.2}

def SideMinimal {V : Type u} (G : SimpleGraph V) (A : Set V) : Prop :=
  ∀ T : Set V, T ⊆ A → T.Nonempty → T ≠ A → 3 ≤ Nat.card (Boundary G T)

def Completion {V : Type u} (G : SimpleGraph V) (A : Set V) (a b : A) :
    SimpleGraph A := G.induce A ⊔ SimpleGraph.edge a b

/-- A singleton cut has exactly the degree of its vertex. -/
theorem boundary_singleton_card {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (z : V) :
    Nat.card (Boundary G ({z} : Set V)) = G.degree z := by
  classical
  let e : Boundary G ({z} : Set V) ≃ G.neighborSet z :=
    { toFun := fun p => ⟨p.1.2, by
        have hp : p.1.1 = z := p.2.1
        simpa [hp] using p.2.2.2⟩
      invFun := fun p => ⟨(z, p.1), by
        refine ⟨by simp, ?_, p.2⟩
        intro hp
        have hp' : p.1 = z := hp
        exact G.ne_of_adj p.2 hp'.symm⟩
      left_inv := by
        intro p
        apply Subtype.ext
        exact Prod.ext (by exact p.2.1.symm) rfl
      right_inv := by intro p; rfl }
  calc
    Nat.card (Boundary G ({z} : Set V)) = Nat.card (G.neighborSet z) := Nat.card_congr e
    _ = G.degree z := by rw [Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree]

/-- Conventional inclusion-minimality among nontrivial cuts implies
`SideMinimal`: cubicity handles the singleton cases that the DAG excludes. -/
theorem side_minimal_of_nontrivial_minimal {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : Cubic G) (A : Set V)
    (hAc : 2 ≤ Nat.card (Aᶜ : Set V))
    (hmin : ∀ T : Set V, T ⊆ A → T ≠ A →
      2 ≤ Nat.card T → 2 ≤ Nat.card (Tᶜ : Set V) →
      Nat.card (Boundary G T) ≤ 2 → False) : SideMinimal G A := by
  classical
  intro T hTA hT hne
  by_contra hn
  have hc : Nat.card (Boundary G T) ≤ 2 := by omega
  have hTc : 2 ≤ Nat.card (Tᶜ : Set V) := by
    let f : (Aᶜ : Set V) → (Tᶜ : Set V) := fun z => ⟨z.1, fun hz => z.2 (hTA hz)⟩
    have hf : Function.Injective f := by
      intro p q h
      exact Subtype.ext (congrArg Subtype.val h)
    exact hAc.trans (Nat.card_le_card_of_injective f hf)
  by_cases hT2 : 2 ≤ Nat.card T
  · exact hmin T hTA hne hT2 hTc hc
  obtain ⟨z, hz⟩ := hT
  have huniq : ∀ v ∈ T, v = z := by
    intro v hv
    by_contra hvz
    let f : Bool → T := fun b => if b then ⟨v, hv⟩ else ⟨z, hz⟩
    have hf : Function.Injective f := by
      intro p q hpq
      cases p <;> cases q <;> simp_all [f, Subtype.ext_iff]
    have hcard := Nat.card_le_card_of_injective f hf
    have hbool : Nat.card Bool = 2 := by rw [Nat.card_eq_fintype_card]; decide
    omega
  have hTsing : T = {z} := by
    ext v
    constructor
    · intro hv; exact huniq v hv
    · intro hv
      have hvz : v = z := hv
      exact hvz.symm ▸ hz
  rw [hTsing, boundary_singleton_card, hG z] at hc
  omega

private theorem third_unique {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {a b c x y : V}
    (ha : G.degree a = 3) (hab : G.Adj a b) (hac : G.Adj a c) (hbc : b ≠ c)
    (hax : G.Adj a x) (hay : G.Adj a y)
    (hxb : x ≠ b) (hxc : x ≠ c) (hyb : y ≠ b) (hyc : y ≠ c) : x = y := by
  classical
  by_contra hxy
  have hs : ({b, c, x, y} : Finset V) ⊆ G.neighborFinset a := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact (G.mem_neighborFinset a _).mpr hab
    · exact (G.mem_neighborFinset a _).mpr hac
    · exact (G.mem_neighborFinset a _).mpr hax
    · exact (G.mem_neighborFinset a _).mpr hay
  have hc := Finset.card_le_card hs
  have h4 : ({b, c, x, y} : Finset V).card = 4 := by
    simp [hbc, Ne.symm hxb, Ne.symm hxc, Ne.symm hyb, Ne.symm hyc, hxy]
  rw [h4, G.card_neighborFinset_eq_degree, ha] at hc
  omega

/-- Minimality itself prevents the two ports from already being adjacent. -/
theorem minimal_side_ports_nonadjacent {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : Cubic G)
    (A : Set V) (a b : A) (hab : a ≠ b) (x y : V)
    (hx : x ∉ A) (hy : y ∉ A) (hax : G.Adj a.1 x) (hby : G.Adj b.1 y)
    (hcut : ∀ z : A, ∀ t : V, t ∉ A → G.Adj z.1 t →
      (z = a ∧ t = x) ∨ (z = b ∧ t = y))
    (hmin : SideMinimal G A) : ¬ G.Adj a.1 b.1 := by
  classical
  intro hadj
  have habv : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
  let T : Set V := {z | z ∈ A ∧ z ≠ a.1 ∧ z ≠ b.1}
  have hTsub : T ⊆ A := fun z hz => hz.1
  have hTne : T.Nonempty := by
    by_contra hn
    have hs : G.neighborFinset a.1 ⊆ {b.1, x} := by
      intro z hz
      have haz := (G.mem_neighborFinset a.1 z).mp hz
      by_cases hzA : z ∈ A
      · by_cases hzb : z = b.1
        · simp [hzb]
        · have hza : z ≠ a.1 := (G.ne_of_adj haz).symm
          exact False.elim (hn ⟨z, hzA, hza, hzb⟩)
      · rcases hcut a z hzA haz with ⟨_, rfl⟩ | ⟨ha, _⟩
        · simp
        · exact False.elim (hab ha)
    have hc := Finset.card_le_card hs
    have hb_x : b.1 ≠ x := fun h => hx (h ▸ b.2)
    rw [G.card_neighborFinset_eq_degree, hG a.1] at hc
    have hp : ({b.1, x} : Finset V).card = 2 := by simp [hb_x]
    omega
  have hTproper : T ≠ A := by
    intro h
    have haT : a.1 ∈ T := h.symm ▸ a.2
    exact haT.2.1 rfl
  have hend (e : Boundary G T) : e.1.2 = a.1 ∨ e.1.2 = b.1 := by
    by_cases hEA : e.1.2 ∈ A
    · by_contra h
      push Not at h
      exact e.2.2.1 ⟨hEA, h.1, h.2⟩
    · rcases hcut ⟨e.1.1, e.2.1.1⟩ e.1.2 hEA e.2.2.2 with ⟨h, _⟩ | ⟨h, _⟩
      · exact False.elim (e.2.1.2.1 (congrArg Subtype.val h))
      · exact False.elim (e.2.1.2.2 (congrArg Subtype.val h))
  let f : Boundary G T → Bool := fun e => if e.1.2 = a.1 then true else false
  have hf : Function.Injective f := by
    intro p q hpq
    have hends : p.1.2 = q.1.2 := by
      rcases hend p with hp | hp <;> rcases hend q with hq | hq
      · exact hp.trans hq.symm
      · simp [f, hp, hq, habv.symm] at hpq
      · simp [f, hp, hq, habv.symm] at hpq
      · exact hp.trans hq.symm
    apply Subtype.ext
    apply Prod.ext
    · rcases hend p with hp | hp
      · have hq : q.1.2 = a.1 := hends.symm.trans hp
        apply third_unique G (hG a.1) hadj hax
          (fun h => hx (h ▸ b.2))
        · simpa [hp] using p.2.2.2.symm
        · simpa [hq] using q.2.2.2.symm
        · exact p.2.1.2.2
        · exact fun h => hx (h ▸ p.2.1.1)
        · exact q.2.1.2.2
        · exact fun h => hx (h ▸ q.2.1.1)
      · have hq : q.1.2 = b.1 := hends.symm.trans hp
        apply third_unique G (hG b.1) hadj.symm hby
          (fun h => hy (h ▸ a.2))
        · simpa [hp] using p.2.2.2.symm
        · simpa [hq] using q.2.2.2.symm
        · exact p.2.1.2.1
        · exact fun h => hy (h ▸ p.2.1.1)
        · exact q.2.1.2.1
        · exact fun h => hy (h ▸ q.2.1.1)
    · exact hends
  have hc := Nat.card_le_card_of_injective f hf
  have hb : Nat.card Bool = 2 := by rw [Nat.card_eq_fintype_card]; decide
  have hl := hmin T hTsub hTne hTproper
  omega

private theorem induce_degree_add_out {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Set V) [DecidablePred (· ∈ A)]
    [DecidableRel (G.induce A).Adj] (v : A) :
    (G.induce A).degree v + ((G.neighborFinset v.1).filter (fun x => x ∉ A)).card =
      G.degree v.1 := by
  classical
  let e : G.neighborSet v.1 ≃
      (G.induce A).neighborSet v ⊕ {x : V // x ∈ (G.neighborFinset v.1).filter (fun x => x ∉ A)} :=
    { toFun := fun z =>
        if h : z.1 ∈ A then Sum.inl ⟨⟨z.1, h⟩, z.2⟩
        else Sum.inr ⟨z.1, Finset.mem_filter.mpr ⟨(G.mem_neighborFinset v.1 z.1).mpr z.2, h⟩⟩
      invFun := Sum.elim (fun z => ⟨z.1.1, z.2⟩)
        (fun z => ⟨z.1, (G.mem_neighborFinset v.1 z.1).mp (Finset.mem_filter.mp z.2).1⟩)
      left_inv := by intro z; by_cases h : z.1 ∈ A <;> simp [h]
      right_inv := by
        rintro (z | z)
        · simp [z.1.2]
        · have hn : z.1 ∉ A := (Finset.mem_filter.mp z.2).2
          simp [hn] }
  have hc := Fintype.card_congr e
  rw [SimpleGraph.card_neighborSet_eq_degree, Fintype.card_sum,
    SimpleGraph.card_neighborSet_eq_degree, Fintype.card_coe] at hc
  exact hc.symm

/-- The virtual edge restores the two missing degrees exactly. -/
theorem completion_cubic {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : Cubic G)
    (A : Set V) [DecidablePred (· ∈ A)] (a b : A) (hab : a ≠ b) (x y : V)
    (hx : x ∉ A) (hy : y ∉ A) (hax : G.Adj a.1 x) (hby : G.Adj b.1 y)
    (hcut : ∀ z : A, ∀ t : V, t ∉ A → G.Adj z.1 t →
      (z = a ∧ t = x) ∨ (z = b ∧ t = y))
    (hnadj : ¬ G.Adj a.1 b.1) :
    @Cubic A _ (Completion G A a b) (Classical.decRel _) := by
  classical
  let K := G.induce A
  let H := Completion G A a b
  have hout_a : ((G.neighborFinset a.1).filter (fun z => z ∉ A)) = {x} := by
    ext z
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
    constructor
    · rintro ⟨haz, hz⟩
      rcases hcut a z hz haz with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · exact False.elim (hab h)
    · rintro rfl; exact ⟨hax, hx⟩
  have hout_b : ((G.neighborFinset b.1).filter (fun z => z ∉ A)) = {y} := by
    ext z
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
    constructor
    · rintro ⟨hbz, hz⟩
      rcases hcut b z hz hbz with ⟨h, _⟩ | ⟨_, h⟩
      · exact False.elim (hab h.symm)
      · exact h
    · rintro rfl; exact ⟨hby, hy⟩
  intro v
  by_cases hva : v = a
  · subst v
    have hd := induce_degree_add_out G A a
    rw [hout_a, Finset.card_singleton, hG a.1] at hd
    have ha := degree_add_new_edge_left K a b hab hnadj
    change H.degree a = 3
    change H.degree a = K.degree a + 1 at ha
    exact ha.trans hd
  by_cases hvb : v = b
  · subst v
    have hd := induce_degree_add_out G A b
    rw [hout_b, Finset.card_singleton, hG b.1] at hd
    have hb := degree_add_new_edge_right K a b hab hnadj
    change H.degree b = 3
    change H.degree b = K.degree b + 1 at hb
    exact hb.trans hd
  have hout : ((G.neighborFinset v.1).filter (fun z => z ∉ A)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro z hz hn
    rcases hcut v z hn ((G.mem_neighborFinset v.1 z).mp hz) with ⟨h, _⟩ | ⟨h, _⟩
    · exact hva h
    · exact hvb h
  have hd := induce_degree_add_out G A v
  rw [hout, Finset.card_empty, add_zero, hG v.1] at hd
  have hn : H.neighborFinset v = K.neighborFinset v := by
    ext z
    simp [H, Completion, K, SimpleGraph.edge_adj, hva, hvb]
  change H.degree v = 3
  rw [← H.card_neighborFinset_eq_degree, hn, K.card_neighborFinset_eq_degree]
  exact hd

private def liftSide {V : Type u} {A : Set V} (S : Set A) : Set V :=
  Subtype.val '' S

private theorem mem_liftSide {V : Type u} {A : Set V} (S : Set A) (z : A) :
    z.1 ∈ liftSide S ↔ z ∈ S := by
  constructor
  · rintro ⟨t, ht, htz⟩
    exact (Subtype.ext htz : t = z) ▸ ht
  · intro hz; exact ⟨z, hz, rfl⟩

private theorem boundary_compl_card {V : Type u} (G : SimpleGraph V) (S : Set V) :
    Nat.card (Boundary G Sᶜ) = Nat.card (Boundary G S) := by
  classical
  let e : Boundary G Sᶜ ≃ Boundary G S :=
    { toFun := fun p => ⟨(p.1.2, p.1.1), by
        exact ⟨by simpa using p.2.2.1, p.2.1, p.2.2.2.symm⟩⟩
      invFun := fun p => ⟨(p.1.2, p.1.1), by
        exact ⟨p.2.2.1, by simpa using p.2.1, p.2.2.2.symm⟩⟩
      left_inv := by intro p; apply Subtype.ext; rfl
      right_inv := by intro p; apply Subtype.ext; rfl }
  exact Nat.card_congr e

/-- With the second port outside S, every original boundary edge injects
into a boundary edge of the completed side. -/
theorem cut_into_completion {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Set V)
    (a b : A) (hab : a ≠ b) (x y : V)
    (hcut : ∀ z : A, ∀ t : V, t ∉ A → G.Adj z.1 t →
      (z = a ∧ t = x) ∨ (z = b ∧ t = y))
    (hnadj : ¬ G.Adj a.1 b.1) (S : Set A) (hbS : b ∉ S) :
    Nat.card (Boundary G (liftSide S)) ≤ Nat.card (Boundary (Completion G A a b) S) := by
  classical
  let T := liftSide S
  let H := Completion G A a b
  have hTsub : T ⊆ A := by rintro z ⟨t, _, rfl⟩; exact t.2
  have hfirst (p : Boundary G T) : (⟨p.1.1, hTsub p.2.1⟩ : A) ∈ S :=
    (mem_liftSide S _).mp p.2.1
  have hout (p : Boundary G T) (h : p.1.2 ∉ A) :
      p.1.1 = a.1 ∧ p.1.2 = x := by
    rcases hcut ⟨p.1.1, hTsub p.2.1⟩ p.1.2 h p.2.2.2 with ⟨hp, ht⟩ | ⟨hp, _⟩
    · exact ⟨congrArg Subtype.val hp, ht⟩
    · exact False.elim (hbS (hp ▸ hfirst p))
  let f : Boundary G T → Boundary H S := fun p =>
    if hp : p.1.2 ∈ A then
      ⟨(⟨p.1.1, hTsub p.2.1⟩, ⟨p.1.2, hp⟩), hfirst p,
        fun hz => p.2.2.1 ((mem_liftSide S _).mpr hz),
        Or.inl p.2.2.2⟩
    else
      ⟨(a, b), by
        have haS : a ∈ S := by
          have ha : (⟨p.1.1, hTsub p.2.1⟩ : A) = a := Subtype.ext (hout p hp).1
          exact ha ▸ hfirst p
        exact ⟨haS, hbS, Or.inr ((SimpleGraph.edge_adj a b a b).mpr
          ⟨Or.inl ⟨rfl, rfl⟩, hab⟩)⟩⟩
  have hf : Function.Injective f := by
    intro p q hpq
    have hfirsteq := congrArg (fun z : Boundary H S => z.1.1.1) hpq
    have hsecondeq := congrArg (fun z : Boundary H S => z.1.2.1) hpq
    by_cases hp : p.1.2 ∈ A <;> by_cases hq : q.1.2 ∈ A
    · simp only [f, hp, hq, ↓reduceDIte] at hfirsteq hsecondeq
      exact Subtype.ext (Prod.ext hfirsteq hsecondeq)
    · simp only [f, hp, hq, ↓reduceDIte] at hfirsteq hsecondeq
      exact False.elim (hnadj (by rw [← hfirsteq, ← hsecondeq]; exact p.2.2.2))
    · simp only [f, hp, hq, ↓reduceDIte] at hfirsteq hsecondeq
      exact False.elim (hnadj (by rw [hfirsteq, hsecondeq]; exact q.2.2.2))
    · have hpo := hout p hp
      have hqo := hout q hq
      exact Subtype.ext (Prod.ext (hpo.1.trans hqo.1.symm) (hpo.2.trans hqo.2.symm))
  exact Nat.card_le_card_of_injective f hf

/-- Every nonempty proper cut in the completed side has at least three edges. -/
theorem minimal_side_completion_three_edge_connected
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Set V)
    (a b : A) (hab : a ≠ b) (x y : V)
    (hcut : ∀ z : A, ∀ t : V, t ∉ A → G.Adj z.1 t →
      (z = a ∧ t = x) ∨ (z = b ∧ t = y))
    (hnadj : ¬ G.Adj a.1 b.1) (hmin : SideMinimal G A)
    (S : Set A) (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) :
    3 ≤ Nat.card (Boundary (Completion G A a b) S) := by
  classical
  have side_bound : ∀ R : Set A, R.Nonempty → b ∉ R →
      3 ≤ Nat.card (Boundary (Completion G A a b) R) := by
    intro R hR hbR
    have hsub : liftSide R ⊆ A := by rintro z ⟨t, _, rfl⟩; exact t.2
    have hne : (liftSide R).Nonempty := by
      obtain ⟨z, hz⟩ := hR
      exact ⟨z.1, (mem_liftSide R z).mpr hz⟩
    have hproper : liftSide R ≠ A := by
      intro h
      have hb : b.1 ∈ liftSide R := h.symm ▸ b.2
      exact hbR ((mem_liftSide R b).mp hb)
    exact (hmin _ hsub hne hproper).trans (cut_into_completion G A a b hab x y hcut hnadj R hbR)
  by_cases hbS : b ∈ S
  · have hh := side_bound Sᶜ hSc (by simpa using hbS)
    rwa [boundary_compl_card] at hh
  · exact side_bound S hS hbS

/-- Combined all-order completion theorem. MinimalBad is not needed here:
the assertion holds for every cubic graph with the stated minimal side. -/
theorem minimal_cut_completion {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : Cubic G)
    (A : Set V) [DecidablePred (· ∈ A)] (a b : A) (hab : a ≠ b) (x y : V)
    (hx : x ∉ A) (hy : y ∉ A) (hax : G.Adj a.1 x) (hby : G.Adj b.1 y)
    (hcut : ∀ z : A, ∀ t : V, t ∉ A → G.Adj z.1 t →
      (z = a ∧ t = x) ∨ (z = b ∧ t = y))
    (hmin : SideMinimal G A) :
    ¬G.Adj a.1 b.1 ∧
    @Cubic A _ (Completion G A a b) (Classical.decRel _) ∧
    ∀ S : Set A, S.Nonempty → Sᶜ.Nonempty →
      3 ≤ Nat.card (Boundary (Completion G A a b) S) := by
  have hnadj := minimal_side_ports_nonadjacent G hG A a b hab x y hx hy hax hby hcut hmin
  exact ⟨hnadj, completion_cubic G hG A a b hab x y hx hy hax hby hcut hnadj,
    minimal_side_completion_three_edge_connected G A a b hab x y hcut hnadj hmin⟩

/-- The completion theorem with exactly the DAG's nontrivial-cut convention. -/
theorem minimal_nontrivial_cut_completion {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : Cubic G)
    (A : Set V) [DecidablePred (· ∈ A)] (a b : A) (hab : a ≠ b) (x y : V)
    (hx : x ∉ A) (hy : y ∉ A) (hax : G.Adj a.1 x) (hby : G.Adj b.1 y)
    (hcut : ∀ z : A, ∀ t : V, t ∉ A → G.Adj z.1 t →
      (z = a ∧ t = x) ∨ (z = b ∧ t = y))
    (hAc : 2 ≤ Nat.card (Aᶜ : Set V))
    (hmin : ∀ T : Set V, T ⊆ A → T ≠ A →
      2 ≤ Nat.card T → 2 ≤ Nat.card (Tᶜ : Set V) →
      Nat.card (Boundary G T) ≤ 2 → False) :
    ¬G.Adj a.1 b.1 ∧
    @Cubic A _ (Completion G A a b) (Classical.decRel _) ∧
    ∀ S : Set A, S.Nonempty → Sᶜ.Nonempty →
      3 ≤ Nat.card (Boundary (Completion G A a b) S) := by
  exact minimal_cut_completion G hG A a b hab x y hx hy hax hby hcut
    (side_minimal_of_nontrivial_minimal G hG A hAc hmin)

#print axioms boundary_singleton_card
#print axioms side_minimal_of_nontrivial_minimal
#print axioms minimal_side_ports_nonadjacent
#print axioms completion_cubic
#print axioms cut_into_completion
#print axioms minimal_side_completion_three_edge_connected
#print axioms minimal_cut_completion
#print axioms minimal_nontrivial_cut_completion

end E64MinimalCut
