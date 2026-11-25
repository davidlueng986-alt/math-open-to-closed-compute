import PairedShadow

namespace E64Triangle
open SimpleGraph Erdos64Closure Erdos64Paired
universe u

variable {V : Type u} [Fintype V]

theorem third_neighbor (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b c : V) (ha : 3≤G.degree a) :
    ∃ x, G.Adj a x ∧ x≠a ∧ x≠b ∧ x≠c := by
  classical
  by_contra h
  have hs : G.neighborFinset a ⊆ ({b,c} : Finset V) := by
    intro x hx
    have hadj := (G.mem_neighborFinset a x).mp hx
    by_cases hb : x=b
    · simp [hb]
    by_cases hc : x=c
    · simp [hc]
    exact False.elim (h ⟨x,hadj,(G.ne_of_adj hadj).symm,hb,hc⟩)
  have hcard := Finset.card_le_card hs
  rw [G.card_neighborFinset_eq_degree] at hcard
  have h2 : ({b,c} : Finset V).card ≤ 2 := Finset.card_le_two
  omega

theorem exterior_unique (G : SimpleGraph V) [DecidableRel G.Adj]
    {a b c x y : V} (hdeg : G.degree a≤3)
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : b≠c)
    (hax : G.Adj a x) (hay : G.Adj a y)
    (hxb : x≠b) (hxc : x≠c) (hyb : y≠b) (hyc : y≠c) : x=y := by
  classical
  by_contra hxy
  have hs : ({b,c,x,y} : Finset V) ⊆ G.neighborFinset a := by
    intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact (G.mem_neighborFinset a _).mpr hab
    · exact (G.mem_neighborFinset a _).mpr hac
    · exact (G.mem_neighborFinset a _).mpr hax
    · exact (G.mem_neighborFinset a _).mpr hay
  have hc := Finset.card_le_card hs
  have h4 : ({b,c,x,y}:Finset V).card = 4 := by
    simp [hbc,Ne.symm hxb,Ne.symm hyb,Ne.symm hxc,Ne.symm hyc,hxy]
  rw [h4,G.card_neighborFinset_eq_degree] at hc
  omega

theorem nat_card_ge_two_of_ne {T : Type*} [Finite T] (a b : T) (h : a≠b) :
    2≤Nat.card T := by
  classical
  let f : Bool → T := fun z => if z then a else b
  have hf : Function.Injective f := by
    intro x y he
    cases x <;> cases y <;> simp_all [f]
  have hc := Nat.card_le_card_of_injective f hf
  have hb : Nat.card Bool=2 := by rw [Nat.card_eq_fintype_card]; decide
  omega

/-- Actual terminal cut obstruction: in a power-free graph, a triangle
whose degrees are <=3 and whose first two vertices are cubic has a
nontrivial cut of at most three edges. The conclusion is exactly the
SmallCut predicate used by the closure DAG. -/
theorem triangle_forces_cut (G : SimpleGraph V) [DecidableRel G.Adj]
    {a b c : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a)
    (ha : G.degree a=3) (hb : G.degree b=3) (hc : G.degree c≤3)
    (hfree : ¬HasPower G) :
    ∃ S : Set V, 2 ≤ Nat.card S ∧ 2 ≤ Nat.card (Sᶜ : Set V) ∧
      Nat.card {e : V × V // e.1 ∈ S ∧ e.2 ∉ S ∧ G.Adj e.1 e.2} ≤ 3 := by
  classical
  have habn := G.ne_of_adj hab
  have hbcn := G.ne_of_adj hbc
  have hcan := G.ne_of_adj hca
  obtain ⟨x,hax,hxa,hxb,hxc⟩ := third_neighbor G a b c (by omega)
  obtain ⟨y,hby,hyb,hyc,hya⟩ := third_neighbor G b c a (by omega)
  have hxy : x≠y := by
    intro he
    subst y
    exact hfree (rectangle_power G hcan.symm habn hxa.symm hbcn.symm hxc.symm hxb.symm
      hca.symm hbc.symm hby hax.symm)
  let S : Set V := {a,b,c}
  have hS3 : Nat.card S = 3 := by
    have hfin : S.Finite := Set.toFinite S
    rw [Nat.card_eq_card_finite_toFinset hfin]
    have he : hfin.toFinset = ({a,b,c} : Finset V) := by
      ext v
      simp [S]
    rw [he]
    simp [habn,hcan.symm,hbcn]
  have hx : x ∈ (Sᶜ : Set V) := by simp [S,hxa,hxb,hxc]
  have hy : y ∈ (Sᶜ : Set V) := by simp [S,hya,hyb,hyc]
  have hS2 : 2≤Nat.card (Sᶜ : Set V) :=
    nat_card_ge_two_of_ne ⟨x,hx⟩ ⟨y,hy⟩ (fun h => hxy (congrArg Subtype.val h))
  let B := {e : V×V // e.1∈S ∧ e.2∉S ∧ G.Adj e.1 e.2}
  let f : B → S := fun e => ⟨e.1.1,e.2.1⟩
  have hinj : Function.Injective f := by
    intro p q he
    have hfst : p.1.1=q.1.1 := congrArg Subtype.val he
    have hp : p.1.1=a ∨ p.1.1=b ∨ p.1.1=c := by simpa [S] using p.2.1
    have hpout : p.1.2≠a ∧ p.1.2≠b ∧ p.1.2≠c := by simpa [S] using p.2.2.1
    have hqout : q.1.2≠a ∧ q.1.2≠b ∧ q.1.2≠c := by simpa [S] using q.2.2.1
    have hqedge : G.Adj p.1.1 q.1.2 := hfst ▸ q.2.2.2
    have hpedge := p.2.2.2
    have hsnd : p.1.2=q.1.2 := by
      rcases hp with hp | hp | hp
      · rw [hp] at hpedge hqedge
        exact exterior_unique G (by omega) hab hca.symm hbcn hpedge hqedge
          hpout.2.1 hpout.2.2 hqout.2.1 hqout.2.2
      · rw [hp] at hpedge hqedge
        exact exterior_unique G (by omega) hab.symm hbc hcan.symm hpedge hqedge
          hpout.1 hpout.2.2 hqout.1 hqout.2.2
      · rw [hp] at hpedge hqedge
        exact exterior_unique G hc hca hbc.symm habn hpedge hqedge
          hpout.1 hpout.2.1 hqout.1 hqout.2.1
    exact Subtype.ext (Prod.ext hfst hsnd)
  have hcut := Nat.card_le_card_of_injective f hinj
  refine ⟨S,by omega,hS2,?_⟩
  change Nat.card B≤3
  omega

/-- Both full subcubic triangle/core leaves are eliminated by this result.
    The designated w may itself have degree three (cubic case). -/
theorem near_subcubic_triangle_cut (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V) (hmax : ∀ v, G.degree v≤3)
    (hdeg : ∀ v, v≠w → G.degree v=3)
    (htri : ∃ a b c, G.Adj a b ∧ G.Adj b c ∧ G.Adj c a)
    (hfree : ¬HasPower G) :
    ∃ S : Set V, 2 ≤ Nat.card S ∧ 2 ≤ Nat.card (Sᶜ : Set V) ∧
      Nat.card {e : V × V // e.1 ∈ S ∧ e.2 ∉ S ∧ G.Adj e.1 e.2} ≤ 3 := by
  classical
  obtain ⟨a,b,c,hab,hbc,hca⟩ := htri
  by_cases ha : a=w
  · subst w
    exact triangle_forces_cut G hbc hca hab
      (hdeg b (G.ne_of_adj hab).symm)
      (hdeg c (G.ne_of_adj hca)) (hmax a) hfree
  · by_cases hb : b=w
    · subst w
      exact triangle_forces_cut G hca hab hbc
        (hdeg c (G.ne_of_adj hbc).symm)
        (hdeg a (G.ne_of_adj hab)) (hmax b) hfree
    · exact triangle_forces_cut G hab hbc hca
        (hdeg a ha) (hdeg b hb) (hmax c) hfree

#print axioms near_subcubic_triangle_cut
#print axioms third_neighbor
#print axioms exterior_unique
#print axioms triangle_forces_cut
end E64Triangle

