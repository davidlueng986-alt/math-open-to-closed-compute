import Shadow
import NonBacktrackingGirth
import Wave5Agent5GirthTripling
import Wave5Agent6ChebyshevGirth
import ChebTraceEngine
import NonSimpleHelpers
import NonSimpleDecomp

namespace E64Wave8Agent2
open SimpleGraph Erdos64Closure E64NonBacktrackingGirth E64Wave5Agent5 E64Wave5Agent6

section NonSimpleBarbell

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Barbell Non-Simple Walk Upper Bound**:
In any cubic, power-free graph `G` of girth `g ≥ 6` and `L = 2^k < 3*g` (`4 ≤ k ≤ 6`),
the barbell non-simple CNB walks of length `L` satisfy
`NS_bar.card ≤ ∑ r ∈ range L, barbellTerm g L r * taillessCount G r`. -/
theorem nonSimple_barbell_card_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {g k : ℕ} (hreg : ∀ v : V, G.degree v = 3) (hg : GirthAtLeast G g) (hg6 : 6 ≤ g)
    (hnp : ¬ HasPower G) (hk4 : 4 ≤ k) (hk6 : k ≤ 6) (hLt : 2 ^ k < 3 * g) :
    let L := 2 ^ k
    haveI : DecidablePred (fun x : Σ v : V, {p : G.Walk v v // p.length = L} =>
      IsCyclicallyNonBacktracking x.2.1 ∧ ¬ x.2.1.IsCycle) := Classical.decPred _
    let NS := ((Finset.univ : Finset V).sigma fun v => nbWalksSub G L v v).filter
      fun x => IsCyclicallyNonBacktracking x.2.1 ∧ ¬ x.2.1.IsCycle
    haveI : DecidablePred (isBarbellElem G g L) := Classical.decPred _
    (NS.filter (isBarbellElem G g L)).card ≤
      ∑ r ∈ Finset.range L, barbellTerm g L r * taillessCount G r := by
  intro L NS
  set s := (g - 1) / 2
  have hL1 : 1 ≤ L := Nat.one_le_two_pow
  have hnot_pow2_cycle : ∀ {z : V} (c : G.Walk z z), c.IsCycle → ¬ isPow2Small c.length = true := by
    intro z c hc hp2
    obtain ⟨m, hm, hlen⟩ := isPow2Small_spec hp2
    exact hnp ⟨m, z, c, hm, hc, hlen⟩
  let TL (r : ℕ) := ((Finset.univ : Finset V).sigma fun v => nbWalksSub G r v v).filter
    fun x => IsCyclicallyNonBacktracking x.2.1
  have hTL_card : ∀ r, (TL r).card = taillessCount G r := fun r =>
    taillessCount_eq_card_sub G r
  let NS_bar := NS.filter (isBarbellElem G g L)
  change NS_bar.card ≤ _
  let isBarPR (p r₁ : ℕ) (x : Σ v : V, {q : G.Walk v v // q.length = L}) : Prop :=
    ∃ (j : Fin L) (u w : V) (c₁ : G.Walk u u) (P : G.Walk u w) (c₂ : G.Walk w w),
      P.length = p ∧ c₁.length = r₁ ∧
      1 ≤ p ∧ 2 * g ≤ L - 2 * p ∧
      g ≤ r₁ ∧ r₁ ≤ L - 2 * p - r₁ ∧
      ¬ isPow2Small r₁ ∧ ¬ isPow2Small (L - 2 * p - r₁) ∧
      c₁.IsCycle ∧ c₂.IsCycle ∧
      c₁.length + c₂.length + 2 * P.length = L ∧
      IsCyclicallyNonBacktracking (c₁.append (P.append (c₂.append P.reverse))) ∧
      unrotate L j (c₁.append (P.append (c₂.append P.reverse)))
        (by simp only [Walk.length_append, Walk.length_reverse]; omega) = x
  have hbar_cover : NS_bar ⊆ (Finset.range L).biUnion fun r₁ =>
      ((Finset.range (L / 2)).filter fun p => 1 ≤ p ∧ 2 * g ≤ L - 2 * p).biUnion fun p =>
        NS_bar.filter (isBarPR p r₁) := by
    intro x hx
    simp only [NS_bar, Finset.mem_filter] at hx
    obtain ⟨j, u, w, c₁, P, c₂, hPp, hc₁, hc₂, hg₁, hle12, hlen, hrc, hunr⟩ := hx.2
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
    refine ⟨c₁.length, by omega, P.length, ⟨by omega, hPp, by omega⟩, ⟨hx.1, hx.2⟩, ?_⟩
    have hr₂_eq : c₂.length = L - 2 * P.length - c₁.length := by omega
    exact ⟨j, u, w, c₁, P, c₂, rfl, rfl, hPp, by omega, hg₁, by omega,
      hnot_pow2_cycle c₁ hc₁, hr₂_eq ▸ hnot_pow2_cycle c₂ hc₂, hc₁, hc₂, hlen, hrc, hunr⟩
  refine le_trans (Finset.card_le_card hbar_cover) ?_
  refine le_trans Finset.card_biUnion_le ?_
  refine Finset.sum_le_sum fun r₁ _ => ?_
  refine le_trans Finset.card_biUnion_le ?_
  unfold barbellTerm
  have hlist_filt : ∀ (n : ℕ) (pred : ℕ → Bool) (f : ℕ → ℕ),
      (((List.range n).filter pred).map f).sum =
        ∑ p ∈ (Finset.range n).filter (fun p => pred p = true), f p := by
    intro n pred f
    induction n with
    | zero => simp
    | succ n ih =>
        rw [List.range_succ, List.filter_append, List.map_append, List.sum_append, ih,
            Finset.range_succ, Finset.filter_insert]
        by_cases h : pred n = true
        · simp [h, Finset.sum_insert, add_comm]
        · simp [h]
  have hbar_sum : ((((List.range (L / 2)).filter fun p =>
        decide (1 ≤ p ∧ 2 * g ≤ L - 2 * p)).map (fun p =>
          let r₂ := L - 2 * p - r₁
          if g ≤ r₁ ∧ r₁ ≤ r₂ ∧ ¬ isPow2Small r₁ ∧ ¬ isPow2Small r₂ then
            (if r₁ = r₂ then L else 2 * L) * 2 ^ (p - 1 + (r₂ - 2 - s))
          else 0)).sum) * taillessCount G r₁ =
      ∑ p ∈ (Finset.range (L / 2)).filter (fun p => 1 ≤ p ∧ 2 * g ≤ L - 2 * p),
        (if g ≤ r₁ ∧ r₁ ≤ L - 2 * p - r₁ ∧ ¬ isPow2Small r₁ ∧ ¬ isPow2Small (L - 2 * p - r₁) then
          (if r₁ = L - 2 * p - r₁ then L else 2 * L) * 2 ^ (p - 1 + (L - 2 * p - r₁ - 2 - s))
        else 0) * taillessCount G r₁ := by
    rw [hlist_filt, Finset.sum_mul]
    congr 1
    ext p; simp
  rw [show ((((List.range (L / 2)).filter fun p => 1 ≤ p ∧ 2 * g ≤ L - 2 * p).map fun p =>
        let r₂ := L - 2 * p - r₁
        if g ≤ r₁ ∧ r₁ ≤ r₂ ∧ ¬ isPow2Small r₁ ∧ ¬ isPow2Small r₂ then
          (if r₁ = r₂ then L else 2 * L) * 2 ^ (p - 1 + (r₂ - 2 - s))
        else 0).sum) * taillessCount G r₁ =
      ∑ p ∈ (Finset.range (L / 2)).filter (fun p => 1 ≤ p ∧ 2 * g ≤ L - 2 * p),
        (if g ≤ r₁ ∧ r₁ ≤ L - 2 * p - r₁ ∧ ¬ isPow2Small r₁ ∧ ¬ isPow2Small (L - 2 * p - r₁) then
          (if r₁ = L - 2 * p - r₁ then L else 2 * L) * 2 ^ (p - 1 + (L - 2 * p - r₁ - 2 - s))
        else 0) * taillessCount G r₁ from hbar_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  simp only [Finset.mem_filter, Finset.mem_range] at hp
  set r₂ := L - 2 * p - r₁
  by_cases hcond : g ≤ r₁ ∧ r₁ ≤ r₂ ∧ ¬ isPow2Small r₁ ∧ ¬ isPow2Small r₂
  · simp only [hcond, ↓reduceIte]
    let S_pr := NS_bar.filter (isBarPR p r₁)
    let u3Set (c1 : Σ u : V, {q : G.Walk u u // q.length = r₁}) : Finset V :=
      ((G.neighborFinset c1.1).erase c1.2.1.snd).erase c1.2.1.reverse.snd
    let Param :=
      (Finset.univ : Finset (Fin L)).sigma fun _ =>
      (TL r₁).sigma fun c1 =>
      (u3Set c1).sigma fun u3 =>
      (nbWalksAvoid G (p - 1) u3 c1.1).sigma fun Pw =>
      let prevW := if h0 : p - 1 = 0 then c1.1 else Pw.2.1.reverse.snd
      ((G.neighborFinset Pw.1).erase prevW).sigma fun v1 =>
      (((G.neighborFinset Pw.1).erase prevW).erase v1).sigma fun v2 =>
      nbWalksBetweenAvoid G (r₂ - 2) v1 Pw.1 v2
    have hParam_card : Param.card ≤ 2 * L * 2 ^ (p - 1 + (r₂ - 2 - s)) * taillessCount G r₁ := by
      simp only [Param, Finset.card_sigma, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul]
      have hinner : ∀ c1 ∈ TL r₁,
          (∑ u3 ∈ u3Set c1,
            ∑ Pw ∈ nbWalksAvoid G (p - 1) u3 c1.1,
              let prevW := if p - 1 = 0 then c1.1 else Pw.2.1.reverse.snd
              ∑ v1 ∈ (G.neighborFinset Pw.1).erase prevW,
                ∑ v2 ∈ ((G.neighborFinset Pw.1).erase prevW).erase v1,
                  (nbWalksBetweenAvoid G (r₂ - 2) v1 Pw.1 v2).card) ≤
          2 * 2 ^ (p - 1 + (r₂ - 2 - s)) := by
        intro c1 hc1_mem
        have hu3_card : (u3Set c1).card ≤ 1 := by
          simp only [TL, Finset.mem_filter, Finset.mem_sigma, Finset.mem_univ, true_and, mem_nbWalksSub_iff] at hc1_mem
          have hcyc1 := hc1_mem.2
          have hsnd_adj : G.Adj c1.1 c1.2.1.snd := by
            cases hq : c1.2.1 with
            | nil => have := c1.2.2; rw [hq] at this; simp at this; omega
            | cons h _ => exact h
          have hrev_adj : G.Adj c1.1 c1.2.1.reverse.snd := by
            cases hq : c1.2.1.reverse with
            | nil =>
                have := Walk.length_reverse c1.2.1; rw [hq] at this; simp at this
                have := c1.2.2; omega
            | cons h _ => exact h
          have hne_sr : c1.2.1.snd ≠ c1.2.1.reverse.snd := by
            intro heq
            have hf : firstNbr c1.2.1 = some c1.2.1.snd := by
              cases hq : c1.2.1 with
              | nil => have := c1.2.2; rw [hq] at this; simp at this; omega
              | cons _ _ => rfl
            have hl : lastNbr c1.2.1 = some c1.2.1.reverse.snd := by
              rw [← firstNbr_reverse]
              cases hq : c1.2.1.reverse with
              | nil =>
                  have := Walk.length_reverse c1.2.1; rw [hq] at this; simp at this
                  have := c1.2.2; omega
              | cons _ _ => rfl
            exact ((isNonBacktracking_append_iff c1.2.1 c1.2.1).mp hcyc1).2.2 _ _ hl hf heq.symm
          have hmem2 : c1.2.1.reverse.snd ∈ (G.neighborFinset c1.1).erase c1.2.1.snd :=
            Finset.mem_erase.mpr ⟨hne_sr.symm, (G.mem_neighborFinset _ _).mpr hrev_adj⟩
          dsimp only [u3Set]
          rw [Finset.card_erase_of_mem hmem2,
              Finset.card_erase_of_mem ((G.mem_neighborFinset _ _).mpr hsnd_adj),
              G.card_neighborFinset_eq_degree, hreg c1.1]
        have hu3_each : ∀ u3 ∈ u3Set c1,
            (∑ Pw ∈ nbWalksAvoid G (p - 1) u3 c1.1,
              let prevW := if p - 1 = 0 then c1.1 else Pw.2.1.reverse.snd
              ∑ v1 ∈ (G.neighborFinset Pw.1).erase prevW,
                ∑ v2 ∈ ((G.neighborFinset Pw.1).erase prevW).erase v1,
                  (nbWalksBetweenAvoid G (r₂ - 2) v1 Pw.1 v2).card) ≤
            2 * 2 ^ (p - 1 + (r₂ - 2 - s)) := by
          intro u3 hu3
          have hu3_adj : G.Adj c1.1 u3 :=
            (G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp (Finset.mem_erase.mp hu3).2).2
          have hPw_each : ∀ Pw ∈ nbWalksAvoid G (p - 1) u3 c1.1,
              (let prevW := if p - 1 = 0 then c1.1 else Pw.2.1.reverse.snd
               ∑ v1 ∈ (G.neighborFinset Pw.1).erase prevW,
                 ∑ v2 ∈ ((G.neighborFinset Pw.1).erase prevW).erase v1,
                   (nbWalksBetweenAvoid G (r₂ - 2) v1 Pw.1 v2).card) ≤
              2 * 2 ^ (r₂ - 2 - s) := by
            intro Pw hPw
            dsimp only
            set prevW := if p - 1 = 0 then c1.1 else Pw.2.1.reverse.snd
            have hprevW_adj : G.Adj Pw.1 prevW := by
              by_cases hp0 : p - 1 = 0
              · simp only [prevW, hp0, ↓reduceIte]
                cases hq : Pw.2.1 with
                | nil => exact hu3_adj.symm
                | cons _ _ => have := Pw.2.2; rw [hq] at this; simp at this; omega
              · simp only [prevW, hp0, ↓reduceIte]
                cases hq : Pw.2.1.reverse with
                | nil =>
                    have := Walk.length_reverse Pw.2.1; rw [hq] at this; simp at this
                    have := Pw.2.2; omega
                | cons h _ => exact h
            have hv1_each : ∀ v1 ∈ (G.neighborFinset Pw.1).erase prevW,
                (∑ v2 ∈ ((G.neighborFinset Pw.1).erase prevW).erase v1,
                  (nbWalksBetweenAvoid G (r₂ - 2) v1 Pw.1 v2).card) ≤ 2 ^ (r₂ - 2 - s) := by
              intro v1 hv1
              have hv1_adj : G.Adj Pw.1 v1 :=
                (G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hv1).2
              have hv2_each : ∀ v2 ∈ ((G.neighborFinset Pw.1).erase prevW).erase v1,
                  (nbWalksBetweenAvoid G (r₂ - 2) v1 Pw.1 v2).card ≤ 2 ^ (r₂ - 2 - s) :=
                fun v2 _ => card_nbWalksBetweenAvoid_le G hg hreg (r₂ - 2) v1 Pw.1 v2 hv1_adj.symm
              have hsum2 := Finset.sum_le_sum hv2_each
              rw [Finset.sum_const, smul_eq_mul] at hsum2
              have hc2 : (((G.neighborFinset Pw.1).erase prevW).erase v1).card = 1 := by
                rw [Finset.card_erase_of_mem hv1,
                    Finset.card_erase_of_mem ((G.mem_neighborFinset _ _).mpr hprevW_adj),
                    G.card_neighborFinset_eq_degree, hreg Pw.1]
              rw [hc2, one_mul] at hsum2
              exact hsum2
            have hsum1 := Finset.sum_le_sum hv1_each
            rw [Finset.sum_const, smul_eq_mul] at hsum1
            have hc1 : ((G.neighborFinset Pw.1).erase prevW).card = 2 := by
              rw [Finset.card_erase_of_mem ((G.mem_neighborFinset _ _).mpr hprevW_adj),
                  G.card_neighborFinset_eq_degree, hreg Pw.1]
            rw [hc1] at hsum1
            exact hsum1
          have hsumPw := Finset.sum_le_sum hPw_each
          rw [Finset.sum_const, smul_eq_mul] at hsumPw
          have hcardPw := card_nbWalksAvoid_le G hreg (p - 1) u3 c1.1 hu3_adj.symm
          calc _ ≤ (nbWalksAvoid G (p - 1) u3 c1.1).card * (2 * 2 ^ (r₂ - 2 - s)) := hsumPw
            _ ≤ 2 ^ (p - 1) * (2 * 2 ^ (r₂ - 2 - s)) := Nat.mul_le_mul_right _ hcardPw
            _ = 2 * 2 ^ (p - 1 + (r₂ - 2 - s)) := by rw [pow_add]; ring
        have hsumU3 := Finset.sum_le_sum hu3_each
        rw [Finset.sum_const, smul_eq_mul] at hsumU3
        calc _ ≤ (u3Set c1).card * (2 * 2 ^ (p - 1 + (r₂ - 2 - s))) := hsumU3
          _ ≤ 1 * (2 * 2 ^ (p - 1 + (r₂ - 2 - s))) := Nat.mul_le_mul_right _ hu3_card
          _ = 2 * 2 ^ (p - 1 + (r₂ - 2 - s)) := one_mul _
      have htot := Finset.sum_le_sum hinner
      rw [Finset.sum_const, smul_eq_mul, hTL_card] at htot
      calc L * ∑ c1 ∈ TL r₁, _ ≤ L * (taillessCount G r₁ * (2 * 2 ^ (p - 1 + (r₂ - 2 - s)))) :=
            Nat.mul_le_mul_left L htot
        _ = 2 * L * 2 ^ (p - 1 + (r₂ - 2 - s)) * taillessCount G r₁ := by ring
    let evalParam (y : Σ _ : Fin L, Σ c1 : Σ u : V, {q : G.Walk u u // q.length = r₁},
        Σ u3 : V, Σ Pw : Σ w : V, {q : G.Walk u3 w // q.length = p - 1},
        Σ v1 : V, Σ v2 : V, {q : G.Walk v1 v2 // q.length = r₂ - 2}) :
        Option (Σ v : V, {q : G.Walk v v // q.length = L}) :=
      let ⟨j, c1, u3, Pw, v1, v2, mid⟩ := y
      if h : G.Adj c1.1 u3 ∧ G.Adj Pw.1 v1 ∧ G.Adj v2 Pw.1 then
        let P : G.Walk c1.1 Pw.1 := Walk.cons h.1 Pw.2.1
        let c₂ : G.Walk Pw.1 Pw.1 := Walk.cons h.2.1 (mid.1.append (Walk.cons h.2.2 .nil))
        let rot := c1.2.1.append (P.append (c₂.append P.reverse))
        some (unrotate L j rot (by
          simp only [rot, P, c₂, Walk.length_append, Walk.length_cons, Walk.length_reverse,
            Walk.length_nil, c1.2.2, Pw.2.2, mid.2]
          omega))
      else none
    have hpre : ∀ x ∈ S_pr, ∃ y ∈ Param, evalParam y = some x ∧
        (r₁ = r₂ → ∃ y' ∈ Param, evalParam y' = some x ∧ y' ≠ y) := by
      intro x hx
      simp only [S_pr, Finset.mem_filter] at hx
      obtain ⟨j, u, w, c₁, P, c₂, hPlen, hc₁len, _, _, _, _, _, _, hc₁, hc₂, htot, hrc, hunr⟩ := hx.2
      have mkWitness : ∀ (j₀ : Fin L) (u₀ w₀ : V) (c₁₀ : G.Walk u₀ u₀) (P₀ : G.Walk u₀ w₀) (c₂₀ : G.Walk w₀ w₀),
          P₀.length = p → c₁₀.length = r₁ → c₂₀.length = r₂ →
          c₁₀.IsCycle → c₂₀.IsCycle →
          IsCyclicallyNonBacktracking (c₁₀.append (P₀.append (c₂₀.append P₀.reverse))) →
          unrotate L j₀ (c₁₀.append (P₀.append (c₂₀.append P₀.reverse)))
            (by simp only [Walk.length_append, Walk.length_reverse]; omega) = x →
          ∃ y ∈ Param, evalParam y = some x ∧ y.1 = j₀ := by
        intro j₀ u₀ w₀ c₁₀ P₀ c₂₀ hP₀ hc₁₀ hc₂₀ hcyc₁₀ hcyc₂₀ hrc₀ hunr₀
        cases P₀ with
        | nil => simp at hP₀; omega
        | cons hu3 Ptail =>
            rename_i u3
            have hPtail_len : Ptail.length = p - 1 := by simp at hP₀; omega
            obtain ⟨v1, v2, hv1, hv2, mid, hv12, hc₂_eq, hmid_len, hmid_nb, hmid_fn⟩ :=
              strip_cycle_ends c₂₀ hcyc₂₀ (by omega)
            have hnb_rot : IsNonBacktracking (c₁₀.append ((Walk.cons hu3 Ptail).append (c₂₀.append (Walk.cons hu3 Ptail).reverse))) :=
              isNonBacktracking_of_append_left hrc₀
            have hnb_c1 : IsNonBacktracking c₁₀ := isNonBacktracking_of_append_left hnb_rot
            have hnb_rest1 : IsNonBacktracking ((Walk.cons hu3 Ptail).append (c₂₀.append (Walk.cons hu3 Ptail).reverse)) :=
              isNonBacktracking_of_append_right hnb_rot
            have hnb_P : IsNonBacktracking (Walk.cons hu3 Ptail) := isNonBacktracking_of_append_left hnb_rest1
            have hnb_Ptail : IsNonBacktracking Ptail := isNonBacktracking_of_append_right (p := .cons hu3 .nil) hnb_P
            have hfn_Ptail : firstNbr Ptail ≠ some u₀ := by
              cases Ptail with
              | nil => simp [firstNbr]
              | cons _ _ => simp only [IsNonBacktracking] at hnb_P; simp [firstNbr, Ne.symm hnb_P.1]
            have hc₁₀_cnb : IsCyclicallyNonBacktracking c₁₀ := by
              have hl_fn : lastNbr c₁₀ ≠ firstNbr c₁₀ := by
                obtain ⟨a₁, b₁, ha₁, hb₁, m₁, hab₁, hc1s, _, _, _⟩ := strip_cycle_ends c₁₀ hcyc₁₀ (by omega)
                have hf : firstNbr c₁₀ = some a₁ := by rw [hc1s]; rfl
                have hl : lastNbr c₁₀ = some b₁ := by
                  rw [hc1s]
                  have : Walk.cons ha₁ (m₁.append (.cons hb₁ .nil)) = (Walk.cons ha₁ m₁).append (.cons hb₁ .nil) := by simp
                  rw [this, lastNbr_append_of_pos _ _ (by simp)]; rfl
                rw [hl, hf]; simp [hab₁.symm]
              rw [IsCyclicallyNonBacktracking, isNonBacktracking_append_iff]
              exact ⟨hnb_c1, hnb_c1, fun a b ha hb heq => hl_fn (by rw [ha, hb, heq])⟩
            have hu3_ne_rev : u3 ≠ c₁₀.reverse.snd := by
              have hl : lastNbr c₁₀ = some c₁₀.reverse.snd := by
                rw [← firstNbr_reverse]
                cases hrv : c₁₀.reverse with
                | nil => have := Walk.length_reverse c₁₀; rw [hrv] at this; simp at this; omega
                | cons _ _ => rfl
              exact ((isNonBacktracking_append_iff c₁₀ _).mp hnb_rot).2.2 _ u3 hl rfl |>.symm
            have hu3_ne_snd : u3 ≠ c₁₀.snd := by
              have hln : lastNbr (c₁₀.append ((Walk.cons hu3 Ptail).append (c₂₀.append (Walk.cons hu3 Ptail).reverse))) = some u3 := by
                rw [lastNbr_append_of_pos _ _ (by simp [Walk.length_append]),
                    lastNbr_append_of_pos _ _ (by simp [Walk.length_append]),
                    lastNbr_append_of_pos _ _ (by simp [Walk.length_reverse]),
                    lastNbr_reverse]; rfl
              have hfn : firstNbr (c₁₀.append ((Walk.cons hu3 Ptail).append (c₂₀.append (Walk.cons hu3 Ptail).reverse))) = some c₁₀.snd := by
                rw [firstNbr_append_of_pos _ _ (by omega)]
                cases hc1 : c₁₀ with
                | nil => simp at hc₁₀; omega
                | cons _ _ => rfl
              exact ((isNonBacktracking_append_iff _ _).mp hrc₀).2.2 u3 c₁₀.snd hln hfn
            let prevW := if p - 1 = 0 then u₀ else Ptail.reverse.snd
            have hln_P : lastNbr (Walk.cons hu3 Ptail) = some prevW := by
              by_cases hp0 : p - 1 = 0
              · simp only [prevW, hp0, ↓reduceIte]
                cases Ptail with
                | nil => rfl
                | cons _ _ => simp at hPtail_len; omega
              · simp only [prevW, hp0, ↓reduceIte]
                rw [← firstNbr_reverse, Walk.reverse_cons,
                    firstNbr_append_of_pos _ _ (by rw [Walk.length_reverse]; omega)]
                cases hrv : Ptail.reverse with
                | nil => have := Walk.length_reverse Ptail; rw [hrv] at this; simp at this; omega
                | cons _ _ => rfl
            have hv1_ne_prev : v1 ≠ prevW := by
              have hnb_Pc2 : IsNonBacktracking ((Walk.cons hu3 Ptail).append c₂₀) :=
                isNonBacktracking_of_append_left (by simpa [Walk.append_assoc] using hnb_rest1)
              have hfn_c2 : firstNbr c₂₀ = some v1 := by rw [hc₂_eq]; rfl
              exact ((isNonBacktracking_append_iff _ _).mp hnb_Pc2).2.2 prevW v1 hln_P hfn_c2 |>.symm
            have hv2_ne_prev : v2 ≠ prevW := by
              have hnb_c2Pr : IsNonBacktracking (c₂₀.append (Walk.cons hu3 Ptail).reverse) :=
                isNonBacktracking_of_append_right hnb_rest1
              have hln_c2 : lastNbr c₂₀ = some v2 := by
                rw [hc₂_eq]
                have : Walk.cons hv1 (mid.append (.cons hv2 .nil)) = (Walk.cons hv1 mid).append (.cons hv2 .nil) := by simp
                rw [this, lastNbr_append_of_pos _ _ (by simp)]; rfl
              have hfn_Pr : firstNbr (Walk.cons hu3 Ptail).reverse = some prevW := by
                rw [firstNbr_reverse, hln_P]
              exact ((isNonBacktracking_append_iff _ _).mp hnb_c2Pr).2.2 v2 prevW hln_c2 hfn_Pr
            let y : Σ _ : Fin L, Σ c1 : Σ u : V, {q : G.Walk u u // q.length = r₁},
                Σ u3 : V, Σ Pw : Σ w : V, {q : G.Walk u3 w // q.length = p - 1},
                Σ v1 : V, Σ v2 : V, {q : G.Walk v1 v2 // q.length = r₂ - 2} :=
              ⟨j₀, ⟨u₀, ⟨c₁₀, hc₁₀⟩⟩, u3, ⟨w₀, ⟨Ptail, hPtail_len⟩⟩, v1, v2, ⟨mid, by omega⟩⟩
            refine ⟨y, ?_, ?_, rfl⟩
            · simp only [Param, Finset.mem_sigma, Finset.mem_univ, true_and, TL, Finset.mem_filter,
                mem_nbWalksSub_iff, u3Set, Finset.mem_erase, G.mem_neighborFinset,
                nbWalksAvoid, nbWalksBetweenAvoid]
              refine ⟨⟨hnb_c1, hc₁₀_cnb⟩, ⟨hu3_ne_rev, hu3_ne_snd, hu3⟩,
                ⟨hnb_Ptail, hfn_Ptail⟩, ⟨hv1_ne_prev, hv1⟩,
                ⟨hv12.symm, hv2_ne_prev, hv2.symm⟩, ⟨hmid_nb, hmid_fn⟩⟩
            · dsimp only [evalParam, y]
              have hcond_e : G.Adj u₀ u3 ∧ G.Adj w₀ v1 ∧ G.Adj v2 w₀ := ⟨hu3, hv1, hv2⟩
              simp only [hcond_e, ↓reduceDIte]
              congr 1
              have hc2_eq' : Walk.cons hv1 (mid.append (Walk.cons hv2 .nil)) = c₂₀ := hc₂_eq.symm
              simpa only [hc2_eq'] using hunr₀
      obtain ⟨y, hy_mem, hy_ev, hy_j⟩ := mkWitness j u w c₁ P c₂ hPlen hc₁len (by omega) hc₁ hc₂ hrc hunr
      refine ⟨y, hy_mem, hy_ev, ?_⟩
      intro heq12
      let j' : Fin L := ⟨(j.1 + (r₁ + p)) % L, Nat.mod_lt _ (by omega)⟩
      have hj'_ne : j' ≠ j := by
        intro hjeq
        have hv : (j.1 + (r₁ + p)) % L = j.1 := congrArg Fin.val hjeq
        have hhalf : 2 * (r₁ + p) = L := by omega
        have hjlt := j.2
        by_cases hlt' : j.1 + (r₁ + p) < L
        · rw [Nat.mod_eq_of_lt hlt'] at hv; omega
        · have hlt2 : j.1 + (r₁ + p) - L < L := by omega
          have hmod : (j.1 + (r₁ + p)) % L = j.1 + (r₁ + p) - L := by
            rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt2]
          rw [hmod] at hv; omega
      let rot1 := c₁.append (P.append (c₂.append P.reverse))
      let rot2 := c₂.append (P.reverse.append (c₁.append P))
      have hrot2_cyc : IsCyclicallyNonBacktracking rot2 := by
        have h1 : rot1 = (c₁.append P).append (c₂.append P.reverse) := by simp [rot1, Walk.append_assoc]
        have h2 : rot2 = (c₂.append P.reverse).append (c₁.append P) := by simp [rot2, Walk.append_assoc]
        rw [h2]; exact isCyclicallyNonBacktracking_rotate _ _ (h1 ▸ hrc)
      have hunr2 : unrotate L j' rot2 (by simp [rot2, Walk.length_append, Walk.length_reverse]; omega) = x := by
        rw [← hunr]
        set A := c₁.append P
        set B := c₂.append P.reverse
        have hA_len : A.length = r₁ + p := by simp [A, Walk.length_append, hc₁len, hPlen]
        have hB_len : B.length = r₁ + p := by simp [B, Walk.length_append, Walk.length_reverse, hPlen]; omega
        have hrot1_AB : rot1 = A.append B := by simp [rot1, A, B, Walk.append_assoc]
        have hrot2_BA : rot2 = B.append A := by simp [rot2, A, B, Walk.append_assoc]
        by_cases hcase : j.1 < r₁ + p
        · have hj'val : j'.1 = j.1 + (r₁ + p) := Nat.mod_eq_of_lt (by omega)
          let spB := splitWalk (r₁ + p - j.1) B (by omega)
          have hB_eq : B = spB.2.1.1.append spB.2.2.1 := (splitWalk_append _ B _).symm
          have hrot1_split : rot1 = (A.append spB.2.1.1).append spB.2.2.1 := by
            rw [hrot1_AB, hB_eq, Walk.append_assoc]
          have hrot2_split : rot2 = spB.2.1.1.append (spB.2.2.1.append A) := by
            rw [hrot2_BA, hB_eq, Walk.append_assoc]
          have h1 := unrotate_append spB.2.2.1 (A.append spB.2.1.1)
            (by rw [Walk.length_append, Walk.length_append, hA_len, spB.2.1.2, spB.2.2.2, hB_len]; omega)
            (by rw [spB.2.2.2, hB_len]; omega)
          have h2 := unrotate_append (spB.2.2.1.append A) spB.2.1.1
            (by rw [Walk.length_append, Walk.length_append, hA_len, spB.2.1.2, spB.2.2.2, hB_len]; omega)
            (by rw [Walk.length_append, hA_len, spB.2.2.2, hB_len]; omega)
          have hj1 : (⟨spB.2.2.1.length, by rw [spB.2.2.2, hB_len]; omega⟩ : Fin L) = j := by
            ext; rw [spB.2.2.2, hB_len]; omega
          have hj2 : (⟨(spB.2.2.1.append A).length, by rw [Walk.length_append, hA_len, spB.2.2.2, hB_len]; omega⟩ : Fin L) = j' := by
            ext; rw [Walk.length_append, hA_len, spB.2.2.2, hB_len, hj'val]; omega
          rw [hj1] at h1; rw [hj2] at h2
          rw [← hrot1_split] at h1; rw [← hrot2_split] at h2
          rw [h1, h2]
          congr 1; ext; simp [Walk.append_assoc]
        · have hj'val : j'.1 = j.1 - (r₁ + p) := by
            have hlt2 : j.1 + (r₁ + p) - L < L := by omega
            have hmod : (j.1 + (r₁ + p)) % L = j.1 + (r₁ + p) - L := by
              rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt2]
            dsimp only [j']; omega
          let spA := splitWalk (L - j.1) A (by omega)
          have hA_eq : A = spA.2.1.1.append spA.2.2.1 := (splitWalk_append _ A _).symm
          have hrot1_split : rot1 = spA.2.1.1.append (spA.2.2.1.append B) := by
            rw [hrot1_AB, hA_eq, Walk.append_assoc]
          have hrot2_split : rot2 = (B.append spA.2.1.1).append spA.2.2.1 := by
            rw [hrot2_BA, hA_eq, Walk.append_assoc]
          have h1 := unrotate_append (spA.2.2.1.append B) spA.2.1.1
            (by rw [Walk.length_append, Walk.length_append, hB_len, spA.2.1.2, spA.2.2.2, hA_len]; omega)
            (by rw [Walk.length_append, hB_len, spA.2.2.2, hA_len]; omega)
          have h2 := unrotate_append spA.2.2.1 (B.append spA.2.1.1)
            (by rw [Walk.length_append, Walk.length_append, hB_len, spA.2.1.2, spA.2.2.2, hA_len]; omega)
            (by rw [spA.2.2.2, hA_len]; omega)
          have hj1 : (⟨(spA.2.2.1.append B).length, by rw [Walk.length_append, hB_len, spA.2.2.2, hA_len]; omega⟩ : Fin L) = j := by
            ext; rw [Walk.length_append, hB_len, spA.2.2.2, hA_len]; omega
          have hj2 : (⟨spA.2.2.1.length, by rw [spA.2.2.2, hA_len]; omega⟩ : Fin L) = j' := by
            ext; rw [spA.2.2.2, hA_len, hj'val]; omega
          rw [hj1] at h1; rw [hj2] at h2
          rw [← hrot1_split] at h1; rw [← hrot2_split] at h2
          rw [h1, h2]
          congr 1; ext; simp [Walk.append_assoc]
      obtain ⟨y', hy'_mem, hy'_ev, hy'_j⟩ := mkWitness j' w u c₂ P.reverse c₁
        (by rw [Walk.length_reverse, hPlen]) (by omega) (by omega) hc₂ hc₁
        (by simpa [rot2] using hrot2_cyc) (by simpa [rot2] using hunr2)
      refine ⟨y', hy'_mem, hy'_ev, fun heq => hj'_ne ?_⟩
      rw [← hy'_j, ← hy_j, heq]
    by_cases heq12 : r₁ = r₂
    · simp only [heq12, ↓reduceIte]
      have h2le : 2 * S_pr.card ≤ Param.card := by
        have hcard_prod : (S_pr.product (Finset.univ : Finset (Fin 2))).card = 2 * S_pr.card := by
          rw [Finset.card_product, Finset.card_univ, Fintype.card_fin, mul_comm]
        rw [← hcard_prod]
        by_cases hne : S_pr.Nonempty
        · obtain ⟨x0, hx0⟩ := hne
          let y0 := Classical.choose (hpre x0 hx0)
          let f' : (Σ v : V, {q : G.Walk v v // q.length = L}) × Fin 2 → _ := fun xb =>
            if h : xb.1 ∈ S_pr then
              let h1 := Classical.choose_spec (hpre xb.1 h)
              if xb.2 = 0 then Classical.choose (hpre xb.1 h)
              else Classical.choose (h1.2.2 heq12)
            else y0
          refine Finset.card_le_card_of_injOn f' ?_ ?_
          · rintro ⟨x, b⟩ hxb
            simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_univ, and_true] at hxb ⊢
            dsimp only [f']
            simp only [hxb, ↓reduceDIte]
            split_ifs
            · exact (Classical.choose_spec (hpre x hxb)).1
            · exact (Classical.choose_spec ((Classical.choose_spec (hpre x hxb)).2.2 heq12)).1
          · rintro ⟨x₁, b₁⟩ h₁ ⟨x₂, b₂⟩ h₂ heq
            simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_univ, and_true] at h₁ h₂
            have hev1 : evalParam (f' (x₁, b₁)) = some x₁ := by
              dsimp only [f']; simp only [h₁, ↓reduceDIte]; split_ifs
              · exact (Classical.choose_spec (hpre x₁ h₁)).2.1
              · exact (Classical.choose_spec ((Classical.choose_spec (hpre x₁ h₁)).2.2 heq12)).2.1
            have hev2 : evalParam (f' (x₂, b₂)) = some x₂ := by
              dsimp only [f']; simp only [h₂, ↓reduceDIte]; split_ifs
              · exact (Classical.choose_spec (hpre x₂ h₂)).2.1
              · exact (Classical.choose_spec ((Classical.choose_spec (hpre x₂ h₂)).2.2 heq12)).2.1
            have hx_eq : x₁ = x₂ := by
              have := hev1.symm.trans (congrArg evalParam heq |>.trans hev2)
              exact Option.some.inj this
            subst hx_eq
            have hb_eq : b₁ = b₂ := by
              fin_cases b₁ <;> fin_cases b₂
              · rfl
              · exfalso
                dsimp only [f'] at heq
                simp only [h₁, ↓reduceDIte, ↓reduceIte, Fin.one_eq_zero_iff, OfNat.one_ne_ofNat] at heq
                exact (Classical.choose_spec ((Classical.choose_spec (hpre x₁ h₁)).2.2 heq12)).2.2 heq.symm
              · exfalso
                dsimp only [f'] at heq
                simp only [h₁, ↓reduceDIte, ↓reduceIte, Fin.one_eq_zero_iff, OfNat.one_ne_ofNat] at heq
                exact (Classical.choose_spec ((Classical.choose_spec (hpre x₁ h₁)).2.2 heq12)).2.2 heq
              · rfl
            rw [hb_eq]
        · rw [Finset.not_nonempty_iff_eq_empty] at hne
          simp [hne]
      have hmul : 2 * S_pr.card ≤ 2 * (L * 2 ^ (p - 1 + (r₂ - 2 - s)) * taillessCount G r₁) := by
        calc 2 * S_pr.card ≤ Param.card := h2le
          _ ≤ 2 * L * 2 ^ (p - 1 + (r₂ - 2 - s)) * taillessCount G r₁ := hParam_card
          _ = 2 * (L * 2 ^ (p - 1 + (r₂ - 2 - s)) * taillessCount G r₁) := by ring
      omega
    · simp only [heq12, ↓reduceIte]
      by_cases hne : S_pr.Nonempty
      · obtain ⟨x0, hx0⟩ := hne
        let y0 := Classical.choose (hpre x0 hx0)
        let f' : (Σ v : V, {q : G.Walk v v // q.length = L}) → _ := fun x =>
          if h : x ∈ S_pr then Classical.choose (hpre x h) else y0
        have hle1 : S_pr.card ≤ Param.card := by
          refine Finset.card_le_card_of_injOn f' ?_ ?_
          · intro x hx; rw [Finset.mem_coe] at hx ⊢; dsimp only [f']; simp only [hx, ↓reduceDIte]; exact (Classical.choose_spec (hpre x hx)).1
          · intro x₁ h₁ x₂ h₂ heq
            rw [Finset.mem_coe] at h₁ h₂
            have hev1 : evalParam (f' x₁) = some x₁ := by
              dsimp only [f']; simp only [h₁, ↓reduceDIte]; exact (Classical.choose_spec (hpre x₁ h₁)).2.1
            have hev2 : evalParam (f' x₂) = some x₂ := by
              dsimp only [f']; simp only [h₂, ↓reduceDIte]; exact (Classical.choose_spec (hpre x₂ h₂)).2.1
            exact Option.some.inj (hev1.symm.trans (congrArg evalParam heq |>.trans hev2))
        exact le_trans hle1 hParam_card
      · rw [Finset.not_nonempty_iff_eq_empty] at hne; simp [hne]
  · simp only [hcond, ↓reduceIte, zero_mul]
    have hemp : NS_bar.filter (isBarPR p r₁) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      simp only [Finset.mem_filter] at hx
      obtain ⟨_, _, _, _, _, _, _, _, _, _, hg₁, hle12, hnp1, hnp2, _⟩ := hx.2
      exact hcond ⟨hg₁, hle12, hnp1, hnp2⟩
    simp [hemp]


end NonSimpleBarbell

end E64Wave8Agent2
