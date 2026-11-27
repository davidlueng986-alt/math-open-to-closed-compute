import Shadow
import NonBacktrackingGirth
import Wave5Agent5GirthTripling
import Wave5Agent6ChebyshevGirth
import ChebTraceEngine
import NonSimpleHelpers
import NonSimpleDecomp
import NonSimpleBarbell

namespace E64Wave8Agent2
open SimpleGraph Erdos64Closure E64NonBacktrackingGirth E64Wave5Agent5 E64Wave5Agent6

section NonSimpleTheta

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Theta (Zero-Tail) Non-Simple Walk Upper Bound**:
In any cubic, power-free graph `G` of girth `g ≥ 6` and `L = 2^k < 3*g` (`4 ≤ k ≤ 6`),
the non-barbell (zero-tail theta) non-simple CNB walks of length `L` satisfy
`NS_th.card ≤ ∑ r ∈ range L, thetaTerm g L r * taillessCount G r`. -/
theorem nonSimple_theta_card_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {g k : ℕ} (hreg : ∀ v : V, G.degree v = 3) (hg : GirthAtLeast G g) (hg6 : 6 ≤ g)
    (hnp : ¬ HasPower G) (hk4 : 4 ≤ k) (hk6 : k ≤ 6) (hLt : 2 ^ k < 3 * g) :
    let L := 2 ^ k
    haveI : DecidablePred (fun x : Σ v : V, {p : G.Walk v v // p.length = L} =>
      IsCyclicallyNonBacktracking x.2.1 ∧ ¬ x.2.1.IsCycle) := Classical.decPred _
    let NS := ((Finset.univ : Finset V).sigma fun v => nbWalksSub G L v v).filter
      fun x => IsCyclicallyNonBacktracking x.2.1 ∧ ¬ x.2.1.IsCycle
    haveI : DecidablePred (isBarbellElem G g L) := Classical.decPred _
    (NS.filter fun x => ¬ isBarbellElem G g L x).card ≤
      ∑ r ∈ Finset.range L, thetaTerm g L r * taillessCount G r := by
  intro L _ NS _
  set s := (g - 1) / 2
  have hL1 : 1 ≤ L := Nat.one_le_two_pow
  have hL_even : L = 2 * 2 ^ (k - 1) := by
    have hk1 : k = (k - 1) + 1 := by omega
    conv_lhs => rw [show L = 2 ^ k from rfl, hk1, pow_succ]; ring
  have hnot_pow2_cycle : ∀ {z : V} (c : G.Walk z z), c.IsCycle → ¬ isPow2Small c.length = true := by
    intro z c hc hp2
    obtain ⟨m, hm, hlen⟩ := isPow2Small_spec hp2
    exact hnp ⟨m, z, c, hm, hc, hlen⟩
  have hhalf_pow2 : isPow2Small (2 ^ (k - 1)) = true := by
    have : k = 4 ∨ k = 5 ∨ k = 6 := by omega
    rcases this with rfl | rfl | rfl <;> decide
  let TL (r : ℕ) := ((Finset.univ : Finset V).sigma fun v => nbWalksSub G r v v).filter
    fun x => IsCyclicallyNonBacktracking x.2.1
  have hTL_card : ∀ r, (TL r).card = taillessCount G r := fun r =>
    taillessCount_eq_card_sub G r
  let NS_th := NS.filter fun x => ¬ isBarbellElem G g L x
  change NS_th.card ≤ _
  let isThRB (r₁ b : ℕ) (x : Σ v : V, {q : G.Walk v v // q.length = L}) : Prop :=
    ∃ (j : Fin L) (u w : V) (Pb : G.Walk u w) (Q₁ Q₂ : G.Walk w u),
      Pb.length = b ∧ (Pb.append Q₁).length = r₁ ∧
      1 ≤ b ∧ b < r₁ ∧
      g ≤ r₁ ∧ r₁ < L - r₁ ∧
      ¬ isPow2Small r₁ ∧ ¬ isPow2Small (L - r₁) ∧
      g ≤ L - 2 * b ∧ ¬ (isPow2Small (L - 2 * b) && decide (L - 2 * b < 2 * g)) ∧
      (Pb.append Q₁).IsCycle ∧ (Pb.append Q₂).IsCycle ∧
      (Pb.append Q₁).length + (Pb.append Q₂).length = L ∧
      firstNbr Q₁ ≠ firstNbr Q₂ ∧ lastNbr Q₁ ≠ lastNbr Q₂ ∧
      unrotate L j ((Pb.append Q₁).append (Pb.append Q₂))
        (by simp only [Walk.length_append]; omega) = x
  have hth_cover : NS_th ⊆ (Finset.range L).biUnion fun r₁ =>
      ((Finset.range r₁).filter fun b =>
        1 ≤ b ∧ g ≤ L - 2 * b ∧ ¬ (isPow2Small (L - 2 * b) && decide (L - 2 * b < 2 * g))).biUnion fun b =>
        NS_th.filter (isThRB r₁ b) := by
    intro x hx
    simp only [NS_th, NS, Finset.mem_filter, Finset.mem_sigma, Finset.mem_univ, true_and, mem_nbWalksSub_iff] at hx
    rcases x with ⟨v, ⟨p, hp⟩⟩
    obtain ⟨j, u, w, c₁, P, c₂, hc₁, hc₂, hg₁, hg₂, hlen, hrc, hunr⟩ :=
      tailless_nonSimple_rotation_decomp hg hLt p hx.1.2.1 hx.1.2.2 hp hL1
    have hP0 : P.length = 0 := by
      by_contra hPne
      apply hx.2
      by_cases hle12 : c₁.length ≤ c₂.length
      · exact ⟨j, u, w, c₁, P, c₂, by omega, hc₁, hc₂, hg₁, hle12, hlen, hrc, hunr⟩
      · let rot1 := c₁.append (P.append (c₂.append P.reverse))
        let rot2 := c₂.append (P.reverse.append (c₁.append P))
        let j' : Fin L := ⟨(j.1 + (c₁.length + P.length)) % L, Nat.mod_lt _ (by omega)⟩
        have hrot2_cyc : IsCyclicallyNonBacktracking rot2 := by
          have h1 : rot1 = (c₁.append P).append (c₂.append P.reverse) := by simp [rot1, Walk.append_assoc]
          have h2 : rot2 = (c₂.append P.reverse).append (c₁.append P) := by simp [rot2, Walk.append_assoc]
          rw [h2]; exact isCyclicallyNonBacktracking_rotate _ _ (h1 ▸ hrc)
        have hunr2 : unrotate L j' rot2 (by simp [rot2, Walk.length_append, Walk.length_reverse]; omega) = ⟨v, ⟨p, hp⟩⟩ := by
          rw [← hunr]
          set A := c₁.append P
          set B := c₂.append P.reverse
          have hA_len : A.length = c₁.length + P.length := by simp [A, Walk.length_append]
          have hB_len : B.length = c₂.length + P.length := by simp [B, Walk.length_append, Walk.length_reverse]
          have hAB : A.length + B.length = L := by omega
          have hrot1_AB : rot1 = A.append B := by simp [rot1, A, B, Walk.append_assoc]
          have hrot2_BA : rot2 = B.append A := by simp [rot2, A, B, Walk.append_assoc]
          by_cases hcase : j.1 < B.length
          · have hj'val : j'.1 = j.1 + A.length := Nat.mod_eq_of_lt (by omega)
            let spB := splitWalk (B.length - j.1) B (by omega)
            have hB_eq : B = spB.2.1.1.append spB.2.2.1 := (splitWalk_append _ B _).symm
            have hrot1_split : rot1 = (A.append spB.2.1.1).append spB.2.2.1 := by rw [hrot1_AB, hB_eq, Walk.append_assoc]
            have hrot2_split : rot2 = spB.2.1.1.append (spB.2.2.1.append A) := by rw [hrot2_BA, hB_eq, Walk.append_assoc]
            have h1 := unrotate_append spB.2.2.1 (A.append spB.2.1.1)
              (by rw [Walk.length_append, Walk.length_append, spB.2.1.2, spB.2.2.2]; omega)
              (by rw [spB.2.2.2]; omega)
            have h2 := unrotate_append (spB.2.2.1.append A) spB.2.1.1
              (by rw [Walk.length_append, Walk.length_append, spB.2.1.2, spB.2.2.2]; omega)
              (by rw [Walk.length_append, spB.2.2.2]; omega)
            have hj1 : (⟨spB.2.2.1.length, by rw [spB.2.2.2]; omega⟩ : Fin L) = j := by ext; rw [spB.2.2.2]; omega
            have hj2 : (⟨(spB.2.2.1.append A).length, by rw [Walk.length_append, spB.2.2.2]; omega⟩ : Fin L) = j' := by
              ext; rw [Walk.length_append, spB.2.2.2, hj'val]; omega
            rw [hj1] at h1; rw [hj2] at h2; rw [← hrot1_split] at h1; rw [← hrot2_split] at h2
            rw [h1, h2]; congr 1; ext; simp [Walk.append_assoc]
          · have hj'val : j'.1 = j.1 - B.length := by
              have hlt2 : j.1 + A.length - L < L := by omega
              have hmod : (j.1 + A.length) % L = j.1 + A.length - L := by
                rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt2]
              dsimp only [j']; omega
            let spA := splitWalk (L - j.1) A (by omega)
            have hA_eq : A = spA.2.1.1.append spA.2.2.1 := (splitWalk_append _ A _).symm
            have hrot1_split : rot1 = spA.2.1.1.append (spA.2.2.1.append B) := by rw [hrot1_AB, hA_eq, Walk.append_assoc]
            have hrot2_split : rot2 = (B.append spA.2.1.1).append spA.2.2.1 := by rw [hrot2_BA, hA_eq, Walk.append_assoc]
            have h1 := unrotate_append (spA.2.2.1.append B) spA.2.1.1
              (by rw [Walk.length_append, Walk.length_append, spA.2.1.2, spA.2.2.2]; omega)
              (by rw [Walk.length_append, spA.2.2.2]; omega)
            have h2 := unrotate_append spA.2.2.1 (B.append spA.2.1.1)
              (by rw [Walk.length_append, Walk.length_append, spA.2.1.2, spA.2.2.2]; omega)
              (by rw [spA.2.2.2]; omega)
            have hj1 : (⟨(spA.2.2.1.append B).length, by rw [Walk.length_append, spA.2.2.2]; omega⟩ : Fin L) = j := by
              ext; rw [Walk.length_append, spA.2.2.2]; omega
            have hj2 : (⟨spA.2.2.1.length, by rw [spA.2.2.2]; omega⟩ : Fin L) = j' := by
              ext; rw [spA.2.2.2, hj'val]; omega
            rw [hj1] at h1; rw [hj2] at h2; rw [← hrot1_split] at h1; rw [← hrot2_split] at h2
            rw [h1, h2]; congr 1; ext; simp [Walk.append_assoc]
        exact ⟨j', w, u, c₂, P.reverse, c₁, by rw [Walk.length_reverse]; omega, hc₂, hc₁, hg₂, by omega,
          by rw [Walk.length_reverse]; omega, by simpa [rot2] using hrot2_cyc, by simpa [rot2] using hunr2⟩
    cases P with
    | cons _ _ => simp at hP0
    | nil =>
        simp only [Walk.reverse_nil, Walk.nil_append, Walk.append_nil, Walk.length_nil,
          mul_zero, add_zero] at hlen hrc hunr
        have hne12 : c₁.length ≠ c₂.length := by
          intro heq
          have hhalf : c₁.length = 2 ^ (k - 1) := by omega
          exact hnot_pow2_cycle c₁ hc₁ (hhalf ▸ hhalf_pow2)
        have hex_ord : ∃ (j₀ : Fin L) (z : V) (d₁ d₂ : G.Walk z z),
            d₁.IsCycle ∧ d₂.IsCycle ∧ g ≤ d₁.length ∧ d₁.length < d₂.length ∧
            d₁.length + d₂.length = L ∧ IsCyclicallyNonBacktracking (d₁.append d₂) ∧
            unrotate L j₀ (d₁.append d₂) (by rw [Walk.length_append]; omega) = ⟨v, ⟨p, hp⟩⟩ := by
          by_cases hlt12 : c₁.length < c₂.length
          · exact ⟨j, u, c₁, c₂, hc₁, hc₂, hg₁, hlt12, hlen, hrc, hunr⟩
          · let j' : Fin L := ⟨(j.1 + c₁.length) % L, Nat.mod_lt _ (by omega)⟩
            have hrc' : IsCyclicallyNonBacktracking (c₂.append c₁) := isCyclicallyNonBacktracking_rotate c₁ c₂ hrc
            have hunr' : unrotate L j' (c₂.append c₁) (by rw [Walk.length_append]; omega) = ⟨v, ⟨p, hp⟩⟩ := by
              rw [← hunr]
              by_cases hcase : j.1 < c₂.length
              · have hj'val : j'.1 = j.1 + c₁.length := Nat.mod_eq_of_lt (by omega)
                let sp := splitWalk (c₂.length - j.1) c₂ (by omega)
                have hc2_eq : c₂ = sp.2.1.1.append sp.2.2.1 := (splitWalk_append _ c₂ _).symm
                have h1 := unrotate_append sp.2.2.1 (c₁.append sp.2.1.1)
                  (by rw [Walk.length_append, Walk.length_append, sp.2.1.2, sp.2.2.2]; omega) (by rw [sp.2.2.2]; omega)
                have h2 := unrotate_append (sp.2.2.1.append c₁) sp.2.1.1
                  (by rw [Walk.length_append, Walk.length_append, sp.2.1.2, sp.2.2.2]; omega) (by rw [Walk.length_append, sp.2.2.2]; omega)
                have hj1 : (⟨sp.2.2.1.length, by rw [sp.2.2.2]; omega⟩ : Fin L) = j := by ext; rw [sp.2.2.2]; omega
                have hj2 : (⟨(sp.2.2.1.append c₁).length, by rw [Walk.length_append, sp.2.2.2]; omega⟩ : Fin L) = j' := by
                  ext; rw [Walk.length_append, sp.2.2.2, hj'val]; omega
                rw [hj1] at h1; rw [hj2] at h2
                have e1 : (c₁.append sp.2.1.1).append sp.2.2.1 = c₁.append c₂ := by rw [hc2_eq, Walk.append_assoc]
                have e2 : sp.2.1.1.append (sp.2.2.1.append c₁) = c₂.append c₁ := by rw [hc2_eq, Walk.append_assoc]
                rw [e1] at h1; rw [e2] at h2; rw [h1, h2]; congr 1; ext; simp [Walk.append_assoc]
              · have hj'val : j'.1 = j.1 - c₂.length := by
                  have hlt2 : j.1 + c₁.length - L < L := by omega
                  have hmod : (j.1 + c₁.length) % L = j.1 + c₁.length - L := by
                    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt2]
                  dsimp only [j']; omega
                let sp := splitWalk (L - j.1) c₁ (by omega)
                have hc1_eq : c₁ = sp.2.1.1.append sp.2.2.1 := (splitWalk_append _ c₁ _).symm
                have h1 := unrotate_append (sp.2.2.1.append c₂) sp.2.1.1
                  (by rw [Walk.length_append, Walk.length_append, sp.2.1.2, sp.2.2.2]; omega) (by rw [Walk.length_append, sp.2.2.2]; omega)
                have h2 := unrotate_append sp.2.2.1 (c₂.append sp.2.1.1)
                  (by rw [Walk.length_append, Walk.length_append, sp.2.1.2, sp.2.2.2]; omega) (by rw [sp.2.2.2]; omega)
                have hj1 : (⟨(sp.2.2.1.append c₂).length, by rw [Walk.length_append, sp.2.2.2]; omega⟩ : Fin L) = j := by
                  ext; rw [Walk.length_append, sp.2.2.2]; omega
                have hj2 : (⟨sp.2.2.1.length, by rw [sp.2.2.2]; omega⟩ : Fin L) = j' := by
                  ext; rw [sp.2.2.2, hj'val]; omega
                rw [hj1] at h1; rw [hj2] at h2
                have e1 : sp.2.1.1.append (sp.2.2.1.append c₂) = c₁.append c₂ := by rw [hc1_eq, Walk.append_assoc]
                have e2 : (c₂.append sp.2.1.1).append sp.2.2.1 = c₂.append c₁ := by rw [hc1_eq, Walk.append_assoc]
                rw [e1] at h1; rw [e2] at h2; rw [h1, h2]; congr 1; ext; simp [Walk.append_assoc]
            exact ⟨j', u, c₂, c₁, hc₂, hc₁, hg₂, by omega, by omega, hrc', hunr'⟩
        obtain ⟨j₀, z, d₁, d₂, hd₁, hd₂, hgd₁, hlt12, hsumd, hrcd, hunrd⟩ := hex_ord
        obtain ⟨d_sh, u', w', Pb, Q₁, Q₂, hPb1, hPblt, hPQ1, hPQ2, hlen1, hlen2, hfnQ, hlnQ, hQ12_cyc, hunr_sh⟩ :=
          exists_maximal_shared_prefix hreg d₁ d₂ hd₁ hd₂ (by omega) hlt12 hsumd hrcd
        let rot_final := (Pb.append Q₁).append (Pb.append Q₂)
        have hrot_len : rot_final.length = L := by simp [rot_final, Walk.length_append]; omega
        have hcomp : ∃ j_tot : Fin L, unrotate L j_tot rot_final hrot_len = ⟨v, ⟨p, hp⟩⟩ := by
          let sp1 := splitWalk (L - d_sh.1) rot_final (by omega)
          have hrot_1 : rot_final = sp1.2.1.1.append sp1.2.2.1 := (splitWalk_append _ rot_final _).symm
          have hd12_eq : ⟨sp1.1, ⟨sp1.2.2.1.append sp1.2.1.1, by rw [Walk.length_append, sp1.2.2.2, sp1.2.1.2, hrot_len]; omega⟩⟩ =
              (⟨z, ⟨d₁.append d₂, hsumd⟩⟩ : Σ a : V, {q : G.Walk a a // q.length = L}) := hunr_sh
          rcases sp1 with ⟨z', ⟨b1, hb1⟩, ⟨a1, ha1⟩⟩
          simp only [Sigma.mk.inj_iff, Subtype.mk.injEq, heq_eq_eq] at hd12_eq
          rcases hd12_eq with ⟨rfl, hd12_w⟩
          let j_tot : Fin L := ⟨(j₀.1 + d_sh.1) % L, Nat.mod_lt _ (by omega)⟩
          refine ⟨j_tot, ?_⟩
          rw [← hunrd, ← hd12_w]
          by_cases hcase : j₀.1 < b1.length
          · have hjt : j_tot.1 = j₀.1 + a1.length := by
              dsimp only [j_tot]; rw [ha1, hrot_len]; exact Nat.mod_eq_of_lt (by omega)
            let sp := splitWalk (b1.length - j₀.1) b1 (by omega)
            have hb1_eq : b1 = sp.2.1.1.append sp.2.2.1 := (splitWalk_append _ b1 _).symm
            have h1 := unrotate_append sp.2.2.1 (a1.append sp.2.1.1)
              (by rw [Walk.length_append, Walk.length_append, sp.2.1.2, sp.2.2.2, ha1, hb1, hrot_len]; omega)
              (by rw [sp.2.2.2]; omega)
            have h2 := unrotate_append (sp.2.2.1.append a1) sp.2.1.1
              (by rw [Walk.length_append, Walk.length_append, sp.2.1.2, sp.2.2.2, ha1, hb1, hrot_len]; omega)
              (by rw [Walk.length_append, sp.2.2.2, ha1, hrot_len]; omega)
            have hj1 : (⟨sp.2.2.1.length, by rw [sp.2.2.2]; omega⟩ : Fin L) = j₀ := by ext; rw [sp.2.2.2]; omega
            have hj2 : (⟨(sp.2.2.1.append a1).length, by rw [Walk.length_append, sp.2.2.2, ha1, hrot_len]; omega⟩ : Fin L) = j_tot := by
              ext; rw [Walk.length_append, sp.2.2.2, hjt]; omega
            rw [hj1] at h1; rw [hj2] at h2
            have e1 : (a1.append sp.2.1.1).append sp.2.2.1 = a1.append b1 := by rw [hb1_eq, Walk.append_assoc]
            have e2 : sp.2.1.1.append (sp.2.2.1.append a1) = rot_final := by rw [hrot_1, hb1_eq, Walk.append_assoc]
            rw [e1] at h1; rw [e2] at h2; rw [h1, h2]; congr 1; ext; simp [Walk.append_assoc]
          · have hjt : j_tot.1 = j₀.1 - b1.length := by
              have hlt2 : j₀.1 + d_sh.1 - L < L := by omega
              have hmod : (j₀.1 + d_sh.1) % L = j₀.1 + d_sh.1 - L := by
                rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt2]
              dsimp only [j_tot]; omega
            let sp := splitWalk (L - j₀.1) a1 (by omega)
            have ha1_eq : a1 = sp.2.1.1.append sp.2.2.1 := (splitWalk_append _ a1 _).symm
            have h1 := unrotate_append (sp.2.2.1.append b1) sp.2.1.1
              (by rw [Walk.length_append, Walk.length_append, sp.2.1.2, sp.2.2.2, ha1, hb1, hrot_len]; omega)
              (by rw [Walk.length_append, sp.2.2.2, ha1, hb1, hrot_len]; omega)
            have h2 := unrotate_append sp.2.2.1 (b1.append sp.2.1.1)
              (by rw [Walk.length_append, Walk.length_append, sp.2.1.2, sp.2.2.2, ha1, hb1, hrot_len]; omega)
              (by rw [sp.2.2.2, ha1, hrot_len]; omega)
            have hj1 : (⟨(sp.2.2.1.append b1).length, by rw [Walk.length_append, sp.2.2.2, ha1, hb1, hrot_len]; omega⟩ : Fin L) = j₀ := by
              ext; rw [Walk.length_append, sp.2.2.2, ha1, hb1, hrot_len]; omega
            have hj2 : (⟨sp.2.2.1.length, by rw [sp.2.2.2, ha1, hrot_len]; omega⟩ : Fin L) = j_tot := by
              ext; rw [sp.2.2.2, ha1, hrot_len, hjt, hb1]; omega
            rw [hj1] at h1; rw [hj2] at h2
            have e1 : sp.2.1.1.append (sp.2.2.1.append b1) = a1.append b1 := by rw [ha1_eq, Walk.append_assoc]
            have e2 : (b1.append sp.2.1.1).append sp.2.2.1 = rot_final := by rw [hrot_1, ha1_eq, Walk.append_assoc]
            rw [e1] at h1; rw [e2] at h2; rw [h1, h2]; congr 1; ext; simp [Walk.append_assoc]
        obtain ⟨j_tot, hj_tot⟩ := hcomp
        have hQ12_len : (Q₁.append Q₂.reverse).length = L - 2 * Pb.length := by
          rw [Walk.length_append, Walk.length_reverse]
          simp only [Walk.length_append] at hlen1 hlen2
          omega
        have hQ12_pos : 1 ≤ (Q₁.append Q₂.reverse).length := by
          simp only [Walk.length_append] at hlen1 hlen2; omega
        have hg_Q12 : g ≤ L - 2 * Pb.length :=
          hQ12_len ▸ girth_le_length_of_nonBacktracking_closed hg _ _ rfl hQ12_pos
            (isNonBacktracking_of_append_left hQ12_cyc)
        have hnp_Q12 : ¬ (isPow2Small (L - 2 * Pb.length) && decide (L - 2 * Pb.length < 2 * g)) = true := by
          intro hbad
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hbad
          obtain ⟨m, hm, hm_eq⟩ := isPow2Small_spec hbad.1
          exact no_cyclicallyNonBacktracking_in_girth_window_of_not_hasPower hg hnp hm
            (hm_eq ▸ hbad.2) (Q₁.append Q₂.reverse) hQ12_cyc (hQ12_len.trans hm_eq)
        simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
        refine ⟨d₁.length, by omega, Pb.length, ⟨hPblt, hPb1, hg_Q12, hnp_Q12⟩, ?_, ?_⟩
        · simp only [NS_th, NS, Finset.mem_filter, Finset.mem_sigma, Finset.mem_univ, true_and,
            mem_nbWalksSub_iff]
          exact ⟨⟨hx.1.1, hx.1.2.1, hx.1.2.2⟩, hx.2⟩
        · exact ⟨j_tot, u', w', Pb, Q₁, Q₂, rfl, hlen1, hPb1, hPblt, hgd₁, by omega,
            hnot_pow2_cycle d₁ hd₁, (show d₂.length = L - d₁.length by omega) ▸ hnot_pow2_cycle d₂ hd₂,
            hg_Q12, hnp_Q12, hPQ1, hPQ2, by omega, hfnQ, hlnQ, hj_tot⟩
  refine le_trans (Finset.card_le_card hth_cover) ?_
  refine le_trans Finset.card_biUnion_le ?_
  refine Finset.sum_le_sum fun r₁ _ => ?_
  refine le_trans Finset.card_biUnion_le ?_
  unfold thetaTerm
  set r₂ := L - r₁
  by_cases hcond : g ≤ r₁ ∧ r₁ < r₂ ∧ ¬ isPow2Small r₁ ∧ ¬ isPow2Small r₂
  · simp only [hcond, ↓reduceIte]
    have hlist_filt : ∀ (n : ℕ) (pred : ℕ → Bool) (f : ℕ → ℕ),
        (((List.range n).filter pred).map f).sum =
          ∑ b ∈ (Finset.range n).filter (fun b => pred b = true), f b := by
      intro n pred f
      induction n with
      | zero => simp
      | succ n ih =>
          rw [List.range_succ, List.filter_append, List.map_append, List.sum_append, ih,
              Finset.range_succ, Finset.filter_insert]
          by_cases h : pred n = true
          · simp [h, Finset.sum_insert, add_comm]
          · simp [h]
    have hth_sum : ((((List.range r₁).filter fun b =>
          decide (1 ≤ b ∧ g ≤ L - 2 * b ∧ ¬ (isPow2Small (L - 2 * b) && decide (L - 2 * b < 2 * g)))).map
            (fun b => L * 2 ^ (r₂ - b - 2 - s))).sum) * taillessCount G r₁ =
        ∑ b ∈ (Finset.range r₁).filter (fun b =>
          1 ≤ b ∧ g ≤ L - 2 * b ∧ ¬ (isPow2Small (L - 2 * b) && decide (L - 2 * b < 2 * g))),
          (L * 2 ^ (r₂ - b - 2 - s)) * taillessCount G r₁ := by
      rw [hlist_filt, Finset.sum_mul]
      congr 1; ext b; simp
    rw [show ((((List.range r₁).filter fun b =>
          1 ≤ b ∧ g ≤ L - 2 * b ∧ ¬ (isPow2Small (L - 2 * b) && decide (L - 2 * b < 2 * g))).map
            (fun b => L * 2 ^ (r₂ - b - 2 - s))).sum) * taillessCount G r₁ =
        ∑ b ∈ (Finset.range r₁).filter (fun b =>
          1 ≤ b ∧ g ≤ L - 2 * b ∧ ¬ (isPow2Small (L - 2 * b) && decide (L - 2 * b < 2 * g))),
          (L * 2 ^ (r₂ - b - 2 - s)) * taillessCount G r₁ from hth_sum]
    refine Finset.sum_le_sum fun b hb => ?_
    simp only [Finset.mem_filter, Finset.mem_range] at hb
    let S_rb := NS_th.filter (isThRB r₁ b)
    let v3Set (c1 : Σ u : V, {q : G.Walk u u // q.length = r₁}) : Finset V :=
      let sp := splitWalk b c1.2.1 (by rw [c1.2.2]; omega)
      ((G.neighborFinset sp.1).erase sp.2.1.1.reverse.snd).erase sp.2.2.1.snd
    let u3Set (c1 : Σ u : V, {q : G.Walk u u // q.length = r₁}) : Finset V :=
      ((G.neighborFinset c1.1).erase c1.2.1.snd).erase c1.2.1.reverse.snd
    let Param :=
      (Finset.univ : Finset (Fin L)).sigma fun _ =>
      (TL r₁).sigma fun c1 =>
      let w := (splitWalk b c1.2.1 (by rw [c1.2.2]; omega)).1
      (v3Set c1).sigma fun v3 =>
      (u3Set c1).sigma fun u3 =>
      nbWalksBetweenAvoid G (r₂ - b - 2) v3 w u3
    have hParam_card : Param.card ≤ L * 2 ^ (r₂ - b - 2 - s) * taillessCount G r₁ := by
      simp only [Param, Finset.card_sigma, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul]
      have hinner : ∀ c1 ∈ TL r₁,
          (let w := (splitWalk b c1.2.1 (by rw [c1.2.2]; omega)).1
           ∑ v3 ∈ v3Set c1, ∑ u3 ∈ u3Set c1,
             (nbWalksBetweenAvoid G (r₂ - b - 2) v3 w u3).card) ≤ 2 ^ (r₂ - b - 2 - s) := by
        intro c1 hc1_mem
        dsimp only
        simp only [TL, Finset.mem_filter, Finset.mem_sigma, Finset.mem_univ, true_and, mem_nbWalksSub_iff] at hc1_mem
        set sp := splitWalk b c1.2.1 (by rw [c1.2.2]; omega)
        have happ : sp.2.1.1.append sp.2.2.1 = c1.2.1 := splitWalk_append b c1.2.1 _
        have hPb_pos : 1 ≤ sp.2.1.1.length := by rw [sp.2.1.2]; omega
        have hQ1_pos : 1 ≤ sp.2.2.1.length := by rw [sp.2.2.2, c1.2.2]; omega
        have hv3_card : (v3Set c1).card ≤ 1 := by
          have h1 : G.Adj sp.1 sp.2.1.1.reverse.snd := by
            cases hrv : sp.2.1.1.reverse with
            | nil => have := Walk.length_reverse sp.2.1.1; rw [hrv] at this; simp at this; omega
            | cons h _ => exact h
          have h2 : G.Adj sp.1 sp.2.2.1.snd := by
            cases hq : sp.2.2.1 with
            | nil => simp [hq] at hQ1_pos
            | cons h _ => exact h
          have hne : sp.2.1.1.reverse.snd ≠ sp.2.2.1.snd := by
            have hln : lastNbr sp.2.1.1 = some sp.2.1.1.reverse.snd := by
              rw [← firstNbr_reverse]
              cases hrv : sp.2.1.1.reverse with
              | nil => have := Walk.length_reverse sp.2.1.1; rw [hrv] at this; simp at this; omega
              | cons _ _ => rfl
            have hfn : firstNbr sp.2.2.1 = some sp.2.2.1.snd := by
              cases hq : sp.2.2.1 with
              | nil => simp [hq] at hQ1_pos
              | cons _ _ => rfl
            exact ((isNonBacktracking_append_iff sp.2.1.1 sp.2.2.1).mp (happ ▸ hc1_mem.1)).2.2 _ _ hln hfn
          have hm : sp.2.2.1.snd ∈ (G.neighborFinset sp.1).erase sp.2.1.1.reverse.snd :=
            Finset.mem_erase.mpr ⟨hne.symm, SimpleGraph.mem_neighborFinset.mpr h2⟩
          dsimp only [v3Set]
          rw [Finset.card_erase_of_mem hm,
              Finset.card_erase_of_mem (SimpleGraph.mem_neighborFinset.mpr h1),
              G.card_neighborFinset_eq_degree, hreg sp.1]
        have hu3_card : (u3Set c1).card ≤ 1 := by
          have h1 : G.Adj c1.1 c1.2.1.snd := by
            cases hq : c1.2.1 with
            | nil => have := c1.2.2; rw [hq] at this; simp at this; omega
            | cons h _ => exact h
          have h2 : G.Adj c1.1 c1.2.1.reverse.snd := by
            cases hq : c1.2.1.reverse with
            | nil => have := Walk.length_reverse c1.2.1; rw [hq] at this; simp at this; have := c1.2.2; omega
            | cons h _ => exact h
          have hne : c1.2.1.snd ≠ c1.2.1.reverse.snd := by
            have hf : firstNbr c1.2.1 = some c1.2.1.snd := by
              cases hq : c1.2.1 with
              | nil => have := c1.2.2; rw [hq] at this; simp at this; omega
              | cons _ _ => rfl
            have hl : lastNbr c1.2.1 = some c1.2.1.reverse.snd := by
              rw [← firstNbr_reverse]
              cases hq : c1.2.1.reverse with
              | nil => have := Walk.length_reverse c1.2.1; rw [hq] at this; simp at this; have := c1.2.2; omega
              | cons _ _ => rfl
            exact ((isNonBacktracking_append_iff c1.2.1 c1.2.1).mp hc1_mem.2).2.2 _ _ hl hf |>.symm
          have hm : c1.2.1.reverse.snd ∈ (G.neighborFinset c1.1).erase c1.2.1.snd :=
            Finset.mem_erase.mpr ⟨hne.symm, SimpleGraph.mem_neighborFinset.mpr h2⟩
          dsimp only [u3Set]
          rw [Finset.card_erase_of_mem hm,
              Finset.card_erase_of_mem (SimpleGraph.mem_neighborFinset.mpr h1),
              G.card_neighborFinset_eq_degree, hreg c1.1]
        have hv3_each : ∀ v3 ∈ v3Set c1,
            (∑ u3 ∈ u3Set c1, (nbWalksBetweenAvoid G (r₂ - b - 2) v3 sp.1 u3).card) ≤ 2 ^ (r₂ - b - 2 - s) := by
          intro v3 hv3
          have hv3_adj : G.Adj sp.1 v3 :=
            SimpleGraph.mem_neighborFinset.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hv3).2).2
          have hu3_each : ∀ u3 ∈ u3Set c1,
              (nbWalksBetweenAvoid G (r₂ - b - 2) v3 sp.1 u3).card ≤ 2 ^ (r₂ - b - 2 - s) :=
            fun u3 _ => card_nbWalksBetweenAvoid_le G hg hreg (r₂ - b - 2) v3 sp.1 u3 hv3_adj.symm
          have hs1 := Finset.sum_le_sum hu3_each
          rw [Finset.sum_const, smul_eq_mul] at hs1
          calc _ ≤ (u3Set c1).card * 2 ^ (r₂ - b - 2 - s) := hs1
            _ ≤ 1 * 2 ^ (r₂ - b - 2 - s) := Nat.mul_le_mul_right _ hu3_card
            _ = 2 ^ (r₂ - b - 2 - s) := one_mul _
        have hs2 := Finset.sum_le_sum hv3_each
        rw [Finset.sum_const, smul_eq_mul] at hs2
        calc _ ≤ (v3Set c1).card * 2 ^ (r₂ - b - 2 - s) := hs2
          _ ≤ 1 * 2 ^ (r₂ - b - 2 - s) := Nat.mul_le_mul_right _ hv3_card
          _ = 2 ^ (r₂ - b - 2 - s) := one_mul _
      have htot := Finset.sum_le_sum hinner
      rw [Finset.sum_const, smul_eq_mul, hTL_card] at htot
      calc L * ∑ c1 ∈ TL r₁, _ ≤ L * (taillessCount G r₁ * 2 ^ (r₂ - b - 2 - s)) := Nat.mul_le_mul_left L htot
        _ = L * 2 ^ (r₂ - b - 2 - s) * taillessCount G r₁ := by ring
    let evalTh (y : Σ _ : Fin L, Σ c1 : Σ u : V, {q : G.Walk u u // q.length = r₁},
        Σ v3 : V, Σ u3 : V, {q : G.Walk v3 u3 // q.length = r₂ - b - 2}) :
        Option (Σ v : V, {q : G.Walk v v // q.length = L}) :=
      let ⟨j, c1, v3, u3, mid⟩ := y
      let sp := splitWalk b c1.2.1 (by rw [c1.2.2]; omega)
      if h : G.Adj sp.1 v3 ∧ G.Adj u3 c1.1 then
        let Q₂ : G.Walk sp.1 c1.1 := Walk.cons h.1 (mid.1.append (Walk.cons h.2 .nil))
        let rot := c1.2.1.append (sp.2.1.1.append Q₂)
        some (unrotate L j rot (by
          simp only [rot, Q₂, Walk.length_append, Walk.length_cons, Walk.length_nil,
            c1.2.2, sp.2.1.2, mid.2]
          omega))
      else none
    have hpre_th : ∀ x ∈ S_rb, ∃ y ∈ Param, evalTh y = some x := by
      intro x hx
      simp only [S_rb, Finset.mem_filter] at hx
      obtain ⟨j, u, w, Pb, Q₁, Q₂, hPblen, hc1len, _, _, _, _, _, _, _, _, hPQ1, hPQ2, hsum12, hfnQ, hlnQ, hunr⟩ := hx.2
      have hQ₂_len : Q₂.length = r₂ - b := by
        simp only [Walk.length_append] at hc1len hsum12; omega
      have hnb_PQ1 : IsNonBacktracking (Pb.append Q₁) := by
        have aux : ∀ {a c : V} (q : G.Walk a c), q.IsTrail → IsNonBacktracking q := by
          intro a c q; induction q with
          | nil => intro _; trivial
          | cons _ r ih => intro ht; cases r with
            | nil => trivial
            | cons _ _ =>
                have hnd := ht.edges_nodup; simp only [Walk.edges_cons, List.nodup_cons] at hnd
                exact ⟨fun h => by subst h; exact hnd.1 (by simp [Sym2.eq_swap]), ih (Walk.IsTrail.mk hnd.2)⟩
        exact aux _ hPQ1.isTrail
      have hnb_PQ2 : IsNonBacktracking (Pb.append Q₂) := by
        have aux : ∀ {a c : V} (q : G.Walk a c), q.IsTrail → IsNonBacktracking q := by
          intro a c q; induction q with
          | nil => intro _; trivial
          | cons _ r ih => intro ht; cases r with
            | nil => trivial
            | cons _ _ =>
                have hnd := ht.edges_nodup; simp only [Walk.edges_cons, List.nodup_cons] at hnd
                exact ⟨fun h => by subst h; exact hnd.1 (by simp [Sym2.eq_swap]), ih (Walk.IsTrail.mk hnd.2)⟩
        exact aux _ hPQ2.isTrail
      have hPQ1_cnb : IsCyclicallyNonBacktracking (Pb.append Q₁) := by
        obtain ⟨a₁, b₁, ha₁, hb₁, m₁, hab₁, hc1s, _, _, _⟩ := strip_cycle_ends (Pb.append Q₁) hPQ1 (by omega)
        have hf : firstNbr (Pb.append Q₁) = some a₁ := by rw [hc1s]; rfl
        have hl : lastNbr (Pb.append Q₁) = some b₁ := by
          rw [hc1s]
          have : Walk.cons ha₁ (m₁.append (.cons hb₁ .nil)) = (Walk.cons ha₁ m₁).append (.cons hb₁ .nil) := by simp
          rw [this, lastNbr_append_of_pos _ _ (by simp)]; rfl
        rw [IsCyclicallyNonBacktracking, isNonBacktracking_append_iff]
        exact ⟨hnb_PQ1, hnb_PQ1, fun a c ha hc heq => hab₁ (by rw [hl] at ha; rw [hf] at hc; simp at ha hc; omega)⟩
      have hnb_Q₂ : IsNonBacktracking Q₂ := isNonBacktracking_of_append_right hnb_PQ2
      obtain ⟨v3, u3, hv3, hu3, mid, hQ₂_eq, hfnQ2, hlnQ2, hmid_len, hmid_nb, hmid_fn⟩ :=
        strip_walk_ends Q₂ hnb_Q₂ (by omega)
      have hsp_eq : ∀ {a c d : V} (p₁ : G.Walk a c) (p₂ : G.Walk c d) (m : ℕ) (hm : m = p₁.length),
          splitWalk m (p₁.append p₂) (by rw [Walk.length_append]; omega) =
            ⟨c, ⟨p₁, hm.symm⟩, ⟨p₂, by rw [Walk.length_append]; omega⟩⟩ := by
        intro a c d p₁
        induction p₁ with
        | nil => intro p₂ m hm; subst hm; rfl
        | cons h r ih =>
            intro p₂ m hm
            cases m with
            | zero => simp at hm
            | succ m' =>
                have hm' : m' = r.length := by simp at hm; omega
                simp only [Walk.cons_append, splitWalk]; rw [ih p₂ m' hm']
      have hsp := hsp_eq Pb Q₁ b hPblen.symm
      have hv3_ne_Pb : v3 ≠ Pb.reverse.snd := by
        have hln : lastNbr Pb = some Pb.reverse.snd := by
          rw [← firstNbr_reverse]
          cases hrv : Pb.reverse with
          | nil => have := Walk.length_reverse Pb; rw [hrv] at this; simp at this; omega
          | cons _ _ => rfl
        exact ((isNonBacktracking_append_iff Pb Q₂).mp hnb_PQ2).2.2 _ v3 hln hfnQ2 |>.symm
      have hv3_ne_Q1 : v3 ≠ Q₁.snd := by
        have hfn1 : firstNbr Q₁ = some Q₁.snd := by
          cases hq : Q₁ with
          | nil => simp [Walk.length_append] at hc1len; omega
          | cons _ _ => rfl
        intro heq; exact hfnQ (hfn1.trans (by rw [← heq, ← hfnQ2]))
      have hu3_ne_Pb : u3 ≠ (Pb.append Q₁).snd := by
        have hPQ2_cnb : IsCyclicallyNonBacktracking (Pb.append Q₂) := by
          obtain ⟨a₁, b₁, ha₁, hb₁, m₁, hab₁, hc2s, _, _, _⟩ := strip_cycle_ends (Pb.append Q₂) hPQ2 (by omega)
          have hf : firstNbr (Pb.append Q₂) = some a₁ := by rw [hc2s]; rfl
          have hl : lastNbr (Pb.append Q₂) = some b₁ := by
            rw [hc2s]
            have : Walk.cons ha₁ (m₁.append (.cons hb₁ .nil)) = (Walk.cons ha₁ m₁).append (.cons hb₁ .nil) := by simp
            rw [this, lastNbr_append_of_pos _ _ (by simp)]; rfl
          rw [IsCyclicallyNonBacktracking, isNonBacktracking_append_iff]
          exact ⟨hnb_PQ2, hnb_PQ2, fun a c ha hc heq => hab₁ (by rw [hl] at ha; rw [hf] at hc; simp at ha hc; omega)⟩
        have hl2 : lastNbr (Pb.append Q₂) = some u3 := by
          rw [lastNbr_append_of_pos Pb Q₂ (by omega), hlnQ2]
        have hf2 : firstNbr (Pb.append Q₂) = some (Pb.append Q₁).snd := by
          rw [firstNbr_append_of_pos Pb Q₂ (by omega), ← firstNbr_append_of_pos Pb Q₁ (by omega)]
          cases hq : Pb.append Q₁ with
          | nil => simp [hq] at hc1len; omega
          | cons _ _ => rfl
        exact ((isNonBacktracking_append_iff _ _).mp hPQ2_cnb).2.2 u3 _ hl2 hf2
      have hu3_ne_Q1 : u3 ≠ (Pb.append Q₁).reverse.snd := by
        have hl1 : lastNbr Q₁ = some (Pb.append Q₁).reverse.snd := by
          rw [← lastNbr_append_of_pos Pb Q₁ (by simp [Walk.length_append] at hc1len; omega), ← firstNbr_reverse]
          cases hrv : (Pb.append Q₁).reverse with
          | nil => have := Walk.length_reverse (Pb.append Q₁); rw [hrv] at this; simp at this; omega
          | cons _ _ => rfl
        intro heq; exact hlnQ (hl1.trans (by rw [← heq, ← hlnQ2]))
      let y : Σ _ : Fin L, Σ c1 : Σ u : V, {q : G.Walk u u // q.length = r₁},
          Σ v3 : V, Σ u3 : V, {q : G.Walk v3 u3 // q.length = r₂ - b - 2} :=
        ⟨j, ⟨u, ⟨Pb.append Q₁, hc1len⟩⟩, v3, u3, ⟨mid, by omega⟩⟩
      refine ⟨y, ?_, ?_⟩
      · simp only [Param, Finset.mem_sigma, Finset.mem_univ, true_and, TL, Finset.mem_filter,
          mem_nbWalksSub_iff, v3Set, u3Set, Finset.mem_erase,
          SimpleGraph.mem_neighborFinset, nbWalksBetweenAvoid]
        rw [hsp]
        exact ⟨⟨hnb_PQ1, hPQ1_cnb⟩, ⟨hv3_ne_Q1, hv3_ne_Pb, hv3⟩,
          ⟨hu3_ne_Q1, hu3_ne_Pb, hu3.symm⟩, ⟨hmid_nb, hmid_fn⟩⟩
      · dsimp only [evalTh, y]
        rw [hsp]
        have hcond_e : G.Adj w v3 ∧ G.Adj u3 u := ⟨hv3, hu3⟩
        simp only [hcond_e, ↓reduceDIte]
        congr 1
        simpa only [← hQ₂_eq] using hunr
    by_cases hne : S_rb.Nonempty
    · obtain ⟨x0, hx0⟩ := hne
      let y0 := Classical.choose (hpre_th x0 hx0)
      let f' : (Σ v : V, {q : G.Walk v v // q.length = L}) → _ := fun x =>
        if h : x ∈ S_rb then Classical.choose (hpre_th x h) else y0
      have hle1 : S_rb.card ≤ Param.card := by
        refine Finset.card_le_card_of_injOn f' ?_ ?_
        · intro x hx; dsimp only [f']; simp only [hx, ↓reduceDIte]; exact (Classical.choose_spec (hpre_th x hx)).1
        · intro x₁ h₁ x₂ h₂ heq
          have hev1 : evalTh (f' x₁) = some x₁ := by
            dsimp only [f']; simp only [h₁, ↓reduceDIte]; exact (Classical.choose_spec (hpre_th x₁ h₁)).2
          have hev2 : evalTh (f' x₂) = some x₂ := by
            dsimp only [f']; simp only [h₂, ↓reduceDIte]; exact (Classical.choose_spec (hpre_th x₂ h₂)).2
          exact Option.some.inj (hev1.symm.trans (congrArg evalTh heq |>.trans hev2))
      exact le_trans hle1 hParam_card
    · rw [Finset.not_nonempty_iff_eq_empty] at hne; simp [hne]
  · simp only [hcond, ↓reduceIte, zero_mul]
    have hemp : ∀ b, NS_th.filter (isThRB r₁ b) = ∅ := fun b => by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      simp only [Finset.mem_filter] at hx
      obtain ⟨_, _, _, _, _, _, _, _, _, _, hg₁, hlt12, hnp1, hnp2, _⟩ := hx.2
      exact hcond ⟨hg₁, hlt12, hnp1, hnp2⟩
    refine Finset.sum_eq_zero fun b _ => by simp [hemp b]

/-- **Main Combinatorial Theorem (100% Unconditional Non-Simple Walk Upper Bound)**:
For EVERY cubic (`d = 3`), power-free (`¬ HasPower G`) simple graph `G` of girth `g ≥ 6`
and target power-of-2 length `L = 2^k` (`k ≥ 4`, `L < 3 * g`, `L ≤ 64`):
`nonSimpleTaillessCount G L ≤ ∑ r ∈ Finset.range L, alphaCoeff g L r * taillessCount G r`. -/
theorem nonSimpleTaillessCount_le_sum_alpha (G : SimpleGraph V) [DecidableRel G.Adj]
    {g k : ℕ} (hreg : ∀ v : V, G.degree v = 3) (hg : GirthAtLeast G g) (hg6 : 6 ≤ g)
    (hnp : ¬ HasPower G) (hk4 : 4 ≤ k) (hk6 : k ≤ 6) (hLt : 2 ^ k < 3 * g) :
    nonSimpleTaillessCount G (2 ^ k) ≤
      ∑ r ∈ Finset.range (2 ^ k), alphaCoeff g (2 ^ k) r * taillessCount G r := by
  set L := 2 ^ k
  haveI : DecidablePred (fun x : Σ v : V, {p : G.Walk v v // p.length = L} =>
    IsCyclicallyNonBacktracking x.2.1 ∧ ¬ x.2.1.IsCycle) := Classical.decPred _
  let NS := ((Finset.univ : Finset V).sigma fun v => nbWalksSub G L v v).filter
    fun x => IsCyclicallyNonBacktracking x.2.1 ∧ ¬ x.2.1.IsCycle
  have hNS_card : NS.card = nonSimpleTaillessCount G L :=
    nonSimpleTaillessCount_eq_card_sub G L
  rw [← hNS_card]
  haveI : DecidablePred (isBarbellElem G g L) := Classical.decPred _
  have hpart : NS.card =
      (NS.filter (isBarbellElem G g L)).card +
      (NS.filter fun x => ¬ isBarbellElem G g L x).card :=
    (Finset.card_filter_add_card_filter_not (s := NS) (p := isBarbellElem G g L)).symm
  rw [hpart]
  have hrhs : (∑ r ∈ Finset.range L, alphaCoeff g L r * taillessCount G r) =
      (∑ r ∈ Finset.range L, barbellTerm g L r * taillessCount G r) +
      (∑ r ∈ Finset.range L, thetaTerm g L r * taillessCount G r) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    unfold alphaCoeff; ring
  rw [hrhs]
  exact Nat.add_le_add
    (nonSimple_barbell_card_le G hreg hg hg6 hnp hk4 hk6 hLt)
    (nonSimple_theta_card_le G hreg hg hg6 hnp hk4 hk6 hLt)

end NonSimpleTheta

end E64Wave8Agent2
