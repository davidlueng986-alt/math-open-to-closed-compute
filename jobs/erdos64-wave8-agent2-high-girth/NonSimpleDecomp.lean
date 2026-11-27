import Shadow
import NonBacktrackingGirth
import Wave5Agent5GirthTripling
import Wave5Agent6ChebyshevGirth
import ChebTraceEngine
import NonSimpleHelpers

namespace E64Wave8Agent2
open SimpleGraph Erdos64Closure E64NonBacktrackingGirth E64Wave5Agent5 E64Wave5Agent6

section NonSimpleDecomp

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem tailless_nonSimple_rotation_decomp {G : SimpleGraph V}
    {g L : ℕ} (hg : GirthAtLeast G g) (hLt : L < 3 * g)
    {v : V} (p : G.Walk v v) (hcyc : IsCyclicallyNonBacktracking p) (hns : ¬ p.IsCycle)
    (hlen : p.length = L) (hL1 : 1 ≤ L) :
    ∃ (j : Fin L) (u w : V) (c₁ : G.Walk u u) (P : G.Walk u w) (c₂ : G.Walk w w),
      c₁.IsCycle ∧ c₂.IsCycle ∧
      g ≤ c₁.length ∧ g ≤ c₂.length ∧
      c₁.length + c₂.length + 2 * P.length = L ∧
      IsCyclicallyNonBacktracking (c₁.append (P.append (c₂.append P.reverse))) ∧
      unrotate L j (c₁.append (P.append (c₂.append P.reverse)))
        (by simp only [Walk.length_append, Walk.length_reverse]; omega) = ⟨v, ⟨p, hlen⟩⟩ := by
  have hnb : IsNonBacktracking p := isNonBacktracking_of_append_left hcyc
  have hnd : ¬ p.support.tail.Nodup := by
    intro hnd
    apply hns
    cases p with
    | nil => simp at hlen; omega
    | cons h rest =>
        have hrest_nd : rest.support.Nodup := by simpa [Walk.support_cons] using hnd
        have hrest_path : rest.IsPath := Walk.IsPath.mk' hrest_nd
        have hnotmem : s(v, _) ∉ rest.edges := by
          intro hmem
          cases rest with
          | nil => simp at hmem
          | cons h₂ rest₂ =>
              simp only [Walk.edges_cons, List.mem_cons] at hmem
              simp only [Walk.support_cons, List.nodup_cons] at hrest_nd
              rcases hmem with heq | hmem₂
              · rw [Sym2.eq_iff] at heq
                rcases heq with ⟨hvc, _⟩ | ⟨rfl, _⟩
                · exact G.ne_of_adj h hvc
                · cases rest₂ with
                  | nil => exact hnb.1 rfl
                  | cons _ r₃ =>
                      simp only [Walk.support_cons, List.nodup_cons] at hrest_nd
                      exact hrest_nd.2.1 (Walk.end_mem_support r₃)
              · have aux2 : ∀ {a b : V} (w : G.Walk a b) {x y : V}, s(x, y) ∈ w.edges → y ∈ w.support := by
                  intro a b w
                  induction w with
                  | nil => intro _ _ h; simp at h
                  | cons _ r ih =>
                      intro x y hm
                      simp only [Walk.edges_cons, List.mem_cons] at hm
                      rcases hm with h0 | h0
                      · rw [Sym2.eq_iff] at h0
                        rcases h0 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                        · exact List.mem_cons_of_mem _ (Walk.start_mem_support r)
                        · exact Walk.start_mem_support _
                      · exact List.mem_cons_of_mem _ (ih h0)
                exact hrest_nd.1 (aux2 rest₂ hmem₂)
        have htrail : (Walk.cons h rest).IsTrail := by
          refine ⟨?_⟩
          simp only [Walk.edges_cons, List.nodup_cons]
          exact ⟨hnotmem, hrest_path.isTrail.edges_nodup⟩
        exact ⟨htrail, by simp, hnd⟩
  -- Now split `p` at a repeated vertex in `p.support.tail`
  have hsplit_rep : ∀ {a b : V} (w : G.Walk a b), ¬ w.support.tail.Nodup →
      ∃ (x : V) (w₁ : G.Walk a x) (w₂ : G.Walk x x) (w₃ : G.Walk x b),
        w = w₁.append (w₂.append w₃) ∧ 1 ≤ w₁.length ∧ 1 ≤ w₂.length := by
    intro a b w
    induction w with
    | nil => intro h; simp at h
    | cons h rest ih =>
        rename_i c
        intro hnd'
        have hnd'' : ¬ rest.support.Nodup := by simpa [Walk.support_cons] using hnd'
        cases rest with
        | nil => simp at hnd''
        | cons h₂ rest₂ =>
            simp only [Walk.support_cons, List.nodup_cons, not_and_or, not_not] at hnd''
            rcases hnd'' with hmem | hnd₂
            · have hmem_tail : c ∈ (Walk.cons h₂ rest₂).support.tail := by
                simpa [Walk.support_cons] using hmem
              have hex_app : ∀ {p0 p1 : V} (q : G.Walk p0 p1) {z : V},
                  z ∈ q.support → ∃ (q₁ : G.Walk p0 z) (q₂ : G.Walk z p1), q = q₁.append q₂ := by
                intro p0 p1 q
                induction q with
                | nil => intro z hz; simp at hz; subst hz; exact ⟨.nil, .nil, rfl⟩
                | cons h' r' ihr =>
                    intro z hz
                    simp only [Walk.support_cons, List.mem_cons] at hz
                    rcases hz with rfl | hmem'
                    · exact ⟨.nil, .cons h' r', rfl⟩
                    · obtain ⟨q₁, q₂, heq⟩ := ihr hmem'
                      exact ⟨.cons h' q₁, q₂, by rw [Walk.cons_append, ← heq]⟩
              obtain ⟨q₁, q₂, heq⟩ := hex_app rest₂ (by simpa [Walk.support_cons] using hmem_tail)
              exact ⟨c, .cons h .nil, .cons h₂ q₁, q₂, by simp [heq], by simp, by simp⟩
            · obtain ⟨x, w₁, w₂, w₃, heq, hw₁, hw₂⟩ := ih (by simpa [Walk.support_cons] using hnd₂)
              exact ⟨x, .cons h w₁, w₂, w₃, by simp [heq], by simp; omega, hw₂⟩
  obtain ⟨x, p₁, p₂, p₃, hp_eq, hp₁_pos, hp₂_pos⟩ := hsplit_rep p hnd
  have hnb₂ : IsNonBacktracking p₂ :=
    isNonBacktracking_of_append_left (isNonBacktracking_of_append_right (hp_eq ▸ hnb))
  have hpp : p.append p = p₁.append (p₂.append ((p₃.append p₁).append (p₂.append p₃))) := by
    conv_lhs => rw [hp_eq]; simp only [Walk.append_assoc]
  have hnb₃₁ : IsNonBacktracking (p₃.append p₁) :=
    isNonBacktracking_of_append_left
      (isNonBacktracking_of_append_right (isNonBacktracking_of_append_right (hpp ▸ hcyc)))
  have hpos₃₁ : 1 ≤ (p₃.append p₁).length := by rw [Walk.length_append]; omega
  obtain ⟨u, t₁, c₁, hc₁_cyc, hc₁_pos, hp₂_eq, hp₂_len⟩ :=
    nonBacktracking_tail_peel p₂.length p₂ rfl hp₂_pos hnb₂
  obtain ⟨w, t₂, c₂, hc₂_cyc, hc₂_pos, hp₃₁_eq, hp₃₁_len⟩ :=
    nonBacktracking_tail_peel (p₃.append p₁).length (p₃.append p₁) rfl hpos₃₁ hnb₃₁
  have hg₁ : g ≤ c₁.length :=
    girth_le_length_of_nonBacktracking_closed hg c₁.length c₁ rfl hc₁_pos
      (isNonBacktracking_of_append_left hc₁_cyc)
  have hg₂ : g ≤ c₂.length :=
    girth_le_length_of_nonBacktracking_closed hg c₂.length c₂ rfl hc₂_pos
      (isNonBacktracking_of_append_left hc₂_cyc)
  have hsum : L = p₂.length + (p₃.append p₁).length := by
    rw [← hlen, hp_eq, Walk.length_append, Walk.length_append, Walk.length_append]; omega
  have hlt₁ : c₁.length < 2 * g := by omega
  have hlt₂ : c₂.length < 2 * g := by omega
  have hc₁ : c₁.IsCycle := tailless_nonBacktracking_lt_two_girth_isCycle hg c₁ hc₁_cyc hc₁_pos hlt₁
  have hc₂ : c₂.IsCycle := tailless_nonBacktracking_lt_two_girth_isCycle hg c₂ hc₂_cyc hc₂_pos hlt₂
  let P : G.Walk u w := t₁.reverse.append t₂
  let a : G.Walk v u := p₁.append t₁
  let b : G.Walk u v := (c₁.append (t₁.reverse.append p₃))
  have hp_ab : p = a.append b := by
    dsimp only [a, b]
    rw [hp_eq, hp₂_eq]
    simp only [Walk.append_assoc]
  have hba_eq : b.append a = c₁.append (P.append (c₂.append P.reverse)) := by
    dsimp only [a, b, P]
    have hP_rev : (t₁.reverse.append t₂).reverse = t₂.reverse.append t₁ := by
      simp [Walk.reverse_append]
    rw [hP_rev]
    calc (c₁.append (t₁.reverse.append p₃)).append (p₁.append t₁)
        = c₁.append (t₁.reverse.append ((p₃.append p₁).append t₁)) := by simp only [Walk.append_assoc]
      _ = c₁.append (t₁.reverse.append ((t₂.append (c₂.append t₂.reverse)).append t₁)) := by rw [hp₃₁_eq]
      _ = c₁.append ((t₁.reverse.append t₂).append (c₂.append (t₂.reverse.append t₁))) := by
            simp only [Walk.append_assoc]
  have hP_len : P.length = t₁.length + t₂.length := by
    simp [P, Walk.length_append, Walk.length_reverse]
  have hlen_tot : c₁.length + c₂.length + 2 * P.length = L := by omega
  have ha_lt : a.length < L := by
    have : a.length + b.length = L := by rw [← Walk.length_append, ← hp_ab, hlen]
    have hb_pos : 1 ≤ b.length := by
      dsimp only [b]; rw [Walk.length_append]; omega
    omega
  have hrot_cyc : IsCyclicallyNonBacktracking (c₁.append (P.append (c₂.append P.reverse))) := by
    rw [← hba_eq]
    exact isCyclicallyNonBacktracking_rotate a b (hp_ab ▸ hcyc)
  have hunrot := unrotate_append a b (hp_ab ▸ hlen) ha_lt
  refine ⟨⟨a.length, ha_lt⟩, u, w, c₁, P, c₂, hc₁, hc₂, hg₁, hg₂, hlen_tot, hrot_cyc, ?_⟩
  simpa only [hba_eq, ← hp_ab] using hunrot

/-- **Maximal Shared Prefix Lemma for Zero-Tail Cubic Cycles**:
If `c₁, c₂ : G.Walk x x` are simple cycles in a cubic graph with `3 ≤ c₁.length < c₂.length`
and `c₁ ++ c₂` is CNB, then some cyclic rotation of `c₁ ++ c₂` equals `(P_b ++ Q₁) ++ (P_b ++ Q₂)`
where `c₁' = P_b ++ Q₁` and `c₂' = P_b ++ Q₂` are simple cycles of lengths `c₁.length, c₂.length`,
`1 ≤ P_b.length < c₁.length`, `firstNbr Q₁ ≠ firstNbr Q₂`, and `lastNbr Q₁ ≠ lastNbr Q₂`. -/
theorem exists_maximal_shared_prefix {G : SimpleGraph V} [DecidableRel G.Adj]
    (hreg : ∀ z : V, G.degree z = 3) {L : ℕ} {x : V}
    (c₁ c₂ : G.Walk x x) (hc₁ : c₁.IsCycle) (hc₂ : c₂.IsCycle)
    (h3 : 3 ≤ c₁.length) (hlt : c₁.length < c₂.length) (hsum : c₁.length + c₂.length = L)
    (hcyc : IsCyclicallyNonBacktracking (c₁.append c₂)) :
    ∃ (d : Fin L) (u w : V) (Pb : G.Walk u w) (Q₁ Q₂ : G.Walk w u),
      1 ≤ Pb.length ∧ Pb.length < c₁.length ∧
      (Pb.append Q₁).IsCycle ∧ (Pb.append Q₂).IsCycle ∧
      (Pb.append Q₁).length = c₁.length ∧ (Pb.append Q₂).length = c₂.length ∧
      firstNbr Q₁ ≠ firstNbr Q₂ ∧ lastNbr Q₁ ≠ lastNbr Q₂ ∧
      IsCyclicallyNonBacktracking (Q₁.append Q₂.reverse) ∧
      unrotate L d ((Pb.append Q₁).append (Pb.append Q₂))
        (by simp only [Walk.length_append]; omega) = ⟨x, ⟨c₁.append c₂, hsum⟩⟩ := by
  have hprefix : ∀ (n : ℕ) {a b₁ b₂ : V} (p₁ : G.Walk a b₁) (p₂ : G.Walk a b₂),
      p₁.length = n → p₁.length < p₂.length →
      ∃ (w : V) (pre : G.Walk a w) (q₁ : G.Walk w b₁) (q₂ : G.Walk w b₂),
        p₁ = pre.append q₁ ∧ p₂ = pre.append q₂ ∧
        (q₁.length = 0 ∨ firstNbr q₁ ≠ firstNbr q₂) := by
    intro n
    induction n with
    | zero =>
        intro a b₁ b₂ p₁ p₂ hp₁ _
        cases p₁ with
        | nil => exact ⟨a, .nil, .nil, p₂, rfl, rfl, Or.inl rfl⟩
        | cons _ _ => simp at hp₁
    | succ n ih =>
        intro a b₁ b₂ p₁ p₂ hp₁ hlt'
        cases p₁ with
        | nil => simp at hp₁
        | cons h₁ r₁ =>
            rename_i y₁
            cases p₂ with
            | nil => simp at hlt'
            | cons h₂ r₂ =>
                rename_i y₂
                by_cases hy : y₁ = y₂
                · subst hy
                  obtain ⟨w, pre, q₁, q₂, heq₁, heq₂, hdiv⟩ :=
                    ih r₁ r₂ (by simp at hp₁; omega) (by simp at hlt'; omega)
                  exact ⟨w, .cons h₁ pre, q₁, q₂, by rw [Walk.cons_append, ← heq₁],
                    by rw [Walk.cons_append, ← heq₂], hdiv⟩
                · exact ⟨a, .nil, .cons h₁ r₁, .cons h₂ r₂, rfl, rfl,
                    Or.inr (by simp [firstNbr, hy])⟩
  have hrev_len₁ : c₁.reverse.length = c₁.length := Walk.length_reverse c₁
  have hrev_len₂ : c₂.reverse.length = c₂.length := Walk.length_reverse c₂
  obtain ⟨u, suf_rev, r₁_rev, r₂_rev, hcr₁, hcr₂, hdiv_back⟩ :=
    hprefix c₁.reverse.length c₁.reverse c₂.reverse rfl (by omega)
  let suf : G.Walk u x := suf_rev.reverse
  let pref₁ : G.Walk x u := r₁_rev.reverse
  let pref₂ : G.Walk x u := r₂_rev.reverse
  have hc₁_eq : c₁ = pref₁.append suf := by
    have := congrArg Walk.reverse hcr₁
    simpa [pref₁, suf, Walk.reverse_append] using this
  have hc₂_eq : c₂ = pref₂.append suf := by
    have := congrArg Walk.reverse hcr₂
    simpa [pref₂, suf, Walk.reverse_append] using this
  have hr₁_pos : 1 ≤ r₁_rev.length := by
    by_contra h0
    have h0' : r₁_rev.length = 0 := by omega
    cases r₁_rev with
    | cons _ _ => simp at h0'
    | nil =>
        have hlen_suf : suf.length = c₁.length := by
          have := congrArg Walk.length hc₁_eq
          simp [pref₁] at this; omega
        have hpref₂_pos : 1 ≤ pref₂.length := by
          have := congrArg Walk.length hc₂_eq
          rw [Walk.length_append] at this; omega
        have hc₂_nd : c₂.support.tail.Nodup := hc₂.support_nodup
        rw [hc₂_eq] at hc₂_nd
        have hlen_s : 1 ≤ suf.length := by omega
        cases pref₂ with
        | nil => simp at hpref₂_pos
        | cons hp₂ pr₂ =>
            cases suf with
            | nil => simp at hlen_s
            | cons hs sr =>
                simp only [Walk.cons_append, Walk.support_cons, List.tail_cons] at hc₂_nd
                rw [Walk.support_append] at hc₂_nd
                simp only [Walk.support_cons, List.tail_cons, List.nodup_append] at hc₂_nd
                exact hc₂_nd.2.2 x (Walk.end_mem_support pr₂) (Walk.end_mem_support sr) rfl
  let c₁' : G.Walk u u := suf.append pref₁
  let c₂' : G.Walk u u := suf.append pref₂
  have hc₁'_len : c₁'.length = c₁.length := by
    rw [hc₁_eq, Walk.length_append, Walk.length_append]; omega
  have hc₂'_len : c₂'.length = c₂.length := by
    rw [hc₂_eq, Walk.length_append, Walk.length_append]; omega
  have hrot_cycle : ∀ {a b : V} (p₁ : G.Walk a b) (p₂ : G.Walk b a),
      (p₁.append p₂).IsCycle → (p₂.append p₁).IsCycle := fun p₁ p₂ h => h.rotate
  have hc₁' : c₁'.IsCycle := hrot_cycle pref₁ suf (hc₁_eq ▸ hc₁)
  have hc₂' : c₂'.IsCycle := hrot_cycle pref₂ suf (hc₂_eq ▸ hc₂)
  obtain ⟨w, Pb, Q₁, Q₂, hc₁'_eq, hc₂'_eq, hdiv_fwd⟩ :=
    hprefix c₁'.length c₁' c₂' rfl (by omega)
  have hQ₁_pos : 1 ≤ Q₁.length := by
    by_contra h0
    have h0' : Q₁.length = 0 := by omega
    cases Q₁ with
    | cons _ _ => simp at h0'
    | nil =>
        have hPb_pos : 1 ≤ Pb.length := by
          have := congrArg Walk.length hc₁'_eq; simp at this; omega
        have hQ₂_pos : 1 ≤ Q₂.length := by
          have := congrArg Walk.length hc₂'_eq; rw [Walk.length_append] at this; omega
        have hc₂'_nd := hc₂'.support_nodup
        rw [hc₂'_eq] at hc₂'_nd
        cases Pb with
        | nil => simp at hPb_pos
        | cons hp pr =>
            cases Q₂ with
            | nil => simp at hQ₂_pos
            | cons hq qr =>
                simp only [Walk.cons_append, Walk.support_cons, List.tail_cons] at hc₂'_nd
                rw [Walk.support_append] at hc₂'_nd
                simp only [Walk.support_cons, List.tail_cons, List.nodup_append] at hc₂'_nd
                exact hc₂'_nd.2.2 u (Walk.end_mem_support pr) (Walk.end_mem_support qr) rfl
  have hQ₂_pos : 1 ≤ Q₂.length := by
    have := congrArg Walk.length hc₁'_eq
    have := congrArg Walk.length hc₂'_eq
    simp only [Walk.length_append] at *; omega
  have hfn_ne : firstNbr Q₁ ≠ firstNbr Q₂ := hdiv_fwd.resolve_left (by omega)
  have hln_ne_c : lastNbr c₁' ≠ lastNbr c₂' := by
    have h1 : lastNbr c₁' = lastNbr pref₁ := lastNbr_append_of_pos suf pref₁ (by simp [pref₁]; omega)
    have h2 : lastNbr c₂' = lastNbr pref₂ := by
      have hp₂_pos : 1 ≤ pref₂.length := by
        have := congrArg Walk.length hc₁_eq
        have := congrArg Walk.length hc₂_eq
        simp only [Walk.length_append] at *; omega
      exact lastNbr_append_of_pos suf pref₂ hp₂_pos
    rw [h1, h2]
    have hrev1 : lastNbr pref₁ = firstNbr r₁_rev := by
      dsimp only [pref₁]; rw [lastNbr_reverse]
    have hrev2 : lastNbr pref₂ = firstNbr r₂_rev := by
      dsimp only [pref₂]; rw [lastNbr_reverse]
    rw [hrev1, hrev2]
    exact hdiv_back.resolve_left (by omega)
  have hln_ne : lastNbr Q₁ ≠ lastNbr Q₂ := by
    have h1 : lastNbr c₁' = lastNbr Q₁ := hc₁'_eq ▸ lastNbr_append_of_pos Pb Q₁ hQ₁_pos
    have h2 : lastNbr c₂' = lastNbr Q₂ := hc₂'_eq ▸ lastNbr_append_of_pos Pb Q₂ hQ₂_pos
    rw [← h1, ← h2]
    exact hln_ne_c
  have hPb_pos : 1 ≤ Pb.length := by
    by_contra h0
    have h0' : Pb.length = 0 := by omega
    cases Pb with
    | cons _ _ => simp at h0'
    | nil =>
        have hfn_c : firstNbr c₁' ≠ firstNbr c₂' := by
          simpa [hc₁'_eq, hc₂'_eq] using hfn_ne
        have hsuf0 : suf.length = 0 := by
          by_contra hs
          have hs1 : 1 ≤ suf.length := by omega
          have e1 : firstNbr c₁' = firstNbr suf := firstNbr_append_of_pos suf pref₁ hs1
          have e2 : firstNbr c₂' = firstNbr suf := firstNbr_append_of_pos suf pref₂ hs1
          exact hfn_c (e1.trans e2.symm)
        cases suf with
        | cons _ _ => simp at hsuf0
        | nil =>
            obtain ⟨a₁, b₁, ha₁, hb₁, _, hne1, hc₁_s, _, _, _⟩ := strip_cycle_ends c₁ hc₁ h3
            obtain ⟨a₂, b₂, ha₂, hb₂, _, hne2, hc₂_s, _, _, _⟩ := strip_cycle_ends c₂ hc₂ (by omega)
            have hnb_12 : IsNonBacktracking (c₁.append c₂) := isNonBacktracking_of_append_left hcyc
            have hnb_21 : IsNonBacktracking (c₂.append c₁) :=
              isNonBacktracking_of_append_left (isCyclicallyNonBacktracking_rotate c₁ c₂ hcyc)
            have hfn1 : firstNbr c₁ = some a₁ := by rw [hc₁_s]; rfl
            have hln1 : lastNbr c₁ = some b₁ := by
              rw [hc₁_s]
              have : Walk.cons ha₁ (_ ++ .cons hb₁ .nil) = (Walk.cons ha₁ _).append (.cons hb₁ .nil) := by simp
              rw [this, lastNbr_append_of_pos _ _ (by simp)]; rfl
            have hfn2 : firstNbr c₂ = some a₂ := by rw [hc₂_s]; rfl
            have hln2 : lastNbr c₂ = some b₂ := by
              rw [hc₂_s]
              have : Walk.cons ha₂ (_ ++ .cons hb₂ .nil) = (Walk.cons ha₂ _).append (.cons hb₂ .nil) := by simp
              rw [this, lastNbr_append_of_pos _ _ (by simp)]; rfl
            have hb1a2 : b₁ ≠ a₂ := (isNonBacktracking_append_iff c₁ c₂).mp hnb_12 |>.2.2 b₁ a₂ hln1 hfn2
            have hb2a1 : b₂ ≠ a₁ := (isNonBacktracking_append_iff c₂ c₁).mp hnb_21 |>.2.2 b₂ a₁ hln2 hfn1
            have hsplit := cubic_no_figure_eight_split G (le_of_eq (hreg x))
              ha₁ hb₁.symm ha₂ hb₂.symm hne1 hne2 hb2a1.symm hb1a2.symm
            rcases hsplit with ha_eq | hb_eq
            · apply hfn_c
              have e1 : c₁' = c₁ := by simp [c₁', hc₁_eq]
              have e2 : c₂' = c₂ := by simp [c₂', hc₂_eq]
              rw [e1, e2, hfn1, hfn2, ha_eq]
            · apply hln_ne_c
              have e1 : c₁' = c₁ := by simp [c₁', hc₁_eq]
              have e2 : c₂' = c₂ := by simp [c₂', hc₂_eq]
              rw [e1, e2, hln1, hln2, hb_eq]
  have hPb_lt : Pb.length < c₁.length := by
    have := congrArg Walk.length hc₁'_eq; rw [Walk.length_append] at this; omega
  have hQ12_cyc : IsCyclicallyNonBacktracking (Q₁.append Q₂.reverse) := by
    have hnb_c1' : IsNonBacktracking c₁' := by
      have htr := hc₁'.isTrail
      have aux : ∀ {a b : V} (w : G.Walk a b), w.IsTrail → IsNonBacktracking w := by
        intro a b w; induction w with
        | nil => intro _; trivial
        | cons _ r ih => intro ht; cases r with
          | nil => trivial
          | cons _ _ =>
              have hnd := ht.edges_nodup; rw [Walk.edges_cons, List.nodup_cons] at hnd
              exact ⟨fun h => by subst h; exact hnd.1 (by simp [Sym2.eq_swap]), ih (Walk.IsTrail.mk hnd.2)⟩
      exact aux _ htr
    have hnb_c2' : IsNonBacktracking c₂' := by
      have htr := hc₂'.isTrail
      have aux : ∀ {a b : V} (w : G.Walk a b), w.IsTrail → IsNonBacktracking w := by
        intro a b w; induction w with
        | nil => intro _; trivial
        | cons _ r ih => intro ht; cases r with
          | nil => trivial
          | cons _ _ =>
              have hnd := ht.edges_nodup; rw [Walk.edges_cons, List.nodup_cons] at hnd
              exact ⟨fun h => by subst h; exact hnd.1 (by simp [Sym2.eq_swap]), ih (Walk.IsTrail.mk hnd.2)⟩
      exact aux _ htr
    have hnb_Q1 : IsNonBacktracking Q₁ := isNonBacktracking_of_append_right (hc₁'_eq ▸ hnb_c1')
    have hnb_Q2 : IsNonBacktracking Q₂ := isNonBacktracking_of_append_right (hc₂'_eq ▸ hnb_c2')
    have hnb_Q2r : IsNonBacktracking Q₂.reverse := E64Wave5Agent5.isNonBacktracking_reverse hnb_Q2
    have hnb_12 : IsNonBacktracking (Q₁.append Q₂.reverse) := by
      rw [isNonBacktracking_append_iff]
      refine ⟨hnb_Q1, hnb_Q2r, ?_⟩
      intro a b ha hb
      rw [firstNbr_reverse] at hb
      intro heq; subst heq
      exact hln_ne (ha.trans hb.symm)
    rw [IsCyclicallyNonBacktracking, isNonBacktracking_append_iff]
    refine ⟨hnb_12, hnb_12, ?_⟩
    intro a b ha hb
    have ha' : lastNbr Q₂.reverse = some a := by
      rwa [lastNbr_append_of_pos Q₁ Q₂.reverse (by rw [Walk.length_reverse]; exact hQ₂_pos)] at ha
    have hb' : firstNbr Q₁ = some b := by
      rwa [firstNbr_append_of_pos Q₁ Q₂.reverse hQ₁_pos] at hb
    rw [lastNbr_reverse] at ha'
    intro heq; subst heq
    exact hfn_ne (hb'.trans ha'.symm)
  by_cases hsuf0 : suf.length = 0
  · cases suf with
    | cons _ _ => simp at hsuf0
    | nil =>
        have hrot_eq : (Pb.append Q₁).append (Pb.append Q₂) = c₁.append c₂ := by
          rw [← hc₁'_eq, ← hc₂'_eq]
          simp [c₁', c₂', hc₁_eq, hc₂_eq]
        have hunrot := unrotate_append (.nil : G.Walk x x) (c₁.append c₂) (by simpa using hsum) (by omega)
        refine ⟨⟨0, by omega⟩, x, w, Pb, Q₁, Q₂, hPb_pos, hPb_lt,
          hc₁'_eq ▸ hc₁', hc₂'_eq ▸ hc₂', by rw [← hc₁'_eq, hc₁'_len], by rw [← hc₂'_eq, hc₂'_len],
          hfn_ne, hln_ne, hQ12_cyc, ?_⟩
        simpa only [hrot_eq, Walk.nil_append, Walk.append_nil] using hunrot
  · let a_rot : G.Walk x u := (pref₁.append suf).append pref₂
    have ha_rot_lt : a_rot.length < L := by
      have : a_rot.length + suf.length = L := by
        dsimp only [a_rot]; rw [← hsum, hc₁_eq, hc₂_eq]
        simp only [Walk.length_append]; omega
      omega
    have hab_eq : a_rot.append suf = c₁.append c₂ := by
      dsimp only [a_rot]; rw [hc₁_eq, hc₂_eq]; simp only [Walk.append_assoc]
    have hba_eq : suf.append a_rot = (Pb.append Q₁).append (Pb.append Q₂) := by
      rw [← hc₁'_eq, ← hc₂'_eq]
      dsimp only [a_rot, c₁', c₂']
      simp only [Walk.append_assoc]
    have hunrot := unrotate_append a_rot suf (hab_eq ▸ hsum) ha_rot_lt
    refine ⟨⟨a_rot.length, ha_rot_lt⟩, u, w, Pb, Q₁, Q₂, hPb_pos, hPb_lt,
      hc₁'_eq ▸ hc₁', hc₂'_eq ▸ hc₂', by rw [← hc₁'_eq, hc₁'_len], by rw [← hc₂'_eq, hc₂'_len],
      hfn_ne, hln_ne, hQ12_cyc, ?_⟩
    simpa only [hba_eq, hab_eq] using hunrot


/-- A non-simple walk `x` of length `L` is a barbell element if it admits a cyclic rotation
`c₁ ++ P ++ c₂ ++ P.reverse` with `P.length ≥ 1`, `c₁, c₂` simple cycles, `g ≤ |c₁| ≤ |c₂|`. -/
def isBarbellElem (G : SimpleGraph V) (g L : ℕ)
    (x : Σ v : V, {p : G.Walk v v // p.length = L}) : Prop :=
  ∃ (j : Fin L) (u w : V) (c₁ : G.Walk u u) (P : G.Walk u w) (c₂ : G.Walk w w),
    1 ≤ P.length ∧ c₁.IsCycle ∧ c₂.IsCycle ∧
    g ≤ c₁.length ∧ c₁.length ≤ c₂.length ∧
    c₁.length + c₂.length + 2 * P.length = L ∧
    IsCyclicallyNonBacktracking (c₁.append (P.append (c₂.append P.reverse))) ∧
    unrotate L j (c₁.append (P.append (c₂.append P.reverse)))
      (by simp only [Walk.length_append, Walk.length_reverse]; omega) = x


end NonSimpleDecomp

end E64Wave8Agent2
