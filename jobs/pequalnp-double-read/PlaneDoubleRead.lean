import PEqualNP.Defs

namespace PlaneDoubleRead

open PEqualNP.CircuitLowerBounds

attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq

def witness : Circuit :=
  ⟨[
    ⟨.or, [0, 1]⟩,
    ⟨.or, [26, 3]⟩,
    ⟨.or, [27, 9]⟩,
    ⟨.and, [13, 28]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.or, [30, 4]⟩,
    ⟨.or, [31, 10]⟩,
    ⟨.or, [14, 29]⟩,
    ⟨.or, [32, 29]⟩,
    ⟨.and, [33, 34]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.or, [36, 5]⟩,
    ⟨.or, [37, 11]⟩,
    ⟨.and, [15, 38]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.or, [40, 6]⟩,
    ⟨.or, [41, 12]⟩,
    ⟨.and, [16, 42]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.or, [44, 7]⟩,
    ⟨.or, [45, 0]⟩,
    ⟨.and, [17, 46]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.or, [48, 8]⟩,
    ⟨.or, [49, 1]⟩,
    ⟨.and, [18, 50]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.or, [52, 9]⟩,
    ⟨.or, [53, 2]⟩,
    ⟨.and, [19, 54]⟩,
    ⟨.or, [7, 8]⟩,
    ⟨.or, [56, 10]⟩,
    ⟨.or, [57, 3]⟩,
    ⟨.and, [20, 58]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [60, 11]⟩,
    ⟨.or, [61, 4]⟩,
    ⟨.and, [21, 62]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [64, 12]⟩,
    ⟨.or, [65, 5]⟩,
    ⟨.and, [22, 66]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [68, 0]⟩,
    ⟨.or, [69, 6]⟩,
    ⟨.and, [23, 70]⟩,
    ⟨.or, [11, 12]⟩,
    ⟨.or, [72, 1]⟩,
    ⟨.or, [73, 7]⟩,
    ⟨.and, [24, 74]⟩,
    ⟨.or, [12, 0]⟩,
    ⟨.or, [76, 2]⟩,
    ⟨.or, [77, 8]⟩,
    ⟨.and, [25, 78]⟩,
    ⟨.or, [35, 39]⟩,
    ⟨.or, [80, 43]⟩,
    ⟨.or, [81, 47]⟩,
    ⟨.or, [82, 51]⟩,
    ⟨.or, [83, 55]⟩,
    ⟨.or, [84, 59]⟩,
    ⟨.or, [85, 63]⟩,
    ⟨.or, [86, 67]⟩,
    ⟨.or, [87, 71]⟩,
    ⟨.or, [88, 75]⟩,
    ⟨.or, [89, 79]⟩
  ], 90⟩

theorem witness_size : witness.size = 65 := rfl

-- The posted desk statement, kept verbatim apart from layout.
def Desk2081 : Prop :=
  have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ))
  have x2 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x2 : Fin (13 : ℕ) → Bool) (x3 : Fin (13 : ℕ)) => !(x2 x3 || x2 (x3 + (1 : Fin (13 : ℕ))) || x2 (x3 + (3 : Fin (13 : ℕ))) || x2 (x3 + (9 : Fin (13 : ℕ))))
  ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x3.size ≤ (64 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧       (∀ x4 ∈ x3.gates, x4.inputs.Nodup) ∧         (∀ (x4 x5 : Fin (13 : ℕ)), x1 x4 x5 → x3.eval (List.ofFn fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x4)) (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x5)) x7) = Bool.true) ∧           (∀ (x4 : Fin (13 : ℕ) → Bool), (∀ (x5 : Fin (13 : ℕ)), x4 x5 = Bool.false → ∃ (x7 : Fin (13 : ℕ)), x1 x5 x7 ∧ x2 x4 x7 = Bool.true) → x3.eval (List.ofFn fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases x4 (x2 x4) x6) = Bool.false) ∧             ∀ (x4 : Bool),               ∃ (x5 : ℕ → Bool),                 (∀ x6 < (26 : ℕ), x5 x6 = Decidable.decide (x6 = if x4 = Bool.true then (0 : ℕ) else (13 : ℕ))) ∧                   (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 x9 : ℕ),                       x3.gates[x6]? = Option.some x7 →                         x7.inputs = [x8, x9] →                           have x12 : List Bool := x3.wires (List.ofFn fun (x12 : Fin (26 : ℕ)) => Decidable.decide (↑x12 = if x4 = Bool.true then (13 : ℕ) else (0 : ℕ)));                           (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5 ((26 : ℕ) + x6) = (x12.getD x8 Bool.false && x5 x9 || x5 x8 && x12.getD x9 Bool.false)) ∧ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5 ((26 : ℕ) + x6) = (x5 x8 || x5 x9))) ∧                     x5 x3.output = Bool.false

abbrev Desk2082 : Prop := ¬ Desk2081

def Candidate (limit : Nat) : Prop :=
  let incident := fun (p l : Fin 13) => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
  let compatible := fun (points : Fin 13 → Bool) (l : Fin 13) =>
    !(points l || points (l + 1) || points (l + 3) || points (l + 9))
  ∃ C : Circuit,
    C.size ≤ limit ∧
    PEqualNP.TopForm.IsAO2 26 C ∧
    (∀ g ∈ C.gates, g.inputs.Nodup) ∧
    (∀ p l : Fin 13, incident p l →
      C.eval (List.ofFn (Fin.addCases (fun i => decide (i = p)) (fun i => decide (i = l)))) = true) ∧
    (∀ points : Fin 13 → Bool,
      (∀ p, points p = false → ∃ l, incident p l ∧ compatible points l = true) →
      C.eval (List.ofFn (Fin.addCases points (compatible points))) = false) ∧
    ∀ side : Bool, ∃ mark : Nat → Bool,
      (∀ i < 26, mark i = decide (i = if side then 0 else 13)) ∧
      (∀ j : Nat, ∀ g : Gate, ∀ a b : Nat,
        C.gates[j]? = some g → g.inputs = [a, b] →
        let values := C.wires (List.ofFn fun i : Fin 26 => decide (i.val = if side then 13 else 0))
        (g.op = .and → mark (26 + j) =
          ((values.getD a false && mark b) || (mark a && values.getD b false))) ∧
        (g.op = .or → mark (26 + j) = (mark a || mark b))) ∧
      mark C.output = false

theorem candidate64_is_desk : Candidate 64 ↔ Desk2081 := Iff.rfl

def hasPoint (p : Fin 13 → Bool) (l : Fin 13) : Bool :=
  (((p l || p (l + 1)) || p (l + 3)) || p (l + 9))

def lines : List (Fin 13) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

def incidence (p l : Fin 13 → Bool) : Bool :=
  lines.foldl (fun a j => a || (l j && hasPoint p j)) false

def trace (k : Bool) (w : Nat) : Bool :=
  if k then decide (w ∈ [0, 26, 27, 28, 29, 33, 34, 46, 69, 70, 76, 77, 78]) else decide (w ∈ [13, 29, 33, 34])

private theorem gateAnd (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  simp [GateOp.eval]

private theorem gateOr (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  simp [GateOp.eval]

private theorem factor (a b c : Bool) : ((b || a) && (c || a)) = (a || (b && c)) := by
  cases a <;> cases b <;> cases c <;> rfl

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem eval_eq (p l : Fin 13 → Bool) :
    witness.eval (List.ofFn (Fin.addCases p l)) = incidence p l := by
  have hi : List.ofFn (Fin.addCases p l) = [p 0, p 1, p 2, p 3, p 4, p 5, p 6, p 7, p 8, p 9, p 10, p 11, p 12, l 0, l 1, l 2, l 3, l 4, l 5, l 6, l 7, l 8, l 9, l 10, l 11, l 12] := by rfl
  have hv : witness.eval (List.ofFn (Fin.addCases p l)) = (((((((((((((l 1 || (l 0 && (((p 0 || p 1) || p 3) || p 9))) && ((((p 1 || p 2) || p 4) || p 10) || (l 0 && (((p 0 || p 1) || p 3) || p 9)))) || (l 2 && (((p 2 || p 3) || p 5) || p 11))) || (l 3 && (((p 3 || p 4) || p 6) || p 12))) || (l 4 && (((p 4 || p 5) || p 7) || p 0))) || (l 5 && (((p 5 || p 6) || p 8) || p 1))) || (l 6 && (((p 6 || p 7) || p 9) || p 2))) || (l 7 && (((p 7 || p 8) || p 10) || p 3))) || (l 8 && (((p 8 || p 9) || p 11) || p 4))) || (l 9 && (((p 9 || p 10) || p 12) || p 5))) || (l 10 && (((p 10 || p 11) || p 0) || p 6))) || (l 11 && (((p 11 || p 12) || p 1) || p 7))) || (l 12 && (((p 12 || p 0) || p 2) || p 8))) := by
    rw [hi]
    simp only [witness, Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.getD_cons_zero, List.getD_cons_succ, gateAnd, gateOr]
  rw [hv, factor]
  rfl

private theorem foldl_or (xs : List Bool) (a : Bool) :
    xs.foldl (fun x y => x || y) a = (a || xs.any id) := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons, ih, List.any_cons, id, Bool.or_assoc]

private theorem all_lines (j : Fin 13) : j ∈ lines := by
  have h : ∀ j : Fin 13, j ∈ lines := by decide +kernel
  exact h j

theorem eval_true_iff (p l : Fin 13 → Bool) :
    witness.eval (List.ofFn (Fin.addCases p l)) = true ↔
      ∃ j : Fin 13, l j = true ∧ hasPoint p j = true := by
  rw [eval_eq, incidence, ← List.foldl_map, foldl_or]
  simp [List.any_eq_true, all_lines]

def background (k : Bool) : List Bool :=
  witness.wires (List.ofFn fun i : Fin 26 => decide (i.val = if k then 13 else 0))

private def traceStep (k : Bool) (j : Fin 65) : Prop :=
  let g := witness.gates.getD j.val ⟨.or, []⟩
  let a := g.inputs.getD 0 0
  let b := g.inputs.getD 1 0
  let w := background k
  (g.op = .and → trace k (26 + j.val) =
    ((w.getD a false && trace k b) || (trace k a && w.getD b false))) ∧
  (g.op = .or → trace k (26 + j.val) = (trace k a || trace k b))

private instance (k : Bool) (j : Fin 65) : Decidable (traceStep k j) := by
  unfold traceStep
  infer_instance

private theorem trace_start : ∀ (k : Bool) (j : Fin 26),
    trace k j.val = decide (j.val = if k then 0 else 13) := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem trace_rules : ∀ (k : Bool) (j : Fin 65), traceStep k j := by decide +kernel

private theorem trace_final : ∀ k : Bool, trace k witness.output = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem construct65 : Candidate 65 := by
  dsimp only [Candidate]
  refine ⟨witness, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · intro p l h
    apply (eval_true_iff _ _).2
    refine ⟨l, by simp, ?_⟩
    rcases h with h | h | h | h <;> subst p <;> simp [hasPoint]
  · intro p _
    let l : Fin 13 → Bool := fun j => !(p j || p (j+1) || p (j+3) || p (j+9))
    change witness.eval (List.ofFn (Fin.addCases p l)) = false
    cases he : witness.eval (List.ofFn (Fin.addCases p l)) with
    | false => rfl
    | true =>
      obtain ⟨j, hj, hp⟩ := (eval_true_iff p l).1 he
      have hp' : (p j || p (j+1) || p (j+3) || p (j+9)) = true := by
        simpa [hasPoint, Bool.or_assoc] using hp
      change (!(p j || p (j+1) || p (j+3) || p (j+9))) = true at hj
      rw [hp'] at hj
      cases hj
  · intro k
    refine ⟨trace k, fun j hj => trace_start k ⟨j, hj⟩, ?_, trace_final k⟩
    intro j g a b hget hpins
    have hj : j < witness.gates.length := List.getElem?_eq_some_iff.mp hget |>.choose
    have hlt : j < 65 := hj
    have h := trace_rules k ⟨j, hlt⟩
    simpa [traceStep, List.getD_eq_getElem?_getD, hget, hpins, background] using h

end PlaneDoubleRead

#print axioms PlaneDoubleRead.eval_true_iff
#print axioms PlaneDoubleRead.construct65
#print axioms PlaneDoubleRead.candidate64_is_desk
