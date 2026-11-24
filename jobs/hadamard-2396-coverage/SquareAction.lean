import Triples

namespace Hadamard2396.SquareAction

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def kind (v : Nat) : Nat :=
  if v%19=0 then 0 else if [1,4,5,6,7,9,11,16,17].contains (v%19) then 1 else 2

theorem kind_lt (v : Nat) : kind v < 3 := by unfold kind; split <;> simp_all <;> split <;> decide

def entry (c : Fin 8) (v : Nat) : Int := sign (c.val.testBit (kind v))
def code (cols : Array Nat) (x : Nat) : Fin 8 :=
  ⟨cols.getD x 0 % 8, Nat.mod_lt _ (by decide)⟩
def vert (a b : Fin 8) (s : Nat) : Int :=
  sumAt 19 (fun k => entry a k * entry b ((k+s)%19))

private def localValues : Array Int := #[19, 19, 19, 17, 17, 17, 1, 1, 1, -1, -1, -1, 1, 1, 1, -1,
  -1, -1, -17, -17, -17, -19, -19, -19, 17, 17, 17, 19, 15, 15, -1, 3,
  -1, 1, 1, -3, -1, -1, 3, 1, -3, 1, -19, -15, -15, -17, -17, -17,
  1, 1, 1, -1, -1, 3, 19, -1, -1, 17, -3, 1, -17, 3, -1, -19,
  1, 1, 1, 1, -3, -1, -1, -1, -1, -1, -1, 1, -3, 1, 17, 1,
  -3, 19, -1, -1, -19, 1, 1, -17, -1, 3, -1, 3, -1, 1, 1, 1,
  1, 1, 1, -1, 3, -1, -17, -1, 3, -19, 1, 1, 19, -1, -1, 17,
  1, -3, 1, -3, 1, -1, -1, -1, -1, -1, -1, 1, 1, -3, -19, 1,
  1, -17, 3, -1, 17, -3, 1, 19, -1, -1, -1, -1, 3, 1, 1, 1,
  -17, -17, -17, -19, -15, -15, 1, -3, 1, -1, -1, 3, 1, 1, -3, -1,
  3, -1, 19, 15, 15, 17, 17, 17, -19, -19, -19, -17, -17, -17, -1, -1,
  -1, 1, 1, 1, -1, -1, -1, 1, 1, 1, 17, 17, 17, 19, 19, 19]

def coefficient (a b : Fin 8) (k : Nat) : Int := localValues.getD ((8*a.val+b.val)*3+k) 0

/-- At a nonzero square or nonsquare shift, 1 or 2 gives the same local correlation. -/
theorem vertical_classes : ∀ a b : Fin 8, ∀ s : Fin 19, vert a b s.val = coefficient a b (kind s.val) := by
  decide +kernel

def crt (x k : Nat) : Nat := x+63*((16*(k+19-x%19))%19)

private theorem crt_spec : ∀ x : Fin 63, ∀ k : Fin 19,
    crt x.val k.val < 1197 ∧ crt x.val k.val % 63 = x.val ∧ crt x.val k.val % 19 = k.val := by
  decide +kernel

private def columnIndex (b k : Nat) := 16*(k+19-b)%19
private theorem columnPerm : ∀ b : Fin 19,
    ((List.range 19).map (columnIndex b.val)).Perm (List.range 19) := by decide +kernel

private theorem perm_sum {l r : List Int} (h : l.Perm r) : l.sum=r.sum := by
  induction h with
  | nil => rfl
  | cons a h ih => simp [List.sum_cons, ih]
  | swap a b rest => simp only [List.sum_cons]; omega
  | trans a b ha hb => exact ha.trans hb

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
    induction w with
    | zero => rfl
    | succ w ih => rw [sumAt_succ, ← ih]; rfl
  | succ h ih =>
    rw [sumAt_succ, ih, ←sumAt_add]
    apply sumAt_congr
    intro i _
    rw [sumAt_succ]

private theorem sum_crt (f : Nat → Int) :
    sumAt 1197 f = sumAt 63 (fun x => sumAt 19 (fun k => f (crt x k))) := by
  change sumAt (19*63) f = _
  rw [grid,swap]
  apply sumAt_congr
  intro x _
  have h := perm_sum ((columnPerm ⟨x%19,Nat.mod_lt _ (by decide)⟩).map (fun j => f (x+63*j)))
  simpa only [sumAt, List.map_map, Function.comp_def, crt, columnIndex, Nat.mul_comm, Nat.add_comm]
    using h.symm

def word (m : Nat) (i : Nat) := m.testBit i

def Represents (m : Nat) (cols : Array Nat) : Prop :=
  ∀ i : Fin 1197, sign (word m i.val) = entry (code cols (i.val%63)) (i.val%19)

abbrev Block (test : Nat → Bool) (start size : Nat) :=
  ∀ i : Fin size, test (start+i.val) = true

theorem join {test : Nat → Bool} {start left right : Nat}
    (a : Block test start left) (b : Block test (start+left) right) : Block test start (left+right) := by
  intro i
  by_cases h : i.val < left
  · exact a ⟨i.val,h⟩
  · have w := b ⟨i.val-left, by have := i.isLt; omega⟩
    change test (start+left+(i.val-left)) = true at w
    rwa [show start+left+(i.val-left) = start+i.val by omega] at w

def representsAt (m : Nat) (cols : Array Nat) (i : Nat) : Bool :=
  decide (sign (word m i) = entry (code cols (i%63)) (i%19))

theorem check_representation {m : Nat} {cols : Array Nat}
    (h : Block (representsAt m cols) 0 1197) : Represents m cols := by
  intro i
  exact of_decide_eq_true (by simpa [representsAt] using h i)

def model (cols : Array Nat) (t v : Nat) : Int :=
  sumAt 63 (fun x => coefficient (code cols x) (code cols ((x+t)%63)) v)

/-- The ordinary one-dimensional periodic autocorrelation equals the 63-column model. -/
theorem reduce_paf (m : Nat) (cols : Array Nat) (h : Represents m cols) (s : Nat) :
    paf 1197 (word m) s = model cols (s%63) (kind (s%19)) := by
  unfold paf model
  rw [sum_crt]
  apply sumAt_congr
  intro x hx
  calc
    _ = vert (code cols x) (code cols ((x+s%63)%63)) (s%19) := by
      apply sumAt_congr
      intro k hk
      obtain ⟨hi,hx',hk'⟩ := crt_spec ⟨x,hx⟩ ⟨k,hk⟩
      have h63 : (crt x k+s)%1197%63 = (x+s%63)%63 := by
        rw [Nat.mod_mod_of_dvd _ (show 63 ∣ 1197 by decide), Nat.add_mod, hx']
      have h19 : (crt x k+s)%1197%19 = (k+s%19)%19 := by
        rw [Nat.mod_mod_of_dvd _ (show 19 ∣ 1197 by decide), Nat.add_mod, hk']
      have left := h ⟨crt x k,hi⟩
      have right := h ⟨(crt x k+s)%1197,Nat.mod_lt _ (by decide)⟩
      dsimp only at left right hx' hk'
      rw [left,right,hx',hk',h63,h19]
    _ = _ := vertical_classes _ _ ⟨s%19,Nat.mod_lt _ (by decide)⟩

def tableValue (table : Array Int) (s : Nat) : Int := table.getD ((s%63)*3+kind (s%19)) 0

def ModelTable (a b : Array Nat) (table : Array Int) : Prop :=
  ∀ x : Fin 63, ∀ k : Fin 3, model a x.val k.val + model b x.val k.val = table.getD (x.val*3+k.val) 0

def tableAt (a b : Array Nat) (table : Array Int) (i : Nat) : Bool :=
  decide (model a (i/3) (i%3) + model b (i/3) (i%3) = table.getD i 0)

theorem check_table {a b : Array Nat} {table : Array Int}
    (h : Block (tableAt a b table) 0 189) : ModelTable a b table := by
  intro x k
  have hx := x.isLt
  have hk := k.isLt
  have computed := h ⟨x.val*3+k.val,by omega⟩
  simp only [Nat.zero_add, tableAt, decide_eq_true_eq] at computed
  simpa only [show (x.val*3+k.val)/3 = x.val by omega,
              show (x.val*3+k.val)%3 = k.val by omega] using computed

theorem pair_table {ma mb : Nat} {a b : Array Nat} {table : Array Int}
    (ha : Represents ma a) (hb : Represents mb b) (ht : ModelTable a b table) :
    (fun s => paf 1197 (word ma) s + paf 1197 (word mb) s) = tableValue table := by
  funext s
  rw [reduce_paf ma a ha,reduce_paf mb b hb]
  exact ht ⟨s%63,Nat.mod_lt _ (by decide)⟩ ⟨kind (s%19),kind_lt _⟩

def exactPairs (f : Nat → Int) := ((List.range 598).filter (fun i => f (i+1) == -2)).length
def energy (f : Nat → Int) := sumAt 598 (fun i => (f (i+1)+2)^2)

#print axioms reduce_paf
#print axioms pair_table
end Hadamard2396.SquareAction
