import Triples

namespace Hadamard2396
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def signWord (v i : Nat) : Bool := v.testBit i
def compress (v q j : Nat) : Int :=
  sumAt (1197/q) fun k => sign (signWord v (j+q*k))

def projectedPaf (u v : Array Int) (q s : Nat) : Int :=
  sumAt q fun i => u.getD i 0 * u.getD ((i+s)%q) 0 + v.getD i 0 * v.getD ((i+s)%q) 0

private abbrev Checked (test : Nat → Bool) (start size : Nat) :=
  ∀ i : Fin size, test (start+i.val) = true

private theorem joinChecks {t : Nat → Bool} {start left right : Nat}
    (a : Checked t start left) (b : Checked t (start+left) right) :
    Checked t start (left+right) := by
  intro i
  by_cases h : i.val < left
  · exact a ⟨i.val,h⟩
  · have w := b ⟨i.val-left, by have := i.isLt; omega⟩
    change t (start+left+(i.val-left)) = true at w
    rwa [show start+left+(i.val-left) = start+i.val by omega] at w

def wordA : Nat := 0x1225705f58f3ec9923b0f6aed5f31d425e748c283b943422d1c5917a4e90ae7c855a40c3b814d9a86f31d2b26dff56a60c31333d3758152c862f42545e84ffd95b5f5da52b55488913cb1d80e7bdfc0d90a3de384efe3e47a8f5fc1960a4a4b2050616095d7e6b23ced58dd8fe5842f9fcf123fc46e40ca6151f8887e1ffc66349d0714693e52d253daf4f32912d1d90657b8c7f022c
def wordB : Nat := 0x4142bd8ebaa4c6ee6b7654dfbf8c9b7dcbdf9bb4dc2b35f851054f4ee5695ea78390e685b50bdd0027a420a0c848ddaaf34ae75f9a9a0de85761d1c6ccf9c2481e7880d7e651d6d3921f99d62b5f0b7905980d1ca509b7e61c5fc16ae498efb5ce69f644e715f666ac281708e3a581ebfa268d262c1dda89014c64db01b73e86c915a53b37af3b6f2824629bc00c011315fc21d133b

def a57 : Array Int := #[-11, 5, 1, 5, 5, -1, -1, 5, 1, -1, -5, -1, 5, -5, 1, 5, 5, -1, 5, -21, -1, 5, -5, -1, -1, 5, -1, 5, 5, 1, -1, -5, 1, 5, -5, -1, -1, -5, -3, -1, -5, 1, -1, 5, -1, -1, -5, -1, 5, 5, 1, 5, -5, 1, -1, 5, 1]
def b57 : Array Int := #[1, 7, 3, -3, 7, -1, 1, 7, 3, 1, -5, -1, -3, -5, 3, -3, 7, -1, -3, -15, -1, -3, -5, -1, 1, 7, -1, -3, 7, 3, 1, -5, 3, -3, -5, -1, 1, -5, -3, 1, -5, 3, 1, 7, -1, 1, -5, -1, -3, 7, 3, -3, -5, 3, 1, 7, 3]

private def margins57Test (i : Nat) : Bool := decide (compress wordA 57 i = a57.getD i 0 ∧ compress wordB 57 i = b57.getD i 0)
private theorem margins57_0 : Checked margins57Test 0 5 := by decide +kernel
private theorem margins57_5 : Checked margins57Test 5 5 := by decide +kernel
private theorem margins57_10 : Checked margins57Test 10 5 := by decide +kernel
private theorem margins57_15 : Checked margins57Test 15 5 := by decide +kernel
private theorem margins57_20 : Checked margins57Test 20 5 := by decide +kernel
private theorem margins57_25 : Checked margins57Test 25 5 := by decide +kernel
private theorem margins57_30 : Checked margins57Test 30 5 := by decide +kernel
private theorem margins57_35 : Checked margins57Test 35 5 := by decide +kernel
private theorem margins57_40 : Checked margins57Test 40 5 := by decide +kernel
private theorem margins57_45 : Checked margins57Test 45 5 := by decide +kernel
private theorem margins57_50 : Checked margins57Test 50 5 := by decide +kernel
private theorem margins57_55 : Checked margins57Test 55 2 := by decide +kernel
theorem margins57 (i : Fin 57) : compress wordA 57 i.val = a57.getD i.val 0 ∧ compress wordB 57 i.val = b57.getD i.val 0 := by
  have h : Checked margins57Test 0 57 := (joinChecks (joinChecks (joinChecks (joinChecks margins57_0 margins57_5) (joinChecks margins57_10 margins57_15)) (joinChecks (joinChecks margins57_20 margins57_25) (joinChecks margins57_30 margins57_35))) (joinChecks (joinChecks margins57_40 margins57_45) (joinChecks margins57_50 margins57_55)))
  have hi := h i
  rw [Nat.zero_add] at hi
  exact of_decide_eq_true hi

private def exact57Test (i : Nat) : Bool := decide (projectedPaf a57 b57 57 i = (if i = 0 then 2354 else -42))
private theorem exact57_0 : Checked exact57Test 0 5 := by decide +kernel
private theorem exact57_5 : Checked exact57Test 5 5 := by decide +kernel
private theorem exact57_10 : Checked exact57Test 10 5 := by decide +kernel
private theorem exact57_15 : Checked exact57Test 15 5 := by decide +kernel
private theorem exact57_20 : Checked exact57Test 20 5 := by decide +kernel
private theorem exact57_25 : Checked exact57Test 25 5 := by decide +kernel
private theorem exact57_30 : Checked exact57Test 30 5 := by decide +kernel
private theorem exact57_35 : Checked exact57Test 35 5 := by decide +kernel
private theorem exact57_40 : Checked exact57Test 40 5 := by decide +kernel
private theorem exact57_45 : Checked exact57Test 45 5 := by decide +kernel
private theorem exact57_50 : Checked exact57Test 50 5 := by decide +kernel
private theorem exact57_55 : Checked exact57Test 55 2 := by decide +kernel
theorem exact57 (i : Fin 57) : projectedPaf a57 b57 57 i.val = (if i.val = 0 then 2354 else -42) := by
  have h : Checked exact57Test 0 57 := (joinChecks (joinChecks (joinChecks (joinChecks exact57_0 exact57_5) (joinChecks exact57_10 exact57_15)) (joinChecks (joinChecks exact57_20 exact57_25) (joinChecks exact57_30 exact57_35))) (joinChecks (joinChecks exact57_40 exact57_45) (joinChecks exact57_50 exact57_55)))
  have hi := h i
  rw [Nat.zero_add] at hi
  exact of_decide_eq_true hi

def a63 : Array Int := #[19, -3, 1, -1, -3, -1, -1, 5, 1, -13, -1, 1, -1, -1, -1, 9, -3, -1, -13, -1, -1, 1, -3, 1, -1, -3, -1, -1, 5, 1, 7, -1, 1, -1, -1, -1, -13, -3, -1, 7, -1, -1, 5, -3, 1, -1, -3, -1, -1, 5, 1, 9, -1, 1, -1, -1, -1, 7, -3, -1, 9, -1, -1]
def b63 : Array Int := #[-17, -3, 1, -3, -3, -1, -5, 1, 1, 3, 3, 1, -3, 3, 5, 1, -3, -1, 3, 3, -1, 5, -3, 1, -5, -3, -1, -1, 1, 1, -1, 3, 1, -5, 3, 5, 3, -3, -1, -1, 3, -1, 13, -3, 1, -1, -3, -1, -3, 1, 1, 1, 3, 1, -1, 3, 5, -1, -3, -1, 1, 3, -1]

private def margins63Test (i : Nat) : Bool := decide (compress wordA 63 i = a63.getD i 0 ∧ compress wordB 63 i = b63.getD i 0)
private theorem margins63_0 : Checked margins63Test 0 5 := by decide +kernel
private theorem margins63_5 : Checked margins63Test 5 5 := by decide +kernel
private theorem margins63_10 : Checked margins63Test 10 5 := by decide +kernel
private theorem margins63_15 : Checked margins63Test 15 5 := by decide +kernel
private theorem margins63_20 : Checked margins63Test 20 5 := by decide +kernel
private theorem margins63_25 : Checked margins63Test 25 5 := by decide +kernel
private theorem margins63_30 : Checked margins63Test 30 5 := by decide +kernel
private theorem margins63_35 : Checked margins63Test 35 5 := by decide +kernel
private theorem margins63_40 : Checked margins63Test 40 5 := by decide +kernel
private theorem margins63_45 : Checked margins63Test 45 5 := by decide +kernel
private theorem margins63_50 : Checked margins63Test 50 5 := by decide +kernel
private theorem margins63_55 : Checked margins63Test 55 5 := by decide +kernel
private theorem margins63_60 : Checked margins63Test 60 3 := by decide +kernel
theorem margins63 (i : Fin 63) : compress wordA 63 i.val = a63.getD i.val 0 ∧ compress wordB 63 i.val = b63.getD i.val 0 := by
  have h : Checked margins63Test 0 63 := (joinChecks (joinChecks (joinChecks (joinChecks margins63_0 margins63_5) (joinChecks margins63_10 margins63_15)) (joinChecks (joinChecks margins63_20 margins63_25) (joinChecks margins63_30 margins63_35))) (joinChecks (joinChecks (joinChecks margins63_40 margins63_45) (joinChecks margins63_50 margins63_55)) margins63_60))
  have hi := h i
  rw [Nat.zero_add] at hi
  exact of_decide_eq_true hi

private def exact63Test (i : Nat) : Bool := decide (projectedPaf a63 b63 63 i = (if i = 0 then 2358 else -38))
private theorem exact63_0 : Checked exact63Test 0 5 := by decide +kernel
private theorem exact63_5 : Checked exact63Test 5 5 := by decide +kernel
private theorem exact63_10 : Checked exact63Test 10 5 := by decide +kernel
private theorem exact63_15 : Checked exact63Test 15 5 := by decide +kernel
private theorem exact63_20 : Checked exact63Test 20 5 := by decide +kernel
private theorem exact63_25 : Checked exact63Test 25 5 := by decide +kernel
private theorem exact63_30 : Checked exact63Test 30 5 := by decide +kernel
private theorem exact63_35 : Checked exact63Test 35 5 := by decide +kernel
private theorem exact63_40 : Checked exact63Test 40 5 := by decide +kernel
private theorem exact63_45 : Checked exact63Test 45 5 := by decide +kernel
private theorem exact63_50 : Checked exact63Test 50 5 := by decide +kernel
private theorem exact63_55 : Checked exact63Test 55 5 := by decide +kernel
private theorem exact63_60 : Checked exact63Test 60 3 := by decide +kernel
theorem exact63 (i : Fin 63) : projectedPaf a63 b63 63 i.val = (if i.val = 0 then 2358 else -38) := by
  have h : Checked exact63Test 0 63 := (joinChecks (joinChecks (joinChecks (joinChecks exact63_0 exact63_5) (joinChecks exact63_10 exact63_15)) (joinChecks (joinChecks exact63_20 exact63_25) (joinChecks exact63_30 exact63_35))) (joinChecks (joinChecks (joinChecks exact63_40 exact63_45) (joinChecks exact63_50 exact63_55)) exact63_60))
  have hi := h i
  rw [Nat.zero_add] at hi
  exact of_decide_eq_true hi

def a133 : Array Int := #[1, -3, -1, -1, 1, 1, 3, -1, 3, 1, -1, 1, -1, -3, 5, 3, 1, 1, -1, -9, 3, 5, 3, 1, 1, 1, 1, -3, -1, 3, 1, -1, -1, -1, -3, -1, -3, -1, -9, 1, -1, -3, -1, -3, 1, 1, -1, 1, -3, -1, 3, -1, -1, -1, 1, 3, 5, -3, 1, -1, -1, 1, 3, -1, -3, -1, 1, -1, 1, -3, 5, 3, -1, 1, 1, -1, -9, -1, 3, -1, 1, 1, 1, 3, 5, -3, -1, 1, -1, -1, -3, 5, -3, 1, -1, -3, 1, -3, 5, -3, 1, 1, 1, -1, 3, 5, -3, -1, -1, -1, -1, 3, -1, 3, -3, 1, -1, -1, 3, -1, -3, 1, -1, 1, -1, 3, 5, 3, -1, -1, 1, 1, -3]
def b133 : Array Int := #[1, 1, 1, -3, -1, 7, 1, -3, -1, -1, -3, -1, -7, -1, 5, -1, -1, 3, 1, -3, 1, 5, -1, -1, 3, -1, 7, -1, -3, -1, -1, -3, 1, -7, -1, -3, 1, 1, -3, -1, -7, -1, -3, 1, -1, 3, 1, 7, -1, -3, -1, 1, -3, 1, 7, 1, 5, -3, -1, -3, 1, 7, 1, -3, 1, 1, 3, 1, 7, -1, 5, -1, 1, 3, -1, -7, -3, -3, -1, 1, 3, -1, 7, 1, 5, 1, 1, 3, 1, -7, -1, 5, 1, -1, -3, -3, 7, -1, 5, 1, -1, 3, -1, -7, 1, 5, 1, 1, -3, 1, -7, 1, -3, -1, -3, 3, 1, -7, 1, -3, 1, -1, -3, -1, -7, 1, 5, -1, 1, -3, -1, 7, -1]

private def margins133Test (i : Nat) : Bool := decide (compress wordA 133 i = a133.getD i 0 ∧ compress wordB 133 i = b133.getD i 0)
private theorem margins133_0 : Checked margins133Test 0 5 := by decide +kernel
private theorem margins133_5 : Checked margins133Test 5 5 := by decide +kernel
private theorem margins133_10 : Checked margins133Test 10 5 := by decide +kernel
private theorem margins133_15 : Checked margins133Test 15 5 := by decide +kernel
private theorem margins133_20 : Checked margins133Test 20 5 := by decide +kernel
private theorem margins133_25 : Checked margins133Test 25 5 := by decide +kernel
private theorem margins133_30 : Checked margins133Test 30 5 := by decide +kernel
private theorem margins133_35 : Checked margins133Test 35 5 := by decide +kernel
private theorem margins133_40 : Checked margins133Test 40 5 := by decide +kernel
private theorem margins133_45 : Checked margins133Test 45 5 := by decide +kernel
private theorem margins133_50 : Checked margins133Test 50 5 := by decide +kernel
private theorem margins133_55 : Checked margins133Test 55 5 := by decide +kernel
private theorem margins133_60 : Checked margins133Test 60 5 := by decide +kernel
private theorem margins133_65 : Checked margins133Test 65 5 := by decide +kernel
private theorem margins133_70 : Checked margins133Test 70 5 := by decide +kernel
private theorem margins133_75 : Checked margins133Test 75 5 := by decide +kernel
private theorem margins133_80 : Checked margins133Test 80 5 := by decide +kernel
private theorem margins133_85 : Checked margins133Test 85 5 := by decide +kernel
private theorem margins133_90 : Checked margins133Test 90 5 := by decide +kernel
private theorem margins133_95 : Checked margins133Test 95 5 := by decide +kernel
private theorem margins133_100 : Checked margins133Test 100 5 := by decide +kernel
private theorem margins133_105 : Checked margins133Test 105 5 := by decide +kernel
private theorem margins133_110 : Checked margins133Test 110 5 := by decide +kernel
private theorem margins133_115 : Checked margins133Test 115 5 := by decide +kernel
private theorem margins133_120 : Checked margins133Test 120 5 := by decide +kernel
private theorem margins133_125 : Checked margins133Test 125 5 := by decide +kernel
private theorem margins133_130 : Checked margins133Test 130 3 := by decide +kernel
theorem margins133 (i : Fin 133) : compress wordA 133 i.val = a133.getD i.val 0 ∧ compress wordB 133 i.val = b133.getD i.val 0 := by
  have h : Checked margins133Test 0 133 := (joinChecks (joinChecks (joinChecks (joinChecks (joinChecks margins133_0 margins133_5) (joinChecks margins133_10 margins133_15)) (joinChecks (joinChecks margins133_20 margins133_25) (joinChecks margins133_30 margins133_35))) (joinChecks (joinChecks (joinChecks margins133_40 margins133_45) (joinChecks margins133_50 margins133_55)) (joinChecks (joinChecks margins133_60 margins133_65) (joinChecks margins133_70 margins133_75)))) (joinChecks (joinChecks (joinChecks (joinChecks margins133_80 margins133_85) (joinChecks margins133_90 margins133_95)) (joinChecks (joinChecks margins133_100 margins133_105) (joinChecks margins133_110 margins133_115))) (joinChecks (joinChecks margins133_120 margins133_125) margins133_130)))
  have hi := h i
  rw [Nat.zero_add] at hi
  exact of_decide_eq_true hi

private def exact133Test (i : Nat) : Bool := decide (projectedPaf a133 b133 133 i = (if i = 0 then 2378 else -18))
private theorem exact133_0 : Checked exact133Test 0 5 := by decide +kernel
private theorem exact133_5 : Checked exact133Test 5 5 := by decide +kernel
private theorem exact133_10 : Checked exact133Test 10 5 := by decide +kernel
private theorem exact133_15 : Checked exact133Test 15 5 := by decide +kernel
private theorem exact133_20 : Checked exact133Test 20 5 := by decide +kernel
private theorem exact133_25 : Checked exact133Test 25 5 := by decide +kernel
private theorem exact133_30 : Checked exact133Test 30 5 := by decide +kernel
private theorem exact133_35 : Checked exact133Test 35 5 := by decide +kernel
private theorem exact133_40 : Checked exact133Test 40 5 := by decide +kernel
private theorem exact133_45 : Checked exact133Test 45 5 := by decide +kernel
private theorem exact133_50 : Checked exact133Test 50 5 := by decide +kernel
private theorem exact133_55 : Checked exact133Test 55 5 := by decide +kernel
private theorem exact133_60 : Checked exact133Test 60 5 := by decide +kernel
private theorem exact133_65 : Checked exact133Test 65 5 := by decide +kernel
private theorem exact133_70 : Checked exact133Test 70 5 := by decide +kernel
private theorem exact133_75 : Checked exact133Test 75 5 := by decide +kernel
private theorem exact133_80 : Checked exact133Test 80 5 := by decide +kernel
private theorem exact133_85 : Checked exact133Test 85 5 := by decide +kernel
private theorem exact133_90 : Checked exact133Test 90 5 := by decide +kernel
private theorem exact133_95 : Checked exact133Test 95 5 := by decide +kernel
private theorem exact133_100 : Checked exact133Test 100 5 := by decide +kernel
private theorem exact133_105 : Checked exact133Test 105 5 := by decide +kernel
private theorem exact133_110 : Checked exact133Test 110 5 := by decide +kernel
private theorem exact133_115 : Checked exact133Test 115 5 := by decide +kernel
private theorem exact133_120 : Checked exact133Test 120 5 := by decide +kernel
private theorem exact133_125 : Checked exact133Test 125 5 := by decide +kernel
private theorem exact133_130 : Checked exact133Test 130 3 := by decide +kernel
theorem exact133 (i : Fin 133) : projectedPaf a133 b133 133 i.val = (if i.val = 0 then 2378 else -18) := by
  have h : Checked exact133Test 0 133 := (joinChecks (joinChecks (joinChecks (joinChecks (joinChecks exact133_0 exact133_5) (joinChecks exact133_10 exact133_15)) (joinChecks (joinChecks exact133_20 exact133_25) (joinChecks exact133_30 exact133_35))) (joinChecks (joinChecks (joinChecks exact133_40 exact133_45) (joinChecks exact133_50 exact133_55)) (joinChecks (joinChecks exact133_60 exact133_65) (joinChecks exact133_70 exact133_75)))) (joinChecks (joinChecks (joinChecks (joinChecks exact133_80 exact133_85) (joinChecks exact133_90 exact133_95)) (joinChecks (joinChecks exact133_100 exact133_105) (joinChecks exact133_110 exact133_115))) (joinChecks (joinChecks exact133_120 exact133_125) exact133_130)))
  have hi := h i
  rw [Nat.zero_add] at hi
  exact of_decide_eq_true hi

#print axioms margins57
#print axioms exact57
#print axioms margins63
#print axioms exact63
#print axioms margins133
#print axioms exact133
end Hadamard2396
