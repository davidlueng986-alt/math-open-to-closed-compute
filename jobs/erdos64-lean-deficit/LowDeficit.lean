import Mathlib

namespace Erdos64Deficit

/-- The choice of branch side for total deficit <= 6. The single
balanced all-degree-two-six-port pattern is the only arithmetic gap. -/
theorem choose_orientation
    (p q dx dy tx ty : ℕ)
    (hbalance : 3*p + dy = 3*q + dx)
    (hbudget : dx+dy ≤ 6)
    (hx : tx ≤ dx) (hy : ty ≤ dy)
    (hex : ¬ (p=q ∧ dx=3 ∧ dy=3 ∧ tx=3 ∧ ty=3)) :
    q+tx ≤ p+2 ∨ p+ty ≤ q+2 := by
  omega

theorem five_deficit_orientation
    (p q dx dy tx ty : ℕ)
    (hbalance : 3*p + dy = 3*q + dx)
    (hbudget : dx+dy ≤ 5)
    (hx : tx ≤ dx) (hy : ty ≤ dy) :
    q+tx ≤ p+2 ∨ p+ty ≤ q+2 := by
  omega

/-- Quotient dimension two: the three two-color shadows have a total
deficit of at most twice the original. At least one has deficit <=4. -/
theorem pair_budget (a b c dx dy t : ℕ)
    (hbudget : dx+dy ≤ 6) (ht : t ≤ dx)
    (hs : a+b+c ≤ 2*(dy+t)) :
    a ≤ 4 ∨ b ≤ 4 ∨ c ≤ 4 := by
  omega

/-- An elementary double-counting obstruction to a codimension-three
six-port label multiset having minimum character weight 3 but a
repeated label. c_i counts nonzero characters of weight i; d counts
equal pairs among the six nonzero labels. -/
theorem six_port_moments
    (c3 c4 c5 c6 d : ℕ)
    (hcnt : c3+c4+c5+c6 = 7)
    (h1 : 3*c3+4*c4+5*c5+6*c6 = 24)
    (h2 : 3*c3+6*c4+10*c5+15*c6 = 30+2*d) :
    d=0 ∧ c3=4 ∧ c4=3 ∧ c5=0 ∧ c6=0 := by
  omega

/-- A bipartite graph with a nontrivial edge and at least two edges,
maximum degree <= 2 and total deficit <=4 must have four vertices
of degree two. The graph part is the standard disjoint paths/cycles
classification; this is its arithmetic core. -/
theorem no_cubic_budget (n e : ℕ)
    (hn : 2 ≤ n) (he : 2 ≤ e) (hmax : e ≤ n)
    (hd : 3*n ≤ 2*e+4)
    (hsmall : n ≤ 3 → e ≤ n-1) :
    n=4 ∧ e=4 := by
  omega

#print axioms choose_orientation
#print axioms five_deficit_orientation
#print axioms pair_budget
#print axioms six_port_moments
#print axioms no_cubic_budget

end Erdos64Deficit
