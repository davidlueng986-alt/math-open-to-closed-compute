# Marked triangle expansions: direct counterexample attack

Scope: fixed simple cubic bases F, arbitrary vertex marking T. Replace each
marked vertex by a triangle, one port per incident edge; the resulting graph
is cubic. Every cycle other than a replacement triangle projects to a simple
base cycle, since a simple cycle crosses a 3-port triangle either zero or two
times, not four. A base cycle of length r containing t marked vertices lifts
to every length r+t+j, 0<=j<=t, by independent short/long triangle traversals.
Thus a marking is a counterexample iff every base cycle avoids every
power p>=4 in [r+t,r+2t]. For a given r,p the exact forbidden cardinality
interval is max(0,ceil((p-r)/2)) <= t <= min(r,p-r). Search over ALL markings
of each sampled base (unless timeout), rather than a fixed marking.

Immediate obstruction: every base triangle has 0 or 2 marks, and every
base 4-cycle has exactly 1. Two triangles abc,abd sharing ab force equal
marks c,d. Their 4-cycle cadb forces c=d=0 and a+b=1, contradictory. Any
base containing a diamond is therefore excluded for ALL markings.

The Lean file checks the arithmetic implications and diamond obstruction
only. The search is lazy SAT with exact cycle separation, and a separate
explicit expanded-graph DFS for a proposed witness. Solver UNSAT for one
base is not a proof for all cubic graphs. A timeout is not UNSAT.
