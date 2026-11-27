# Complete finite SAT DAG validation

This job validates the reference formulations for the selected famous finite
problems. Full mathematical specifications and existing research queues live in
https://github.com/davidlueng986-alt/math-open-to-closed/tree/main/research/finite-sat-portfolio .

It executes known small Ramsey, MOLS, plane and Moore controls, independently
checks original witnesses, produces and independently replays UNSAT proofs, and
tests all sixteen leaves of a complete R(3,3)=6 partition. It also exhausts small
Latin families and checks an independently constructed Hoffman-Singleton graph.
The seven original-target decision roots remain OPEN; no production target is
solved by this workflow. The source manifest records exact module hashes.

One job, ten-minute hard cap, pinned existing SAT container, no schedule.
Results preserve DIMACS, solver logs, witnesses, proofs, checker logs and hashes.
The reference Moore57 and R(3,10) DIMACS expansions are deliberately not emitted.
