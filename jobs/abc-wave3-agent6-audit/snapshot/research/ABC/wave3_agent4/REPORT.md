# Wave 3 Agent 4 — actual Fermat square-area formalization

Task: `FERMAT-FORMAL`. This is supporting formal work for the quartic ROOT escape in Agent 1's report. It formalizes a classical theorem; it is not a new proof of abc.

## Current evidence status

**LEAN_VERIFIED.** All four public declarations compiled successfully in the pinned environment, produced the `.olean`, and passed the standard-axiom audit. Both the orchestrator and the author independently checked the downloaded source provenance against the exact local files. There is no remaining verification blocker for the statements below.

| Evidence | Value |
|---|---|
| Lean | 4.36.0 |
| Mathlib | `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` |
| Successful Actions run | `46041248187` |
| Verification job | `140649315040` |
| Compute source commit | `e2a47a835201e7be2c50fa14e86317da52cc6df4` |
| Lean source SHA-256 | `e97ea98a8feb82460a48bb63f6b1db94528f3ed30cf761b5945d83ff54d5bdef` |
| Kernel log SHA-256 | `6c51e52638a5a727bb9dceec6859f7702129a524ef1dbd6022abbc741c08a0f5` |
| Public declarations audited | 4 |
| Axioms of every declaration | `propext`, `Classical.choice`, `Quot.sound` |

The [result receipt](../wave3/verification/46041248187/abc-wave3-agent4/result.json), [kernel log](../wave3/verification/46041248187/abc-wave3-agent4/kernel.log), and [source provenance](../wave3/verification/46041248187/abc-wave3-agent4/provenance.json) are retained with the research record. The compiled artifact is retained in the same evidence directory.

### Preserved first-attempt failure

The first submitted source had SHA-256 `d349b129b4a797f46a3da4243cf7a8020ddda0556c3d2aad14dc5abf349d7c69`. Its run `46040627898`, job `140647230441`, source commit `cc05ee1fa5ea1d2c6ca2a2551da03873f2066f0f`, was rejected because `Int.pow_emod` is unavailable at this pin and the strong-induction branch is named `ind`, not `h`. No certificate from that failed compilation is accepted. The successful source uses `pow_two` plus `Int.mul_emod` and the correct branch name; no mathematical assumption was added. The [failed kernel log](../wave3/verification/46040627898/abc-wave3-agent4/kernel.log) is preserved.

## Exact statements

`PrimitiveSquareArea x y z` means that x, y, z are positive integers, x²+y²=z², gcd(x,y)=1, and there is an integer s with xy=2s².

The four verified public declarations are:

1. `primitive_square_area_descent_odd`: every such triangle with an odd first leg produces another such triangle with strictly smaller positive hypotenuse.
2. `primitive_square_area_descent`: the same construction with either leg orientation.
3. `no_primitive_square_area`: there are no such primitive positive integer triangles.
4. `fourth_difference_not_square`: for integers 0<b<c, gcd(c,b)=1, odd c and even b, c⁴−b⁴ is not the square of any integer w.

The last theorem is the precise scope needed for the quartic ROOT map. No claim is made here that a general theorem without the coprimality or parity hypotheses has been formalized.

For a primitive positive triple a+b=c, the required b<c follows from a>0 and gcd(c,b)=gcd(a+b,b)=gcd(a,b)=1. Thus after the stated odd-c/even-b orientation, these restrictions introduce no additional open assumption into the ROOT escape.

## Mathematical content of the source

The descent begins with the existing primitive Pythagorean classification. With the odd leg first, x=m²−n², y=2mn and z=m²+n², where m>n>0, gcd(m,n)=1 and m,n have opposite parity. The square-area hypothesis yields

\[
mn(m+n)(m-n)=s^2.
\]

The source proves the required pairwise coprimality. In particular, the potentially delicate coprimality of m+n and m−n has an explicit Bezout proof: combine a Bezout identity for m,n with the identity certifying that the odd integer m+n is coprime to 2. It does not assume that subtraction preserves coprimality without the parity condition.

Four applications of Mathlib's coprime-product square extraction theorem, with positivity excluding the negative-square case, give positive r,t,u,v satisfying

\[
m=r^2,\quad n=t^2,\quad m+n=u^2,\quad m-n=v^2.
\]

Both u and v are odd, and u>v. Therefore p=(u+v)/2 and q=(u−v)/2 are positive integers. The source derives

\[
p^2+q^2=r^2,\qquad 2pq=t^2.
\]

It proves that t is even, so pq=2(t/2)². Coprimality of u,v descends to coprimality of p,q by another explicit Bezout identity. Thus p,q,r form a new primitive square-area triangle, and r<z. Strong induction on the natural absolute value of the hypotenuse then rules out the initial triangle.

For the quartic consequence, a hypothetical equality c⁴−b⁴=w² produces the triangle

\[
(c^4-b^4,\ 2c^2b^2,\ c^4+b^4)
\]

with area (bcw)². Its primitive status is obtained from the Pythagorean classification with parameters c²,b² and the supplied coprimality and parity hypotheses. This contradicts `no_primitive_square_area`.

## Relation to abc closure

The formal target removes a classical supporting theorem from the informal part of the proposed quartic ROOT escape. It does not establish the uniform ROOT inequality, any positive power saving, or the abc conjecture. The remaining open inequality must retain its open status in the Closure DAG.

The source does **not** use Mathlib's `not_fermat_42` theorem as a substitute: that theorem concerns a⁴+b⁴=c² and has a different sign.

## Reproduction and audit

Research source: `FermatSquareArea.lean` in this directory.

Compute bundle: `math-open-to-closed-compute/jobs/abc-wave3-agent4-lean/`, containing an identical source, `run.sh`, `audit.py` and `README.md`. The runner compiles an `.olean`, captures the actual Lean version and Mathlib commit, and asks Lean for the axiom lists of all four public declarations. The audit rejects incomplete compilation, forbidden proof escape constructs and any axiom outside `propext`, `Classical.choice` and `Quot.sound`.

The successful receipt certifies this exact source and scope. It does not certify the uniform ROOT bound, the complete analytic transport to abc, or the original abc conjecture. No new global core estimate has been proved by this formalization.
