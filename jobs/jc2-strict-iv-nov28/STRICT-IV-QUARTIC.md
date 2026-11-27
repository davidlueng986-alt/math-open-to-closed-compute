# Complete strict-IV residual target with an arbitrary quartic divisor

This is a prepared exact coefficient obstruction, not a proved exclusion. The script has not been deployed by this agent.

## Why every strict-IV candidate is covered

The small boundary has degrees (6,9,5) and generic boundary degree e=4. NORMALFORM-695.md proves that it has at most one nonimmersive parameter and that its cusp can only have type (2,3) or (2,5). The smooth-source multiplicity-two formula excludes (2,5) when e=4; an ordinary cusp contributes exactly two extra local pages. Thus this small curve contributes either zero or two.

The exact global cusp budget for profile IV is six. Its large e=2 boundary must therefore contribute six or four. Since its source chart is smooth, has no rotational quotient, and maps once onto the target normalization, the rank-one e=2 local formula identifies that excess with deg gcd(p',q'). Consequently its derivative gcd has degree six or four. Over C either gcd has a monic quartic divisor, including all repeated-root patterns. We introduce an arbitrary monic quartic D and require D|p',D|q'. This covers the entire residual profile, not just simple cusps.

The large curve has degrees (18,27,15) for p,q,T, where

    T=q²-p³-lambda*p-kappa.

Its e=2,h=1 divisor is the only y-divisor with e=2h. The small e=4,h=1 divisor has e>2h and contributes zero to the terminal residue. The nonzero terminal residue therefore forces the large curve's trace sum q(alpha)/p'(alpha) to be nonzero. Put R=polynomial part of sqrt(p), S=p-R². Once p,q are monic, deg R=9, deg S<=8, and that trace is half the leading coefficient S8. Hence S8!=0.

Under t=rho*u with compatible target scalings p_new=rho^-18 p(rho*u), q_new=rho^-27 q(rho*u), this coefficient becomes rho^-10 S8. Choose a tenth root of S8 and then translate the parameter to remove R8. These are invertible normalizations. Thus

    R=t9+r7t7+...+r0,
    S=t8+s7t7+...+s0.

No normalization divides by lambda, which is allowed to be zero.

## Exact compact algebra

Divide S²=R*U+V. The polynomial part of p^(3/2) is forced to be

    q=R³+(3/2)RS+(3/8)U.

All later binomial terms have negative degree; any polynomial difference from this expression would make q²-p³ have degree greater than18. Define p=R²+S. Then

    E=q²-p³=(S³-6VR²)/8-(9/8)VS+(9/64)U²,
    8W=24VR'-6RV'+6SU'-9US',   W=2pq'-3qp',
    H=UU'-4SV'.

These identities avoid expanding Q². Their polynomial identities are included in NormalForm695.lean. The derivative ideal identity is

    3H=(U+4SR)*(8q)'-3[4R(U+4SR)+8S²]*p'.

A common derivative divisor therefore divides both W and H.

The script enforces W9 through W16 equal zero. Since qW=pE'-3p'E, p and q are monic of degrees18 and27, and deg E<=26, these equations force deg E<=18. A hypothetical leading E term of degree19..26 has nonzero multiplier deg E-54 and cannot cancel. Let lambda=E18, and impose T17=T16=0, where T=E-lambda*p. The exact degree15 is enforced by z*T15=1. The original constant kappa only changes T0 and does not affect any equation.

The degree26 and25 equations force V8=V7=0. These two necessary equations are retained explicitly, so H can be truncated to degrees0..13. Similarly W can be truncated to degrees0..8. W8=-36lambda is retained as a redundant checked coefficient equation.

W=0 is not an omitted case: in characteristic zero it makes q²/p³ constant, hence equal to1 by monicity. Then T=-lambda*p-kappa has degree18 or is constant, contradicting its exact degree15. Nevertheless no inverse of W8 or lambda occurs anywhere in this model.

## Same-fibre cubic phase orbit

COMMON-FIBRES-135 section5 gives three normalization inverse branches at the same p=X18 whose leading parameter ratios are the cube roots of unity. Any distinct pair of their q values first differs at X^-19. The canonical Laurent expansion is

    q(t(X))=X27+(lambda/2)X^-9
             +(T(t(X))+kappa)/(2X27)+O(X^-45).

The first two terms and the kappa term are fixed by X -> zeta*X, zeta³=1. Therefore the canonical coefficients of T(t(X)) at degrees14,13,11,10 must vanish. No nonvanishing coefficient is imposed beyond T15!=0; omitting the known nonzero degree8 canonical coefficient only weakens the system.

With p17=0, the exact Lagrange identity

    [X^j]T(t(X))=(1/j)[t^-1]T'(t)p(t)^(-j/18)

gives the following four equations, after clearing denominators:

    T14=0,
    6T13-5T15*p16=0,
    216T11-156T13*p16-168T14*p15-180T15*p14+145T15*p16²=0,
    162T10-108T12*p16-117T13*p15-126T14*p14+98T14*p16²
       -135T15*p13+210T15*p16*p15=0.

They are independently checked symbolically over QQ by phase_IV_coefficients_check.py.

## Safe coefficient system and certificate acceptance

The script keeps all sixteen boundary coefficients, four independent coefficients of the monic quartic D, and z: twenty-one variables. Keeping the linear elimination variables prevents the dense substitutions that caused the previous inverse-W computation to exhaust memory.

The first stage imposes D|W,D|H. The second adds D|p'. The third adds D|q' using

    q'=(3/2)R*p'+(3/2)S*R'+(3/8)U'.

Every stage uses only necessary equations. A unit-ideal certificate at any stage excludes every candidate. A nonunit ideal at an early stage need not satisfy the later divisibility conditions. The total internal time budget is20 minutes. Expanded remainder terms are capped at350000; reaching that cap is explicitly inconclusive and is not a mathematical bound.

Before the research stages, the script tests the whole certificate pipeline on the known unit ideal (r7,1-r7). That self-test is labelled explicitly and never counts as evidence about profile IV.

An accepted research result requires all of the following: no Singular interpreter-error line (a line beginning with '?'); an exported lift matrix with exactly one column and one row per original generator; an independent exact QQ polynomial reconstruction in Sage proving the sum of generator times lift coefficient equals1; and a fresh Singular replay with the same dimension and error checks. Each coefficient is exported separately and parsed into the original Sage polynomial ring. The replay matrix is then generated from those parsed coefficients, rather than trusting an unparsed matrix string. Stale certificate files are removed before a stage, and a wrong file count, failed parse, or nonzero residual stops acceptance.

The independent check uses polynomial arithmetic, not another ideal-membership test. Even an accepted algebraic certificate still requires the requested Lean replay and the independently audited geometric prerequisites before terminal closure is claimed. No finite-field computation is used.

## Optional triangular reduction to seventeen variables

There is an exact smaller formulation, deliberately not substituted into the safe script. V8=V7=0 solve r1,r0 with constant coefficient -1. The high E equations determine V6..V1 recursively, starting with V6=1/6. They depend only on r7..r4 and s7..s3.

After those substitutions, the coefficient of r2 in T17 is exactly -1/4, so T17=0 determines r2. This expression is independent of s0. The quotient U is also independent of s0. The V8 equation gives r1=2s0+an expression independent of s0. In T16 the direct S³ term contributes (3/8)s0 and the V6 R² term contributes -(1/2)s0. Thus the coefficient of s0 is exactly -1/8, so T16=0 determines s0. The lambda*p16 subtraction is independent of s0 after the common V0 term cancels.

This leaves twelve boundary parameters r7..r3,s7..s1, plus the four quartic coefficients and z. Every elimination divides only by a nonzero rational constant, so there are no missed exceptional branches. It can be used later if a compact quotient-ring implementation avoids dense coefficient expansion.
