# A complete common target for strict profiles II and III

The algebraic target is stronger than the earlier strict-III target: exclude every phase-compatible (12,18,10) polynomial parametrization whose derivative gcd has degree at least three. No such exclusion is claimed until an exact certificate is obtained.

## Why both whole profiles enter this target

For profile III, NORMALFORM-695.md excludes every cusp on the small e=5 boundary, since its only possible types (2,3),(2,5) require e divisible by2 or3. Thus the large e=2 curve supplies the full excess five. Its smooth-source rank-one formula gives derivative gcd of degree five, so it has a cubic divisor.

For profile II, there is one y-boundary curve, with e=4,h=2,f=1 and no rotational stabilizer. Its total cusp excess is eight. At a cusp of multiplicity m, rank one gives exactly

    d-4=3(m-1).

In rank zero, the quadratic Weierstrass-root computation of COMMON-FIBRES-135 section6 gives

    d=3m-2gamma+2,

where gamma is the separation order of the two roots. Each root has order at least one after the t-preserving shear, hence gamma>=1, including ramified Puiseux roots. Consequently

    d-4 <= 3m-4 < 3(m-1).

This also covers m=2: the only rank-zero type is the ordinary cusp, with excess two. Smooth image branches have zero excess. Summing over every normalization parameter gives

    8 <= 3 sum(m-1) = 3 deg gcd(p',q'),

so the integer gcd degree is at least three. This implication has been independently audited by the sibling agent against the complete local proof; it does not invoke the corrected-away strict r>1 polar inequality.

## Same coefficients and all normalization branches

Both profiles have the same-P opposite-phase contact of COMMON-FIBRES-135 section5. Therefore they satisfy the three exact canonical T coefficients C9=C7=C5=0 in STRICT-III-PHASE.md.

The nonzero residue also covers profile II. Its only y-divisor has e=2h=4, h=2, so the residue trace from this curve, multiplied by nonzero -2J, must cancel the fixed nonzero terminal contribution. For III the e=5,h=2 divisor has e>2h and gives zero; its e=2,h=1 divisor must supply the nonzero trace. In both cases, writing p=R²+S with R the monic polynomial square root at infinity, the trace is half the coefficient S5. Hence S5 is nonzero and the normalization S5=1 is exhaustive. Target affine Weierstrass changes add only a constant on a fixed p-fibre, and the extra trace of that constant is zero because sum 1/p'(alpha)=0.

The same unconditional triangular eliminations r1,r0,r2 leave seven free boundary coefficients. Unlike the saturated degree-five script, **lambda is allowed to be zero**. The exact degree of T is ten, so a new Rabinowitsch variable z satisfies z*T10=1. This is the only saturation in the shared script.

If a complex gcd has degree at least three, it has a monic cubic divisor, including when some roots repeat. Introduce

    D=t³+d2*t²+d1*t+d0.

The full script imposes D|p' and D|q' by their exact monic remainders. Thus every candidate from either entire profile maps to a zero of the system. This does not select only simple cusps or only one multiplicity partition.

## Two exact stages

The generic identity from NormalForm695.lean, with S²=RU+V, gives

    3H=(U+4SR)*(8q)'-3[4R(U+4SR)+8S²]*p',
    H=UU'-4SV'.

Therefore D divides H and W=2pq'-3qp'. The preliminary stage imposes these two lower-degree remainders. The original W6 through W10 equations are retained, so W can be truncated to degrees0 through5 for division. If the preliminary ideal is nonunit or times out, the script adds the p' and q' remainders automatically.

`strict135_II_III_cubic_eliminate.sage` has eleven variables: seven boundary coefficients, three cubic-divisor coefficients, and the inverse of T10. It uses characteristic-zero QQ arithmetic, saves the complete equations, and accepts a unit-ideal result only after producing a lift certificate, checking its product, and replaying that certificate in a fresh Singular process. The total internal budget is20 minutes. A30-minute Actions timeout leaves setup margin.

A replayed unit ideal establishes the fixed-degree shared algebraic obstruction. Its use to close both terminal profiles still requires the ordinary geometric prerequisites, cusp classification, and the requested Lean replay. A timeout, nonunit ideal, or unverified certificate establishes none of these conclusions.
