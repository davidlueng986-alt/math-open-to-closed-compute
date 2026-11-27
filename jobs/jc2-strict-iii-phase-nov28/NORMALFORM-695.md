# Complete parametrization and cusp classification for the (6,9,5) boundary

Snapshot audited: main `1bbc45337cf57a98d8ff1bf6f11a3d80c251c541`.
This is an ordinary algebraic proof plus exact symbolic identities. It does not close a strict-135 terminal obligation and does not prove the Jacobian conjecture. The separate local-defect hypotheses used to translate cusp types to missing-page excess must be audited independently; in particular no strict inequality for normalization degree r>1 is used here.

## Theorem

Let p,q be complex polynomials of degrees 6,9 and suppose

    deg(q^2-p^3-lambda*p-kappa)=5.

After an affine change of the parameter, the compatible scaling p -> a^2 p, q -> a^3 q, and choosing the sign of q, the pair is

    R=(t+b)(t^2+b*t+2*c), S=t^2+b*t+c,
    p=R^2+S,
    q=R^3+(3/2)*R*S+(3/8)*t,

where b is nonzero. In these coordinates lambda=(1-6*c^2)/8. The derivative gcd divides t, so the normalization has at most one nonimmersive parameter, and it has multiplicity two. The nonimmersive parameter exists exactly when

    G=4*b^2*c+8*c^2+1=0,

and is t=0. Its analytic type is (2,3), except when

    F=160*c^4+40*c^2-1=0,

in which case its type is (2,5). No cusp of type (2,7), (2,9), or higher multiplicity occurs. Polynomial degrees 6,9,5 have gcd one, so the parametrization is birational onto its image.

Scalings must be retained when comparing two different boundary curves for the same Keller map: the normalization lambda=(1-6*c^2)/8 is not a common invariant until the separate target scaling factors have been matched.

## Exhaustiveness

Normalize the leading coefficients of p,q to one, and let R be the polynomial part of the Laurent square root of p at infinity. Then R is monic of degree three and p=R^2+S with deg S<=2. The bound deg(q^2-p^3)<=6 says q-p^(3/2)=O(t^-3). Expand

    p^(3/2)=R^3+(3/2)*R*S+(3/8)*S^2/R+O(t^-3).

Divide S^2 by R as S^2=R*U+V, deg V<3. The missing t^-1 and t^-2 coefficients force V to be constant. If deg S<2, U=0 and S is constant. Then q=R^3+(3/2)*R*S and q^2-p^3 is affine in p, making the asserted remainder constant, a contradiction. Thus S is quadratic and U is linear.

Write S=alpha*t^2+beta*t+gamma with alpha nonzero. Translate the zero of U to t=0. The identity S^2=R*U+V gives U=alpha^2*t, V=gamma^2, and

    R=(alpha*t+beta)*(alpha*t^2+beta*t+2*gamma)/alpha^2.

A fourth root of alpha, with the compatible parameter and target scalings, makes alpha=1. This is exactly the displayed form. Direct expansion gives the coefficient of t^6 in q^2-p^3 as (1-6*c^2)/8 and the coefficient of t^5 in q^2-p^3-lambda*p as -b/8. Hence b is nonzero. There are no omitted lower-degree S cases.

## All critical parameters, with a small Bezout identity

Put A=p' and K=(8/3)*q'-4*R*A. Direct differentiation gives

    K=4*S*R'+1,
    S^2=t*R+c^2,
    2*S*A-R*K=t*R'.

Consequently the polynomial identity

    t=(t+4*S*R)*K-8*S^2*A
     =(8/3)*(t+4*S*R)*q'
       -[4*R*(t+4*S*R)+8*S^2]*p'

holds for every b,c. This proves gcd(p',q') divides t, including multiplicities. At t=0,

    p'(0)=b*G,
    q'(0)=(3/8)*(8*b^2*c+1)*G.

Their simultaneous vanishing is equivalent to G=0. For instance

    (8/3)*q'(0)-8*b*c*p'(0)=G.

The gcd identity also shows that the first nonzero derivative of the parametrization has order exactly two at a critical parameter. In particular no appeal to an uncomputed resultant is needed.

## Cusp order

Write p=p0+a2*t^2+a3*t^3+... and q=q0+q2*t^2+q3*t^3+... under G=0. Define

    C3=a2*q3-a3*q2.

Exact polynomial division proves

    1024*c^5*C3 = F + G*J3,

where the explicit polynomial J3 is saved by normalform695_check.py. Since G=0 implies c!=0, a cusp is ordinary when F!=0. This determinant formulation does not require the fixed first coordinate to have a nonzero second derivative.

If F=0, then G+F=4*c*(b^2+40*c^3+12*c). Hence put H=b^2+40*c^3+12*c=0. Modulo H,F, the second coefficient is

    a2=(3/2)*(1-4*c^2).

It is nonzero, since F+(40*c^2+20)*(1-4*c^2)=19. Subtract the linear multiple (q2/a2)*(p-p0) from q-q0 and then the appropriate quadratic multiple of (p-p0)^2. The first possible odd term is now fifth order; its numerator is

    C5=a2^2*q5-a2*q2*a5-2*a2*a3*q4+2*a3*q2*a4.

Exact reduction modulo H,F gives

    C5=-(21/16)*(580*c^2+159).

This is nonzero because

    F-(8*c^2/29-28/4205)*(580*c^2+159)=247/4205.

After using the analytic coordinate z with p-p0=z^2, the first odd term is therefore exactly degree five. This proves type (2,5), not merely an upper bound.

## Consequences for the strict-135 profiles

These implications use only the smooth-source, normalization-degree-one, multiplicity-two local formula from LOCAL-DEFECT: for cusp (2,2*l+1), e=(l+1)*a and extra local degree d-e=l*a. They must not be generalized to quotient charts without a separate argument.

- Profile I: the e=6 boundary of degree (6,9,5) has extra 0,3,or4; the e=2 boundary of the same degrees has extra 0 or1. Exact budget four therefore leaves only (ordinary cusp, ordinary cusp) or ((2,5) cusp, immersed).
- Profile III: the e=5 boundary of degree (6,9,5) is immersed, since neither 2 nor3 divides5. Its entire cusp excess five must occur on the e=2 boundary of degree (12,18,10).
- Profile IV: the e=4 boundary of degree (6,9,5) is immersed or has exactly one ordinary cusp contributing two. The e=2 boundary of degree (18,27,15) must contribute six or four respectively.
- Profile II has no degree-(6,9,5) boundary, and this theorem by itself places no additional restriction on it.

For Profile III, write W=2*p*q'-3*q*p' on its (12,18,10) boundary. The exact Weierstrass equation gives deg W<=5 and gcd(p',q') divides W. The e=2 local rank-one formula identifies the total cusp excess with deg gcd(p',q'), so the exact budget forces degree five and W to be a nonzero constant times that gcd. The resulting remaining obligation is a fixed-degree polynomial identity problem, not a conjectural global degree cutoff.

The nonzero residue comes only from this e=2 branch. If R is the polynomial part of sqrt p and S=p-R^2, then the coefficient of t^11 in q modulo p is half the coefficient of t^5 in S. Therefore that coefficient of S is nonzero. It can be scaled to one, and a parameter translation removes the t^5 coefficient of the monic sextic R.

## Verification scope

`normalform695_check.py` checks every displayed polynomial identity symbolically over Q[b,c,t]; it uses no floating point and no finite parameter search. It saves explicit coefficient certificates in `normalform695_certificates.txt`. A Lean source file is being prepared for the algebraic identities and critical-parameter conclusions. The Laurent normalization and analytic cusp-coordinate argument above remain ordinary mathematical proofs unless explicitly incorporated into a later formal theorem.
