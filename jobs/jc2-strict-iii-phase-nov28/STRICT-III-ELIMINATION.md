# Exact residual polynomial problem for strict profile III

This compute target is conditional on the four-profile classification and its exact Euler budget. It is not a global Jacobian degree cutoff. The recent correction of LOCAL-DEFECT's r>1 inequality must be accounted for when reconfirming those prerequisites.

The (6,9,5), e=5 branch has no cusps by NORMALFORM-695.md and the smooth-source multiplicity-two classification. The entire cusp excess is therefore five on the (12,18,10), e=2 branch. This branch has no rotational quotient and has normalization degree one. Its local rank-one formula gives

    deg gcd(p',q')=5.

Let T=q²-p³-lambda*p-kappa have degree10. Put W=2p*q'-3q*p'. Differentiating the displayed identity gives

    q*W=p*T'-3p'*T-2lambda*p*p'-3kappa*p'.

First W cannot be zero: in characteristic zero W=0 makes q²/p³ constant; monicity then gives q²=p³, so T=-lambda*p-kappa has degree12 or at most0, contradicting its exact degree10. Thus deg W<=5, and equality holds because a common divisor of degree5 divides this nonzero W. In particular lambda is nonzero (if lambda=0, deg W<=3). After leading normalization the leading coefficient of W is -24lambda. The exact divisibility target is W|p'. It then also divides q', because W is proportional to the derivative gcd in the candidate under consideration. For a proof of impossibility it suffices to impose W|p', which is a weaker condition.

## Nonzero residue and source normalization

Let R be the polynomial part of sqrt(p), so R is monic sextic and p=R²+S, deg S<=5. Let U be the quotient of S² on division by R. The polynomial part of p^(3/2) is exactly

    q=R³+(3/2)RS+(3/8)U.

Higher binomial terms have negative degree. Since deg(q²-p³)<=12, this q is forced, not a free choice. The quotient of q by p is R and the remainder is (1/2)RS+(3/8)U, of degree<=11. Hence the residue trace sum q(alpha)/p'(alpha) over p(alpha)=a is half the coefficient S5 of t^5 in S. The fixed right-side terminal residue is nonzero; all other y-divisors have e>2h and give zero. Thus S5!=0.

Under t=rho*u and the compatible leading normalization p_new=rho^-12 p(rho*u), q_new=rho^-18 q(rho*u), this coefficient becomes rho^-7 S5. Choose a seventh root rho of S5. Then translate u to remove the t^5 coefficient of R. These operations preserve all degrees, nonvanishing, and divisibility. No S5=0 branch is discarded without a reason: it contradicts the required nonzero residue of this exact profile.

We can consequently write

    R=t^6+r4*t^4+r3*t^3+r2*t²+r1*t+r0,
    S=t^5+s4*t^4+s3*t^3+s2*t²+s1*t+s0.

## Exact equations in characteristic zero

The Sage script computes U, p, q, E=q²-p³, W over QQ in the ten displayed coefficient variables. Before imposing equations, deg W<=10. Impose its coefficients of degrees6 through10 to vanish. The identity qW=pE'-3p'E, with p,q monic and deg E<=17, then forces deg E<=12: a hypothetical leading term of E of degree13..17 has nonzero multiplier deg(E)-36 and cannot cancel. Impose E11=0. Because p11=0, this is exactly the remaining degree11 cancellation needed for deg(E-lambda*p)<=10, with lambda=E12.

Let z*lambda=1. A degree-six quotient of p' by W must have leading coefficient -z/2. Introduce its six remaining coefficients and impose every coefficient of p'-W_low*quotient=0, where W_low has degrees0..5. This is the complete necessary polynomial system.

The computation is over QQ, with no reduction modulo primes. If the ideal is the unit ideal, Singular must also produce a lift matrix M satisfying matrix(I)*M=1. The script multiplies the result and checks the remainder is the literal zero polynomial before reporting a verified certificate. The coefficient rows are saved for an independent replay and a potential Lean ring certificate. A timeout, large basis, nonunit result, or missing certificate is inconclusive.

The combined script enforces an overall internal budget of3600 seconds. Its lower-degree stage receives at most450 seconds; any nonunit or timeout continues to the stronger stage if time remains. A70-minute Actions timeout allows setup margin and stays below six hours. Every unit-ideal certificate is replayed in a fresh Singular process.

## Further exact triangular reduction (eight variables)

The deployed reduced script uses eight variables r4,r3,s4,s3,s2,s1,s0,z. The earlier seventeen-variable system is retained in strict135_III_eliminate_full.sage as an independent description of the same necessary target before eliminations.

Write S²=R*U+V. The vanishing of the degree17 and degree16 terms of E forces V5=V4=0. The degree15,14,13 terms then give respectively

    V3=1/6,
    V2=s4/2,
    V1=(s3+s4²)/2-r4/3.

Using these three identities in E11=0 gives

    r2=(3s1+6s4s2+3s3²+3s3s4²+3r4²
        -6r3s4-6r4s3-6r4s4²)/2.

No variable coefficient is divided out. With this r2, set Rbase=t6+r4t4+r3t3+r2t² and divide S²=Rbase*U+Vbase. The quotient U is unaffected by the two missing lower coefficients of R. Thus r1=Vbase5 and r0=Vbase4-r1*U3 exactly enforce V5=V4=0. These substitutions retain every candidate.

The original W6..W10, E11, and W5+24lambda equations are still imposed after substitution. With z*lambda=1, the monic polynomial

    D=t5-(z/24)*(W0+W1t+W2t²+W3t³+W4t4)

is exactly -zW/24. The five coefficients of the exact monic remainder of p' on division by D replace the quotient variables. This gives an eight-variable characteristic-zero ideal. A candidate of the original profile maps to a zero of every displayed equation, so a checked unit-ideal certificate for this reduced system excludes the entire residual profile. A nonunit ideal still can include extra solutions because q' divisibility was not imposed.

## Lower-degree necessary ideal

The companion strict135_III_eliminate_low.sage substitutes the necessary divisibility W|H for W|p', where

    H=U*U'-4*S*V', deg H=7, H7=2, H6=8s4.

There is an exact Bezout identity, with Q8=8q:

    3H=(U+4SR)*Q8'-3[4R(U+4SR)+8S²]*p'.

It follows by differentiating S²=RU+V. Therefore the derivative gcd divides H, and the saturated degree-five W must divide H as well. This weaker ideal needs only three monic-division steps and is much less prone to coefficient expansion. A checked unit ideal for it closes the same residual target. A nonunit result does not resolve the stronger target and must not be reported as a candidate Keller map.
