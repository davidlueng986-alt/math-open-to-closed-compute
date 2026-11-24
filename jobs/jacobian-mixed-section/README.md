# Mixed target graph sections of Gallagher's family: new all-degree exclusion

Let d>=5 and p(w)=(2w-(d+1)w^d)/(d-1), q(w)=(w^2-dw^(d+1))/(d-1),
f(w)=q(w)-w p(w)=(w^(d+1)-w^2)/(d-1).
For the 3D Keller family in the previous 2026-11-20 note, pulled back by
arbitrary polynomial (X,Y,Z) on C^2, write U=1+XY, G=1-(d+1)/d*XY+X^2 Z,
W=GU, C=XG, BC=p(W)+G, AC^2=q(W)+GW.

Theorem (restricted family, NOT planar JC): for ANY L in C[c] and constant
kappa in C, no such pullback has nonzero constant Jacobian [B,C] and
A=L(C)B+N(C), where h(c)=c L(c), N(c)=f(h(c))/c^2+kappa.
N is polynomial, since f has no terms of degree below 2. The degrees of L
and the source pullback are unrestricted. This extends the earlier
constant-coefficient linear graph exclusions to a correlated mixed family.

Proof. Algebra gives BC(W-h(C))=C^2 N(C)-f(W).
Set T=U-X L(C); W-h(C)=G T. Let S_d(w,h)=sum_{i=0}^d w^(d-i)h^i.
The divided difference is f(w)-f(h)=(w-h)(S_d-w-h)/(d-1).
Consequently (W-h)(BC+(S_d-W-h)/(d-1))=kappa*C^2.

If kappa != 0, both factors on the left are divisible by G; after cancellation
T*M=kappa*X^2 for polynomial M, while T=1+X(Y-L(C)).
Hence T divides 1 by Bezout. If X is constant, C nonconstant requires X!=0;
Y, W, G and B then depend rationally on C, contradicting the algebraic
independence of B,C. If X is nonconstant, T is a constant and X divides
T-1, hence T=1 and Y=L(C). Modulo X^2, G=1-(d+1)XY/d and W=1-XY/d.
Since p(1)=-1 and p'(1)=-(d+2), BC=p(W)+G is XY/d mod X^2.
Using C=XG gives B=Y/d mod X. Thus B-L(0)/d and C both are divisible
by nonconstant X, so the Jacobian [B,C] is divisible by X, impossible.

If kappa=0 and W=h, then T=0, X is a nonzero constant and Y=L(C)-1/X;
B,C again algebraically dependent. Otherwise cancel W-h to obtain
(d-1)BC=W+h-S_d(W,h). Taking bracket with C gives
(d-1)C[B,C]=D[W,C], D=1-partial_w S_d(W,h).
Thus D divides C. Since G,U are 1 mod X, W(W-1) is divisible by XG=C;
h is divisible by C, so D=1-dW mod C. Multiply by
E=1+d/(1-d) W. Then DE=1 mod C, so D divides 1. But C,W are
algebraically independent, since B is rational in C,W and B,C are
independent. D contains nonzero w^(d-1) coefficient -d and is nonconstant
as a polynomial in those independent coordinates. Contradiction.

The Lean file verifies the three ring identities/divisibility steps; the
polynomial composition, chain rule, algebraic independence and general
geometric context remain ordinary mathematical arguments. The full JC2
problem and arbitrary N outside the offset family remain open. No novelty
or external acceptance claim is made.

General linear-in-b graph A=L(C)B+N(C) forces
T | ((d-1)N(C)+L(C)^2-C^(d-1)L(C)^(d+1)).
The offset family above is the constant-right-hand-side case. A nonconstant
right-hand-side is the next real obstruction, not a closure.
