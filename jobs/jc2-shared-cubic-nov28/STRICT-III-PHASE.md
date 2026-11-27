# Exact same-fibre phase equations for the strict-III target

This strengthens STRICT-III-ELIMINATION.md using the new ordinary geometric result in `defect-closure/COMMON-FIBRES-135.md` section5. It is a separate script/job and does not alter the original run. The geometric premise must be independently audited before a resulting algebraic contradiction is used for terminal closure.

## Premise and exact consequence

For the large (12,18,10) target-normalization curve of strict III, the two normalization parameters in one physical window have leading ratio -1. At the same P=w^-12, their Q values first differ at order w15, with a nonzero coefficient. Choose the canonical Laurent parameter X=p(t)^(1/12), leading term t, so these two inverse branches are t(X) and t(-X). Normalize p monic, p11=0, q monic. Then

    q(t(X))-q(t(-X))=nonzero*X^-15+lower Laurent powers.

Set T=q²-p³-lambda*p-kappa. Its degree is10. Since

    q(t(X))=X18+(lambda/2)*X^-6
              +(1/2)*(T(t(X))+kappa)*X^-18+O(X^-30),

the odd terms at X^-9, X^-11, X^-13 vanish. Equivalently the coefficients of T(t(X)) at X9,X7,X5 vanish. The nonzero leading difference is equivalent to the canonical X3 coefficient being nonzero. The strengthened script retains only the three vanishing conditions; omitting the additional nonvanishing is a weakening and is safe for an impossibility proof.

## Exact coefficient extraction

For any nonzero integer j, formal Laurent change of variable and integration by parts give

    [X^j] T(t(X)) = (1/j) [t^-1] T'(t) p(t)^(-j/12).

Write p=t12+p10*t10+p9*t9+p8*t8+p7*t7+..., and T=sum T_i t^i. Expanding the finite binomial coefficients needed for j=9,7,5 gives

    C9=T9,
    C7=T7-(3/4)T9*p10-(5/6)T10*p9,
    C5=T5-(7/12)T7*p10-(2/3)T8*p9-(3/4)T9*p8
          +(17/32)T9*p10²-(5/6)T10*p7+(85/72)T10*p10*p9.

The script imposes C9=12C7=288C5=0. All original eight-variable equations are retained. The independent `phase_coefficients_check.py` verifies these expressions symbolically over QQ, and saves the exact output. Reducing the last equation by the first two gives

    T5-(2/3)T8*p9-(5/6)T10*p7+(25/36)T10*p10*p9=0.

## Nonzero W and computation scope

First, W=0 is impossible for the original candidate: it makes the derivative of q²/p³ zero, hence q²/p³ is constant in characteristic zero; monicity makes q²=p³. Then T=-lambda*p-kappa has degree12 if lambda is nonzero, and is constant otherwise, contradicting degree(T)=10. The candidate derivative gcd has degree five, and the nonzero W=2p*q'-3q*p' has degree at most five. Therefore W is a nonzero constant times that gcd. Alternatively the script explicitly enforces z*lambda=1 and W5=-24lambda, which excludes W=0 over characteristic zero. There is no missing zero-W branch in the coefficient system.

`strict135_III_phase_eliminate.sage` uses the same exact QQ ideal, lift certificate, polynomial multiplication check, and independent fresh Singular replay as the original script. It tries W|H for at most120 seconds and then adds W|p' if time remains. Its total internal budget is1200 seconds; a30-minute Actions job leaves setup margin and is below the user's six-hour bound. No timeout, nonunit ideal, or incomplete certificate is a theorem. Even a replayed QQ certificate still requires the intended Lean replay and the separately audited geometric prerequisites.

The same phase equations apply to the (12,18,10) curve in strict II, but that profile has a different cusp budget and does not give degree-five derivative gcd automatically. The present script therefore proves only a potential strict-III residual contradiction.
