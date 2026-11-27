# ABC Wave 3 — Agent 3: explicit root escape and the height-route obstruction

**Date:** 2026-11-28 (Asia/Taipei). **Self-claimed package:** `HEIGHT-CORE`.
**Original abc:** `BLOCKED`. **LOW/CUSP:** both still `BLOCKED`.
**Classification:** external exploratory work, independently reviewable; no literature novelty claim.

## 1. What changed

The direct height attack did not prove LOW or CUSP. It identified the limitation of a proposed conductor-preserving isogeny bypass (§7). While discussing the root orchestrator's cubic Belyi-map idea, we found a different, complete reduction: two explicit maps of degrees 3 and 4 send every odd-c triple either directly or indirectly to a root of the squaring map. The sole apparent obstruction is resolved by a rank-zero elliptic-curve calculation proved below.

Consequently **ROOT alone implies full abc**, using the already proved odd-c parity bridge. GROWTH remains unproved as a standalone unconditional statement, but it is no longer an independently necessary premise for this proof route. This is a dependence reduction, not a new global abc estimate.

The orchestrator and Agent 1 subsequently found the simpler single map `(c^4-b^4,b^4,c^4)`, using Fermat's right-triangle theorem. That is the preferred main route. This report preserves an independently derived two-map route and a complete rational-point calculation, rather than replacing the simpler main proof or claiming another global inequality.

All written results labelled `PROVED` below use explicitly stated classical elliptic-curve inputs; they are not labelled `LEAN_VERIFIED`.

## 2. Two homogeneous maps and exact arithmetic control

Let `(a,b,c)` be a primitive positive triple with `a+b=c`, c odd, a the odd summand and b even. Put R=rad(abc). Recall from Wave 2 that such a triple belongs to the image of

$$T(u,v,w)=((u-v)^2,4uv,w^2)$$

if and only if both its odd summand and its third coordinate are squares. A **root** is a triple outside this image.

### W3-A3-MAPS — `PROVED`

Define the cubic map

$$M_3(a,b,c)=(a^2(3c-2a),\ b^2(c+2a),\ c^3),$$

and the raw quartic map

$$\widetilde M_4(a,b,c)=(a^2Q,\ b^3(c+3a),\ c^4),\qquad Q=6c^2-8ac+3a^2.$$

Divide all three quartic coordinates by their common gcd g and call the result M4. The following statements hold:

1. Both maps produce primitive positive odd-c triples, retaining the first summand as the odd summand.
2. The cubic needs no normalization. The quartic normalization has `g|81`, hence `g<=81`.
3. If their heights and radicals are c3,R3 and c4,R4, then

$$c_3=c^3,\qquad R_3\le4Rc^2;$$
$$c_4=c^4/g\ge c^4/81,\qquad R_4\le24Rc^3.$$

**Proof.** Direct expansion gives both sum identities. The quartic identity is

$$a^2(6c^2-8ac+3a^2)+(c-a)^3(c+3a)=c^4.$$

All coordinates are positive: `3c-2a=c+2b>0`, and `Q=a^2+4ab+6b^2>0`. They have the asserted parity.

For the cubic, a prime dividing both its first and third coordinates would divide `gcd(a,c)` or `gcd(3c-2a,c)`, the latter dividing 2. Since c is odd, this is impossible.

For the quartic, `g=gcd(Q,c^4)` because `gcd(a,c)=1`. For every prime p|c with p!=3, Q is congruent to 3a^2 modulo p, so p does not divide g. If v3(c)>=2, then v3(Q)=1. If v3(c)=1, then v3(g)<=v3(c^4)=4. Thus g divides 81, and is odd.

The cubic radical is at most `R(3c-2a)(c+2a)`. The product is `4c^2-(c-2a)^2<=4c^2`. The quartic radical, even before normalization, is at most `RQ(c+3a)`. Since `0<a<c`, Q<=6c^2 and c+3a<=4c. Normalization cannot introduce prime factors. This proves all bounds. ∎

## 3. A complete rank-zero calculation

The classical inputs used in this section are:

- Mordell–Weil finite generation for E(Q).
- The standard rational 2-isogeny descent for `y^2=x(x^2+Ax+B)` and its partner with coefficients `-2A,A^2-4B`. The square-class map is `alpha(O)=1`, `alpha((0,0))=B`, and `alpha((x,y))=x`. Its image is represented by squarefree signed divisors d of B, with the quartic equation

  $$n^2=d u^4+A u^2v^2+(B/d)v^4,\quad \gcd(u,v)=1.$$

  If alpha and alpha' are the two descent maps, then `2^rank=|im alpha| |im alpha'|/4`. This is unconditional; no BSD or parity conjecture is used. See Silverman–Tate, *Rational Points on Elliptic Curves*, Chapter III, and the explicit unconditional formula in [D1, §2].
- At a prime of good reduction p, the subgroup of rational torsion of order prime to p injects into E(Fp); see Silverman, *The Arithmetic of Elliptic Curves*, VII.3, Proposition 3.1.

### W3-A3-RANK-ZERO — `PROVED`

For

$$E:\quad Y^2=X^3-2X^2+9X,$$

one has exactly

$$\boxed{E(\mathbb Q)=\{O,(0,0),(3,6),(3,-6)\}.}$$

**Proof.** The discriminant is `16*9^2*((-2)^2-4*9)=-41472=-2^9*3^4`, so E is nonsingular and has good reduction at 5 and 7. Its 2-isogenous curve is

$$E':\quad Y^2=X^3+4X^2-32X=X(X+8)(X-4).$$

For E, `X^2-2X+9=(X-1)^2+8>0`, so every nonzero rational point has X>0. The square-class support rule gives `im alpha subset {1,3}`. The point `(3,6)` realizes class 3, while O realizes 1, hence the image has size 2.

For E', the support rule gives `im alpha' subset {1,-1,2,-2}`. The point `(0,0)` has class `-32=-2 mod squares`, so 1 and -2 occur. Class2 would require

$$n^2=2u^4+4u^2v^2-16v^4,\quad \gcd(u,v)=1.$$

Modulo 3, each nonzero square is1. For `(u^2,v^2)` equal to `(1,0)`, `(0,1)` or `(1,1)`, the right side is2. These exhaust all possibilities because u,v cannot both be divisible by 3. Since 2 is not a square modulo 3, class 2 is impossible. Class-1 is also impossible: multiplying it by the known class -2 in the image subgroup would give class 2. Alternatively its quartic `n^2=-u^4+4u^2v^2+32v^4` has the same obstruction modulo 3. Hence `im alpha'={1,-2}`, also of size 2.

The rank formula gives `2^rank=2*2/4=1`, so rank = 0. The tangent formula gives `2(3,6)=(0,0)`, showing an order 4 subgroup.

Direct counting gives `#E(F5)=4` and `#E(F7)=12`. To avoid an unstated assertion about p-primary torsion, use prime-to-p injection at both primes: every prime-primary rational torsion component for a prime other than 5 injects modulo 5 and hence has order dividing 4; the 5-primary component injects modulo 7 and is trivial because 5 does not divide 12. Thus the entire torsion has order at most 4. Rank zero and the four displayed points prove the claim. ∎

This proves the full rational point set on one fixed elliptic curve, not merely a finite-height search.

## 4. Resolving the genus-two obstruction exactly

Set

$$P(x)=(3-2x^2)(3x^4-8x^2+6)=-6x^6+25x^4-36x^2+18.$$

### W3-A3-SEXTIC — `PROVED`

The affine curve `y^2=P(x)` has exactly four rational points:

$$\boxed{(x,y)=(1,1),(1,-1),(-1,1),(-1,-1).}$$

**Proof.** Given a rational point, put

$$X=9-6x^2,\qquad Y=6y.$$

Direct expansion gives `Y^2=X^3-2X^2+9X`. The preceding theorem permits only X=0 or 3 for affine rational points. If X=0, then x^2=3/2, impossible over Q by the odd3-adic valuation. If X=3, then x^2=1 and P(x)=1. This gives exactly the four points. ∎

For the independent geometric fallback, P is squarefree. An exact certificate is

$$(504x^4-572x^2+4)P(x)+(-84x^5+212x^3-145x)P'(x)=72.$$

Its discriminant is 35831808. Therefore its smooth projective model has genus 2: the double cover of P1 has six simple branch points, so Riemann–Hurwitz gives `2g-2=-4+6=2`. Faltings would give finiteness without determining the points, but **Faltings is not needed in the primary proof**, because the rank-zero calculation determined them. At infinity the leading coefficient is-6, so there are no additional rational points there.

## 5. Universal two-map root escape

### W3-A3-ESCAPE — `PROVED`

Every primitive positive odd-c triple is a root itself, or at least one of M3 and M4 is a root.

**Proof.** Suppose the original triple is not a root. Then a and c are squares. Put `t=a/c=x^2`, with x rational and `0<x<1`.

The ratios of the odd summands to the third coordinates of the normalized maps are unaffected by their common gcd and equal

$$F_3(t)=t^2(3-2t),\qquad F_4(t)=t^2(6-8t+3t^2).$$

If both outputs were in the squaring-map image, both ratios would be rational squares. Since t!=0, it would follow that both `3-2t` and `6-8t+3t^2` are rational squares. Their product would give a rational point

$$y^2=(3-2x^2)(3x^4-8x^2+6)$$

with 0<x<1, contradicting the exact point determination above. Thus at least one output is a root. No finite exceptional set remains. ∎

## 6. Quantified consequence for the closure DAG

### W3-A3-ROOT-SUFFICES — `PROVED` implication, root estimate still `BLOCKED`

Assume that for every delta>0 there is `B_delta>=1`, independent of the root, such that every odd-c root satisfies

$$c\le B_\delta R^{1+\delta}.\tag{ROOT-ABC}$$

This is equivalent by an elementary epsilon conversion to the existing `W2-A2-ROOT-BOUND` formulation. Explicitly, a logarithmic ROOT parameter d gives ROOT-ABC exponent `1/(1-d)` and constant `exp(A_d/(1-d))`. Conversely ROOT-ABC at exponent parameter `delta=d/(1-d)` gives the logarithmic ROOT inequality with `A_d=(1-d)log B_delta`. For large requested exponents, one may simply use any smaller admissible parameter.

Then full abc follows. To see the odd-c step, fix epsilon>0, set

$$\delta=\frac{\epsilon}{4+3\epsilon}<\frac13,\qquad M_\delta=81B_\delta24^{1+\delta}.$$

For a nonroot choose a successful map of degree d=3 or 4. The proved height/radical bounds give

$$c^d\le81B_\delta(24Rc^{d-1})^{1+\delta},$$

hence

$$c^{1-(d-1)\delta}\le M_\delta R^{1+\delta}.$$

Since c>=1 and d<=4, this also bounds `c^(1-3delta)`, yielding

$$c\le M_\delta^{1/(1-3\delta)}R^{(1+\delta)/(1-3\delta)}
=M_\delta^{1/(1-3\delta)}R^{1+\epsilon}.$$

The same constant covers original roots since M_delta>=B_delta>=1 and delta<=epsilon. Thus the bound is uniform over all odd-c triples. The established `W2-A2-PARITY` bridge implies full abc. Conversely abc immediately supplies ROOT-ABC by restriction. ∎

For a direct full-target parameter choice, first apply the odd-c result at `eta=epsilon/(2+epsilon)` and use `delta=epsilon/(8+7epsilon)`. The parity bridge then gives a valid full constant

$$K_\epsilon=1+\left(81B_\delta24^{1+\delta}\right)^{(8+7\epsilon)/8}.$$

The additive 1 makes the original strict inequality harmless. The displayed constants are deliberately loose but effective in terms of B_delta; no ineffective exceptional set is used.

Since Wave 2 also proved `abc => GROWTH`, the established arrows now give `ROOT => GROWTH`. This does **not** prove ROOT or GROWTH unconditionally. It removes one independent assumption from this route. The simpler Fermat map in Agent1's report improves the constants and is preferred for the canonical route.

## 7. HEIGHT-CORE attempts and what blocked them

### 7.1 Ordinary Szpiro is not the missing modified bound

I investigated applying ordinary Szpiro to the rational 2-isogenous Frey curves. The classical implication reaches abc with exponent 6/5+epsilon, as explicitly distinguished in Stein's primary lecture notes [H1]. It does not supply the coefficient 1+epsilon required here. No invocation of ordinary Szpiro is treated as a proved global input. Agent1 handles the product-bound version of this issue.

### 7.2 A fixed-depth 2-isogeny bypass cannot uniformly remove the cusp

The explicit modular polynomial for a cyclic 2-isogeny [H2] is

$$\Phi_2(X,Y)=X^3+Y^3-X^2Y^2+1488(X^2Y+XY^2)-162000(X^2+Y^2)$$
$$\hspace{15mm}+40773375XY+8748000000(X+Y)-157464000000000.$$

For any complex X,Y with Phi2(X,Y)=0, putting M=max(1,|Y|) gives the elementary bound

$$\max(1,|X|)\le10^{15}M^2.\tag{*}$$

Indeed this is immediate if |X|<=M. Otherwise |X|>=M>=1, and every term on the right after solving for X^3 is bounded by its absolute coefficient times |X|^2 M^2; the sum of these coefficients is less than 10^15. Divide by |X|^2. Symmetry yields the same estimate with X,Y exchanged.

Along at most m 2-isogenies, induction gives

$$\log\max(1,|j_m|)\ge2^{-m}\log\max(1,|j_0|)-(1-2^{-m})\log(10^{15}).$$

Write $J_m=\max(|j_m|,|j_m-1728|)$, as in Wave 2. Since $J_m\ge |j_m|$, the same lower bound applies asymptotically to $J_m$. Apply this to the known semistable Frey family with `A=-1,B=2^n,C=B-1`, n>=5. It has

$$j_0=\frac{256(B^2-B+1)^3}{B^2(B-1)^2}\ge32B^2,\qquad N=2\operatorname{rad}(B-1)<2B.$$

Conductor is invariant under rational isogeny. For every fixed m and every `0<eta<2^(2-m)`, the displayed inequality implies, uniformly over every rational 2-isogeny chain of length at most m,

$$\frac{J_m}{1728N^{\eta/2}}\longrightarrow\infty\qquad(B=2^n\to\infty).$$

Thus a fixed depth independent of eta cannot place all curves in the LOW regime. This is a proved obstruction to **that precise bounded-depth strategy**. It does not exclude a depth depending on eta, other kinds of transformations, or a direct proof of CUSP. No isogeny-class classification theorem is invoked here.

### 7.3 Literature input did not close LOW/CUSP

The exact 2025 fixed-polynomial-family result of Cuevas Barrientos–Pasten [H3, Theorem1.1] bounds logarithmic height by a subexponential expression in the conductor. It is not a sharp power-law bound for H, and its constant depends on the fixed polynomial family. Pasten's 2026 arXiv 2609.17390 full text could not be retrieved in this pass; its abstract-level status is unchanged from Wave 1. No theorem was silently upgraded from an abstract.

The original LOW and CUSP estimates are therefore still BLOCKED. The completed reduction in §§2–6 changes the root route, not the truth status of these height estimates.

## 8. Verification scope

`verify.py` checks all polynomial identities exactly, the finite modulo 3 obstruction exhaustively, finite-field point counts at 5 and 7, rational doubling of (3,6), and the arithmetic behavior of the two maps on a bounded regression domain. These are mathematical certificate checks, not a search claimed to cover all rational points. The rank-zero proof above covers all rational points by classical descent.

With `--require-sage`, the script additionally requires an independent Sage `rank(proof=True, algorithm="mwrank_lib")` result 0, torsion order 4, the exact torsion point set, and genus 2. It must fail if Sage is absent. Hosted success may only be claimed after the orchestrator attaches the observed run receipt. Local checks alone do not earn `LEAN_VERIFIED`.

**Observed hosted verification:** the orchestrator's independent Sage 10.6 job succeeded in [run46039036660](https://github.com/davidlueng986-alt/math-open-to-closed-compute/actions/runs/46039036660), job140641767556, source commit `3b2425e4d6006b7e1f71ec0814272ab029794612`. Both elliptic curves have certified rank 0 using `mwrank_lib`, `proof=True`, `use_database=False`, and the exact torsion sets stated above; conductor 96 was also returned. The degree 6 discriminant, genus 2, Bezout identity and modulo 3 obstruction were checked. The raw result and source hashes are in [../wave3/verification/curves/result.json](../wave3/verification/curves/result.json) and [provenance.json](../wave3/verification/curves/provenance.json). This is the independently authored orchestrator verifier, not a claim that this agent's optional-Sage script has already been hosted.

This agent's local verifier passed 8 exact identities, all 8 nonzero residue pairs modulo 3, both finite-field counts, and all 3283 positive primitive odd-c triples with c<=180 and first summand odd. Of 20 input nonroots, 18 escaped with the cubic and 2 needed the quartic. These bounded tests detect arithmetic/normalization mistakes; the universal escape theorem comes from the written proof, not this finite sample.


## Sources

- **[D1]** A.J.Hollier, B.K.Spearman, Q.Yang, *Elliptic Curves y²=x³+pqx with Maximal Rank*, International Mathematical Forum 5 (2010), no.23,1105–1110, §2: https://www.m-hikari.com/imf-2010/21-24-2010/spearmanIMF21-24-2010.pdf . Only the unconditional general descent formula is imported, not the paper's parity-dependent rank 4 application.
- **[D2]** J.H.Silverman and J.Tate, *Rational Points on Elliptic Curves*, Chapter III; J.H.Silverman, *The Arithmetic of Elliptic Curves*, X.4 and VII.3: https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf . Classical descent and prime-to-p torsion reduction inputs are explicit imports.
- **[D3]** SageMath official reference, `rank`, torsion, and rational-curve algorithms: https://doc.sagemath.org/html/en/reference/arithmetic_curves/sage/schemes/elliptic_curves/ell_rational_field.html .
- **[H1]** W.Stein, *Szpiro and ABC*: https://wstein.org/mcs/archive/Fall2001/notes/12-10-01/12-10-01/node2.html . The ordinary/modified distinction and 6/5 implication are used; no erroneous displayed Frey formula from these notes is used.
- **[H2]** A.V.Sutherland, *Modular polynomials*: https://math.mit.edu/~drew/ClassicalModPolys.html ; the displayed Phi2 is the classical modular polynomial; estimate (*) is derived directly from its coefficients.
- **[H3]** J.Cuevas Barrientos and H.Pasten, *On the greatest prime factor of polynomial values and subexponential Szpiro in families*, arXiv 2504.15971v2: https://arxiv.org/html/2504.15971v2 .
- **[F]** G.Faltings, *Endlichkeitssätze für abelsche Varietäten über Zahlkörpern*, Invent.Math.73(1983),349–366, with 1984 erratum. Primary academic-hosted article: https://math.uchicago.edu/~drinfeld/Deligne%27s_conjecture_Manin_conf/Faltings_argument/Faltings.pdf . This is needed only for the optional finiteness fallback, not the exact descent proof.

No literature novelty or abc closure is claimed. The preferred main implementation is the separately credited Fermat-map proof.


## Final hosted execution receipt — 2026-11-28

This receipt supersedes the pending-hosted wording in the original research draft. The exact submitted verifier succeeded in [run 46040760555](https://github.com/davidlueng986-alt/math-open-to-closed-compute/actions/runs/46040760555), job 140647642833, source `03cbd0a1991144457cc014443cd4d9cf4b2520dd`. Artifact ZIP SHA256: `2c296112a85a3358c259c3c6019969a1654d855687d8ac5086c314aad0d6d43b`. Source-file hashes were checked against the downloaded provenance.

Status `CHECKED`: exact computations are reproducible and passed. Universality of the written structural results rests on their proofs; the open ROOT/LOW/CUSP estimates are unchanged.
