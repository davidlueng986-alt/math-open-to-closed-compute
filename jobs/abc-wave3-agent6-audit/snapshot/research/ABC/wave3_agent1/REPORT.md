# ABC Wave 3 — Agent 1: a uniform quartic map into roots

**Date:** 2026-11-28 (Asia/Taipei). **Self-claimed task:** `VALUATION-CORE`.
**Scope:** external exploratory work for independent review. No literature novelty claim.

## Result and effect on the actual closure gap

`PROVED`: the existing `W2-A2-ROOT-BOUND` **alone** implies the full abc conjecture. The independent `W2-A2-GROWTH-BOUND` premise can be removed from that sufficient route. The proof is an explicit degree-four transformation together with the classical Fermat square-area descent, reproved below; it has **no exceptional triples** and needs no Faltings theorem.

This does **not** prove ROOT or abc. The refined root route changes from two simultaneous open estimates to one. GROWTH follows conditionally from ROOT because ROOT implies abc and abc implies GROWTH; GROWTH has not become an unconditional theorem. Zero open global arithmetic estimates were proved in this package.

The transformation was found while testing whether PRODUCT could bootstrap to a sharp height bound. That particular bootstrap still fails: the same quartic transformation preserves the thin-cusp loss in the PRODUCT exponent. Section 6 states the exact limited obstruction, without claiming that PRODUCT cannot imply abc by another method.

`PROVED` denotes the complete written arguments below, not kernel verification. `CHECKED` refers only to the finite exact verifier. Any later `LEAN_VERIFIED` status needs an actual source-pinned kernel receipt. In particular, Mathlib's `not_fermat_42` proves a **sum** of fourth powers is not a square and must not be cited as the **difference** theorem needed here.

## 1. Definitions and prior inputs

A primitive positive triple has positive integers a,b,c with a+b=c and gcd(a,b)=1. Its radical is R=rad(abc), with rad(1)=1. For odd c, exactly one summand is even. Throughout the quartic construction, **b is the even summand**, regardless of which summand is larger.

The Wave 2 image classification proves that an odd-c triple lies in the image of

    T(a,b,c)=((a-b)^2,4ab,c^2)

if and only if c and its odd summand are both integer squares. An odd-c triple outside that image is called a root. We use this established classification, not a new definition of root.

The exact open premise ROOT is:

> For every 0<δ<1/2 there is Aδ≥0, independent of the root, such that every root satisfies
>
> log R ≥ (1−δ) log c − Aδ.

The existing parity reduction is recalled and proved in Section 4 so the complete target remains explicit.

## 2. Classical Fermat square-area descent — PROVED

### 2.1 Primitive Pythagorean parametrization

If positive integers X,Y,Z satisfy X²+Y²=Z² and gcd(X,Y)=1, exchange X,Y so X is odd and Y is even. Then Z is odd. The positive integers (Z+X)/2 and (Z−X)/2 are coprime, and their product is (Y/2)². Hence they are m²,n² for coprime m>n>0. Therefore

    X=m²−n²,  Y=2mn,  Z=m²+n²,

and m,n have opposite parity. These assertions follow directly from factorization; the fact that coprime factors of a square are squares follows prime by prime.

### 2.2 No integer right triangle has nonzero square area

Suppose a positive integer right triangle has square area. Among all such triangles choose one with least hypotenuse Z. It is primitive: if the three sides have gcd g>1, division by g gives another integer right triangle. Its area is w²/g²; because that area is an integer, prime factorization gives g|w. Thus the smaller triangle still has square area, contradicting minimality.

Use the parametrization above. The square area is

    mn(m−n)(m+n).

The four positive factors m,n,m−n,m+n are pairwise coprime: m,n are coprime, m±n are odd, and their gcd divides 2. Each factor is therefore a square. Write

    m=r²,  n=s²,  m+n=u²,  m−n=v²,

with all r,s,u,v positive. The numbers u>v are odd. Set

    p=(u+v)/2,  q=(u−v)/2.

They are positive integers and

    p²+q²=m=r²,  2pq=n=s².

The second identity makes s even. Consequently p,q,r form another integer right triangle of square area pq/2=(s/2)². Its hypotenuse r is strictly smaller than the old Z=m²+n² because r²=m and n>0. This contradicts the choice of Z. ∎

### 2.3 No nonzero difference of fourth powers is a square

For positive b<c there is no integer w such that

    c⁴−b⁴=w².

If such w existed, the positive Pythagorean triangle with sides

    2b²c²,  c⁴−b⁴,  c⁴+b⁴

would have area

    b²c²(c⁴−b⁴)=(bcw)²,

contradicting Section 2.2. This proof needs no coprimality or parity assumption on b,c. ∎

This is a classical theorem, not a claimed new number-theoretic discovery. A primary academic exposition giving this descent and its fourth-power corollary is Karl-Dieter Crisman, *Number Theory: In Context and Interactive*, §3.4, especially Proposition 3.4.11 and Corollary 3.4.12:
https://math.gordon.edu/ntic/ntic2017/section-pyth-triples.html

## 3. The quartic root transformation — PROVED

For an odd-c primitive triple with b even, define

    A=c⁴−b⁴=a(c+b)(c²+b²),  B=b⁴,  C=c⁴.

All three are positive and A+B=C. Since gcd(b,c)=1, gcd(A,B)=1. C and A are odd, while B is even. C is a square, but A is not a square by Section 2.3. Thus (A,B,C) is always a root by the Wave 2 image criterion.

There are **no exceptional inputs** and no normalization factor.

Set P=c+b and Q=c²+b². The exact prime-support identity gives

    R′=rad(ABC)=rad(abc P Q).

In fact P,Q and abc are pairwise coprime here. Indeed gcd(P,bc)=gcd(Q,bc)=1; modulo a=c−b they are congruent to 2b and 2b² respectively, and a is odd. Finally gcd(P,Q) divides 2 and both are odd. Hence

    R′=R rad(P) rad(Q) ≤ R P Q < 4 R c³.                     (3.1)

Only the non-strict upper bound is needed below. The elementary constant 4 is uniform in every original triple.

The auxiliary triangle identity can be checked symbolically:

    (2b²c²)²+(c⁴−b⁴)²=(c⁴+b⁴)².

Its use with a purported square difference is the reason this transformation escapes the old T-image at every input.

## 4. ROOT alone implies full abc — PROVED implication

### 4.1 Odd-c logarithmic transport

Apply ROOT with a fixed δ to the root constructed in Section 3. Write H=log c and L=log R. Since log C=4H and (3.1) gives log R′≤L+3H+log4,

    (1−δ)4H−Aδ ≤ L+3H+log4,

so

    (1−4δ)H ≤ L+Aδ+log4.                                  (4.1)

All constants remain independent of a,b,c.

Equivalently, if abc on roots is given in exponent form C<Kroot,η (R′)^(1+η), choose

    η=ε/(4+3ε),  0<η<1/3.

Then

    c^(1−3η) < 4^(1+η) Kroot,η R^(1+η),

and (1+η)/(1−3η)=1+ε. An odd-c constant is

    Kodd,ε=(4^(1+η) Kroot,η)^(1/(1−3η)).

This exponent conversion is not an estimate for Kroot,η; that unknown constant is the ROOT premise.

### 4.2 Even-c reduction and one explicit all-parity constant

If c is even, a,b are odd. Put l=a+c, which is odd. The triple

    (b²,4ac,l²)

is positive and primitive because b²+4ac=(a+c)² and gcd(b,2ac)=1. Moreover gcd(l,abc)=1: gcd(l,a)=gcd(l,c)=1 and gcd(l,b)=gcd(2a+b,b)=1 because b is odd. Its radical is

    Rodd=R rad(l) ≤ R l.

Apply the quartic construction to this odd-c triple, choosing its even summand 4ac. The resulting root has height coordinate l⁸ and radical at most

    4 Rodd (l²)³ ≤ 4 R l⁷.

ROOT consequently gives

    (1−8δ)log l ≤ log R+Aδ+log4.                            (4.2)

Now fix any target ε>0 and take

    δ=ε/[8(1+ε)].

It satisfies 0<δ<1/8<1/2 and 1−8δ=1/(1+ε). For even c, (4.2) and c<l give

    log c ≤ (1+ε)(log R+Aδ+log4).

For odd c, (4.1) gives the same weaker inequality because H≥0 and 1−4δ≥1−8δ. Therefore

    Kε=1+exp((1+ε)(Aδ+log4))                               (4.3)

is positive and satisfies the original strict inequality

    c<Kε R^(1+ε)

for **every** primitive positive triple. ∎

The proof above is a theorem about the implication ROOT ⇒ abc, with ROOT still open. It does not replace Aδ by a known effective value.

### 4.3 Equivalence and removal of the independent GROWTH premise

Conversely, abc at exponent ε=δ/(1−δ) yields ROOT, after rearranging logarithms and increasing Aδ to be nonnegative. Thus

    ROOT ⇔ full abc.                                      (4.4)

The Wave 2 exact orbit identity is

    Wn=Hn+L0−H0−Ln.

Given abc, for each δ there is Cδ≥0 with Ln≥(1−δ)Hn−Cδ uniformly over all triples. Hence

    Wn≤δHn+(L0−H0)+Cδ
      ≤max(L0−H0,0)+δHn+Cδ,

which is precisely the existing GROWTH estimate. Combining with (4.4) proves ROOT ⇒ GROWTH.

**DAG consequence:** retain `W2-A2-GROWTH-BOUND` as an open standalone mathematical claim and a consequence of ROOT; the root proof route now has the one-element frontier `{W2-A2-ROOT-BOUND}`. Do not mark ROOT or GROWTH unconditionally PROVED. No claim that this remaining estimate is easy is made.

## 5. Independent checks and scope of the machine evidence

The standard-library Python verifier checks primitive odd-c triples up to a stated finite height, the exact transformed primitive triple, nonsquareness of its odd summand by integer square root, the factorized radical identity, and the uniform radical upper bound. It independently factors A,B,C for a smaller subset. It also checks the complete even-c two-map transport, polynomial triangle identity, and exact rational epsilon conversions.

These checks test implementation and boundary cases; they do not replace the descent proof or prove ROOT. The verifier records its own source SHA256 and explicitly reports `original_abc_closed: false` and `new_global_core_estimates_proved: 0`.

The completed local run checked 5,841 odd-c primitive triples, 491 independently factored outputs, 1,037 complete even-c transports, and 200 exact rational parameter choices. Verifier SHA256: `885bbb77b5209675d0d0fd4df3e086d3c0258fec02eb6bae5ace0b329d9820fc`. See `local-evidence/result.json`. No hosted run is claimed until a receipt is added.

A formalization should target the difference-of-fourths theorem or the square-area descent itself. The pinned Mathlib file `Mathlib/NumberTheory/FLT/Four.lean` contains `not_fermat_42`, whose statement is a⁴+b⁴≠c². That statement is not the negative-sign equation used above. No direct reuse of it is asserted.

## 6. Why the same map does not solve PRODUCT

The original task asked whether

    PRODUCT:  ∀δ>0 ∃Cδ ∀primitive triples, abc≤Cδ R^(3+δ)

could itself give the sharp abc exponent by transformations. No proof of PRODUCT or THIN was obtained.

Here is a precise asymptotic diagnostic. Consider an unbounded sequence with a≤b, a/c→0, and subsequential limits

    α=lim log a/log c ∈[0,1),  r=lim log R/log c.

PRODUCT on the original sequence forces

    r≥(2+α)/3.                                            (6.1)

On the branch where b is even, the quartic root map has

    log(ABC)=(11+α+o(1))log c,
    log R′≤(r+3+o(1))log c.

PRODUCT on the transformed triples therefore again gives only

    11+α≤3(r+3),

which is exactly (6.1), not r≥1. More concretely, when b≥c/2,

    ABC ≥ (15/128) a c¹¹,   R′≤4Rc³,

so its PRODUCT inequality implies

    a c^(2−3δ) ≤ (128/15)·4^(3+δ)·Cδ·R^(3+δ).

The surviving a/c loss is explicit. Choosing δ separately for each triple is not justified, since Cδ is not uniform in that choice.

### Fixed Belyi-map budget obstruction

The same calculation has a scoped generalization. Assume a fixed degree-d rational Belyi map preserves the source tripod {0,1,∞}, and normalize its three homogeneous coordinate forms to a primitive integer triple. Its finite set of bad primes contributes a fixed constant. The reduced inverse-image tripod has d+2 points by Riemann–Hurwitz, so removing the three source points leaves a squarefree factor of degree d−1. Consequently the standard support estimate is

    R′≲R c^(d−1).

If the source cusp 0 has ramification index e≥1 and a/c→0, the product of the three normalized coordinates has logarithm

    [3d−e(1−α)+o(1)]log c.

Using PRODUCT only through this standard support estimate forces at most

    r≥1−e(1−α)/3 ≤ (2+α)/3.                               (6.2)

Thus a fixed finite collection of these transformations, using only their degree bounds on new radicals, cannot improve the strongest asymptotic inequality furnished by the identity map at this cusp. This is a statement about the displayed inequalities and this restricted proof method. It is **not** a theorem that PRODUCT is logically weaker than abc, and does not cover arithmetic savings in the new factors, maps of varying degree with uniform constants, or new number-field estimates.

The quartic ROOT theorem succeeds because ROOT supplies the sharp **height** coefficient, not the weaker **product** coefficient. The map makes a decisive change to domain coverage but does not manufacture the missing sharp arithmetic estimate.

For an external boundary check, van Frankenhuijsen's *Two Restricted ABC Conjectures*, arXiv:2010.09493v1, introduction and Theorem7.6, explains that its not-highly-divisible reduction uses bounded-degree number fields even to conclude abc over Q. A Q-only balanced estimate cannot silently be substituted into that theorem:
https://arxiv.org/html/2010.09493v1

## 7. What remains and what should be claimed

- `PROVED`: classical square-area descent; quartic map into roots; explicit radical/height transport; ROOT ⇒ full abc; ROOT ⇒ GROWTH; the scoped exponent-budget obstruction.
- `CHECKED`: only the stated finite verifier ranges.
- `BLOCKED`: ROOT, PRODUCT, THIN, full abc and an infinite counterexample sequence.
- No unconditionally new global exponent bound or countersequence is claimed.
- No need to add another difficult open lemma to the ROOT route: the descent is classical and has a complete proof here.
- The quantitative constant (4.3) is explicit **in the unknown ROOT constant**. It is not an unconditional numerical Kε.

This replaces the root route's former two simultaneous open estimates by one, while preserving the original target and all quantifiers.

## Sources and provenance

1. Existing repository Wave2 Agent2 image classification and root/growth definitions: `research/ABC/wave2_agent2/REPORT.md`, observed current main07d39071d2dd976a2f7f4f1a5587ea4cdb6d8a82 (unchanged from fixed Wave2 snapshot0d4a6c7bce5e2a8c2dbac4cfca6eeae2830dff99).
2. Existing Wave2 Agent3 PRODUCT/THIN definitions: `research/ABC/wave2_agent3/REPORT.md`, same baseline.
3. Crisman, *Number Theory: In Context and Interactive*, §3.4. https://math.gordon.edu/ntic/ntic2017/section-pyth-triples.html . Consulted as a source check for the classical theorem; the complete descent is reproduced in original exposition above.
4. Mathlib pinned source, read directly: https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/NumberTheory/FLT/Four.lean . It proves the sum-of-fourths theorem, not the needed difference theorem.
5. Machiel van Frankenhuijsen, *Two Restricted ABC Conjectures*, arXiv:2010.09493v1. https://arxiv.org/html/2010.09493v1 . Only the stated number-field scope boundary is imported; no contested IUT inequality is used.

The parent and Agent3 independently checked the quartic square-area implication after it was proposed. Their earlier cubic/quartic Faltings or rank-zero routes are alternatives; they are not dependencies of this proof.


## Final hosted execution receipt — 2026-11-28

This receipt supersedes the pending-hosted wording in the original research draft. The exact submitted verifier succeeded in [run 46040760555](https://github.com/davidlueng986-alt/math-open-to-closed-compute/actions/runs/46040760555), job 140647642797, source `03cbd0a1991144457cc014443cd4d9cf4b2520dd`. Artifact ZIP SHA256: `2c296112a85a3358c259c3c6019969a1654d855687d8ac5086c314aad0d6d43b`. Source-file hashes were checked against the downloaded provenance.

Status `CHECKED`: exact computations are reproducible and passed. Universality of the written structural results rests on their proofs; the open ROOT/LOW/CUSP estimates are unchanged.
