# ABC Wave 3 — Agent 2: late orbit power kernels

Date: **2026-11-28 (Asia/Taipei)**. Self-claimed package: **ORBIT-CORE**.

**Original abc status: BLOCKED.** Neither positive normalized lifting mass nor zero normalized lifting mass has been proved. The contribution is an unconditional, but ineffective, exclusion of one proposed source of positive mass: the new differences cannot remain in bounded power-free classes at arbitrarily late indices, even when the seed varies. It uses an explicit classical Faltings/Darmon–Granville import, not a new proof of that import. This is external exploratory work for independent review; no literature novelty is asserted.

## 1. What changed, and what did not

For a positive primitive opposite-parity seed, write

\[
T(a,b,c)=((a-b)^2,4ab,c^2),\qquad
c_j=c_0^{2^j},\quad d_j=a_j-b_j,\quad D_j=|d_j|.
\]

For a fixed integer \(m\ge2\), define the *power-free kernel*

\[
K_m(D)=\prod_{p\mid D}p^{v_p(D)\bmod m}.
\]

This is different from \(\operatorname{rad}(D)\). In particular, \(K_2(D)\) is the squarefree integer in the square class of \(D\); a prime of even valuation does not appear in it.

The main result is:

> **Uniform late-index kernel escape — PROVED, with a classical import.** For every fixed \(m\ge2\) and every \(B\ge1\), there is an integer \(J(m,B)\) such that, for **every** permitted seed and every \(j\ge J(m,B)\),
> \[
> \boxed{K_m(D_j)>B.}
> \]
> More precisely, for any finite set of nonzero coefficients \(\mathcal T\subset\mathbb Z\), there are only finitely many pairs (seed, index \(j\ge3\)) for which \(d_j=t y^m\) with \(t\in\mathcal T\), \(y\in\mathbb Z\).

Ordered versus unordered seeds changes the finite count by at most two and does not affect the theorem. The bound is ineffective here. For each fixed \(m\), the theorem rules out a late orbit construction based on bounded \(m\)-power-free kernels. It does **not** bound a growing kernel at the exponential scale relevant to abc.

For \(m=2\), the exact comparison

\[
\boxed{
\frac12\log\frac{D_j}{K_2(D_j)}
\le e_j:=\log\frac{D_j}{\operatorname{rad}(D_j)}
\le\log\frac{D_j}{K_2(D_j)}
}
\]

shows the remaining gap. The main route would require either a fixed-seed power saving in \(K_2(D_j)\) infinitely often, or the sharp opposite assertion

\[
\log K_2(D_j)=\log D_j-o(2^j).
\]

Neither follows from kernel escape. The hard disproof frontier remains **one** unproved infinite estimate, `W2-A1-POSITIVE-MASS`; the alternative orbit-exclusion target `W2-A1-ZERO-MASS` also remains open.

## 2. Exact homogeneous form

The recurrence gives

\[
d_{j+1}=2d_j^2-c_j^2,\qquad c_{j+1}=c_j^2.
\]

Put

\[
f(X)=2X^2-1,
\]

and calculate

\[
f^{\circ3}(X)=P(X)
=128X^8-256X^6+160X^4-32X^2+1.
\]

Its homogeneous degree-eight form is

\[
F(X,Z)=128X^8-256X^6Z^2+160X^4Z^4-32X^2Z^6+Z^8.
\]

For every \(j\ge3\),

\[
\boxed{d_j=F(d_{j-3},c_{j-3}).}
\]

The predecessor pair is primitive: \(\gcd(d_{j-3},c_{j-3})=1\). Indeed, a common prime would divide both \(a-b\) and \(a+b\), hence divide both summands or be 2; primitivity and opposite parity exclude both possibilities. Also

\[
0<|d_{j-3}|<c_{j-3},\qquad
c_{j-3}=c_0^{2^{j-3}}\ge3^{2^{j-3}}.
\]

The eight roots of \(P\) are simple. This can be proved without a numerical root calculation. Set

\[
Q(X)=128X^7-192X^5+80X^3-8X=P'(X)/8.
\]

The exact polynomial certificate is

\[
\boxed{P(X)^2+(1-X^2)Q(X)^2=1.}
\]

Thus \(P\) and \(P'\) have no common root in characteristic zero. Since \(F(1,0)=128\ne0\), the homogeneous form also has eight distinct projective roots and no root at infinity.

These are polynomial identities, proved by expansion. The supplied checker expands them over the integers. `Structural.lean` contains the same identities and the no-common-zero consequence for independent kernel verification; it is not labelled `LEAN_VERIFIED` until an actual successful compiler receipt exists.

## 3. Proof of uniform kernel escape

### 3.1 Classical input, explicitly isolated

We use the following consequence of Darmon–Granville, *On the equations \(z^m=F(x,y)\) and \(Ax^p+By^q=Cz^r\)*, Theorem 1 and the corollary immediately following it, pp. 514–515:

If a binary form has at least eight distinct simple roots and \(m\ge2\) is fixed, then for a fixed nonzero coefficient \(t\), the equation

\[
F(x,z)=t y^m,\qquad \gcd(x,z)=1,
\]

has only finitely many distinct projective ratios \(x/z\) among integral solutions. The theorem permits algebraic coefficients, so multiplying the form by \(1/t\) is allowed. Here the primitive pair and \(z>0\) determine the integers \(x,z\) uniquely; each determines finitely many \(y\). Thus in our situation there are finitely many primitive pairs as well.

Primary source, read directly: [Darmon–Granville, 1995](https://www.math.mcgill.ca/darmon/pub/Articles/Research/12.Granville/pub12.pdf). The cited theorem is unconditional and derives from Faltings. Its proof is imported; this contribution does not formalize it in Lean.

### 3.2 Application to the actual orbit

Fix \(m\) and a finite set \(\mathcal T\) of nonzero integer coefficients. For each \(t\in\mathcal T\), Section 2 verifies every hypothesis of the classical input. Hence there are finitely many pairs

\[
(x,z)=(d_{j-3},c_{j-3})
\]

with \(F(x,z)=t y^m\).

Let \(H\) be the largest positive denominator \(z\) among this finite union; if the union is empty, there are no such events. Every permitted event satisfies

\[
3^{2^{j-3}}\le c_0^{2^{j-3}}=z\le H.
\]

Only finitely many indices \(j\ge3\) satisfy this inequality. For each such \(j\), \(c_0\) is determined by \(z=c_0^{2^{j-3}}\), when an integral root exists. There are finitely many positive pairs \(a_0+b_0=c_0\). Therefore the pairs (seed, \(j\ge3\)) are finite.

Now take

\[
\mathcal T=\{-B,-B+1,\ldots,-1,1,\ldots,B\}.
\]

If \(K_m(D_j)\le B\), write \(D_j=K_m(D_j)y^m\). With the sign of \(d_j\), this is one of the finitely many equations above. The finite set of possible indices has a maximum, proving the claimed \(J(m,B)\). For a real bound B, replace it by its integer part. \(\square\)

The theorem does not claim that the finite set has been computed. It provides no explicit or usable rate for \(J(m,B)\).

### 3.3 Direct Faltings proof for squares

For \(m=2\), the argument has a particularly transparent curve form. If \(d_j=t y^2\), then

\[
X=\frac{d_{j-3}}{c_{j-3}},\qquad
Y=\frac{y}{c_{j-3}^4}
\]

is a rational point on

\[
C_t:\quad tY^2=P(X).
\]

By the squarefreeness certificate, its smooth projective model has genus \((8-2)/2=3\). It is geometrically irreducible because a squarefree polynomial with eight roots cannot be a square in \(\overline{\mathbb Q}(X)\). Faltings gives finitely many rational points. Their reduced X-denominators are bounded, while every orbit predecessor has reduced denominator exactly \(c_0^{2^{j-3}}\). This proves the same uniform conclusion for every finite set of square classes, independently of the higher-power formulation.

## 4. Why this does not prove zero normalized mass

Let \(D\ge1\). Write

\[
D=K_2(D)B_D^2,\qquad
B_D=\prod_p p^{\lfloor v_p(D)/2\rfloor},\quad
Q_D=D/\operatorname{rad}(D).
\]

For every positive prime exponent \(v\),

\[
\lfloor v/2\rfloor\le v-1\le2\lfloor v/2\rfloor.
\]

Consequently,

\[
B_D\mid Q_D\mid B_D^2,
\]

and taking logarithms proves the displayed two-sided mass comparison in Section 1. It follows that

\[
e_j=o(2^j)
\iff
\log D_j-\log K_2(D_j)=o(2^j).
\]

Using the already recorded fixed-seed Baker estimate from Wave 1, \(\log D_j=2^j\log c_0-O_{\rm seed}(j)\). Thus the sharp exclusion target is

\[
\frac{\log K_2(D_j)}{2^j}\longrightarrow\log c_0.
\]

The theorem proved here only says \(K_2(D_j)\to\infty\), uniformly in the late index. It does not give a positive lower bound for \(\log K_2(D_j)/2^j\), much less the required limit. For example, kernels growing like a tiny positive power of \(D_j\) would satisfy escape while still providing positive normalized mass. No claim is made that such a sequence actually exists.

There is also an exact sufficient construction target: if one fixed seed has

\[
K_2(D_j)\le D_j^{1-\eta}
\]

for some fixed \(\eta>0\) and infinitely many j, then \(e_j\ge(\eta/2)\log D_j\), so Baker plus the established Wave 2 forward implication yields a genuine abc countersequence. Conversely, positive normalized mass forces a fixed power saving in \(K_2(D_j)\) along a subsequence. This is an equivalent diagnostic, not a newly solved estimate.

## 5. Literature attack: the exact Lucas embedding

Set \(d=d_0\), \(c=c_0\), and

\[
\alpha=d+2\sqrt{-a_0b_0},\quad
\beta=d-2\sqrt{-a_0b_0}.
\]

Then \(\alpha+\beta=2d\), \(\alpha\beta=c^2\), and \(\gcd(2d,c^2)=1\). The ratio \(\alpha/\beta\) is not a root of unity by the Wave 1 non-torsion argument. The Lucas sequences with parameters \((u,v)=(2d,c^2)\) obey

\[
V_{2^j}=2d_j,
\qquad
U_{2^{j+1}}=2^{j+1}\prod_{i=0}^{j}d_i.
\]

The first identity follows by the trace-doubling recurrence; the second follows from \(U_{2n}=U_nV_n\) and \(U_1=1\). For every odd \(p\mid D_j\), its rank of apparition in U is exactly \(2^{j+1}\), because \(\alpha/\beta=z^2\) has that order modulo p. Its initial multiplicity is \(v_p(D_j)\). For \(j\ge1\), the first-occurrence primitive part at index \(2^{j+1}\) is therefore exactly \(D_j\); the nonprimitive factor 2 in the cyclotomic value has been removed.

Two sources were examined for a core estimate:

1. **Riasat (2026), arXiv:2611.20650v1.** Theorem 1.1 controls repeated primitive-prime mass when \(\phi(n)/n\) stays bounded below, but explicitly assumes rational abc. Our indices have ratio 1/2. Applying that theorem would establish the desired negligible mass only conditionally on the conjecture being investigated, so it cannot close this route. The unconditional Theorem 1.3 describes the initial multiplicity by distance to a Hensel root; the root varies with p, and the theorem gives no required global sum bound. [Primary full text](https://arxiv.org/html/2611.20650v1).
2. **Stewart (2010 preprint; subsequent Acta Mathematica publication).** Theorem 1 gives a large prime divisor of the cyclotomic value. Here \(\Phi_{2^{j+1}}(\alpha,\beta)=2d_j\), so eventually the greatest prime of \(D_j\) exceeds \(2^{j+1}\exp(\log(2^{j+1})/(104\log\log(2^{j+1})))\). This is unconditional, but yields a logarithmic radical contribution on the scale j per layer, not \(2^j\), and does not force that prime's multiplicity to be one. [Primary paper](https://arxiv.org/pdf/1008.1274), Theorem 1.

Both sources' hypotheses and the factor-of-two index conversion were checked. Neither supplies an unconditional bound on the normalized repeated mass.

## 6. Constructive attack and a diagnostic counterexample

An early finite search found no square \(D_2\) for small permitted seeds. That observation is not a theorem: the exact seed

\[
\boxed{(a_0,b_0,c_0)=(233930115,10478411804,10712341919)}
\]

has

\[
D_2=4936424930851777122654982737863450361601
\]

which is a perfect square. The verifier reconstructs the integer square root and the orbit directly. This refutes the auxiliary claim that square differences are impossible from index 2 onward.

The witness was found structurally, using rational points on

\[
Y^2=8X^4-8X^2+1.
\]

A birational map from \(E:y^2=x^3+4x^2+2x\) is

\[
X=x/y,\qquad Y=(2x+4)X^2-1.
\]

The point \(7(-1,1)\) gives the rational X leading to the displayed seed. This is an exact group-law construction, not a search inferred to cover all points. It produces one high-multiplicity event, not infinitely many late events for a fixed seed. The degree-eight curve appearing after three iterations has genus 3; its finite rational-point set is not enumerated here.

The earlier Hensel/CRT construction can force arbitrarily large valuation by changing the seed. It likewise does not provide one fixed seed at infinitely many levels. The uniform kernel-escape result now adds a stronger restriction on any such construction with bounded full power-free kernel: it cannot continue to arbitrarily late levels even with changing seeds.

## 7. Verification and exact claim boundaries

`verify.py` uses only Python's standard library. It checks the polynomial composition and squarefreeness certificate exactly, the Lucas identities and finite-field rank conversion on a bounded set of small seeds, the prime-exponent comparison, and the elliptic-curve construction of the displayed large square witness. It writes source hashes and GitHub provenance when run in Actions.

These checks do not verify Faltings or Darmon–Granville and do not estimate the unresolved limsup. The infinite result is the written reduction to an explicitly identified classical theorem. The Lean source only formalizes the algebraic certificate and integer-exponent interface; its status remains pending until the orchestrator records actual hosted verification.

The following outcomes must remain distinct:

- **PROVED:** uniform late-index escape from every bounded fixed-m power-free kernel family, with the classical import.
- **FAILED:** a proposed disproof mechanism that keeps those kernels bounded at arbitrarily late levels.
- **BLOCKED:** producing a power-saving kernel along infinitely many levels of a fixed seed, or proving sharp kernel growth.
- **CONDITIONAL:** importing the 2026 abc-assuming primitive-multiplicity theorem to prove zero mass.
- **CHECKED:** finite symbolic identities and the large index-2 witness.

No global abc core estimate was solved in this package. The result eliminates a concrete infinite construction mechanism and identifies precisely why qualitative finiteness is still insufficient for the main route.


## Final hosted execution receipt — 2026-11-28

This receipt supersedes the pending-hosted wording in the original research draft. The exact submitted verifier succeeded in [run 46040760555](https://github.com/davidlueng986-alt/math-open-to-closed-compute/actions/runs/46040760555), job 140647642827, source `03cbd0a1991144457cc014443cd4d9cf4b2520dd`. Artifact ZIP SHA256: `2c296112a85a3358c259c3c6019969a1654d855687d8ac5086c314aad0d6d43b`. Source-file hashes were checked against the downloaded provenance.

Five declarations in `Structural.lean` compiled in Lean 4.36.0 with only `propext`, `Classical.choice`, and `Quot.sound`; none uses a custom axiom. These are the exact polynomial and valuation-exponent interfaces, not a kernel proof of Darmon–Granville, its application to all orbits, or abc. The separate exact finite Python audit also succeeded.
