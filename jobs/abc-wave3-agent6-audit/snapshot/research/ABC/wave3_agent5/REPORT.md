# ABC Wave 3 — Agent 5: direct ROOT obstruction and a fixed-prime test family

**Date:** 2026-11-28 (Asia/Taipei). **Self-claimed task:** `ROOT-CORE`.
**Status of ROOT and original abc:** `BLOCKED`.
**Scope:** external exploratory work for independent review; no priority claim.

## 1. Result and effect on the remaining gap

No sharp global radical estimate was proved. The contribution is an explicit
infinite family of genuine roots showing that the root condition does **not**
force any coordinate's squarefree kernel to grow, together with an exact audit
of why the cited unconditional bounds still miss the required exponent even
on this family.

For every odd positive integer k, define integers u_k,v_k by

    (1+2i)^k = u_k + i v_k.

Then

    (a_k,b_k,c_k) = (u_k^2,v_k^2,5^k)

is a primitive positive root, and its three squarefree kernels are exactly

    (K_2(a_k),K_2(b_k),K_2(c_k)) = (1,1,5).

Here K_2(n)=product p^(v_p(n) mod 2), whereas rad(n)=product p over all prime
divisors. These are different invariants. In particular, K_2(abc)=5 for the
entire family does not mean rad(abc)=5.

This disproves every proposed estimate of the form

    c <= F(K_2(a),K_2(b),K_2(c))

on all roots, for a finite-valued function F, and hence every attempt to infer
a growing squarefree kernel merely from membership in the root domain. It
does not disprove an estimate involving the full radical. The elementary
construction supplies a concrete family on which the actual radical problem
remains visible.

The Frey curve attached to these roots has v_5(j)=-2k, so the 2026 theorem for
elliptic curves with integral j-invariant does not apply to any member of this
family. The directly applicable fixed-prime bound gives only

    log R_k >= c_0 (log k)^2 / log log k

for all sufficiently large odd k and some c_0>0. ROOT would require

    log R_k >= (1-delta) k log 5 - A_delta

for every delta>0 with a uniform constant. Thus this package removes an invalid
shortcut but proves **zero** previously open global estimates. The main Wave 3
ROOT-only closure route and its one-element frontier are unchanged.

## 2. Complete elementary construction — PROVED

The complex notation is optional. Start with (u_0,v_0)=(1,0) and use the integer
recurrence

    u_(k+1)=u_k-2v_k,    v_(k+1)=2u_k+v_k.                 (2.1)

The identity

    (u-2v)^2+(2u+v)^2=5(u^2+v^2)

proves by induction that

    u_k^2+v_k^2=5^k.                                    (2.2)

Also u_k is odd and v_k is even. Put w_k=u_k-2v_k. Since

    w_(k+1)=2w_k-5u_k,

we have

    u_k-2v_k == 2^k (mod 5).                            (2.3)

Suppose a prime divides both u_k and v_k. By (2.2) it must be 5, but (2.3)
excludes that. Therefore gcd(u_k,v_k)=1. Neither coordinate is divisible by 5:
if one were, (2.2) would make the other divisible by 5 too.

For **odd k**, 5^k is not a square, so (2.2) also shows u_k and v_k are both
nonzero. Hence a_k=u_k^2 and b_k=v_k^2 are positive. Equation (2.2), the
coprimality just proved, and the parity statements show that

    a_k+b_k=c_k,    gcd(a_k,b_k)=1,    c_k odd.

The existing image criterion `W2-A2-IMAGE` says that an odd-c triple is in the
image of T exactly when both c and the odd summand are squares. Here c_k=5^k
is not square. Therefore each odd-index triple is a root.

Finally,

    K_2(a_k)=K_2(b_k)=1,    K_2(c_k)=5,
    R_k=rad(a_k b_k c_k)=5 rad(|u_k v_k|).               (2.4)

The last identity uses 5 not dividing u_k v_k. The heights c_k=5^k are
unbounded. This proves the family and all assertions in Section 1 concerning
squarefree kernels without invoking a finiteness theorem, density argument,
or unproved hypothesis.

Some exact examples are

| k | u_k | v_k | (a_k,b_k,c_k) |
|---:|---:|---:|---|
| 1 | 1 | 2 | (1,4,5) |
| 3 | -11 | -2 | (121,4,125) |
| 5 | 41 | -38 | (1681,1444,3125) |

The signs of u_k and v_k have no bearing on positivity of a_k and b_k.

### Relation to the existing orbit map

For every k, squaring u_k+i v_k gives

    u_(2k)=u_k^2-v_k^2,    v_(2k)=2u_k v_k.

Consequently

    T(a_k,b_k,c_k)=(a_(2k),b_(2k),c_(2k)).               (2.5)

The odd k therefore index roots in this family, while multiplication of k by
powers of 2 follows their T-orbits. Distinct odd k give distinct root triples
because their total coordinates are different. They are not a single fixed
root orbit. This matters when checking quantifier scope in a proposed use of
a fixed-orbit estimate.

## 3. A falsified surrogate, and the actual remaining sub-lemma

### 3.1 Squarefree-kernel height control — FAILED

The following candidate strategy is false:

> There is a finite-valued function F on triples of positive integers such
> that every root satisfies c<=F(K_2(a),K_2(b),K_2(c)).

On the family of Section 2 this would give 5^k<=F(1,1,5) for every odd k,
which is impossible. In particular, no fixed positive eta and constant C can
give max{K_2(a),K_2(b),K_2(c)}>=c^eta/C for all roots.

Only this surrogate is `FAILED`; neither ROOT nor abc is falsified. A root
merely records failure of a simultaneous-square test, not the amount of
distinct prime support left in the coordinates.

### 3.2 Gaussian-root radical limit — BLOCKED necessary subproblem

A concrete necessary test for ROOT is

    lim_(k -> infinity, k odd) log R_k / (k log 5) = 1.  (G)

This statement is equivalent to ROOT restricted to this family. Indeed, for
all k under consideration,

    R_k=5 rad(|u_k v_k|) <= 5 |u_k v_k| <= (5/2) 5^k,

where the last inequality follows from 2|u_k v_k|<=u_k^2+v_k^2. Thus the
limsup of the displayed quotient is at most 1. The uniform restricted ROOT
inequalities imply the liminf is at least 1, by dividing by k log 5 and then
letting delta decrease to zero. Conversely, (G) gives each restricted ROOT
inequality for all sufficiently large odd k; a finite enlargement of A_delta
covers the remaining k. This is an exact equivalence for this family only.

Failure of (G) would produce a countersequence to abc: if for some eta>0
there are infinitely many odd k with log R_k <= (1-eta) k log 5, their
qualities satisfy q_k >= 1/(1-eta)>1. No such sequence was found or proved.
Proving (G) would settle a necessary special case; it would not prove ROOT
on all roots.

For a useful exact decomposition put

    e_k=log(|u_k v_k|/rad(|u_k v_k|)) >= 0,
    g_k=log(5^k/(2|u_k v_k|)) >= 0.

Then

    log R_k = k log 5 + log(5/2) - e_k - g_k.             (3.1)

Therefore (G) is exactly e_k+g_k=o(k) along odd k. Equation (3.1) is proved
algebra; the little-o estimate is the unproved arithmetic subproblem. No
unproved bound for g_k or e_k is inserted into the claim.

This target is recorded as a **necessary diagnostic**, not as another
independent prerequisite artificially added to the main closure frontier.

## 4. Audit of applicable unconditional estimates

### 4.1 Pasten's fixed-prime bound and exact remaining scale

Pasten, *The largest prime factor of n^2+1 and improvements on subexponential
ABC*, Theorem 1.4(2), gives

    log c <= q exp(kappa sqrt((log R) log log R)),
    q=min{P(a),P(b),P(c)},                               (4.1)

with an absolute constant; P(1)=1. The primary text was read directly at
https://arxiv.org/html/2312.03566v1 . Its separate n^2+1 theorem concerns that
specific polynomial and cannot silently be applied to an arbitrary root.

In our family P(c_k)=5, so q<=5. Write L_k=log R_k. Taking logs in (4.1)
gives, for all sufficiently large odd k,

    L_k log L_k >= (log k)^2/(4 kappa^2).

If L_k>=(log k)^2, the desired lower bound below follows immediately. If not,
log L_k<=2 log log k, and so

    L_k >= (log k)^2/(8 kappa^2 log log k).

After choosing a smaller positive constant to cover both cases,

    log R_k >= c_0 (log k)^2/log log k.                  (4.2)

This is a valid unconditional consequence of an existing theorem, not a new
improvement on Pasten. The lower-bound function in (4.2) is o(k), whereas (G)
requires log R_k to have asymptotic leading coefficient log 5 times k.
Thus the cited inequality alone does not establish (G). This comparison does
not assert that the actual radicals grow as slowly as the lower bound.

The proof of (4.1) combines logarithmic-form estimates with a product bound on
prime exponents. Root membership does not supply a new quantitative input to
that proof: the present roots already satisfy its fixed-prime hypothesis yet
retain the unresolved jump from (4.2) to (G).

### 4.2 2026 general Szpiro improvement

Pasten, *Improved bounds for Szpiro's conjecture*, arXiv:2609.17390, Corollary
1.3, proves h(E) <<_S N for elliptic curves semistable outside a fixed finite
set S; the paper also uses log Delta << max{1,h(E)}. The primary text was
read via https://arxiv.org/abs/2609.17390 (some display equations are absent
from the browser extraction, but the stated h(E)<<_S N consequence is also
explicit in its concluding text). No secondary AI summary is used as a
mathematical dependency.

For Frey curves the usual bounded contribution at 2 gives N<<R, so this is
on the scale log c<<R, not log c<<log R. On our prime-power family it is weaker
than (4.1). It supplies no estimate exploiting the ROOT nonsquare condition.
The paper improves a broad class of elliptic curves; that improvement should
not be presented as a sharp abc exponent for the present family.

### 4.3 The integral-j improvement does not cover this family — PROVED

For E_k: y^2=x(x-a_k)(x+b_k), the standard Frey invariants give

    j(E_k)=256(a_k^2+a_k b_k+b_k^2)^3/(a_k^2 b_k^2 c_k^2).

As 5 divides c_k=a_k+b_k and divides neither a_k nor b_k,

    a_k^2+a_k b_k+b_k^2 == a_k^2 != 0 (mod 5).

It follows exactly that

    v_5(j(E_k)) = -2k.                                  (4.3)

Thus j(E_k) is nonintegral for every odd k. Pasten's *Power-saving bounds for
Thue--Mahler and Mordell equations*, arXiv:2608.23559, Theorem 1.6, explicitly
requires integral j for its height application. That hypothesis fails here.
The primary introduction and theorem scope were read directly at
https://arxiv.org/abs/2608.23559 . Equation (4.3) is our own exact calculation;
we do not claim to have independently reproved that paper's new theorems.

## 5. Reproducibility and status boundary

`verify.py` is a standard-library exact-integer verifier. It checks the norm,
coprimality, parity, congruence, nonsquare total, full family membership and
5-adic j calculation for all 501 odd indices through k=1001. It also checks
200 doubling identities, directly factors the small-coordinate sample
k<=21, and records exact certificates and source SHA256. Large-index
radicals are **not** estimated by pretending unfactored integers are prime.

The universal arguments are the written proofs in Sections 2--4. Finite
execution is tagged `CHECKED`, not `LEAN_VERIFIED`. No hosted run is claimed
until the orchestrator attaches an actual receipt. The compute job is
`jobs/abc-wave3-agent5-root-kernel/`, with the standard invocation

    bash jobs/abc-wave3-agent5-root-kernel/run.sh 0 1 OUT

The job creates result.json and certificates.json. Its output explicitly
sets original_abc_closed=false and new_global_core_estimates_proved=0.

## 6. Handoff

- Keep `W2-A2-ROOT-BOUND` blocked. Agent 1's ROOT-only implication is unaffected.
- Retire the squarefree-kernel surrogate using the infinite counterfamily.
- If claiming an improvement on ROOT, test it against the exact odd-index
  family above; all three squarefree kernels are fixed and the associated
  Frey j-invariants are nonintegral.
- (G) is an explicit necessary proof/disproof target, but no additional main
  DAG prerequisite or solved-core count should be manufactured from it.
- No numerical K_epsilon, infinite high-quality subsequence, or abc closure
  is claimed by this package.

The known sources are credited in sources.json. Construction and obstruction
proofs are given completely here; they are elementary structural work, not
a claim to solve an established open estimate.


## Final hosted execution receipt — 2026-11-28

This supersedes the draft pending-hosted wording. Actual run [46041841448](https://github.com/davidlueng986-alt/math-open-to-closed-compute/actions/runs/46041841448), job140651292050, source `a4639f950f2acf69ecf27e0d8eb73ce28b6ad9d7` succeeded. The downloaded summary artifact has SHA256 `d4a22ad847df88f0d16ebbb85ae071efd436aab893170d30b783f4685dd0fd42`; all compute bundle source hashes match the recorded provenance. All501 odd-index checks and the stated exact certificates passed. Status remains CHECKED only, with no new global estimate or abc closure.
