# Erdős #307 at the (49,12) split of 61 primes

This calculation tests both placements of two primes greater than 2381 in a cycle at the (49,12) split. The side of size 49 contains 2. The two large primes have unrestricted height. The [previous bounded search](https://github.com/davidlueng986-alt/math-open-to-closed-compute/blob/results/runs/erdos-307/45018719937/erdos-307.json) covers zero large primes. The [single-tail search](https://github.com/davidlueng986-alt/math-open-to-closed-compute/blob/results/runs/erdos-307-tail61/45019734608/tail61.json) covers one.

## Common bounds

For squarefree $n$ let $F(n)=\sum_{r\mid n} n/r$ with $r$ prime, and write $\sigma(n)=F(n)/n$. The two products in a solution to [Erdős #307](https://www.erdosproblems.com/307) are coprime and obey $F(A)=B,\ F(B)=A$. Here $A$ has 12 odd prime factors and $B$ has 49 factors. The union has mass $\sigma(A)+\sigma(B)\ge 2$. Write $T_j$ for the sum of the first $j$ prime reciprocals. Since $T_{58}+3/2382<2$, at most two primes exceed 2381.

The bound $T_{61}$ gives $0.907<\sigma(A),\sigma(B)<1.103$. The product of the smallest 49 primes exceeds $1.103\cdot2381^{12}$. So at least one large prime lies in $A$. If there are two large primes altogether, the largest prime on that side exceeds $10^{20}$. This follows from $B<1.103 A$, the same product lower bound for $B$, and at most 10 or 11 remaining primes $\le2381$ in $A$, according to placement. Put $\tau=10^{-20}+1/2382$. The remaining 59 primes have mass greater than $2-\tau$, contain every prime through 157, and are all at most 1190. These follow from $T_{60}-1/157+\tau<2$ and $T_{58}+1/1191+\tau<2$. Their $i$-th smallest prime is at most $(60-i)/(2-\tau-T_{i-1})$. Finally $T_{59}+\tau$ narrows each full side's mass to $(0.948,1.055)$. The bounded portion of $A$ contains 3 and 5 by these mass bounds. The exact inequalities are checked in the runner.

## Both large primes in the odd product

Write $A=dpq$ and $B=e$ with $p,q>2381$ and $d$ supported on 10 bounded odd primes. With $f=F(d)$ and $g=F(e)$, the two derivative identities give

$$pq=g/d,\qquad p+q=(e-fpq)/d,\qquad d e-f g=d^2(p+q).$$

Because $d,f,e$ are invertible where required, the last identity gives $\sigma(e)\equiv d f^{-1}\pmod{d^2}$. For a chosen prefix of $e$, subtract its reciprocal mass in this congruence. If the remaining product and derivative are $V,W$, the remaining equation is $W\equiv rV\pmod{d^2}$ for a computed residue $r$. Bounds $V\le V_0$ and $W\le W_0$ follow from the upper bounds on the ranks of the largest remaining primes. When $2 V_0 W_0<d^2$, the fraction $(rV-W)/(d^2 V)$ is a convergent of $r/d^2$. It is reduced since $\gcd(V,W)=1$. The determinant bound shows there is at most one possible reduced $W/V$ in the rectangle. We check its factorization within the bounded prime pool and the two algebraic tests for $pq$ and $p+q$. All branches unable to use this bound are extended by the next eligible prime. The only possible third primes of $d$ are 7 and 11. The enumeration uses exact upper and lower integers for each reciprocal and includes all admissible completions.

## One large prime on each side

Write $A=dp$ and $B=eq$ with $d$ supported on 11 odd bounded primes. Put $D=de,\ C=F(D),\ f=F(d),\ U=d^2+f^2,\ V=df$. The two derivative identities give

$$D(qU-V)-CqV=d^4.$$

The rank caps on the core supply lower bounds on the ordered reciprocal coordinates of $d$. The first 11 odd primes supply upper bounds, and 3 and 5 are fixed. The minimum possible reciprocal product subject to these bounds and the required total mass is attained by filling the coordinates from largest to smallest up to their upper bounds until attaining the required sum. This vector maximizes all initial partial sums at that total, so the concavity of the logarithm bounds any other coordinate product below by its product. Applied to $\sigma(d)>0.948-10^{-20}$, this gives $d\le H=443759330344295771$. The runner checks the bounds using rational arithmetic.

For $q\le Q=5{,}000{,}000$, $(qU-V)/(qV)$ is reduced since $\gcd(U,V)=1$ and $q\nmid df$. The latter uses $q\mid B=d+fp$ and $\gcd(d,f)=1$. Its positive error from $C/D$ is $d^4/(DqV)$. Because $D>2Q\cdot1.055 H^6$, Legendre's criterion applies and every candidate is a convergent with a positive fourth-power remainder. Check such a remainder against the split and the original equations.

For $q>Q$ we have the stronger mass cutoff $2-10^{-20}-1/(Q+1)$. All core primes are then at most 794 and every prime through 167 is required. We also have $0.95<\sigma(d)<1.05$. If $x=\sigma(d)$, the identity gives the interval

$$0<x+1/x-C/D=(1+d^4/(DV))/q<2/(Q+1).$$

We index the eligible core supports by the integer floor of $2^{62} C/D$. For each admissible $d$ we check every matching support in the expanded interval with an exact membership bit test, then reconstruct $q$ as the quotient $(DV+d^4)/(DU-CV)$. Both original derivative identities must still hold. All rounding widens the search. The derivative of $x+1/x$ has absolute value below 1 in the needed interval, so errors from the 11 reciprocal roundings and the two integer floor operations fit the allowance in the code.

## Replaying

```bash
OMP_NUM_THREADS=8 bash jobs/erdos-307-dual61/run.sh 0 1 out
```

The merger requires all shard results and reports an exclusion only with zero remaining integer candidates. An integer hit would require independent primality verification for the large primes.

An independent check covers the whole opposite-side branch without the cutoff at five million. For each bounded odd core $d$ and a known complementary anchor $L$, write $B=LE$ with $E=Vq$, and put $K=F(d)L$ and $J=dL-F(d)F(L)$. The exact equation is $JE-KF(E)=d^2$. When $E<K$, recover $E$ from its residue $d^2J^{-1}$ modulo $K$. Otherwise, $0<J/K-F(V)/V\le (V_0+d^2/K)/K$ for $V\le V_0$. Once $K>4V_0^3$ and $K>d^2$, there is at most one possible fraction in this interval, and it is a continued-fraction convergent. In both cases only the exact derivative equations can admit a candidate. This independent program completed with 9,290,543 admissible odd cores, 24,773,453 reconstructions and zero candidates.

```bash
g++ -O3 -std=c++20 -fopenmp audit/anchor.cpp -lgmpxx -lgmp -o /tmp/erdos307-anchor
OMP_NUM_THREADS=8 /tmp/erdos307-anchor solve 0 1 1190
```
