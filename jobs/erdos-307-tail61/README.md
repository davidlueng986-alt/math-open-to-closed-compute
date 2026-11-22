# Erdős #307 at 61 primes with one large prime

This job tests four splits of the 61 primes into the two sides of [Erdős #307](https://www.erdosproblems.com/307). Exactly one prime is greater than 2381. The splits, with the side containing 2 first, are (11, 50), (13, 48), (49, 12), and (47, 14).

## Reduction

For squarefree $n$, write $F(n)=\sum_{r\mid n}n/r$, summing over primes $r$. The two prime sets in a solution are disjoint, since the reciprocal sum on each side has denominator equal to that side's prime product in lowest terms. Their products $A,B$ satisfy $F(A)=B,\ F(B)=A$. The union's reciprocal sum is $F(A)/A+A/F(A)$. With 61 primes this sum is at most the sum of the reciprocals of the first 61 primes, so both sides' reciprocal sums are in $(0.907,1.103)$.

For the four splits the large prime $p$ lies on the smaller side. The smallest possible product on the larger side exceeds $1.103\cdot 2381^j\cdot 10^{30}$, where $j$ is the smaller side's size. Hence $p>10^{30}$. Put $A=dp$, $D=dB$, $C=F(D)$, and $x=F(d)/d$. The 60-prime core $D$ has reciprocal sum $C/D>2-10^{-30}$, and $x>0.906$.

If the core primes are $r_1<\cdots<r_{60}$ and $T_i$ is the sum of the first $i$ prime reciprocals, then $r_i\le (61-i)/(2-10^{-30}-T_{i-1})$ when the denominator is positive. Thus the $i$-th largest prime of $d$ has the upper bound on the $i$-th largest prime of the core. Taking reciprocals gives lower bounds for the ordered coordinates of $x$. The first primes of the appropriate parity give upper bounds. At a given sum, the vector obtained by filling the first coordinate to its upper bound, then the second, and so on, maximizes every initial partial sum. The concavity of the logarithm then gives a lower bound on the reciprocal product. Using the minimum sum $0.906$ and exact rational arithmetic gives the integer upper bound $H=609560875805190030554252117$ for $d$ across these four cases.

The product rule gives $B=d+pF(d)$ and $C=BF(d)+d^2p$. Eliminating $p$ gives

$$x^2-(C/D)x+1=d^2/D.$$

If $C>2D$, put $\Delta=C^2-4D^2$ and $\alpha_\pm=(C\pm\sqrt\Delta)/(2D)$. Let $m/q$ be the reduced fraction $\max(x,1/x)$, so $q\le d\le H$. If $x>1$, then $x\ge\alpha_+$ and $x-\alpha_+\le d^2/\sqrt\Delta$. If $x<1$, then $x\le\alpha_-$ and $\alpha_--x\le d^2/\sqrt\Delta$. Applying $\alpha_+\alpha_-=1$ and $x>0.906$ in the second case gives $q|m/q-\alpha_+|\le 2H^3/\sqrt\Delta$ in both cases.

For $M=2D$, $t=\lfloor\sqrt\Delta\rfloor$, and $N=C+t$, the rational $N/M$ differs from $\alpha_+$ by less than $1/M$. Consequently the target satisfies $|Nq-Mm|\le E$, where $E=\lceil 2MH^3/t\rceil+H$. When $2HE<M$, Legendre's continued-fraction criterion makes $m/q$ a convergent of $N/M$. The determinant of two distinct reduced fractions with denominators at most $H$ shows that at most one can satisfy this error bound. The code uses the Euclidean remainders to find it and checks both orientations of the fraction. This reconstruction applies at arbitrary support sizes whenever its bounds hold. Its discriminant test scales with the fourth power of $H$ in $t$. The earlier reconstruction of $x+1/x$ from $C/D$ required a bound that grew with the sixth power of $H$.

## Exact search

Every core contains all primes through 103 by $T_{61}-1/103<2-10^{-30}$. The sum of the upward-rounded weights $\lceil 2^{62}/r\rceil$ is at least $2^{63}$ in any solution core. This integer bound prunes core enumeration. Each shard has a disjoint list of possible maximum primes of the core.

Before continued fractions, the engine checks the known Jacobi obstruction. In a solution, $A+B$ satisfies $(A+B)^2=(C+2D)p+D$, so $(D\mid C+2D)=1$. Write $D=2R$, and let $a$ count the primes of $R$ congruent to 3 modulo 4. Since $R$ has 59 primes, $C\equiv R(7-4a)\pmod 8$. Quadratic reciprocity and $C\equiv D/r\pmod r$ for primes $r\mid R$ give $(D\mid C+2D)=(-1)^{[a\ \mathrm{even}]+\binom{a}{2}}$. Thus $a\equiv 1,2\pmod 4$ is required. See Bonfioli's [computational treatment](https://github.com/ElVec1o/erdos307/blob/36c3b7979a77e003fcf47016e41f2f7133495415/paper/erdos307-computational.tex) for the general Jacobi filter.

A core outside the continued-fraction bound counts as uncovered unless its mass or Jacobi sign already excludes it. A recovered core must have $d\mid D$, the required size and parity, and both exact original derivative identities. Any remaining candidate is printed for rigorous verification of the large prime. The summary reports an exclusion only after complete shard coverage, zero uncovered cores and zero candidates.

```bash
OMP_NUM_THREADS=8 bash jobs/erdos-307-tail61/run.sh 0 1 out
```
