# Erdős #307 at (11,50), opposite large primes

This search treats level 61, with 2 on the side of size 11 and exactly one prime greater than 2381 on each side. It uses no upper bound on either large prime.

Let the two products in a putative solution be $dp$ and $eq$, where $d$ and $e$ each contain only bounded primes. Their arithmetic derivatives obey $F(dp)=eq$ and $F(eq)=dp$. The total reciprocal mass is at least 2. Since the first 58 primes have mass less than $2-3/2382$, at most two primes exceed 2381. The 50-prime product is greater than $3\cdot 10^{20}\cdot2381^{10}$, and the mass of the 11-prime side is less than 3. Consequently $p>10^{20}$. The 59-prime bounded union has mass greater than $2-1/2382-10^{-20}$, all its primes are at most 1190, and it contains every prime through 157. The runner checks these numerical bounds using exact fractions.

## Compulsory-prime reconstruction

Let $L$ be the product of the primes through 157 omitted by $d$, and write $e=LV$. Put $f=F(d)$, $K=fL$, and $J=dL-fF(L)$. Eliminating $p$ yields

$$ (JV-KF(V))q=KV+d^2. $$

For a solution, $\gcd(J,K)=1$. Indeed $\gcd(F(d),d)=1$, $\gcd(F(L),L)=1$, and $\gcd(f,L)=1$ because $eq=d+fp$ and $d$ is disjoint from $L$.

If $E=Vq<K$, then $E$ is the least residue $d^2J^{-1}$ modulo $K$. It is odd, and the bounded part $V$ is its gcd with the product of the primes above 157 up to 1190. For $c$ primes of $d$ at most 157, $V$ has exactly $12+c$ prime factors. The product of the smallest $12+c$ eligible primes is a necessary lower bound. The companion rank bounds give an upper bound $U_c$.

If $Vq\ge K$, then $q\ge K/U_c>20{,}000{,}000$. The last inequality holds for all $c$ from 0 to 10. It uses $K=(f/d)\cdot dL$ and the smallest possible product of the $10-c$ additional primes of $d$. The bounded union now contains every prime through 167 and has all its primes at most 794. It has a finite catalogue.

Writing $M=de$, $T=F(M)$, and $x=f/d$ gives
$$
q\left(x+1/x-T/M\right)=1+d^2/(ef)<2.
$$
For the $c$-th class, $K$ has a certified lower bound $K_c$, so $T/M$ is in $(x+1/x-2U_c/K_c,x+1/x)$. The search matches this interval in the catalogue, requires that the union contain $d$, and tests the exact forced value
$$
q=\frac{Mdf+d^4}{M(d^2+f^2)-Tdf}.
$$
All reciprocal rounding widens the intervals. The derivative of $x+1/x$ has absolute value less than 1 over the full input interval, so the rounding of $x$ is covered by the stated integer slack.

The search decomposes the even core by its five smallest primes, including 2. The merger independently counts the prefixes and requires every assigned prefix to complete. Integer candidates, if any, require independent primality verification to settle the original problem.


