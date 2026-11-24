# Lifting the surviving seven-entry supports

Consider the cyclic order-1197 Legendre construction with independent multiplication by the nonzero squares modulo 19. The necessary seven-heavy-entry theorem and the finite quotient tests leave 8,521 oriented cases covering 3,763 sparse templates. Each case still admits many choices for the signs. This job starts a full-length search in each oriented case. Independent starts also polish the two previous lowest-error witnesses, on either group law. [Seven-entry theorem and finite enumeration](../hadamard-2396-399/symmetry/README.md) · [Fixed inputs for polishing](../hadamard-2396-abelian/records.json)

For each of the two words use $X=a+18M$, $F=a-M$, and $D$ on the light positions, with the notation of the theorem. Define the following three functions on $C_{63}$, summing over both words.

$$
\begin{aligned}
r(t)&=\sum_f P_{X_f}(t)-2396\,\mathbf1_{t=0}+38,\\
u(t)&=\sum_f[P_{F_f}(t)+19P_{D_f}(t)]-2396\,\mathbf1_{t=0},\\
s(t)&=\sum_{f,x}[F_f(x)D_f(x+t)-D_f(x)F_f(x+t)].
\end{aligned}
$$

The unnormalized Fourier transform of the original error in the vertical coordinate is $r(t)$ at the trivial character and $u(t)\pm i\sqrt{19}s(t)$ at the two nontrivial character classes of size nine. Plancherel and reflection give the **exact original squared error**
$$
E=\frac{1}{38}\sum_{t=0}^{62}\left[r(t)^2+18u(t)^2+342s(t)^2\right].
$$
This formula includes every original shift. The implementation also scores the 63-point quotient by $\sum_t r(t)^2$, with the zero shift counted once. It allows swaps within the singleton signs and within the light-position signs. Both word sums and the required length-19 projected norm stay exact. The signed support is fixed during each search. The seven-entry condition fixes the positions and orientations of $M$ and the diagonal 63-point equation additionally requires $\sum aM=-1$. The latter is tested by the $t=0$ term in the objective. [C++ search and updates](search.cpp)

Each oriented template gets a quotient warm-up followed by a search minimizing full error. Within each shard, the six best words for each objective are refined. Their masks are checked against the template, exact 63-point sums and original correlations. The optimized Fourier score is checked by bit rotations after every individual search. The final merger additionally evaluates all 598 original correlations by direct integer multiplication. A nonzero score records the finite search outcome. [Schedules](scan.py) · [Independent check and merger](merge.py)

~~~sh
bash jobs/hadamard-2396-squares/run.sh 0 16 /tmp/hadamard-squares/shard-0
mkdir -p /tmp/hadamard-squares-summary
python3 jobs/hadamard-2396-squares/merge.py /tmp/hadamard-squares /tmp/hadamard-squares-summary
~~~

All 8,521 oriented cyclic templates received a search. The best full-energy lift within these fixed supports has $E=41,088$, with 210 exact original pairs. The best 63-point objective is 7,424 across all quotient shifts, or 3,712 when counted using one representative per reflected pair and the zero shift. Its quotient zero-shift error is zero. Separate polishing of the earlier full-energy endpoints attained 29,568 on the cyclic group and 33,312 on the elementary-3 group. The cyclic minimum solves original shift 1 and fails shift 399 with value 26. [Full masks](lifts.json) · [All 16 shards](https://github.com/davidlueng986-alt/math-open-to-closed-compute/actions/runs/45468476344) · [Archived results](https://github.com/davidlueng986-alt/math-open-to-closed-compute/blob/e1a4210e952a4474057b8841967276cb21c1a07d/runs/hadamard-2396-squares/45468476344/results.json)
