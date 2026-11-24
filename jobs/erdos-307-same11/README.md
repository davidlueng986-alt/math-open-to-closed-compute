# Erdős #307, 61 primes, split (11,50), same-side placement

The side of size 11 contains 2. Assume exactly two primes exceed 2381 and both
are on that side. The larger prime exceeds 10^20 by the product bound. The
other 59 primes are at most 1190 and include every prime through 157.
The wrapper checks these and the search's fixed rational bounds exactly.

Write A = dpq, B = E, and f = F(d), where F is the numerator of the sum
of reciprocals of the distinct prime factors, expressed over their
product. Then

    F(E) = dpq,   E = f pq + d(p+q).

Thus f F(E) = d E modulo d^2. Enumerate the nine-prime core d with the
reciprocal-sum and product bounds. For each d, enumerate an increasing
prefix H of E with remaining product V. The exact residue satisfies

    F(V) = r V modulo d^2,
    r = d / f - F(H) / H modulo d^2.

The divisions are defined because f and H are coprime to d. The
remaining primes are distinct and coprime to H and d. For exact upper
bounds U on V and W on F(V), if 2 U W < d^2, the reduced fraction

    (r V - F(V)) / (d^2 V)

must be a convergent of r/d^2, by its strict error bound. There is at
most one reduced fraction in the rectangle by the determinant bound.
The code either reconstructs it and tests prime factors and all
constraints or extends H recursively. The test at a complete product
checks d divisibility, the recovered pq and p+q, the discriminant, and
the two integer roots. It reports an integer-root candidate for
independent primality verification. Zero candidates can therefore
exclude this placement. The two large primes have no upper cutoff.

The merger independently enumerates the five-prime prefixes in Python
and requires full disjoint shard coverage. Run a local sample with
`OMP_NUM_THREADS=4 bash run.sh 19 48 out`, or invoke the workflow's
`erdos-307-same11` job.
