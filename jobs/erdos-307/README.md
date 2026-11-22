# Erdős #307 witness search

The job looks for two finite sets of primes whose reciprocal sums multiply to 1. It uses the existing `sharded-run` workflow. The witness is two prime lists and their exact rational sums. The collector verifies those sums again before recording `CLOSED YES`.

## Search

Put \(D=\prod_{p\in U}p\) and \(C=\sum_{p\in U}D/p\) for a candidate union \(U\). For a solution with side products \(A,B\), the reduced fractions force \(F(A)=B\) and \(F(B)=A\), where \(F(n)=\sum_{p\mid n}n/p\) for squarefree \(n\). Hence \(C=A^2+B^2\) and \(C\pm2D=(A\pm B)^2\). The search uses these two squares to recover the only possible products without enumerating the partitions of \(U\).

For a fixed union size \(k\), the reciprocal sum must exceed 2. If dropping a prime from the first \(k+1\) primes leaves a sum smaller than 2, that prime is compulsory. For each compulsory odd prime \(r\), both square conditions reduce modulo \(r\) to \(D/r\) being a quadratic residue. These conditions combine into one XOR signature for the optional primes. The odd part of \(D\) also has a required residue modulo 8. In order of \(k\bmod4=0,1,2,3\) these residues are \(7,5,3,1\). This follows from \(C\equiv5\pmod8\), since \(D\) is even and squarefree and both square roots are odd. Writing \(R=D/2\), one has \(C\equiv R(1+2\sum_{p\mid R}p)\pmod8\), and \(\sum_{p\mid R}p\pmod4\) is determined by \(k-1\) and \(R\pmod4\).

Each shard handles its own strided list of possible maximum primes. Reciprocals are rounded up on a fixed-point grid during pruning. The final three primes come from an index keyed by the required XOR, with increasing indices and an explicit maximum-prime constraint. Surviving supports are checked with GMP integers. A separate Python verifier uses trial division and `Fraction` on a candidate, independent of the square filter and arithmetic-derivative checks.

## Run and interpret results

Use `job=erdos-307`, eight shards, and `timeout_minutes=20` in `sharded-run`. Each search domain in `run.py` also has its own wall-clock budget. A shard records every maximum-prime value it exhausted and every value left pending. To reproduce a shard locally, run `bash jobs/erdos-307/run.sh 0 8 out` with a C++20 compiler, GMP headers, OpenMP and Python 3 installed.

The result file `erdos-307.json` reports the current mathematical status and coverage of each domain. The `witness.json` file is created if exact verification succeeds. A completed domain without a witness excludes just the stated support size and interval of maximum primes.
