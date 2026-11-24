# Changing the 399-point compression

A length-1197 cyclic Legendre pair would construct a Hadamard matrix of order 2396. The earlier sign words solve every original shift in the subgroups of orders 57 and 63. Their 399-point compression fails at shift 1 with a combined periodic autocorrelation of 42, against the required −6. This search changes the sums of the triples of signs above the 399 residues. Every candidate remains an actual pair of binary sign words with the same exact 57-, 63- and 133-point margins and multiplier 463. [Previous certificate](../hadamard-2396-diagonal/README.md)

For $T_j=\sum_{i\equiv j\pmod{399}} A_i$ and the corresponding second word $U$, write $C(t)=P_T(t)+P_U(t)$. The quotient score is $(C(0)-2390)^2+\sum_{t=1}^{199}(C(t)+6)^2$. The full score is $\sum_{s=1}^{598}(P_A(s)+P_B(s)+2)^2$. Both scores use integer arithmetic. The checker recomputes each quotient entry from its three original shifts, and evaluates every original shift with packed bits and ordinary sign multiplication. [Independent checker](audit.py)

The prescribed original shifts comprise the previous 58 subgroup pairs and all nine additional pairs above the 399-point residue 1 and its images under reflection and multiplication by 463. All 67 equations must equal −2 on the same words. The selected quotient equations are necessary for this to hold. A balanced rectangle changes eight orbit cells in one word while preserving the prescribed smaller margins. The quotient search computes the exact autocorrelation change as a linear term plus pair interactions. It can join moves in separate words by a 64-bit fingerprint and checks every accepted match against all selected integer equations. The phase search holds all 399 margins fixed, then repairs the original shifts. A separate search minimizes the full original score. Its balanced mode keeps original shift 399 exact. [Quotient search](search.cpp) · [Phase repair](phases.cpp) · [Full original search](raw.cpp)

Run from this directory using Python 3.10 or newer and a C++17 compiler.

```sh
python3 audit.py
bash run.sh 0 12 /tmp/hadamard-399-shard
python3 audit.py /tmp/hadamard-399-shard/result.json
```

The sharded workflow runs seven seeds per shard and archives the full sign words for the best quotient, full, balanced and 67-pair candidates. The merge rechecks each shard's four winners directly from both sign words. [Shard driver](shard.py) · [Merger](merge.py)
