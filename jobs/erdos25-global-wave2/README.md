# Exact finite probes of two global Erdős 25 targets

These probes keep the original singleton and activation rules. They seek
structures relevant to two open global estimates; they do not decide the
infinite problem and do not prove finite optimality.

For a chosen period `L`, admissible moduli are its divisors `2 <= q <= X <= L`.
Each modulus is absent or carries exactly one normalized residue. The full
first-kill cells are evaluated by integer counting over the entire period.
The actual first-kill harmonic masses use only integers `n >= q`.

Writing `e_i` for the full first-kill measures, `h_i` for their activated
harmonic masses up to `X`, `H_X=sum(1/n,n<=X)`, `c_i=h_i/H_X`, and
`beta=sum e_i`, the two objectives are:

- `entropy`: `K = sum c_i log_+(c_i/e_i)`;
- `energy`: `R = (sum h_i-beta H_X)_+^2 /
  (H_X (1+sum e_i log q_i))`.

A uniform absolute bound on either quantity would settle the original
problem positively, by the reductions recorded in the primary research notes.
A finite numerical value cannot settle or refute the existence of such a
constant. The squarefree divisor models exclude the long binary residue
channels in the known bounded-energy construction; that is a substantial
limitation, not evidence against that construction or other asymptotic ones.

## Implementation and independent check

`search.cpp` uses simulated annealing with omissions, residue moves and
restarts. It maintains the least covering modulus on each residue of `L`.
It rebuilds that ownership array from scratch every 500 iterations and checks
equality. Zero active-hit counts are stored as integers to avoid treating
floating-point cancellation as a nonempty cell.

`verify.py` does not use the incremental ownership algorithm. It enumerates
the full periodic union and the actually activated integer union separately.
It verifies all Haar cell counts exactly and recomputes the harmonic values,
energy and entropy with 60-digit decimal arithmetic. Transcendental diagnostic
values are numerical; no rigorous transcendental interval or theorem
certificate is claimed.

`seed.py` makes the squarefree digit-forcing example proposed and independently
checked by the quotient agent. It leaves the old survivor `390 mod 2310`, then
adds `(q,a)=(390,0)`, making the final full cell have measure `1/30030` while
its actual first kill at `X=390` contributes `1/390`.

The workflow runs four models and both objectives, at most four runners
concurrently, with a 90-second search budget per model. There are no external
Python dependencies. Logs record source hashes and the compiler version.
Wall-clock stopping is used only to cap resources; replay the recorded
iteration count with a larger time limit to repeat a candidate search under
the recorded compiler/runtime. The independent candidate verifier is
deterministic regardless of the search trajectory.

Example local replay:

```sh
g++ -O3 -std=c++17 -Wall -Wextra -Werror search.cpp -o search
python seed.py seed.tsv
./search 30030 390 2501 90 entropy candidate.json 100000000 seed.tsv
python verify.py candidate.json verified.json
```

## Sources and status

The exact targets, their sufficiency, and the known obstructions are credited
to Plasma AI's pinned [spectral-sieve note](https://github.com/plasma-ai/erdos/blob/6ca84eeb1eb98dcb7012e2a628982cfc0b3b809d/wiki/research/erdos_25/spectral_sieve.md)
and [rank and moment note](https://github.com/plasma-ai/erdos/blob/6ca84eeb1eb98dcb7012e2a628982cfc0b3b809d/wiki/research/erdos_25/rank_and_moment_obstructions.md).
The normalized disjoint entropy must not be confused with the already-refuted
unnormalized entropy/linear-energy charge.

**Original Erdős #25 status: OPEN.** Search success means only that a finite
candidate passed the separate verifier. A zero or small best energy ratio is
not a lower bound on the true optimum and is not affirmative proof evidence.
