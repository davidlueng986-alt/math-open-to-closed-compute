# ABC Wave 1 Agent 5: exact squaring-orbit audit

Run `bash run.sh 0 1 OUTDIR` in the Sage 10.6 toolbox. Sage factors and checks primes with `proof=True`. A local SymPy fallback is allowed only for the same explicitly bounded (<2^64) factorization inputs. `setup.sh` installs SymPy only outside Sage.

The job enumerates every positive primitive opposite-parity seed with `a<=b` and odd `c=a+b<=41`, plus the classical triple `(2,3^10*109,23^5)`. It checks seven orbit states per seed with exact integers. Complete factorization and radical claims stop as soon as a new difference reaches 2^64; all larger states retain only algebraic and gcd checks. No partial factorization is silently treated as complete.

Certificates include exact squaring and product identities, pairwise coprimality of new difference factors, radical recurrence, repeated-prime defect, finite-field orders forcing `p=±1 mod 2^(j+2)`, and quality thresholds checked by integer powers. Floating logarithms are display only.

This verifies the bounded certificates supporting the mathematical report. The proof that the zero-epsilon strengthening fails is an infinite algebraic argument in the report. The Baker-Wüstholz import used to isolate the residual prime-power problem is not re-proved or kernel-verified by this script. ABC remains open.
