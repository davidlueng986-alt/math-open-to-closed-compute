# Three surviving three-negative comparators at length 599

Consider a half-flip Goethals–Seidel source of length 599 from \((s,s\tau,sq,sq\tau)\), where \(\tau=+1\) on indices \(0,\ldots,299\) and \(-1\) on indices \(300,\ldots,598\). Assume \(q\) has one negative entry in the first half and two in the second. The necessary correlation congruences reduce all such comparators, up to reflecting the first half, to 149 symmetric placements. Three survive the exact tests below. Survival leaves a system of quadratic equations and does not establish a 64-modular source.

## Positions of the three negative entries

Write \(C_d\) for one quarter of the combined cyclic correlation of the four sequences. It is the sum of \(s_i s_{i+d}\) over pairs with the same \(\tau\) and \(q\) signs. Let \(M_d\) be the number of these pairs. The 64-modular condition requires \(C_d\equiv0\pmod{16}\), so \(M_d\) is even. For \(1\le d\le299\), pairs within a half are ordinary distance-\(d\) pairs, with total \(599-2d\) before considering \(q\). Removing pairs of different \(q\) signs changes the parity by the sum of the distance-\(d\) degrees at the three negative positions, because an edge between two negative entries is counted twice.

The degree at position \(j\) within a half of length \(L\) is \([d\le j]+[d\le L-1-j]\). Thus the sum of the six endpoint-distance indicators must be odd for every \(1\le d\le299\). At \(d=299\) this forces the negative position in the first half to be an endpoint. Its two distances are 0 and 299, so the four remaining endpoint distances must have even multiplicities, by subtracting the indicator sums at consecutive \(d\). The two distinct negative positions in the second half must therefore be a reflection pair. Reflecting the first half preserves all \(C_d\) and allows its singleton to be put at 299.

Write \(h\in\{0,\ldots,148\}\) for the smaller local index of the pair in the second half, with local indexing beginning at 0. The negative indices in \(q\) are \(299,300+h,598-h\). The four sign classes give a full sequence \(A\) of length 299, a singleton, a sequence \(B\) with holes at \(h,298-h\), and a sequence \(C\) supported on those two holes. The singleton contributes no off-diagonal correlations. The other three supports are symmetric under \(j\mapsto298-j\), and \(C_d\) for \(1\le d\le298\) is the sum of their ordinary autocorrelations, using zero at a hole. All longer lags follow by symmetry or vanish.

## Exact tests at the next three moduli

Write \(C_d=M_d-2N_d\), where \(N_d\) counts opposite signs among the eligible pairs. For the first test \(C_d\equiv0\pmod4\), the condition is \(N_d\equiv M_d/2\pmod2\). The parity of \(N_d\) is linear in the sign bits, with coefficient equal to the distance-\(d\) degree at each position. A position and its reflection have equal degrees. Each midpoint has even degree. The unknowns therefore record only the sign difference in each of the 298 reflection pairs of \(A,B,C\). Seventeen comparators give inconsistent systems. Every other system has rank 298, so the reflection differences are uniquely forced.

Choose representative signs with these differences. Any other choice is obtained by flipping whole reflection orbits, including singleton midpoints. A reflection-fixed edge cannot change its product. Two distinct reflected edges either cancel, or contribute \(2\epsilon\) with a common product \(\epsilon\in\{\pm1\}\). In the latter case a flip changes their combined contribution by \(-4\epsilon\ell\), where \(\ell\) is the parity of the endpoint flips. Therefore \(C_d\equiv0\pmod8\) is a second linear system in the orbit flips. Sixteen more comparators fail this test. Fixing one representative sign in each of \(A,B,C\) removes three global sign choices without affecting any correlation.

On the affine solution space that remains, \(C_d/8\bmod2\) is a quadratic function of the free bits. In fact, measured from a particular solution, the change in \(C_d/4\) is a signed sum of linear parities \(\ell_e\) and is even on the affine solution space. For an even sum,
\[
 \frac{\sum_e\epsilon_e\ell_e}{2}
 \equiv \sum_{e<f}\ell_e\ell_f+\sum_{\epsilon_e=-1}\ell_e\pmod2 .
\]
The constant, linear and quadratic coefficients can therefore be recovered by evaluating the autocorrelations at zero, one and two free bits. For a necessary test, allow the degree-two monomials to take independent values. This yields a linear system that every actual 64-modular source must satisfy. Another 110 comparators fail even this relaxation.

| Hole index \(h\) | Free orbit bits after the modulo-32 test and global sign normalization |
|---:|---:|
| 0 | 149 |
| 1 | 51 |
| 2 | 32 |
| 37 | 38 |
| 74 | 75 |
| 99 | 51 |

## Three exact Boolean contradictions

The table lists the six comparators that survive linearization. For \(h=2\), taking linear consequences of the quadratic equations and substituting the resulting pivot variables reduces the dimension successively to \(30,28,27,26,24\). The resulting equation span contains the constant polynomial 1, which contradicts the requirement that every equation vanish.

For \(h=37\), work in the Boolean polynomial ring over \(\mathbb F_2\), with \(x_i^2=x_i\). Multiply the quadratic equations by the individual variables and add the resulting degree-at-most-three equations to the original span. Gaussian elimination produces the constant polynomial 1 after adding the multipliers for the first 33 of the 38 variables. This is an exact contradiction because every polynomial so added vanishes at a common solution of the original equations.

For \(h=99\), a first cubic pass gives one linear equation. Substitute its pivot to reduce from 51 to 50 free bits in the quadratic equations. A second cubic pass gives the constant polynomial 1 after adding the multipliers for the first 33 of the 50 variables.

The [stdlib verifier](defect12_t599_comparators.py) reconstructs the systems for all 149 cases and checks the three Boolean contradictions. The remaining indices are \(0,1,74\). The \(h=0\) comparator is the one used in [NEAR64_599.md](NEAR64_599.md). Solving the product relations for any surviving index, and finding an exact tetrad and panel for any positive source, remain open in this calculation.
