"""Check the arithmetic for the semiprime T–Paley residual slice."""

from math import gcd, isqrt

p, step = 17_380_351_759, 20_224_424_220
t0, L = 20_018_009, 24_342_780
assert L % 11 == t0 % 11 == 0
assert step == (L//11)*13*19*37 and gcd(p, step) == 1
assert all(p % d for d in range(2, isqrt(p) + 1))
assert (p % (L//11), p % 13, p % 19, p % 37) == (1_819_819, 4, 14, 27)
assert (p % 3, p % 5) == (1, 4)
assert step % (3*5) == 0 and p > 799
t = 11*p
assert t == 191_183_869_349 and t % L == t0 and 11*step % L == 0
assert (t % 13, t % 19, t % 37) == (5, 2, 1)
assert (4*t - 1) % (5*479) == (4*p - 1) % (3*5) == 0
assert 4*t//p - 1 == 43 and 4*t//(11*p) - 1 == 3
assert (16*t + 1) % 37 == 17 and all(x*x%37 != 17 for x in range(37))
print("semiprime T-Paley slice: first t=191183869349, only width p or 11p survives the q conditions")

refinement = 23**2
refined_prime = 5_963_361_072_439
refined_step = step*refinement
assert gcd(step, refinement) == 1 and refined_step == 10_698_720_412_380
assert refined_prime % step == p and gcd(refined_prime, refined_step) == 1
assert refined_prime % refinement == 435
assert all(refined_prime % d for d in range(2, isqrt(refined_prime) + 1))
assert refined_prime % 4 == 3 and refined_step % 4 == 0
assert (11*refined_prime - 1) % refinement == 23
assert all((a*a + b*b) % 23 != 0 or (a, b) == (0, 0)
           for a in range(23) for b in range(23))
print("refined semiprime slice: arbitrary binary Golay seeds fail at every bounded base width")

remaining_prime = 261_129_632_466_031_099
remaining_step = refined_step*31**2*41
assert remaining_step == 421_540_282_968_184_380
assert remaining_prime % refined_step == refined_prime and gcd(remaining_prime, remaining_step) == 1
assert remaining_prime % 31**2 == 16 and remaining_prime % 41 == 21
assert (2*remaining_prime - 1) % 31**2 == 31 and (2*remaining_prime - 1) % 41 == 0
print("further semiprime slice: 31 exactly divides 2p-1, excluding the 2p conference template")
