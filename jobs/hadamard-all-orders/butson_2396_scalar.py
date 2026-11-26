"""Check the scalar dimensions and a small quaternary-to-real reconstruction."""

from math import comb, gcd, isqrt

from border4_2396 import pack
from verify import verify_orthogonal


def admissible_phase_counts(dimension):
    # phi(k) dividing 4 requires k to divide 2**3*3*5.
    return tuple(k for k in range(1, 121) if 120 % k == 0
                 and dimension % sum(gcd(j, k) == 1 for j in range(k)) == 0)


def check_dimensions():
    prime = 599
    assert all(prime % d for d in range(2, isqrt(prime) + 1))
    assert 2_396 == 4*prime
    assert admissible_phase_counts(4) == (1, 2, 3, 4, 5, 6, 8, 10, 12)
    assert admissible_phase_counts(2) == (1, 2, 3, 4, 6)
    assert all(prime % k == k-1 for k in (6, 10, 12))
    assert prime % 4 == 3 and (2*prime-1) == 3**2*7*19
    assert all((a*a + b*b) % prime != 0 or a == b == 0
               for a in range(prime) for b in range(prime))
    assert (prime-1) == 2*13*23
    for h in (13, 23):
        assert gcd(384, h) == 1
        assert all(v*v % (h*h) != prime % (h*h) for v in range(isqrt(prime) + 1)
                   if v % h in (1, h-1))
    assert isqrt((prime-1)//2)**2 != (prime-1)//2


def quaternary_control():
    q = 13
    n = q+1
    squares = {i*i % q for i in range(1, q)}
    source = []
    for i in range(n):
        row = []
        for j in range(n):
            if j == i:
                row.append((0, -1))
            else:
                value = 1 if i == q or j == q or (j-i) % q in squares else -1
                row.append((value, 0))
        source.append(row)
    for i, x in enumerate(source):
        for j, y in enumerate(source):
            assert sum(a*c+b*d for (a, b), (c, d) in zip(x, y, strict=True)) == (n if i == j else 0)
            assert sum(b*c-a*d for (a, b), (c, d) in zip(x, y, strict=True)) == 0
    real = []
    for row in source:
        real.append(tuple(value for a, b in row for value in (a-b, a+b)))
        real.append(tuple(value for a, b in row for value in (a+b, b-a)))
    assert verify_orthogonal(2*n, list(map(pack, real))) == comb(28, 2) == 378
    for i, row in enumerate(source):
        for j, (a, b) in enumerate(row):
            c, d = real[2*i][2*j:2*j+2]
            assert real[2*i+1][2*j:2*j+2] == (d, -c)
            assert (c+d, d-c) == (2*a, 2*b)
    print("BH(14,4) to H(28): all 378 inner products and 196 reverse blocks verified")


if __name__ == "__main__":
    check_dimensions()
    quaternary_control()
