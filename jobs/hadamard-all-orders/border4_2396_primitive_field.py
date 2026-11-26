"""Check primitive cyclotomic factors and the residuals of the joint source."""

from math import gcd, isqrt

from border4_2396 import periodic
from border4_2396_joint_q13_mod16 import joint_words

FACTORS = {
    7: (
        "113355010250306254165064551334236451503360614102512626645535412663211"
        "5665452343134455513004646516251636250161504366624344205530304651"
    ),
    11: (
        "1988467233a5a9708969a1690866343300338a2945a93a207316a18486566751a1091"
        "a4646a875049a0131283462760194833405413792945308016a4509933225511"
    ),
}
N = 299


def product(a, b, prime):
    c = [0] * (len(a) + len(b) - 1)
    for i, u in enumerate(a):
        for j, v in enumerate(b):
            c[i+j] += u*v
    return tuple(v % prime for v in c)


def remainder(poly, divisor, prime):
    assert divisor[-1] == 1 and len(poly) >= len(divisor)
    values = [v % prime for v in poly]
    for i in range(len(values)-1, len(divisor)-2, -1):
        u = values[i]
        if u:
            start = i-len(divisor)+1
            for j, v in enumerate(divisor):
                values[start+j] = (values[start+j]-u*v) % prime
    return tuple(values[:len(divisor)-1])


def binomial(degree):
    return (-1,) + (0,)*(degree-1) + (1,)


def order(a, m):
    x = a % m
    k = 1
    while x != 1:
        x = x*a % m
        k += 1
    return k


def primitive_factor(prime):
    first = tuple(int(d, 16) for d in FACTORS[prime])
    assert len(first) == 133 and first[-1] == first[0] == 1
    second = first[::-1]
    assert first != second and all(0 <= v < prime for v in first)
    assert order(prime, 13) == 12 and order(prime, 23) == 22
    assert order(prime, N) == 132
    assert all(pow(prime, i, N) != N-1 for i in range(132))
    phi = product(first, second, prime)
    assert product(phi, product(binomial(13), binomial(23), prime), prime) == (
        product(binomial(N), binomial(1), prime)
    )
    return first


def quotient(poly, modulus):
    return tuple(sum(poly[i::modulus]) for i in range(modulus))


def normalize(words):
    values = periodic(words)
    assert values[0] == 597 and all((v+2) % 8 == 0 for v in values[1:])
    return (0,) + tuple((v+2)//8 for v in values[1:])


def evaluate(poly, x, prime):
    value = 0
    for a in reversed(poly):
        value = (x*value+a) % prime
    return value


def check_split_field(words, residual):
    prime = 599
    assert (prime-1)//2 == N and gcd(N, prime-2) == 1
    assert all(prime % d for d in range(2, isqrt(prime)+1))
    root = next(a for a in range(2, prime) if pow(a, N, prime) == 1
                and pow(a, 13, prime) != 1 and pow(a, 23, prime) != 1)
    matches = []
    for d in range(1, N//2+1):
        x = pow(root, d, prime)
        inverse = pow(x, -1, prime)
        norm = sum(evaluate(w, x, prime)*evaluate(w, inverse, prime)
                   for w in words) % prime
        assert norm == 8*evaluate(residual, x, prime) % prime
        if norm == 0:
            matches.append(d)
    assert set(range(23, 150, 23)) <= set(matches)
    print("599 split-field exact inverse pairs", len(matches), "of 149")


def main():
    words = joint_words()
    residual = normalize(words)
    assert quotient(residual, 13) == (0,)*13
    assert max(map(abs, residual)) == 5
    assert sum(v*v for v in residual) == 1080
    q23 = quotient(residual, 23)
    assert 64*sum(v*v for v in q23) == 41088

    pure = [0]*23
    pure[1] = pure[-1] = 1
    pure[2] = pure[-2] = -1
    repeated = tuple(pure[d % 23] for d in range(N))
    assert quotient(repeated, 13) == (0,)*13
    assert quotient(repeated, 23) == tuple(13*v for v in pure)

    for prime in FACTORS:
        factor = primitive_factor(prime)
        assert not any(remainder(repeated, factor, prime))
        normalized = remainder(residual, factor, prime)
        assert any(normalized)
        norm = [0]*132
        for word in words:
            a = remainder(word, factor, prime)
            b = remainder((word[0], *word[:0:-1]), factor, prime)
            for j, v in enumerate(remainder(product(a, b, prime), factor, prime)):
                norm[j] += v
        norm[0] -= 599
        assert tuple(v % prime for v in norm) == tuple(8*v % prime for v in normalized)
        print(prime, "verified primitive factor, nonzero norm residual coefficients",
              sum(v != 0 for v in normalized))
    assert 7*11 > (597+2)//8
    check_split_field(words, residual)


if __name__ == "__main__":
    main()
