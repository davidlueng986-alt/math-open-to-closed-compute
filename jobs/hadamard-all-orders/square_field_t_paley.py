"""Replay square-field C-partitions, an exact H(180), and the prime progression."""

from itertools import product
from math import comb, gcd, isqrt, lcm, prod

from border4_2396 import pack
from paley_progression import small_paley_blocks
from verify import verify_orthogonal

FIELD = 83
BASE = 261_129_632_466_031_099
PERIOD = 421_540_282_968_184_380
EXCLUDED_DIVISORS = (17, 43, 47, 67, 73, 127, 631)
OUTER_PRIME = 215_970_540_982_539_780_403


def prime_divisors(value):
    divisors = set()
    for divisor in range(2, isqrt(value) + 1):
        while value % divisor == 0:
            divisors.add(divisor)
            value //= divisor
        if value == 1:
            break
    if value > 1:
        divisors.add(value)
    return divisors


def finite_field(p):
    """Return powers of a generator in F_p[i], using x + i y ↔ (x,y)."""
    assert p % 8 == 3 and prime_divisors(p) == {p}
    order = p*p - 1

    def mul(left, right):
        a, b = left
        c, d = right
        return (a*c - b*d) % p, (a*d + b*c) % p

    def power(value, exponent):
        result = (1, 0)
        while exponent:
            if exponent & 1:
                result = mul(result, value)
            value = mul(value, value)
            exponent >>= 1
        return result

    divisors = tuple(prime_divisors(order))
    gen = next((a, b) for a, b in product(range(p), repeat=2) if (a or b)
               and all(power((a, b), order//r) != (1, 0) for r in divisors))
    values = [(1, 0)]
    for _ in range(1, order):
        values.append(mul(values[-1], gen))
    assert len(set(values)) == order and mul(values[-1], gen) == (1, 0)
    return values


def t_selectors(p):
    """The four SDS in (36) from Xia–Xia–Seberry–Zuo, using ordinary classes."""
    powers = finite_field(p)
    m = (p - 3)//8
    half = p + 1
    narrow = 2*half
    a = tuple(tuple(range(i, narrow, 8)) for i in range(8))
    picked = tuple(group[:m] for group in a[:4])
    rest = tuple(group[m:] for group in a[:4])

    def pair_halves(group):
        return set(group) | {(x + half) % narrow for x in group}

    def whole_classes(*indices):
        return {position for index in indices for position in a[index]}

    d0 = pair_halves(picked[3]) | whole_classes(0, 1, 2)
    d2 = pair_halves(picked[1]) | whole_classes(2, 3, 4)
    d1 = pair_halves(picked[0] + rest[1] + picked[2]) | whole_classes(3)
    d3 = pair_halves(rest[0] + picked[2] + picked[3]) | whole_classes(5)
    classes = (d0, d1, d2, d3)
    assert all(len(group) == p for group in classes)

    selectors = [0]*(p*p)
    # At zero all four SDS sign words are +1, giving selector +1.
    selectors[0] = 1
    for exponent, (x, y) in enumerate(powers):
        signs = tuple(1 if exponent % narrow not in group else -1 for group in classes)
        assert signs.count(-1) % 2 == 0
        active = []
        for i in range(4):
            value = sum((-1)**((i & j).bit_count())*sign for j, sign in enumerate(signs))
            assert value in (-4, 0, 4)
            if value:
                active.append((i + 1)*(value//4))
        assert len(active) == 1
        selectors[x*p + y] = active[0]
    assert all(1 <= abs(value) <= 4 for value in selectors)
    return tuple(selectors)


def verify_periodic(p, selectors):
    """Lift each mask to a 2 by 2 tile; shifts reduce to exact integer bitcounts."""
    row_stride = 2*p
    vertical = p*row_stride
    masks = []
    for label in range(1, 5):
        plus = sum(1 << ((index//p)*row_stride + index%p)
                   for index, value in enumerate(selectors) if value == label)
        minus = sum(1 << ((index//p)*row_stride + index%p)
                    for index, value in enumerate(selectors) if value == -label)
        wide_plus, wide_minus = plus | (plus << p), minus | (minus << p)
        masks.append((plus, minus, wide_plus | (wide_plus << vertical),
                      wide_minus | (wide_minus << vertical)))
    for x, y in product(range(p), repeat=2):
        shift = x*row_stride + y
        total = 0
        for plus, minus, wide_plus, wide_minus in masks:
            shifted_plus, shifted_minus = wide_plus >> shift, wide_minus >> shift
            total += (plus & shifted_plus).bit_count() + (minus & shifted_minus).bit_count()
            total -= (plus & shifted_minus).bit_count() + (minus & shifted_plus).bit_count()
        assert total == (p*p if (x, y) == (0, 0) else 0), (p, x, y, total)
    print(f"Xia square-field T{p*p}: all {p*p-1} nonzero additive lags zero")


def verify_product(selectors):
    """Use the product of the additive square of F_3 and the cyclic order-5 action."""
    p = 3
    blocks = small_paley_blocks()
    side = len(blocks[0][0])
    points = tuple(product(range(p), range(p), range(side)))
    words = tuple({(x, y, z): (1 if selector > 0 else -1)*blocks[abs(selector)-1][j][z]
                   for x, y, z in points for selector in (selectors[x*p+y],)}
                  for j in range(4))
    size = len(points)
    for a, b, c in points:
        total = sum(word[x, y, z]*word[(x+a)%p, (y+b)%p, (z+c)%side]
                    for word in words for x, y, z in points)
        assert total == (4*size if (a, b, c) == (0, 0, 0) else 0)

    # G-developed Goethals–Seidel array, with the coordinate permutation x -> -x.
    # Entries are word number, sign and type: difference, reversal or transpose-reversal.
    array = (
        ((0, 1, "D"), (1, 1, "R"), (2, 1, "R"), (3, 1, "R")),
        ((1, -1, "R"), (0, 1, "D"), (3, -1, "T"), (2, 1, "T")),
        ((2, -1, "R"), (3, 1, "T"), (0, 1, "D"), (1, -1, "T")),
        ((3, -1, "R"), (2, -1, "T"), (1, 1, "T"), (0, 1, "D")),
    )
    rows = []
    for i, (a, b, c) in product(range(4), points):
        row = []
        for j, (x, y, z) in product(range(4), points):
            k, sign, kind = array[i][j]
            if kind == "D":
                shift = ((x-a)%p, (y-b)%p, (z-c)%side)
            elif kind == "R":
                shift = ((-x-a)%p, (-y-b)%p, (-z-c)%side)
            else:
                shift = ((x+a)%p, (y+b)%p, (z+c)%side)
            row.append(sign*words[k][shift])
        rows.append(pack(row))
    pairs = verify_orthogonal(4*size, rows)
    assert 4*size == 180 and pairs == comb(180, 2)
    print(f"Noncyclic T9–Paley product: H(180), all {pairs:,} pairwise row dots zero")


def verify_progression():
    middle_prime = 6_419_670_084_493_781
    middle_factors = (2, 2, 5, 1319, 4337, 56_111_063)
    outer_factors = (2, 3, 3, 3, 7, 89, middle_prime)
    assert all(prime_divisors(p) == {p}
               for p in set(middle_factors + outer_factors) - {middle_prime})
    for prime, factors in ((middle_prime, middle_factors), (OUTER_PRIME, outer_factors)):
        assert prod(factors) == prime - 1 and pow(2, prime - 1, prime) == 1
        assert all(gcd(pow(2, (prime - 1)//factor, prime) - 1, prime) == 1
                   for factor in set(factors))

    length = FIELD**2
    modulus = 44*PERIOD
    width_modulus = prod(EXCLUDED_DIVISORS)
    period = modulus*width_modulus
    assert gcd(modulus, width_modulus) == 1 and gcd(FIELD, period) == 1
    assert gcd(BASE, PERIOD) == 1
    assert period == 249_768_541_093_990_632_815_972_500_309_680
    assert gcd(OUTER_PRIME, period) == 1 and OUTER_PRIME % 8 == 3 and period % 8 == 0
    assert (44*BASE*pow(length, -1, modulus) - 1) % modulus == OUTER_PRIME % modulus
    assert OUTER_PRIME % modulus == 11_945_044_025_938_540_483
    assert period % (4*width_modulus) == 0
    t = length*(OUTER_PRIME + 1)//4
    assert t == 371_955_264_207_179_136_800_789
    assert t % 11 == 0 and t % 24_342_780 == 20_018_009
    n = t//11
    assert n % PERIOD == BASE and n % length == 0 and length == 6889
    assert n % (31**2) == 16 and n % 41 == 21 and n % (23**2) == 435
    assert ((t - 1)//2) % (23**2) == 276
    assert (t % 13, t % 19, t % 37) == (5, 2, 1)
    assert all((4*t - 1) % p == 0 for p in (5, 479))
    assert all((2*t - 1) % p == 0 for p in (3, 7))
    assert (16*t + 1) % 37 not in {x*x % 37 for x in range(37)}
    assert tuple(t % p for p in EXCLUDED_DIVISORS) == (3, 7, 38, 23, 4, 23, 156)
    assert (FIELD*FIELD - 1)//2 % 9 == 6 and gcd(FIELD, lcm(period, 9)) == 1
    print(f"T6889–Paley progression: first certified Q={OUTER_PRIME}, order {4*t}")


if __name__ == "__main__":
    control = t_selectors(3)
    verify_periodic(3, control)
    verify_product(control)
    verify_periodic(FIELD, t_selectors(FIELD))
    verify_progression()
