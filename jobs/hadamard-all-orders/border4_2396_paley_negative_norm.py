"""Construct a modular negative complement to the exact Paley positive half."""

from random import Random

from border4_2396 import periodic
from border4_2396_paley_one_hole import paley_words

N = 299
J = (1 << N) - 1
CYCLIC = (1 << N) | 1
AUGMENTATION_IDENTITY = J ^ 1
SELF_RECIPROCAL = 0x1FFF
DIRECTED_PAIRS = (0xAE3, 0x149F002C19C0597A7AFD2689FA4D13F49F)
ABSOLUTE_SUMS = {(3, 33): 7, (15, 27): 11, (11, 25): 15, (5, 17): 21}
MASKS = (
    0x12B9D735496954E65AD80FD48CD36F99B29C5D349F1E4EB5BCD81ABE59BB0F298CD543EAA72,
    0x63EE96915CE2CE73832722C5636E6553A296B9DE9E1424A202290C21AACE2413B9D1F3B7F6D,
    0x3583547CF7978E2E6E7C4DCDC46A3190F78A1F95D2BBE264EDE32678CBCCB754BB2C4483D9E,
)
PEAK64_MASKS = (
    0x4570BA31D3B7C7DB9A4C4E8F687B2AC009B7C41D93D87356312CCAFF6C18D1DF6E92D652AAF,
    0x66918C92E8A62963A7B71A8A645FB719062BA2246343CA72018CE020D005A657B257BAD56F0,
    0x1791E11259AB9F035475027DFB3CA8524D6ECF6D7F074E23324400F608BCC8A3AE4588EB525,
)


def divide(left, right):
    quotient = 0
    while left and left.bit_length() >= right.bit_length():
        shift = left.bit_length() - right.bit_length()
        quotient ^= 1 << shift
        left ^= right << shift
    return quotient, left


def multiply(left, right):
    result = 0
    while right:
        bit = right & -right
        result ^= left << (bit.bit_length() - 1)
        right ^= bit
    return result


def remainder(left, right):
    return divide(left, right)[1]


def inverse(left, modulus):
    previous, current = modulus, remainder(left, modulus)
    a, b = 0, 1
    while current:
        quotient, tail = divide(previous, current)
        previous, current = current, tail
        a, b = b, a ^ multiply(quotient, b)
    assert previous == 1
    return remainder(a, modulus)


def power(left, exponent, modulus):
    result = 1
    while exponent:
        if exponent & 1:
            result = remainder(multiply(left, result), modulus)
        left = remainder(multiply(left, left), modulus)
        exponent >>= 1
    return result


def reciprocal(poly, width):
    return int(f"{poly:0{width}b}"[::-1], 2)


def reflect(poly):
    return (poly & 1) | (reciprocal(poly >> 1, N - 1) << 1)


def augmentation(poly):
    return poly ^ (J if poly.bit_count() % 2 else 0)


def circular(left, right):
    return remainder(multiply(left, right), CYCLIC)


def shift(poly, amount):
    return ((poly << amount) | (poly >> (N - amount))) & J


def check_factors():
    factors = (3, SELF_RECIPROCAL, *DIRECTED_PAIRS,
               *(reciprocal(f, f.bit_length()) for f in DIRECTED_PAIRS))
    assert sorted(f.bit_length() - 1 for f in factors) == [1, 11, 11, 12, 132, 132]
    combined = 1
    for f in factors:
        combined = multiply(combined, f)
        degree = f.bit_length() - 1
        x = remainder(2, f)
        assert power(x, 1 << degree, f) == x
        for prime in (2, 3, 11):
            if degree % prime == 0:
                inverse(power(x, 1 << (degree // prime), f) ^ x, f)
    assert combined == CYCLIC
    assert power(2, 1 << 6, SELF_RECIPROCAL) == inverse(2, SELF_RECIPROCAL)


def sign_word(poly):
    return tuple(1 - 2 * (poly >> i & 1) for i in range(N))


def sign_sum(poly):
    return N - 2 * poly.bit_count()


def find_two_heads(d, k, random):
    f = J ^ d ^ shift(d, k)
    proper_f = augmentation(f)
    proper_inverse = augmentation(inverse(f, J))
    assert circular(proper_f, proper_inverse) == AUGMENTATION_IDENTITY
    required = AUGMENTATION_IDENTITY ^ circular(proper_inverse, reflect(proper_inverse))
    assert required == reflect(required) and not required & 1
    h = required & ((1 << 150) - 2)
    assert h ^ reflect(h) == required
    base = circular(h, proper_f)
    directions = tuple(circular((1 << i) | (1 << (N - i)), proper_f) for i in range(1, 150))
    directions += (J,)
    for _ in range(1000):
        u = base
        for direction in directions:
            if random.getrandbits(1):
                u ^= direction
        v = u ^ f
        w_sum = ABSOLUTE_SUMS.get(tuple(sorted((abs(sign_sum(u)), abs(sign_sum(v))))))
        if w_sum is not None:
            assert circular(u, reflect(u)) ^ circular(v, reflect(v)) == 1
            return u, v, w_sum
    raise AssertionError("Expected an exact sum pair from the affine family")


def required_norm(u, v):
    constant = u.bit_count() + v.bit_count() - N
    result = 0
    for i in range(N):
        coefficient = (N if i == 0 else 0) + constant
        coefficient -= (u & shift(u, i)).bit_count() + (v & shift(v, i)).bit_count()
        assert coefficient % 2 == 0
        result |= (coefficient // 2 % 2) << i
    assert not result & 1 and reflect(result) == result and augmentation(result) == result
    return result


def field_embedding(f):
    quotient, residual = divide(CYCLIC, f)
    assert residual == 0
    return circular(quotient, inverse(quotient, f))


def find_repeated(required, w_sum, random):
    self_target = remainder(required, SELF_RECIPROCAL)
    self_root = power(self_target, 32, SELF_RECIPROCAL)
    base = circular(self_root, field_embedding(SELF_RECIPROCAL))
    assert remainder(circular(base, reflect(base)), SELF_RECIPROCAL) == self_target
    targets = tuple((f, remainder(required, f), field_embedding(f)) for f in DIRECTED_PAIRS)
    for _ in range(1000):
        w = base
        for f, target, embedding in targets:
            value = random.randrange(1, 1 << (f.bit_length() - 1))
            companion = remainder(multiply(target, inverse(value, f)), f)
            w ^= circular(embedding, value) ^ reflect(circular(embedding, companion))
        if random.getrandbits(1):
            w ^= J
        if abs(sign_sum(w)) == w_sum:
            assert augmentation(circular(w, reflect(w))) == required
            return w
    raise AssertionError("Expected an exact sum from the norm family")


def audit(source, k, masks, sums, expected):
    one_hole, d = source
    translated = d[-k:] + d[:-k]
    u, v, w = map(sign_word, masks)
    assert all(a * b == -c * e for a, b, c, e in zip(u, v, d, translated, strict=True))
    positive = (one_hole,
                tuple((a + b) // 2 for a, b in zip(d, translated, strict=True)),
                tuple((a - b) // 2 for a, b in zip(d, translated, strict=True)),
                (0,) * N)
    negative = ((1,) + (0,) * (N - 1),
                tuple((a + b) // 2 for a, b in zip(u, v, strict=True)),
                tuple((a - b) // 2 for a, b in zip(u, v, strict=True)),
                w)
    assert all(a * a + b * b == 1 for s, t in zip(positive, negative, strict=True)
               for a, b in zip(s, t, strict=True))
    assert periodic(positive) == [597] + [-2] * (N - 1)
    auxiliary = periodic((u, v, w, w))
    assert auxiliary[0] == 1196 and all(value % 16 == 0 for value in auxiliary[1:])
    t_correlation = periodic(negative)
    assert t_correlation[0] == 599 and all(value % 8 == 0 for value in t_correlation[1:])
    assert tuple(map(sum, negative)) == sums
    assert sum(sum(row)**2 for row in negative) == 599
    words = tuple(tuple(s[i % N] + (1 - 2 * (i % 2)) * t[i % N] for i in range(2 * N))
                  for s, t in zip(positive, negative, strict=True))
    assert all(abs(value) == 1 for row in words for value in row)
    assert tuple(map(sum, words)) == (0, 2, 0, 0)
    residual = tuple(value + 4 for value in periodic(words)[1:])
    for i, value in enumerate(residual, 1):
        assert value == 2 * (1 - 2 * (i % 2)) * (t_correlation[i % N] if i % N else 0)
    stats = (sum(value % 16 == 0 for value in residual), residual.count(0),
             max(map(abs, residual)), sum(value * value for value in residual))
    assert stats == expected
    print(f"Paley split {k}: exact positive half and modular negative complement {stats}")


def main():
    check_factors()
    source = paley_words()
    d = sum((value < 0) << i for i, value in enumerate(source[1]))
    inverse(d, J)
    random = Random(40)
    u, v, w_sum = find_two_heads(d, 1, random)
    w = find_repeated(required_norm(u, v), w_sum, random)
    assert (u, v, w) == MASKS
    audit(source, 1, MASKS, (1, -6, -11, -21), (597, 77, 112, 1150976))
    audit(source, 4, PEAK64_MASKS, (1, 6, -21, 11), (597, 121, 64, 432128))


if __name__ == "__main__":
    main()
