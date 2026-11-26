"""Check the nested progression parity classification and exact norm obstructions."""

from math import isqrt
from random import Random

from direct_2396_cyclic import quarter_correlations


P = 599
HALF = P // 2
SIZES = (299, 298, 290, 277)
RESIDUES = frozenset(x*x % P for x in range(1, P))
LEGENDRE = sum(1 << x for x in RESIDUES)
PARITY_STEPS = (23, 36, 91, 123, 129, 158, 217)
NORM_CERTIFICATES = (
    (23, 3593, 9849752, 1770),
    (123, 9346951739, 19599398982566011826, 439425609),
    (217, 574799201, 246435235388561686, 536927035),
)


def rotation(mask, offset, length=P):
    offset %= length
    return ((mask << offset) | (mask >> (length-offset))) & ((1 << length)-1)


def reflection(mask, length=P):
    return (mask & 1) | sum((mask >> i & 1) << (length-i) for i in range(1, length))


def word(mask, length=P):
    return ''.join('-' if mask >> i & 1 else '+' for i in range(length))


def product_mod_two(x, y, length):
    result = 0
    while x:
        bit = x & -x
        result ^= rotation(y, bit.bit_length()-1, length)
        x ^= bit
    return result


def construct_first_pair(length, support, lower, anchor):
    """Construct the weights for sums 1, 3, given the two valid tail masks."""
    assert length >= 3 and length % 2 and not support & lower
    half = length//2
    rs, rl = reflection(support, length), reflection(lower, length)
    required = ((1 << length)-1) if support.bit_count() % 2 else 0
    required ^= product_mod_two(support, rs, length)
    required ^= product_mod_two(support, rl, length)
    required ^= product_mod_two(lower, rs, length)
    assert reflection(required, length) == required and not required & 1
    unequal = [i for i in range(1, half+1) if required >> i & 1]
    equal = [i for i in range(1, half+1) if not required >> i & 1]
    pairs, remainder = divmod(half-1-len(unequal), 2)
    assert not remainder and 0 <= pairs <= len(equal)
    b = sum(1 << ((anchor+i) % length) for i in unequal)
    b |= sum((1 << ((anchor+i) % length)) | (1 << ((anchor-i) % length))
             for i in equal[:pairs])
    return b | (1 << anchor), b


def check_arbitrary_tail():
    rng = Random(599)
    for final_sums in ((1, 1), (1, 5), (3, 5), (5, 7), (7, 9), (19, 45)):
        length = (10+sum(s*s for s in final_sums))//4
        k = (length-final_sums[1])//2
        m = (final_sums[1]-final_sums[0])//2
        for anchor in (0, length//2):
            used = rng.sample(range(length), k+m)
            support = sum(1 << i for i in used[:m])
            lower = sum(1 << i for i in used[m:])
            a, b = construct_first_pair(length, support, lower, anchor)
            signs = (a, b, support | lower, lower)
            words = tuple(word(x, length) for x in signs)
            assert tuple(length-2*x.bit_count() for x in signs) == (1, 3, *final_sums)
            assert not any(x % 2 for x in quarter_correlations(words)[1:])


def nested_parity_steps():
    difference = rotation(LEGENDRE, -1) ^ rotation(reflection(LEGENDRE), 1)
    for step in range(1, HALF+1):
        support = sum(1 << (j*step % P) for j in range(-6, 7))
        support_squared = sum(1 << (2*j*step % P) for j in range(-6, 7))
        target = difference ^ support_squared
        rhs = rotation(target, 6*step) ^ rotation(target, 7*step)
        # Multiplication by 1+z^(13*step) on the cycle, with coefficient zero at zero.
        disagreement, value = 0, 0
        for j in range(1, P):
            k = 13*j*step % P
            value ^= rhs >> k & 1
            disagreement |= value << k
        assert rotation(disagreement, 13*step) ^ disagreement == rhs
        assert reflection(disagreement) == disagreement
        if support & disagreement:
            continue
        different = [i for i in range(1, HALF+1) if disagreement >> i & 1]
        equal = [i for i in range(1, HALF+1)
                 if not ((support | disagreement) >> i & 1)]
        paired, remainder = divmod(SIZES[-1]-len(different), 2)
        if remainder or not 0 <= paired <= len(equal):
            continue
        smallest = sum(1 << i for i in different)
        smallest |= sum((1 << i) | (1 << (P-i)) for i in equal[:paired])
        samples = (LEGENDRE, LEGENDRE ^ 2, smallest | support, smallest)
        assert not support & smallest
        assert tuple(x.bit_count() for x in samples) == SIZES
        assert not any(x % 2 for x in quarter_correlations(tuple(map(word, samples)))[1:])
        yield step, support, samples


def check_coupled_change(step, support, samples):
    allowed = 0
    for i in range(P):
        change_late = (1 << i) | (1 << ((i+step) % P))
        change_early = (1 << ((1+i-6*step) % P)) | (1 << ((1+i+7*step) % P))
        if change_late & support or change_early & 2:
            continue
        trial = tuple(x ^ (change_early if j < 2 else change_late)
                      for j, x in enumerate(samples))
        if tuple(x.bit_count() for x in trial) != SIZES:
            continue
        assert not any(x % 2 for x in quarter_correlations(tuple(map(word, trial)))[1:])
        allowed += 1
    assert allowed
    return allowed


def check_norm_certificate(step, prime, trace, quotient):
    assert prime % P == P-1
    assert all(prime % j for j in range(2, isqrt(prime)+1))
    modulus = prime*prime
    assert 0 < quotient < prime and 0 <= trace < modulus
    assert pow((trace*trace-4) % prime, (prime-1)//2, prime) == prime-1

    def add(x, y):
        return (x[0]+y[0]) % modulus, (x[1]+y[1]) % modulus

    def scale(k, x):
        return (k*x[0]) % modulus, (k*x[1]) % modulus

    def multiply(x, y):
        a, b = x
        c, d = y
        return (a*c-b*d) % modulus, (a*d+b*c+trace*b*d) % modulus

    def star(x):
        a, b = x
        return (a+trace*b) % modulus, (-b) % modulus

    def norm(x):
        return multiply(x, star(x))

    powers = [(1, 0)]
    for _ in range(P):
        powers.append(multiply(powers[-1], (0, 1)))
    assert powers[-1] == (1, 0)
    assert tuple(sum(x[i] for x in powers[:-1]) % modulus for i in range(2)) == (0, 0)
    a = tuple(-2*sum(powers[j][i] for j in RESIDUES) % modulus for i in range(2))
    b = add(a, (0, 2))
    m = tuple(sum(powers[j*step % P][i] for j in range(-6, 7)) % modulus
              for i in range(2))
    assert norm(a) == (P+1, 0)
    target = add((2*P, 0), scale(-pow(2, -1, modulus), add(norm(a), norm(b))))
    target = add(target, scale(-1, norm(m)))
    assert target == (prime*quotient, 0)
    print(f"Nested progression step {step}: exact norm obstruction at prime {prime}")


if __name__ == "__main__":
    check_arbitrary_tail()
    print("Arbitrary nested tail supports replayed for six odd lengths.")
    instances = list(nested_parity_steps())
    assert tuple(row[0] for row in instances) == PARITY_STEPS
    print("Seven progression steps admit all raw modulo eight and the exact four sums.")
    for record in NORM_CERTIFICATES:
        check_norm_certificate(*record)
    for instance in instances:
        check_coupled_change(*instance)
    print("Coupled two-position swaps in each word pair preserve raw modulo eight.")
