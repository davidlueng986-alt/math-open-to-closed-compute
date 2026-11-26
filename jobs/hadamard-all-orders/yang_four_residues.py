"""Replay the Yang seeds and certify coverage of four prescribed residues."""

from itertools import product
from math import comb, gcd, prod

from paley_progression import verify_control
from t187_yang import yang_selectors

# HadamardR Basesequences, BaseOrder 14 and 23, four words in BaseMatrix order.
BASES = {
    493: ("+-+---+-+++--++", "++++-++++-++---", "++-+--+-+++-++", "+++---+-++-+++"),
    799: ("+++-----+--++--+++--++-+", "++++---++-+--+-+-+---+--",
          "++++-++-+-++++--+-+++-+", "+++--------+-++--++-+-+"),
}
WIDTHS = (43, 67, 73, 493, 799)
PRESCRIBED_PRIMES = (13, 19, 23, 31)
FIRST, STEP = 20_018_009, 24_342_780


def verify_yang_seeds():
    blocks = tuple(tuple(((-1)**((i & j).bit_count()),) for j in range(4)) for i in range(4))
    for length, base in BASES.items():
        selectors = yang_selectors(base)
        assert len(selectors) == length
        assert verify_control(selectors, blocks) == comb(4*length, 2)


def verify_residue_tuples():
    modulus = 4*STEP
    starts = tuple((4*FIRST*pow(width, -1, modulus) - 1) % modulus for width in WIDTHS)
    assert starts == (56_208_811, 15_728_107, 7_766_131, 29_591_011, 18_258_283)
    assert all(gcd(q, modulus) == 1 and q % 8 == 3 for q in starts)

    auxiliary_prime, auxiliary_residue = 37, 1
    primes = PRESCRIBED_PRIMES + (auxiliary_prime,)
    assert all(gcd(modulus, prime) == 1 for prime in primes)
    assert all(gcd(width, prod(primes)) == 1 for width in WIDTHS)
    forbidden = [tuple(width*pow(4, -1, prime) % prime for prime in primes)
                 for width in WIDTHS]
    assert all(len(set(column)) == len(WIDTHS) for column in zip(*forbidden, strict=True))
    assert all(row[-1] != auxiliary_residue for row in forbidden)
    discriminant = (16*auxiliary_residue + 1) % auxiliary_prime
    assert discriminant == 17
    assert all(value*value % auxiliary_prime != discriminant for value in range(auxiliary_prime))

    # Each column can forbid at most one width. Enumerate the same cover independently.
    count = 0
    for prescription in product(*(range(prime) for prime in PRESCRIBED_PRIMES)):
        assert any(all(a != b for a, b in zip(prescription, row[:-1], strict=True)) for row in forbidden)
        count += 1
    assert count == prod(PRESCRIBED_PRIMES) == 176_111
    print("Five widths satisfy 176111 prescribed residue tuples with Scarpis excluded modulo 37")


if __name__ == "__main__":
    verify_yang_seeds()
    verify_residue_tuples()
