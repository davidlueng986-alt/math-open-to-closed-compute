"""Check three published T seeds and their Paley-I progression certificates."""

import json
from math import gcd, isqrt, prod
from pathlib import Path

from paley_progression import selection_words, small_paley_blocks, verify_control
from t599_length_change import aperiodic

# HadamardR T_sequences, sorted by Matrix and ColumnNumber within each Order.
T43 = (1, 1, -1, 2, 2, -2, 1, -2, 1, 1, -1, 1, 1, 1, -2, 1, -2, 2, -2, -1, -1, 2,
       3, 3, -3, -4, 3, -4, -3, -4, 3, 4, -3, 4, -3, -4, 3, -4, -3, -4, -3, 3, 3)
T67 = (2, 1, -2, 2, 1, -2, -1, 2, 1, 2, -2, -1, 1, -1, -2, -2, -2,
       2, 2, 2, 1, -1, -1, -2, 2, 1, 2, -1, -2, 1, -2, 2, 1, -1,
       3, -3, 4, 3, -3, 3, 4, 3, 4, 3, 3, 4, 3, 3, 3, -4, -4, -4,
       3, 3, 3, 4, -3, -3, 4, -3, -4, -3, 3, 3, -4, -3, 3)
T73 = (1, -2, 1, 2, -1, 2, 1, 2, -1, 2, -1, 2, 1, -2, -1, 2, 1, -2, -1,
       2, 1, 2, 1, 2, -1, -2, -1, -2, 1, 2, 1, -2, -1, -2, -1, -2, 2,
       3, 3, -4, 3, -4, 4, -4, -4, -4, -3, -3, -4, 3, 3, 4, 3, 4, 3, -3,
       4, 3, 4, -3, 3, 4, 3, 3, 4, -4, -4, -4, 4, 3, 4, -3, 3)

FIRST, STEP = 20_018_009, 24_342_780
BASE_MODULUS = 4 * STEP


def check_explicit_progression():
    r, q, exponent_step = 43, 445_693_291, 31_548
    modulus = BASE_MODULUS * 13 * 19
    assert modulus == 24_050_666_640
    assert FIRST == 599 + 199 * 100_590 and STEP == 242 * 100_590
    assert STEP % 121 == STEP % 4 == 0 and (FIRST % 121, FIRST % 4) == (11, 1)
    assert q % 8 == 3 and gcd(q, modulus) == 1
    assert all(q % d for d in range(2, isqrt(q) + 1))
    assert pow(q, exponent_step, modulus) == 1
    assert q % BASE_MODULUS == (4 * FIRST * pow(r, -1, BASE_MODULUS) - 1) % BASE_MODULUS == 56_208_811
    t = r * ((q + 1) // 4)
    assert t == 4_791_202_889 and t % STEP == FIRST
    assert (t % 13, t % 19) == (5, 2)
    assert (4 * t - 1) % (5 * 479) == (2 * t - 1) % (3 * 7) == 0
    assert (16 * t + 1) % 19 == 14 and all(x*x % 19 != 14 for x in range(19))
    assert t % 13 != 0 and t % 19 not in {0, 3, 4, 9, 11, 13, 14, 15, 16}
    print("T43 AP: prime 445693291, period 31548, first multiplier 4791202889")


def prescribed_residue_classes():
    widths = (43, 67, 73)
    initial = {r: (4 * FIRST * pow(r, -1, BASE_MODULUS) - 1) % BASE_MODULUS for r in widths}
    assert initial == {43: 56_208_811, 67: 15_728_107, 73: 7_766_131}
    assert all(gcd(q, BASE_MODULUS) == 1 and q % 8 == 3 for q in initial.values())

    moduli = (13, 19, 23)
    assert all(gcd(BASE_MODULUS, p) == 1 for p in moduli)
    forbidden = {r: tuple(r * pow(4, -1, p) % p for p in moduli) for r in widths}
    assert forbidden == {43: (1, 6, 5), 67: (7, 12, 11), 73: (2, 4, 1)}
    assert (16 * 2 + 1) % 23 == 10 and all(x*x % 23 != 10 for x in range(23))

    for a in range(13):
        for b in range(19):
            r = next(r for r, (f13, f19, f23) in forbidden.items()
                     if a != f13 and b != f19 and 2 != f23)
            q, modulus = initial[r], BASE_MODULUS
            for p, target in zip(moduli, (a, b, 2), strict=True):
                residue = (4 * target * pow(r, -1, p) - 1) % p
                assert residue != 0
                q += modulus * ((residue - q) * pow(modulus, -1, p) % p)
                modulus *= p
            assert modulus == 4 * STEP * 13 * 19 * 23
            assert gcd(q, modulus) == 1 and q % 8 == 3
            t = r * ((q + 1) // 4)
            assert t % STEP == FIRST
            assert (t % 13, t % 19, t % 23) == (a, b, 2)
    print("T43/T67/T73 AP: all 247 residue pairs modulo 13 and 19, excluding Scarpis modulo 23")


def check_explicit_prime_parameters():
    data = json.loads(Path(__file__).with_name("t43_prime_parameters.json").read_text())
    proved = set()
    for p, (base, factors) in data["lucas_certificates"]:
        assert p not in proved
        if p == 2:
            assert (base, factors) == (1, [])
        else:
            assert 2 <= base < p and all(q in proved for q in factors)
            assert prod(factors) == p - 1
            assert pow(base, p - 1, p) == 1
            assert all(gcd(pow(base, (p - 1) // q, p) - 1, p) == 1 for q in set(factors))
        proved.add(p)

    parameters = data["parameters"]
    assert len(parameters) == 13 * 19
    modulus = BASE_MODULUS * 13 * 19 * 23
    for idx, (r, q) in enumerate(parameters):
        a, b = divmod(idx, 19)
        assert r in {43, 67, 73} and q in proved and q % 8 == 3
        assert pow(q, 473_220, modulus) == 1
        t = r * ((q + 1) // 4)
        assert (t % STEP, t % 13, t % 19, t % 23) == (FIRST, a, b, 2)
    print(f"T43/T67/T73 AP: {len(parameters)} explicit prime-power bands, "
          f"{len(proved)} replayed Lucas primality certificates")


if __name__ == "__main__":
    blocks = small_paley_blocks()
    for selectors, length, pairs in ((T43, 43, 369_370), (T67, 67, 897_130), (T73, 73, 1_065_070)):
        assert len(selectors) == length and all(1 <= abs(entry) <= 4 for entry in selectors)
        assert aperiodic(selection_words(selectors)) == [length] + [0]*(length - 1)
        assert verify_control(selectors, blocks) == pairs
    check_explicit_progression()
    prescribed_residue_classes()
    check_explicit_prime_parameters()
