"""Rebuild the two periodic T seeds and the order-7572 real matrix."""

from math import comb, gcd, isqrt

from paley_progression import verify_control
from verify import signs


# Finite signed orbit representatives from Kolpakov, hexagon:2611.01070v1, §2.
SEEDS = {
    127: (22, 9, (
        (1, 1), (2, 3), (3, 1), (4, -1), (5, 4), (8, 2), (10, -2),
        (11, 4), (13, -1), (16, 1), (20, -2), (23, -3), (33, 3), (39, -2),
    )),
    631: (458, 21, (
        (1, 1), (2, -3), (3, 3), (4, 3), (5, 1), (6, -4), (7, 1), (8, -4),
        (9, 2), (10, -2), (12, 1), (13, -1), (14, 2), (17, 4), (18, -1),
        (20, 3), (23, 2), (24, 1), (25, -1), (26, -1), (27, 3), (28, -2),
        (35, 3), (36, -4), (46, -2), (50, -2), (52, -3), (56, 4), (70, 2),
        (140, -4),
    )),
}


def selectors(prime):
    multiplier, orbit_size, representatives = SEEDS[prime]
    assert all(prime % divisor for divisor in range(2, isqrt(prime) + 1))
    unit_powers = [pow(multiplier, j, prime) for j in range(orbit_size)]
    assert len(set(unit_powers)) == orbit_size and pow(multiplier, orbit_size, prime) == 1
    chosen = [0]*prime
    chosen[0] = 1
    for representative, label in representatives:
        for j, power in enumerate(unit_powers):
            x = representative*power % prime
            assert not chosen[x]
            value = abs(label)
            moved = value if value == 1 else 2 + (value-2+j) % 3
            chosen[x] = moved if label > 0 else -moved
    assert all(chosen)

    # Signed label equality gives exactly the sum of the four correlations.
    for shift in range(1, prime):
        rotated = chosen[shift:] + chosen[:shift]
        assert sum((a == b) - (a == -b) for a, b in zip(chosen, rotated, strict=True)) == 0
    print(f"T({prime}): all {prime-1} nonzero periodic shifts exact")
    return tuple(chosen)


def williamson_three():
    a, b, c, d = (signs(word) for word in ("+++", "+--", "+--", "+--"))
    na, nb, nc, nd = (tuple(-x for x in word) for word in (a, b, c, d))
    return ((a,b,c,d),(nb,a,nd,c),(nc,d,a,nb),(nd,nc,b,a))


def verify_progressions():
    start, step = 20_018_009, 24_342_780
    width = 127
    residue, modulus = 560_813_812_987, 4_579_071_660_240
    assert modulus == 4*step*37*31*41
    assert gcd(residue, modulus) == 1 and residue % 8 == 3
    assert residue % (4*step) == 53_532_907
    assert (width*(residue+1)-4*start) % (4*step) == 0
    assert step % 11 == start % 11 == 0
    t0 = width*((residue+1)//4)
    assert (t0 % 37, t0 % 31, t0 % 41) == (1, 21, 26)
    assert (2*(t0//11)-1) % (31*41) == 0
    assert all(a*a % 37 != (16*t0+1) % 37 for a in range(37))
    q = residue+modulus
    assert q == 5_139_885_473_227
    assert all(q % divisor for divisor in range(2, isqrt(q) + 1))
    assert width*(q+1) == 652_765_455_099_956

    # The same prime-power Paley template has no parameter for T(631) in the main AP.
    other_residue = (4*start*pow(631, -1, 4*step)-1) % (4*step)
    assert other_residue == 23_273_755 and other_residue % 5 == 0 and other_residue % 8 == 3
    assert {pow(5, j, 8) for j in (1, 2)} == {1, 5}
    print("T127 AP: q=560813812987 mod4579071660240; certified order 652765455099956")


def verify():
    selectors(127)
    root = selectors(631)
    verify_progressions()
    assert verify_control(root, williamson_three()) == comb(7572,2) == 28_663_806


if __name__ == "__main__":
    verify()
