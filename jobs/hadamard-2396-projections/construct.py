"""Construct the three projected layers from orbit parameters and seek a binary lift."""

import argparse
import itertools
import json
from collections import defaultdict
from functools import cache

from verify import HERE, LENGTH, QUOTIENTS, check, paf

# Each triple is (fibre sum, mean on the two nonzero orbits, half their difference).
# For 63, the nine mod-9 classes reduce to the representatives 0, 3, 6, 1, 2.
def profile63(values):
    return tuple(values[i] for i in (0, 3, 6, 1, 2))


SEVEN = (
    ((-23, -7, -1, 19, -7, -1, 29, -7, -1), (-7, -2, 0, 3, -2, 0, 4, -2, 0), (-6, -1, 1, 4, -1, 1, 5, -1, 1)),
    ((-11, 1, 5, -7, 1, 5, 1, 1, 5), (1, 0, 0, -2, 0, 0, -2, 0, 0), (2, -3, 1, 1, -3, 1, 3, -3, 1)),
)
NINETEEN = {
    57: (
        ((25, -21, -3), (2, 0, 0), (-3, 5, -1)),
        ((-17, 3, 15), (-1, 1, 1), (2, 6, -2)),
    ),
    133: (
        ((37, -3, -3, -9, -3, -9, -9), (2, 0, 0, 0, 0, 0, 0), (-3, -3, 1, 1, 1, 1, 3)),
        ((19, -3, -3, -3, -3, -3, -3), (1, 0, 0, 0, 0, 0, 0), (-4, 1, -1, 3, -1, 7, 1)),
    ),
}


def expand(prime, fibre_sums, means, differences):
    rows = []
    for t in range(prime * len(fibre_sums)):
        i, j = t % len(fibre_sums), t % prime
        if j == 0:
            value = fibre_sums[i] - (prime - 1) * means[i]
        else:
            symbol = 1 if pow(j, (prime - 1) // 2, prime) == 1 else -1
            value = means[i] + symbol * differences[i]
        rows.append(value)
    return rows


@cache
def choices(total):
    return [(b, c) for b in range(-19, 20) if abs(total - 6 * b) <= 19
            for c in range(-19, 20) if abs(b) + abs(c) <= 19 and (b + c) % 2]


def spectral_key(d, c):
    x, y = d[0] - d[2], d[1] - d[2]
    z, w = c[0] - c[2], c[1] - c[2]
    return x*x + y*y - x*y + 7*(z*z + w*w - z*w), x*w - y*z


def coarse(sums, mean, delta):
    by_key = defaultdict(list)
    for u, v in itertools.product(choices(sums[3]), choices(sums[4])):
        b = mean - 3 * (u[0] + v[0])
        c = delta - 3 * (u[1] + v[1])
        key = spectral_key(
            (sum(sums[:3]) - 7*b, 3*(sums[3] - 7*u[0]), 3*(sums[4] - 7*v[0])),
            (c, 3*u[1], 3*v[1]),
        )
        if key[0] <= 2396:
            by_key[key].append((b, c, u, v))
    return by_key


@cache
def fine(sums, mean, delta):
    by_key = defaultdict(list)
    last = set(choices(sums[2]))
    for u, v in itertools.product(choices(sums[0]), choices(sums[1])):
        w = (mean-u[0]-v[0], delta-u[1]-v[1])
        if w in last:
            b, c = zip(u, v, w)
            key = spectral_key(tuple(a-7*h for a, h in zip(sums, b)), c)
            if key[0] <= 2396:
                by_key[key].append((u, v, w))
    return by_key


def complements(left, right):
    for (energy, determinant), candidates in left.items():
        yield from itertools.product(candidates, right.get((2396-energy, -determinant), ()))


def count63():
    # Only the 9- and 7-point margins enter the enumeration; the individual
    # 63-point cells below are used afterwards to identify the archived pair.
    a, b = (profile63(row[0]) for row in SEVEN)
    first, second = ((sum(row[1]), sum(row[2])) for row in SEVEN)
    expected = tuple(tuple(zip(profile63(row[1]), profile63(row[2]))) for row in SEVEN)
    count, matches = 0, 0
    class_at = (0, 3, 4, 1, 3, 4, 2, 3, 4)
    for x, y in complements(coarse(a, *first), coarse(b, *second)):
        for u, v in complements(fine(a[:3], *x[:2]), fine(b[:3], *y[:2])):
            parameters = (u + x[2:], v + y[2:])
            projected = []
            for row, five in zip(SEVEN, parameters):
                means, differences = zip(*(five[j] for j in class_at))
                projected.append(expand(7, row[0], means, differences))
            if [paf(projected, shift) for shift in range(63)] != [2358] + [-38]*62:
                raise ValueError("spurious spectral match in the 63-point search")
            count += 1
            matches += parameters == expected
    if matches != 1:
        raise ValueError("the 7- and 9-point search did not regenerate the 63-point pair")
    return count


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lift", type=int, metavar="SECONDS",
                        help="seek both sign words from margins and the 199-triple condition")
    args = parser.parse_args()
    margins = {"63": [expand(7, *params) for params in SEVEN]}
    margins.update({str(n): [expand(19, *params) for params in rows] for n, rows in NINETEEN.items()})
    for q in QUOTIENTS:
        rows = margins[str(q)]
        m = LENGTH // q
        if [paf(rows, s) for s in range(q)] != [2396 - 2*m] + [-2*m] * (q-1):
            raise ValueError(f"failed projection at {q}")
    if margins != json.loads((HERE / "witness.json").read_text())["projections"]:
        raise ValueError("reconstruction differs from the archived margins")
    print(f"{count63()} solutions in the fixed 63-point orbit search. All three archived layers reconstructed.")
    if args.lift is not None:
        from lift import Lift
        status, masks = Lift(margins, 1).solve(args.lift, 1197)
        if masks is None:
            raise SystemExit(f"no lift returned within this run ({status})")
        print(json.dumps({"negative_masks": masks, **check(masks, margins)}))


if __name__ == "__main__":
    main()
