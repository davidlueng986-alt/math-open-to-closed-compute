"""Necessary intersection conditions for 2-(1198, 599, 598) designs.

This checks designs with exactly three intersections between distinct blocks.
It enumerates arithmetic profiles, tests necessary graph congruences, and
checks a conference-matrix obstruction. Survival does not certify existence.
"""

from dataclasses import dataclass
from math import gcd, isqrt


def intersection_profiles(t):
    """Yield possible intersection triples and their per-block multiplicities.

    For odd t > 1, blocks are distinct and never complementary. The zeroth,
    first and second moments for intersections with all other blocks are
    4t-3, 2t(t-1), and t²(t-1). The weighted adjacency matrix obtained by
    subtracting the smallest intersection and dividing by the gcd of the
    differences is integral. Its two eigenvalues on the space perpendicular
    to the constant vector imply that this gcd divides t and the smallest
    intersection.
    """
    if t < 3 or t % 2 == 0:
        raise ValueError("expected an odd multiplier of at least three")

    count = 4 * t - 3
    first = 2 * t * (t - 1)
    second = t * t * (t - 1)
    # In a three-valued profile with positive multiplicities, a < mean < c.
    last_a = min(t - 3, (first - 1) // count)
    first_c = first // count + 1
    for a in range(1, last_a + 1):
        for b in range(a + 1, t - 1):
            c_numerator = second - (a + b) * first + a * b * count
            if c_numerator <= 0:
                continue
            for c in range(max(b + 1, first_c), t):
                c_count, remainder = divmod(c_numerator, (c - a) * (c - b))
                if remainder:
                    continue
                d = gcd(b - a, c - a)
                if t % d or a % d:
                    continue
                a_count, remainder = divmod(
                    second - (b + c) * first + b * c * count, (a - b) * (a - c)
                )
                if remainder or a_count <= 0:
                    continue
                b_count = count - a_count - c_count
                if b_count > 0 and a * a_count + b * b_count + c * c_count == first:
                    yield (a, b, c), (a_count, b_count, c_count)


@dataclass(frozen=True)
class CongruenceObstruction:
    exceptional_intersection: int
    modulus: int
    nonadjacent_residue: int
    adjacent_residue: int
    required_total: int
    lower_total: int
    upper_total: int


def common_neighbor_obstructions(t, intersections, degrees):
    """Exclude profiles by applying the intersection Gram equation modulo a gap.

    Let A be the graph for the exceptional intersection a, with degree d.
    Modulo the gap between the other two intersections, the block Gram matrix
    P is alpha I + beta J + gamma A. In P²=tP+t²(t−1)J this determines the
    number of common neighbors modulo the gap for each pair type. Sum those
    counts around a vertex and compare with the exact value d(d−1).

    This routine uses profiles where the gcd of the differences is one.
    """
    if gcd(intersections[1] - intersections[0], intersections[2] - intersections[0]) != 1:
        raise ValueError("expected intersection differences with gcd one")

    vertices = 4 * t - 2
    for index, (a, degree) in enumerate(zip(intersections, degrees, strict=True)):
        b, c = (value for i, value in enumerate(intersections) if i != index)
        modulus = c - b
        if modulus == 1:
            continue
        alpha, beta, gamma = t - b, b, a - b
        inverse = pow(gamma * gamma, -1, modulus)
        constant = t * beta + t * t * (t - 1) - 2 * alpha * beta
        constant -= beta * beta * vertices + 2 * beta * gamma * degree
        nonadjacent = constant * inverse % modulus
        adjacent = (constant + gamma * (t - 2 * alpha)) * inverse % modulus

        lower_total, upper_total = 0, 0
        empty_interval = False
        for residue, is_adjacent in ((nonadjacent, False), (adjacent, True)):
            # There are vertices−2 common-neighbor positions. An adjacent
            # endpoint uses one of its neighbors on the other endpoint.
            used = degree - int(is_adjacent)
            lower = max(0, 2 * used - (vertices - 2))
            upper = used
            lower += (residue - lower) % modulus
            upper -= (upper - residue) % modulus
            multiplicity = degree if is_adjacent else vertices - 1 - degree
            empty_interval |= multiplicity > 0 and lower > upper
            lower_total += multiplicity * lower
            upper_total += multiplicity * upper

        required = degree * (degree - 1)
        wrong_total = not lower_total <= required <= upper_total
        wrong_residue = (required - lower_total) % modulus != 0
        if empty_interval or wrong_total or wrong_residue:
            yield CongruenceObstruction(
                a, modulus, nonadjacent, adjacent, required, lower_total, upper_total
            )


def conference_obstruction(t, intersections, degrees):
    """The near-duplicate matching profile forces a conference matrix of order 2t.

    Put t=2k+1. Write P=(k+1)I+kJ+A+kM for the block Gram matrix, where M
    matches the pairs of intersection 2k and A has degree 2k. The two
    restricted eigenvalues of A+kM are k and -k-1, and its constant
    eigenvalue is 3k. Expanding the resulting matrix polynomial gives

        A²+A=k(I+J-AM-MA-M).

    Between two matching groups there is at most one A-edge. Two edges
    sharing an endpoint would make AM or MA nonzero on an existing edge.
    Two opposite edges would make AM+MA equal two on a cross pair. Each
    group has degree 4k in total, so there is exactly one edge to every
    other group. Define T_ij as +1 or -1 according to the selected endpoint
    in group i, with diagonal zero. The four common-neighbor counts between
    two groups are k-1, k, 0 and 0. Thus exactly 2k-1 of the other groups h
    have T_hi=T_hj. This gives TᵀT=(4k+1)I-J. Border T by a row of ones and
    a column from its one-dimensional left kernel. That column can be
    taken to be a sign vector since (4k+1)I-TTᵀ is rank one with diagonal 1.

    If a prime p=3 mod 4 divides 2t−1 exactly once, the conference matrix
    C is impossible. Over F_p, ker C=im Cᵀ: if Cx=0 mod p, lift x to an
    integer vector and use Cᵀ(Cx/p)=((2t−1)/p)x, with invertible coefficient.
    The reverse inclusion follows from CCᵀ=(2t−1)I. This is a totally
    isotropic subspace of dimension t. In a basis starting with that
    subspace, the ambient dot product has Gram determinant (-1)^t times
    a square, from its block form [0, B; Bᵀ, D]. Since t is odd, this
    contradicts the determinant class of the identity over F_p.

    Return the obstructing prime if one exists.
    """
    k = (t - 1) // 2
    if intersections != (k, k + 1, 2 * k) or degrees != (6 * k, 2 * k, 1):
        return None

    order_minus_one = 2 * t - 1
    remainder = order_minus_one
    for prime in range(3, isqrt(order_minus_one) + 1, 2):
        exponent = 0
        while remainder % prime == 0:
            remainder //= prime
            exponent += 1
        if exponent == 1 and prime % 4 == 3:
            return prime
    return remainder if remainder % 4 == 3 else None


def main():
    t = 599
    profiles = tuple(intersection_profiles(t))
    expected = (
        ((1, 299, 300), (1, 1197, 1195)),
        ((259, 295, 306), (12, 1390, 991)),
        ((270, 299, 322), (46, 2250, 97)),
        ((286, 299, 303), (391, 507, 1495)),
        ((286, 299, 309), (271, 1680, 442)),
        ((299, 300, 598), (1794, 598, 1)),
    )
    if profiles != expected:
        raise ValueError(f"unexpected intersection profiles: {profiles}")

    exclusions = []
    for intersections, degrees in profiles:
        obstructions = tuple(common_neighbor_obstructions(t, intersections, degrees))
        print(f"intersection sizes {intersections}, per-block counts {degrees}")
        for obstruction in obstructions:
            print(f"  excluded using intersection {obstruction.exceptional_intersection} "
                  f"modulo {obstruction.modulus}: required {obstruction.required_total}, "
                  f"bounds [{obstruction.lower_total}, {obstruction.upper_total}]")
        prime = conference_obstruction(t, intersections, degrees)
        if prime is not None:
            print(f"  excluded by conference matrix of order {2 * t}: "
                  f"{prime} divides {2 * t - 1} exactly once and is 3 modulo 4")
        if obstructions or prime is not None:
            exclusions.append(intersections)

    if exclusions != [(259, 295, 306), (270, 299, 322), (299, 300, 598)]:
        raise ValueError(f"unexpected exclusions: {exclusions}")
    print("Six arithmetic profiles, three excluded, three remain under these conditions.")


if __name__ == "__main__":
    main()
