"""Replay the four-channel low-energy second-column candidate and its mod-five support."""

from collections import Counter, defaultdict
from hashlib import sha256

from stack_1197_four_channels import LOWER_OMITTED, sources
from stack_1198 import projection_targets
from stack_1198_channels import signatures
from stack_1198_joint import dot
from stack_1198_mod5 import Basis
from stack_odd_t_residual import conference_positive_columns
from verify import verify_orthogonal


UPPER_PIVOT, LOWER_PIVOT = 614, 894
UPPER_FLIPS = (
    333, 1175, 887, 643, 779, 338, 704, 898, 690, 915, 30, 957, 327, 508, 844, 313,
    721, 139, 303, 1012, 10, 871, 602, 367, 590, 238, 123, 5, 161, 763, 271, 125,
)
LOWER_FLIPS = (
    413, 409, 1154, 891, 529, 643, 331, 395, 368, 597, 674, 292, 1090, 798, 595,
    136, 759, 531, 382, 942, 299, 469, 465, 95, 166, 879, 221, 147, 1171, 1137,
    997, 426, 467, 1124,
)
LOW_ENERGY_UPPER = (
    244, 844, 831, 759, 511, 744, 258, 39, 1015, 165, 199, 12, 261, 1144, 467, 183,
    692, 772, 666, 154, 1050, 52, 560, 1136, 914, 601, 413, 387, 984, 855, 617, 334,
)
LOW_ENERGY_LOWER = (
    58, 645, 438, 1112, 328, 1194, 781, 949, 229, 493, 1161, 1008, 727, 69, 88,
    669, 213, 889, 305, 422, 461, 865, 257, 736, 80, 90, 137, 753, 1065, 460, 233,
    601, 192, 855,
)


def sorted_pairing(upper_deck, lower_deck):
    groups_a, groups_b = defaultdict(list), defaultdict(list)
    for i, (p, q) in enumerate(upper_deck):
        groups_a[p].append((q, i))
    for j, (p, q) in enumerate(lower_deck):
        if j not in LOWER_OMITTED:
            groups_b[p].append((q, j))
    assert groups_a.keys() == groups_b.keys()
    return {i: j for p in groups_a for (_, i), (_, j) in zip(sorted(groups_a[p]), sorted(groups_b[p]), strict=True)}


def check_channel_support(residues):
    conference = conference_positive_columns(149)
    side = len(conference)
    graph = [[0 if i == j else 2 * (col >> i & 1) - 1 for i in range(side)]
             for j, col in enumerate(conference)]
    graph += [[-int(i == j) for i in range(side)] for j in range(side)]
    channel_size = len(graph)
    supports, energies, failures = [], [], []
    for start in range(0, len(residues), channel_size):
        values = residues[start:start + channel_size]
        support = {j for j, value in enumerate(values) if value}
        basis = Basis(side)
        assert all(basis.add(graph[j]) for j in sorted(support))
        selected = set(support)
        for j in range(channel_size):
            if basis.rank == side:
                break
            if start + j not in LOWER_OMITTED and basis.add(graph[j]):
                selected.add(j)
        assert len(selected) == basis.rank == side
        assert sum(j not in selected and start + j not in LOWER_OMITTED for j in range(channel_size)) == 149
        transform = [sum(graph[j][i] * (values[j] // 4) for j in support) for i in range(side)]
        failures.append(sum(value % 25 != 0 for value in transform))
        supports.append(len(support))
        energies.append(sum(value**2 for value in values))
    return tuple(supports), tuple(energies), tuple(failures)


def verify_candidate(upper, lower, u, v, pivot_a, pivot_b, flips_a, flips_b, projection):
    n, m = len(upper), len(lower)
    assert len(set(flips_a)) == 32 and len(set(flips_b)) == 34
    x = upper[pivot_a] ^ sum(1 << i for i in flips_a)
    y = lower[pivot_b] ^ sum(1 << i for i in flips_b)
    assert dot(n, u, x) == dot(m, v, y) == 0
    assert tuple(dot(m, y, lower[j]) // 2 for j in LOWER_OMITTED) == projection
    assert (projection, 0) in projection_targets(upper, lower, v, LOWER_OMITTED)
    top_dots, top_deck = signatures(upper, u, x)
    lower_dots, lower_deck = signatures(lower, v, y)
    pairing = sorted_pairing(top_deck, lower_deck)
    assert set(pairing) == set(range(n)) and set(pairing.values()) == set(range(m)) - set(LOWER_OMITTED)
    residues = [0] * m
    old = []
    for i, col in enumerate(upper):
        j = pairing[i]
        a1, a2 = top_dots[i]
        b1, b2 = lower_dots[j]
        sign = -1 if (a1 or a2) * (b1 or b2) > 0 else 1
        assert a1 + sign * b1 == 0
        residues[j] = sign * a2 + b2
        low = lower[j] if sign > 0 else lower[j] ^ ((1 << m) - 1)
        old.append(col | low << n)
    old.append(u | v << n)
    assert verify_orthogonal(n + m, old) == 715806
    second = x | y << n
    dots = Counter(abs(dot(n + m, col, second)) for col in old)
    assert Counter(map(abs, residues)) == dots + Counter({0: 3})
    digest = sha256(''.join(f'{col:x}\n' for col in [*old, second]).encode('ascii')).hexdigest()
    return dots, digest, check_channel_support(residues)


def main():
    upper, lower, u, v = sources()
    dots, digest, channel_data = verify_candidate(upper, lower, u, v, UPPER_PIVOT, LOWER_PIVOT,
                                                 UPPER_FLIPS, LOWER_FLIPS, (30, -34, -4, 18))
    assert dots == {0: 1067, 4: 130}
    assert digest == '41062f6b119457dbda4c53c2740a52087443fffe4526f16174838e436c75b40a'
    assert channel_data == ((50, 13, 11, 56), (800, 208, 176, 896), (148, 147, 105, 141))
    print('Four-channel next column: 1067 exact products, 130 of magnitude four, energy 2080')
    print('Four-channel next-column packed SHA256', digest)
    print('Four-channel mod5: independent residual supports (50, 13, 11, 56); 596 protected exact slots')

    dots, digest, channel_data = verify_candidate(upper, lower, u, v, 120, 1190,
                                                 LOW_ENERGY_UPPER, LOW_ENERGY_LOWER, (-34, 30, -18, 4))
    assert dots == {0: 1079, 4: 116, 8: 2}
    assert digest == '2b412687810b7697cf045a3d433a780aacf2a19b5f0b0a9633f4fbc0426a69b1'
    assert channel_data == ((36, 14, 14, 54), (624, 272, 224, 864), (145, 147, 146, 143))
    print('Four-channel next column: 1079 exact products, 116 of magnitude four, two of eight, energy 1984')
    print('Four-channel lower-energy packed SHA256', digest)


if __name__ == '__main__':
    main()
