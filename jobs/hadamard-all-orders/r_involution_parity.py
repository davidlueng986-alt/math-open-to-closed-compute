"""Exact design controls for the involution parity obstruction."""

from itertools import combinations

from verify import rows_from_columns


def replay(t, pairs, representatives, fixed_blocks):
    def image(word):
        for a, b in pairs:
            if ((word >> a) ^ (word >> b)) & 1:
                word ^= (1 << a) | (1 << b)
        return word

    assert len({i for pair in pairs for i in pair}) == 2 * len(pairs)
    assert all(image(b) == b for b in fixed_blocks)
    assert all(b < image(b) for b in representatives)
    blocks = (*fixed_blocks, *representatives, *map(image, representatives))
    assert len(set(blocks)) == len(blocks) == 4 * t - 2
    assert all(b.bit_count() == t for b in blocks)
    incidence = rows_from_columns(2 * t, blocks)
    assert all(x.bit_count() == 2 * t - 1 for x in incidence)
    assert all((x & y).bit_count() == t - 1 for x, y in combinations(incidence, 2))

    differences = [tuple(((word >> a) & 1) - ((word >> b) & 1) for a, b in pairs)
                   for word in representatives]
    for i in range(len(pairs)):
        for j in range(len(pairs)):
            assert sum(row[i] * row[j] for row in differences) == t * (i == j)
    sums = tuple(map(sum, differences))
    assert sum(n*n for n in sums) == t * len(pairs)
    return sums


def verify():
    sums = replay(
        5, ((0, 1), (2, 3), (4, 5), (6, 7), (8, 9)),
        (117, 214, 309, 331, 334, 403, 428, 793, 976), (),
    )
    assert len(sums) == 9 and all(n % 2 for n in sums)

    reps = (1509, 1878, 2955, 4984, 5326, 6556, 8677, 9099, 10006, 13160, 13514, 14740)
    sums = replay(
        7, ((0, 3), (1, 4), (2, 5), (6, 9), (7, 10), (8, 11)),
        reps, (4159, 8255),
    )
    assert sum(n % 2 for n in sums) == 6
    assert sum(n % 4 == 2 for b, n in zip(reps, sums, strict=True)
               if (b >> 12).bit_count() == 1) == 3
    print("Outer design involutions: fixed-free R(5) and two-fixed-point R(7) verified")
    print("At two fixed points, R(7) has three singleton-fixed orbit sums equal to two modulo four")


if __name__ == "__main__":
    verify()
