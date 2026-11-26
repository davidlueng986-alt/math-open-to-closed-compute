"""Exact saturation of the one-flip family on fixed physical exteriors."""

from itertools import combinations

from r_paley_full92_skew import build_source
from r_paley_full92_unrestricted import NEXT_SELECTED
from r_paley_punctured_fibre import ALT_SELECTED
from verify import rows_from_columns, verify_orthogonal


WARM_SELECTED = int(
    "d5c38b0c64aabc97367bf4537a84cbdd9858c1078d2cd1c2ec385592e64a64c1"
    "b0cd06a9e7dde859b0e85163dac29a6aad361d3f7df0ec12719ba21c34c227a3"
    "b35dd92806723be7c73c9737adae75f0e431143a65dca6dbe515aa5c174a8c65"
    "99c459087dd5db96200c4456603ba749bed965cb5c8c723f8d624b2b1d26f496"
    "2fb251fe6d85708120c96c4ab488b56fdbae9f2d695",
    16,
)
WARM_CEILING = 128
WARM_EDGES = (102426, 96759, 91847, 83986, 70531, 49943, 21917, 1789, 152, 105, 0)


def verify_exterior(source, selected_mask, expected_ceiling, expected_counts):
    selected = [j for j in range(1196) if selected_mask >> j & 1]
    assert len(selected) == selected_mask.bit_count() == 600
    rows = rows_from_columns(1196, [source[j] for j in selected])
    graph = [0] * len(rows)
    ceiling = 0
    for (i, u), (j, v) in combinations(enumerate(rows), 2):
        correlation = abs(600 - 2 * (u ^ v).bit_count())
        ceiling = max(ceiling, correlation)
        if correlation <= 2:
            graph[i] |= 1 << j
            graph[j] |= 1 << i
    assert ceiling == expected_ceiling < 596
    counts = [sum(word.bit_count() for word in graph) // 2]
    while counts[-1]:
        reduced = graph.copy()
        for i, neighbors in enumerate(graph):
            pending = neighbors >> (i + 1)
            while pending:
                bit = pending & -pending
                j = i + bit.bit_length()
                pending ^= bit
                if (neighbors & graph[j]).bit_count() < 16:
                    reduced[i] ^= 1 << j
                    reduced[j] ^= 1 << i
        next_count = sum(word.bit_count() for word in reduced) // 2
        assert next_count < counts[-1]
        counts.append(next_count)
        graph = reduced
    assert tuple(counts) == expected_counts
    assert not any(graph)
    print(f"Fixed physical exterior, maximum row correlation {ceiling}, no family of 18 one-flips")
    print("Edge counts:", *counts)


def verify():
    source = build_source()
    assert verify_orthogonal(1196, source) == 714610
    verify_exterior(source, NEXT_SELECTED, 128,
                    (102360, 96367, 90936, 82190, 67235, 44206, 16139, 857, 106, 0))
    verify_exterior(source, ALT_SELECTED, 122,
                    (101428, 95019, 88704, 77787, 57724, 27913, 3517, 156, 16, 0))
    verify_exterior(source, WARM_SELECTED, WARM_CEILING, WARM_EDGES)


if __name__ == "__main__":
    verify()
