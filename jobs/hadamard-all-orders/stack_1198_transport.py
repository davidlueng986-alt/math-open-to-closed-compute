"""Verify capped pairings of two jointly modulo-eight next-column witnesses."""

from collections import Counter, defaultdict
from hashlib import sha256
import json
from pathlib import Path

from stack_1197 import LOWER_FLIPS, LOWER_OMITTED, UPPER_FLIPS, flipped_column, source_matrices
from stack_1198_joint import dot, lower_channels, signature
from verify import verify_orthogonal


def grouped_values(first, second, omitted=()):
    groups = defaultdict(lambda: defaultdict(list))
    for index, (old, new) in enumerate(zip(first, second, strict=True)):
        if index not in omitted:
            groups[signature(old, new, 8)][signature(old, new)[1]].append(index)
    return groups


def sorted_values(group):
    return sorted(value for value, indices in group.items() for _ in indices)


def check_transport(upper, lower, cap, certificate):
    left, right = Counter(), Counter()
    p, q = dict(certificate["left_dual"]), dict(certificate["right_dual"])
    assert p.keys() == upper.keys() and q.keys() == lower.keys()
    penalty = sum(map(len, upper.values())) * cap**2 + 1

    def cost(a, b):
        return (a != b) * penalty + (a - b)**2

    for a in upper:
        for b in lower:
            if abs(a - b) <= cap:
                assert p[a] + q[b] <= cost(a, b)
    nonzero = energy = 0
    for a, b, count in certificate["plan"]:
        assert count > 0 and abs(a - b) <= cap
        assert p[a] + q[b] == cost(a, b)
        left[a] += count
        right[b] += count
        nonzero += (a != b) * count
        energy += (a - b)**2 * count
    assert left == Counter({a: len(indices) for a, indices in upper.items()})
    assert right == Counter({b: len(indices) for b, indices in lower.items()})
    return nonzero, energy


def pair_columns(upper_groups, lower_groups, groups):
    pairs = {}
    for group, certificate in groups:
        upper = {val: indices.copy() for val, indices in upper_groups[group].items()}
        lower = {val: indices.copy() for val, indices in lower_groups[group].items()}
        for a, b, count in certificate["plan"]:
            for _ in range(count):
                pairs[upper[a].pop()] = lower[b].pop()
        assert not any(upper.values()) and not any(lower.values())
    return pairs


def verify_columns(upper, lower, u, v, x, y, spectra, pairs, cap):
    n, m = len(upper), len(lower)
    first_a, second_a, first_b, second_b = spectra
    columns = []
    mask = (1 << m) - 1
    for i, column in enumerate(upper):
        j = pairs[i]
        choices = [sign for sign in (1, -1) if first_a[i] + sign * first_b[j] == 0
                   and (second_a[i] + sign * second_b[j]) % 8 == 0]
        sign = min(choices, key=lambda s: abs(second_a[i] + s * second_b[j]))
        attached = lower[j] if sign == 1 else lower[j] ^ mask
        columns.append(column | (attached << n))
    columns.append(u | (v << n))
    assert verify_orthogonal(n + m, columns) == 715806
    new = x | (y << n)
    dots = [dot(n + m, column, new) for column in columns]
    assert all(value % 8 == 0 for value in dots) and max(map(abs, dots)) == cap
    packed = "".join(f"{column:x}\n" for column in [*columns, new]).encode("ascii")
    return dots.count(0), sum(value**2 for value in dots), sha256(packed).hexdigest()


def check_cap16_curve(groups):
    strict_swaps = total_absolute = 0
    for _, certificate in groups:
        pairs = sorted((a, b) for a, b, count in certificate["plan"] for _ in range(count))
        left, right = map(list, zip(*pairs, strict=True))
        total_absolute += sum(abs(a - b) for a, b in pairs)
        for i in range(1, len(right)):
            j = i
            while j > 0 and right[j - 1] > right[j]:
                old = (left[j - 1] - right[j - 1], left[j] - right[j])
                right[j - 1], right[j] = right[j], right[j - 1]
                new = (left[j - 1] - right[j - 1], left[j] - right[j])
                assert max(map(abs, new)) <= 16 and sum(map(abs, old)) == sum(map(abs, new))
                if left[j - 1] < left[j]:
                    assert sorted(map(abs, old)) == [0, 16]
                    assert sorted(map(abs, new)) == [8, 8]
                    strict_swaps += 1
                else:
                    assert sorted(old) == sorted(new)
                j -= 1
        assert right == sorted(right)
    assert strict_swaps == 43 and total_absolute == 1160
    print("cap 16 full tradeoff: E + 128N = 27840 for every N from 100 through 143")


def verify_witness(name, record, upper, lower, u, v):
    n, m = len(upper), len(lower)
    witness = record["words"]
    flips = witness["upper_flips"]
    assert len(flips) == len(set(flips)) == 32 and all(0 <= i < n for i in flips)
    for support in (witness["dense_holes"], witness["sparse_support"]):
        assert len(support) == len(set(support)) == 34
        assert all(0 <= i < m // 2 for i in support)
    assert witness["sparse_sign"] in (-1, 1)
    x = upper[witness["upper_pivot"]] ^ sum(1 << i for i in flips)
    modified, y = lower_channels(lower, v, witness)
    assert verify_orthogonal(m, modified) == 719400
    assert dot(n, u, x) == dot(m, v, y) == 0
    first_a, second_a = ([dot(n, ref, col) for col in upper] for ref in (u, x))
    first_b, second_b = ([dot(m, ref, col) for col in modified] for ref in (v, y))
    assert first_b == [dot(m, v, col) for col in lower]
    assert tuple(second_b[j] // 2 for j in LOWER_OMITTED) == (18, 4, 34, -30)
    assert second_a[witness["upper_pivot"]] == second_b[witness["lower_pivot"]] == 1132
    spectra = (first_a, second_a, first_b, second_b)
    upper_groups = grouped_values(first_a, second_a)
    lower_groups = grouped_values(first_b, second_b, LOWER_OMITTED)
    assert upper_groups.keys() == lower_groups.keys()
    minimum_cap = max(
        abs(a - b) for group in upper_groups for a, b in zip(
            sorted_values(upper_groups[group]), sorted_values(lower_groups[group]), strict=True
        )
    )
    assert minimum_cap == record["bottleneck"]
    print(f"{name}: fixed-word bottleneck {minimum_cap}")
    for entry in record["caps"]:
        cap = entry["cap"]
        groups = [(tuple(group), certificate) for group, certificate in entry["groups"]]
        assert len(groups) == len(upper_groups) and {group for group, _ in groups} == upper_groups.keys()
        sums = [check_transport(upper_groups[group], lower_groups[group], cap, cert) for group, cert in groups]
        nonzero, energy = map(sum, zip(*sums, strict=True))
        assert (1197 - nonzero, energy) == (entry["exact_zeros"], entry["squared_residual"])
        pairs = pair_columns(upper_groups, lower_groups, groups)
        result = verify_columns(upper, modified, u, v, x, y, spectra, pairs, cap)
        assert result == (1197 - nonzero, energy, entry["packed_sha256"])
        print(f"cap {cap}: {1197 - nonzero} exact zeros; squared residual {energy}")
        if name == "frozen_1109" and cap == 16:
            assert (nonzero, energy) == (100, 15040)
            check_cap16_curve(groups)


def verify():
    path = Path(__file__).with_name("stack_1198_transport_data.json")
    records = json.loads(path.read_text(encoding="ascii"))
    assert set(records) == {"frozen_1109", "distinct_cap8"}
    assert [entry["cap"] for entry in records["frozen_1109"]["caps"]] == [16, 24, 32, 40]
    assert [entry["cap"] for entry in records["distinct_cap8"]["caps"]] == [8]
    upper, lower = source_matrices()
    u, v = flipped_column(len(upper), UPPER_FLIPS), flipped_column(len(lower), LOWER_FLIPS)
    for name, record in records.items():
        verify_witness(name, record, upper, lower, u, v)


if __name__ == "__main__":
    verify()
