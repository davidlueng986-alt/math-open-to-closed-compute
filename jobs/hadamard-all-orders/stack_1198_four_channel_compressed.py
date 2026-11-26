"""Verify the compressed odd checks and a fixed-word modulo-32 obstruction."""

from collections import Counter
from itertools import product

from stack_1197_four_channels import LOWER_OMITTED, sources
from stack_1198_channels import signatures
from stack_1198_four_channel_mod16 import verify as verify_mod16
from stack_1198_four_channels import (
    LOWER_FLIPS, LOWER_PIVOT, LOW_ENERGY_LOWER, LOW_ENERGY_UPPER, SHARP_CAP_LOWER,
    SHARP_CAP_UPPER, UPPER_FLIPS, UPPER_PIVOT, common_basis, conference_graph_columns,
)
from stack_odd_t_residual import sylvester_four


SYLVESTER = tuple(tuple(1 - 2 * ((i & j).bit_count() % 2) for j in range(4)) for i in range(4))


def dot(left, right):
    return sum(a * b for a, b in zip(left, right, strict=True))


def odd_checks():
    residues = verify_mod16()
    channels = [tuple(r // 4 for r in residues[i:i + 300]) for i in range(0, len(residues), 300)]
    local = list(zip(*channels, strict=True))
    assert all(sum(bool(x) for x in row) % 2 == 0 for row in local)
    active = {i for i, row in enumerate(local) if any(row)}
    omitted_bases = {j % 300 for j in LOWER_OMITTED}
    assert len(active) == 60 and not active & omitted_bases
    graph = conference_graph_columns()
    index_set = common_basis(graph, active, omitted_bases, (3, 5, 13))
    assert len(index_set) == 150 and not index_set & omitted_bases

    ternary_forms = ((-1, -1, 1, 0), (-1, 1, 0, 1))
    mod13_form = (1, 2, 3, 5)
    even_patterns = [a for a in product((-1, 0, 1), repeat=4) if sum(bool(s) for s in a) % 2 == 0]
    assert len(even_patterns) == 41
    assert [a for a in even_patterns if all(dot(a, row) % 3 == 0 for row in ternary_forms)] == [(0, 0, 0, 0)]
    assert [a for a in even_patterns if dot(a, mod13_form) % 13 == 0] == [(0, 0, 0, 0)]
    assert all(any(any(a) and dot(a, row) % 3 == 0 for a in even_patterns)
               for row in product(range(3), repeat=4))

    def violations(form, modulus):
        combined = [dot(form, a) for a in local]
        return sum(sum(graph[j][i] * combined[j] for j in active) % modulus != 0 for i in range(150))

    defects = tuple(violations(row, 3) for row in ternary_forms)
    prime_13 = violations(mod13_form, 13)
    print('Four-channel odd controls: 60 active base positions in a common F3/F5/F13 basis; 596 protected positions')
    print(f'Four-channel checks: two mod3 systems 150 rows each, one mod13 system 150 rows; current failed rows {defects}, {prime_13}')


def signature_mod8(first, second):
    if first > 0:
        return first, second % 8
    if first < 0:
        return -first, -second % 8
    return 0, min(second % 8, -second % 8)


def affine_separation(vectors, target, dimension):
    basis = {}
    for vector in vectors:
        while vector:
            position = vector.bit_length() - 1
            if position not in basis:
                basis[position] = vector
                break
            vector ^= basis[position]
    reductions = sorted(basis.items(), reverse=True)

    def reduce(word):
        for position, vector in reductions:
            if word >> position & 1:
                word ^= vector
        return word

    residual = reduce(target)
    assert residual
    coordinate = residual.bit_length() - 1
    dual = sum(((reduce(1 << j) >> coordinate) & 1) << j for j in range(dimension))
    assert (target & dual).bit_count() % 2 == 1
    assert all((vector & dual).bit_count() % 2 == 0 for vector in vectors)
    return len(basis), dual.bit_count()


def prove_fixed_words():
    upper, lower, u, v = sources()
    cases = (
        (1920, 411, 30, SHARP_CAP_UPPER, SHARP_CAP_LOWER, (74576, 74592), 357),
        (1984, 120, 1190, LOW_ENERGY_UPPER, LOW_ENERGY_LOWER, (74384, 74392), 356),
        (2080, UPPER_PIVOT, LOWER_PIVOT, UPPER_FLIPS, LOWER_FLIPS, (74856, 74880), 357),
    )
    base_side = 300
    base = [column & ((1 << base_side) - 1) for column in lower[:base_side]]
    assert lower == sylvester_four(base)
    row0 = [2 * (column & 1) - 1 for column in base]
    states_by_mask = {}
    for values in product(range(8), repeat=4):
        transform = [dot(values, row) for row in SYLVESTER]
        if any(value % 2 for value in transform):
            continue
        mask = tuple(value // 2 % 2 for value in transform)
        by_orientation = states_by_mask.setdefault(mask, {1: [], -1: []})
        for sign, states in by_orientation.items():
            phase = sum((((value - 2 * c * sign) // 4) % 2) << j
                        for j, (value, c) in enumerate(zip(transform, mask, strict=True)))
            states.append((values, phase))
    assert set(states_by_mask) == {bits for bits in product(range(2), repeat=4) if sum(bits) % 2 == 0}
    assert all(len(states[1]) == len(states[-1]) == 256 for states in states_by_mask.values())

    for energy, upper_pivot, lower_pivot, upper_flips, lower_flips, expected_range, expected_rank in cases:
        x = upper[upper_pivot] ^ sum(1 << i for i in upper_flips)
        y = lower[lower_pivot] ^ sum(1 << i for i in lower_flips)
        upper_dots, _ = signatures(upper, u, x)
        lower_dots, _ = signatures(lower, v, y)
        assert all(q % 4 == 0 for _, q in (*upper_dots, *lower_dots))
        supply = Counter(signature_mod8(p, q // 4) for p, q in upper_dots)
        slot = {signature: i for i, signature in enumerate(sorted(supply), 300)}
        phase_start = 300 + len(slot)
        demands = []
        for index, (p, q) in enumerate(lower_dots):
            if index in LOWER_OMITTED:
                demands.append((0, *([-1] * 7)))
            else:
                keys = [signature_mod8(p, q // 4 - value) for value in range(8)]
                demands.append(tuple(1 << slot[key] if key in slot else -1 for key in keys))

        target = ((1 << 300) - 1) | sum((copies % 2) << slot[key] for key, copies in supply.items())
        sizes, dual_sizes = [], []
        for by_orientation in states_by_mask.values():
            vectors = []
            for j in range(base_side):
                a, b, c, d = demands[j::base_side]
                for (x0, x1, x2, x3), phase in by_orientation[row0[j]]:
                    bits = (a[x0], b[x1], c[x2], d[x3])
                    if min(bits) < 0:
                        continue
                    parity = bits[0] ^ bits[1] ^ bits[2] ^ bits[3]
                    vectors.append((1 << j) | parity | (phase << phase_start))
            rank, dual_terms = affine_separation(vectors, target, phase_start + 4)
            assert rank == expected_rank
            sizes.append(len(vectors))
            dual_sizes.append(dual_terms)

        assert (min(sizes), max(sizes)) == expected_range
        print(f'Four-channel E{energy} fixed words: all eight Walsh classes excluded; '
              f'{min(sizes)}–{max(sizes)} states per class, GF2 rank {expected_rank}, '
              f'{min(dual_sizes)}–{max(dual_sizes)} dual coordinates')


if __name__ == '__main__':
    odd_checks()
    prove_fixed_words()
