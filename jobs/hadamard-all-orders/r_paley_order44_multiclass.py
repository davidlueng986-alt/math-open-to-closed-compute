"""Replay the exhaustive exterior census for the three H(20) classes."""

import argparse
from collections import Counter, defaultdict
from itertools import combinations
import json
from pathlib import Path

from r_paley_isotropic_code import assemble, dot, half_projections, maximal_set
from r_paley_order44_classifier import act, bits, code_signs, reduced_rows, reserve_basis, trace_six
from verify import rows_from_columns, verify_orthogonal


DATA = Path(__file__).with_name('r_paley_order44_multiclass_data.json')
SIDE = 20
FULL = (1 << SIDE)-1
INDICES = range(SIDE)
WIDTHS = (32, 36, 44)


def signs(word):
    return tuple(2*(word >> i & 1)-1 for i in INDICES)


def verify_actions(source, data):
    operations = []
    for row_order, col_order, row_signs, col_signs in data:
        rows = [int(i, 20) for i in row_order]
        cols = [int(i, 20) for i in col_order]
        row_bits, col_bits = int(row_signs, 16), int(col_signs, 16)
        assert set(rows) == set(cols) == set(INDICES)
        for a in INDICES:
            for b in INDICES:
                assert (source[b] >> a & 1) == (
                    (source[cols[b]] >> rows[a]) ^ (row_bits >> a) ^ (col_bits >> b)
                ) & 1
        operations.append(cols)
    return operations


def exterior_orbits(operations):
    remaining = {bits(indices) for indices in combinations(INDICES, 12)}
    assert len(remaining) == 125970
    while remaining:
        seed = min(remaining)
        seen, queue = {seed}, [seed]
        for mask in queue:
            for operation in operations:
                image = act(mask, operation)
                if image not in seen:
                    seen.add(image)
                    queue.append(image)
        assert seen <= remaining
        remaining.difference_update(seen)
        yield seed, len(seen)


def physical_words(source):
    for z in range(1, 1 << SIDE, 2):
        hits = bits(j for j, col in enumerate(source) if abs(10-(z ^ col).bit_count()) == 1)
        if hits.bit_count() >= 12:
            yield z, hits


def wrong_phase_words(source):
    for support in combinations(INDICES, 5):
        mask = bits(support)
        orientations = [1 << support[0]]
        for i in support[1:]:
            orientations += [word | (1 << i) for word in orientations]
        for word in orientations:
            projections = tuple(5-2*((col ^ word) & mask).bit_count() for col in source)
            hits = bits(j for j, x in enumerate(projections) if abs(x) == 1)
            if hits.bit_count() >= 12:
                yield projections, hits


def code_roots(matrix):
    rows, pivots = reduced_rows(matrix, 5)
    assert len(pivots) == 10
    free = [i for i in INDICES if i not in pivots]
    lifts = (0, 1, 2, -2, -1)
    contributions = [tuple(tuple(-value*row[i] % 5 for row in rows) for value in lifts) for i in free]
    partial = [0]*len(free)

    def enumerate_lifts(j, weight, dependent):
        if j == len(free):
            fixed = tuple(lifts[x] for x in dependent)
            total = weight + sum(x*x for x in fixed)
            if total not in (5, 10):
                return
            vector = [0]*SIDE
            for i, x in zip(free, partial, strict=True):
                vector[i] = x
            for i, x in zip(pivots, fixed, strict=True):
                vector[i] = x
            if total == 10:
                yield tuple(vector)
            else:
                yield tuple(vector)
                for i, x in enumerate(vector):
                    if abs(x) == 2:
                        alternate = vector.copy()
                        alternate[i] = -3 if x == 2 else 3
                        yield tuple(alternate)
            return

        partial[j] = 0
        yield from enumerate_lifts(j+1, weight, dependent)
        for x, contribution in zip(lifts[1:], contributions[j][1:], strict=True):
            if weight+x*x <= 10:
                partial[j] = x
                updated = tuple((a+b) % 5 for a, b in zip(dependent, contribution, strict=True))
                yield from enumerate_lifts(j+1, weight+x*x, updated)

    return set(enumerate_lifts(0, 0, (0,)*len(pivots)))


def connected(roots):
    remaining = set(roots)
    queue = [remaining.pop()]
    for root in queue:
        neighbours = [other for other in remaining if dot(root, other)]
        remaining.difference_update(neighbours)
        queue.extend(neighbours)
    return not remaining


def check_components(source, chosen, unused, lowers, vectors):
    q = reserve_basis(vectors)
    matrix = []
    for i in INDICES:
        row = [2*(col >> i & 1)-1 for col in source]
        matrix.append([row[j] for j in chosen] + [dot([row[j] for j in unused], col) for col in q])
    residues = {sum(row) % 4 for row in matrix}
    assert len(residues) == 1
    parity = ((residues.pop()-2)//2) % 2
    frames = []
    recovered = set()
    for mask in code_signs(matrix):
        assert mask.bit_count() % 2 == parity
        frame = signs(mask)
        numerators = [dot(row, frame) for row in matrix]
        assert all(abs(x) == 10 for x in numerators)
        word = bits(i for i, x in enumerate(numerators) if x > 0)
        recovered.add(word if word & 1 else word ^ FULL)
        frames.append(frame)
    k = len(lowers)
    assert recovered == set(lowers)
    assert len(frames) == k and all(not dot(a, b) for a, b in combinations(frames, 2))

    roots = code_roots(matrix)
    assert all(dot(root, root) == 10 for root in roots)
    assert all(not any(dot(row, root) % 5 for row in matrix) for root in roots)
    attached = {root for root in roots if any(dot(root, char) for char in frames)}
    expected = {tuple((a*x+b*y)//2 for x,y in zip(u,v,strict=True))
                for u,v in combinations(frames,2) for a in (-1,1) for b in (-1,1)}
    assert attached == expected and len(attached) == 2*k*(k-1) and connected(attached)

    separate = roots-attached
    want = {8:264, 12:240, 20:0}
    assert len(separate) == want[k]
    if separate:
        assert connected(separate) and len(reduced_rows(separate, 101)[1]) == SIDE-k
    print(f'Order 44: attached D{k} component, {len(attached)} touching and {len(separate)} separate roots')


def verify_source(record, trace_widths, check_phase, check_root_components):
    raw = [int(row, 16) for row in record['rows'].split()]
    assert len(raw) == len(set(raw)) == SIDE and all(0 <= row <= FULL for row in raw)
    source = rows_from_columns(SIDE, raw)
    assert verify_orthogonal(SIDE, source) == 190
    operations = verify_actions(source, record['actions'])
    words = list(physical_words(source))
    assert len(words) == 242080
    even_words = list(wrong_phase_words(source)) if check_phase else []
    assert not check_phase or len(even_words) == 218880
    totals, phase_counts = Counter(), Counter()
    verified_components = set()
    orbit_count = 0
    for mask, size in exterior_orbits(operations):
        orbit_count += 1
        chosen = [i for i in INDICES if mask >> i & 1]
        unused = [i for i in INDICES if not (mask >> i & 1)]
        lower = [z for z, hits in words if hits & mask == mask]
        projections = (half_projections(source, z) for z in lower)
        vectors = [tuple(u[j] for j in unused) for u in projections]
        assert all(all(x % 2 for x in w) and dot(w, w) == 88 for w in vectors)
        frame = maximal_set(11, vectors, SIDE)
        selected = [lower[i] for i in frame]
        cols = assemble(11, source, chosen, selected)
        width = 24+len(frame)
        assert len(cols) == width and verify_orthogonal(44, cols) == width*(width-1)//2
        totals[width] += size
        trace = trace_six(source, unused)
        assert trace % 256 == 0
        assert trace_widths.setdefault(trace, width) == width

        if check_phase:
            wrong = [tuple(u[j] for j in unused) for u, hits in even_words if hits & mask == mask]
            assert all(dot(v, v) == 88 for v in wrong)
            phase_counts[(width, len(maximal_set(11, wrong, SIDE)))] += size
        if check_root_components and width not in verified_components:
            selected_vectors = [vectors[j] for j in frame]
            if len(reduced_rows(selected_vectors, 11)[1]) == 4:
                check_components(source, chosen, unused, selected, selected_vectors)
                verified_components.add(width)

    assert orbit_count == record['orbits'] and sum(totals.values()) == 125970
    assert totals == dict(zip(WIDTHS, record['widths'], strict=True))
    print(f"Order 44 {record['name']}: {orbit_count} orbits, widths 32/36/44 counts {record['widths']}", flush=True)
    if check_phase:
        assert phase_counts == {(a, b): total for a,b,total in record['phase']}
        print(f"Order 44 {record['name']}: exact wrong-phase maximum census", flush=True)
    if check_root_components:
        assert verified_components == set(WIDTHS)
    return totals


def verify(selection, check_phase, check_root_components):
    records = json.loads(DATA.read_text(encoding='ascii'))
    assert [r['name'] for r in records] == ['Williamson', 'Tonchev IV', 'Paley']
    trace_widths, totals = {}, Counter()
    for i, record in enumerate(records):
        if selection in (i, -1):
            totals.update(verify_source(record, trace_widths, check_phase, check_root_components and i == 2))
    if selection == -1:
        assert len(trace_widths) == 71 and totals == {32:52970, 36:246495, 44:78445}
        print('Order 44: all three H20 classes, 78445 of 377910 exteriors complete, 71 separating sixth traces')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=int, choices=(-1,0,1,2), default=-1)
    parser.add_argument('--wrong-phase', action='store_true')
    parser.add_argument('--root-components', action='store_true')
    args = parser.parse_args()
    verify(args.source, args.wrong_phase, args.root_components)
