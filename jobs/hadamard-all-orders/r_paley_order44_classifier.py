"""Classify every Paley H(20) exterior at order 44."""

from collections import Counter, defaultdict
from itertools import combinations, product

from r_paley_isotropic_code import assemble, dot, maximal_set
from verify import paley, rows_from_columns, verify_orthogonal


TRACE_RESIDUES = {
    32: {44, 96, 142, 159, 174},
    36: {11, 12, 23, 36, 37, 53, 63, 72, 80, 81, 85, 95, 103, 109,
         116, 120, 145, 150, 161, 166, 195},
    44: {6, 31, 52, 73, 79, 86, 90, 110, 149, 179, 193, 196},
}


def bits(indices):
    return sum(1 << i for i in indices)


def generators(source):
    q, m = 19, 20
    skew = [source[0] ^ ((1 << m)-1), *source[1:]]
    translation = (0,) + tuple(1+i % q for i in range(1, m))
    inverse = (1, 0) + tuple(1+(-pow(i-1, -1, q)) % q for i in range(2, m))
    signs = 2 | bits(1+x*x % q for x in range(1, (q+1)//2))
    for i, j in product(range(m), repeat=2):
        entry = skew[j] >> i & 1
        assert entry == (skew[translation[j]] >> translation[i] & 1)
        assert entry == (skew[inverse[j]] >> inverse[i] & 1) ^ ((signs >> i ^ signs >> j) & 1)
    return translation, inverse


def act(mask, permutation):
    image = 0
    while mask:
        bit = mask & -mask
        image |= 1 << permutation[bit.bit_length()-1]
        mask ^= bit
    return image


def exterior_orbits(source):
    operations = generators(source)
    remaining = {bits(indices) for indices in combinations(range(20), 12)}
    assert len(remaining) == 125970
    while remaining:
        seed = min(remaining)
        found, queue = {seed}, [seed]
        for mask in queue:
            for permutation in operations:
                image = act(mask, permutation)
                if image not in found:
                    found.add(image)
                    queue.append(image)
        assert found <= remaining
        remaining.difference_update(found)
        yield seed, len(found)


def trace_six(source, unused):
    rows = rows_from_columns(20, [source[j] for j in unused])
    forms = [[((8-2*(left ^ right).bit_count())**2-8)//4 - 14*(i == j)
              for j, right in enumerate(rows)] for i, left in enumerate(rows)]
    squared = [[dot(row, col) for col in forms] for row in forms]
    return sum(dot(row, col)**2 for row in squared for col in forms)


def reduced_rows(matrix, p):
    rows = [list(x % p for x in row) for row in matrix]
    rank, pivots = 0, []
    for j in range(len(rows[0])):
        source = next((i for i in range(rank, len(rows)) if rows[i][j]), None)
        if source is None:
            continue
        rows[rank], rows[source] = rows[source], rows[rank]
        inverse = pow(rows[rank][j], -1, p)
        rows[rank] = [x*inverse % p for x in rows[rank]]
        for i, row in enumerate(rows):
            if i != rank and (factor := row[j]):
                rows[i] = [(a-factor*b) % p for a, b in zip(row, rows[rank], strict=True)]
        pivots.append(j)
        rank += 1
    return rows[:rank], pivots


def norm_eleven_candidates():
    profiles = ((3, 1, 1), (2, 2, 1, 1, 1), (2, 1, 1, 1, 1, 1, 1, 1))
    for profile in profiles:
        for support in combinations(range(8), len(profile)):
            heavy = sum(x > 1 for x in profile)
            for selected in combinations(support, heavy):
                large = set(selected)
                magnitudes = [profile[0] if j in large else 1 for j in support]
                for orientation in product((-1, 1), repeat=len(support)-1):
                    vector = [0]*8
                    for j, magnitude, sign in zip(support, magnitudes, (1,*orientation), strict=True):
                        vector[j] = magnitude*sign
                    yield tuple(vector)


def reserve_basis(vectors):
    basis, pivots = reduced_rows(vectors, 11)
    assert len(basis) == len(pivots) == 4
    lattice_basis = [v for v in norm_eleven_candidates() if all(dot(v, u) % 11 == 0 for u in basis)]
    assert len(lattice_basis) == 8 and all(dot(x, x) == 11 for x in lattice_basis)
    assert all(not dot(x, y) for x, y in combinations(lattice_basis, 2))
    assert len(reduced_rows(lattice_basis, 11)[1]) == 4
    return lattice_basis


def subset_projections(columns):
    values = [(0,)*len(columns[0])]
    for column in columns:
        values += [tuple((a+b) % 5 for a, b in zip(row, column, strict=True)) for row in values]
    return values


def code_signs(matrix):
    rows, pivots = reduced_rows(matrix, 5)
    assert len(pivots) == 10 and all(dot(x, y) % 5 == 0 for x in rows for y in rows)
    columns = list(zip(*rows, strict=True))
    target = [3*sum(row) % 5 for row in rows]
    right = defaultdict(list)
    for mask, projection in enumerate(subset_projections(columns[10:])):
        right[projection].append(mask)
    for mask, projection in enumerate(subset_projections(columns[:10])):
        if not (mask & 1):  # One word for each antipodal line.
            needed = tuple((a-b) % 5 for a, b in zip(target, projection, strict=True))
            for other in right.get(needed, ()):
                yield mask | (other << 10)


def lattice_roots(matrix):
    rows, pivots = reduced_rows(matrix, 5)
    free = [i for i in range(20) if i not in pivots]
    canonical = (0, 1, 2, -2, -1)
    factors = [tuple(tuple(-coefficient*row[j] % 5 for row in rows) for coefficient in canonical)
               for j in free]
    units, roots = 0, 0

    def search(j, weight, twos, dependent):
        nonlocal units, roots
        if j == len(free):
            entries = tuple(canonical[x] for x in dependent)
            weight += sum(x*x for x in entries)
            if weight == 5:
                units += 1
                # A coordinate of absolute value two may instead lift to three.
                roots += twos + sum(abs(x) == 2 for x in entries)
            elif weight == 10:
                roots += 1
            return
        search(j+1, weight, twos, dependent)
        for x, projection in zip(canonical[1:], factors[j][1:], strict=True):
            if weight+x*x <= 10:
                updated = tuple((a+b) % 5 for a, b in zip(dependent, projection, strict=True))
                search(j+1, weight+x*x, twos+(abs(x) == 2), updated)

    search(0, 0, 0, (0,)*len(pivots))
    return units, roots


def lattice_control(source, chosen, unused, compatible, check_roots):
    vectors = [tuple(10-(source[j] ^ z).bit_count() for j in unused) for z in compatible]
    q = reserve_basis(vectors)
    matrix = []
    for i in range(20):
        sign = [2*(col >> i & 1)-1 for col in source]
        matrix.append([sign[j] for j in chosen] + [dot([sign[j] for j in unused], c) for c in q])
    assert all(all(v % 2 for v in row) for row in matrix)
    sums = {sum(row) % 4 for row in matrix}
    assert len(sums) == 1
    want_parity = ((sums.pop()-2)//2) % 2
    recovered = set()
    for mask in code_signs(matrix):
        assert mask.bit_count() % 2 == want_parity
        vector = [1-2*(mask >> i & 1) for i in range(20)]
        numerators = [dot(row, vector) for row in matrix]
        assert all(abs(value) == 10 for value in numerators)
        packed = bits(i for i, value in enumerate(numerators) if value > 0)
        recovered.add(packed if packed & 1 else packed ^ ((1 << 20)-1))
    assert recovered == set(compatible)
    if check_roots:
        assert lattice_roots(matrix) == (0, 120+32*len(compatible))


def verify(check_roots=False):
    source = paley(19)
    assert verify_orthogonal(20, source) == 190
    eligible = []
    for z in range(1, 1 << 20, 2):
        hits = bits(j for j, c in enumerate(source) if abs(10-(z ^ c).bit_count()) == 1)
        if hits.bit_count() >= 12:
            eligible.append((z, hits))
    assert len(eligible) == 242080

    orbits, outcomes, orbit_sizes = Counter(), Counter(), Counter()
    trace_values = set()
    residues = defaultdict(set)
    lattice_cases = set()
    for mask, size in exterior_orbits(source):
        chosen = [j for j in range(20) if mask >> j & 1]
        unused = [j for j in range(20) if not (mask >> j & 1)]
        lower = [z for z, hits in eligible if hits & mask == mask]
        vectors = [tuple(10-(source[j] ^ z).bit_count() for j in unused) for z in lower]
        assert all(all(x % 2 for x in row) and dot(row, row) == 88 for row in vectors)
        frame = maximal_set(11, vectors, 20)
        compatible = [lower[j] for j in frame]
        cols = assemble(11, source, chosen, compatible)
        width = len(cols)
        assert width == len(frame)+24 and verify_orthogonal(44, cols) == width*(width-1)//2
        orbit_sizes[size] += 1
        orbits[width] += 1
        outcomes[width] += size

        value = trace_six(source, unused)
        assert value % 256 == 0
        trace_values.add(value)
        residues[width].add(value//256 % 203)
        if width not in lattice_cases and len(reduced_rows([vectors[j] for j in frame], 11)[1]) == 4:
            lattice_control(source, chosen, unused, compatible, check_roots)
            lattice_cases.add(width)

    assert orbit_sizes == {3420:29, 1710:13, 855:3, 570:3, 285:1}
    assert orbits == {32:8, 36:26, 44:15}
    assert outcomes == {32:24510, 36:69255, 44:32205}
    assert len(trace_values) == 40 and residues == TRACE_RESIDUES
    assert lattice_cases == {32, 36, 44}
    print('Order 44: 49 orbits, widths 32/36/44 in 24510/69255/32205 of 125970 exterior choices')
    print('Order 44: sixth pair-product Gram trace separates all three maximal widths')
    print('Order 44: exact F5 characteristic-word lift in all three width classes')
    if check_roots:
        print('Order 44: no unit vectors; 376/504/760 lattice roots in the three controls')


if __name__ == '__main__':
    import argparse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lattice-roots', action='store_true')
    verify(parser.parse_args().lattice_roots)
