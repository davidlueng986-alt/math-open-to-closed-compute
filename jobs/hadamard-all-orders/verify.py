"""Exact integer checks of the all-order reductions and one standalone 2396-column-length witness."""

from fractions import Fraction
from itertools import combinations
from math import comb, isqrt


def require(condition, message):
    if not condition:
        raise ValueError(message)


def verify_orthogonal(n, columns):
    require(all(0 <= word < 1 << n for word in columns), "column outside row range")
    for i, left in enumerate(columns):
        for j in range(i):
            require(2 * (left ^ columns[j]).bit_count() == n, f"dot product at {i}, {j}")
    return comb(len(columns), 2)


def rows_from_columns(n, columns):
    return [sum(1 << i for i, col in enumerate(columns) if col >> r & 1) for r in range(n)]


def paley(p):
    """Normalized Paley-I columns over the prime field, with bit 1 representing +1."""
    require(p % 4 == 3 and all(p % d for d in range(2, isqrt(p) + 1)), "expected prime 3 mod 4")
    squares = {i * i % p for i in range(1, p)}
    columns = [(1 << (p + 1)) - 1]
    for j in range(p):
        positives = (i + 1 for i in range(p) if (j - i) % p in squares)
        columns.append(1 + sum(1 << r for r in positives))
    return columns


def check_marginals(t, y, x):
    m = 4 * t - 2
    require(len(y) == 2 * t, "Y column count")
    for row in range(m):
        require(sum((v >> row) & 1 for v in y) == t, "Y row size")
    for group, size, common in [(y, 2 * t - 1, t - 1), (x, 2 * t - 2, t - 2)]:
        require(all(w.bit_count() == size for w in group), "marginal column size")
        require(all((a & b).bit_count() == common for a, b in combinations(group, 2)), "marginal pair")


def permutation_swap(word, i, j):
    if (word >> i ^ word >> j) & 1:
        return word ^ (1 << i | 1 << j)
    return word


def check_fractional_prefixes(t, y, full_x):
    m = 4 * t - 2
    loads = [0] * m
    for j, new in enumerate(full_x):
        slots_left = 2 * t - 1 - j
        need = [t - 1 - d for d in loads]
        require(all(0 <= d <= slots_left for d in need), "capacity")
        require(sum(need) == slots_left * (2 * t - 2), "fractional mass")
        for group, want in ((y, t - 1), (full_x[:j], t - 2)):
            for column in group:
                value = sum(d for r, d in enumerate(need) if column & (1 << r))
                require(value == slots_left * want, "fractional intersection")
        for r in range(m):
            loads[r] += (new >> r) & 1
    require(loads == [t - 1] * m, "final inner row loads")


def determinant(matrix):
    work = [list(map(Fraction, row)) for row in matrix]
    result = Fraction(1)
    for j in range(len(work)):
        pivot = next((i for i in range(j, len(work)) if work[i][j]), None)
        if pivot is None:
            return 0
        if pivot != j:
            work[j], work[pivot] = work[pivot], work[j]
            result = -result
        result *= work[j][j]
        for i in range(j + 1, len(work)):
            scale = work[i][j] / work[j][j]
            work[i] = [v - scale * w for v, w in zip(work[i], work[j], strict=True)]
    return result


def check_fractional_vertex(y):
    # Six times a vertex of the first rounding polytope of our order-20 example.
    numerators = (6, 0, 0, 0, 0, 5, 6, 4, 0, 4, 0, 4, 3, 0, 3, 2, 5, 6)
    require(sum(numerators) == 6 * 8 and all(0 <= v <= 6 for v in numerators), "vertex mass and box")
    for col in y:
        require(sum(v for r, v in enumerate(numerators) if col & (1 << r)) == 6 * 4, "vertex counts")
    free = [r for r, v in enumerate(numerators) if 0 < v < 6]
    minor = [[(col >> r) & 1 for r in free] for col in y[:8]]
    require(len(free) == 8 and determinant(minor) == 12, "vertex must be uniquely pinned by its active bounds")
    print("n=20: exact nonintegral vertex with 8 fractional entries, nonzero minor determinant 12")


def check_extraction(t):
    n, h = 4 * t, 2 * t - 8
    columns = paley(n - 1)
    verify_orthogonal(n, columns)
    outside = [w for w in columns[1:] if not w & 2]
    inside = [w for w in columns[1:] if w & 2]
    require(len(inside) == 2 * t - 1, "full interior size")
    y, full_x = [w >> 2 for w in outside], [w >> 2 for w in inside]
    x = full_x[:h]
    check_marginals(t, y, full_x)
    check_fractional_prefixes(t, y, full_x)
    if t == 5:
        check_fractional_vertex(y)
    require(all((a & b).bit_count() == t - 1 for a in y for b in full_x), "mixed pairs")
    assembled = [(1 << n) - 1] + [(v << 2) | 1 for v in y] + [(v << 2) | 3 for v in x]
    require(assembled == [columns[0]] + outside + inside[:h], "border reconstruction")
    require(len(assembled) == n - 7, "completion width")
    verify_orthogonal(n, assembled)

    blocks = [sum(((v >> r) & 1) << j for j, v in enumerate(y)) for r in range(n - 2)]
    if t == 5:
        cuts = [sum(1 << i for i in half) for half in combinations(range(2 * t), t)]
    else:
        cuts = blocks
    for cut in cuts:
        deviations = [2 * (cut & block).bit_count() - t for block in blocks]
        require(sum(v * v for v in deviations) == 2 * t * t, "outer energy")
        require(sum(abs(v) == t for v in deviations) <= 1, "pure blocks")

    row = 0
    seed = [v ^ (1 << row) for v in y if (v >> row) & 1][:min(t, h)]
    require(len(seed) == min(t, h), "seed width")
    check_marginals(t, y, seed)

    # A column family can pass both marginal checks and still fail the mixed tests.
    for i, j in combinations(range(n - 2), 2):
        swapped = [permutation_swap(v, i, j) for v in x]
        bad = sum((a & b).bit_count() != t - 1 for a in y for b in swapped)
        if bad:
            check_marginals(t, y, swapped)
            print(f"n={n}: reconstructed {n-7} columns; swapping X rows {i},{j} breaks {bad} mixed counts")
            return
    raise ValueError("expected an incompatible row permutation")


def check_blocked_prefix():
    t = 7
    blocks = (
        885, 1819, 2174, 2667, 3245, 3544, 4551, 5546, 5857, 5940, 6866, 7052,
        7191, 8678, 8892, 9395, 10058, 11153, 11589, 11910, 12505, 12815, 13404,
        14633, 14642, 15968,
    )
    m = len(blocks)
    y = [sum(1 << r for r, block in enumerate(blocks) if block >> j & 1) for j in range(2*t)]
    check_marginals(t, y, [])

    # Since YᵀY = I over F₂, project each row basis vector by I + YYᵀ.
    # These projections span exactly ker(Yᵀ), which contains every candidate.
    basis = {}
    for r, block in enumerate(blocks):
        projected = 1 << r
        for j, column in enumerate(y):
            if block >> j & 1:
                projected ^= column
        while projected:
            pivot = projected.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = projected
                break
            projected ^= basis[pivot]
    require(len(basis) == m - len(y), "binary kernel rank")
    require(all((v & a).bit_count() % 2 == 0 for a in y for v in basis.values()), "kernel basis")

    kernel = [0]
    for v in basis.values():
        kernel += [z ^ v for z in kernel]
    x = sorted(z for z in kernel if z.bit_count() == 2*t-2
               and all((z & a).bit_count() == t-1 for a in y))
    require(x == [31991091, 37103254, 40024233, 43545194, 52742502], "complete mixed census")
    check_marginals(t, y, x)
    loads = [sum(z >> r & 1 for z in x) for r in range(m)]
    require(sorted(loads) == [0] + [2]*20 + [4]*5, "even row loads")
    columns = [(1 << (4*t)) - 1] + [(z << 2) | 1 for z in y] + [(z << 2) | 3 for z in x]
    verify_orthogonal(4*t, columns)
    rows = rows_from_columns(4*t, columns)
    defect = []
    for r, left in enumerate(rows):
        row = []
        for s, right in enumerate(rows):
            dot = len(columns) - 2 * (left ^ right).bit_count()
            value = (4*t if r == s else 0) - dot
            require(value % 4 == 0, "integral defect Gram matrix")
            row.append(value // 4)
        defect.append(row)
    roots = (11, 2, 3, 4, 5, 6, 8, 9)
    require(determinant([[defect[r][s] for s in roots] for r in roots]) == 1, "E8 Gram determinant")
    print(f"n=28: {len(kernel):,} binary kernel vectors; fixed outer design has exactly {len(x)} inside columns")
    print("n=28: integral rank-8 defect Gram matrix with diagonal 2 and a principal determinant of 1")
    check_prefix_repair(columns)


def check_prefix_repair(columns):
    # Normalization fixes the first entry to +1, leaving 2^13 choices in the
    # first half and 2^14 in the second. Each five-bit digit is a distance.
    half_mask = (1 << 14) - 1
    left = [sum(((v ^ (col & half_mask)).bit_count()) << (5*i)
                for i, col in enumerate(columns)) for v in range(1, 1 << 14, 2)]
    right = [sum((14 - (v ^ (col >> 14)).bit_count()) << (5*i)
                 for i, col in enumerate(columns)) for v in range(1 << 14)]
    full_mask = (1 << (5*len(columns))) - 1
    for i, j in combinations(range(len(columns)), 2):
        keep = full_mask ^ (31 << (5*i)) ^ (31 << (5*j))
        index = {}
        for v, signature in enumerate(left):
            index.setdefault(signature & keep, []).append(2*v+1)
        eligible = {lo | (hi << 14) for hi, signature in enumerate(right)
                    for lo in index.get(signature & keep, ())}
        require(eligible == {columns[i], columns[j]}, f"new column after deleting {i}, {j}")

    replaced = {9, 12, 19}
    kept = [word for i, word in enumerate(columns) if i not in replaced]
    first_four = [210585043, 90966887, 54089267, 43457415]
    last_seven = [238560157, 72738319, 82980019, 51293467, 174485591, 219361643, 102562017]
    require(len(kept + first_four) == 21 and len(kept + first_four + last_seven) == 28, "repair widths")
    checked = verify_orthogonal(28, kept + first_four + last_seven)
    print(f"n=28: no new columns for any of 190 deletion pairs; three deletions give a full repair ({checked} dots)")


def signs(word):
    return tuple(1 if symbol == '+' else -1 for symbol in word)


def length_299_words():
    # A base sequence of lengths (7,7,6,6) and the length-23 Williamson quadruple
    # tabulated in SageMath. The README cites the table and the array constructions.
    base_a, base_b, base_c, base_d = map(signs, ('+++++-+', '+-+-++-', '+++---', '+--++-'))
    selectors = []
    for pair_index, (left, right) in enumerate(((base_a, base_b), (base_c, base_d))):
        for a, b in zip(left, right, strict=True):
            selectors.append((2 * pair_index + int(a != b), a))
    williamson = tuple(map(signs, (
        '++---+---+-++-+---+---+', '+-++-++--++++++--++-++-',
        '+++---++-+-++-+-++---++', '+++-+++-+------+-+++-++',
    )))
    words = [[], [], [], []]
    for position in range(13 * 23):
        selector, sign = selectors[position % 13]
        a, b, c, d = (word[position % 23] for word in williamson)
        # Left multiplication by 1, i, j or k in the quaternion basis.
        row = ((a, b, c, d), (-b, a, -d, c), (-c, d, a, -b), (-d, -c, b, a))[selector]
        for word, value in zip(words, row, strict=True):
            word.append(sign * value)
    for shift in range(1, 299):
        total = sum(word[i] * word[(i + shift) % 299] for word in words for i in range(299))
        require(total == 0, f"length-299 complementary words at shift {shift}")
    return words


def goethals_seidel(words):
    """C(v) has entry v[col-row]. The reversal sends col to size-1-col."""
    size = len(words[0])
    # (word index, coefficient, coordinate formula) in the 4 by 4 array.
    # D = circulant, R = circulant times reversal, T = transpose times reversal.
    blocks = (
        ((0, 1, 'D'), (1, 1, 'R'), (2, 1, 'R'), (3, 1, 'R')),
        ((1, -1, 'R'), (0, 1, 'D'), (3, -1, 'T'), (2, 1, 'T')),
        ((2, -1, 'R'), (3, 1, 'T'), (0, 1, 'D'), (1, -1, 'T')),
        ((3, -1, 'R'), (2, -1, 'T'), (1, 1, 'T'), (0, 1, 'D')),
    )
    columns = []
    for block_col in range(4):
        for c in range(size):
            column = 0
            for block_row in range(4):
                index, coefficient, kind = blocks[block_row][block_col]
                for r in range(size):
                    if kind == 'D':
                        position = c - r
                    elif kind == 'R':
                        position = -1 - c - r
                    else:
                        position = 1 + c + r
                    if coefficient * words[index][position % size] == 1:
                        column |= 1 << (block_row * size + r)
            columns.append(column)
    return columns


def check_scarpis():
    """First member q=43 of the covered family q=43^(60k+1), using Djokovic's array."""
    q = 43
    small = paley(q)
    core = [sum(((small[c + 1] >> (r + 1)) & 1) << c for c in range(q)) for r in range(q)]
    all_plus = (1 << q) - 1
    rows = []
    for word in core:
        row = all_plus
        for i in range(q):
            if word & (1 << i):
                row |= all_plus << (q * (i + 1))
        rows.append(row)
    for r in range(q):
        for k in range(q):
            row = core[r]
            for i in range(q):
                row |= core[(i * r + k) % q] << (q * (i + 1))
            rows.append(row)
    n = q * (q + 1)
    require(len(rows) == n, "Scarpis row count")
    checked = verify_orthogonal(n, rows)
    print(f"n={n}: Scarpis construction; all {checked:,} pairwise dots zero")


def check_2396():
    short = goethals_seidel(length_299_words())
    base = paley(599)
    mask = (1 << 600) - 1
    long = [w | (w << 600) for w in base] + [w | ((w ^ mask) << 600) for w in base]
    require((len(short), len(long)) == (1196, 1200), "factor sizes")
    verify_orthogonal(1196, short)
    verify_orthogonal(1200, long)
    columns = [word | (long[j] << 1196) for j, word in enumerate(short)]
    checked = verify_orthogonal(2396, columns)
    print(f"n=2396: {len(columns)} explicit orthogonal columns; all {checked:,} pairwise dots zero")
    rows = rows_from_columns(2396, columns)
    # Top-top dots are zero and bottom-bottom dots are bounded by the four
    # omitted entries of the order-1200 Hadamard, so only cross pairs can win.
    maximum = max(abs(len(columns) - 2 * (a ^ b).bit_count())
                  for a in rows[:1196] for b in rows[1196:])
    require(maximum == 168, "maximum absolute row correlation")
    reusable = 1 + (len(columns) + maximum) // 2
    print(f"n=2396: largest absolute row dot {maximum}; outer design can reuse at most {reusable} columns")
    retained_mask = (1 << 1196) - 1
    classes = [[] for _ in range(8)]
    omitted_rows = rows_from_columns(1200, long[1196:])
    for retained, omitted in zip(rows[1196:], omitted_rows, strict=True):
        # Make the first omitted sign positive to quotient by row negation.
        if not omitted & 1:
            omitted ^= 15
            retained ^= retained_mask
        classes[omitted >> 1].append(retained)
    min_pattern = 1200
    for group in classes:
        for j in range(1196):
            ones = sum(row >> j & 1 for row in group)
            min_pattern = min(min_pattern, ones, len(group) - ones)
    require(min_pattern == 52, "joint retained and omitted row patterns")
    print("n=2396: every joint five-sign pattern up to negation occurs at least 52 times")


if __name__ == "__main__":
    for multiplier in (5, 11, 15):
        check_extraction(multiplier)
    check_blocked_prefix()
    check_scarpis()
    check_2396()
