"""Exact four-profile reallocation census and necessary width-1212 cuts."""

from collections import defaultdict
from itertools import combinations, product
from math import prod

from r_paley_cooper_wallis import build_source, build_pair
from r_paley_cooper_wallis_growth import ONE_FLIPS, SELECTED
from r_paley_isotropic_code import assemble, half_projections
from verify import rows_from_columns, verify_orthogonal

HEIGHT = 1196
ALL = (1 << HEIGHT) - 1


def sign(mask, index):
    return 1 - 2 * (mask >> index & 1)


def inventory(source, far, selected):
    decks = [half_projections(source, word) for word in far]
    eligible = tuple(j for j in range(HEIGHT) if all(abs(deck[j]) == 1 for deck in decks))
    assert len(eligible) == 702
    rows = rows_from_columns(HEIGHT, source)
    roots, reserves = map(set, zip(*ONE_FLIPS, strict=True))
    emask = sum(1 << j for j in eligible)
    max_same_reserve = 0
    # A reused reserve forces all 598 opposite normalized row entries into K.
    for r, pivot in ONE_FLIPS:
        for s, row in enumerate(rows):
            if r == s:
                continue
            change = rows[r] ^ row
            if change >> pivot & 1:
                change ^= ALL
            assert change.bit_count() == 598
            max_same_reserve = max(max_same_reserve, (change & emask).bit_count())
    assert max_same_reserve == 418 < 598

    by_code = defaultdict(list)
    bit_code = {}
    for j in eligible:
        if j in reserves:
            continue
        base = decks[0][j]
        sign_tail = [base * decks[1][j], *(base * sign(rows[r], j) for r, _ in ONE_FLIPS)]
        code = sum((value < 0) << k for k, value in enumerate(sign_tail))
        by_code[code].append(j)
        bit_code[j] = code
    assert len(by_code) and len(bit_code) - len(selected) == 101
    return decks, rows, roots, reserves, by_code, bit_code, max_same_reserve


def four_profiles(caps, old_counts):
    """Each surviving pair encodes all physical representatives of one profile trade."""
    unselected = {code: cap - old_counts[code] for code, cap in caps.items() if cap > old_counts[code]}
    changes = []
    physical = 0
    for a, b, c in combinations(sorted(unselected), 3):
        d = a ^ b ^ c
        if d <= c or d not in unselected:
            continue
        p, q = a ^ b, a ^ c
        if not (p & q and p & ~q and q & ~p):
            continue  # An unused balanced axis would make the switch a row permutation.
        vary = p | q
        added = (a, b, c, d)
        deleted = tuple(code ^ vary for code in added)
        if not all(old_counts.get(code, 0) for code in deleted):
            continue
        changes.append((deleted, added))
        physical += prod(old_counts[code] for code in deleted) * prod(unselected[code] for code in added)
    return changes, physical


def verify_five():
    """After pinning singletons, weight-two columns are the edges of K5."""
    edges = tuple((1 << i) | (1 << j) for i, j in combinations(range(5), 2))

    def profiles(columns):
        return sorted(sum((c >> r & 1) << i for i, c in enumerate(columns)) for r in range(5))

    def target_embeddings(first, target, remaining):
        p = len(target)
        if p == len(first):
            yield target
            return
        overlaps = [(first[p] & a).bit_count() for a in first[:p]]
        for x in remaining:
            if any((x & y).bit_count() != k for y, k in zip(target, overlaps, strict=True)):
                continue
            yield from target_embeddings(first, (*target, x), tuple(e for e in remaining if e != x))

    tested = nontrivial = 0
    for n in range(1, 11):
        for source in combinations(edges, n):
            a = profiles(source)
            # A permutation of the five samples can fix the first target edge.
            for target in target_embeddings(source, edges[:1], edges[1:]):
                b = profiles(target)
                tested += 1
                nontrivial += a != b
                assert set(a).intersection(b)
    assert (tested, nontrivial) == (12931, 1380)
    print("12931 five-sample edge-intersection embeddings; all 1380 differing multisets share a profile")


def raw_domains(source, far, decks, rows, used_rows, used_pivots):
    origin = far[0]
    directions = [origin ^ far[1], *(origin ^ source[g] ^ (1 << r) for r, g in ONE_FLIPS)]
    assert all(u.bit_count() % 2 == 0 for u in directions)
    assert all((u & v).bit_count() % 2 == 1 for u, v in combinations(directions, 2))
    pivot_by_signature = defaultdict(list)
    for j, col in enumerate(source):
        if j not in used_pivots:
            sig = sum((((col ^ origin) & u).bit_count() % 2) << i for i, u in enumerate(directions))
            pivot_by_signature[sig].append(j)
    result = {}
    for r in range(HEIGHT):
        if r in used_rows:
            continue
        need = sum((1 - (u >> r & 1)) << i for i, u in enumerate(directions))
        pairs = []
        for g in pivot_by_signature[need]:
            raw = sign(rows[r], g)
            moment = tuple([raw * decks[i][g] - sign(far[i], r) for i in range(2)] + [
                raw * sign(rows[s], g) + sign(rows[r], h) * sign(rows[s], h) for s, h in ONE_FLIPS
            ])
            pairs.append((g, moment))
        if pairs:
            result[r] = pairs
    return result


def support_range(selected_count, cap, positive):
    return (2 * max(0, selected_count - (cap - positive)) - selected_count,
            2 * min(positive, selected_count) - selected_count)


def directions(dimension):
    result = []
    for support in (2, 3):
        for positions in combinations(range(dimension), support):
            for signs in product((1, -1), repeat=support - 1):
                result.append((positions, (1, *signs)))
    return result


def coordinate_bounds(intervals, signs):
    minsum = sum(l for l, _ in intervals)
    maxsum = sum(u for _, u in intervals)
    minus = [0] * len(signs[0])
    for (l, u), pattern in zip(intervals, signs, strict=True):
        for i, sign_value in enumerate(pattern):
            if sign_value < 0:
                minus[i] += l + u
    return [minsum - t for t in minus], [maxsum - t for t in minus]


def support_replay(by_code, bit_code, caps, old_counts, rows, b0, domain, changes):
    codes = tuple(sorted(by_code))
    index = {code: i for i, code in enumerate(codes)}
    masks = [sum(1 << j for j in by_code[c]) for c in codes]
    base_mask = sum(1 << j for j, v in enumerate(b0) if v < 0)
    shape_signs = [(1, *(sign(c, k) for k in range(len(ONE_FLIPS) + 1))) for c in codes]
    check_directions = directions(len(shape_signs[0]))
    always = []
    for r, alternatives in domain.items():
        positive = ALL ^ rows[r] ^ base_mask
        quantities = [(g & positive).bit_count() for g in masks]
        intervals = [support_range(old_counts[c], caps[c], a) for c, a in zip(codes, quantities, strict=True)]
        lo, hi = coordinate_bounds(intervals, shape_signs)
        always.append((quantities, intervals, lo, hi, alternatives))
    coordinate = []
    direction_count = []
    for deleted, added in [((), ()), *changes]:
        counts = dict(old_counts)
        for c in deleted:
            counts[c] -= 1
        for c in added:
            counts[c] += 1
        replaced = [index[c] for c in (*deleted, *added)]
        count_coord = count_dir = 0
        for quantity, intervals, lo0, hi0, alternatives in always:
            lo, hi = lo0.copy(), hi0.copy()
            delta = {}
            for k in replaced:
                c = codes[k]
                u, v = support_range(counts[c], caps[c], quantity[k])
                delta[k] = (u, v)
                du = u - intervals[k][0]
                dv = v - intervals[k][1]
                for i, s in enumerate(shape_signs[k]):
                    lo[i] += du if s > 0 else -dv
                    hi[i] += dv if s > 0 else -du
            for pivot, vector in alternatives:
                c = bit_code.get(pivot)
                if c is not None and counts[c] == caps[c]:
                    continue
                if any(x < low or x > high for x, low, high in zip(vector, lo, hi, strict=True)):
                    continue
                count_coord += 1
                new = [delta.get(k, value) for k, value in enumerate(intervals)]
                active = [(shape_signs[k], l, h) for k, (l, h) in enumerate(new) if l or h]
                for pos, sg in check_directions:
                    target = sum(s * vector[j] for j, s in zip(pos, sg, strict=True))
                    low = high = 0
                    for v, l, h in active:
                        w = sum(v[j] * s for j, s in zip(pos, sg, strict=True))
                        if w >= 0:
                            low += w * l
                            high += w * h
                        else:
                            low += w * h
                            high += w * l
                    if not low <= target <= high:
                        break
                else:
                    count_dir += 1
        coordinate.append(count_coord)
        direction_count.append(count_dir)
    return coordinate, direction_count


def verify():
    verify_five()
    source = build_source()
    far, _ = build_pair(source)
    selected = [j for j in range(HEIGHT) if SELECTED >> j & 1]
    words = [*far, *(source[g] ^ (1 << r) for r, g in ONE_FLIPS)]
    cols = assemble(599, source, selected, words)
    assert len(cols) == 1211 and verify_orthogonal(2396, cols) == 732655
    decks, rows, roots, reserves, by_code, bit_code, max_reuse = inventory(source, far, selected)
    assert len(set(bit_code[j] for j in selected)) == 462
    caps = {c: len(J) for c, J in by_code.items()}
    chosen = set(selected)
    old_counts = {c: sum(j in chosen for j in J) for c, J in by_code.items()}
    changes, physical = four_profiles(caps, old_counts)
    assert len(changes) == 61 and physical == 641
    domain = raw_domains(source, far, decks, rows, roots, reserves)
    assert len(domain) == 828 and sum(map(len, domain.values())) == 1377
    coordinate, directional = support_replay(by_code, bit_code, caps, old_counts, rows, decks[0], domain, changes)
    assert coordinate[0] == 3 and sum(coordinate[1:]) == 221 and not any(directional)
    print(f"CW 1211: reused-reserve opposite positions at most {max_reuse} of 598 required")
    print("61 nontrivial four-profile trades, 641 physical swaps; 62 hulls including the original")
    print("1377 raw row/pivot pairs; coordinate cuts leave 224 hull/pair settings; signed cuts exclude all")


if __name__ == '__main__':
    verify()
