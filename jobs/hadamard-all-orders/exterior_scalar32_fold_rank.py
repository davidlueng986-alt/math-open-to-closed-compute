"""Check necessary fold changes for joint mod16 at the scalar32 growth point."""

from collections import defaultdict
from itertools import combinations, product
import json
from pathlib import Path

from exterior_mod16_invariant import decode
from exterior_scalar32 import anchors_from_pairs, lower_signed
from five_column_constraints import BOTTOM, LOWER_OMISSIONS, TOP, correlations, require
from five_column_gram import gram_fixture
from verify import paley, rows_from_columns


HALF = BOTTOM // 2
ALL = (1 << HALF) - 1
RESIDUES = (0, 4, 8, 12)
# Character labels use the fold changes of columns 1, 3 and 4 as the basis.
# By physical row weights, the change in column 5 is their XOR.
CHARACTERS = {1: (0,), 2: (2,), 4: (3,), 7: (4,), 3: (0, 2), 5: (0, 3), 6: (0, 4)}


def positions(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def subsets(mask, size):
    return (sum(1 << i for i in rows) for rows in combinations(positions(mask), size))


def conditional_labels(axes, upper, lower, cohorts):
    def bit(row):
        return sum(row[j] >> 2 & 1 for j in axes) % 2

    goal = tuple(sum(row[1] % 16 == t and bit(row) for row in upper) for t in RESIDUES)
    select = tuple(sum(1 << (i % HALF) for i, row in lower.items() if i // HALF == s and bit(row))
                   for s in (0, 1))
    return goal, tuple(tuple(m & select[s] for m in cohorts[s]) for s in (0, 1))


def deficit(labels, cohorts, toggle_first, toggle_second):
    goal, low = labels
    return sum(abs(((a ^ toggle_first) & p).bit_count() + ((b ^ toggle_second) & q).bit_count() - target)
               for a, b, p, q, target in zip(*low, *cohorts, goal, strict=True))


def arbitrary_offsets(labels, cohorts):
    return min(deficit(labels, cohorts, a, b) for a, b in product((0, ALL), repeat=2))


def codewords_at_most_four(paley_rows, fixed):
    bases = tuple(tuple(i % HALF for i in fixed if i // HALF == copy) for copy in (0, 1))
    conditions = [(i, group[0]) for group in bases for i in group[1:]]
    row_signature = [sum((((row >> a) ^ (row >> b)) & 1) << k for k, (a, b) in enumerate(conditions))
                     for row in paley_rows]
    pairs = defaultdict(list)
    for a, b in combinations(range(HALF), 2):
        pairs[row_signature[a] ^ row_signature[b]].append((a, b))
    require(tuple(pairs[0]) == ((124, 145), (190, 515)), 'all admissible weight-two words')
    # A four-set has exactly one pairing that splits its increasing list in half.
    # Its XOR is zero exactly when those two pairs have the same signature.
    four = [left + right for group in pairs.values() for left, right in combinations(group, 2) if left[1] < right[0]]
    require(len(four) == 80933, 'all admissible weight-four words')
    return (bases[0][0], bases[1][0]), pairs[0], four


def shifted_labels(paley_rows, support, representatives):
    q = 0
    for i in support:
        q ^= paley_rows[i]
    return tuple(q ^ (ALL if q >> i & 1 else 0) for i in representatives)


def small_unions(weight_four, conditions, cohorts, paley_rows, representatives):
    characters = tuple(CHARACTERS)
    triples = tuple(combinations(characters, 3))
    dependent = [(x, y, z) for x, y, z in triples if not x ^ y ^ z]
    require(not any((a ^ b) in weight_four[z]
                    for x, y, z in dependent for a in weight_four[x] for b in weight_four[y]),
            'no admissible dependent triple of weight four')

    index = {}
    for char in characters:
        for k in (1, 2, 3):
            by_subset = defaultdict(set)
            for word in weight_four[char]:
                for subset in subsets(word, k):
                    by_subset[subset].add(word)
            index[char, k] = by_subset

    checked = set()
    for x, y, z in triples:
        if not x ^ y ^ z:
            continue
        x, y, z = sorted((x, y, z), key=lambda ch: len(weight_four[ch]))
        for a, b in product(weight_four[x], weight_four[y]):
            if (a ^ b).bit_count() < 4:
                continue
            union = a | b
            intersection_needed = union.bit_count() + 4 - 9
            require(1 <= intersection_needed <= 3, 'two distinct weight-four words at distance at least four')
            candidates = set().union(*(index[z, intersection_needed].get(q, ())
                                       for q in subsets(union, intersection_needed)))
            for c in candidates:
                if (union | c).bit_count() > 9:
                    continue
                words = {x: a, y: b, z: c, x ^ y: a ^ b, x ^ z: a ^ c, y ^ z: b ^ c, x ^ y ^ z: a ^ b ^ c}
                if min(word.bit_count() for word in words.values()) < 4:
                    continue
                key = tuple(words[ch] for ch in characters)
                if key in checked:
                    continue
                checked.add(key)
                passes = all(word in weight_four[ch] if word.bit_count() == 4 else
                             deficit(conditions[ch], cohorts, *shifted_labels(paley_rows, positions(word), representatives)) == 0
                             for ch, word in words.items())
                require(not passes, 'no coupled seven-character solution on at most nine physical bases')
    require(len(checked) == 2775, 'all remaining coupled rank-three tuples on at most nine bases')


def main():
    here = Path(__file__).parent
    pivot = json.loads((here / 'exterior_reindexed_pivot_witness.json').read_text())['ten']
    witness = json.loads((here / 'exterior_scalar32_witness.json').read_text())['growth']
    upper = decode(json.loads((here / 'exterior_mod16_invariant_witness.json').read_text())['upper'])
    new = decode(witness['lower'])
    top, lower, *_ = gram_fixture()
    above = correlations(top[3:], upper, TOP)
    below = lower_signed(correlations(lower, new, BOTTOM))
    all_projections = above + list(below.values())
    for j in range(len(new)):
        require(len({row[j] % 4 for row in all_projections}) == 1,
                'the same constant modulo-four class in each coordinate')
    cohorts = tuple(tuple(sum(1 << (i % HALF) for i, row in below.items() if i // HALF == s and row[1] % 16 == t)
                          for t in RESIDUES) for s in (0, 1))
    require(sum(m.bit_count() for group in cohorts for m in group) == 1193 and
            all(sum(m.bit_count() for m in selected) == sum(row[1] % 16 == t for row in above)
                for t, selected in zip(RESIDUES, zip(*cohorts, strict=True), strict=True)), 'matching scalar mod16 counts')

    axes = (*CHARACTERS.values(), (2, 3), (2, 4), (3, 4))
    caps = tuple(1193 - arbitrary_offsets(conditional_labels(a, above, below, cohorts), cohorts) for a in axes)
    require(caps == (1165, 1173, 1170, 1186, 1164, 1185, 1177, 1177, 1185, 1164),
            'all individual fixed folds and all equal fold-change pairs are excluded')
    print(f'n=2396 fixed scalar32 second column: four individual fold caps {caps[:4]}; six equal-change caps {caps[4:]}')

    critical = [pair for pair in pivot['anchors'] if pair[0] in (12, 14, 18, 313)]
    named = anchors_from_pairs(critical + witness['extra_anchors'])
    require(len(named) == 20 and all(below[i] == tuple(above[j - 3]) for i, j in named.items()), 'ten exact named pairs')
    paley_columns = paley(HALF - 1)
    complement = (1 << BOTTOM) - 1
    require(lower == [complement ^ (p | ((p ^ mask) << HALF)) for mask in (0, ALL) for p in paley_columns],
            'the signed lower source is the asserted Sylvester split')
    paley_rows = rows_from_columns(HALF, paley_columns)
    representatives, two, four = codewords_at_most_four(paley_rows, (*LOWER_OMISSIONS, *named))

    conditions = {ch: conditional_labels(axes, above, below, cohorts) for ch, axes in CHARACTERS.items()}
    require(all(deficit(labels, cohorts, *shifted_labels(paley_rows, support, representatives)) > 0
                for labels in conditions.values() for support in two), 'all seven characters exclude the two admissible short supports')
    weight_four = {ch: set() for ch in conditions}
    for support in four:
        shift = shifted_labels(paley_rows, support, representatives)
        word = sum(1 << r for r in support)
        for ch, labels in conditions.items():
            if not deficit(labels, cohorts, *shift):
                weight_four[ch].add(word)
    require(tuple(map(len, weight_four.values())) == (5, 237, 8, 679, 53, 5, 281), 'exact compatible weight-four supports')
    small_unions(weight_four, conditions, cohorts, paley_rows, representatives)
    print('n=2396 anchored scalar32 fold rank: rank 3 and at least 10 changed physical base pairs for full joint mod16')


if __name__ == '__main__':
    main()
