"""Rebuild the joint m70 and axis39 support, and replay its exact oriented slice."""

from io import StringIO
from itertools import combinations, product
from math import comb
import os
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from border4_2396 import periodic
from border4_2396_dual_changed_support import cyclic_tail_negative, independent_dihedral, positive_words
from border4_2396_dual_mod5_forest import FACTORS_5, check_factors, forest, residual
from border4_2396_nested import nested_negative_words
from border4_2396_primitive_field import primitive_factor, remainder

N = 299
AXIS = 39
LIMB = (1 << 64) - 1

HEAD_ONLY_MASKS = (
    0x317A0829F0CA41A8220204412340022258048E86582B0590320800D40051008202703200108,
    0x4A08418818914A228420C88AE07006012E1E1042B21011CA8824D83001DA2C90700912100,
    0x1BA99AB8419400108009D2008804800010080C020180840031180804000083A2C020003B880,
    0x91546D8058101000059C040000480420211088440180402000180C04460117E0400233808C,
)
JOINT_MASKS = (
    0x30762828940204E032034005044402021900C882583D85901AA825802050C80802B06306A00,
    0x4080341861840A2021641418A208204400C1D8242960491F60D24A812013A0443E6C214412,
    0x440180002801008020090010A22C81974F044020000CC418AC084100A40CC5A0010041B0080,
    0x606D01010009180028400081A00409268FC8042200080581204009802804092210040DA3204,
)
JOINT_FOREST_MASKS = (
    0x30662008941204E03283900501E4020A1900C880583C81805AA025A03050802880306306A08,
    0x144803419A08018A2214B1C00F808004C10E18024E9D0491E005240C3201320402A60312E0A,
    0x42180102000008820098010A20C81954F544120200CC418AC084100A00C45A001004130080,
    0x606D09000009180028400081800009768DC8040200080D8120C00D80A844090200040CA3204,
)
HIGH_5 = (19, 31, 49, 50, 65, 71, 81, 96, 98, 99, 105, 106, 108, 112, 115, 139, 148)


def change_second_head(negative):
    multiplier, inverse = 70, 47
    assert (multiplier % 13, multiplier % 23, multiplier * inverse % N) == (5, 1, 1)
    b = tuple(negative[1][inverse * i % N] for i in range(N))
    return negative[:1] + (b,) + negative[2:]


def raw_stats(s, t):
    assert all(a * a + b * b == 1 for u, v in zip(s, t, strict=True)
               for a, b in zip(u, v, strict=True))
    binary = tuple(tuple(u[j % N] + (1 - 2 * (j % 2)) * v[j % N] for j in range(2 * N))
                   for u, v in zip(s, t, strict=True))
    assert all(value in (-1, 1) for row in binary for value in row)
    assert tuple(map(sum, s)) == (0, 1, 0, 0)
    assert tuple(map(sum, binary)) == (0, 2, 0, 0)
    normalized = residual(s)
    raw = [a + 4 for a in periodic(binary)[1:]]
    assert all(a % 8 == 0 for a in raw)
    for d, a in enumerate(raw, 1):
        assert a == 8 * normalized[d % N]
    # These counts and the energy come directly from all 597 nonzero raw shifts.
    return (sum(a % 16 == 0 for a in raw), raw.count(0), max(map(abs, raw)),
            sum(a * a for a in raw), sum(a % 32 == 0 for a in raw),
            sum(a % 64 == 0 for a in raw))


def compressed(row, q):
    return tuple(sum(row[j::q]) for j in range(q))


def positions(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def kernel(columns):
    echelon = {}
    generators = []
    for j, code in columns:
        mask = 1 << j
        while code:
            pivot = code.bit_length() - 1
            if pivot not in echelon:
                echelon[pivot] = code, mask
                break
            other, physical = echelon[pivot]
            code ^= other
            mask ^= physical
        else:
            generators.append(mask)
    return generators


def head_blocks(row, fixed_margin_dimension):
    support = tuple(bool(a) for a in row)
    columns = tuple(sum((support[(i-d) % N] ^ support[(i+d) % N]) << (d-1)
                        for d in range(1, 150)) for i in range(N))
    margins = tuple((1 << (i % 13)) | (1 << (13 + i % 23)) for i in range(N))
    occupied = tuple(i for i, value in enumerate(row) if value)
    global_basis = kernel((i, columns[i] | (margins[i] << 149)) for i in occupied)
    local_basis = []
    for y in range(12):
        residues = {y, (-y) % 23}
        basis = kernel((i, columns[i]) for i in occupied if i % 23 in residues)
        local_basis.extend(basis)
        masks = [0]
        for v in basis:
            masks.extend([a ^ v for a in masks])
        choices = []
        for mask in masks:
            sites = tuple(positions(mask))
            if any(sum(row[i] for i in sites if i % 23 == y) for y in residues):
                continue
            charge = sum(row[i] << (6 * (i % 13)) for i in sites)
            choices.append((charge & LIMB, charge >> 64 & LIMB,
                            *(mask >> (64 * j) & LIMB for j in range(5))))
        assert choices
        if len(choices) > 1:
            yield choices
    # The local kernel is contained in the global kernel. Equal dimensions after
    # imposing the necessary margin parities prove equality for the fixed margins.
    local_margin_columns = []
    for j, mask in enumerate(local_basis):
        code = 0
        for i in positions(mask):
            code ^= margins[i]
        local_margin_columns.append((j, code))
    assert len(kernel(local_margin_columns)) == len(global_basis) == fixed_margin_dimension


def literal_orientations(row):
    support = frozenset(i for i in range(N) if row[i])
    classes = [tuple(i for i in range(j, N, q) if i in support)
               for q in (13, 23) for j in range(q)]
    required = tuple(sum(row[i] > 0 for i in cells) for cells in classes)

    def walk(remaining, targets, positive):
        if not remaining:
            assert not any(targets)
            yield tuple(0 if i not in support else (1 if i in positive else -1) for i in range(N))
            return
        smallest = None
        for j, cells in enumerate(classes):
            active = tuple(i for i in cells if i in remaining)
            if not 0 <= targets[j] <= len(active):
                return
            if active:
                choice = (comb(len(active), targets[j]), j, active)
                if smallest is None or choice < smallest:
                    smallest = choice
        _, j, active = smallest
        todo = remaining.difference(active)
        for chosen in combinations(active, targets[j]):
            targets2 = list(targets)
            for i in chosen:
                targets2[i % 13] -= 1
                targets2[13 + i % 23] -= 1
            yield from walk(todo, targets2, positive.union(chosen))

    return tuple(walk(support, required, frozenset()))


def tail_pairs(s):
    u, v = s[2], tuple(s[3][(AXIS - i) % N] for i in range(N))
    assert all(bool(x) == bool(y) for x, y in zip(u, v, strict=True))
    phases = tuple(tuple((x + sign * y) // 2 for x, y in zip(u, v, strict=True))
                   for sign in (1, -1))
    choices = tuple(literal_orientations(w) for w in phases)
    assert tuple(map(len, choices)) == (51, 16)
    return tuple((tuple(x + y for x, y in zip(a, b, strict=True)),
                  tuple(a[(AXIS-i) % N] - b[(AXIS-i) % N] for i in range(N)))
                 for a, b in product(*choices))


def orientation(row, mask):
    assert mask >> N == 0 and all(not (mask >> i & 1) or x for i, x in enumerate(row))
    return tuple(-x if mask >> i & 1 else x for i, x in enumerate(row))


def census(anchor, negative):
    data = StringIO()
    for row in anchor[:2]:
        print(*row, file=data)
    tails = tail_pairs(anchor)
    print(len(tails), file=data)
    for t in tails:
        for row in t:
            print(*row, file=data)
    for row, dimension in zip(anchor[:2], (50, 55), strict=True):
        blocks = tuple(head_blocks(row, dimension))
        print(len(blocks), file=data)
        for block in blocks:
            print(len(block), file=data)
            for option in block:
                print(*option, file=data)
    with TemporaryDirectory() as tmp:
        binary = Path(tmp) / "joint_geometry"
        cpp = Path(__file__).with_suffix(".cpp")
        subprocess.run([os.environ.get("CXX", "g++"), "-std=c++20", "-O3",
                        str(cpp), "-o", str(binary)], check=True)
        result = subprocess.run([binary], input=data.getvalue(), capture_output=True,
                                text=True, check=True)
    head, q5, q7, *hits, end = result.stdout.splitlines()
    assert (head, q5, q7, end) == ("decks 1284 780 816", "prefix 5 24 0",
                                  "prefix 7 16 0", "interval 0 21")
    assert len(hits) == 21 and len(set(hits)) == 21
    scores = []
    q7_factor = primitive_factor(7)
    for line in hits:
        head, *values = line.split()
        assert head == "hit" and len(values) == 11
        tail, *raw_masks = map(int, values)
        a, b = (sum(raw_masks[5*r+j] << (64*j) for j in range(5)) for r in range(2))
        positive = (orientation(anchor[0], a), orientation(anchor[1], b), *tails[tail])
        for row, baseline in zip(positive[:2], anchor[:2], strict=True):
            assert all(compressed(row, q) == compressed(baseline, q) for q in (13, 23))
        scores.append(raw_stats(positive, negative))
        assert scores[-1][2] == 48
        assert any(remainder(residual(positive), q7_factor, 7))
    best = ((389, 81, 48, 362496, 177, 81),
            (341, 101, 48, 408576, 177, 101),
            (285, 69, 48, 313856, 145, 69))
    assert all(record in scores for record in best)
    assert (max(r[0] for r in scores), max(r[1] for r in scores),
            min(r[3] for r in scores)) == (389, 101, 313856)
    print("816 tails; no peak <=40, 21 peak-48 full integer replays; zero mod5 and mod7 prefix hits.")


def main():
    original = nested_negative_words()
    head = change_second_head(original)
    assert not independent_dihedral(original[1], head[1])
    assert periodic(head) == [599] + [0] * (N - 1)
    assert raw_stats(positive_words(head, HEAD_ONLY_MASKS), head) == (309, 93, 80, 525312, 185, 101)
    joint = change_second_head(cyclic_tail_negative(original))
    counts = tuple(sum(bool(a) != bool(b) for a, b in zip(u, v, strict=True))
                   for u, v in zip(original, joint, strict=True))
    assert counts == (0, 84, 144, 142)
    assert tuple(independent_dihedral(a, b) for a, b in zip(original, joint, strict=True)) == (
        True, False, False, False)
    assert periodic(joint) == [599] + [0] * (N - 1)
    anchor = positive_words(joint, JOINT_MASKS)
    assert raw_stats(anchor, joint) == (293, 61, 64, 509952, 177, 85)
    forest_words = positive_words(joint, JOINT_FOREST_MASKS)
    assert raw_stats(forest_words, joint) == (269, 65, 64, 333312, 129, 69)
    e = residual(forest_words)
    assert tuple(d for d in range(1, 150) if abs(e[d]) >= 5) == HIGH_5
    assert forest(HIGH_5)[1] == ()
    check_factors()
    assert tuple(sum(bool(v) for v in remainder(e, g, 5)) for g in FACTORS_5) == (29, 39, 33)
    census(anchor, joint)


if __name__ == "__main__":
    main()
