"""Exact T11 times an unreal sixth-root source, and the order-19 palette test."""

from itertools import combinations, product
from math import comb

from border4_2396 import pack, periodic
from t599_length_change import aperiodic, disjoint
from verify import goethals_seidel, rows_from_columns, signs, verify_orthogonal

UNREAL_A = (
    "+------------",
    "---+++++++---",
    "----++++++--+",
    "---+++-+++--+",
    "---++++-++--+",
    "--++--++--+++",
    "-++-+---++++-",
    "-+++--++--+-+",
    "-++-++--+-++-",
    "-+-+--++--+++",
    "-++--+--++++-",
    "-+++--++---++",
    "-++-++---+++-",
)

UNREAL_B = (
    "+++++++++++++",
    "+++++++------",
    "+++----+++--+",
    "+---++-+--+++",
    "+--+--+-++++-",
    "+-+++---+-+-+",
    "+-+-+-+--+-++",
    "+-+--+++-++--",
    "+-++-+-++--+-",
    "++-+-+---+-++",
    "++---++-+-+-+",
    "++--+-+++--+-",
    "++-++--+-++--",
)

SZOLLOSI_19 = (
    "3011005435321135430",
    "0013314245151433150",
    "0014242432413314510",
    "1242124424503511340",
    "2543204201424153130",
    "0354504531345341310",
    "5435323011001135430",
    "4245150013311433150",
    "2432410014243314510",
    "4424501242123511340",
    "4201422543204153130",
    "4531340354505341310",
    "5533215533210000113",
    "5231535231530013010",
    "3355123355121300010",
    "1325351325350101041",
    "2513532513531041100",
    "3152353152351010401",
    "0000000000004110100",
)


def t11_selectors():
    base = tuple(map(signs, ("+++-++", "+++-+-", "+++--", "+-++-")))
    assert aperiodic(base) == [22] + [0]*5
    words = tuple(word + (0,)*5 for word in disjoint(*base[:2])) + tuple(
        (0,)*6 + word for word in disjoint(*base[2:]))
    assert periodic(words) == [11] + [0]*10
    selectors = []
    for column in zip(*words, strict=True):
        assert sum(map(abs, column)) == 1
        selectors.append(sum((index + 1)*value for index, value in enumerate(column)))
    return tuple(selectors)


def endpoint_rows(selectors, parameters):
    a, b, c, d = parameters
    # The linear quaternion matrix in Kolpakov's Section 3.2.
    frame = ((a,-b,-c,-d), (b,a,d,-c), (c,-d,a,b), (d,c,-b,a))
    words = tuple(tuple((1 if label > 0 else -1)*row[abs(label)-1] for label in selectors)
                  for row in frame)
    assert periodic(words) == [44] + [0]*10
    return rows_from_columns(44, goethals_seidel(words))


def dot(left, right):
    return sum(a*b for a, b in zip(left, right, strict=True))


def neighbor_permutation(matrix):
    size = len(matrix)
    as_signs = tuple(tuple(2*((row >> j) & 1) - 1 for j in range(size)) for row in matrix)
    representatives = ((2,) + (0,)*(size-1), (1,)*size, (3,) + (1,)*(size-1))
    neighbors = []
    for representative in representatives:
        # Representatives are doubled. Applying H/2 takes the doubled
        # vectors to the following integer coordinates in D^*/D.
        numerators = [dot(row, representative) for row in as_signs]
        assert all(value % 2 == 0 for value in numerators)
        numerators = [value//2 for value in numerators]
        half = numerators[0] % 2
        assert all(value % 2 == half for value in numerators)
        parity = sum((value-half)//2 for value in numerators) % 2
        neighbors.append(parity + 2*half)
    assert set(neighbors) == {1, 2, 3} and neighbors[0] != 1
    return tuple(neighbors)


def verify_sixth_root_action(plus, one_minus):
    def row_dot(x, y):
        return 44 - 2*(x ^ y).bit_count()

    assert verify_orthogonal(44, plus) == comb(44, 2)
    assert verify_orthogonal(44, one_minus) == comb(44, 2)
    for i, j in product(range(44), repeat=2):
        assert row_dot(plus[i], one_minus[j]) + row_dot(one_minus[i], plus[j]) == 44*(i == j)
    p, q = map(neighbor_permutation, (plus, one_minus))
    rotation = tuple(q[p.index(label)] for label in (1, 2, 3))
    assert rotation in ((2, 3, 1), (3, 1, 2))
    print(f"T11 sixth-root action cycles the three 2-adic neighbor classes: {rotation}")


def verify_unreal_product():
    a, b = tuple(map(signs, UNREAL_A)), tuple(map(signs, UNREAL_B))
    for i, j in product(range(13), repeat=2):
        assert dot(a[i], b[j]) == dot(b[i], a[j])
        assert dot(a[i], a[j]) + 3*dot(b[i], b[j]) == 52*(i == j)
    a_columns, b_columns = tuple(zip(*a, strict=True)), tuple(zip(*b, strict=True))
    assert (dot(a[1], b_columns[2]), dot(b[1], a_columns[2])) == (1, -7)

    selectors = t11_selectors()
    plus = endpoint_rows(selectors, (1, 1, 1, 1))
    one_minus = endpoint_rows(selectors, (1, -1, 1, 1))
    verify_sixth_root_action(plus, one_minus)
    minus = endpoint_rows(selectors, (1, -1, -1, -1))
    rows = []
    for i, x in product(range(44), range(13)):
        row = []
        for j, y in product(range(44), range(13)):
            sign_plus = 2*((plus[i] >> j) & 1) - 1
            sign_minus = 2*((minus[i] >> j) & 1) - 1
            row.append(sign_plus*(a[x][y] if sign_plus == sign_minus else b[x][y]))
        rows.append(pack(row))
    pairs = verify_orthogonal(572, rows)
    assert pairs == comb(572,2)
    print(f"Noncommuting unreal BH(13,6) times T11: H(572), all {pairs:,} row dots zero")


def verify_palette_obstruction():
    values = ((1,0), (0,1), (-1,1), (-1,0), (0,-1), (1,-1))
    matrix = tuple(tuple(map(int, word)) for word in SZOLLOSI_19)
    for left, right in combinations(matrix, 2):
        terms = tuple(values[(x-y)%6] for x, y in zip(left, right, strict=True))
        assert tuple(map(sum, zip(*terms, strict=True))) == (0,0)
    a, b, c = matrix[:3]
    residues = {((y-x)%3, (z-x)%3) for x, y, z in zip(a,b,c, strict=True)}
    assert residues == set(product(range(3), repeat=2)) - {(2,2)}
    for u, v in product(range(3), repeat=2):
        assert any(len({0, (x+u)%3, (y+v)%3}) == 3 for x,y in residues)
    print("Szöllősi BH(19,6): all 171 row dots vanish; 8/9 residue-pair palette obstruction")


if __name__ == "__main__":
    verify_unreal_product()
    verify_palette_obstruction()
