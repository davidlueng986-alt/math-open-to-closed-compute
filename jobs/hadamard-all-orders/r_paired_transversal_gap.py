"""Replay the two exceptional residual designs with exactly 2t-4 transversals."""

from collections import Counter

from verify import rows_from_columns, verify_orthogonal


R5 = tuple(int(row, 16) for row in (
    '253 272 0a7 0e5 14e 1ca 29c 394 139 329 01f 2aa 0d9 26c 307 1b2 3c1 174'
).split())
PAIRING5 = ((0, 5), (1, 2), (3, 4), (6, 7), (8, 9))

K9 = (
    (0, -1, 1, 1, -1),
    (-1, 0, 1, 1, -1),
    (-1, -1, 0, 1, 1),
    (-1, -1, 1, 0, 1),
    (-1, -1, -1, -1, 0),
)
P9 = (
    (-1, -1, 1, 1),
    (-1, 1, 1, -1),
    (1, -1, -1, 1),
    (1, -1, 1, -1),
    (-1, 1, -1, 1),
    (1, 1, 1, 1),
)
ACTIVE9 = 0x3DE1
DENSE9 = 0x2914


def r9():
    tau = (1, 1, -1, -1)
    u = (1, -1, 1, -1)
    v = (1, -1, -1, 1)
    balanced = (u, tuple(-x for x in u), v, tuple(-x for x in v), tuple(-x for x in tau))
    sparse, sums = [], []
    for triple in (False, True):
        for i in range(4):
            sparse.append([int((i != j) if triple else (i == j)) for j in range(4)] + [0]*5)
            signs = [tau[j]*(int(i == j)-(not triple)) for j in range(4)]
            sums.append(signs + [word[i] for word in balanced])
    for i, (top, bottom) in enumerate(zip(P9, ((0,)*5, *K9), strict=True)):
        sparse.extend([[0]*4 + [int(i == 0 or j+1 == i) for j in range(5)]]*2)
        row = [*top, *bottom]
        sums.extend((row, [-x for x in row]))
    dense = [[(-1)**((i & j).bit_count() % 2) for j in (1, 2, 3, 4, 8, 9, 10, 11, 12)]
             for i in range(1, 16) if i != 8]
    rows = []
    for i, (m, d) in enumerate(zip(sums + [[0]*9 for _ in dense], sparse + dense, strict=True)):
        mask, position = (ACTIVE9, i) if i < len(sums) else (DENSE9, i-len(sums))
        sign = 2*(mask >> position & 1)-1
        row = [sign*(x+y) for x,y in zip(m,d,strict=True)] + [sign*(x-y) for x,y in zip(m,d,strict=True)]
        assert set(map(abs, row)) == {1}
        rows.append(sum((x > 0) << j for j,x in enumerate(row)))
    assert sum(any(row) for row in sparse) == 20
    return tuple(rows)


def verify_design(t, rows):
    assert len(rows) == 4*t-2 and all(row >> (2*t) == 0 and row.bit_count() == t for row in rows)
    columns = rows_from_columns(2*t, rows)
    assert all(column.bit_count() == 2*t-1 for column in columns)
    bordered = [col | (1 << len(rows)) for col in columns]
    assert verify_orthogonal(4*t, bordered) == t*(2*t-1)
    return columns


def transversals(columns, pairing, height):
    mask = (1 << height)-1
    for i,j in pairing:
        mask &= columns[i]^columns[j]
    return mask.bit_count()


def large_pairings(columns, limit, height):
    """Enumerate matchings whose surviving row count is at least the limit."""
    def visit(unpaired, rows):
        if rows.bit_count() < limit:
            return
        if not unpaired:
            yield rows.bit_count()
            return
        first, *others = unpaired
        for j, partner in enumerate(others):
            yield from visit(others[:j] + others[j+1:], rows & (columns[first]^columns[partner]))
    return Counter(visit(list(range(len(columns))), (1 << height)-1))


def verify():
    cols5 = verify_design(5, R5)
    assert transversals(cols5, PAIRING5, len(R5)) == 6
    print('R(5): exact residual and a pairing with six transversal blocks')
    rows9 = r9()
    cols9 = verify_design(9, rows9)
    assert transversals(cols9, tuple((j,j+9) for j in range(9)), len(rows9)) == 14
    high = large_pairings(cols9, 14, len(rows9))
    assert high == {14: 1}
    print('R(9): exact residual, one pairing with fourteen transversals, none larger')


if __name__ == '__main__':
    verify()
