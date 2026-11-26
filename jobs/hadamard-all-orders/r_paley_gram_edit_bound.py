"""Exact small monotone factor and arithmetic for the Paley binary edit bounds."""

from hashlib import sha256
from itertools import combinations
from math import isqrt

from r_paley_isotropic_code import assemble
from verify import rows_from_columns, verify_orthogonal


SMALL_DIGEST = "b87f5fde420102a00260ea7dddb46e74c04a4c493bd4bffa54c4834cef5a0c8a"


def verify_small():
    m = 8
    mask = (1 << m) - 1
    source = [sum((1 - (r & j).bit_count() % 2) << r for r in range(m)) for j in range(m)]
    assert source[0] == mask and verify_orthogonal(m, source) == 28
    reserve = (1, 2)
    old = [word for j in reserve for word in (source[j], source[j] ^ mask)]
    assert all(word.bit_count() == m // 2 for word in old)
    untouched = (0, 1, 2, 3)
    changed = (4, 7, 5, 6)
    first = [word ^ (1 << r) for word, r in zip(old, changed, strict=True)]
    last = [
        (1 << i) | sum(1 << r for word, r in zip(old, changed, strict=True) if word >> i & 1)
        for i in untouched
    ]
    assert all(old[j] >> r & 1 for j, r in enumerate(changed))
    assert all(word.bit_count() == m // 2 - 1 for word in first + last)
    base = rows_from_columns(m, old)
    built = rows_from_columns(m, first + last)
    for r in range(m):
        for s in range(m):
            assert (built[r] & built[s]).bit_count() == (base[r] & base[s]).bit_count() + (r == s)

    selected = [j for j in range(m) if j not in reserve]
    columns = assemble(5, source, selected, first + last)
    assert len(columns) == 20 and verify_orthogonal(20, columns) == 190
    assert sha256(b"".join(c.to_bytes(3, "little") for c in columns)).hexdigest() == SMALL_DIGEST
    print("Pure-deletion control: full H20, all 190 products zero, SHA256", SMALL_DIGEST)


def verify_bounds():
    # The square gap is positive at 44, and increases for every larger m.
    assert (44 - 4)**2 - 36 * 44 == 16
    assert 2 * 44 - 44 > 0
    m = 1196
    one_deletion_rows = 6 * isqrt(m)
    many_deletion_rows = (m + 4) // 2
    pure_rows = 4 + one_deletion_rows + many_deletion_rows
    assert (one_deletion_rows, many_deletion_rows, pure_rows) == (204, 600, 808)
    assert m - 4 > one_deletion_rows
    assert m - pure_rows == 388

    # Fixed-exterior inputs come from the independently replayed 1217 controls.
    old_columns, single_flip_maximum, other_distance = m - 4, 17, 11
    additions_per_other_column = (other_distance - 1) // 2
    assert additions_per_other_column == 5
    assert (old_columns - single_flip_maximum) * additions_per_other_column == 5875
    print("H1196 binary factor: at least 388 different rows require old-column additions")
    print("Fixed 1217 exteriors: at least 5875 additions among the 1192 old columns")


if __name__ == "__main__":
    verify_small()
    verify_bounds()
