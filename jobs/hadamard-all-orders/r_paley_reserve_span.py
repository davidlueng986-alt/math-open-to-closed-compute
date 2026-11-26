"""Replay the full old reserve span and distance-five exclusion for both exteriors."""

from collections import Counter
from hashlib import sha256
import json
from math import isqrt
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from r_paley_full92_contrast import AGREE, OPPOSITE
from r_paley_full92_skew import SOURCE_DIGEST, build_source, frame
from r_paley_full92_unrestricted import NEXT_PIVOTS, NEXT_ROOTS, NEXT_SELECTED
from r_paley_isotropic_code import half_projections, rank_mod
from r_paley_punctured_fibre import ALT_SELECTED
from verify import verify_orthogonal


PRIME = 599
ORDER = 1196
SQUARED_NORM = PRIME * 596


def check_arithmetic():
    bound = 962
    left = PRIME * 579 - (299 * bound + 596)
    assert left > 0 and left * left > 4 * 299 * bound * 596
    assert SQUARED_NORM // (2 * PRIME - bound) ** 2 == 6
    assert 340 * 3 < 2 * PRIME + 3
    assert (340 + 17 * 6) * 5 < 4 * PRIME + 3
    assert all(pow(x % PRIME, (PRIME - 1) // 2, PRIME) == PRIME - 1
               for x in (-1, -19, -27))
    assert 7 % PRIME != 0


def check_contacts(source, unused, rows, pivots, contacts, expected_bound, sparse_root):
    axes = []
    for r, g in zip(rows, pivots, strict=True):
        word = source[g] ^ (1 << r)
        projections = half_projections(source, word)
        axes.append(tuple(projections[j] - PRIME * (j == g) for j in unused))
    assert rank_mod(axes, PRIME) == 17
    axis_rows = list(zip(*axes, strict=True))
    nonpivots = [row for g, row in zip(unused, axis_rows, strict=True) if g not in pivots]
    assert len(nonpivots) == 579
    assert all(abs(x) == 1 for row in nonpivots for x in row)
    multiplicities = Counter(min(row, tuple(-x for x in row)) for row in nonpivots)
    assert max(multiplicities.values()) == 2

    l1_bound = 0
    assert len(contacts) == 17
    for axis, matching in enumerate(contacts):
        used = set()
        assert len(matching) >= 107
        for contact in matching:
            assert len(contact) == 4
            signed_rows = []
            for i in contact:
                index = abs(i) - 1
                assert 0 <= index < len(nonpivots) and index not in used
                used.add(index)
                direction = 1 if i > 0 else -1
                signed_rows.append(tuple(direction * x for x in nonpivots[index]))
            assert tuple(map(sum, zip(*signed_rows, strict=True))) == tuple(
                2 * (j == axis) for j in range(17)
            )
        l1_bound += isqrt(SQUARED_NORM // len(matching))
    assert l1_bound == expected_bound
    root = dict(sparse_root)
    assert len(root) == 5 and set(root) <= set(unused) - set(pivots)
    assert all(value % PRIME != 0 for value in root.values())
    assert sum(value * value for value in root.values()) == 2 * PRIME
    assert all(sum(value * coefficient for value, coefficient in zip(
        (root.get(g, 0) for g in unused), axis, strict=True
    )) == 0 for axis in axes)
    print(f"Old span: 17 disjoint-contact matchings force centered coefficient norm <= {l1_bound}",
          flush=True)


def replay():
    check_arithmetic()
    source = build_source()
    assert verify_orthogonal(ORDER, source) == 714610
    assert sha256(b"".join(c.to_bytes(150, "little") for c in source)).hexdigest() == SOURCE_DIGEST
    frame_rows, frame_pivots = frame()
    fixed_rows = tuple(frame_rows[j] for j in AGREE + OPPOSITE)
    fixed_pivots = tuple(frame_pivots[j] for j in AGREE + OPPOSITE)
    cases = (
        (NEXT_SELECTED, NEXT_ROOTS, NEXT_PIVOTS, 958,
         ((3, 14), (256, -14), (399, -9), (1066, -14), (1089, 23))),
        (ALT_SELECTED, (972, 1013, 1066, 1051, 429), (1027, 645, 204, 324, 636), 962,
         ((3, 14), (166, -9), (256, -14), (684, 14), (822, -23))),
    )
    source_input = "\n".join(
        " ".join(str((column >> (64 * j)) & ((1 << 64) - 1)) for j in range(19))
        for column in source
    )
    native = Path(__file__).with_suffix(".cpp")
    contacts = json.loads(Path(__file__).with_name("r_paley_reserve_span_contacts.json").read_text())
    with TemporaryDirectory() as folder:
        executable = Path(folder) / "reserve_span"
        subprocess.run(["c++", "-O3", "-std=c++17", str(native), "-o", str(executable)], check=True)
        for (mask, rows, pivots, bound, sparse_root), matchings in zip(cases, contacts, strict=True):
            unused = tuple(g for g in range(ORDER) if not ((mask >> g) & 1))
            assert len(unused) == 596
            data = (unused, fixed_rows + rows, fixed_pivots + pivots)
            check_contacts(source, *data, matchings, bound, sparse_root)
            encoded = "\n".join(" ".join(map(str, line)) for line in data)
            subprocess.run([str(executable)], input=encoded + "\n" + source_input + "\n",
                           text=True, check=True)
    print("Reserve-code distance >= 5, attained by one finite-field control per exterior")


if __name__ == "__main__":
    replay()
