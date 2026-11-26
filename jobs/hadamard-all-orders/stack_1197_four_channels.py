"""Replay a second exact 1197-column stack at 2396 using four H300 channels."""

import argparse
from hashlib import sha256
from pathlib import Path

from stack_1197 import assemble, correlations, flipped_column, normalize, source_matrices
from stack_1198 import export_search, projection_targets
from stack_odd_t_residual import paley_type_two, sylvester_four
from verify import verify_orthogonal


UPPER_FLIPS = (
    475, 1021, 819, 975, 61, 103, 916, 35, 867, 1010, 120, 825, 1158, 938, 710, 775,
    627, 329, 754, 995, 800, 348, 553, 853, 469, 386, 650, 795, 16, 390, 407, 611,
)
LOWER_FLIPS = (
    815, 790, 1030, 1012, 646, 92, 1147, 462, 1098, 1035, 974, 896, 1110, 1163, 761,
    605, 180, 729, 394, 907, 227, 613, 818, 585, 158, 1119, 190, 215, 123, 782, 497,
    376, 486, 1050,
)
LOWER_OMITTED = (967, 814, 93, 304)
COLUMN_HASH = '1fadec78a5e38794c1c3fe117cdb4461bf837905bde612b7a2a172f07d3965ef'


def sources():
    upper, _ = source_matrices()
    lower = normalize(sylvester_four(paley_type_two(149)))
    u = flipped_column(len(upper), UPPER_FLIPS)
    v = flipped_column(len(lower), LOWER_FLIPS)
    return upper, lower, u, v


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--export', type=Path, help='input file for bounded next-column searches')
    args = parser.parse_args()
    upper, lower, u, v = sources()
    columns = assemble(upper, lower, u, v, LOWER_OMITTED)
    assert len(columns) == 1197 and verify_orthogonal(2396, columns) == 715806
    before = correlations(lower, v)
    assert [before[j] for j in LOWER_OMITTED] == [-8, -36, -60, -68]
    assert sorted(j // 300 for j in LOWER_OMITTED) == [0, 1, 2, 3]
    digest = sha256(''.join(f'{col:x}\n' for col in columns).encode('ascii')).hexdigest()
    assert digest == COLUMN_HASH
    print('Four-channel stack: 1197 columns, 715806 exact products, one omission per H300 channel')
    print('Four-channel stack packed SHA256', digest)
    targets = projection_targets(upper, lower, v, LOWER_OMITTED)
    if args.export is not None:
        export_search(args.export, upper, lower, u, v, targets, LOWER_OMITTED)


if __name__ == '__main__':
    main()
