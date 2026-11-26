"""Replay exact-dual witnesses of peak 40 and the fixed-tail census."""

import argparse
from io import StringIO
import os
from pathlib import Path
import shlex
import subprocess
from tempfile import TemporaryDirectory

from border4_2396 import periodic
from border4_2396_493 import product_mod2, reverse_mod2
from border4_2396_dual_peak48 import PEAK48_MASKS, check_primitive_norm
from border4_2396_dual_quotient import dual_words, replay
from border4_2396_full_y_expanded import Q_MASK, indices
from border4_2396_nested import nested_negative_words
from border4_2396_primitive_field import primitive_factor


PEAK40_325_MASKS = (
    0x311E0020B48006D0300084000421802A99400E00082A010018A000390009780086F04101808,
    0x5001184C1202300000900403C0910E90601600003204006C0900971048C8A083906101E00,
    0x282450080792108805954008844006020100002018000423110884006010A808060300C600,
    0x1448280018C0301804054201800844223108000601000020101800884400AA680442127804,
)
PEAK40_293_MASKS = (
    0x71120800A08007383282A44407C1822519000602082B000068A000010009380A87D01001808,
    0x20018001002902080900C03C08308D0400C00082A00000A082037004988A081006101C08,
    0x2824500C07921088059500088440060201000020180004211108840060108808060300C600,
    0x1448280018C03018040442018008442221080006010000201018008844002A68044212780C,
)
PEAK40_LOW_ENERGY_MASKS = (
    0x31000800D08007E81080C4000481802898400E00083A010024A800750049A80084804002808,
    0x107001181C1202E8200050040380910810400D80083704107E08008F0209A88081106907A08,
    0xA8A1718805911008019440088440060001000020188000220108840060102828040200C840,
    0x31D0A2A0084C01008050502018008442011000046010000200018008844008A600402226804,
)
FIXED_HEAD_SOURCE = (
    0x200200000080021010008000000100080840420200200100002020000008000004000001800,
    0x18080002802000200C0240010810400800000200000C00200B0008808000002002C00,
    0,
    0,
)
FIXED_TAILS = (
    PEAK48_MASKS[2:],
    PEAK40_293_MASKS[2:],
    (
        0x2282454880793108805954008844006020100002018000423110884006010A808060300C600,
        0x25448288018C0301804054201800844223108000601000020101800884400AA680442327804,
    ),
    (
        0x2C02855080B901188009D2008004006010100002018840020010840006010B028000302DA00,
        0x15428068016D03000050342018000842001000846010000202018008004012E400462027404,
    ),
)


def limbs(value, count):
    return tuple((value >> (64 * j)) & ((1 << 64) - 1) for j in range(count))


def head_blocks(row, theta):
    sites = [[next(i for i in range(y, 299, 23) if i % 13 == x)
              for x in range(13)] for y in range(23)]
    allowed = [sum(1 << x for x, i in enumerate(cells) if row[i]) for cells in sites]
    blocks = []
    for y in range(12):
        opposite = (-y) % 23
        options = []
        for a, b in enumerate(theta):
            if a & ~allowed[y] or b & ~allowed[opposite] or (y == 0 and a != b):
                continue
            first = [sites[y][x] for x in indices(a)]
            last = [sites[opposite][x] for x in indices(b)] if y else []
            if sum(row[i] for i in first) or sum(row[i] for i in last):
                continue
            locations = first + last
            packed_charge = sum(row[i] * (1 << (6 * (i % 13))) for i in locations)
            flip_mask = sum(1 << i for i in locations)
            options.append((*limbs(packed_charge, 2), *limbs(flip_mask, 5)))
        assert options
        if len(options) > 1:
            blocks.append(options)
    return blocks


def census():
    complement = ((1 << 13) - 1) ^ Q_MASK
    squared = product_mod2(complement, complement, 13)
    theta = [product_mod2(squared, reverse_mod2(a, 13), 13) for a in range(1 << 13)]
    assert all(theta[b] == a for a, b in enumerate(theta))
    heads = dual_words(FIXED_HEAD_SOURCE)[:2]
    data = StringIO()
    for row in heads:
        print(*row, file=data)
    print(len(FIXED_TAILS), file=data)
    for masks in FIXED_TAILS:
        tails = dual_words((0, 0, *masks))[2:]
        assert tuple(map(sum, heads + tails)) == (0, 1, 0, 0)
        for q, diagonal, off_diagonal in ((13, 553, -46), (23, 573, -26)):
            compressed = tuple(tuple(sum(row[i::q]) for i in range(q)) for row in heads + tails)
            assert periodic(compressed) == [diagonal] + [off_diagonal] * (q - 1)
        for row in tails:
            print(*row, file=data)
    for row in heads:
        blocks = head_blocks(row, theta)
        print(len(blocks), file=data)
        for block in blocks:
            print(len(block), file=data)
            for option in block:
                print(*option, file=data)
    source = Path(__file__).with_suffix(".cpp")
    compiler = shlex.split(os.environ.get("CXX", "g++"))
    with TemporaryDirectory() as directory:
        executable = Path(directory) / "peak40"
        subprocess.run([*compiler, "-O3", "-std=c++20", source, "-o", executable], check=True)
        subprocess.run([executable], input=data.getvalue(), text=True, check=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--census", action="store_true")
    args = parser.parse_args()
    negative = nested_negative_words()
    assert periodic(negative) == [599] + [0] * 298
    factor = primitive_factor(7)
    fixtures = (
        (PEAK40_325_MASKS, (325, 77, 40, 251904), 129, 77, 106),
        (PEAK40_293_MASKS, (293, 93, 40, 275456), 181, 93, 118),
        (PEAK40_LOW_ENERGY_MASKS, (253, 69, 40, 211456), 129, 69, 110),
    )
    for masks, metrics, mod32, mod64, nonzero in fixtures:
        positive = dual_words(masks)
        assert tuple(map(sum, positive)) == (0, 1, 0, 0)
        residual = replay(positive, negative, metrics, mod32, 5)
        assert 1 + 2 * sum(value % 8 == 0 for value in residual[1:]) == mod64
        assert check_primitive_norm(positive, residual, factor) == nonzero
        print(f"mod16/exact/peak/energy {metrics}; mod32 {mod32}, "
              f"mod64 {mod64}, mod7 primitive nonzero {nonzero}.", flush=True)
    if args.census:
        census()


if __name__ == "__main__":
    main()
