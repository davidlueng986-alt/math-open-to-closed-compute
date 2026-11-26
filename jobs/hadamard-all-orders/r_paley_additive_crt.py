"""Verify the blockwise additive CRT obstruction for the double-far source family."""

from itertools import combinations
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from r_paley_double_far import WILLIAMSON, build_source, fibres
from r_paley_far_family import quaternion_basis
from r_paley_period23_support import affine_representatives, selector_family
from verify import signs


PAIRS = ((32, 19), (45, 6))


def first_channel():
    source = build_source()
    groups = fibres()
    masks = [sum(1 << r for r in group) for group in groups]
    g = [[2 * (source[col[0]] & mask).bit_count() - 23 for col in groups] for mask in masks]
    assert all(2 * (source[j] & mask).bit_count() - 23 == g[i][k]
               for k, cols in enumerate(groups) for j in cols for i, mask in enumerate(masks))
    for first, second in PAIRS:
        words = [tuple(1 if row[pivot] > 0 else -1 for row in g) for pivot in (first, second)]
        words = [tuple(w[0] * z for z in w) for w in words]
        assert sum(x * y for x, y in zip(*words, strict=True)) == 0
        p, q = [[sum(a * b for a, b in zip(word, row, strict=True)) for row in zip(*g, strict=True)]
                for word in words]
        blocks = [[j for j in range(13 * b, 13 * b + 13) if abs(p[j]) == abs(q[j]) == 2]
                  for b in range(4)]
        modes = [{int(p[j] != q[j]) for j in block} for block in blocks]
        sectors = [next(iter(mode)) for mode in modes]
        sizes = [len(block) for block in blocks]
        assert all(len(mode) == 1 for mode in modes)
        assert [i for i, size in enumerate(sizes) if size == 12] == ([1, 2] if first == 32 else [0, 3])
        assert all(sorted(sz for sz, sign in zip(sizes, sectors, strict=True) if sign == side) == [4, 12]
                   for side in (0, 1))
        yield sizes
        yield sectors
        yield from ([row[j] for block in blocks for j in block] for row in g)


def second_channel(representatives):
    sums = tuple(sum(signs(word)) for word in WILLIAMSON)
    assert sums == (-3, -3, -3, 5)
    basis = quaternion_basis(*sums)
    yield (len(representatives),)
    for word in representatives:
        for component in range(4):
            yield [s * basis[k][component] for k, s in word]


def encode(rows):
    return "".join(" ".join(map(str, row)) + "\n" for row in rows)


def verify():
    directory = Path(__file__).parent
    with TemporaryDirectory() as temp:
        worker = Path(temp) / "additive"
        base_worker = Path(temp) / "base-sequences"
        for exe, cpp in ((worker, Path(__file__).with_suffix(".cpp")),
                         (base_worker, directory / "r_paley_period23_support.cpp")):
            subprocess.run(["g++", "-O3", "-march=native", "-std=c++17", str(cpp), "-o", str(exe)],
                           check=True)
        bases = subprocess.run([str(base_worker), "bases"], check=True, text=True,
                               capture_output=True).stdout
        representatives = affine_representatives(selector_family(bases))
        alpha = subprocess.run([str(worker), "alpha"], input=encode(first_channel()), check=True,
                               text=True, capture_output=True).stdout.splitlines()
        expected = []
        for pair in range(2):
            expected.append(f"one {pair} 24")
            expected.extend(f"two {pair} {u} {v} 33538050 0" for u, v in combinations(range(4), 2))
        assert alpha == expected
        print("Additive CRT: one block at most 552 common projections; two blocks fail both-pair quotas",
              flush=True)
        beta = subprocess.run([str(worker), "beta"], input=encode(second_channel(representatives)),
                              check=True, text=True, capture_output=True).stdout.strip()
        assert beta == "beta 4416 182361 68 28 0"
        print(beta, flush=True)


if __name__ == "__main__":
    verify()
