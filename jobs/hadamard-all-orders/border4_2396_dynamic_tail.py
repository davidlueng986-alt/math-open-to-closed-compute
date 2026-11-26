"""Build and replay an exact two-block dynamic relative-phase search."""

from collections import Counter
from itertools import combinations
import argparse
from pathlib import Path
import subprocess
import tempfile

from border4_2396_full_y_expanded import H, POSITIVE_Y, incident, indices, occupy
from border4_2396_full_y_expanded import reducer, reflect, set_mask
from border4_2396_changed_margins import CHANGED_MARGINS
from border4_2396 import periodic
from border4_2396_nested import nested_negative_words
from border4_2396_shifted_tail import compress, verify_lift

HERE = Path(__file__).parent


def words(mask):
    return tuple((mask >> (64*j)) & ((1 << 64)-1) for j in range(5))


def unpack(row):
    return sum(int(x) << (64*j) for j, x in enumerate(row))


def support_groups(source):
    a, b = source[2], reflect(source[3])
    support = occupy(a)
    assert support == occupy(b)
    last_sites = sorted(support)
    last_columns = [incident(support, i) for i in last_sites]
    rank, solve = reducer(enumerate(last_columns))
    assert rank == 129 and len(last_sites) == 130
    groups = []
    for r, row in enumerate(source[:2]):
        sites = occupy(row)
        for y in POSITIVE_Y:
            groups.append([(r, i, incident(sites, i)) for i in sorted(sites)
                           if i % 23 in (y, 23 - y)])
    return last_sites, solve, groups


def delta_basis(front, solve):
    top = [col for _, _, col in front]
    rem = [solve(col)[0] for col in top]
    top_rank, _ = reducer(enumerate(top))
    rem_rank, decompose = reducer(enumerate(rem))
    delta = {}
    for j, col in enumerate(rem):
        effect = 0
        vector = (1 << j) ^ decompose(col)[1]
        for k in indices(vector):
            effect ^= top[k]
        while effect:
            k = effect.bit_length() - 1
            if k not in delta:
                residual, new_tail = solve(effect)
                assert residual == 0
                delta[k] = (effect, vector, new_tail)
                break
            v, inputs, _ = delta[k]
            effect ^= v
            vector ^= inputs
    assert len(delta) == top_rank - rem_rank
    return top_rank, rem_rank, list(delta.values())


def kernel_basis(sites):
    rank, reduce = reducer((j, t[2]) for j, t in enumerate(sites))
    values = [v for j, (_, _, c) in enumerate(sites)
              for v in [(1 << j) ^ reduce(c)[1]] if v]
    assert len(values) == len(sites)-rank
    return values


def front_mask(vector, front):
    mask = [0, 0]
    for j in indices(vector):
        r, i, _ = front[j]
        mask[r] |= 1 << i
    return tuple(mask)


def inputs(positive):
    tail_sites, solve, groups = support_groups(positive)
    aligned = (*positive[:3], reflect(positive[3]))
    q = set_mask(i for i in tail_sites if aligned[2][i] == aligned[3][i])
    lines = [aligned[0], aligned[1], aligned[2], aligned[3]]
    for j, g in enumerate(groups):
        basis = kernel_basis(g)
        assert len(basis) == 13
        for v in basis:
            f = front_mask(v, g)
            assert not f[1-j//4]
            lines.append(words(f[j//4]))
    phases = {}
    for a, b in combinations(range(8), 2):
        both = groups[a] + groups[b]
        raw_rank, lifted_rank, delta = delta_basis(both, solve)
        assert (raw_rank, lifted_rank, len(delta)) == (26, 20, 6)
        modes = [(0, 0)]
        for _, f, t in delta:
            modes.extend([(x ^ f, y ^ t) for x, y in modes])
        items = []
        for f, t in modes:
            if t.bit_count() % 2:
                continue
            ft = front_mask(f, both)
            rt = set_mask(tail_sites[j] for j in indices(t))
            x = set(indices(q ^ rt))
            y = set(tail_sites) - x
            assert len(x) % 2 == len(y) % 2 == 0
            rank, _ = reducer((i, incident(s, i) | (1 << (H+k)))
                              for k, s in enumerate((x, y)) for i in s)
            assert rank == 128
            items.append((*ft, rt))
        phases[a,b] = items
        lines.append((a, b, len(items)))
        for triple in items:
            lines.append(tuple(x for mask in triple for x in words(mask)))
    assert Counter(map(len, phases.values())) == {32: 22, 64: 6}
    return "\n".join(" ".join(map(str, row)) for row in lines)+"\n", phases


def replay(positive, negative, output, phases, radius):
    result, best = [], None
    for line in output.splitlines():
        if not line.startswith("hit "):
            continue
        a, b, j, c, d, *masks = map(int, line.split()[1:])
        assert len(masks) == 15
        f0, f1, ft = (unpack(masks[k:k+5]) for k in (0,5,10))
        rt = phases[a,b][j][2]

        def switch(row, mask):
            return tuple(-v if mask >> i & 1 else v for i, v in enumerate(row))

        p = (switch(positive[0], f0), switch(positive[1], f1),
             switch(positive[2], ft), reflect(switch(reflect(positive[3]), rt ^ ft)))
        assert tuple(map(sum, p)) == (0, 1, 0, 0)
        qcorr = periodic(tuple(map(compress, p)))
        qc = tuple(v-(553 if i == 0 else -46) for i, v in enumerate(qcorr))
        energy = sum(v*v for v in qc)
        raw = periodic(p)[1:]
        exact = 2*sum(v == -2 for v in raw)+1
        maximum = 2*max(abs(v+2) for v in raw)
        raw_e = 8*sum((v+2)**2 for v in raw)
        signs = tuple("".join(".+-"[0 if v == 0 else 1 if v > 0 else 2] for v in w) for w in p)
        failed = {i for i in range(1, H+1) if (raw[i-1]+2) % 8}
        assert failed == ({c, d} if radius else set())
        verify_lift(signs, negative, list(qc[:7]), 597-4*radius, exact, maximum, raw_e)
        result.append((a,b,j,bool(rt),energy,qc[:7],exact,maximum,raw_e))
        if best is None or (energy,-exact) < (best[0],-best[2]):
            best = (energy,qc[:7],exact,maximum,raw_e,result[-1][:4],signs)
    return result, best


EXPECTED = {
    0: ((1088, 1088, 5695757322, 1331, 45, 44, 0),
        (21632, (-16, -40, 40, 32, 16, 32, -72), 121, 112, 692224)),
    2: ((1088, 1088, 8959426267506, 2134448, 83339, 80246, 0),
        (896, (16, -8, 8, -8, 8, 0, -8), 165, 96, 621056)),
}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--radius", choices=("zero", "two", "both"), default="zero",
                        help="test zero or two inverse errors; both tests both radii")
    args = parser.parse_args()
    negative = nested_negative_words()
    positive = verify_lift(CHANGED_MARGINS, negative, [0]*7, 509, 109, 88, 700928)
    source, phases = inputs(positive)
    radii = {"zero": (0,), "two": (2,), "both": (0, 2)}[args.radius]
    with tempfile.TemporaryDirectory() as directory:
        checker = Path(directory) / "checker"
        subprocess.run(["g++", "-O3", "-std=c++20",
                        str(HERE/"border4_2396_dynamic_tail.cpp"), "-o", str(checker)], check=True)
        for radius in radii:
            check = subprocess.run([str(checker), str(radius)], input=source, text=True,
                                   check=True, capture_output=True)
            count = tuple(map(int, check.stdout.splitlines()[-1].split()[1:]))
            result, best = replay(positive, negative, check.stdout, phases, radius)
            expected_count, expected_best = EXPECTED[radius]
            assert count == expected_count and best[:5] == expected_best
            if radius == 0:
                assert len(result) == 45 and sum(row[3] for row in result) == 44
            print(radius, "inverse errors verified", count, flush=True)
            print("smallest directly checked quotient error", best[:5], flush=True)


if __name__ == "__main__":
    main()
