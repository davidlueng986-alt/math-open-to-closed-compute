"""Independent finite-difference audit and positive controls for the Hadamard case study."""
import argparse
import itertools
import json
import math
from collections import Counter, defaultdict
from functools import cache
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
P = 149
ORIGIN = np.array([1, 1, 1, 2])
COSETS = [sorted(pow(2, c + 4*i, P) for i in range(37)) for c in range(4)]


def base_orbits():
    unvisited = {sum(1 << i for i in cells) for cells in itertools.combinations(range(16), 4)}
    while unvisited:
        rep = min(unvisited)
        todo, orbit = [rep], {rep}
        while todo:
            m = todo.pop()
            grid = np.array([(m >> i) & 1 for i in range(16)]).reshape(4, 4)
            neighbors = [np.roll(grid, 1, axis=1), grid[[1, 0, 2, 3]], grid[[0, 2, 1, 3]]]
            for f in range(4):
                moved = grid.copy()
                moved[f] = np.roll(moved[f], 2)
                neighbors.append(moved)
            for a in neighbors:
                other = sum(1 << int(i) for i in np.flatnonzero(a))
                if other not in orbit:
                    orbit.add(other)
                    todo.append(other)
        unvisited -= orbit
        yield rep, len(orbit)


def support_array(mask):
    a = np.zeros((4, P), dtype=np.int16)
    for i in range(16):
        if mask >> i & 1:
            a[i//4, COSETS[i % 4]] = 1
    return a


@cache
def target_rows(k, sizes):
    bound = math.isqrt(4*k+3)
    squares = defaultdict(list)
    values = []
    for off, size in zip(ORIGIN, sizes):
        values.append([x for x in range(-bound, bound+1)
                       if x in range(int(off-2*size), int(off+2*size)+1, 4)])
    for x, y in itertools.product(*values[:2]):
        squares[x*x+y*y].append((x, y))
    return [prefix+(z, w) for z, w in itertools.product(*values[2:])
            for prefix in squares[4*k+3-z*z-w*w]]


def congruences(a):
    """Evaluate the all-positive PAF and its single-flip differences directly."""
    k = a.shape[1]
    t = 2*a.copy()
    t[:, 0] = ORIGIN
    f, y = np.nonzero(a)
    shifts = np.arange(1, (k+1)//2)[:, None]
    forwards = t[f, (y+shifts) % k]
    backwards = t[f, (y-shifts) % k]
    paf = 2*forwards.sum(axis=1) + (t[:, shifts[:, 0]].T * ORIGIN).sum(axis=1)
    if np.any(paf % 4):
        return None
    return (forwards+backwards) % 4, (paf//4) % 4


def row_forms(coeff, rhs):
    """Solve Boolean parity equations, with the highest coefficient as pivot."""
    count = coeff.shape[1]
    odd = coeff % 2
    lengths = odd.sum(axis=1)
    high = (coeff//2) % 2
    for i in np.flatnonzero((lengths == 2) & (rhs % 2 == 0)):
        high[i, np.flatnonzero(odd[i])[0]] ^= 1
    binary = np.concatenate([odd, high[lengths <= 2]])
    sides = np.concatenate([rhs % 2, (rhs[lengths <= 2] // 2) % 2])
    pivots = {}
    for packed, s in zip(np.packbits(binary.astype(np.uint8), axis=1, bitorder="little"), sides):
        bits = int.from_bytes(packed.tobytes(), "little")
        s = int(s)
        while bits:
            j = bits.bit_length()-1
            if j not in pivots:
                pivots[j] = bits ^ (1 << j), s
                break
            row, side = pivots[j]
            bits ^= (1 << j) | row
            s ^= side
        else:
            if s:
                return None
    forms, dim = [], 0
    for j in range(count):
        if j not in pivots:
            dim += 1
            forms.append(1 << dim)
            continue
        bits, s = pivots[j]
        while bits:
            b = bits & -bits
            s ^= forms[b.bit_length()-1]
            bits ^= b
        forms.append(s)
    return forms


def norm_survives(a, forms, targets):
    # Expand row sums as integer linear combinations of distinct parity characters.
    by_form = defaultdict(lambda: np.zeros(4, dtype=int))
    by_form[0] += ORIGIN
    for f, form in zip(np.nonzero(a)[0], forms):
        by_form[form >> 1][f] += -2 if form & 1 else 2
    offset = by_form.pop(0)
    weights = np.array(list(by_form.values()), dtype=int).reshape((-1, 4))
    directions = list(np.eye(4, dtype=int))
    for u, v in itertools.combinations(np.eye(4, dtype=int), 2):
        directions.extend([u+v, u-v])
    for d in directions:
        widths = np.abs(weights @ d).tolist()
        low = int(offset @ d) - sum(widths)
        reachable = 1
        for step in widths:
            reachable |= reachable << (2*step)
        targets = [r for r in targets if (k := int(d @ r)-low) >= 0 and (reachable >> k) & 1]
        if not targets:
            return False
    return True


def audit_support(a):
    # Test the norm first. This yields independent rejection counts by stage.
    targets = target_rows(a.shape[1], tuple(map(int, a.sum(axis=1))))
    if not targets:
        return "norm"
    parity = a[:3].sum(axis=0) % 2
    if not np.array_equal(parity[1:], parity[:0:-1]):
        return "parity"
    system = congruences(a)
    if system is None:
        return "parity"
    forms = row_forms(*system)
    if forms is None:
        return "linear"
    return "survives" if norm_survives(a, forms, targets) else "norm_after_elimination"


def check_walsh_controls():
    records = json.loads((HERE/"appendix-a.json").read_text())["witnesses"]
    walsh = np.array([[(-1)**((i & j).bit_count()) for j in range(4)] for i in range(4)])
    out = {}
    for record in records:
        if record["border"] != 12:
            continue
        k = record["group"][-1]
        def decode(s):
            return [1-2*int(b) for b in bin(int("1"+s, 16))[3:][:4*k]]
        a = np.array([decode(s) for s in record["blocks"]]).reshape(4, 4, k)
        w = (walsh @ a)//2
        m = int((np.prod(a, axis=1) < 0).sum())
        for theta in range(4):
            layer = w[:, theta]
            expected = -4 if theta else 0
            assert int((layer*layer).sum()) == 4*k+3+expected
            assert all(int((layer*np.roll(layer, s, axis=1)).sum()) == expected for s in range(1,k))
        row = {"k": k, "mixed": m, "nonzero_shift_equations_checked": 4*(k-1)}
        if m == 3:
            layer = w[:, 0].copy()
            order = sorted(range(4), key=lambda f: not np.any(np.abs(layer[f]) == 1))
            layer = layer[order]
            for f in range(3):
                layer[f] = np.roll(layer[f], -int(np.flatnonzero(np.abs(layer[f]) == 1)[0]))
            primitive = next(g for g in range(2, k) if len({pow(g,i,k) for i in range(k-1)}) == k-1)
            quartics = [[pow(primitive, c+4*j, k) for j in range((k-1)//4)] for c in range(4)]
            distances = []
            for center in np.flatnonzero(np.abs(layer[3]) == 2):
                recentered = layer.copy()
                recentered[3] = np.roll(layer[3], -int(center))
                sizes = sorted((int((np.abs(seq[coset]) == 2).sum()) for seq in recentered
                                for coset in quartics), reverse=True)
                distances.append(k-1-sum(sizes[:4]))
            row["quartic_minimum_exchange_distance"] = min(distances)
            row["fourth_block_centers_tried"] = len(distances)
            row["exchange_distance_by_center"] = distances
            for f, spike in enumerate(ORIGIN):
                y = np.flatnonzero(np.abs(layer[f]) == spike)[0]
                layer[f] = np.roll(layer[f], -y) * np.sign(layer[f, y])
            support = (np.abs(layer) == 2).astype(np.int16)
            support[:, 0] = 0
            assert audit_support(support) == "survives"
            coeff, rhs = congruences(support)
            negative = (layer[np.nonzero(support)] < 0).astype(np.int16)
            assert np.all((coeff @ negative-rhs) % 4 == 0)
            assert all(int(np.sum(layer*np.roll(layer, s, axis=1))) % 32 == 0 for s in range(1,k))
            row["positive_control"] = "original signs pass the norm sieve and every shift modulo 16 and 32"
        out[str(record["order"])] = row
    return out


def three_layers():
    # The four cosets are 2^c times the quartic residues. Signs are per selected cell.
    spec = [(0x0093, [1,-1,-1,1]), (0x006c, [1,-1,1,-1]), (0xa500, [1,-1,1,-1])]
    used = 0
    out = []
    for mask, signs in spec:
        assert not mask & used
        used |= mask
        x = np.zeros((4, P), dtype=int)
        x[:3, 0] = 1
        for i, sign in zip((i for i in range(16) if mask >> i & 1), signs):
            x[i//4, COSETS[i % 4]] = 2*sign
        assert int((x*x).sum()) == 595
        assert all(int((x*np.roll(x, s, axis=1)).sum()) == -4 for s in range(1,P))
        out.append({"support_mask_hex": hex(mask), "signs_in_increasing_cell_order": signs})
    return {"three_nontrivial_layers": out, "fourth_support_mask_hex": hex(65535 ^ used),
            "shifts_verified": 3*(P-1)}


def three_compression():
    def candidates(ell):
        energy = (4*ell+6)//3
        triplets = []
        for x in range(-math.isqrt(energy), math.isqrt(energy)+1):
            for y in range(x, math.isqrt(energy)+1):
                z = 1-x-y
                if x % 2 and y % 2 and z % 2 and y <= z and max(-x,z) <= ell//3:
                    triplets.append((x,y,z))
        return [(a,b) for i,a in enumerate(triplets) for b in triplets[i:]
                if sum(x*x for x in a+b) == energy]
    seeds = [[1,3,4,7,8,13,14,17,19,24,28,29,36,39,40,47,51,56,63,78,95],
             [2,5,7,9,13,14,18,19,20,24,34,36,39,40,42,47,56,58,73,78,79]]
    triple = []
    for row in seeds:
        plus = {s*h % 117 for s in row for h in (1,16,22)}
        triple.append(tuple(sorted(sum(1 if j in plus else -1 for j in range(c,117,3)) for c in range(3))))
    assert tuple(sorted(triple)) in candidates(117)
    pairs = candidates(1197)
    return {"117_known_sorted_triples": sorted(triple), "117_candidates": len(candidates(117)),
            "1197_candidates": len(pairs), "1197_example": pairs[0]}


def replay_lift():
    census = json.loads((HERE/"lift-2396.json").read_text())
    cert = census["best"]
    occupied = [int(s, 16) for s in cert["supports"]]
    negative = [int(s, 16) for s in cert["negative"]]
    assert all(u.bit_length() <= P and not (u & 1) and not (n & ~u)
               for u, n in zip(occupied, negative))
    value = np.zeros((4, P), dtype=np.int64)
    for f in range(4):
        value[f,0] = ORIGIN[f]
        for j in range(1, P):
            if (occupied[f] >> j) & 1:
                value[f,j] = -2 if (negative[f] >> j) & 1 else 2
    sums = value.sum(axis=1)
    # Linear autocorrelation plus its wrapped tail gives cyclic autocorrelation.
    linear = sum(np.correlate(row, row, mode="full") for row in value)
    paf = linear[P-1:].copy()
    paf[1:] += linear[:P-1]
    half = paf[1:(P+1)//2]
    assert np.array_equal(half, census["half_autocorrelations"])
    assert np.array_equal(sums, cert["row_sums"]) and sum(sums*sums) == paf[0] == 599
    assert np.array_equal(paf[1:], paf[:0:-1]) and not np.any(half % 16)
    metric = [int(half @ half), int(np.abs(half).max()), int(np.count_nonzero(half))]
    assert metric == cert["score"]
    return {"seed": cert["seed"], "row_sums": sums.tolist(), "score": metric,
            "mod32_failures_in_74_shifts": int(np.count_nonzero(half % 32))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exchanges", action="store_true", help="also replay every one-exchange class")
    args = parser.parse_args()
    out = {"controls": check_walsh_controls(), "projection_2396": three_layers(),
           "legendre_mod_3": three_compression(), "alternative_support_witness": replay_lift()}
    base, moves = Counter(), Counter()
    for mask, weight in base_orbits():
        a = support_array(mask)
        base[audit_support(a)] += weight
        if args.exchanges:
            for i in range(16):
                if not mask >> i & 1:
                    continue
                f, c = divmod(i, 4)
                source = COSETS[c][-1]
                for g, z in zip(*np.nonzero(1-a)):
                    if z:
                        a[f,source], a[g,z] = 0, 1
                        moves[audit_support(a)] += 37*weight
                        a[f,source], a[g,z] = 1, 0
    assert sum(base.values()) == 1820
    out["bases"] = dict(sorted(base.items()))
    if args.exchanges:
        assert sum(moves.values()) == 119595840
        out["one_exchange"] = dict(sorted(moves.items()))
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
