"""Independent quadratic audit of the 4,096 fixed supports at order 2396."""
import json
import random
from collections import Counter
from functools import cache

import numpy as np

from case_study import HERE, ORIGIN, P, congruences, norm_survives, row_forms, target_rows


def support(seed):
    rng = random.Random(seed)
    fourth = set(rng.sample(range(1, P), 32)) | {0}
    opposite_pairs = range(1, (P+1)//2)
    eligible = [s for s in opposite_pairs if sum((y+s) % P in fourth for y in fourth) % 2]
    for _ in range(128):
        rng.shuffle(eligible)
        empty = set()
        for s in eligible:
            twice, half = (2*s) % P, (pow(2, -1, P)*s) % P
            if empty.isdisjoint({min(twice, P-twice), min(half, P-half)}):
                empty.add(s)
                if len(empty) == 16:
                    break
        if len(empty) == 16:
            break
    else:
        raise ValueError(f"no template for seed {seed}")
    points = [s for s in opposite_pairs if s not in empty]
    rng.shuffle(points)
    a = np.zeros((4, P), dtype=np.int16)
    for f, chosen in enumerate((points[:18], points[18:36], points[36:])):
        for s in chosen:
            a[f, [s, -s]] = 1
    a[3, sorted(fourth - {0})] = 1
    return a


def positions(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length()-1
        mask ^= bit


@cache
def low_truth_tables(width):
    # One packed bit for each assignment of the low coordinates.
    assignments = np.arange(1 << width, dtype=np.uint32)
    return [int.from_bytes(np.packbits(((assignments >> j) & 1).astype(np.uint8),
                                       bitorder="little").tobytes(), "little") for j in range(width)]


def count_norm(a, forms, dim):
    """Evaluate the squared row norm on the free coordinates by a Walsh transform."""
    rows = [Counter({0: int(c)}) for c in ORIGIN]
    for f, form in zip(np.nonzero(a)[0], forms):
        rows[f][form >> 1] += -2 if form & 1 else 2
    energy = np.zeros(1 << dim, dtype=np.int32)
    # Products of two Walsh characters have their binary sum as frequency.
    for row in rows:
        for i, u in row.items():
            for j, v in row.items():
                energy[i ^ j] += u*v
    for bit in range(dim):
        step = 1 << bit
        blocks = energy.reshape(-1, 2*step)
        left, right = blocks[:, :step], blocks[:, step:]
        saved = left.copy()
        left += right
        np.subtract(saved, right, out=right)
    return int(np.count_nonzero(energy == 599))


def project(a, forms):
    f, y = np.nonzero(a)
    seq = np.zeros_like(a, dtype=np.int32)
    seq[:, 0] = ORIGIN
    dim = max(form.bit_length() for form in forms)-1
    shifts = (P-1)//2

    def evaluate(x):
        coordinate = (x << 1) | 1
        seq[f,y] = [2-4*((coordinate & form).bit_count() % 2) for form in forms]
        linear = sum(np.correlate(row, row, mode="full") for row in seq)
        half = linear[P:P+shifts] + linear[:shifts]
        assert not np.any(half % 16)
        flags = np.packbits((half % 32 != 0).astype(np.uint8), bitorder="little")
        return int.from_bytes(flags.tobytes(), "little")

    # Each shift, divided by 16 on the affine space and reduced modulo 2, is quadratic.
    # Interpolation at zero, singletons and pairs recovers its multilinear coefficients.
    constant = evaluate(0)
    linear = [evaluate(1 << i) ^ constant for i in range(dim)]
    pair = {(i,j): evaluate((1 << i) | (1 << j)) ^ constant ^ linear[i] ^ linear[j]
            for j in range(dim) for i in range(j)}
    for sample in (2026, (1 << dim)-1, ((1 << dim)-1)//3):
        chosen = list(positions(sample & ((1 << dim)-1)))
        predicted = constant
        for j in chosen:
            predicted ^= linear[j]
            for i in chosen:
                if i < j:
                    predicted ^= pair[i,j]
        assert predicted == evaluate(sample)

    width = min(14, dim)
    variables = low_truth_tables(width)
    full = (1 << (1 << width))-1
    low = [full if (constant >> s) & 1 else 0 for s in range(shifts)]
    derivatives = [[0]*shifts for _ in range(dim-width)]
    for j in range(width):
        for s in positions(linear[j]):
            low[s] ^= variables[j]
        for i in range(j):
            monomial = variables[i] & variables[j]
            for s in positions(pair[i,j]):
                low[s] ^= monomial
    for j in range(width, dim):
        for i in range(width):
            for s in positions(pair[i,j]):
                derivatives[j-width][s] ^= variables[i]

    high, scalar = 0, 0
    total = valid = 0
    for step in range(1 << (dim-width)):
        if step:
            bit = step & -step
            j = width + bit.bit_length()-1
            scalar ^= linear[j]
            for k in positions(high & ~bit):
                i = k+width
                scalar ^= pair[min(i,j),max(i,j)]
            high ^= bit
            low = [q ^ d for q, d in zip(low, derivatives[j-width])]
        candidates = full
        for s, table in enumerate(low):
            candidates &= table if (scalar >> s) & 1 else ~table
            if not candidates:
                break
        total += candidates.bit_count()
        for rest in positions(candidates):
            assert evaluate((high << width) | rest) == 0
            row_sums = seq.sum(axis=1)
            valid += int(row_sums @ row_sums == 599)
    return dim, total, valid


def run():
    seen, verdicts, rows, before_norm = set(), Counter(), [], []
    dimensions = Counter()
    for seed in range(4096):
        a = support(seed)
        key = np.packbits(a).tobytes()
        assert key not in seen
        seen.add(key)
        equations = congruences(a)
        forms = row_forms(*equations) if equations is not None else None
        if forms is None:
            verdicts["inconsistent"] += 1
            continue
        dim, raw, valid = project(a, forms)
        dimensions[dim] += 1
        if raw:
            before_norm.append({"seed":seed,"signings":raw})
        targets = target_rows(P, tuple(map(int, a.sum(axis=1))))
        if not norm_survives(a, forms, targets):
            assert not valid
            verdicts["norm_rejected"] += 1
            continue
        rows.append({"seed":seed,"dimension":dim,"norm_and_mod16":count_norm(a, forms, dim),
                     "mod32_before_norm":raw,"mod32_and_norm":valid})
        verdicts["exhausted"] += 1
    return {"distinct_supports":len(seen),"statuses":dict(sorted(verdicts.items())),
            "all_mod16_affine_spaces_by_dimension":dict(sorted(dimensions.items())),
            "signings_in_all_mod16_spaces":sum((1 << d)*count for d,count in dimensions.items()),
            "mod32_before_any_norm_sieve":before_norm,"spaces_passing_norm_sieve":rows,
            "norm_and_mod16":sum(r["norm_and_mod16"] for r in rows),
            "mod32_with_norm":sum(r["mod32_and_norm"] for r in rows)}


if __name__ == "__main__":
    audit = run()
    public = json.loads((HERE/"lift-2396.json").read_text())
    direct = {r["seed"]:(r["dim"], r["norm_hits"], r["mod32_hits"]) for r in public["enumerated"]}
    quadratic = {r["seed"]:(r["dimension"], r["norm_and_mod16"], r["mod32_and_norm"])
                 for r in audit["spaces_passing_norm_sieve"]}
    assert quadratic == direct and audit["statuses"] == public["statuses"]
    assert audit["norm_and_mod16"] == public["norm_and_mod16"]
    assert audit["mod32_with_norm"] == public["norm_and_mod32"]
    print(json.dumps(audit, indent=2))
