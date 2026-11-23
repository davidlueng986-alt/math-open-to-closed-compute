"""Exact necessary conditions on the trivial Walsh component of a width-12 core."""
import argparse
import itertools
import json
from collections import Counter, defaultdict
from functools import cache
from pathlib import Path

P = 149
ALL = (1 << P) - 1
RHS = 1 << (4 * P)
TARGET = 4 * P + 3
GENERATOR = 2
COSETS = [[pow(GENERATOR, c + 4 * j, P) for j in range(37)] for c in range(4)]
ORBIT_BITS = [sum(1 << j for j in coset) for coset in COSETS]
ORIGIN = (1, 1, 1, 2)
ENUM_LIMIT = 16


def bits(value):
    while value:
        low = value & -value
        yield low.bit_length() - 1
        value ^= low


def shift(x, s):
    return ((x << s) & ALL) | (x >> (P - s))


def reflected(x):
    return sum(1 << (-i % P) for i in bits(x))


def canonical(mask):
    """Common scaling, reversal in each row, and permutations of the three spike rows."""
    rows = [(mask >> (4 * f)) & 15 for f in range(4)]

    def rotate(row, n):
        return ((row << n) | (row >> (4 - n))) & 15

    def orient(row, n):
        return min(rotate(row, n), rotate(row, (n + 2) % 4))

    return min(tuple(sorted(orient(row, n) for row in rows[:3])) + (orient(rows[3], n),)
               for n in range(4))


def base_classes():
    groups = defaultdict(list)
    for cells in itertools.combinations(range(16), 4):
        mask = sum(1 << i for i in cells)
        groups[canonical(mask)].append(mask)
    return sorted((min(group), len(group)) for group in groups.values())


def supports(mask):
    return [sum(ORBIT_BITS[c] for c in range(4) if mask & (1 << (4*f+c))) for f in range(4)]


@cache
def norm_targets(counts):
    """Exact allowed row sums before any shift equation."""
    options = [[r for r in range(-24, 25) if abs(r - off) <= 2*n and (off + 2*n-r) % 4 == 0]
               for n, off in zip(counts, ORIGIN)]
    return [rows for rows in itertools.product(*options) if sum(r*r for r in rows) == TARGET]


def add_equation(pivots, row, rhs):
    while row:
        i = (row & -row).bit_length()-1
        if i not in pivots:
            pivots[i] = row | ((rhs & 1) * RHS)
            return True
        prior = pivots[i]
        row ^= prior & (RHS-1)
        rhs ^= int(bool(prior & RHS))
    return rhs % 2 == 0


def shift_system(occupied):
    """All low bits. Also the high bit of the mod-16 equation when L_s is 0 or 2."""
    full = [*occupied[:3], occupied[3] | 1]
    pivots = {}
    for s in range(1, (P+1)//2):
        opposite = (1 << s) | (1 << (P-s))
        neighbors = sum(((occupied[f] & opposite) << (f*P)) for f in range(3))
        length = neighbors.bit_count()
        if length % 2:
            return None
        common = 0
        linear = 0
        for f, (u, w) in enumerate(zip(occupied, full)):
            plus, minus = shift(w, s), shift(w, P-s)
            common += (w & plus).bit_count()
            linear |= ((u & (plus ^ minus)) << (f*P))
        d = common + length//2
        if not add_equation(pivots, neighbors, d):
            return None
        if length <= 2:
            if length == 2 and d % 2 == 0:
                linear ^= neighbors & -neighbors
            if not add_equation(pivots, linear, d//2):
                return None
    return pivots


def affine_forms(occupied, pivots):
    # Bit 0 is the constant. Each higher bit is an independent free binary coordinate.
    positions = [f*P+j for f, u in enumerate(occupied) for j in bits(u)]
    forms = {}
    dimension = 0
    for i in reversed(positions):
        if i not in pivots:
            dimension += 1
            forms[i] = 1 << dimension
        else:
            row = pivots[i]
            form = int(bool(row & RHS))
            for j in bits((row & (RHS-1)) ^ (1 << i)):
                form ^= forms[j]
            forms[i] = form
    return forms, dimension


def possible_sums(constant, coefficients):
    # Allow a separate sign per distinct linear form. This is an outer bound.
    values = {constant}
    for w in coefficients.values():
        if w:
            values = {x + d for x in values for d in (w, -w)}
    return values


def compatible_norms(forms, targets):
    offsets = list(ORIGIN)
    coeff = [Counter() for _ in range(4)]
    for position, form in forms.items():
        row = position//P
        w = -2 if form & 1 else 2
        if form >> 1:
            coeff[row][form >> 1] += w
        else:
            offsets[row] += w
    for i in range(4):
        allowed = possible_sums(offsets[i], coeff[i])
        targets = [v for v in targets if v[i] in allowed]
    for i, j in itertools.combinations(range(4), 2):
        if not targets:
            break
        for sign in (1, -1):
            weights = coeff[i].copy()
            for key, w in coeff[j].items():
                weights[key] += sign*w
            allowed = possible_sums(offsets[i]+sign*offsets[j], weights)
            targets = [v for v in targets if v[i]+sign*v[j] in allowed]
    return targets


def exact_projection(occupied, neg):
    full = [*occupied[:3], occupied[3] | 1]
    for s in range(1, (P+1)//2):
        total = 0
        opposite = (1 << s) | (1 << (P-s))
        for f, (w, n) in enumerate(zip(full, neg)):
            common = w & shift(w, s)
            mismatches = common & (n ^ shift(n, s))
            total += 4*(common.bit_count() - 2*mismatches.bit_count())
            if f < 3:
                total += 2*((w & opposite).bit_count() - 2*(n & opposite).bit_count())
        if total:
            return False
    return True


def enumerate_affine(occupied, forms, dimension, targets):
    targets = set(targets)
    masks = [0]*(dimension+1)
    for i, form in forms.items():
        for j in bits(form):
            masks[j] |= 1 << i
    word = masks[0]
    for k in range(1 << dimension):
        if k:
            word ^= masks[(k & -k).bit_length()]
        neg = [(word >> (P*f)) & ALL for f in range(4)]
        rows = tuple(off + 2*(u.bit_count()-2*n.bit_count()) for off,u,n in zip(ORIGIN,occupied,neg))
        if rows in targets and exact_projection(occupied, neg):
            return neg
    return None


def screen(occupied):
    # Odd cross terms mod 4 can be detected across every shift in one operation.
    odd = occupied[0] ^ occupied[1] ^ occupied[2]
    if odd != reflected(odd):
        return "mod4", None
    targets = norm_targets(tuple(u.bit_count() for u in occupied))
    if not targets:
        return "row_norm", None
    pivots = shift_system(occupied)
    if pivots is None:
        return "shift_inconsistent", None
    forms, dimension = affine_forms(occupied, pivots)
    targets = compatible_norms(forms, targets)
    if not targets:
        return "affine_norm", None
    if dimension > ENUM_LIMIT:
        return "unresolved", {"dimension": dimension}
    neg = enumerate_affine(occupied, forms, dimension, targets)
    if neg is None:
        return "affine_exhausted", None
    return "exact_projection", {"negative": [hex(x) for x in neg], "dimension": dimension}


def placements(mask, base):
    # A nonzero source has a free orbit of length 37 under simultaneous quartic scaling.
    for cell in bits(mask):
        f, c = divmod(cell, 4)
        y = COSETS[c][0]
        for g, u in enumerate(base):
            for z in bits((ALL ^ u) & ~1):
                moved = base.copy()
                moved[f] ^= 1 << y
                moved[g] ^= 1 << z
                yield (f, y, g, z), moved


def run(shard, shards):
    if not 0 <= shard < shards:
        raise ValueError("invalid shard")
    result = {"shard": shard, "shards": shards, "classes": []}
    for i, (mask, weight) in enumerate(base_classes()):
        if i % shards != shard:
            continue
        base = supports(mask)
        status, evidence = screen(base)
        tally = Counter()
        survivors = []
        for move, candidate in placements(mask, base):
            verdict, info = screen(candidate)
            tally[verdict] += 1
            if info is not None:
                survivors.append({"move": move, "status": verdict, **info})
        if sum(tally.values()) != 4*444:
            raise AssertionError("incomplete move enumeration")
        result["classes"].append({"mask": mask, "base_multiplicity": weight, "base_status": status,
                                  "base_evidence": evidence, "moves": dict(tally), "survivors": survivors})
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("shard", type=int)
    parser.add_argument("shards", type=int)
    parser.add_argument("outdir", type=Path)
    args = parser.parse_args()
    out = run(args.shard, args.shards)
    args.outdir.mkdir(parents=True, exist_ok=True)
    (args.outdir / "result.json").write_text(json.dumps(out) + "\n")
