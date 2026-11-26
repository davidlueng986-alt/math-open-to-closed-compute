"""Check the modular reserve-code criterion and fixed-exterior controls."""

from collections import defaultdict
from itertools import combinations
import json

from r_paley_bucket_extension import SELECTED
from r_paley_periodic_skew import DATA
from r_paley_projective_lift import build
from verify import goethals_seidel, length_299_words, paley, rows_from_columns, verify_orthogonal


def dot(x, y):
    return sum(a * b for a, b in zip(x, y, strict=True))


def half_projections(source, z):
    return tuple(len(source) // 2 - (col ^ z).bit_count() for col in source)


def rank_mod(rows, p):
    basis = {}
    for row in rows:
        word = [x % p for x in row]
        for pivot in sorted(basis):
            factor = word[pivot]
            if factor:
                word = [(x-factor*y) % p for x,y in zip(word,basis[pivot],strict=True)]
        pivot = next((i for i,x in enumerate(word) if x), None)
        if pivot is not None:
            inverse = pow(word[pivot], -1, p)
            basis[pivot] = [x*inverse % p for x in word]
    return len(basis)


def assemble(t, source, chosen, lowers):
    gamma, *w = chosen
    outside, fixed = build(t, source, (), w, gamma)
    low_mask = (1 << (2*t-2)) - 1
    top_mask = (1 << t) - 1
    result = outside + fixed
    for z in lowers:
        p = half_projections(source, z)
        assert all(abs(p[j]) == 1 for j in chosen)
        lower = low_mask ^ source[gamma] ^ z
        if p[gamma] == 1:
            lower ^= low_mask
        top = sum((p[gamma]*p[j] == 1) << i for i,j in enumerate(w))
        result.append(top | ((top ^ top_mask) << t) | (lower << (2*t))
                      | (3 << (4*t-2)))
    return result


def projective_line(vector, p):
    inverse = pow(next(x for x in vector if x % p), -1, p)
    return tuple(x*inverse % p for x in vector)


def full_28():
    source = paley(11)
    assert verify_orthogonal(12, source) == 66
    documented = []
    for z in range(1, 1 << 12, 2):
        projection = half_projections(source, z)
        hits = sum((abs(p) == 1) << j for j,p in enumerate(projection))
        if hits.bit_count() >= 8:
            documented.append((z, projection, hits))
    assert len(documented) == 1024
    count = 0
    for chosen in combinations(range(12),8):
        mask = sum(1 << j for j in chosen)
        unused = [j for j in range(12) if not (mask >> j & 1)]
        buckets = defaultdict(list)
        for z, projection, hits in documented:
            if hits & mask == mask:
                line = projective_line([projection[j] for j in unused], 7)
                assert dot(line,line) % 7 == 0
                buckets[line].append(z)
        for u,v in combinations(buckets,2):
            if dot(u,v) % 7:
                continue
            span = [projective_line([a+i*b for a,b in zip(u,v,strict=True)],7)
                    for i in range(7)] + [v]
            assert len(set(span)) == 8
            lowers = [z for line in span for z in buckets.get(line,())]
            if len(lowers) == 12:
                cols = assemble(7, source, chosen, lowers)
                assert len(cols) == 28 and verify_orthogonal(28, cols) == 378
                count += 1
                break
        else:
            raise AssertionError(chosen)
    assert count == 495
    print("Order 28: every one of 495 outer choices completes, each with 378 exact dot products")


def maximal_set(p, vectors, target):
    # Every vertex is isotropic. A clique is a mutually compatible family.
    adjacency = [0] * len(vectors)
    for (i,u),(j,v) in combinations(enumerate(vectors),2):
        if dot(u,v) % p == 0:
            adjacency[i] |= 1 << j
            adjacency[j] |= 1 << i

    best = []
    def search(available, prefix):
        nonlocal best
        if len(best) == target:
            return
        if len(prefix) > len(best):
            best = prefix
        if len(prefix) + available.bit_count() <= len(best):
            return

        remaining = available
        order = []
        color = 0
        # Each color class is independent. Its index bounds the largest
        # clique in the prefix ending at this vertex.
        while remaining:
            color += 1
            pool = remaining
            while pool:
                bit = pool & -pool
                j = bit.bit_length() - 1
                order.append((j,color))
                remaining ^= bit
                pool &= ~(bit | adjacency[j])

        for j,bound in reversed(order):
            if len(prefix) + bound <= len(best):
                return
            new = available & adjacency[j]
            if len(prefix) + 1 + new.bit_count() > len(best):
                search(new, prefix + [j])
            available ^= 1 << j

    search((1 << len(vectors)) - 1, [])
    return best


def check_44():
    source = paley(19)
    assert verify_orthogonal(20, source) == 190
    cases = (
        ((0,1,2,4,5,6,7,8,10,14,18,19),340,8),
        (tuple(range(12)),334,12),
        ((0,1,3,4,6,7,8,11,12,16,17,19),363,20),
    )
    for chosen,candidate_count,want in cases:
        spare = [i for i in range(20) if i not in chosen]
        lowers = [z for z in range(1,1 << 20,2)
                  if all(abs(10-(z ^ source[j]).bit_count()) == 1 for j in chosen)]
        vectors = [tuple(10-(z ^ source[j]).bit_count() for j in spare) for z in lowers]
        assert len(lowers) == candidate_count
        assert all(all(v % 11 for v in w) and dot(w,w) == 88 for w in vectors)
        chosen_indices = maximal_set(11, vectors, 20)
        assert len(chosen_indices) == want
        if want == 20:
            assert rank_mod([vectors[i] for i in chosen_indices], 11) == 4
        cols = assemble(11, source, chosen, [lowers[i] for i in chosen_indices])
        assert len(cols) == 24 + want
        pairs = verify_orthogonal(44, cols)
        print(f"Order 44: {candidate_count} individually compatible lines, exact fixed-exterior width {len(cols)}, checked {pairs} pair products")


def sign(row, index):
    return 2 * (row >> index & 1) - 1


def check_2396():
    t, m = 599, 1196
    source = goethals_seidel(length_299_words())
    cases = json.loads(DATA.read_text(encoding="ascii"))["extensions"]
    old = next(c for c in cases if c["width"] == 1214)
    rows = old["inner_rows"] + [319]
    pivots = old["inner_columns"] + [344]
    used = tuple(j for j in range(m) if SELECTED >> j & 1)
    spare = tuple(j for j in range(m) if not (SELECTED >> j & 1))
    lowers = [source[g] ^ (1 << r) for r,g in zip(rows,pivots,strict=True)]
    projections = [half_projections(source,z) for z in lowers]
    assert len(used) == 600 and len(spare) == 596
    assert all(all(abs(v[j]) == 1 for j in used) for v in projections)
    vectors = [tuple(v[j] for j in spare) for v in projections]
    assert all(dot(w,w) == t * (t-3) for w in vectors)
    assert all(all(v % t for v in w) for w in vectors)
    assert all(dot(u,v) % t == 0 for u,v in combinations(vectors,2))
    assert rank_mod(vectors,t) == 15

    lower_rows = rows_from_columns(m, [source[j] for j in spare])
    ref = []
    for r,g,w in zip(rows,pivots,vectors,strict=True):
        s = spare.index(g)
        row = lower_rows[r]
        at_pivot = sign(row,s)
        assert all((w[j] + int(j == s) + at_pivot*sign(row,j)) % t == 0
                   for j in range(t-3))
        ref.append((row,s,at_pivot))

    # Apart from its own already used line, each result would give a new
    # exact column by the modular pair criterion.
    fits = []
    for r,row in enumerate(lower_rows):
        base = [(t-3)-2*(row ^ a).bit_count()+e*sign(row,h) for a,h,e in ref]
        for s,g in enumerate(spare):
            e = sign(row,s)
            if all((b + e*(sign(a,s)+(f if h == s else 0))) % t == 0
                   for b,(a,h,f) in zip(base,ref,strict=True)):
                fits.append((r,g))
    assert set(fits) == set(zip(rows,pivots,strict=True)) and len(fits) == 15
    print("Order 2396: rank 15 isotropic residue span over F599; all 712816 single-flip lines checked on the fixed 1215-column exterior")


if __name__ == "__main__":
    full_28()
    check_44()
    check_2396()
