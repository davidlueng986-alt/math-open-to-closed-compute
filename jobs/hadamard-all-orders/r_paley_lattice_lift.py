"""Replay two rearrangements of the full Paley sign-lift lattice."""

from itertools import combinations, product
from math import isqrt

from r_paley_isotropic_code import assemble, dot, half_projections, rank_mod
from verify import paley, verify_orthogonal


CONTROLS = (
    (7, tuple(range(8)),
     (227, 737, 1521, 699, 2385, 2421, 1081, 1735, 3257, 1413, 1485, 2915)),
    (11, (0, 1, 3, 4, 6, 7, 8, 11, 12, 16, 17, 19),
     (666501, 255107, 220717, 361425, 411473, 153655, 798779, 120435,
      234801, 920953, 958779, 78829, 206777, 711061, 307927, 421763,
      424531, 144043, 758167, 7005)),
)


def norm_words(norm, n):
    if n == 0:
        if norm == 0:
            yield ()
        return
    bound = isqrt(norm)
    for j in range(-bound,bound+1):
        for tail in norm_words(norm-j*j,n-1):
            yield (j,*tail)


def reserve_span(vectors, t, v):
    basis = []
    for w in vectors:
        trial = [*basis,w]
        if rank_mod(trial,t) == len(trial):
            basis = trial
    assert len(basis) == v//2
    return {tuple(sum(a*w[j] for a,w in zip(coef,basis,strict=True))%t for j in range(v))
            for coef in product(range(t), repeat=len(basis))}


def signs(column, m):
    return tuple(2*(column >> j & 1)-1 for j in range(m))


def check(t, chosen, lowers):
    m, d, v = 2*t-2, (t-1)//2, t-3
    source = paley(m-1)
    assert len(lowers) == m and len(chosen) == t+1
    assert verify_orthogonal(4*t,assemble(t,source,chosen,lowers)) == (4*t)*(4*t-1)//2
    unused = tuple(j for j in range(m) if j not in chosen)
    decks = [half_projections(source,z) for z in lowers]
    selected = [tuple(row[j] for j in chosen) for row in decks]
    reserves = [tuple(row[j] for j in unused) for row in decks]
    assert all(dot(z,z) == t*v for z in reserves)
    assert all(dot(a,b) % t == 0 for a,b in combinations(reserves,2))
    code = reserve_span(reserves,t,v)

    # These low-rank residue lattices are standard; recover actual norm-one
    # generators by enumerating the integer representatives of norm t.
    q = [w for w in norm_words(t,v)
         if next((a for a in w if a),0) > 0 and tuple(a%t for a in w) in code]
    assert len(q) == v and all(dot(a,b) == 0 for a,b in combinations(q,2))
    raw_source = [signs(source[j],m) for j in chosen+unused]
    x, y = raw_source[:t+1],raw_source[t+1:]
    right = [tuple(dot(row,w) for row in zip(*y,strict=True)) for w in q]
    M = list(zip(*x,*right,strict=True))
    assert rank_mod(M,d) == m//2
    assert all(dot(a,b)%d == 0 for a in M for b in M)

    lifted = []
    for z,b,w in zip(lowers,selected,reserves,strict=True):
        c = []
        for a in q:
            product = dot(w,a)
            assert product in (t,-t)
            c.append(product//t)
        u = (*b,*c)
        assert all(abs(s) == 1 for s in u)
        raw = tuple(dot(row,u) for row in M)
        assert all(a % (4*d) == 2*d for a in raw)
        assert raw == tuple(2*d*a for a in signs(z,m))
        lifted.append(u)
    assert all(dot(a,b) == 0 for a,b in combinations(lifted,2))
    # This frame gives the D_m roots by taking signed halves. Their
    # integer representatives have squared norm 2d and lie in the code.
    for a,b in combinations(lifted,2):
        for s in (-1,1):
            root = tuple((u+s*v)//2 for u,v in zip(a,b,strict=True))
            assert dot(root,root) == 2*d
            assert all(dot(row,root)%d == 0 for row in M)
    print(f"Lattice lift at order {4*t}: {m} norm-four characteristic lines in the correct phase, "
          f"verified signed D_{m} root generators")


if __name__ == "__main__":
    for parameters in CONTROLS:
        check(*parameters)
