"""Recover every one-imaginary partner of a prescribed quaternary word."""

from itertools import product
from math import isqrt
from struct import unpack

from quaternary_599_phase import A_PHASE, N, QR, direct_scores, sign_sums
from verify import verify_orthogonal

JOINT_A = 0x3EEDF8F2AFC5FE48D9BEF4A3ABA924D5A3969BE9FA70144A98DE94C65970B777894E823CC28EBCC3BE8D6E1112F1659CC284E6ADC3F1A06826963A54DB6A2A3B908264ED805C0AB0E04880
JOINT_B = 0x76DF8C6EC1871C0615E2F43B7717D2FA3C502DC5F6A41532B423FB11594B758A37BE57AE5EE2AA9BE73FFFD55D8FF62334B32C7301FF71B786244F3587CBA62E4B513C745F2337FC68F100


def cyclic_product(a, b, modulus=0):
    n = len(a)
    assert n == len(b)
    if modulus == 3:
        # A cyclic coefficient is at most 4n before reduction.  This
        # packing base also exceeds all noncyclic coefficients.
        assert 4*n < 1 << 16
        data = (int.from_bytes(bytes(x for u in a for x in (u, 0)), "little")
                * int.from_bytes(bytes(x for u in b for x in (u, 0)), "little"))
        chunks = unpack(f"<{2*n}H", data.to_bytes(4*n, "little"))
        return tuple((chunks[j]+chunks[n+j]) % 3 for j in range(n))
    return tuple(sum(a[i]*b[(j-i) % n] for i in range(n)) for j in range(n))


def apply_frobenius(v, power):
    n = len(v)
    inverse = pow(3, -power, n)
    return tuple(v[j*inverse % n] for j in range(n))


def geometric_product(v, terms):
    """Compute v^(1+9+...+9^(terms-1)) in characteristic three."""
    if terms == 1:
        return v
    half, tail = divmod(terms, 2)
    sub = geometric_product(v, half)
    both = cyclic_product(sub, apply_frobenius(sub, 2*half), 3)
    if tail:
        return cyclic_product(both, apply_frobenius(v, 4*half), 3)
    return both


def symmetric_roots_mod3(target, signed_sum):
    """Roots in F3[C_n]^+ with the selected augmentation."""
    n = len(target)
    m = (n-1)//2
    assert m % 2 and n % 3
    assert all(target[j] == target[-j] for j in range(n))
    mass = (signed_sum*signed_sum * pow(n, -1, 3)) % 3
    v = tuple((x-mass) % 3 for x in target)
    if v == (0,)*n:
        root = v
    elif m == 1:
        root = v
    else:
        geom = apply_frobenius(geometric_product(v, (m-1)//2), 1)
        root = cyclic_product(v, cyclic_product(geom, geom, 3), 3)
    if cyclic_product(root, root, 3) != v:
        return
    for sign in (1, -1) if any(root) else (1,):
        yield tuple((sign*x+signed_sum*pow(n, -1, 3)) % 3 for x in root)


def gaussian_correlation(word):
    x,y = zip(*word, strict=True)
    n = len(word)
    real = tuple(sum(x[j]*x[(j-d) % n]+y[j]*y[(j-d) % n]
                     for j in range(n)) for d in range(n))
    imag = tuple(sum(y[j]*x[(j-d) % n]-x[j]*y[(j-d) % n]
                     for j in range(n)) for d in range(n))
    return real,imag


def recover(word):
    """A has +i at zero and has real signs at all other positions."""
    n = len(word)
    m = (n-1)//2
    assert n > 3 and all(n%d for d in range(2,isqrt(n)+1))
    residues = {pow(3, j, n) for j in range(m)}
    assert len(residues | {n-r for r in residues}) == n-1
    assert all(abs(x)+abs(y)==1 for x,y in word)
    sums = tuple(map(sum, zip(*word, strict=True)))
    square = 2*n-1-sum(s*s for s in sums)
    if square < 0 or (s := isqrt(square)) ** 2 != square or s % 2:
        return []
    real,imag = gaussian_correlation(word)
    if any(d not in (-2,0,2) for d in imag):
        return []
    t = tuple(d//2 for d in imag)
    target = tuple((2*n-1)*(d==0)+u-r
                   for d,(u,r) in enumerate(zip(cyclic_product(t,t),real,strict=True)))
    results = []
    for signed_sum in (s,-s) if s else (0,):
        for root in symmetric_roots_mod3(target, signed_sum):
            sym = tuple(-1 if x==2 else x for x in root)
            if (sym[0] != 0 or sum(sym) != signed_sum or
                any((x == 0) == (y == 0) for x,y in zip(sym[1:],t[1:],strict=True))):
                continue
            if cyclic_product(sym,sym) != target:
                continue
            a = ((0,1),)+tuple((x+y,0) for x,y in zip(sym[1:],t[1:],strict=True))
            ra,ia = gaussian_correlation(a)
            assert tuple(u+r for u,r in zip(ra,real,strict=True)) == (2*n,)+(0,)*(n-1)
            assert all(u+r==0 for u,r in zip(ia,imag,strict=True))
            results.append(a)
    return results


def physical_matrix(a,b):
    n = len(a)
    star = lambda w: tuple((w[-d][0],-w[-d][1]) for d in range(n))
    astar,bstar = star(a),star(b)
    row = lambda w, k: tuple(w[(k-i) % n] for i in range(n))
    gauss = [row(a,k)+row(b,k) for k in range(n)]
    gauss += [tuple((-x,-y) for x,y in row(bstar,k))+row(astar,k) for k in range(n)]
    maps = {(1,0):((1,1),(1,-1)),(-1,0):((-1,-1),(-1,1)),
            (0,1):((-1,1),(1,1)),(0,-1):((1,-1),(-1,-1))}
    rows = [tuple(v for z in line for v in maps[z][r]) for line in gauss for r in range(2)]
    columns = [sum((x==1)<<i for i,x in enumerate(c)) for c in zip(*rows,strict=True)]
    return verify_orthogonal(4*n,columns)


def small_control():
    count = 0
    for signs in product((-1,1),repeat=7):
        b = tuple((e,0) for e in signs)
        for a in recover(b):
            assert physical_matrix(a,b) == 378
            count += 1
    assert count == 84
    print("128 length-7 real inputs: 84 exact H28 completions, every construction checked")


def verify_p599_certificates():
    residues = {pow(3,j,N) for j in range((N-1)//2)}
    assert len(residues) == 299 and residues.isdisjoint({N-r for r in residues})
    qr = tuple((QR>>j)&1 for j in range(N))
    assert frobenius_binary_square(qr) == qr
    assert all(sum(qr[j]*qr[(j-d)%N] for j in range(N)) == (299 if not d else 149)
               for d in range(N))
    target = 4*N-3
    margins = [(a,isqrt(target-2*a*a)) for a in range(0,isqrt(target//2)+1,2)
               if isqrt(target-2*a*a)**2 == target-2*a*a]
    assert margins == [(34,9)]
    # For m=4, the upper bound on the square is 600 + 2*sqrt(4736) < 738.
    assert 4*4736 < 138**2 and (599*4)//2-25 > 738
    assert all(599*m-50 > 2*(1196+m) for m in range(5,300))
    print("599: all Paley-signed second words excluded when the first has one imaginary site")
    assert sign_sums(A_PHASE,JOINT_A) == (10,1) and sign_sums(QR,JOINT_B) == (-16,-29)
    score = direct_scores(QR,JOINT_B,JOINT_A)
    assert score[:3] == (193088,7,179)
    print("599: a physical non-Paley pair passes the joint mod-8 sums and",score[2],
          "separate inverse pairs, with peak",score[3])


def frobenius_binary_square(coefficients):
    inv2 = pow(2,-1,len(coefficients))
    return tuple(coefficients[j*inv2 % len(coefficients)] for j in range(len(coefficients)))


if __name__ == "__main__":
    small_control()
    verify_p599_certificates()
