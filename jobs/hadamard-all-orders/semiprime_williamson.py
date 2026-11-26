"""Check actual refined semiprime orders and a finite-field product control."""

from math import comb, gcd, prod

from paley_progression import verify_control
from t599_length_change import aperiodic, disjoint
from verify import signs

PRIMES = (498_104_500_041_919, 958_149_477_774_259, 2_627_149_862_105_539)
CERTIFICATES = (
    (2, 1, ()),
    (3, 2, (2,)),
    (5, 2, (2, 2)),
    (7, 3, (2, 3)),
    (11, 2, (2, 5)),
    (13, 2, (2, 2, 3)),
    (17, 3, (2, 2, 2, 2)),
    (23, 5, (2, 11)),
    (31, 3, (2, 3, 5)),
    (37, 2, (2, 2, 3, 3)),
    (43, 3, (2, 3, 7)),
    (53, 2, (2, 2, 13)),
    (151, 6, (2, 3, 5, 5)),
    (173, 2, (2, 2, 43)),
    (211, 2, (2, 3, 5, 7)),
    (223, 3, (2, 3, 37)),
    (337, 10, (2, 2, 2, 2, 3, 7)),
    (829, 2, (2, 2, 3, 3, 23)),
    (907, 2, (2, 3, 151)),
    (1039, 3, (2, 3, 173)),
    (5443, 2, (2, 3, 907)),
    (43793, 3, (2, 2, 2, 2, 7, 17, 23)),
    (301051, 7, (2, 3, 3, 3, 5, 5, 223)),
    (3612613, 2, (2, 2, 3, 301051)),
    (36126131, 2, (2, 5, 3612613)),
    (47357263, 3, (2, 3, 3, 37, 211, 337)),
    (72252263, 5, (2, 36126131)),
    (103264597, 2, (2, 2, 3, 3, 17, 31, 5443)),
    (359382756163, 2, (2, 3, 829, 72252263)),
    (498104500041919, 7, (2, 3, 3, 7, 11, 359382756163)),
    (958149477774259, 2, (2, 3, 7, 11, 43793, 47357263)),
    (996209000083837, 5, (2, 2, 3, 3, 7, 11, 359382756163)),
    (1916298955548517, 2, (2, 2, 3, 7, 11, 43793, 47357263)),
    (2627149862105539, 2, (2, 3, 7, 11, 53, 1039, 103264597)),
    (5254299724211077, 14, (2, 2, 3, 7, 11, 53, 1039, 103264597)),
)


def verify_primes():
    proven = set()
    for p, generator, factors in CERTIFICATES:
        assert p not in proven
        if p == 2:
            assert generator == 1 and not factors
        else:
            assert 2 <= generator < p and all(factor in proven for factor in factors)
            assert prod(factors) == p - 1 and pow(generator, p - 1, p) == 1
            assert all(gcd(pow(generator, (p - 1)//factor, p) - 1, p) == 1
                       for factor in set(factors))
        proven.add(p)

    mod, base = 10_698_720_412_380, 5_963_361_072_439
    raw_mod, raw_base = 20_224_424_220, 17_380_351_759
    assert mod == raw_mod*529 and base % raw_mod == raw_base and base % 529 == 435
    assert gcd(base, mod) == 1 and gcd(2*base - 1, mod) == 1
    for p, offset in zip(PRIMES, (46, 89, 245), strict=True):
        q, t = 2*p - 1, 11*p
        assert p in proven and q in proven and (p % 4, q % 4) == (3,1)
        assert p == base + offset*mod and t % 24_342_780 == 20_018_009
        assert (t % 13, t % 19, t % 37) == (5,2,1)
        assert ((t - 1)//2) % 529 == 276
    orders = tuple(44*p for p in PRIMES)
    assert orders == (21_916_598_001_844_436, 42_158_577_022_067_396, 115_594_593_932_643_716)
    print(f"refined semiprime slice: {len(PRIMES)} exact Williamson-pair orders {orders}")


def williamson_blocks(q):
    p = (q + 1)//2
    assert q % 4 == 1
    squares = {i*i % q for i in range(1, q)}
    nonsquare = next(i for i in range(1, q) if i not in squares)

    def mul(left, right):
        a,b = left
        c,d = right
        return (a*c + nonsquare*b*d) % q, (a*d + b*c) % q

    def chi(value):
        residue = value % q
        return 0 if residue == 0 else (1 if residue in squares else -1)

    for real in range(1, q):
        inv_norm = pow(real*real - nonsquare, -1, q)
        delta = tuple(inv_norm*i % q for i in mul((real, 1), (real, 1)))
        gamma = mul(delta, delta)
        orbit = [(1, 0)]
        for _ in range(1, p):
            orbit.append(mul(orbit[-1], gamma))
        assert mul(orbit[-1], gamma) == (1, 0)
        if len(set(orbit)) == p:
            break
    else:
        raise AssertionError("No norm-one element produced the required orbit")
    points = orbit + [mul((0,1),point) for point in orbit]
    labels = {(y*pow(x,-1,q) % q if x else q) for x,y in points}
    assert labels == set(range(q+1))
    conference = tuple(tuple(chi(x*v-y*u) for u,v in points) for x,y in points)
    for i,row in enumerate(conference):
        for j, other in enumerate(conference):
            assert sum(a*b for a,b in zip(row,other,strict=True)) == (q if i == j else 0)
    r, s = conference[0][:p], conference[0][p:]
    neg_r = tuple(-entry for entry in r)
    for i in range(q+1):
        for j in range(q+1):
            word = ((r,s),(s,neg_r))[i//p][j//p]
            assert word[(j-i)%p] == conference[i][j]
    assert all(r[i] == r[-i] and s[i] == s[-i] for i in range(p))
    a = b = s
    c = (1,) + r[1:]
    d = (-1,) + r[1:]
    na,nb,nc,nd = (tuple(-x for x in word) for word in (a,b,c,d))
    return ((a,b,c,d),(nb,a,nd,c),(nc,d,a,nb),(nd,nc,b,a))


def verify_control_matrix():
    base = tuple(map(signs,("+++-++", "+++-+-", "+++--", "+-++-")))
    assert aperiodic(base) == [22]+[0]*5
    words = tuple(word + (0,)*5 for word in disjoint(*base[:2])) + tuple(
        (0,)*6 + word for word in disjoint(*base[2:]))
    assert aperiodic(words) == [11]+[0]*10
    selectors = []
    for col in zip(*words,strict=True):
        assert sum(map(abs,col)) == 1
        selectors.append(sum((i+1)*sign for i,sign in enumerate(col)))
    assert verify_control(selectors, williamson_blocks(13)) == comb(308,2) == 47_278
    assert verify_control(selectors, williamson_blocks(29)) == comb(660,2) == 217_470


if __name__ == "__main__":
    verify_primes()
    verify_control_matrix()
