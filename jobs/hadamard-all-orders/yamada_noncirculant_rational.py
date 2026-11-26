"""Verify the rational Gram parameters and exact noncirculant H(4532) control."""
from fractions import Fraction
from itertools import product
from math import comb
from pathlib import Path

from border4_2396 import pack
from unreal_butson_product import endpoint_rows, t11_selectors
from verify import verify_orthogonal
from yamada_circulant_reverse import gram, small_yamada_words, yamada_blocks

TAU=(10,8,30,26,17,15,34,9,1,7,0,49,23,32,18,5,29,4,14,35,41,44,48,12,40,46,3,38,39,16,2,45,13,50,6,19,47,43,27,28,24,20,42,37,21,31,25,36,22,11,33)


def reversal_core():
    data=Path(__file__).with_name('yamada_reversing_drt51.txt').read_text().strip()
    n=len(TAU)
    assert len(data)==comb(n,2) and set(data)=={'0','1'}
    core=[[0]*n for _ in range(n)]
    for symbol,(i,j) in zip(data,((i,j) for i in range(n) for j in range(i+1,n)),strict=True):
        core[i][j]=2*int(symbol)-1
        core[j][i]=-core[i][j]
    for i,j in product(range(n),repeat=2):
        assert TAU[TAU[i]]==i and core[i][j]==-core[TAU[i]][TAU[j]]
    fixed,=tuple(i for i in range(n) if TAU[i]==i)
    left=tuple(i for i in range(n) if core[fixed][i]>0)
    right=tuple(TAU[i] for i in left)
    assert len(left)==len(right)==25 and not set(left)&set(right)
    # The induced skew half is not vertex-transitive, hence is not circulant.
    profiles={tuple(sorted(sum(core[x][y]==1 for y in left if core[i][y]==1)
                           for x in left if core[i][x]==1)) for i in left}
    print(f'Vertex profiles of the skew half: {len(profiles)} distinct')
    assert len(profiles)>1
    order=left+(fixed,)+right[::-1]
    normalized=tuple(tuple(core[i][j] for j in order) for i in order)
    pp=gram(normalized,normalized)
    for i,j in product(range(n),repeat=2):
        assert normalized[i][j]==-normalized[n-i-1][n-j-1] and pp[i][j]==n*(i==j)-1
    assert pow(3,10,25)==24 and n%3==0
    return normalized


def verify_product(blocks):
    p=len(blocks[0])
    source=tuple(tuple(map(pack,block)) for block in blocks)
    selectors=t11_selectors()
    plus=endpoint_rows(selectors,(1,1,1,1))
    flipped=tuple(endpoint_rows(selectors,tuple(-1 if i==j else 1 for j in range(4)))
                  for i in range(4))
    full=(1<<p)-1
    rows=[]
    for i in range(44):
        placements=[]
        for j in range(44):
            mask=1<<j
            active,=tuple(k for k in range(4) if (plus[i]^flipped[k][i])&mask)
            placements.append((source[active],0 if plus[i]&mask else full))
        for row in range(p):
            rows.append(sum((block[row]^orientation)<<(j*p)
                            for j,(block,orientation) in enumerate(placements)))
    order=44*p
    pairs=verify_orthogonal(order,rows)
    assert order==4532 and pairs==comb(4532,2)
    print(f'Noncirculant reversing core, Yamada and T11: H({order}), {pairs:,} exact row dots')


def verify_rational_parameters():
    r = 307_076_037_508_906_904_285_239
    n = 2*r + 1
    x, y = 1_586_879_471_199, 975_713_682_669
    assert r % 4 == 3 and x*x - 2*y*y == n
    for target, parameters in (
        (r, (1, 7, 505_324_252_150, 227_427_873_617)),
        (n, (1, 25, 733_902_817_722, 274_843_099_163)),
    ):
        assert sum(value*value for value in parameters) == target
    a = Fraction(x - n, x - 1)
    b = Fraction(2*y, x - 1)
    assert a*a + r*b*b == n
    print(f"Exact rational reversing-core Gram parameters for r={r}")


if __name__ == "__main__":
    verify_rational_parameters()
    s = reversal_core()
    verify_product(yamada_blocks(s, *small_yamada_words(101)))
