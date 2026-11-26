"""Check the reversing-core route, residue obstruction, and one full H(660)."""

import json
from itertools import product
from math import comb, gcd, prod
from pathlib import Path

from border4_2396 import pack
from unreal_butson_product import endpoint_rows, t11_selectors
from verify import verify_orthogonal

BASE = 261_129_632_466_031_099
PERIOD = 421_540_282_968_184_380


def gram(left, right):
    return tuple(tuple(sum(x*y for x,y in zip(row,other,strict=True)) for other in right)
                 for row in left)


def field_char(p):
    squares={x*x%p for x in range(1,p)}
    return lambda x: 0 if x%p==0 else 1 if x%p in squares else -1


def small_yamada_words(q):
    chi=field_char(q)
    d=next(a for a in range(1,q) if chi(a)==-1)

    def mul(u,v):
        a,b=u; c,e=v
        return ((a*c+d*b*e)%q,(a*e+b*c)%q)

    powers=None
    for g in product(range(q),repeat=2):
        if g==(0,0):continue
        words=[(1,0)]
        for _ in range(1,q*q-1):words.append(mul(words[-1],g))
        if len(set(words))==q*q-1:
            powers=words;break
    assert powers is not None
    n=(q+1)//2
    beta=tuple(chi(2*powers[(4*x+n)%(q*q-1)][0]) for x in range(n))
    alpha=tuple(chi(2*powers[(4*x)%(q*q-1)][0]) for x in range(n))
    m=tuple(tuple(beta[(y-x)%n] for y in range(n)) for x in range(n))
    h=tuple(tuple(alpha[(y-x)%n] for y in range(n)) for x in range(n))
    g1,g2=gram(m,m),gram(h,h)
    assert not beta[0] and all(abs(x)==1 for x in beta[1:]+alpha)
    assert all(g1[x][y]+g2[x][y]==q*(x==y) for x,y in product(range(n),repeat=2))
    return m,h


def reversing_core_from_word(word):
    r=len(word)
    assert abs(word[0]) == 1 and sum(word) == -1
    assert all(sorted((abs(word[i]),abs(word[-i]))) == [0,2] for i in range(1,r))
    d=tuple(tuple(word[(j-i)%r] for j in range(r)) for i in range(r))
    dd=gram(d,d)
    assert all(dd[i][j] == (2*r+1)*(i==j)-2 for i,j in product(range(r),repeat=2))
    a=tuple(tuple((d[i][j]-d[j][i])//2 for j in range(r)) for i in range(r))
    b=tuple(tuple(-(d[i][j]+d[j][i])//2 for j in range(r)) for i in range(r))
    core=((0,)+(1,)*r+(-1,)*r,) + tuple((-1,)+a[i]+b[i] for i in range(r)) + tuple(
        (1,)+tuple(-x for x in b[i])+tuple(-x for x in a[i]) for i in range(r))
    n=2*r+1
    # Index order +r, ..., +1, fixed vertex, -1, ..., -r pairs reflection.
    order=tuple(range(r,0,-1))+(0,)+tuple(range(r+1,2*r+1))
    core=tuple(tuple(core[i][j] for j in order) for i in order)
    ss=gram(core,core)
    for i,j in product(range(n),repeat=2):
        assert core[i][j] == -core[j][i] == -core[n-1-i][n-1-j]
        assert ss[i][j] == n*(i==j)-1
    return core


def yamada_blocks(s,m,n):
    side=len(s)
    identity=tuple(tuple(int(i==j) for j in range(side)) for i in range(side))
    zero=tuple((0,)*side for _ in range(side))
    reverse=tuple(tuple(int(i+j==side-1) for j in range(side)) for i in range(side))
    sr=tuple(tuple(row[side-1-j] for j in range(side)) for row in s)
    output=[]
    for u,v,corner,border in zip((identity,zero,sr,sr),(m,n,reverse,reverse),
                                 (1,-1,1,1),(-1,-1,1,1),strict=True):
        core=tuple(tuple(u[x][y]+(-1 if a!=b else 1)*v[x][y]
                         for y,b in product(range(side),range(2)))
                   for x,a in product(range(side),range(2)))
        matrix=((corner,)+(border,)*(2*side),)+tuple((border,)+row for row in core)
        assert all(set(row) <= {-1,1} for row in matrix)
        output.append(matrix)
    p=2*side+1
    parts=[gram(w,w) for w in output]
    assert all(sum(part[i][j] for part in parts)==4*p*(i==j) for i,j in product(range(p),repeat=2))
    for i in range(4):
        for j in range(i):
            assert gram(output[i],output[j])==gram(output[j],output[i])
    return tuple(output)


def verify_control():
    # beta=1−2 zeta_3 with beta*conjugate(beta)=7; canonical sum −1.
    word=(1,-2,0)
    s=reversing_core_from_word(word)
    source=yamada_blocks(s,*small_yamada_words(13))
    p=len(source[0])
    selectors=t11_selectors()
    all_plus=endpoint_rows(selectors,(1,1,1,1))
    flips=tuple(endpoint_rows(selectors,tuple(-1 if j==i else 1 for j in range(4)))
                for i in range(4))
    outer_terms=[]
    for i,j in product(range(44),repeat=2):
        mask=1<<j
        active=tuple(k for k,other in enumerate(flips) if (all_plus[i]^other[i])&mask)
        assert len(active)==1
        outer_terms.append((active[0],1 if all_plus[i]&mask else -1))
    rows=[pack(sign*source[k][x][y]
               for j in range(44) for k,sign in (outer_terms[44*i+j],) for y in range(p))
          for i,x in product(range(44),range(p))]
    assert p==15 and verify_orthogonal(44*p,rows)==comb(660,2)
    print("Cyclotomic reversing core, symmetric Yamada inputs and T11: H(660), all 217,470 row dots zero")


def valuation(value, prime):
    count=0
    while value%prime==0:
        count+=1
        value//=prime
    return count


def verify_arithmetic():
    proved=set()
    certificates=json.loads(Path(__file__).with_name('yamada_reversing_primes.json').read_text())
    for n,witness,factors in certificates:
        assert n not in proved
        if n==2:
            assert witness==1 and not factors
        else:
            assert 2<=witness<n and set(factors)<=proved and prod(factors)==n-1
            assert pow(witness,n-1,n)==1
            assert all(gcd(pow(witness,(n-1)//prime,n)-1,n)==1 for prime in set(factors))
        proved.add(n)
    p=1_228_304_150_035_627_617_140_959
    q=p-2
    r=(p-3)//4
    h=80_565_666_406_639_618_073
    n=2*r+1
    assert {p,q,r,h}<=proved
    assert p==BASE+2_913_847*PERIOD and (p%16,q%8,r%4,h%8)==(15,5,3,1)
    assert n==3**2*7*11**2*h and (r%3,r%7)==(1,3)
    assert all(pow(-r,(prime-1)//2,prime)==1 for prime in (7,h))
    assert pow(3,(r-1)//2,r)==r-1
    failing=[]
    for k in (839,1303,2235):
        n_old=(BASE+k*PERIOD-1)//2
        failing.append(tuple(valuation(n_old,prime) for prime in (3,11)))
    assert tuple(failing)==((1,1),(2,1),(1,2))
    print(f"Reversing core local tests: three prior P candidates fail; certified P={p} passes")


if __name__=='__main__':
    verify_control()
    verify_arithmetic()
