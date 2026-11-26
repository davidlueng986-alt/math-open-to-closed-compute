"""Replay saturated paired transversals and extract normalized conferences."""

from collections import Counter
from verify import paley, verify_orthogonal


def dot(a, b):
    return sum(x*y for x,y in zip(a,b,strict=True))


def conference_core(t):
    if t == 9:
        def multiply(x,y):
            a,b = x%3,x//3
            c,d = y%3,y//3
            return (a*c-b*d)%3+3*((a*d+b*c)%3)
        def difference(x,y):
            return (x-y)%3+3*((x//3-y//3)%3)
        squares = {multiply(j,j) for j in range(1,t)}
    else:
        def difference(x,y):
            return (x-y)%t
        squares = {j*j%t for j in range(1,t)}
    assert len(squares)==(t-1)//2
    c = [[0 if i==j else (1 if difference(j,i) in squares else -1) for j in range(t)] for i in range(t)]
    check_conference(c)
    return c


def check_conference(c):
    t=len(c)
    assert all(c[i][i]==0 and all(abs(c[i][j])==1 for j in range(t) if j!=i) for i in range(t))
    assert all(sum(row)==0 for row in c)
    ct=list(zip(*c))
    assert all(sum(row)==0 for row in ct)
    assert all(dot(a,b)==t*(i==j)-1 for i,a in enumerate(ct) for j,b in enumerate(ct))


def balanced_w(t):
    m=2*t-2
    if m&(m-1)==0:
        cols=[sum(((i&j).bit_count()%2==0)<<i for i in range(m)) for j in range(m)]
    else:
        cols=paley(m-1)
    assert verify_orthogonal(m,cols)==m*(m-1)//2
    return [[1 if (cols[j]^cols[0])>>i&1==0 else -1 for j in range(1,t+1)] for i in range(m)]


def build(t,mode):
    c,w=conference_core(t),balanced_w(t)
    sigma=w[0].copy()
    signs=[]
    for i in range(t):
        for j in (1,-1):
            m=[(j if mode else 1)*x for x in c[i]]
            d=[(sigma[i] if mode else j)*(k==i) for k in range(t)]
            signs.append([x+y for x,y in zip(m,d,strict=True)]+[x-y for x,y in zip(m,d,strict=True)])
    for row_no,raw in enumerate(w):
        d=[(-x if mode and row_no==0 else x) for x in raw]
        signs.append(d+[-x for x in d])
    return signs


def check_design(rows,t):
    assert len(rows)==4*t-2
    assert all(len(row)==2*t and set(map(abs,row))=={1} and sum(row)==0 for row in rows)
    cols=list(zip(*rows))
    assert all(sum(col)==0 for col in cols)
    assert all(dot(a,b)==4*t*(i==j)-2 for i,a in enumerate(cols) for j,b in enumerate(cols))


def pairings(points):
    if not points:
        yield ()
        return
    for j in range(1,len(points)):
        for other in pairings(points[1:j]+points[j+1:]):
            yield ((points[0],points[j]),)+other


def count_transversals(rows, pairing):
    return sum(all(row[x]==-row[y] for x,y in pairing) for row in rows)


def extract(rows,pairing):
    t=len(pairing)
    m=[[sum((row[i],row[j]))//2 for i,j in pairing] for row in rows]
    d=[[(row[i]-row[j])//2 for i,j in pairing] for row in rows]
    active=[i for i,row in enumerate(m) if any(row)]
    assert len(active)==2*t
    pairs=[[i for i in active if d[i][j]] for j in range(t)]
    assert all(len(x)==2 for x in pairs)
    assert sorted(j for pair in pairs for j in pair)==active
    k=[m[x[0]] for x in pairs]
    v=[1,*(-dot(row,k[0]) for row in k[1:])]
    assert set(map(abs,v))=={1}
    c=[[s*x for x in row] for s,row in zip(v,k,strict=True)]
    check_conference(c)
    return d,m


for t in (3,5,7,9,11,13):
    standard=tuple((i,t+i) for i in range(t))
    for mode in (0,1):
        rows=build(t,mode)
        check_design(rows,t)
        d,m=extract(rows,standard)
        dense=[x for x,y in zip(d,m,strict=True) if not any(y)]
        assert set(map(abs,(sum(col) for col in zip(*dense))))=={2*mode}
        if t in (5,7):
            counts=Counter(count_transversals(rows,pairing) for pairing in pairings(tuple(range(2*t))))
            assert max(counts)==2*t-2 and 2*t-3 not in counts
            print(t,'mode',mode,'all pairing counts',sorted(counts.items()),flush=True)
    print(t,'both saturated types checked',flush=True)


def residual_from_hadamard(t):
    n=4*t
    cols=paley(n-1)
    assert verify_orthogonal(n,cols)==n*(n-1)//2
    normalize=[word if word&1 else word^((1<<n)-1) for word in cols]
    normalize=[word^(normalize[0]^((1<<n)-1)) for word in normalize]
    selected=[word for word in normalize if not (word>>1&1)]
    return [[1 if word>>i&1 else -1 for word in selected] for i in range(2,n)]


rows21=residual_from_hadamard(21)
check_design(rows21,21)
assert 21%4==1 and 21%9==3
print('t=21 has an exact Paley residual, while prime 3 forces every pairing below saturation')
first,step=20_018_009,24_342_780
assert first==599+100_590*199 and step==100_590*242
assert first%121==11 and step%121==0 and first%4==1 and step%4==0
