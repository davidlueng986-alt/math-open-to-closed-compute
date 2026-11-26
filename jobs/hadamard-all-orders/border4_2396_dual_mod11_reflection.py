"""Exact primitive F11 certificates at all single-row reflection centers."""

from collections import Counter
from pathlib import Path
from struct import unpack

from border4_2396_dual_quotient import MORE_MOD16, dual_words
from border4_2396_primitive_field import primitive_factor, remainder

N = 299
HALF = N//2
Q = 11
FACTOR = primitive_factor(Q)
DEGREE = len(FACTOR)-1
INV = [0]+[pow(i,-1,Q) for i in range(1,Q)]
ROOT = Path(__file__).parent


def plus(a,b,c=1):
    return [(x+c*y) % Q for x,y in zip(a,b,strict=True)]


def scale(v,c):
    return [c*x % Q for x in v]


def shift_left(v):
    c=v[-1]
    return [(-c*FACTOR[0])%Q]+[(v[j-1]-c*FACTOR[j])%Q for j in range(1,DEGREE)]


def shift_right(v):
    c=(-v[0]*INV[FACTOR[0]])%Q
    return [(v[j+1]+c*FACTOR[j+1])%Q for j in range(DEGREE-1)]+[c]


def encode(v):
    raw=bytearray(2*DEGREE)
    raw[::2]=bytes(v)
    return int.from_bytes(raw,'little')


def multiply(a,b):
    part=unpack(f'<{2*DEGREE}H',(encode(a)*encode(b)).to_bytes(4*DEGREE,'little'))
    return list(remainder(part,FACTOR,Q))


def trim(a):
    while a and not a[-1]:
        a.pop()
    return a


def residue_norm(v):
    """Resultant Res(FACTOR, v) in the prime field."""
    big, small, result = list(FACTOR),trim(v.copy()),1
    while small:
        m,n=len(big)-1,len(small)-1
        lc=small[-1]
        if n==0:
            return result*pow(lc,m,Q)%Q
        normalized=[x*INV[lc]%Q for x in small]
        for j in range(m,n-1,-1):
            coefficient=big[j]
            if coefficient:
                pivot=j-n
                for i in range(n):
                    big[pivot+i]=(big[pivot+i]-coefficient*normalized[i])%Q
        tail=trim(big[:n])
        if not tail:
            return 0
        if m*n%2:result=-result
        result=result*pow(lc,m-(len(tail)-1),Q)%Q
        big,small=small,tail
    return 0


def inverse_reconstruction():
    powers=[[1]+[0]*(DEGREE-1)]
    for _ in range(1,N):
        powers.append(shift_left(powers[-1]))
    assert shift_left(powers[-1])==powers[0]
    columns=[]
    for d in range(1,HALF+1):
        column=plus(powers[d],powers[N-d],-1)
        for q in (13,23):
            column.extend(((d%q==j)-((-d)%q==j))%Q for j in range(1,q//2+1))
        columns.append(column)
    matrix=[list(r) for r in zip(*columns,strict=True)]
    rows=[r+[int(j==i) for j in range(HALF)] for i,r in enumerate(matrix)]
    for k in range(HALF):
        pivot=next(i for i in range(k,HALF) if rows[i][k])
        rows[k],rows[pivot]=rows[pivot],rows[k]
        unit=scale(rows[k],INV[rows[k][k]])
        rows[k]=unit
        for i in range(HALF):
            if i!=k and rows[i][k]:
                rows[i]=plus(rows[i],unit,-rows[i][k])
    assert all(row[:HALF]==[int(i==j) for j in range(HALF)] for i,row in enumerate(rows))
    return [row[HALF:HALF+DEGREE] for row in rows]


def check_source(data, filename, inverse):
    certs=filename.read_text().splitlines()
    assert len(certs)==4*N
    projections=[(list(remainder(row,FACTOR,Q)),
                  list(remainder(row[:1]+row[:0:-1],FACTOR,Q))) for row in data]
    norms=[multiply(a,b) for a,b in projections]
    target=[599%Q]+[0]*(DEGREE-1)
    for norm in norms:target=plus(target,norm,-1)
    checked=Counter()
    for i,(a,b) in enumerate(projections):
        remaining=plus(target,norms[i])
        for h in range(N):
            even=scale(plus(a,b),INV[2])
            r=plus(multiply(even,even),remaining,-1)
            text=certs[N*i+h]
            if text=='-':
                assert pow(residue_norm(r),5,Q)==Q-1
                checked['nonsquare']+=1
            else:
                values=[int(w,16) for w in text]
                assert len(values)==DEGREE and all(x < Q for x in values)
                assert multiply(values,values)==r
                odd=scale(plus(a,b,-1),INV[2])
                for x in (values,scale(values,-1)):
                    delta=plus(x,odd,-1)
                    assert any(sum(u*v for u,v in zip(delta,row,strict=True))%Q not in (0,2,Q-2)
                               for row in inverse)
                    checked['nonphysical root']+=1
                checked['square']+=1
            a,b=shift_right(a),shift_left(b)
        assert (a,b)==projections[i]
    print(filename.name,dict(checked),flush=True)


if __name__=='__main__':
    inv=inverse_reconstruction()
    check_source(dual_words(),ROOT/'border4_2396_dual_mod11_reflection_80.txt',inv)
    check_source(dual_words(MORE_MOD16),ROOT/'border4_2396_dual_mod11_reflection_469.txt',inv)
