#!/usr/bin/env python3
import sys,json,hashlib
from pathlib import Path
from collections import Counter
root=Path(__file__).resolve().parent
def bits(x):
    while x:
        b=x&-x;yield b.bit_length()-1;x^=b
def decode(s):
    s=s.strip()
    n=s[0]-63
    assert 0<n<63 and len(s)==1+(n*(n-1)//2+5)//6
    assert all(63<=x<=126 for x in s)
    a=[0]*n;k=0
    for j in range(n):
        for i in range(j):
            if ((s[1+k//6]-63)>>(5-k%6))&1:
                a[i]|=1<<j;a[j]|=1<<i
            k+=1
    return a
def count(a,k):
    def rec(p,k):
        if k==0:return 1
        if p.bit_count()<k:return 0
        if k==1:return p.bit_count()
        z=0
        while p.bit_count()>=k:
            b=p&-p;p^=b;i=b.bit_length()-1
            z+=rec(p&~a[i],k-1)
        return z
    return rec((1<<len(a))-1,k)
def maximal(a):
    full=(1<<len(a))-1;b=[full^((1<<i)|a[i]) for i in range(len(a))];out=[]
    def visit(r,p,x):
        if not p|x:out.append(r);return
        u=max(bits(p|x),key=lambda i:(p&b[i]).bit_count())
        for v in bits(p&~b[u]):
            m=1<<v;visit(r|m,p&b[v],x&b[v]);p^=m;x|=m
    visit(0,full,0)
    assert len(out)==len(set(out))
    return out
def stats(a):
    n=len(a);assert all(not (a[i]>>i&1) and a[i]>>n==0 for i in range(n))
    assert all((a[i]>>j&1)==(a[j]>>i&1) for i in range(n) for j in range(n))
    return dict(n=n,edges=sum(x.bit_count() for x in a)//2,triangles=sum((a[i]&a[j]).bit_count() for i in range(n) for j in bits(a[i]))//6,degree_histogram=dict(Counter(x.bit_count() for x in a)),independent_10_sets=count(a,10),alpha=max(x.bit_count() for x in maximal(a)))
def matrix(p):
    s=Path(p).read_text().splitlines();assert len(s)==40 and all(len(r)==40 and set(r)<=set('01') for r in s)
    return [sum(1<<j for j,x in enumerate(r) if x=='1') for r in s]
if len(sys.argv)>1:
    a=matrix(sys.argv[1]);s=stats(a);s['closure_witness']=(s['triangles']==0 and s['independent_10_sets']==0)
    assert s['triangles']==0 and max(x.bit_count() for x in a)<=9
    print(json.dumps(s,indent=2));sys.exit(0)
ex=decode((root/'exoo39.g6').read_bytes());ka=decode((root/'kalbfleisch35.g6').read_bytes())
e=stats(ex);k=stats(ka)
assert e['n']==39 and e['triangles']==0 and e['alpha']==9 and count(ex,9)==4511
assert k['n']==35 and k['triangles']==0 and k['alpha']==8 and count(ka,8)==3360
rows=maximal(ka);targets=[x for x in rows if x.bit_count()==8]
miss=[]
for s in rows:
    m=bytearray((len(targets)+7)//8)
    for i,t in enumerate(targets):
        if not s&t:m[i//8]|=1<<(i%8)
    miss.append(int.from_bytes(m,'little'))
assert len(rows)==3365 and len(targets)==3360 and all(miss)
a=[0]*len(rows);pairs=0
for i,di in enumerate(miss):
    for j in range(i):
        if not di&miss[j]:
            a[i]|=1<<j;a[j]|=1<<i;pairs+=1
tri=sum((a[i]&a[j]&((1<<j)-1)).bit_count() for i in range(len(a)) for j in bits(a[i]&((1<<i)-1)))
assert pairs==191100 and tri==0
print(json.dumps(dict(exoo=e,kalbfleisch=k,degree4=dict(rows=len(rows),targets=len(targets),compatible_pairs=pairs,compatible_triangles=tri,scope='Uses published uniqueness of the (3,9,35) graph; not an independent proof of uniqueness')),indent=2))
