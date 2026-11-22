"""Sound F3 linear-dependence contradiction prefilter for voltage covers.

Every simple base power-of-two cycle imposes f(v) != 0 in F3 on a
hypothetical counterexample voltage vector v. If normalized forms u,w,z
satisfy u + eps*w = s*z with eps,s = +/-1, then all three nonzero
values force u(v) = eps*w(v) = -s*z(v).
The signed DSU collects these equality constraints. An inconsistency is a
finite mathematical UNSAT certificate (independent of any large enumeration).
This is a one-sided filter: noncontradiction does not certify satisfiability.
"""
def normalize(v):
    t=tuple(int(x)%3 for x in v)
    for x in t:
        if x:
            return t if x==1 else tuple((-a)%3 for a in t)
    raise ValueError('zero linear form')

def contradiction(forms_input):
    forms_all={normalize(f) for f in forms_input}
    vs=list(forms_all);n=len(vs)
    if not n:return False,0,0
    indexes={v:i for i,v in enumerate(vs)}
    parent=list(range(n));relative=[1]*n
    def root(x):
        if parent[x]==x:return x,1
        r,s=root(parent[x])
        relative[x]*=s;parent[x]=r
        return parent[x],relative[x]
    def equal(x,y,sgn):
        a,sa=root(x);b,sb=root(y)
        if a==b:return sa==sgn*sb
        parent[a]=b;relative[a]=sgn*sb*sa
        return True
    relations=0
    for i,u in enumerate(vs):
        for j in range(i+1,n):
            v=vs[j]
            for op in (1,-1):
                wraw=tuple((a+op*b)%3 for a,b in zip(u,v))
                if not any(wraw):continue
                s=1 if next(x for x in wraw if x)==1 else -1
                w=wraw if s==1 else tuple((-x)%3 for x in wraw)
                k=indexes.get(w)
                if k is None:continue
                relations+=1
                if not equal(i,j,op):return True,relations,n
                if not equal(i,k,-s):return True,relations,n
    return False,relations,n
