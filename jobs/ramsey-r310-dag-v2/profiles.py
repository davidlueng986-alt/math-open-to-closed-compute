import json,itertools
from collections import Counter
E=[129,118,104,95,86]
def screen(ns):
    D=sum((4-i)*n for i,n in enumerate(ns))
    if D%2:return 'parity'
    a,b=ns[:2]
    if a>2 or (a==2 and b) or (a==1 and b>5):return 'low_degree_cliques'
    L=[max(0,E[i]-180+D//2+9*(i+5)) for i in range(5)]
    for i,n in enumerate(ns):
        if not n:continue
        k=i+5;u=0
        for j,m in enumerate(ns):
            t=min(k,m-int(i==j));u+=t*(4-j);k-=t
        if L[i]>u:return 'individual_neighbor_deficit'
    if sum(n*l for n,l in zip(ns,L))>sum(n*(i+5)*(4-i) for i,n in enumerate(ns)):return 'total_neighbor_deficit'
    if 2*sum(n*(4-i)*l for i,(n,l) in enumerate(zip(ns,L)))>D*D:return 'weighted_mantel'
    return 'survives'
if __name__=='__main__':
    cnt=Counter();by=Counter();survive=[]
    for c in itertools.combinations(range(44),4):
        b=(-1,)+c+(44,);ns=tuple(b[i+1]-b[i]-1 for i in range(5))
        q=screen(ns);cnt[q]+=1
        if q=='survives':survive.append(ns);by[next(i+5 for i,n in enumerate(ns) if n)]+=1
    D=max(sum((4-i)*n for i,n in enumerate(ns)) for ns in survive)
    assert sum(cnt.values())==135751 and len(survive)==1578 and D==42
    print(json.dumps(dict(counts=dict(cnt),by_min_degree=dict(by),max_deficit=D,min_edges=180-D//2,survivors=survive),indent=2))
