from math import comb
def upsets(n):
    if not n: return [0,1]
    a=upsets(n-1); shift=1<<(n-1)
    return [x|(y<<shift) for x in a for y in a if not x&~y]
def add(x,y): return (x[0]+y[0],x[1]+y[1])
def norm2(x): return x[0]**2+x[1]**2
def check(n):
    fs=upsets(n); assert len(fs)==[2,3,6,20,168,7581][n]
    b=[comb(n,k) for k in range(n+1)]
    phases=[[(1,0),(-1,0)],[(1,0),(0,1),(-1,0),(0,-1)],[(1,0),(0,-1),(-1,0),(0,1)]]
    tails=[]
    for phase in phases:
        B=(0,0); mx=0
        for k in reversed(range(n+1)):
            p=phase[k%len(phase)]; B=add(B,(b[k]*p[0],b[k]*p[1])); mx=max(mx,norm2(B))
        tails.append(mx)
    for f in fs:
        c=[0]*(n+1)
        for x in range(1<<n):
            if (f>>x)&1: c[x.bit_count()]+=1
        assert all(c[k]*b[k+1]<=c[k+1]*b[k] for k in range(n))
        for phase,mx in zip(phases,tails):
            v=(0,0)
            for k in range(n+1):
                p=phase[k%len(phase)]; v=add(v,(c[k]*p[0],c[k]*p[1]))
            assert norm2(v)<=mx
    print(f"PASS n={n}: all {len(fs)} monotone Boolean functions, three exact phases",flush=True)
    return len(fs)
print("PASS total monotone functions:",sum(check(n) for n in range(6)))
