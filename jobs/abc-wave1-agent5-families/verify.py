#!/usr/bin/env python3
"""Exact, bounded audit of primitive squaring orbits. No global abc claim."""
import argparse
import hashlib
import json
import math
import os
import platform
import time
from functools import lru_cache
from pathlib import Path

try:
    from sage.all import ZZ
    from sage.env import SAGE_VERSION
    BACKEND = 'SageMath proof=True'
    BACKEND_VERSION = SAGE_VERSION
except ImportError:
    import sympy
    BACKEND = 'SymPy; all primality inputs below 2^64'
    BACKEND_VERSION = sympy.__version__
    ZZ = None

@lru_cache(None)
def factors(n):
    n = abs(int(n))
    assert 0 < n < 2**64, 'The factorization audit is explicitly bounded.'
    if ZZ is not None:
        fs = [(int(p), int(e)) for p,e in ZZ(n).factor(proof=True)]
        assert all(ZZ(p).is_prime(proof=True) for p,e in fs)
    else:
        fs = sorted((int(p),int(e)) for p,e in sympy.factorint(n).items())
        assert all(sympy.isprime(p) for p,e in fs)
    assert all(e > 0 for p,e in fs)
    assert math.prod(p**e for p,e in fs) == n
    return tuple(fs)

def rad(n):
    return math.prod(p for p,e in factors(n))

def triple_rad(a,b,c):
    return math.prod(set(p for x in (a,b,c) for p,e in factors(x)))

def primitive(a,b,c):
    return 0<a and 0<b and a+b==c and math.gcd(a,b)==1 and (a-b)%2==1

def mul(x,y,s,p):
    return ((x[0]*y[0]+s*x[1]*y[1])%p, (x[0]*y[1]+x[1]*y[0])%p)

def power(x,e,s,p):
    out=(1,0)
    while e:
        if e&1: out=mul(out,x,s,p)
        x=mul(x,x,s,p);e//=2
    return out

def run(outdir):
    started=time.monotonic()
    # All primitive positive seeds with a<=b, odd c<=41, plus the well-known high-quality seed.
    seeds=[(a,c-a,c) for c in range(3,42,2) for a in range(1,c//2+1) if math.gcd(a,c)==1]
    special=(2,3**10*109,23**5)
    assert special[0]+special[1]==special[2]
    seeds.append(special)
    rows=[]; exact_steps=0; prime_orders=0; coprime_checks=0; threshold_checks=0
    special_rows=[]
    for a0,b0,c0 in seeds:
        assert primitive(a0,b0,c0)
        r0=triple_rad(a0,b0,c0)
        a,b,c=a0,b0,c0
        differences=[]; product_d=1; defect=1; r=r0
        factorable=True
        for n in range(7):
            assert primitive(a,b,c)
            assert c==c0**(2**n)
            assert a*b==4**n*a0*b0*product_d**2
            assert 4*a*b<=c*c
            exact_steps+=1
            if factorable:
                assert r*defect==r0*product_d
                # Strong exact form of c_n/R_n >= 2^(n+1)*sqrt(a0*b0)*Q_n/R0.
                assert c*c*r0*r0 >= 4**(n+1)*a0*b0*r*r*defect*defect
                # The guaranteed quality margin obtained only from |d_j|<c_j.
                assert r<=r0*c0**(2**n-1)
                for u,v in [(8,5),(11,10),(6,5)]:
                    assert (c**v >= r**u)==(c**v*defect**u >= (r0*product_d)**u)
                    threshold_checks+=1
                row={'seed':[a0,b0,c0],'step':n,'a':a,'b':b,'c':c,'radical':r,
                     'Q_defect':defect,'difference_product':product_d,
                     'quality_display':math.log(c)/math.log(r),'q_gt_8_over_5':c**5>r**8}
                rows.append(row)
                if (a0,b0,c0)==special: special_rows.append(row)
            d=a-b
            assert d!=0 and d%2==1
            assert math.gcd(abs(d),a*b*c)==1
            assert math.gcd(abs(d),a0*b0*c0)==1
            assert all(math.gcd(abs(d),abs(old))==1 for old in differences)
            coprime_checks+=2+len(differences)
            if differences:
                old_d=differences[-1]
                old_c=c0**(2**(n-1))
                assert d==2*old_d**2-old_c**2
            if factorable and abs(d)<2**64:
                fs=factors(d);rd=math.prod(p for p,e in fs)
                assert math.gcd(r,rd)==1
                s=(-a0*b0)
                for p,e in fs:
                    assert p!=2 and math.gcd(p,c0)==1
                    inv=pow(c0,-1,p)
                    z=(((a0-b0)*inv)%p,(2*inv)%p)
                    assert (z[0]*z[0]-s*z[1]*z[1])%p==1
                    assert power(z,2**(n+1),s,p)==(p-1,0)
                    assert power(z,2**(n+2),s,p)==(1,0)
                    chi=pow(s%p,(p-1)//2,p)
                    assert chi in (1,p-1)
                    chi=1 if chi==1 else -1
                    assert (p-chi)%(2**(n+2))==0
                    prime_orders+=1
                r*=rd;defect*=abs(d)//rd
            else:
                factorable=False
            differences.append(d);product_d*=abs(d)
            a,b,c=d*d,4*a*b,c*c
    assert len(special_rows)>=3
    assert special_rows[0]['q_gt_8_over_5']
    assert not special_rows[1]['q_gt_8_over_5']
    assert special_rows[1]['radical']==15042*7*13*70729
    assert special_rows[2]['radical']==special_rows[1]['radical']*41426408232193
    cert={'rows':rows,'factorizations':{str(n):list(factors(n)) for n in sorted({abs(row['a']-row['b']) for row in rows if abs(row['a']-row['b'])<2**64})}}
    raw=json.dumps(cert,sort_keys=True,separators=(',',':')).encode()
    (outdir/'certificates.json').write_bytes(raw+b'\n')
    result={'problem':'ABC','agent':5,'status':'CHECKED','resolution':'unknown',
            'scope':'Finite exact orbit invariants, radical recurrence, prime-order congruences, quality threshold certificates; no infinite prime-power-defect estimate.',
            'seed_count':len(seeds),'seed_domain':'all 1<=a<=b, a+b=c odd<=41, gcd(a,b)=1, plus (2,3^10*109,23^5)',
            'integer_orbit_states_checked':exact_steps,'factorized_orbit_states':len(rows),
            'coprimality_checks':coprime_checks,'prime_order_certificates':prime_orders,
            'rational_quality_threshold_checks':threshold_checks,'known_seed_orbit':special_rows,
            'factorization_limit':'each new difference < 2^64; later states have exact algebra/gcd checks only',
            'backend':BACKEND,'backend_version':BACKEND_VERSION,'python':platform.python_version(),
            'certificate_sha256':hashlib.sha256(raw).hexdigest(),
            'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'github_run_id':os.getenv('GITHUB_RUN_ID'),'github_sha':os.getenv('GITHUB_SHA'),
            'elapsed_seconds':round(time.monotonic()-started,4)}
    (outdir/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('outdir');args=p.parse_args()
    out=Path(args.outdir);out.mkdir(parents=True,exist_ok=True);run(out)
