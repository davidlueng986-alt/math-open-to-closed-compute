#!/usr/bin/env sage -python
"""Deterministic, bounded Dokchitser-style abc relation search; no global claim."""
import argparse
import hashlib
import itertools
import json
import math
import os
import platform
import time
from pathlib import Path
from sage.all import ZZ, matrix, RealIntervalField, proof
from sage.version import version as sage_version

proof.all(True)
RIF = RealIntervalField(256)
RECORD = (2, 6436341, 6436343)
EPSILONS = [(1, 100), (1, 10), (1, 2)]

def dump(path, obj):
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + '\n')

def factors(n):
    f = [(int(p), int(e)) for p,e in ZZ(n).factor(proof=True)]
    assert math.prod(p**e for p,e in f) == int(n)
    assert all(ZZ(p).is_prime(proof=True) and e>0 for p,e in f)
    return f

def certify(triple, provenance):
    a,b,c = map(int,triple)
    assert 0<a<=b and a+b==c
    assert math.gcd(a,b)==math.gcd(b,c)==math.gcd(a,c)==1
    fs = [factors(x) for x in (a,b,c)]
    rad = math.prod({p for f in fs for p,e in f})
    q = RIF(c).log()/RIF(rad).log()
    return dict(a=str(a), b=str(b), c=str(c), radical=str(rad),
                factors=[[[str(p),e] for p,e in f] for f in fs],
                quality_display=float(q.center()), quality_interval_256=str(q),
                quality_gt_8_over_5=(c**5>rad**8),
                quality_test={'numerator':8,'denominator':5,
                              'lhs':'c^5','rhs':'radical^8','strict_gt':c**5>rad**8},
                origin=provenance)

def normalize(terms):
    terms=list(map(int,terms))
    assert sum(terms)==0
    if 0 in terms: return None
    g=math.gcd(*terms)
    positives=[t//g for t in terms if t>0]
    negatives=[-t//g for t in terms if t<0]
    if len(positives)==1:
        a,b=sorted(negatives);c=positives[0]
    else:
        a,b=sorted(positives);c=negatives[0]
    assert a+b==c and math.gcd(a,b)==1
    return (a,b,c)

def kernel(A,B,C):
    """Full saturated Z-kernel, not a merely rational or finite-index kernel."""
    g,u,v=ZZ(A).xgcd(ZZ(B))
    assert g==1 and u*A+v*B==1
    K=matrix(ZZ,[[B,-A,0],[-u*C,-v*C,1]])
    assert all(sum(row[i]*[A,B,C][i] for i in range(3))==0 for row in K.rows())
    return K

def seeds():
    # The reference seed is explicitly separated from exploratory enumeration.
    yield ('known_reyssat_replay',(2,3**10,23**5),None)
    primes=[2,3,5,7,11,13,17,19,23]
    offsets=[(0,0,0),(-1,0,1),(1,-1,0),(0,1,-1)]
    for bits in [20,32,48,64]:
        for ps in itertools.combinations(primes,3):
            base_exp=[]
            for p in ps:
                e=1
                while p**(e+1)<=2**bits: e+=1
                base_exp.append(e)
            for off in offsets:
                es=[max(1,e+o) for e,o in zip(base_exp,off)]
                yield ('exploratory',tuple(p**e for p,e in zip(ps,es)),dict(bits=bits,primes=ps,exponents=es,offset=off))

def exact_ratio_bracket(c,rad,num,den,scale=10000):
    """Certify a rational bracket for c/R^(1+num/den) by integer powers."""
    interval=RIF(c)/(RIF(rad)**(RIF(den+num)/den))
    low=int((interval.lower()*scale).floor())
    # The decimal bracket is ultimately checked by exact integers, not intervals.
    while (c*scale)**den <= low**den * rad**(den+num): low-=1
    high=low+1
    while (c*scale)**den >= high**den * rad**(den+num): high+=1
    assert low>=0 and (c*scale)**den > low**den*rad**(den+num)
    assert (c*scale)**den < high**den*rad**(den+num)
    return dict(epsilon_numerator=num,epsilon_denominator=den,
                lower_numerator=str(low),upper_numerator=str(high),denominator=scale,
                exact_lower_check=True,exact_upper_check=True,
                interpretation='Any global K_epsilon is greater than the certified lower endpoint. The upper endpoint bounds this one ratio only, not global K_epsilon.')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',required=True);ap.add_argument('--shard',type=int,default=0);ap.add_argument('--shards',type=int,default=1)
    args=ap.parse_args();assert 0<=args.shard<args.shards
    out=Path(args.out);out.mkdir(parents=True,exist_ok=True)
    started=time.monotonic();manifest=list(seeds())
    observations={};seen_relations=0;zero_relations=0;lll_calls=0;bkz_calls=0;processed=[]
    for idx,(kind,bases,meta) in enumerate(manifest):
        if idx%args.shards!=args.shard: continue
        A,B,C=map(ZZ,bases);K=kernel(A,B,C)
        L=K.LLL();lll_calls+=1
        reductions=[('LLL',L)]
        # Rank is two: BKZ(2) is a reproducibility cross-check, not a larger-block advantage.
        if idx%32==0 or kind=='known_reyssat_replay':
            K2=K.BKZ(block_size=2);bkz_calls+=1;reductions.append(('BKZ-2',K2))
        processed.append(dict(index=idx,kind=kind,bases=list(map(str,bases)),meta=meta))
        for algorithm,L in reductions:
            assert L.nrows()==2 and L.ncols()==3
            for i,j in itertools.product(range(-2,3),repeat=2):
                if (i,j)==(0,0):continue
                # Remove global-sign duplicates; other duplicates are deduplicated below.
                if i<0 or (i==0 and j<0):continue
                coeff=i*L.row(0)+j*L.row(1)
                terms=[coeff[t]*[A,B,C][t] for t in range(3)]
                assert sum(terms)==0;seen_relations+=1
                triple=normalize(terms)
                if triple is None: zero_relations+=1;continue
                if triple in observations:
                    if kind=='exploratory':observations[triple]['seen_exploratory']=True
                    continue
                cert=certify(triple,dict(kind=kind,seed_index=idx,algorithm=algorithm,
                                       bases=list(map(str,bases)),coefficients=list(map(str,coeff)),combination=[i,j]))
                cert['seen_exploratory']=(kind=='exploratory');observations[triple]=cert
        if idx%200==0:
            print(json.dumps(dict(progress_seed=idx,total_seeds=len(manifest),unique_triples=len(observations))),flush=True)
    # A replay assertion is required only in the shard that contains seed zero.
    if args.shard==0:
        assert RECORD in observations, 'LLL/BKZ replay failed to recover the known benchmark'
        assert observations[RECORD]['quality_gt_8_over_5']
    vals=list(observations.values());vals.sort(key=lambda d:d['quality_display'],reverse=True)
    high=[d for d in vals if d['quality_gt_8_over_5']]
    reference=certify(RECORD,{'kind':'independent_reference'})
    qref=RIF(int(reference['c'])).log()/RIF(int(reference['radical'])).log()
    stronger=[];unresolved=[]
    for d in vals:
        if (int(d['a']),int(d['b']),int(d['c']))==RECORD:continue
        interval=RIF(int(d['c'])).log()/RIF(int(d['radical'])).log()
        if interval.lower()>qref.upper():stronger.append(d)
        elif interval.upper()>=qref.lower():unresolved.append(d)
    constants=[]
    for num,den in EPSILONS:
        # Maximizer chosen using intervals, then its lower bound is certified exactly.
        chosen=max(vals,key=lambda d:(RIF(int(d['c']))/RIF(int(d['radical']))**(RIF(num+den)/den)).lower())
        cc=int(chosen['c']);rr=int(chosen['radical'])
        constants.append(dict(source_triple=[chosen[t] for t in ['a','b','c']],
                              bracket=exact_ratio_bracket(cc,rr,num,den)))
    record_constants=[exact_ratio_bracket(RECORD[2],15042,n,d) for n,d in EPSILONS]
    # Store complete certificates for every high-quality hit, top 40, and constant witnesses.
    kept={tuple(d[t] for t in ['a','b','c']):d for d in vals[:40]+high+stronger+unresolved}
    for row in constants:
        key=tuple(row['source_triple']);kept[key]=observations[tuple(map(int,key))]
    canonical='\n'.join(','.join(map(str,t)) for t in sorted(observations))+'\n'
    certificates=dict(reference=reference,record_constant_brackets=record_constants,
                      finite_search_constant_witnesses=constants,candidates=list(kept.values()))
    dump(out/'certificates.json',certificates);dump(out/'seed_manifest.json',processed)
    summary=dict(problem='ABC',agent=4,status='CHECKED',resolution='unknown',
        scope='Bounded heuristic lattice search and exact finite certificates only; not an exhaustive abc search, not an infinite family, not a global K upper bound.',
        environment={'sage':str(sage_version),'python':platform.python_version(),'proof_all':True},
        shard=args.shard,shards=args.shards,total_manifest_seeds=len(manifest),processed_seeds=len(processed),
        lll_calls=lll_calls,bkz_calls=bkz_calls,bkz_block_size=2,
        coefficient_combination_box=[-2,2],relations_tested=seen_relations,zero_relations=zero_relations,
        unique_primitive_triples=len(vals),unique_triples_sha256=hashlib.sha256(canonical.encode()).hexdigest(),
        seeded_replay_included=(args.shard==0),
        high_quality_gt_8_over_5=[dict(a=d['a'],b=d['b'],c=d['c'],quality=d['quality_display'],seen_exploratory=d['seen_exploratory']) for d in high],
        strictly_above_reference=[dict(a=d['a'],b=d['b'],c=d['c'],quality=d['quality_display']) for d in stronger],
        unresolved_reference_comparisons=len(unresolved),top=vals[:10],
        record_constant_brackets=record_constants,finite_search_constant_witnesses=constants,
        certificate_sha256=hashlib.sha256((out/'certificates.json').read_bytes()).hexdigest(),
        elapsed_seconds=round(time.monotonic()-started,3))
    dump(out/'result.json',summary)
    print(json.dumps({k:v for k,v in summary.items() if k!='top'},indent=2),flush=True)

if __name__=='__main__':main()
