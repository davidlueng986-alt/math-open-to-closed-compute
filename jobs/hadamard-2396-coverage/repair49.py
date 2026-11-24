"""Enumerate every pair of equal-size orbit exchanges around the 310-pair certificate."""

from collections import Counter
import json
from math import comb
from pathlib import Path
import subprocess
import sys

from coverage import GROUP, HERE
from audit_group import N, all_paf
from remaining import reduction


def label(s):
    return min(u*s%N for a in GROUP for u in (a,-a))


def main(binary=None):
    record=json.loads((HERE/"results.json").read_text())["witnesses"]["cyclic"]["coverage"]
    masks=[int(m,16) for m in record["negative_masks"]]
    initial=all_paf(record["negative_masks"],False,True)
    reps=sorted({label(s) for s in initial})
    exact=[i for i,s in enumerate(reps) if initial[s]==-2]
    reverse={s:i for i,s in enumerate(reps)}
    qs=reduction(record,"cyclic")["independent_quotient_equations"]
    rows=[list(Counter(reverse[label(s)] for s in range(t,N,q) if s).items()) for q,t in qs]
    weight=Counter(label(s) for s in initial)
    orbits={tuple(sorted({i*g%N for g in GROUP})) for i in range(N)}
    buckets={size:[sum(1<<i for i in orb) for orb in sorted(orbits) if len(orb)==size] for size in (1,9)}
    if sum(k*len(v) for k,v in buckets.items())!=N:
        raise ValueError("incomplete orbit partition")
    mask=(1<<N)-1
    def paf(bits,s):
        return N-2*(bits^((bits>>s)|((bits<<(N-s))&mask))).bit_count()
    def moves(bits):
        yield 0
        for bucket in buckets.values():
            inside=[m for m in bucket if bits&m==m]
            outside=[m for m in bucket if bits&m==0]
            if len(inside)+len(outside)!=len(bucket):
                raise ValueError("starting word breaks square invariance")
            for a in inside:
                for b in outside:
                    yield a|b
    def changes(bits):
        before=[paf(bits,s) for s in reps]
        for swap in moves(bits):
            d=[paf(bits^swap,s)-p for s,p in zip(reps,before)] if swap else [0]*len(reps)
            known=tuple(d[i] for i in exact)
            quotient=tuple(sum(w*d[i] for i,w in row) for row in rows)
            yield swap,d,known,quotient
    first={}
    original_only=Counter()
    na=0
    for swap,d,known,more in changes(masks[0]):
        na+=1
        first.setdefault(known+more,[]).append((swap,d))
        original_only[known]+=1
    raw_count=0
    both=0
    nb=0
    minimum=record["raw_energy"]
    highest=record["raw_exact_pairs"]
    for swap,d,known,more in changes(masks[1]):
        nb+=1
        raw_count+=original_only[tuple(-v for v in known)]
        for left,delta in first.get(tuple(-v for v in known+more),()):
            both+=1
            actual=all_paf([hex(masks[0]^left),hex(masks[1]^swap)],False,False)
            if any(actual[s]!=initial[s]+d[i]+delta[i] for i,s in enumerate(reps)):
                raise ValueError("matched moves disagree with direct original correlations")
            minimum=min(minimum,sum(weight[s]*(actual[s]+2)**2 for s in reps))
            highest=max(highest,sum(weight[s] for s in reps if actual[s]==-2))
    result={"row_neighborhoods":[na,nb],"word_pairs":na*nb,"preserve_310_including_identity":raw_count,
            "preserve_310_and_six_quotients_including_identity":both,"minimum_energy":minimum,
            "maximum_exact_pairs":highest}
    if (na,nb,raw_count,both)!=(4962,4962,1,1):
        raise ValueError("single-exchange census changed")
    if binary is not None:
        data=[" ".join(map(str,GROUP))]
        data.extend(" ".join(str(mask>>i&1) for i in range(N)) for mask in masks)
        data += [str(len(exact))," ".join(str(reps[i]) for i in exact)]
        def meet(radius,control=False):
            args=[str(binary.resolve()),str(radius)]
            if control: args.append("control")
            return json.loads(subprocess.run(args,input="\n".join(data)+"\n",text=True,
                                             stdout=subprocess.PIPE,check=True).stdout)
        small=meet(1)
        if small["row_neighborhoods"]!=[na,nb] or small["exact_matches"]!=raw_count:
            raise ValueError("independent scalar and fingerprint one-exchange censuses disagree")
        control=meet(2,True)
        if control["exact_matches"]<1:
            raise ValueError("two-exchange planted control failed")
        choices=[]
        for bits in masks:
            sizes={w:(sum(bits&m==m for m in bucket),sum(bits&m==0 for m in bucket))
                   for w,bucket in buckets.items()}
            def ways(w,k):
                a,b=sizes[w]
                return comb(a,k)*comb(b,k)
            choices.append(sum(ways(1,i)*ways(9,j) for i in range(3) for j in range(3-i)))
        large=meet(2)
        if (large["row_neighborhoods"]!=choices or large["word_pairs"]!=choices[0]*choices[1]
            or large["fingerprint_matches"]!=1 or large["exact_matches"]!=1):
            raise ValueError("two-exchange census changed")
        result["two_exchanges"]=large
        result["planted_matches"]=control["exact_matches"]
    print(json.dumps(result))


if __name__=="__main__":
    main(Path(sys.argv[1]) if len(sys.argv)>1 else None)
