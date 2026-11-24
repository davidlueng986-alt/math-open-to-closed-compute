#!/usr/bin/env python3
"""Reconstruct the finite point-set inputs. Standard-library exact arithmetic."""
from collections import Counter
from itertools import combinations, product
from pathlib import Path
import json
from profile_data import PROFILES


def verify(inputs):
    def load(name, n, dim):
        rows=[tuple(map(int,s.strip())) for s in (inputs/name).read_text().splitlines() if s.strip()]
        assert len(rows)==len(set(rows))==n
        assert all(len(p)==dim and all(0<=x<3 for x in p) for p in rows)
        S=set(rows)
        for p,q in combinations(rows,2):
            assert tuple((-x-y)%3 for x,y in zip(p,q)) not in S
        return rows
    lower=load('cap236.txt',236,7)
    H=load('hill112.txt',112,6);S=set(H);neg=lambda p:tuple(-x%3 for x in p)
    assert (0,)*6 not in S and {neg(p) for p in H}==S
    space=list(product(range(3),repeat=6))
    conv=Counter(tuple((x+y)%3 for x,y in zip(p,q)) for p in H for q in H)
    assert all(conv[z]==(112 if not any(z) else 1 if z in S else 20) for z in space)
    normals=[p for p in space if any(p) and next(x for x in p if x)==1]
    assert len(normals)==364
    values=[[sum(x*y for x,y in zip(u,p))%3 for u in normals] for p in H]
    bases=[tuple(sum(values[i][j]==r for i in range(112)) for r in range(3)) for j in range(364)]
    assert Counter(bases)=={(22,45,45):56,(40,36,36):308}
    negative={u for u,b in zip(normals,bases) if b[0]==22}
    assert negative|{neg(u) for u in negative}==S
    # This is an exact real-character check: F_H(u)=(3*h0-112)/2.
    assert {(3*b[0]-112)//2 for b in bases}=={-23,4}
    Nmask=sum(1<<j for j,b in enumerate(bases) if b[0]==22)
    masks=[sum(1<<j for j,v in enumerate(vs) if v==0) for vs in values]
    for mask in masks:
        assert (mask&Nmask).bit_count()==11 and (mask&~Nmask).bit_count()==110
    pair_counts=Counter()
    for i,j in combinations(range(112),2):
        opposite=H[j]==neg(H[i]);c=masks[i]&masks[j]
        assert (c&Nmask).bit_count()==(11 if opposite else 2)
        assert c.bit_count()==(121 if opposite else 40)
        pair_counts['antipodal' if opposite else 'ordinary']+=1
    assert pair_counts=={'antipodal':56,'ordinary':6160}
    # Recount every one-/two-point deletion, not a sample or an orbit assumption.
    def fingerprint(indices):
        cnt=Counter()
        for j,b in enumerate(bases):
            row=list(b)
            for i in indices:row[values[i][j]]-=1
            cnt[(row[0],min(row[1:]),max(row[1:]))]+=1
        return dict(cnt)
    expected={k:dict(zip(map(tuple,hs),mult)) for k,(hs,mult) in PROFILES.items()}
    assert fingerprint(())==expected[(112,'single')]
    for i in range(112):assert fingerprint((i,))==expected[(111,'single')]
    for i,j in combinations(range(112),2):
        kind='antipodal' if H[j]==neg(H[i]) else 'ordinary'
        assert fingerprint((i,j))==expected[(110,kind)]
    # The two encodings consumed by separate completion checkers coincide.
    cap45=json.loads((inputs/'cap45.json').read_text())['cap45']
    codes=[sum(int(x)*3**i for i,x in enumerate(p)) for p in cap45]
    assert len(codes)==len(set(codes))==45
    assert set(codes)==set(map(int,(inputs/'cap45_codes.txt').read_text().split()))
    result={'status':'PASS','lower_bound':236,'lower_pairs_checked':236*235//2,
            'hill_size':112,'hill_pairs_checked':6216,'hill_convolution_points':729,
            'negative_fourier_support_equals_hill':True,
            'all_deleted_singletons':112,'all_deleted_pairs':6216,
            'projective_normals':364,'negative_normals':56,'positive_normals':308,
            'point_zero_incidence':[11,110],
            'pair_classes':dict(pair_counts),
            'classification_theorems_imported_not_reclassified':True}
    return result

if __name__=='__main__':
    print(json.dumps(verify(Path(__file__).resolve().parent.parent/'inputs'),indent=2))
