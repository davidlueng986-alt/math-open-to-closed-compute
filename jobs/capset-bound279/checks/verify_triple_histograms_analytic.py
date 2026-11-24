#!/usr/bin/env python3
"""Independent exact character-projection derivation of all four H-minus3 histograms.
No numpy and no point-triple enumeration. The derivation's geometric hypotheses
and spectrum are documented in HILL_MINUS3_CLASSIFICATION.md.
"""
from itertools import product
from collections import Counter
from pathlib import Path
import json,hashlib
OUT=Path(__file__).resolve().parent

def row_profile(base,values,center):
 row=[base[r]-values.count(r) for r in range(3)]
 if center:
  shift=sum(values)%3
  row=[row[(r-shift)%3] for r in range(3)]
 return (row[0],min(row[1:]),max(row[1:]))

def histogram(case,center):
 counts=Counter()
 if case=='antipodal':
  for x,y in product(range(3),repeat=2):
   nonzero=bool(x or y)
   n_total=81-(not nonzero)
   n_neg=18-9*((x==0)+(y==0)) if nonzero else 4
   values=[x,-x%3,y]
   counts[row_profile((22,45,45),values,center)]+=n_neg
   counts[row_profile((40,36,36),values,center)]+=n_total-n_neg
 else:
  extra={'no_signed_sum':None,'positive_sum':(1,1,1),'one_negative_sum':(1,1,2)}[case]
  k=3+(extra is not None)
  for w in product(range(3),repeat=3):
   nonzero=any(w);n_total=27-(not nonzero)
   orth=sum(x==0 for x in w)+(extra is not None and sum(a*b for a,b in zip(extra,w))%3==0)
   n_neg=4+k-3*orth if nonzero else 8-2*k
   assert 0<=n_neg<=n_total
   counts[row_profile((22,45,45),list(w),center)]+=n_neg
   counts[row_profile((40,36,36),list(w),center)]+=n_total-n_neg
 assert all(v%2==0 for v in counts.values())
 answer={k:v//2 for k,v in counts.items() if v};assert sum(answer.values())==364
 return answer

def main():
 supplied=json.loads((OUT/'deleted_triple_histograms.json').read_text())
 result=[]
 for case in ('no_signed_sum','positive_sum','one_negative_sum','antipodal'):
  r={'case':case}
  for key,center in [('completion_center_zero',False),('remaining_cap_centroid_zero',True)]:
   want=histogram(case,center)
   matches=[]
   for h in supplied[key]['histogram_classes']:
    if dict(zip(map(tuple,h['hprofiles']),h['multiplicities']))==want:matches.append(h['id'])
   assert len(matches)==1,(case,key,matches)
   assert sum(sum(x*x for x in h)*v for h,v in want.items())==1464088
   assert sum(sum(x*x*x for x in h)*v for h,v in want.items())==54697072
   r[key]={'matching_exhaustive_class_id':matches[0],'hprofiles':[list(x) for x in sorted(want)],'multiplicities':[want[x] for x in sorted(want)]}
   if center:
    origin_present=case in ('positive_sum','antipodal')
    first=sum(h[0]*v for h,v in want.items())
    assert first==121*109+243*origin_present
    r[key].update({'contains_origin':origin_present,'sum_of_zero_level_counts':first})
  result.append(r)
 report={'status':'PASS','exact_character_projection_cases':result,'does_not_assume_affine_orbit_classification':True,'independent_of_numpy_and_exhaustive_triple_enumeration':True,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
 (OUT/'deleted_triple_histograms_analytic.json').write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({'status':report['status'],'matching_cases':[{k:v for k,v in r.items() if k=='case'}|{k:r[k]['matching_exhaustive_class_id'] for k in ('completion_center_zero','remaining_cap_centroid_zero')} for r in result]},indent=2))
if __name__=='__main__':main()
