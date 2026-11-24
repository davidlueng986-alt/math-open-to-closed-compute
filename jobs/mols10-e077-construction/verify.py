#!/usr/bin/env python3
"""Independent standard-library witness/checkpoint verifier, including exact pair audit.
This program cannot conclude global nonexistence from any restricted search result.
"""
import argparse,json
from pathlib import Path

def check_square(q,n):
 assert len(q)==n*n and all(type(x) is int and 0<=x<n for x in q)
 target=set(range(n))
 assert all(set(q[r*n:(r+1)*n])==target for r in range(n))
 assert all({q[r*n+c] for r in range(n)}==target for c in range(n))

def check_pair(a,b,n):
 assert len(set(zip(a,b)))==n*n

def all_transversals(a,b,n):
 result=[]
 def dfs(rows,cols,aa,bb,cells):
  if not rows:
   result.append(tuple(sorted(cells)));return
  r,allowed=min(((r,[c for c in range(n) if c not in cols and a[n*r+c] not in aa and b[n*r+c] not in bb]) for r in rows),key=lambda t:len(t[1]))
  for c in allowed:
   i=n*r+c;dfs(rows-{r},cols|{c},aa|{a[i]},bb|{b[i]},cells+[i])
 dfs(set(range(n)),set(),set(),set(),[])
 return result

def maximum_packing(ts,n):
 masks=[sum(1<<i for i in t) for t in ts]
 groups=[[m for t,m in zip(ts,masks) if c in t] for c in range(n)]
 groups.sort(key=len);best=[];chosen=[];nodes=0
 def dfs(d,used):
  nonlocal best,nodes
  nodes+=1
  if len(chosen)>len(best):best=chosen[:]
  if len(best)==n or d==n or len(chosen)+n-d<=len(best):return
  for m in groups[d]:
   if not m&used:chosen.append(m);dfs(d+1,used|m);chosen.pop()
  dfs(d+1,used)
 dfs(0,0)
 return len(best),nodes

def candidate(c,n,exhaustive=False):
 a,b=c['A'],c['B'];check_square(a,n);check_square(b,n);check_pair(a,b,n)
 ts=c['disjoint_transversals'];assert len(ts)==c['packing']
 seen=set();goal=set(range(n))
 for t in ts:
  assert len(t)==n and len(set(t))==n and all(type(i) is int and 0<=i<n*n for i in t)
  assert not seen.intersection(t);seen.update(t)
  assert {i//n for i in t}==goal and {i%n for i in t}==goal
  assert {a[i] for i in t}==goal and {b[i] for i in t}==goal
 if 'two_remaining_odd_cycle' in c:
  cycle=c['two_remaining_odd_cycle'];assert len(ts)==n-2 and len(cycle)>=3 and len(cycle)%2==1 and len(cycle)==len(set(cycle))
  assert all(type(i) is int and 0<=i<n*n and i not in seen for i in cycle)
  assert all(u//n==v//n or u%n==v%n or a[u]==a[v] or b[u]==b[v] for u,v in zip(cycle,cycle[1:]+cycle[:1]))
 result={'order':n,'pair_valid':True,'packing_lower_bound':len(ts),'triple_valid':False}
 if len(ts)==n:
  third=[None]*(n*n)
  for j,t in enumerate(ts):
   for i in t:third[i]=j
  check_square(third,n);check_pair(a,third,n);check_pair(b,third,n)
  if 'C'in c:assert c['C']==third
  result['triple_valid']=True
 elif 'C' in c:raise AssertionError('A full third square was claimed without a full transversal decomposition')
 if exhaustive:
  allts=all_transversals(a,b,n);assert len(allts)==c['common_transversals']
  maxp,nodes=maximum_packing(allts,n)
  assert maxp>=len(ts)
  if c['packing_search_complete']:assert maxp==len(ts)
  result.update(common_transversals=len(allts),maximum_disjoint=maxp,packing_nodes=nodes,pair_extendible=maxp==n)
 return result

def main():
 ap=argparse.ArgumentParser();ap.add_argument('checkpoint',type=Path);ap.add_argument('--exhaustive',action='store_true');ap.add_argument('--report',type=Path);a=ap.parse_args()
 d=json.loads(a.checkpoint.read_text());n=d.get('order',10)
 result=candidate(d['best'],n,a.exhaustive)
 for c in d.get('elite',[]):candidate(c,n,False)
 assert (d['status']=='YES_WITNESS')==result['triple_valid']
 result.update(checkpoint=str(a.checkpoint),status=d['status'],elite_verified=len(d.get('elite',[])),global_nonexistence_claim=False)
 if a.report:a.report.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
