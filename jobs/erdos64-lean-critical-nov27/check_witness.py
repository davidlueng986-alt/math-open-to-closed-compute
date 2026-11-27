import json
from pathlib import Path
edges10=[(0,2),(0,5),(0,6),(1,6),(1,8),(2,4),(2,5),(3,5),(3,8),(3,9),(4,7),(6,9),(7,9)]
edges12=[(0,1),(0,4),(0,8),(1,11),(2,6),(2,9),(3,5),(3,6),(4,6),(4,10),(5,8),(7,8),(7,9),(9,11),(10,11)]
def verify(n,edges):
 adj=[set() for _ in range(n)]
 for u,v in edges:adj[u].add(v);adj[v].add(u)
 cycles=set()
 for start in range(n):
  def dfs(p):
   v=p[-1]
   for u in adj[v]:
    if u==start and len(p)>=3 and p[1]<p[-1]: cycles.add(tuple(p))
    if u>start and u not in p:dfs(p+[u])
  dfs([start])
 lengths=sorted(set(map(len,cycles)))
 assert all(x&(x-1) for x in lengths)
 witnesses={}
 for start in range(n):
  def dfs(p):
   if len(p)-1 in (4,8):
    stop=p[-1]
    if stop>start and stop not in witnesses.get(start,{}):witnesses.setdefault(start,{})[stop]=p[:]
   if len(p)==9:return
   for u in adj[p[-1]]:
    if u not in p:dfs(p+[u])
  dfs([start])
 assert sum(map(len,witnesses.values()))==n*(n-1)//2
 # biconnectivity independently by deletion connectivity
 connected=[]
 for deleted in range(n):
  s=next(i for i in range(n) if i!=deleted);seen={s};todo=[s]
  while todo:
   v=todo.pop()
   for u in adj[v]-seen-{deleted}:seen.add(u);todo.append(u)
  connected.append(len(seen)==n-1)
 out={'order':n,'edges':edges,'degrees':[len(x) for x in adj],'cycle_lengths':lengths,'cycles':sorted(cycles),'pair_paths':[{'u':s,'v':t,'path':p,'length':len(p)-1} for s,d in witnesses.items() for t,p in sorted(d.items())],'all_vertex_deletions_connected':all(connected),'scope':'Counterexample to all-pairs dyadic-path forcing, NOT original minimum-degree-three counterexample.'}
 Path(f'nov27/core_attack/witness{n}.json').write_text(json.dumps(out,indent=2))
 print({k:v for k,v in out.items() if k not in ('cycles','pair_paths')})
 print('cycles',len(cycles),'pairs',len(out['pair_paths']))
verify(10,edges10)
verify(12,edges12)
