#!/usr/bin/env python3
"""Convert source squares to a bounded, validated orthogonal-pair seed corpus."""
import argparse,hashlib,json,re
from pathlib import Path
R=Path(__file__).resolve().parent

def latin(s):
 return len(s)==100 and all(set(s[10*r:10*r+10])==set(range(10)) for r in range(10)) and all({s[10*r+c] for r in range(10)}==set(range(10)) for c in range(10))
def orth(a,b):return len(set(zip(a,b)))==100

def parse(path):
 lines=path.read_text().splitlines();words=[x.strip() for x in lines if re.fullmatch('[a-j]{10}',x.strip())]
 return [[ord(c)-97 for line in words[i:i+10] for c in line] for i in range(0,len(words)-9,10)]

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--random-pairs',type=int,default=500);a=ap.parse_args()
 triples=json.loads((R/'baseline.json').read_text())['squares'];s=[[x for row in q for x in row] for q in triples]
 pairs=[(s[0],s[1]),(s[0],s[2])];sources=[]
 for name,cap in [('2MOLS10_achieving_all_parities.txt',32),('MOLS10.txt',a.random_pairs)]:
  p=R/name
  if not p.exists():continue
  q=parse(p);npairs=min(cap,len(q)//2)
  for i in range(npairs):
   x,y=q[2*i:2*i+2];assert latin(x) and latin(y) and orth(x,y),(name,i)
   pairs.append((x,y))
  sources.append({'name':name,'source':'https://users.monash.edu.au/~iwanless/data/MOLS/'+name,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'pairs_used':npairs})
 lines=[str(len(pairs))]
 for x,y in pairs:
  assert latin(x) and latin(y) and orth(x,y)
  lines.extend([''.join(map(str,x)),''.join(map(str,y))])
 (R/'seeds.txt').write_text('\n'.join(lines)+'\n');(R/'source_manifest.json').write_text(json.dumps({'pairs':len(pairs),'sources':sources},indent=2)+'\n')
 print(json.dumps({'pairs':len(pairs),'sources':sources}))
if __name__=='__main__':main()
