#!/usr/bin/env python3
"""Deterministic, original-space CNF for mutually orthogonal Latin squares.

Orthogonality uses a conjugate Latin-square channel, not pairwise cell
collisions. See ENCODING.md for the equivalence and normalization proof.
No solver-specific preprocessing is part of the trusted encoding.
"""
from __future__ import annotations
import argparse, hashlib, itertools, json, pathlib

VERSION='mols-composition-cnf-v2'

def partitions(n,low=2):
    if n==0: yield ()
    for a in range(low,n+1):
        for tail in partitions(n-a,a): yield (a,)+tail

def permutation(parts):
    p=[];cycles=[];start=0
    for size in parts:
        cyc=list(range(start,start+size));cycles.append(cyc)
        p.extend(cyc[1:]+cyc[:1]);start+=size
    return p,cycles

def pair_orbits(parts):
    """Independently construct the explicit centralizer action on pairs."""
    p,cycles=permutation(parts);n=len(p);generators=[]
    for cycle in cycles[1:]:
        g=list(range(n))
        for x in cycle:g[x]=p[x]
        generators.append(g)
    for a,b in itertools.combinations(cycles[1:],2):
        if len(a)!=len(b):continue
        g=list(range(n))
        for x,y in zip(a,b):g[x],g[y]=y,x
        generators.append(g)
    for g in generators:
        assert sorted(g)==list(range(n)) and g[0]==0 and g[1]==1
        assert all(g[p[x]]==p[g[x]] for x in range(n))
    remaining=set(itertools.combinations(range(2,n),2));orbits=[]
    while remaining:
        rep=min(remaining);orbit={rep};todo=[rep]
        for pair in todo:
            for g in generators:
                image=tuple(sorted(g[x] for x in pair))
                if image not in orbit:orbit.add(image);todo.append(image)
        assert orbit<=remaining
        remaining-=orbit
        orbits.append({'representative':list(rep),'members':[list(x) for x in sorted(orbit)]})
    return orbits

def neg(lit):
    if lit is True:return False
    if lit is False:return True
    return -lit

class Formula:
    def __init__(self,amo='pairwise'):
        self.nvars=0;self.clauses=[];self.amo=amo
    def new(self):
        self.nvars+=1;return self.nvars
    def add(self,*lits):
        if any(x is True for x in lits):return
        clause=[];seen=set()
        for x in lits:
            if x is False:continue
            assert isinstance(x,int) and x!=0
            if -x in seen:return
            if x not in seen:seen.add(x);clause.append(x)
        if not clause:
            # Represent an empty clause by contradictory units. This avoids
            # legacy LRAT parsers that stop at an empty input clause.
            z=self.new();self.clauses.extend([[z],[-z]])
        else:self.clauses.append(clause)
    def exactly_one(self,lits):
        true_count=sum(x is True for x in lits)
        variables=[x for x in lits if x is not False and x is not True]
        if true_count:
            if true_count>1:self.add()
            for x in variables:self.add(-x)
            return
        self.add(*variables)
        if self.amo=='pairwise' or len(variables)<=3:
            for x,y in itertools.combinations(variables,2):self.add(-x,-y)
        elif len(variables)>=2:
            # Sinz sequential at-most-one. All auxiliary variables are fresh.
            aux=[self.new() for _ in range(len(variables)-1)]
            self.add(-variables[0],aux[0])
            for i in range(1,len(variables)-1):
                self.add(-variables[i],aux[i]);self.add(-aux[i-1],aux[i])
                self.add(-variables[i],-aux[i-1])
            self.add(-variables[-1],-aux[-1])
    def dimacs(self):
        return f'p cnf {self.nvars} {len(self.clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in self.clauses)
    def xor_even(self,lits):
        acc=False
        for lit in lits:
            if lit is False:continue
            if lit is True:acc=neg(acc);continue
            if acc is False:acc=lit;continue
            if acc is True:acc=-lit;continue
            y=self.new()
            self.add(acc,lit,-y);self.add(acc,neg(lit),y)
            self.add(neg(acc),lit,y);self.add(neg(acc),neg(lit),-y)
            acc=y
        self.add(neg(acc))

def enforce_even_permutation(f,cells,domains):
    """Exact inversion parity, given that the row is a permutation."""
    inversions=[]
    for c,d in itertools.combinations(range(len(cells)),2):
        if len(domains[c])==len(domains[d])==1:
            inversions.append(domains[c][0]>domains[d][0]);continue
        inv=f.new();inversions.append(inv)
        for u in domains[c]:
            for v in domains[d]:
                if u==v:continue # row Latin constraints exclude equal values
                f.add(neg(cells[c][u]),neg(cells[d][v]),inv if u>v else -inv)
    f.xor_even(inversions)

def encode(n=10,squares=3,parts=None,amo='pairwise',pair_symmetry=True,channel_reverse=False,even_second_rows=False):
    assert n>=2 and 1<=squares<=3 and amo in ('pairwise','sequential')
    if parts is not None:
        parts=tuple(parts);assert sum(parts)==n and all(x>=2 for x in parts)
        p,_=permutation(parts)
    if even_second_rows:
        # n row-parity signatures, at most 2^squares signatures. Two equal
        # signatures normalize all second-row permutations to even ones.
        assert n>2**squares
        if parts is not None:assert (n-len(parts))%2==0
    pairs=list(itertools.combinations(range(squares),2))
    labels=[f'L{s}' for s in range(squares)]+[f'Z{a}_{b}' for a,b in pairs]
    f=Formula(amo);tables={};fixeds={};domains={};variables=[]
    for label in labels:
        fixed={(0,c):c for c in range(n)}
        if label=='L0':
            fixed.update({(r,0):r for r in range(n)})
            if parts is not None:fixed.update({(1,c):p[c] for c in range(n)})
        for (r,c),v in fixed.items():
            assert all(rr!=r or cc==c or vv!=v for (rr,cc),vv in fixed.items())
            assert all(cc!=c or rr==r or vv!=v for (rr,cc),vv in fixed.items())
        table=[];domain=[]
        for r in range(n):
            row=[];drow=[]
            for c in range(n):
                if (r,c) in fixed:
                    allowed=[fixed[r,c]]
                else:
                    forbidden={v for (rr,cc),v in fixed.items() if rr==r or cc==c}
                    allowed=[v for v in range(n) if v not in forbidden]
                drow.append(allowed);cell=[]
                for v in range(n):
                    if (r,c) in fixed:lit=(v==fixed[r,c])
                    elif v not in allowed:lit=False
                    else:
                        lit=f.new();variables.append({'id':lit,'square':label,'r':r,'c':c,'value':v})
                    cell.append(lit)
                row.append(cell)
            table.append(row);domain.append(drow)
        tables[label]=table;domains[label]=domain
        fixeds[label]=[[r,c,v] for (r,c),v in sorted(fixed.items())]
    semantic_vars=f.nvars
    for table in tables.values():
        for r in range(n):
            for c in range(n):f.exactly_one(table[r][c])
        for r in range(n):
            for v in range(n):f.exactly_one([table[r][c][v] for c in range(n)])
        for c in range(n):
            for v in range(n):f.exactly_one([table[r][c][v] for r in range(n)])
    for a,b in pairs:
        P=tables[f'L{a}'];Q=tables[f'L{b}'];Z=tables[f'Z{a}_{b}']
        for r in range(n):
            for c in range(n):
                for u in domains[f'L{a}'][r][c]:
                    for v in domains[f'L{b}'][r][c]:
                        f.add(neg(P[r][c][u]),neg(Q[r][c][v]),Z[r][u][v])
                        if channel_reverse:
                            f.add(neg(P[r][c][u]),neg(Z[r][u][v]),Q[r][c][v])
                            f.add(neg(Q[r][c][v]),neg(Z[r][u][v]),P[r][c][u])
    orbits=None
    if squares==3:
        if parts is not None and pair_symmetry:
            orbits=pair_orbits(parts)
            allowed={tuple(x['representative']) for x in orbits}
        else:allowed={(a,b) for a in range(n) for b in range(n) if a<b}
        for a in range(n):
            for b in range(n):
                if (a,b) not in allowed:
                    f.add(neg(tables['L1'][1][0][a]),neg(tables['L2'][1][0][b]))
    parity_variables=f.nvars
    parity_clauses=len(f.clauses)
    if even_second_rows:
        for s in range(squares):
            if s==0 and parts is not None:continue # canonical permutation already checked even
            enforce_even_permutation(f,tables[f'L{s}'][1],domains[f'L{s}'][1])
    parity_variables=f.nvars-parity_variables
    parity_clauses=len(f.clauses)-parity_clauses
    metadata={'version':VERSION,'n':n,'squares':squares,'parts':list(parts) if parts else None,
              'amo':amo,'pair_symmetry':pair_symmetry,'channel_reverse':channel_reverse,
              'even_second_rows':even_second_rows,'parity_variables':parity_variables,'parity_clauses':parity_clauses,
              'variables':variables,'fixed':fixeds,'semantic_variables':semantic_vars,
              'nvars':f.nvars,'clauses':len(f.clauses),'pair_orbits':orbits}
    return f,metadata

def sha256_file(path):
    h=hashlib.sha256()
    with open(path,'rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()

def write_instance(directory,n,squares,parts,amo='pairwise',pair_symmetry=True,channel_reverse=False,even_second_rows=False):
    directory=pathlib.Path(directory);directory.mkdir(parents=True,exist_ok=True)
    f,m=encode(n,squares,parts,amo,pair_symmetry,channel_reverse,even_second_rows)
    (directory/'base.cnf').write_text(f.dimacs())
    m['cnf_sha256']=sha256_file(directory/'base.cnf')
    (directory/'mapping.json').write_text(json.dumps(m,indent=2)+'\n')
    return m

def verify_squares(squares):
    assert squares and len(squares[0])>=2
    n=len(squares[0]);alphabet=set(range(n))
    for square in squares:
        assert len(square)==n and all(len(row)==n for row in square)
        assert all(set(row)==alphabet for row in square)
        assert all({square[r][c] for r in range(n)}==alphabet for c in range(n))
    for a,b in itertools.combinations(range(len(squares)),2):
        assert len({(squares[a][r][c],squares[b][r][c]) for r in range(n) for c in range(n)})==n*n

def decode_model(metadata,model):
    positive={x for x in model if x>0};n=metadata['n'];m=metadata['squares']
    squares=[[[None]*n for _ in range(n)] for _ in range(m)]
    for s in range(m):
        for r,c,v in metadata['fixed'][f'L{s}']:squares[s][r][c]=v
    for var in metadata['variables']:
        if not var['square'].startswith('L') or var['id'] not in positive:continue
        s=int(var['square'][1:]);r=var['r'];c=var['c'];v=var['value']
        assert squares[s][r][c] is None
        squares[s][r][c]=v
    verify_squares(squares)
    assert all(square[0]==list(range(n)) for square in squares)
    assert [squares[0][r][0] for r in range(n)]==list(range(n))
    if metadata['parts']:
        p,_=permutation(metadata['parts']);assert squares[0][1]==p
    if m==3:
        pair=[squares[1][1][0],squares[2][1][0]]
        assert pair[0]<pair[1]
        if metadata['pair_orbits']:assert pair in [o['representative'] for o in metadata['pair_orbits']]
    if metadata['even_second_rows']:
        for square in squares:
            assert sum(square[1][c]>square[1][d] for c,d in itertools.combinations(range(n),2))%2==0
    return squares

def read_dimacs(path):
    clauses=[];carry=[];header=None
    for line in pathlib.Path(path).read_text().splitlines():
        if not line or line.startswith('c'):continue
        if line.startswith('p'):
            _,kind,nvars,nclauses=line.split();assert kind=='cnf';header=(int(nvars),int(nclauses));continue
        for x in map(int,line.split()):
            if x==0:clauses.append(carry);carry=[]
            else:carry.append(x)
    assert header is not None and not carry and len(clauses)==header[1]
    assert all(0<abs(x)<=header[0] for c in clauses for x in c)
    return header[0],clauses

def verify_model_cnf(path,model):
    nvars,clauses=read_dimacs(path);truth=set(model)
    assert all(-x not in truth for x in truth)
    assert all(any(x in truth for x in clause) for clause in clauses)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--n',type=int,default=10)
    ap.add_argument('--squares',type=int,default=3);ap.add_argument('--shard',type=int,default=0)
    ap.add_argument('--amo',choices=['pairwise','sequential'],default='pairwise')
    ap.add_argument('--even-row-normalization',action='store_true')
    ap.add_argument('--out',required=True);args=ap.parse_args()
    parts=list(partitions(args.n))[args.shard]
    metadata=write_instance(args.out,args.n,args.squares,parts,args.amo,even_second_rows=args.even_row_normalization)
    print(json.dumps({k:v for k,v in metadata.items() if k not in ('variables','fixed','pair_orbits')}))
