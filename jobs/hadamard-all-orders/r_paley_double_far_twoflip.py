"""Exact physical two-flip census, both far-pair pivots. Stdlib only."""
from collections import Counter
from itertools import combinations
from pathlib import Path
import json
import subprocess
import sys
from tempfile import TemporaryDirectory

from r_paley_double_far import build_source, dot, fibres
from r_paley_isotropic_code import assemble
from verify import rows_from_columns, verify_orthogonal

N = 1196
SIZE = 23
SECTOR = 368
LIMIT = 68
MASK = (1 << N) - 1
DIR = Path(__file__).parent


def sign(word, r):
    return 2 * ((word >> r) & 1) - 1


def raw_word(word, groups):
    return sum(1 << r for i, group in enumerate(groups) if word[i] > 0 for r in group)


def data(pivots):
    source = build_source()
    assert verify_orthogonal(N, source) == 714610
    groups = fibres()
    masks = [sum(1 << r for r in group) for group in groups]
    order = {r: i for i, group in enumerate(groups) for r in group}
    g = [[2 * (source[col[0]] & mask).bit_count() - SIZE for col in groups] for mask in masks]
    rows = rows_from_columns(N, source)
    assert all(2 * (source[c] & mask).bit_count() - SIZE == g[i][j]
               for i, mask in enumerate(masks) for c, j in order.items())
    assert all(2 * (rows[r] & mask).bit_count() - SIZE == g[i][j]
               for j, mask in enumerate(masks) for r, i in order.items())
    anchor = tuple(raw_word(tuple(1 if row[j] > 0 else -1 for row in g), groups) for j in pivots)
    anchor = tuple(w if w & 1 else w ^ MASK for w in anchor)
    assert dot(*anchor) == 0
    decks = tuple(tuple(dot(w, c) for c in source) for w in anchor)
    assert all(max(map(abs, deck)) == 230 for deck in decks)
    sides = [[j for j, (c, *_) in enumerate(groups) if abs(decks[0][c]) == 2
              and decks[0][c] == e * decks[1][c]] for e in (1, -1)]
    assert tuple(map(len, sides)) == (16, 16)
    reflect = tuple(13*(j//13) + 12-j%13 for j in range(52))
    assert all(g[i][j] == g[reflect[i]][reflect[j]] for i in range(52) for j in range(52))
    assert all(sign(w, groups[j][0]) == sign(w, groups[reflect[j]][0])
               for w in anchor for j in range(52))
    m0, m1 = [sum(masks[j] for j in part) for part in sides]
    assert m0.bit_count() == m1.bit_count() == SECTOR
    kept = sorted(col for side in sides for col in [r for j in side for r in groups[j]][:300])
    assert verify_orthogonal(2396, assemble(599, source, kept, anchor)) == 721801
    sites = [side[i] for side in sides for i in range(16) if side[i] < reflect[side[i]]]
    assert len(sites) == 16 and set(sides[0] + sides[1]) == set(sites) | {reflect[j] for j in sites}
    paired = [masks[j] | masks[reflect[j]] for j in sites]
    low = [i for i in range(52) if i < reflect[i]]
    fixed = [i for i in range(52) if i == reflect[i]]
    odd = [[(g[i][j]-g[reflect[i]][j])//2 for j in sites] for i in low]
    even = [[g[i][j]+g[reflect[i]][j] for j in sites] for i in low]
    even.extend([g[i][j] for j in sites] for i in fixed)
    assert all((g[i][j]-g[reflect[i]][j]) % 2 == 0 for i in low for j in sites)
    return source, rows, groups, masks, order, g, anchor, decks, sides, (m0,m1), sites, paired, low, fixed, reflect, odd, even


def max_affordable(budget, items):
    count = 0
    for x in sorted(items):
        if x > budget:
            break
        budget -= x
        count += 1
    return count


def census(bundle):
    source, rows, groups, masks, order, g, anchor, decks, sides, sectors, sites, paired, *_ = bundle
    batches = [
        [[[sum(abs(g[i][k] + e*g[j][k]) for k in side) for j in range(52)]
          for i in range(52)] for e in (1,-1)] for side in sides
    ]
    ordinary = 0
    counts = Counter()
    symmetric = []
    exceptional = {}
    words = [masks[j] for side in sides for j in side]
    max_corr = 0
    total = 0
    for r, s in combinations(range(N), 2):
        u, v = rows[r], rows[s]
        i, j = order[r], order[s]
        change = u ^ v
        corr = [SECTOR-2*(change & m).bit_count() for m in sectors]
        max_corr = max(max_corr,abs(sum(corr)))
        for k,e in enumerate((1,-1)):
            if i == j and e == -1:
                continue
            total += 1
            cuts = [SECTOR + e*corr[t] - batches[t][k][i][j] for t in (0,1)]
            assert all(x % 4 == 0 for x in cuts)
            base = [x//4 for x in cuts]
            if max(base) > LIMIT:
                continue
            ordinary += 1
            w = v if e == 1 else v ^ MASK
            both_plus = u & w
            both_minus = MASK ^ (u | w)
            capacities = tuple(((both_plus & m).bit_count(),(both_minus & m).bit_count()) for m in words)
            assert sum(min(a,b) for a,b in capacities[:16]) == base[0]
            assert sum(min(a,b) for a,b in capacities[16:]) == base[1]
            bad = [max_affordable(LIMIT-base[t], [SIZE-a-b for a,b in capacities[16*t:16*t+16]])
                   for t in (0,1)]
            if max(bad) > 2:
                counts[tuple(bad)] += 1
                exceptional.setdefault((i,j,e,capacities),(r,s,e))
            physical = [((both_plus & m).bit_count(),(both_minus & m).bit_count()) for m in paired]
            cost = [sum(min(a,b) for a,b in physical[8*t:8*t+8]) for t in (0,1)]
            if max(cost) <= LIMIT:
                poor = [max_affordable(LIMIT-cost[t],[2*SIZE-a-b for a,b in physical[8*t:8*t+8]])
                        for t in (0,1)]
                symmetric.append((r,s,e,max(poor)))
    print('census',total,'ordinary',ordinary,'symmetric',len(symmetric),
          'exceptional',sum(counts.values()),'unique',len(exceptional),'max restricted correlation',max_corr,
          'max symmetric poor pairs',max(z[3] for z in symmetric),flush=True)
    print('defect histogram',sorted(counts.items()),flush=True)
    assert total == 1416064
    assert (736+max_corr)//2 < 598
    return symmetric, exceptional


def loss(v, a, b):
    return 23 - ((23-a-b if abs(v)==2 else 0)
                   +(a if abs(v-4)==2 else 0)
                   +(b if abs(v+4)==2 else 0))


def pair_loss(left, right, p):
    if abs(p) >= 4:
        return 23 + min(*(loss(v, *left) for v in (-6,-2,2,6)),
                        *(loss(v, *right) for v in (-6,-2,2,6)))
    values = {v-2*p for v in (-6,-2,2,6)} | {v+2*p for v in (-6,-2,2,6)}
    return min(loss(v+2*p, *left)+loss(v-2*p, *right) for v in values)


def worker_input(bundle, exceptional):
    *_, sides, sectors, sites, paired, low, fixed, reflect, odd, even = bundle
    col_order = [j for side in sides for j in side]
    pairs = [(col_order.index(j),col_order.index(reflect[j])) for j in sites]
    costs = [[[pair_loss(c[i],c[j],p) for p in range(-4,5)] for i,j in pairs]
             for _,_,_,c in exceptional]
    all_max = []
    for threshold in (1,2,3):
        bounds = []
        for w in costs:
            base = [min(row) for row in w]
            more = [min(v for i,v in enumerate(row) if abs(i-4)>threshold)-b for row,b in zip(w,base)]
            bound = [max_affordable(LIMIT-sum(base[8*t:8*t+8]),more[8*t:8*t+8]) for t in (0,1)]
            bounds.append(bound)
        all_max.append((max(max(a) for a in bounds),max(sum(a) for a in bounds)))
    print('odd thresholds side/total',all_max,flush=True)
    assert all_max == [(4,8),(2,3),(1,2)]
    def format_rows(rows):
        return ''.join(' '.join(map(str,row))+'\n' for row in rows)

    return (format_rows([*odd,[len(costs)],*(row for matrix in costs for row in matrix)]),
            format_rows([*odd,*even]))


def replay_symmetric(bundle,symmetric,output):
    source,rows,groups,masks,order,g,anchor,decks,sides,sectors,sites,paired,low,fixed,reflect,odd,even = bundle
    assert max(z[3] for z in symmetric) <= 2
    x,y=anchor
    e=[c for side in sides for j in side for c in groups[j]]
    phase=[decks[0][j]//2 for j in e]
    raw_part=(MASK ^ x ^ y,x^y)
    words=set()
    assert output.splitlines()[-1] == 'final visits 260471 valid 16'
    for line in output.splitlines():
        bits=line.split()
        if bits[0]!='hit':
            continue
        a,b=map(int,bits[1:3])
        q=[0]*52
        vals=[2*(n >> k & 1)-1 for n in (a,b) for k in range(14)]
        for i,v in zip(low,vals[:24]):q[i]=q[reflect[i]]=v
        for i,v in zip(fixed,vals[24:]):q[i]=v
        z=raw_word(q,groups)
        words.add(z)
    closest=0
    counted=0
    for z in words:
        if z in (x,y,MASK^x,MASK^y):
            continue
        for r,s,phi,_ in symmetric:
            zr,zs=sign(z,r),sign(z,s)
            if zr*zs!=phi:
                continue
            edited=z ^ (1<<r) ^ (1<<s)
            h=[((edited^x)&p).bit_count() for p in raw_part]
            if not all(k%2 for k in h):
                continue
            counted+=1
            columns=[[],[]]
            for i,col in enumerate(e):
                p=phase[i]*dot(edited,source[col])
                if abs(p)==2:columns[i//368].append(p)
            found=sum(min(c.count(2),(k+1)//2)+min(c.count(-2),(599-k)//2)
                      for c,k in zip(columns,h))
            closest=max(closest,found)
            assert found<600
    assert (len(words),counted,closest)==(4,9424,276)
    print('symmetric raw lines',len(words),'phase-parity cases',counted,'best capacity',closest,flush=True)


def verify():
    with TemporaryDirectory() as temp:
        odd_worker = Path(temp) / 'odd'
        symmetric_worker = Path(temp) / 'symmetric'
        for program,exe,options in [('r_paley_double_far_twoflip_odd.cpp',odd_worker,['-mavx2']),
                                    ('r_paley_double_far_twoflip_even.cpp',symmetric_worker,[])]:
            subprocess.run(['g++','-O3','-std=c++17',*options,str(DIR/program),'-o',str(exe)],check=True)
        for pivots,profile_count in [((32,19),380),((45,6),852)]:
            print('pivot pair',*pivots,flush=True)
            family=data(pivots)
            symmetric,exceptional=census(family)
            assert len(exceptional)==profile_count
            odd_in,symmetric_in=worker_input(family,exceptional)
            odd_run=subprocess.run([str(odd_worker)],input=odd_in,text=True,check=True,stdout=subprocess.PIPE)
            assert odd_run.stdout.strip()=='complete 187046447 26 0'
            print('odd MITM',odd_run.stdout.strip(),flush=True)
            sym_run=subprocess.run([str(symmetric_worker)],input=symmetric_in,text=True,check=True,stdout=subprocess.PIPE)
            replay_symmetric(family,symmetric,sym_run.stdout)


def main():
    if len(sys.argv)==1:
        verify()
        return
    pivots=tuple(map(int,sys.argv[1:3]))
    tag=f'{pivots[0]}-{pivots[1]}'
    out=DIR/f'hadamard599-round34-twoflip-{tag}'
    family=data(pivots)
    if len(sys.argv)>3 and sys.argv[3]=='replay':
        symmetric=json.loads((out.with_suffix('.sym.json')).read_text())
        replay_symmetric(family,symmetric,out.with_suffix('.sym.log').read_text())
        return
    symmetric,exceptional=census(family)
    odd_in,sym_in=worker_input(family,exceptional)
    out.with_suffix('.odd.in').write_text(odd_in)
    out.with_suffix('.sym.in').write_text(sym_in)
    out.with_suffix('.sym.json').write_text(json.dumps(symmetric)+'\n')


if __name__=='__main__':main()
