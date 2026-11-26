"""Examine every possible repeated reserve with the twelve fixed inner columns."""
from collections import defaultdict,Counter
from itertools import combinations
from r_paley_full92_contrast import (
    AGREE, OPPOSITE, PAIR_FIBRES, PAIR_INDICES, WHOLE_FIBRES,
    centre_column, local_index,
)
from r_paley_full92_skew import build_source,frame
from verify import rows_from_columns
S=build_source();R0,P0=frame()
R=[R0[i]for i in AGREE+OPPOSITE];P=[P0[i]for i in AGREE+OPPOSITE]
rr=set(R)
G=defaultdict(list)
for j in set(range(1196))-set(P):
    G[centre_column(S,R,j)].append(j)
profiles=defaultdict(list)
for r in set(range(1196))-rr:
    profile=sum((1^((S[P[0]]>>r)^(S[P[0]]>>R[0])^(S[g]>>r)^(S[g]>>s))&1)<<i
                for i,(s,g) in enumerate(zip(R,P,strict=True)))
    profiles[profile].append(r)
W=rows_from_columns(1196,S)
old_pairs=[W[a]^W[b]for a,b in combinations(R,2)]
full=(1<<1196)-1

def check(r,s,g):
    if ((W[r]^W[s])>>g)&1:
        sector=(W[r]^W[s])^full
    else:
        sector=W[r]^W[s]
    assert sector.bit_count()==598
    if any(sector>>h&1 for h in P):return 0
    if any(abs(598-2*(sector&c).bit_count())>2 for c in old_pairs):return 1
    return 2

c=Counter()
survivors=[]
for v,rs in profiles.items():
    for r,s in combinations(rs,2):
        if not G[v]:continue
        c['new row pair']+=1
        g=G[v]
        ans=Counter(check(r,s,h)for h in g)
        c.update(('new status',i)for i in ans.elements())
        if ans[2]: survivors.append(('new',r,s,ans[2]))
for i,s in enumerate(R):
    for r in set(range(1196))-rr:
        q=check(r,s,P[i])
        c['old row pair']+=1
        c['old status',q]+=1
        if q==2:survivors.append(('old',r,s,P[i]))

assert c == Counter({
    'old row pair': 14208, 'new row pair': 1406,
    ('old status', 0): 14199, ('old status', 1): 9,
    ('new status', 0): 4972, ('new status', 1): 4538,
})
assert not survivors

scale = 100000
weights = (
    -27431, -6625, -11866, 463, 3566, 4635, -1272, -2058, 2078, 1950, 5023,
    9128, 2626, -5235, -1946, 2742, -10207, 1192, 635, 3333, -314, 7304, -6069,
    -1842, 4552, 2097, -7180, 4078, 234, -1445, 8341, -3782, 9327, -8267,
    -3167, 1975, 6457, 3927, -2485, -1549, 623, -2773, 2933, 3694, 2438,
    11030, -6349, -8374, -12781, -2650, -1304, 4968, 6063, -3478, -543,
    -732, 4060, -4976, 41, 3505, 2984, -5498, -3971, 1773, 11846, 8193, -7361,
)
pairs = tuple(combinations(range(12), 2))
assert len(weights) == 1 + len(pairs)
assert sum(len(G[v]) for v in G) == 1184
assert sum(len(rs) for v, rs in profiles.items() if G[v]) == 476
bound = 600 * weights[0]
for profile, columns in G.items():
    capacity = len(columns)
    demand = len(profiles[profile])
    slope = weights[0] + sum(w * (1 - 2 * (((profile >> i) ^ (profile >> j)) & 1))
                             for (i, j), w in zip(pairs, weights[1:], strict=True))
    bound += max(scale * min(demand, capacity - x) - x * slope
                 for x in (0, max(0, capacity - demand), capacity))
assert bound == 36701330 and bound // scale == 367
print("Arbitrary exterior: all reserves distinct, dual bound 36701330/100000, width at most 1579")
original = [local_index(fibre, j) for fibre in WHOLE_FIBRES for j in range(92)]
original.extend(local_index(fibre, j) for pair in PAIR_INDICES
                for group, j in zip(PAIR_FIBRES, pair, strict=True) for fibre in group)
assert len(original) == len(set(original)) == 600 and set(original).isdisjoint(P)
occupied = Counter(centre_column(S, R, j) for j in original)
assert sum(min(len(profiles[v]), len(group) - occupied[v]) for v, group in G.items()) == 236
print("Original projected histogram: all reserves distinct and width at most 1448")
