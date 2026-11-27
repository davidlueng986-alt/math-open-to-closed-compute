#!/usr/bin/env python3
"""Exact orbit classification of the 3x3 bipartite skeleton G[X,Y] for D9-C6 (c=6, 1 <= e(X,Y) <= 9).

In D9-C6: |S|=6, |X|=3, |Y|=3, |T|=26, e(T) = 72 + e(X,Y).
Since e(3,8,26) = 73 (Goedgebeur & Radziszowski 2013), e(X,Y) in [1, 9] is exhaustive.
Under S_3(X) x S_3(Y) x Z_2(swap X <-> Y) (order 72), all 2^9 - 1 = 511 nonempty 3x3
bipartite graphs partition into exactly 25 isomorphism classes.
"""
import argparse, itertools, json

PERMS = list(itertools.permutations(range(3)))

def canon_3x3(mask: int) -> int:
    best = 1 << 9
    for px in PERMS:
        for py in PERMS:
            for sw in (0, 1):
                m = 0
                for i in range(3):
                    for j in range(3):
                        if (mask >> (3 * i + j)) & 1:
                            ni, nj = (py[j], px[i]) if sw else (px[i], py[j])
                            m |= 1 << (3 * ni + nj)
                if m < best:
                    best = m
    return best

def enumerate_d9c6_skeletons():
    orbits = {}
    for mask in range(1, 1 << 9):
        c = canon_3x3(mask)
        orbits[c] = orbits.get(c, 0) + 1
    assert sum(orbits.values()) == 511
    assert len(orbits) == 25
    records = []
    for idx, (mask, size) in enumerate(sorted(orbits.items(), key=lambda kv: (kv[0].bit_count(), kv[0]))):
        e_xy = mask.bit_count()
        adj_x = [(mask >> (3 * i)) & 7 for i in range(3)]
        adj_y = [sum(((mask >> (3 * i + j)) & 1) << i for i in range(3)) for j in range(3)]
        deg_t_x = [8 - m.bit_count() for m in adj_x]
        deg_t_y = [8 - m.bit_count() for m in adj_y]
        cap_xx = {f"{i},{j}": 5 - (adj_x[i] & adj_x[j]).bit_count() for i in range(3) for j in range(i + 1, 3)}
        cap_yy = {f"{i},{j}": 5 - (adj_y[i] & adj_y[j]).bit_count() for i in range(3) for j in range(i + 1, 3)}
        records.append({
            'id': f'D9-C6-S{idx:02d}',
            'mask': mask,
            'e_xy': e_xy,
            'e_T': 72 + e_xy,
            'orbit_size': size,
            'deg_T_X': deg_t_x,
            'deg_T_Y': deg_t_y,
            'cap_T_XX': cap_xx,
            'cap_T_YY': cap_yy,
            'forces_full_S_domination': (e_xy == 9),
        })
    return records

def selftest():
    recs = enumerate_d9c6_skeletons()
    assert len(recs) == 25
    assert sum(r['orbit_size'] for r in recs) == 511
    assert recs[0]['e_xy'] == 1 and recs[0]['e_T'] == 73
    assert recs[-1]['e_xy'] == 9 and recs[-1]['e_T'] == 81 and recs[-1]['forces_full_S_domination']
    print(f"PASS: D9-C6 exact 3x3 skeleton classification verified (25 orbits covering all 511 graphs)", flush=True)

if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--selftest', action='store_true')
    p.add_argument('--dump', action='store_true')
    a = p.parse_args()
    if a.selftest:
        selftest()
    elif a.dump:
        print(json.dumps(enumerate_d9c6_skeletons(), indent=2))
    else:
        selftest()
