import time, sys
from itertools import combinations
from pysat.solvers import Cadical195
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

def test_3part_cadical(m0, m1, m5, max_e01, max_e05, max_e15, max_tot):
    vpool = IDPool()
    ng0 = {(u,v): vpool.id(f"ng0_{u}_{v}") for u,v in combinations(range(8), 2)}
    ng1 = {(u,v): vpool.id(f"ng1_{u}_{v}") for u,v in combinations(range(6), 2)}
    ng5 = {(u,v): vpool.id(f"ng5_{u}_{v}") for u,v in combinations(range(5), 2)}
    e01 = {(u,w): vpool.id(f"e01_{u}_{w}") for u in range(8) for w in range(6)}
    e05 = {(u,z): vpool.id(f"e05_{u}_{z}") for u in range(8) for z in range(5)}
    e15 = {(w,z): vpool.id(f"e15_{w}_{z}") for w in range(6) for z in range(5)}

    clauses = []
    def add_card(lits, bound, kind="atmost"):
        if kind == "atmost":
            cnf = CardEnc.atmost(lits=lits, bound=bound, vpool=vpool, encoding=EncType.totalizer)
        elif kind == "equals":
            cnf = CardEnc.equals(lits=lits, bound=bound, vpool=vpool, encoding=EncType.totalizer)
        clauses.extend(cnf.clauses)

    add_card(list(ng0.values()), m0, "equals")
    add_card(list(ng1.values()), m1, "equals")
    add_card(list(ng5.values()), m5, "equals")
    add_card(list(e01.values()), max_e01, "atmost")
    add_card(list(e05.values()), max_e05, "atmost")
    add_card(list(e15.values()), max_e15, "atmost")
    add_card(list(e01.values()) + list(e05.values()) + list(e15.values()), max_tot, "atmost")

    # Max-6-Cut & deletion bound on A0
    for u in range(8):
        nb0 = [ng0[(min(u,v), max(u,v))] for v in range(8) if v != u]
        add_card(nb0, m0 - 5, "atmost")
        add_card([e01[(u,w)] for w in range(6)] + nb0, 6, "atmost")
        add_card([e05[(u,z)] for z in range(5)] + nb0, 5, "atmost")
        add_card([e01[(u,w)] for w in range(6)], 1 + m1, "atmost")
    for w in range(6):
        nb1 = [ng1[(min(w,v), max(w,v))] for v in range(6) if v != w]
        add_card([e01[(u,w)] for u in range(8)] + nb1, 8, "atmost")
        add_card([e15[(w,z)] for z in range(5)] + nb1, 5, "atmost")
        add_card([e01[(u,w)] for u in range(8)], 3 + (m0 - 10), "atmost")
    for z in range(5):
        nb5 = [ng5[(min(z,v), max(z,v))] for v in range(5) if v != z]
        add_card([e05[(u,z)] for u in range(8)] + nb5, 8, "atmost")
        add_card([e15[(w,z)] for w in range(6)] + nb5, 6, "atmost")

    # No G1-independent 4-set {u,v in A0 (non-edge), w in A1, z in A5}
    for u, v in combinations(range(8), 2):
        for w in range(6):
            for z in range(5):
                clauses.append([-ng0[(u,v)], e01[(u,w)], e01[(v,w)], e05[(u,z)], e05[(v,z)], e15[(w,z)]])

    # No G1-independent 4-set {u in A0, w1,w2 in A1 (non-edge), z in A5}
    for w1, w2 in combinations(range(6), 2):
        for u in range(8):
            for z in range(5):
                clauses.append([-ng1[(w1,w2)], e01[(u,w1)], e01[(u,w2)], e05[(u,z)], e15[(w1,z)], e15[(w2,z)]])

    t0 = time.time()
    with Cadical195(bootstrap_with=clauses) as s:
        res = s.solve()
        dt = time.time() - t0
        if res:
            mset = set(l for l in s.get_model() if l > 0)
            c01 = sum(1 for v in e01.values() if v in mset)
            c05 = sum(1 for v in e05.values() if v in mset)
            c15 = sum(1 for v in e15.values() if v in mset)
            print(f"3-part m=({m0},{m1},{m5}) caps=({max_e01},{max_e05},{max_e15},tot={max_tot}): SAT in {dt:.3f}s -> E01={c01}, E05={c05}, E15={c15}", flush=True)
        else:
            print(f"3-part m=({m0},{m1},{m5}) caps=({max_e01},{max_e05},{max_e15},tot={max_tot}): UNSAT in {dt:.3f}s (clauses={len(clauses)})", flush=True)

if __name__ == "__main__":
    print("=== CaDiCaL195 3-PART VERTEX-LEVEL PROBE (#7) ===", flush=True)
    test_3part_cadical(10, 4, 0, 11, 7, 9, 27)
    test_3part_cadical(10, 4, 0, 16, 10, 10, 27)
    test_3part_cadical(10, 5, 0, 16, 10, 11, 28)
    test_3part_cadical(12, 3, 0, 16, 12, 9, 28)
    test_3part_cadical(13, 2, 0, 16, 13, 8, 28)
