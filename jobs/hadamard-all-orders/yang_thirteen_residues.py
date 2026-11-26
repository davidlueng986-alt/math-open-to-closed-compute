"""Exact branch and bound for maximum number of ruled-out Yang widths."""

from collections import Counter, defaultdict
from functools import reduce
from itertools import product
from math import gcd, isqrt, lcm, prod
from operator import or_

from t187_yang import yang_selectors
from t599_length_change import GOLAY_26, aperiodic
from verify import signs
from yang_four_residues import FIRST, STEP


BASES = {
    47: ("+++-----+--++--+++--++-+", "++++---++-+--+-+-+---+--",
         "++++-++-+-++++--+-+++-+", "+++--------+-++--++-+-+"),
    53: ("++++-++--+-+++++-+---++---+", "++++-++--+-+++++-+---++----",
         "+++--+++-+--+-+-+--++-++++", "+++--+++-+--+-+-+--++-++++"),
    59: ("++++-++++-+--++--++++-+---+-++", "++++-++++-+--++--++++-+---+-+-",
         "+++-+---+-++---+--++++-++++--", "+-++++-++++--+---++-+---+-++-"),
    71: ("+++-+-+--+----+-++--++-+-++++--++++-", "--+-+-+----+++++--++-++-++-++--+++--",
         "+++--++++++--+---++-+++++-+-++++-+-", "------+++-++-+--+---+++-+++-+-+++-+"),
}
PRIMES = (13, 17, 19, 23, 29, 31, 37, 41, 43)


def verify_construction_inputs():
    for width, base in BASES.items():
        words = tuple(map(signs, base))
        assert sum(map(len, words)) == 2*width
        assert aperiodic(words) == [2*width] + [0]*(width//2)
    assert aperiodic(((1, 1), (1, -1))) == [4, 0]
    assert aperiodic(tuple(map(signs, ("+--+-+++++", "+-+---++--")))) == [20] + [0]*9
    assert aperiodic(GOLAY_26) == [52] + [0]*25
    selectors = yang_selectors(BASES[59], GOLAY_26)
    assert len(selectors) == 3_127
    print("T(3127) Golay/Yang control: all 3126 nonzero lags exact")


def candidate_widths():
    modulus = 4*STEP
    target = 4*FIRST
    widths = set()
    for base, a, b, c in product(BASES, range(11), range(3), range(3)):
        width = base*(1+2**(a+1)*10**b*26**c)
        if gcd(width, modulus) != 1 or any(width % p == 0 for p in PRIMES):
            continue
        q = (target*pow(width, -1, modulus)-1)%modulus
        if gcd(q, modulus) == 1:
            assert q % 8 == 3
            widths.add(width)
    return widths


def local_classes(widths, prime):
    classes = defaultdict(int)
    for index, width in enumerate(widths):
        classes[width % prime] |= 1 << index
    return list(classes.values())


def exact_maximum(widths, primes):
    tables = [local_classes(widths, p) for p in primes]
    tables.sort(key=lambda table: -max(mask.bit_count() for mask in table))
    best = 0
    nodes = 0
    witnesses = []

    def walk(depth, union, chosen):
        nonlocal best, nodes, witnesses
        nodes += 1
        score = union.bit_count()
        if score > best:
            best, witnesses = score, chosen
        if depth == len(tables):
            return
        marginal = sum(max((mask & ~union).bit_count() for mask in table)
                       for table in tables[depth:])
        if score + marginal <= best:
            return
        choices = sorted(tables[depth], key=lambda mask: -(mask & ~union).bit_count())
        seen = set()
        for mask in choices:
            new = union | mask
            if new in seen:
                continue
            seen.add(new)
            walk(depth+1, new, chosen+[mask])

    walk(0, 0, [])
    return best, nodes, witnesses


def verify():
    verify_construction_inputs()
    widths = sorted(candidate_widths())
    best, nodes, witness = exact_maximum(widths, PRIMES)
    assert len(widths) == 56 and best == 43 and reduce(or_, witness, 0).bit_count() == 43
    further = (67,73,79,109)
    primes = PRIMES + further
    maxima = []
    for p in further:
        counts = Counter(r%p for r in widths)
        assert 0 not in counts
        maxima.append(max(counts.values()))
    assert maxima == [3,4,3,2] and best + sum(maxima) == 55
    assert all(r%113 not in (0,8) for r in widths)
    assert (16*2+1)%113 == 33 and all(a*a%113 != 33 for a in range(113))
    total = prod(primes)
    assert total == 238_527_628_758_402_157_213

    primary = (3,5,7,11,479)
    assert 4*STEP == 2**4 * 3 * 5 * 7 * 11**2 * 479
    assert len(set(primes + (113,))) == 14
    assert all(gcd(prime, 4*STEP) == 1 for prime in primes + (113,))
    assert all(all(prime % d for d in range(2, isqrt(prime) + 1))
               for prime in primary + primes + (113,))
    all_primes = primary + primes + (113,)
    period = lcm(*(p-1 for p in all_primes))
    assert period == 516_756_240
    assert all(pow(2,period,p)==1 for p in all_primes)
    print(f"exact width union bound {best}/56 in {nodes} nodes, "
          f"covering {total} thirteen-prime residue prescriptions")


if __name__ == '__main__':
    verify()
