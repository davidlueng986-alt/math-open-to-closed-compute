#!/usr/bin/env python3
"""Exact translation/reflection input and nonvacuous completion examples."""
from collections import Counter
from itertools import combinations, product
from pathlib import Path
import hashlib
import json

BASE = Path(__file__).resolve().parent


def add(a, b):
    return tuple((x+y) % 3 for x, y in zip(a, b))


def neg(a):
    return tuple(-x % 3 for x in a)


def cap_check(S):
    S = set(S)
    pairs = 0
    for a, b in combinations(S, 2):
        assert neg(add(a, b)) not in S
        pairs += 1
    return pairs


def main():
    A = {tuple(x) for x in json.loads((BASE/'cap45.json').read_text())['cap45']}
    F = list(product(range(3), repeat=5))
    sum_count = Counter(add(a, b) for a in A for b in A)
    diff_count = Counter(add(a, neg(b)) for a in A for b in A)
    sums = Counter(sum_count[z] for z in F)
    diffs = Counter(diff_count[z] for z in F)
    assert sums == {1: 45, 10: 198}
    assert diffs == {0: 22, 9: 220, 45: 1}
    holes = {z for z in F if not diff_count[z]}
    assert len(holes) == 22
    cap_check(holes)
    full = {(1,)+a for a in A} | {(2,)+neg(a) for a in A} | {(0,)+neg(h) for h in holes}
    assert len(full) == 112
    controls = []
    for size in (112, 109, 108, 107):
        S = full.copy()
        if size < 112:
            removed_a = sorted(x for x in S if x[0] == 1)[:1]
            removed_b = sorted(x for x in S if x[0] == 2)[:2]
            removed_c = sorted(x for x in S if x[0] == 0)[:109-size]
            S.difference_update(removed_a+removed_b+removed_c)
        assert len(S) == size
        controls.append({'size': size, 'layer_sizes': [sum(x[0] == t for x in S) for t in range(3)],
                         'pairs_checked': cap_check(S), 'points': sorted(S)})
    result = {'status': 'EXACT_PASS', 'sum_representation_distribution': dict(sums),
              'difference_representation_distribution': dict(diffs),
              'reflected_holes_form_cap': True, 'reflected_completion_size': 112,
              'positive_controls': controls,
              'input_sha256': hashlib.sha256((BASE/'cap45.json').read_bytes()).hexdigest(),
              'verifier_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    (BASE/'reflection_completion_verification.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'positive_controls'}, indent=2))


if __name__ == '__main__':
    main()
