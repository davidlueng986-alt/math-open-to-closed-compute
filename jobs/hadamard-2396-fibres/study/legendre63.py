"""Try all margin-preserving single rectangles at each step of a 63-point descent."""
import itertools
import json

import numpy as np

from legendre_margins import autocorrelation, certificate, compress, zero_one_matrix

Q = 63
HALF = 32
TARGET = np.array([2358] + [-38]*(HALF-1), dtype=np.int32)


def residual(rows):
    plain = rows.tolist()
    return np.array([autocorrelation(plain, s) for s in range(HALF)]) - TARGET


def energy(v):
    return v[..., 0]**2 + 2*np.sum(v[..., 1:]**2, axis=-1)


def direct_half(row):
    ordinary = np.correlate(row, row, mode="full")
    half = ordinary[Q-1:Q-1+HALF].copy()
    half[1:] += ordinary[:HALF-1]
    return half


def rectangles():
    where = {(i % 9, i % 7): i for i in range(Q)}
    corners = [(where[i,j], where[k,l], where[k,j], where[i,l])
               for i,k in itertools.combinations(range(9), 2)
               for j,l in itertools.combinations(range(7), 2)]
    result = np.zeros((len(corners), Q), dtype=np.int32)
    for index, points in enumerate(corners):
        result[index, list(points)] = [2, 2, -2, -2]
    return np.concatenate([result, -result])


def descent():
    initial = certificate()
    start = [[1-2*((int(word,16) >> j) & 1) for j in range(1197)]
             for word in initial["negative_bit_masks_hex"]]
    rows = np.array([compress(row, Q) for row in start], dtype=np.int32)
    moves = rectangles()
    products = np.stack([(moves*np.roll(moves, s, axis=1)).sum(axis=1)
                         for s in range(HALF)], axis=1)
    path = []
    while True:
        ph = residual(rows)
        cost = int(energy(ph))
        path.append(cost)
        best, chosen = cost, None
        admissible, ties = 0, 0
        for f, row in enumerate(rows):
            neighbors = np.stack([np.roll(row, s)+np.roll(row, -s) for s in range(HALF)], axis=1)
            scores = energy(ph + moves @ neighbors + products)
            bounded = np.max(np.abs(row + moves), axis=1) <= 19
            admissible += int(np.count_nonzero(bounded))
            ties += int(np.count_nonzero(bounded & (scores == cost)))
            scores[~bounded] = np.iinfo(scores.dtype).max
            i = int(np.argmin(scores))
            if scores[i] < best:
                best, chosen = int(scores[i]), (f, i)
        if chosen is None:
            break
        f, i = chosen
        rows[f] += moves[i]
        assert int(energy(residual(rows))) == best

    # Recompute every terminal neighbor from its scalar products, independently of the update formula.
    checked = equal = 0
    for f in range(2):
        other = direct_half(rows[1-f])
        for move in moves:
            candidate = rows[f] + move
            if np.max(np.abs(candidate)) <= 19:
                score = int(energy(other + direct_half(candidate) - TARGET))
                assert score >= cost
                equal += int(score == cost)
                checked += 1
    assert (checked, equal) == (admissible, ties)
    signs = []
    for f, row in enumerate(rows):
        nineteen = initial["projections"][19][("first", "second")[f]]
        grid = zero_one_matrix([(19+int(x))//2 for x in row], [(63+x)//2 for x in nineteen])
        signs.append([2*grid[t % Q][t % 19]-1 for t in range(1197)])
        assert np.array_equal(compress(signs[-1], Q), row)
        for q, pair in initial["projections"].items():
            assert compress(signs[-1], q) == pair[("first", "second")[f]]
    full = [autocorrelation(signs, s) for s in range(1, 599)]
    return {"energy_path":path, "rectangles_per_step":2*len(moves), "terminal_bounded_moves":admissible,
            "terminal_tied_moves":ties, "terminal_improving_moves":0, "q63_rows":rows.tolist(),
            "q63_residuals_0_to_31":ph.tolist(), "q63_shift_pairs_satisfied":int(np.count_nonzero(ph[1:]==0)),
            "length_1197_negative_bit_masks_hex":[hex(sum(1 << j for j,v in enumerate(row) if v<0))
                                                  for row in signs],
            "full_shift_pairs_matching_minus_two":full.count(-2), "full_paf_at_one":full[0]}


if __name__ == "__main__":
    print(json.dumps(descent(), indent=2))
