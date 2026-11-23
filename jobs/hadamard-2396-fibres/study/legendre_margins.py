"""Construct two order-1197 sign sequences with compatible exact 9-, 7- and 19-point projections."""
import json

LENGTH = 1197


def prime_row(q, mean, contrast):
    # At a primitive character the squared amplitude is (1-q*mean)^2 + q*contrast^2.
    return [1-(q-1)*mean] + [mean + (contrast if pow(j, (q-1)//2, q) == 1 else -contrast)
                              for j in range(1, q)]


def zero_one_matrix(row_degrees, col_degrees):
    remaining = list(col_degrees)
    out = [[0]*len(remaining) for _ in row_degrees]
    for i in sorted(range(len(row_degrees)), key=row_degrees.__getitem__, reverse=True):
        degree = row_degrees[i]
        columns = sorted(range(len(remaining)), key=remaining.__getitem__, reverse=True)
        assert 0 <= degree <= len(columns)
        for j in columns[:degree]:
            assert remaining[j] > 0
            out[i][j] = 1
            remaining[j] -= 1
    assert not any(remaining)
    return out


def realize(margins):
    required = {q: [(LENGTH//q + v)//2 for v in row] for q, row in margins.items()}
    r, c = required[9], required[7]
    total = sum(r)
    assert total == sum(c) == sum(required[19])
    # The fractional matrix r_i/7 + c_j/9 - total/63 has the required margins.
    base = [[(9*x + 7*y - total)//63 for y in c] for x in r]
    row_deficit = [x-sum(row) for x, row in zip(r, base)]
    col_deficit = [c[j]-sum(row[j] for row in base) for j in range(7)]
    correction = zero_one_matrix(row_deficit, col_deficit)
    pairs = [base[i][j]+correction[i][j] for i in range(9) for j in range(7)]
    occupancy = zero_one_matrix(pairs, required[19])
    # The three moduli are pairwise coprime, so these 1197 cells occur once each.
    return [2*occupancy[7*(t%9)+(t%7)][t%19]-1 for t in range(LENGTH)]


def compress(row, q):
    return [sum(row[j::q]) for j in range(q)]


def autocorrelation(rows, shift):
    return sum(x*row[(i+shift) % len(row)] for row in rows for i, x in enumerate(row))


def certificate():
    nine = [[-17,-5,9,-13,-5,9,19,-5,9], [-17,-3,-3,17,-3,-3,19,-3,-3]]
    seven = [prime_row(7, 2, 13), prime_row(7, 1, 12)]
    nineteen = [prime_row(19, 1, 10), prime_row(19, 0, 3)]
    margins = {9:nine, 7:seven, 19:nineteen}
    signs = [realize({q: pair[i] for q, pair in margins.items()}) for i in range(2)]
    assert all(sum(row) == 1 and set(row) == {-1, 1} for row in signs)
    values = {}
    for q, pair in margins.items():
        assert pair == [compress(row, q) for row in signs]
        paf = [autocorrelation(pair, s) for s in range(q)]
        m = LENGTH//q
        assert paf == [2*(LENGTH+1)-2*m] + [-2*m]*(q-1)
        values[q] = {"first":pair[0], "second":pair[1], "origin":paf[0], "nonzero":paf[1]}
    full = [autocorrelation(signs, s) for s in range(1, (LENGTH+1)//2)]
    # Compression modulo 63 measures what is missing when the 9 and 7 margins are coupled.
    sixty_three = [compress(row, 63) for row in signs]
    joint = [autocorrelation(sixty_three, s) for s in range(1, 32)]
    return {"length": LENGTH, "row_sums":list(map(sum, signs)), "projections":values,
            "nontrivial_fourier_modes_verified":sum(q-1 for q in margins),
            "negative_bit_masks_hex":[hex(sum(1 << i for i,x in enumerate(row) if x < 0)) for row in signs],
            "full_nonzero_shift_pairs":len(full), "full_shift_pairs_matching_minus_two":full.count(-2),
            "full_maximum_absolute_error":max(abs(x+2) for x in full), "full_paf_at_one":full[0],
            "q63_shift_pairs_matching_minus_38":joint.count(-38), "q63_paf_at_one":joint[0]}


if __name__ == "__main__":
    print(json.dumps(certificate(), indent=2))
