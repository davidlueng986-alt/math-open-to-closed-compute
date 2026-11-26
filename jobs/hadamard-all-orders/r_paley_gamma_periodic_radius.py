"""Verify raw periodic-predecessor distance bounds at the fixed width-1215 exterior."""

from collections import Counter
from fractions import Fraction
from itertools import product
from math import ceil

from r_paley_bucket_extension import SELECTED
from verify import goethals_seidel, length_299_words, verify_orthogonal


HEIGHT, CHOSEN, BLOCK = 1196, 600, 299
DUAL = {
    13: (((3, 26), (5, 13), (7, 13)), Fraction(3185, 512),
         (Fraction(726255174977, 159207840), Fraction(709888242289, 157477320))),
    23: (((1, 46), (5, 46)), Fraction(1927, 512),
         (Fraction(3999814547, 1338480), Fraction(293469749, 94640))),
}


def geometry(source, period):
    length = BLOCK//period
    fibres = [tuple(block*BLOCK+j for j in range(residue, BLOCK, period))
              for block in range(4) for residue in range(period)]
    assert all(len(fibre) == length for fibre in fibres)
    masks = [sum(1 << j for j in fibre) for fibre in fibres]
    counts = [(mask & SELECTED).bit_count() for mask in masks]
    assert sum(counts) == CHOSEN and all(0 < n < length for n in counts)
    signatures = [tuple(2*(column & mask).bit_count()-length for mask in masks)
                  for column in source]
    assert all(all(signatures[j] == signatures[fibre[0]] for j in fibre) for fibre in fibres)
    compressed = [signatures[fibre[0]] for fibre in fibres]
    assert all(value % 2 for row in compressed for value in row)
    return length, counts, compressed


def block_constants(source):
    length, counts, compressed = geometry(source, 1)
    required = []
    for signs in product((-1, 1), repeat=4):
        alpha = [sum(a*b for a,b in zip(row, signs, strict=True)) for row in compressed]
        assert length*sum(value*value for value in alpha) == HEIGHT**2
        required.append(sum(n*max(abs(x)-2, 0)**2 for n,x in zip(counts, alpha, strict=True)))
    minimum = min(required)
    assert minimum == 641760 and ceil(Fraction(minimum, 4*HEIGHT)) == 135
    print('Fixed 1215: all 16 block-constant profiles, raw Hamming distance at least 135')


def maximum_dual_cost(rate, weight, cap, phase, length):
    """Maximize the exact quadratic over the allowed grid for L times |alpha|."""
    cap -= (cap-phase) % 4
    assert cap >= 2*length and phase in (0, 2)
    points = [phase, cap]
    if rate < weight:
        # Above 2L the concave quadratic has its vertex at 2L*w/(w-rate).
        vertex = (2*length*weight)//(weight-rate)
        below = vertex-(vertex-phase) % 4
        points.extend(x for x in (below, below+4) if phase <= x <= cap)
    return max(rate*x*x-weight*max(x-2*length, 0)**2 for x in points)/length**2


def periodic(source, period):
    length, counts, compressed = geometry(source, period)
    histogram, rate, expected = DUAL[period]
    assert all(Counter(map(abs, row)) == dict(histogram) for row in compressed)
    cap = sum(value*count for value,count in histogram)
    smallest, smallest_count = histogram[0]
    thresholds = [(value-previous, sum(count for _,count in histogram[:j]))
                  for j, ((previous,_), (value,_)) in enumerate(zip(histogram, histogram[1:]), 1)]
    weights = [(Fraction(n*length, length-n), count) for n,count in Counter(counts).items()]
    assert len({column.bit_count() % 2 for column in source}) == 1
    fibres = len(counts)
    margins = []
    for phase in (0, 2):
        phase_margins = []
        for distance in range(55):
            quotient, remainder = divmod(distance, fibres)
            balanced = fibres*quotient**2 + remainder*(2*quotient+1)
            # Past this repeat count the cap stays constant and the energy decreases.
            for repeats in range(max(0, distance-smallest_count)+1):
                squared = max(balanced, distance+2*repeats)
                maximum_error = 4*HEIGHT*(distance-Fraction(squared, length))
                minimum_energy = (HEIGHT**2-maximum_error)/length
                weighted_flips = smallest*distance + sum(delta*max(0, distance-before-repeats)
                                                         for delta,before in thresholds)
                numerator_cap = length*cap-2*weighted_flips
                loss = sum(count*maximum_dual_cost(rate, w, numerator_cap, phase, length)
                           for w,count in weights)
                phase_margins.append(rate*minimum_energy-loss-maximum_error)
        margins.append(min(phase_margins))
    assert tuple(margins) == expected and min(margins) > 0
    print(f'Fixed 1215: period {period}, exact rational margins {margins[0]} and {margins[1]}, '
          'raw Hamming distance at least 55')


def verify():
    source = goethals_seidel(length_299_words())
    assert len(source) == HEIGHT and verify_orthogonal(HEIGHT, source) == 714610
    block_constants(source)
    for divisor in (13, 23):
        periodic(source, divisor)


if __name__ == '__main__':
    verify()
