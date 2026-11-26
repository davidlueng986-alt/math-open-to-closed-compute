"""Check the single-lag coefficient formula for every length t = 32k+23."""
from functools import lru_cache

from defect12_mod32_construction import Affine
from defect12_t599_near64 import RUNS_AFTER, TEMPLATES, source_words


COUNTS = (0, 1, 0, 1, -1, 1, 0, 0)
LENGTH = Affine(32, 23)
FIRST_LAG = Affine(0, 1)
AFTER_LAST = Affine(16, 12)


def negative_runs(runs):
    word = length = 0
    for i, run in enumerate(runs):
        if i % 2:
            word |= ((1 << run) - 1) << length
        length += run
    return word, length


@lru_cache(maxsize=None)
def sources(k):
    runs = [run for template, bias, after in zip(TEMPLATES, COUNTS, RUNS_AFTER, strict=True)
            for run in template * (k + bias) + after]
    s, n = negative_runs(runs)
    q, a = negative_runs((16 * k + 11, 2, 16 * k + 9, 1))
    tau, b = negative_runs((16 * k + 12, 16 * k + 11))
    assert n == a == b == LENGTH(k)
    return s, q, tau


def coefficient(k, lag):
    n = LENGTH(k)
    s, q, tau = sources(k)
    all_bits = (1 << n) - 1

    def rotate(word):
        return (word >> lag) | ((word & ((1 << lag) - 1)) << (n - lag))

    eligible = all_bits ^ ((q ^ rotate(q)) | (tau ^ rotate(tau)))
    return 4 * (eligible.bit_count() - 2 * ((s ^ rotate(s)) & eligible).bit_count())


def expected(k, d):
    if d % 4 == 0 and 1 <= d <= 4 * k:
        i = d // 4
        return 64 * (-1)**i * (2 * k + 1 - 2 * i)
    if d % 4 == 2 and 4 * k + 10 <= d <= 8 * k + 6:
        j = (d - 4 * k - 10) // 4
        return 64 * (-1)**(k - 1 + j) * (j + 1)
    if d == 8 * k + 8:
        return 16
    if d % 4 == 2 and 8 * k + 10 <= d <= 12 * k + 6:
        j = (d - 8 * k - 10) // 4
        return 64 * (-1)**(j + 1) * (k - j)
    return 0


def lag_breakpoints():
    """All shifts where an endpoint of a source interval can cross another."""
    location = Affine(0, 0)
    endpoints = {location, LENGTH, Affine(16, 11), Affine(16, 12), Affine(16, 13), Affine(32, 22)}
    for template, bias, after in zip(TEMPLATES, COUNTS, RUNS_AFTER, strict=True):
        weight = sum(template)
        location += Affine(weight, weight * bias)
        endpoints.add(location)
        for run in after:
            location += Affine(0, run)
            endpoints.add(location)
    assert location == LENGTH
    table = {
        FIRST_LAG, AFTER_LAST, Affine(4, 1), Affine(4, 10), Affine(8, 7),
        Affine(8, 8), Affine(8, 9), Affine(8, 10), Affine(12, 7),
    }
    table.update(right - left + wrap for right in endpoints for left in endpoints
                 for wrap in (Affine(0, 0), LENGTH))
    return sorted(table, key=lambda line: (line.a, line.b))


def ceil_divide(value, positive_divisor):
    return -(-value // positive_divisor)


def verify():
    cuts = lag_breakpoints()
    gaps = [right - left for left, right in zip(cuts, cuts[1:])]
    start = max(1, *(ceil_divide(-gap.b, gap.a) for gap in gaps if gap.a > 0))
    assert all(gap.nonnegative_after(start) for gap in gaps)
    assert sources(18) == source_words()
    for k in range(1, start):
        for d in range(1, AFTER_LAST(k)):
            assert coefficient(k, d) == expected(k, d)

    # For fixed k,d mod 8 in each interval between successive cut lines,
    # both quantities are affine in (k,d). Verify both rounded edges at
    # two successive k on each progression on which the strip is nonempty.
    checked = set()
    region = cuts[cuts.index(FIRST_LAG):cuts.index(AFTER_LAST) + 1]
    for left, right in zip(region, region[1:]):
        for k0 in range(start, start + 8):
            for residue in range(8):
                low_shift = (residue - left(k0)) % 8
                high_shift = 1 + (right(k0) - 1 - residue) % 8
                width = right(k0) - high_shift - left(k0) - low_shift
                difference = right.a - left.a
                if width < 0 and difference == 0:
                    continue
                k_first = k0 if width >= 0 else k0 + 8 * ceil_divide(-width, 8 * difference)
                for k in (k_first, k_first + 8):
                    lower = left(k) + low_shift
                    upper = right(k) - high_shift
                    assert 1 <= lower <= upper < AFTER_LAST(k)
                    checked.update(((k, lower), (k, upper)))
    for k, lag in checked:
        assert coefficient(k, lag) == expected(k, lag), (k, lag)
    print(f"t=32k+23, k>=1: exact single-lag mod64 defect at ±(8k+8); {len(checked)} affine edge checks")


if __name__ == "__main__":
    verify()
