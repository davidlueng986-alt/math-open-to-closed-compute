"""Exact complete-short-fibre Gram exclusion in the fixed Cooper–Wallis source."""

from itertools import combinations, product

from r_paley_cooper_wallis import T_LEN, W_LEN, build_pair, build_source
from r_paley_isotropic_code import half_projections


def encode(moment):
    # A difference of candidate moments has all coordinates strictly between
    # -256 and 256, so base 256 carries cannot hide a nonzero first digit.
    return sum(x << (8 * i) for i, x in enumerate(moment))


def short_fibres(source, words):
    first, second = (half_projections(source, word) for word in words)
    sectors = []
    for sign in (1, -1):
        fibres = []
        for block, long_phase in product(range(4), range(W_LEN)):
            group = tuple(block * T_LEN * W_LEN + x * W_LEN + long_phase for x in range(T_LEN))
            flags = {abs(first[j]) == 1 and first[j] == sign * second[j] for j in group}
            assert len(flags) == 1
            if True in flags:
                fibres.append(group)
        assert len(fibres) == 27
        sectors.append(fibres)
    return sectors


def moments(source, fibres, block, long_phase):
    rows = tuple(block * T_LEN * W_LEN + x * W_LEN + long_phase for x in range(T_LEN))
    result = []
    for group in fibres:
        signs = tuple(sum((source[j] >> row & 1) << i for i, row in enumerate(rows)) for j in group)
        # Check the source action directly. Each column fibre restricts to all
        # cyclic translates of one row sign mask, with multiplicities.
        mask = (1 << T_LEN) - 1
        first = signs[0]
        assert sorted(signs) == sorted(
            ((first << d) | (first >> (T_LEN - d))) & mask for d in range(T_LEN)
        )
        row0 = sum((source[j] >> rows[0] & 1) << i for i, j in enumerate(group))
        gram = tuple(T_LEN - 2 * (row0 ^ sum((source[j] >> rows[d] & 1) << i
                                           for i, j in enumerate(group))).bit_count()
                     for d in range(1, (T_LEN + 1) // 2))
        assert all(x % 4 == 1 for x in gram)
        result.append(gram)
    return result


def omission_sums(fibres):
    return {sum(values) for values in combinations(map(encode, fibres), 4)}


def verify():
    source = build_source()
    words, _ = build_pair(source)
    sectors = short_fibres(source, words)
    frames = profiles = candidates = 0
    for block, long_phase in product(range(4), range(W_LEN)):
        left, right = (moments(source, fibres, block, long_phase) for fibres in sectors)
        total = tuple(map(sum, zip(*left, *right, strict=True)))
        minimum = []
        maximum = []
        for a, b in zip(zip(*left, strict=True), zip(*right, strict=True), strict=True):
            s, t = sorted(a), sorted(b)
            minimum.append(sum(s[:4]) + sum(t[:4]))
            maximum.append(sum(s[-4:]) + sum(t[-4:]))
        a, b = sorted((omission_sums(left), omission_sums(right)), key=len)
        frames += 1
        for signs in product((-2, 2), repeat=6):
            target = tuple(x - y for x, y in zip(total, signs, strict=True))
            if not all(lo <= x <= hi for x, lo, hi in zip(target, minimum, maximum, strict=True)):
                continue
            u = encode(target)
            profiles += 1
            candidates += len(a)
            assert not any(u - x in b for x in a), (block, long_phase, signs)
    assert frames == 92
    print(f"CW complete short-fibre exclusion: {frames} raw fibres, {profiles} bounded "
          f"lag profiles, {candidates} exact omitted-vector probes, zero hits")


if __name__ == "__main__":
    verify()
