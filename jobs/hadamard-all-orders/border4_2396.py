"""Verify the width-four construction, its design bridge, and the 2396 multiplier sieve."""

from itertools import combinations, repeat

from verify import goethals_seidel, rows_from_columns, signs, verify_orthogonal


PUBLISHED_668 = (
    "155B13CDEF8E5C05AB2DBD549D86420DCB803565B4",
    "F11284B6FCD2BB559C1F01DDAD692052576AB383E0",
    "F53A7B8376405BBC8F38E158B08F91100B7791E71C",
    "1D67B459F8C0B34ECEE6BC530974C0E01668D9DCD4",
)


def periodic(words):
    size = len(words[0])
    return [sum(value * word[(i + lag) % size] for word in words for i, value in enumerate(word))
            for lag in range(size)]


def pack(word):
    return sum((value == 1) << index for index, value in enumerate(word))


def bordered_columns(words):
    size = len(words[0])
    core_size = 4 * size
    core = goethals_seidel(words)
    sylvester = [[(-1)**((i & j).bit_count() % 2) for j in range(4)] for i in range(4)]
    columns = []
    for i, column in enumerate(core):
        block = i // size
        end = [row[block] * (-1 if block == 0 else 1) for row in sylvester]
        columns.append(column | (pack(end) << core_size))
    for i in range(4):
        top = pack(value for row in sylvester for value in repeat(row[i], size))
        bottom = pack(-1 if j == i else 1 for j in range(4))
        columns.append(top | (bottom << core_size))
    return columns


def verify_design(words):
    size = len(words[0])
    first = tuple(-value for value in words[0])
    p, q, r = words[1:]
    a = (first, p, q, r)
    b = [tuple(sign * table[(-j) % size] for j in range(size))
         for sign, table in ((1, r), (1, q), (-1, p), (-1, first))]
    a_masks = tuple(map(pack, a))
    b_masks = tuple(map(pack, b))
    fixed = (1 << (2 * size), 1 << (2 * size + 1))
    all_points = (1 << size) - 1
    blocks = [all_points | fixed[0], all_points | fixed[1]]
    for a_word, b_word, fixed_mask in zip(a_masks, b_masks, (sum(fixed), *fixed, 0), strict=True):
        for _ in range(size):
            blocks.append(a_word | (b_word << size) | fixed_mask)
            a_word = ((a_word << 1) & all_points) | (a_word >> (size - 1))
            b_word = ((b_word << 1) & all_points) | (b_word >> (size - 1))
    assert len(blocks) == len(set(blocks)) == 4 * size + 2
    assert all(block.bit_count() == size + 1 for block in blocks)
    incidence = rows_from_columns(2 * size + 2, blocks)
    assert all(points.bit_count() == 2 * size + 1 for points in incidence)
    assert all((a_bits & b_bits).bit_count() == size for a_bits, b_bits in combinations(incidence, 2))


def verify_paley_half():
    prime = 599
    squares = {value * value % prime for value in range(1, prime)}
    subgroup_size = len(squares)
    generator = next(x for x in sorted(squares)
                     if pow(x, 13, prime) != 1 and pow(x, 23, prime) != 1)

    def character(value):
        value %= prime
        return 0 if not value else (1 if value in squares else -1)

    abscissae = [pow(generator, i, prime) for i in range(subgroup_size)]
    skew = tuple(character(x - 1) for x in abscissae)
    symmetric = tuple(character(x + 1) for x in abscissae)
    assert tuple(sorted((sum(skew), abs(sum(symmetric))))) == (0, 1)
    assert sum(bool(value) for value in skew) == 298 and all(symmetric)
    assert periodic((skew, symmetric)) == [597] + [-2] * 298
    # Complementary supports leave two full odd-length words and one spike.
    assert (599 - 1) % 8 == 6
    print("width four / 2396: exact Paley S half on Z299, whose complementary support is impossible for T")

    for fill in (-1, 1):
        affine = [0] + [character(1 + x) for x in range(1, prime - 1)] + [fill]
        assert sum(affine) == fill - 1
        multipliers = (squares - {1}) | {prime - 1}
        for r in multipliers:
            correlation = sum(affine[x] * affine[r*x % prime] for x in range(1, prime))
            assert correlation == (2 * fill if r == prime - 1 else -2)
    print("width four / 2396: verified the Paley correlations underlying the common-quotient mask exclusion")


def verify_order_eleven():
    size, quotient, fiber = 598, 26, 23
    diagonal = 4 * size - 4 * (fiber - 1)
    choices = [(n21, n23) for n21 in range(4 * quotient + 1)
               for n23 in range(4 * quotient + 1 - n21)
               if 4 * quotient + 440 * n21 + 528 * n23 == diagonal]
    assert choices == [(5, 0)]
    spikes = choices[0][0]
    # If the spike correlation is nonzero, neither sign can reach -4*fiber.
    error_bound = 4 * quotient + 40 * spikes
    assert -400 + error_bound < -4 * fiber < 400 - error_bound
    assert 4 * ((quotient + 2) // 20)**2 < spikes
    print("width four / 2396: order-11 multiplier excluded by the five-spike compression")


def verify():
    small = tuple(map(signs, ("++", "+-", "+-", "+-")))
    published = tuple(tuple(1 if bit == "0" else -1
                            for bit in f"{int(word, 16):0168b}"[:166])
                      for word in PUBLISHED_668)
    for words in (small, published):
        size = len(words[0])
        assert tuple(map(sum, words)) == (2, 0, 0, 0)
        assert periodic(words) == [4 * size] + [-4] * (size - 1)
        order = 4 * size + 4
        pair_count = verify_orthogonal(order, bordered_columns(words))
        verify_design(words)
        print(f"width four / {order}: verified {pair_count} column pairs and the cyclic outer design")
    verify_paley_half()
    verify_order_eleven()


if __name__ == "__main__":
    verify()
