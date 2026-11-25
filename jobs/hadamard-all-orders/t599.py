"""Generate and independently check the first two congruence layers of T(599)."""

from random import Random

from verify import require

LENGTH = 599
HALF = LENGTH // 2
MASK = (1 << LENGTH) - 1


def rotate(word, shift):
    shift %= LENGTH
    return ((word << shift) | (word >> (LENGTH - shift))) & MASK


def solve_binary(equations, free_bits):
    pivots = {}
    for row, rhs in equations:
        while row:
            pivot = row.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = row, rhs
                break
            old_row, old_rhs = pivots[pivot]
            row ^= old_row
            rhs ^= old_rhs
        else:
            if rhs:
                return len(pivots), None

    solution = free_bits
    for pivot in sorted(pivots):
        row, rhs = pivots[pivot]
        if (solution & row).bit_count() % 2 != rhs:
            solution ^= 1 << pivot
    return len(pivots), solution


def support_equations(first_bit):
    for shift in range(1, HALF + 1):
        yield rotate(first_bit, shift) ^ rotate(first_bit, -shift), 1


def phase_equations(supports):
    for shift in range(1, HALF + 1):
        forward = sum(word & rotate(word, shift) for word in supports)
        backward = sum(word & rotate(word, -shift) for word in supports)
        count = forward.bit_count()
        require(count % 2 == 0, f"even support autocorrelation at {shift}")
        yield forward ^ backward, (count // 2) % 2


def generate(seed):
    rng = Random(seed)
    first_bit = rng.getrandbits(LENGTH)
    support_rank, second_bit = solve_binary(support_equations(first_bit), rng.getrandbits(LENGTH))
    require(second_bit is not None, "support system consistency")
    supports = (first_bit & second_bit, first_bit & ~second_bit,
                second_bit & ~first_bit, MASK ^ (first_bit | second_bit))
    phase_rank, negatives = solve_binary(phase_equations(supports), rng.getrandbits(LENGTH))
    return supports, negatives, support_rank, phase_rank


def integer_correlations(supports, negatives):
    # Compute the original signed autocorrelations directly from membership
    # and sign masks, without using either system that generated the witness.
    positive = [word & ~negatives for word in supports]
    negative = [word & negatives for word in supports]
    result = []
    for shift in range(LENGTH):
        total = 0
        for plus, minus in zip(positive, negative, strict=True):
            shifted_plus = rotate(plus, shift)
            shifted_minus = rotate(minus, shift)
            total += (plus & shifted_plus).bit_count() + (minus & shifted_minus).bit_count()
            total -= (plus & shifted_minus).bit_count() + (minus & shifted_plus).bit_count()
        result.append(total)
    return result


def lift_odd_coefficients(supports, negatives):
    colors = [next(i for i, word in enumerate(supports) if word >> r & 1) for r in range(LENGTH)]
    edges = [[(x, (x + shift) % LENGTH) for x in range(LENGTH)
              if colors[x] == colors[(x + shift) % LENGTH]] for shift in range(1, HALF + 1)]
    coefficient = [1 - 2 * (negatives >> r & 1) for r in range(LENGTH)]
    rows = [row for row, _ in phase_equations(supports)]
    odd_support = next(word for word in supports if word.bit_count() % 2)

    def correlations():
        return [sum(coefficient[x] * coefficient[y] for x, y in shift) for shift in edges]

    for exponent in range(2, 12):
        modulus = 1 << exponent
        norm = sum(value * value for value in coefficient)
        target = [(-c // modulus) % 2 for c in correlations()]
        rank, correction = solve_binary(zip(rows, target, strict=True), 0)
        require(rank == HALF and correction is not None, "surjective phase derivative")
        if correction.bit_count() % 2 != ((LENGTH - norm) // (2 * modulus)) % 2:
            correction ^= odd_support
        for r, value in enumerate(coefficient):
            if correction >> r & 1:
                coefficient[r] = value * (1 - modulus) % (4 * modulus)
        require(all(c % (2 * modulus) == 0 for c in correlations()), "higher off-shift congruence")
        require((sum(v*v for v in coefficient) - LENGTH) % (4 * modulus) == 0, "higher norm congruence")


if __name__ == '__main__':
    require(pow(2, 299, LENGTH) == 1 and pow(2, 13, LENGTH) != 1
            and pow(2, 23, LENGTH) != 1, "order of 2 modulo 599")
    supports, negatives, support_rank, phase_rank = generate(599)
    require(support_rank == phase_rank == 299 and negatives is not None, "sample linear ranks")
    require(sum(supports) == MASK and sum(word.bit_count() for word in supports) == LENGTH,
            "one active channel per position")
    correlations = integer_correlations(supports, negatives)
    require(correlations[0] == LENGTH and all(c % 4 == 0 for c in correlations[1:]), "full mod-4 replay")
    mod_eight = sum(c % 8 == 0 for c in correlations[1:HALF + 1])
    exact = sum(c == 0 for c in correlations[1:HALF + 1])
    print(f"T(599): both linear ranks 299; all 598 nonzero shifts vanish modulo 4")
    print(f"T(599): {mod_eight}/{HALF} reflected shift pairs vanish modulo 8, of which {exact} are exact")
    lift_odd_coefficients(supports, negatives)
    print("T(599): odd coefficients lift through modulus 4096 off-shift and 8192 at zero shift")
