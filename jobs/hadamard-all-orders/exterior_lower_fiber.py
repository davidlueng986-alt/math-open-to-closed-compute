"""Invert indexed modulo-eight signatures of the fixed five-column lower profile."""

from collections import Counter, defaultdict
from hashlib import sha256

from five_column_gram import MOD8_LOWER_ROWS, gram_fixture
from five_column_constraints import (
    BOTTOM, LOWER_OMISSIONS, WIDTH, correlations, positive_columns, require, rows_from_columns,
)


def binary_echelon(equations):
    """Reduce packed binary equations, returning None for an inconsistent RHS."""
    pivots = {}
    for coefficients, target in equations:
        while coefficients:
            leading = coefficients.bit_length() - 1
            if leading not in pivots:
                pivots[leading] = (coefficients, target)
                break
            row, value = pivots[leading]
            coefficients ^= row
            target ^= value
        else:
            if target:
                return None
    return pivots


class LowerFiber:
    """Binary equations in one coordinate per allowed replacement of a reference row."""

    def __init__(self, lower, reference_rows):
        self.lower = lower
        self.reference_rows = list(reference_rows)
        self.omitted_patterns = rows_from_columns(BOTTOM, [lower[j] for j in LOWER_OMISSIONS])
        self.profile = Counter(zip(self.omitted_patterns, self.reference_rows, strict=True))
        self.reference_dots = correlations(lower, positive_columns(self.reference_rows), BOTTOM)
        choices = defaultdict(list)
        for omitted, mask in self.profile:
            choices[omitted].append(mask)

        count_rows = defaultdict(int)
        bit_rows = []
        self.replacements = []
        for row, (omitted, current) in enumerate(zip(self.omitted_patterns, self.reference_rows, strict=True)):
            replacements = [0] * WIDTH
            for alternative in choices[omitted]:
                if alternative == current:
                    continue
                variable = 1 << len(self.replacements)
                self.replacements.append((row, alternative))
                count_rows[omitted, current] ^= variable
                count_rows[omitted, alternative] ^= variable
                for j in range(WIDTH):
                    if (current ^ alternative) >> j & 1:
                        replacements[j] ^= variable
            bit_rows.append(replacements)

        self.count_equations = [(value, 0) for value in count_rows.values()]
        self.dot_rows = []
        for old in lower:
            coefficients = [0] * WIDTH
            for row, replacements in enumerate(bit_rows):
                if old >> row & 1:
                    for j in range(WIDTH):
                        coefficients[j] ^= replacements[j]
            self.dot_rows.append(coefficients)

    def equations(self, targets):
        """Build equations for indexed lower dot vectors (sign as in the lower block)."""
        equations = self.count_equations.copy()
        for index, vector in targets.items():
            if not 0 <= index < BOTTOM or len(vector) != WIDTH:
                return None
            differences = [x - y for x, y in zip(vector, self.reference_dots[index], strict=True)]
            if any(value % 4 for value in differences):
                return None
            equations.extend((row, (difference // 4) % 2)
                             for row, difference in zip(self.dot_rows[index], differences, strict=True))
        return equations

    def invert(self, targets):
        """Return the unique grouped placement certified by the supplied signature, if determined."""
        equations = self.equations(targets)
        if equations is None:
            return None
        pivots = binary_echelon(equations)
        if pivots is None or len(pivots) != len(self.replacements):
            return None

        state = 0
        for pivot, (coefficients, target) in sorted(pivots.items()):
            if target ^ ((coefficients & state).bit_count() % 2):
                state |= 1 << pivot
        rows = self.reference_rows.copy()
        for variable, (row, alternative) in enumerate(self.replacements):
            if state >> variable & 1:
                if rows[row] != self.reference_rows[row]:
                    return None
                rows[row] = alternative
        if Counter(zip(self.omitted_patterns, rows, strict=True)) != self.profile:
            return None

        actual = correlations([self.lower[i] for i in targets], positive_columns(rows), BOTTOM)
        return rows if all(
            (x - y) % 8 == 0
            for observed, expected in zip(actual, targets.values(), strict=True)
            for x, y in zip(observed, expected, strict=True)
        ) else None


def information_sets():
    """Select six disjoint subsets of retained lower column indices."""
    half = BOTTOM // 2
    bases = sorted(
        (i for i in range(half) if i not in LOWER_OMISSIONS and i + half not in LOWER_OMISSIONS),
        key=lambda i: sha256(f"0:{i}".encode()).digest(),
    )
    return [[i + shift for i in bases[part::3]] for shift in (0, half) for part in range(3)]


def check_paley_distance(lower):
    """Check the code and symmetry hypotheses for the duplicated distance bound."""
    half = BOTTOM // 2
    prime = half - 1
    mask = (1 << half) - 1
    for first, second in zip(lower[:half], lower[half:], strict=True):
        require(first >> half == first & mask and second == first ^ (mask << half),
                "two Sylvester copies")
    paley_rows = rows_from_columns(half, lower[:half])
    require(paley_rows[0] == 0 and all(row & 1 == 0 for row in paley_rows),
            "zero infinite coordinate of all Paley rows")
    generators = paley_rows + [mask]
    require(all(row.bit_count() % 4 == 0 for row in generators)
            and all((row & other).bit_count() % 2 == 0
                    for row in generators for other in generators), "doubly even Paley code")

    finite = [row >> 1 for row in paley_rows[1:]]
    finite_mask = (1 << prime) - 1
    require(all(((row << 1) & finite_mask) | (row >> (prime - 1)) == finite[(i + 1) % prime]
                for i, row in enumerate(finite)), "cyclic translations of finite Paley rows")
    inversion = [1, 0] + [1 + pow(-x, -1, prime) for x in range(1, prime)]
    span = binary_echelon((row, 0) for row in generators)
    require(len(span) == 300, "extended Paley code dimension")
    for row in generators:
        moved = sum(((row >> i) & 1) << j for j, i in enumerate(inversion))
        while moved:
            pivot = moved.bit_length() - 1
            require(pivot in span, "Paley code invariant under inversion")
            moved ^= span[pivot][0]

    # A nonzero codeword can be moved to have a 1 at infinity. The odd
    # punctured word of weight w has a cyclic autocorrelation of all ones.
    # The support lies in zero and at most w(w-1) nonzero differences.
    punctured_weight = next(w for w in range(1, prime + 1) if 1 + w * (w - 1) >= prime)
    extended_weight = ((punctured_weight + 4) // 4) * 4
    require(extended_weight == 28, "Paley minimum distance lower bound")
    return 2 * extended_weight


def main():
    _, lower, _, grouped_rows = gram_fixture()
    reference = [int(symbol, 32) for symbol in MOD8_LOWER_ROWS]
    fiber = LowerFiber(lower, reference)
    require(fiber.profile == Counter(zip(fiber.omitted_patterns, grouped_rows, strict=True)),
            "grouped lower profile preserved")
    require(len(fiber.replacements) == 786, "number of binary replacement coordinates")
    subsets = information_sets()
    indices = [index for subset in subsets for index in subset]
    require(len(indices) == len(set(indices)) == 1186 and set(indices).isdisjoint(LOWER_OMISSIONS),
            "six disjoint retained information sets")

    # Round-trip a different placement, not merely the zero change.
    row, alternative = fiber.replacements[0]
    partner = next(i for i, mask in enumerate(reference)
                   if mask == alternative and fiber.omitted_patterns[row] == fiber.omitted_patterns[i])
    changed = reference.copy()
    changed[row], changed[partner] = changed[partner], changed[row]
    changed_dots = correlations(lower, positive_columns(changed), BOTTOM)
    for subset in subsets:
        targets = {i: changed_dots[i] for i in subset}
        require(fiber.invert(targets) == changed, "full-rank indexed inverse on each information set")
    print("  lower grouped fiber: six disjoint indexed modulo-eight information sets, each rank 786")
    distance = check_paley_distance(lower)
    print(f"  different placements change at least {distance} indexed retained modulo-eight vectors")


if __name__ == "__main__":
    main()
