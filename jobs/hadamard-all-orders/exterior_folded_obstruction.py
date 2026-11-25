"""Rebuild and check a fixed Sylvester row-pair obstruction modulo sixteen."""

from collections import Counter, defaultdict
from gzip import open as gzip_open
from itertools import combinations
import json
from pathlib import Path

from exterior_exact_factors import decode
from exterior_lower_fiber import binary_echelon
from five_column_constraints import (
    BOTTOM, LOWER_OMISSIONS, ORDER, TOP, WIDTH, correlations, positive_columns, require,
)
from five_column_gram import gram_fixture
from verify import paley, rows_from_columns


LOW = (6, 4, 4, 6, 6)
HIGH = 28
BRIDGE = {
    113: 15, 218: 19, 231: 27, 316: 15, 561: 23,
    713: 27, 818: 7, 831: 27, 916: 15, 1161: 23,
}


def bit_indices(word):
    while word:
        bit = word & -word
        yield bit.bit_length() - 1
        word ^= bit


class Formula:
    def __init__(self, variables):
        self.variables = variables
        self.clauses = []
        self.xors = {}

    def fresh(self):
        self.variables += 1
        return self.variables

    def add(self, *clause):
        literals = set(clause)
        if not any(-literal in literals for literal in literals):
            self.clauses.append(tuple(sorted(literals)))

    def parity(self, inputs):
        current = inputs[0]
        for next_input in inputs[1:]:
            a, b = sorted((current, next_input))
            if (a, b) not in self.xors:
                out = self.fresh()
                self.xors[a, b] = out
                self.add(-a, -b, -out)
                self.add(a, b, -out)
                self.add(a, -b, out)
                self.add(-a, b, out)
            current = self.xors[a, b]
        return current

    def exactly(self, literals, target):
        size = len(literals)
        require(0 <= target <= size, "valid cardinality target")
        if target > size // 2:
            literals = [-literal for literal in literals]
            target = size - target
        if target == 0:
            for literal in literals:
                self.add(-literal)
            return
        always = self.fresh()
        self.add(always)
        previous = [always]
        for i, literal in enumerate(literals, 1):
            current = [always]
            for j in range(1, min(i, target + 1) + 1):
                a = previous[j] if j < len(previous) else -always
                b = previous[j - 1]
                out = self.fresh()
                current.append(out)
                # out is true iff the first i inputs contain at least j true inputs.
                self.add(-a, out)
                self.add(-b, -literal, out)
                self.add(-out, a, b)
                self.add(-out, a, literal)
            previous = current
        self.add(previous[target])
        self.add(-previous[target + 1])


def residue_parts(dots):
    return tuple(value % 8 for value in dots), sum((value >> 3 & 1) << j for j, value in enumerate(dots))


def load_fixture():
    directory = Path(__file__).parent
    top, lower, _, _ = gram_fixture()
    upper = decode(json.loads((directory / "exterior_mod16_invariant_witness.json").read_text())["upper"])
    lower_text = json.loads((directory / "exterior_exact_factor_witnesses.json").read_text())[7]["lower"]
    return top, lower, upper, [int(symbol, 32) for symbol in lower_text]


def build_formula(top, lower, upper, signs):
    target = sum(residue_parts(row) == (LOW, HIGH) for row in correlations(top[3:], upper, TOP))
    require(target == 3, "required residue multiplicity")
    half = BOTTOM // 2
    paley_rows = rows_from_columns(half, paley(half - 1))
    indexed = {}
    for i, row in enumerate(correlations(lower, positive_columns(signs), BOTTOM)):
        if i not in LOWER_OMISSIONS:
            low, high = residue_parts([-value for value in row])
            if low == LOW:
                indexed[i] = high

    pools = defaultdict(dict)
    row_types = []
    for r in range(half):
        left, right = signs[r], signs[r + half]
        key = (left ^ right, left.bit_count(), right.bit_count(), r == 0)
        pools[key][left] = None
        row_types.append(key)

    choices = []
    row_choices = []
    pool_counts = defaultdict(dict)
    projections = defaultdict(dict)
    changes = [[0] * WIDTH for _ in range(BOTTOM)]
    for r, key in enumerate(row_types):
        old = signs[r]
        folded = key[0]
        alternatives = []
        for new in pools[key]:
            if new == old:
                continue
            variable = len(choices)
            choices.append((r, new))
            alternatives.append(variable)
            pool_counts[key, old][variable] = -1
            pool_counts[key, new][variable] = 1
            for j in bit_indices(old ^ new):
                copy = folded >> j & 1
                bit_change = (new >> j & 1) - (old >> j & 1)
                for i in LOWER_OMISSIONS[1:]:
                    old_top = 2 * (lower[i] >> r & 1) - 1
                    old_bottom = 2 * (lower[i] >> (r + half) & 1) - 1
                    coefficient = bit_change * (old_top + (1 - 2 * copy) * old_bottom)
                    if coefficient:
                        projections[i, j][variable] = coefficient // 2
                for i in bit_indices(paley_rows[r]):
                    changes[i + half * copy][j] ^= 1 << variable
        row_choices.append(alternatives)

    formula = Formula(len(choices))
    for alternatives in row_choices:
        for a, b in combinations(alternatives, 2):
            formula.add(-(a + 1), -(b + 1))
    parity = []
    for terms in (*pool_counts.values(), *projections.values()):
        require(all(abs(value) == 1 for value in terms.values()), "signed cardinality coefficients")
        formula.exactly([i + 1 if value > 0 else -(i + 1) for i, value in terms.items()],
                        sum(value < 0 for value in terms.values()))
        parity.append((sum(1 << i for i in terms), 0))

    events = []
    for i, high in indexed.items():
        tests = [(bits, (high ^ HIGH) >> j & 1) for j, bits in enumerate(changes[i])]
        if binary_echelon(parity + tests) is None:
            continue
        literals = []
        for bits, wanted in tests:
            if bits:
                value = formula.parity([j + 1 for j in bit_indices(bits)])
                literals.append(value if wanted else -value)
        event = formula.fresh()
        for literal in literals:
            formula.add(-event, literal)
        formula.add(event, *(-literal for literal in literals))
        events.append(event)
    require(len(events) == 51, "possible indices of the required residue")
    formula.exactly(events, target)
    return formula


class UnitPropagation:
    """Check reverse unit propagation steps without a SAT solver."""

    def __init__(self, variables):
        self.assignment = [0] * (variables + 1)
        self.watch = defaultdict(list)
        self.clauses = []
        self.units = []
        self.trail = []
        self.contradiction = False

    def add(self, clause):
        if not clause:
            self.contradiction = True
        elif len(clause) == 1:
            self.units.append(clause[0])
        else:
            index = len(self.clauses)
            self.clauses.append(list(clause))
            self.watch[clause[0]].append(index)
            self.watch[clause[1]].append(index)

    def value(self, literal):
        return self.assignment[literal] if literal > 0 else -self.assignment[-literal]

    def assume(self, literal):
        value = self.value(literal)
        if value == 0:
            self.assignment[abs(literal)] = 1 if literal > 0 else -1
            self.trail.append(literal)
        return value != -1

    def propagate(self, assumptions):
        if self.contradiction or any(not self.assume(literal)
                                     for group in (self.units, assumptions) for literal in group):
            return True
        processed = 0
        while processed < len(self.trail):
            false = -self.trail[processed]
            processed += 1
            watched = self.watch[false]
            i = 0
            while i < len(watched):
                clause = self.clauses[watched[i]]
                if clause[0] == false:
                    clause[0], clause[1] = clause[1], clause[0]
                if self.value(clause[0]) > 0:
                    i += 1
                    continue
                move = next((k for k in range(2, len(clause)) if self.value(clause[k]) >= 0), None)
                if move is not None:
                    clause[1], clause[move] = clause[move], false
                    self.watch[clause[1]].append(watched[i])
                    watched[i] = watched[-1]
                    watched.pop()
                else:
                    if not self.assume(clause[0]):
                        return True
                    i += 1
        return False

    def verify_step(self, clause):
        conflict = self.propagate(-literal for literal in clause)
        for literal in self.trail:
            self.assignment[abs(literal)] = 0
        self.trail.clear()
        require(conflict, "reverse unit propagation")
        self.add(clause)


def check_bridge(top, lower, upper, signs):
    half = BOTTOM // 2
    alternate = [BRIDGE.get(row, mask) for row, mask in enumerate(signs)]
    for row in BRIDGE:
        require(alternate[row] != signs[row], "actual change at each bridge row")
    require([mask.bit_count() for mask in alternate] == [mask.bit_count() for mask in signs],
            "unchanged row weights")
    require(all(a ^ b == c ^ d for a, b, c, d in zip(signs[:half], signs[half:],
                                                    alternate[:half], alternate[half:], strict=True)),
            "unchanged physical row-pair XOR")
    def grouped(rows):
        return Counter((a ^ b, a.bit_count(), b.bit_count(), a)
                       for a, b in zip(rows[:half], rows[half:], strict=True))
    require(grouped(signs) != grouped(alternate), "changed folded-pool mask counts")

    old = positive_columns(signs)
    new = positive_columns(alternate)
    require(all(a.bit_count() == b.bit_count() and (a >> half).bit_count() == (b >> half).bit_count()
                for a, b in zip(old, new, strict=True)), "unchanged half column weights")
    require(all(a.bit_count() + b.bit_count() == ORDER // 2 for a, b in zip(upper, new, strict=True)),
            "exact column balance")
    require(correlations(old, old, BOTTOM) == correlations(new, new, BOTTOM), "unchanged exact Gram")
    omitted = [lower[i] for i in LOWER_OMISSIONS]
    require(correlations(omitted, old, BOTTOM) == correlations(omitted, new, BOTTOM),
            "unchanged exact omitted projections")
    retained = [column for i, column in enumerate(lower) if i not in LOWER_OMISSIONS]
    old_dots = [[-value for value in row] for row in correlations(retained, old, BOTTOM)]
    new_dots = [[-value for value in row] for row in correlations(retained, new, BOTTOM)]
    require(all((a - b) % 8 == 0 for before, after in zip(old_dots, new_dots, strict=True)
                for a, b in zip(before, after, strict=True)), "unchanged indexed residues modulo eight")
    require(sum(residue_parts(row) == (LOW, HIGH) for row in old_dots) == 4
            and sum(residue_parts(row) == (LOW, HIGH) for row in new_dots) == 3,
            "match the required precise residue multiplicity outside the obstructed pools")
    upper_dots = correlations(top[3:], upper, TOP)
    hi = lambda dots: Counter(tuple(value % 16 for value in row) for row in dots)
    require(sum((hi(upper_dots) & hi(new_dots)).values()) == 906, "bridge modulo-sixteen vector count")


def main():
    fixture = load_fixture()
    formula = build_formula(*fixture)
    require((formula.variables, len(formula.clauses)) == (67203, 267722), "reconstructed formula size")
    with gzip_open(Path(__file__).with_name("exterior_folded_case8.json.gz"), "rt") as file:
        certificate = json.load(file)
    generated = set(formula.clauses)
    premises = [tuple(row) for row in certificate["premises"]]
    require(len(premises) == 7356 and all(row in generated for row in premises),
            "each core premise was independently reconstructed")
    checker = UnitPropagation(formula.variables)
    for clause in premises:
        checker.add(clause)
    lemmas = certificate["lemmas"]
    require(len(lemmas) == 587 and lemmas[-1] == [], "proof ends in the empty clause")
    for clause in lemmas:
        require(all(1 <= abs(value) <= formula.variables for value in clause), "proof literal range")
        checker.verify_step(clause)
    require(checker.contradiction, "verified contradiction")
    check_bridge(*fixture)
    print("n=2396: factor 8 fixed folded pool cannot realize the required modulo-sixteen multiplicity")
    print("  7356 independently reconstructed premises and 587 verified RUP lemmas")
    print("  a ten-row change of pool multiplicities restores the targeted count; 906 full vectors modulo 16")


if __name__ == "__main__":
    main()
