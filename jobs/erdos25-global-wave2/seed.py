#!/usr/bin/env python3
"""Produce one explicit nonlinear first-kill seed; no solver needed."""
from pathlib import Path
import sys


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def main():
    output = Path(sys.argv[1])
    target, previous = 390, 1
    rules = {}
    for p in (2, 3, 5, 7, 11):
        ds = divisors(previous)[:p - 1]
        digits = [a for a in range(p) if a != target % p]
        assert len(ds) == p - 1
        for d, digit in zip(ds, digits):
            q = p * d
            a = next(a for a in range(target % d, q, d) if a % p == digit)
            assert q not in rules
            rules[q] = a
        previous *= p
    assert previous == 2310 and max(rules) < target
    rules[target] = 0
    output.write_text("".join(f"{q}\t{a}\n" for q, a in sorted(rules.items())))


if __name__ == "__main__":
    main()
