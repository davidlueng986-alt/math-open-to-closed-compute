"""Enumerate the multiplier groups remaining after the three published obstructions."""

from collections import Counter
from math import gcd


def powers(a, n):
    subgroup = {1}
    v = a % n
    while v not in subgroup:
        subgroup.add(v)
        v = v*a % n
    return subgroup


def main():
    n = 1197
    primes = (3, 7, 19)
    squares = {p: {x*x % p for x in range(1, p)} for p in primes}
    allowed = {i for i in range(n) if gcd(i, n) == 1 and all(i % p in squares[p] for p in primes)}
    cycles = {a: powers(a, n) for a in allowed}
    trivial = frozenset([1])
    groups, stack = {trivial}, [trivial]
    while stack:
        current = stack.pop()
        for a in allowed - current:
            generated = frozenset(x*y % n for x in current for y in cycles[a])
            if 400 in generated or generated in groups:
                continue
            groups.add(generated)
            stack.append(generated)
    full_399 = {i % 399 for i in allowed}
    sizes = Counter()
    excluded_27 = 0
    for group in groups:
        image = {a % 399 for a in group}
        if len(image) != len(group):
            raise ValueError("reduction to modulus 399 must be injective")
        if image == full_399:
            excluded_27 += 1
        else:
            sizes[len(group)] += 1
    extensions = sorted(sorted(h) for h in groups if len(h) == 9 and 463 in h)
    if (len(allowed), len(full_399), excluded_27, sizes, len(extensions)) != (
            81, 27, 9, {1: 1, 3: 12, 9: 18}, 3):
        raise ValueError("unexpected subgroup census")
    if not all(599 % d for d in range(2, 25)) or 598 in {i*i % 599 for i in range(599)}:
        raise ValueError("failed the prime/negative-square arithmetic")
    print(f"Surviving candidate groups by order: {dict(sorted(sizes.items()))}")
    print(f"Order-27 groups with the excluded full image: {excluded_27}")
    print(f"Order-9 candidates containing 463: {extensions}")


if __name__ == "__main__":
    main()
