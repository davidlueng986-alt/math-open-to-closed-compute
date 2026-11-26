"""Solve the primitive F11 phase equation for a fixed ternary reflection profile."""

import json
from struct import unpack

from direct_2396_cyclic import quarter_correlations
from direct_2396_cyclic_ap import LEGENDRE, P
from direct_2396_cyclic_mod12 import DATA, divide_by_pair


PRIME = 11
DEGREE = P-1
REAL_SIZE = PRIME**(DEGREE//2)
ZERO = (0,)*DEGREE
ONE = (1,) + (0,)*(DEGREE-1)


def reduce_at_primitive(poly):
    assert len(poly) == P
    last = poly[-1]
    return tuple((u-last) % PRIME for u in poly[:-1])


def conjugate(element):
    return reduce_at_primitive((element[0], 0, *element[:0:-1]))


def add(*elements):
    return tuple(sum(values) % PRIME for values in zip(*elements, strict=True))


def times_constant(coefficient, element):
    return tuple(coefficient*value % PRIME for value in element)


def positive_integer_digits(element):
    # Each product coefficient is at most 598 * 10^2, so base 2^16 has no carries.
    raw = bytearray(2*DEGREE)
    raw[::2] = bytes(element)
    return int.from_bytes(raw, "little")


def multiply(left, right):
    result = positive_integer_digits(left)*positive_integer_digits(right)
    values = unpack(f"<{2*P}H", result.to_bytes(4*P, "little"))
    edge = values[DEGREE]
    return tuple((values[i]+values[i+P]-edge) % PRIME for i in range(DEGREE))


def power(element, exponent):
    value = ONE
    while exponent:
        if exponent & 1:
            value = multiply(value, element)
        element = multiply(element, element)
        exponent //= 2
    return value


def imaginary_unit():
    gauss = reduce_at_primitive([0] + [1 if LEGENDRE >> j & 1 else -1 for j in range(1,P)])
    imaginary = times_constant(3, gauss)
    assert multiply(imaginary, imaginary) == times_constant(-1, ONE)
    assert conjugate(imaginary) == times_constant(-1, imaginary)
    return imaginary


def anti_invariant_root(element, imaginary):
    """Return one root of the real element in the anti-invariant line, if it exists."""
    assert conjugate(element) == element
    if element == ZERO:
        return ZERO
    sign = power(element, (REAL_SIZE-1)//2)
    if sign == ONE:
        return None
    assert sign == times_constant(-1, ONE)
    root = multiply(imaginary, power(times_constant(-1, element), (REAL_SIZE+1)//4))
    assert conjugate(root) == times_constant(-1, root)
    assert multiply(root, root) == element
    return root


def squared_odd_target(even, tail):
    mask = reduce_at_primitive([1 if i in (1,P-1) else 0 for i in range(P)])
    third = pow(3, -1, PRIME)
    return add(
        multiply(even, even),
        times_constant(2*third, multiply(mask, even)),
        multiply(mask, mask),
        times_constant(third, add(multiply(tail, conjugate(tail)), times_constant(-4*P, ONE))),
    )


def centered_anti_coefficients(element):
    values = tuple((value-element[0]) % PRIME for value in (*element, 0))
    assert values[0] == 0 and all((a+b) % PRIME == 0
                                   for a,b in zip(values[1:], values[:0:-1], strict=True))
    return values


def wanted_odd_square(ternary, tail):
    even = reduce_at_primitive([(ternary[i]+ternary[-i % P])//2 for i in range(P)])
    return squared_odd_target(even, reduce_at_primitive(tail))


def check_witness():
    assert pow(PRIME, P-1, P) == 1
    assert all(pow(PRIME, (P-1)//q, P) != 1 for q in (2,13,23))
    assert pow(PRIME, DEGREE//2, P) == P-1 and REAL_SIZE % 4 == 3
    imaginary = imaginary_unit()
    odd = reduce_at_primitive([0,1] + [0]*(P-3) + [-1])
    root = anti_invariant_root(multiply(odd, odd), imaginary)
    assert root in (odd, times_constant(-1, odd))
    assert centered_anti_coefficients(odd) == tuple([0,1]+[0]*(P-3)+[PRIME-1])
    assert anti_invariant_root(ZERO, imaginary) == ZERO

    ternary_text, tail_text = json.loads(DATA.read_text())
    table = {'+': 1, '-': -1, '.': 0}
    ternary = [table[x] for x in ternary_text]
    tail = [table[x] for x in tail_text]
    assert len(ternary) == len(tail) == P and 0 not in tail
    assert [i for i, value in enumerate(ternary) if value == 0] == [1,P-1]
    error = quarter_correlations((ternary_text.replace('.', '-'), ternary_text.replace('.', '+'),
                                  ternary_text.replace('.', '+'), tail_text))
    assert not any(x % 3 for x in error[1:])
    rhs = [-sum(tail[j]*tail[(j+d)%P] for j in range(P)) for d in range(P)]
    rhs[0] += 4*P
    trace = divide_by_pair(rhs)
    assert all((a+b-c) % 3 == 0 for a,b,c in zip(
        ternary, ternary[:1]+ternary[:0:-1], trace, strict=True))
    assert sum(ternary) == 19 and sum(tail) == 35
    anti_pairs = sum(ternary[j] != ternary[P-j] for j in range(1,P//2+1))
    assert anti_pairs == 118

    target = wanted_odd_square(ternary, tail)
    assert target != ZERO and anti_invariant_root(target, imaginary) is None
    print("Direct mod11: fixed physical tail and all 2^118 reflection phases excluded by the real square.")


if __name__ == "__main__":
    check_witness()
