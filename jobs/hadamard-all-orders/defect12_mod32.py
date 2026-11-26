"""Check the binary error-kernel arithmetic for the Eliahou–Kervaire source."""

from math import gcd, isqrt


def remainder(dividend, divisor):
    while dividend and dividend.bit_length() >= divisor.bit_length():
        dividend ^= divisor << (dividend.bit_length() - divisor.bit_length())
    return dividend


def polynomial_gcd(left, right):
    while right:
        left, right = right, remainder(left, right)
    return left


def polynomial_product(left, right):
    product = 0
    while right:
        shift = (right & -right).bit_length() - 1
        product ^= left << shift
        right ^= 1 << shift
    return product


def error_polynomial(t, m):
    return sum((1 << (2 * i)) + (1 << (t - 2 * i)) for i in range(1, m) if (m - i) % 2)


def check_kernel(r):
    t = 4 * r + 3
    m = r // 2
    error = error_polynomial(t, m)
    factor = polynomial_gcd(error, (1 << t) | 1)
    if m % 2 == 0:
        period = gcd(t, m)
        assert factor == ((1 << period) | 1) and period <= 7
    else:
        left = gcd(t, m - 1)
        right = gcd(t, m + 1)
        assert gcd(left, right) == 1
        assert ((factor << 1) ^ factor) == polynomial_product((1 << left) | 1, (1 << right) | 1)
        period = max(left, right)
        assert period <= 15
    return t // period


def error_image(t, error, blocks):
    cycle = (1 << t) | 1
    return [remainder(polynomial_product(error, sum(1 << j for j in block)), cycle)
            for block in blocks]


def verify():
    # For t >= 225 the period bound of 15 proves the minimum-weight bound.
    small_minima = [check_kernel(r) for r in range(4, 56)]
    assert min(small_minima) == 15
    assert all(error_polynomial(4 * r + 3, r // 2) == 0 for r in range(1, 4))

    t = 599
    r = 149
    assert all(t % d for d in range(2, isqrt(t) + 1))
    assert pow(2, 299, t) == 1 and pow(2, 13, t) == 405 and pow(2, 23, t) == 212
    assert check_kernel(r) == t
    error = error_polynomial(t, r // 2)
    tetrad = ((), (299, 300), (), (299, 300))
    residual = ((0, 1, 150, 300), (299, 449), (0, 299, 449, 598), (299, 449))
    row_image = error_image(t, error, tetrad)
    column_image = error_image(t, error, residual)
    row_weight = sum(word.bit_count() for word in row_image)
    column_weight = sum(word.bit_count() for word in column_image)
    assert (row_weight, column_weight) == (296, 888)
    print(f"binary error kernel minimum >= 15 for r >= 4; at t=599 minimum = {t}")
    print(f"t=599 fixed tetrad/panel error images: weights {row_weight}, {column_weight}")


if __name__ == "__main__":
    verify()
