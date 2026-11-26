"""Replay the exact short-reflection obstruction on the cyclic Pell factor."""


def minus_shift(word):
    return tuple(value - word[i-1] for i, value in enumerate(word))


def correlation(word):
    return tuple(sum(value * word[(i + d) % len(word)] for i, value in enumerate(word))
                 for d in range(len(word)))


def main():
    r = 307076037508906904285239
    p = 146850491611181
    y = -207677217568161
    assert r % 4 == 3 and 0 < p < r
    assert (r + y * y) % p == 0 and y % p
    root = pow(p, (r + 1) // 4, r)
    root = min(root, r - root)
    assert root == 68648617375908982806326 and root * root % r == p
    square_norm = p + (root * root - p) // r
    assert square_norm == 15346794074029717674286 < root

    w = (2, -1, 0)
    assert sum(w) == 1 and correlation(w) == (5, -2, -2)
    v = minus_shift(w)
    assert sum(v) == 0 and sum(x % 2 for x in v) == 2
    assert correlation(v) == (14, -7, -7)
    print(f"CYCLIC-PELL-SHORT-REFLECTION-PASS centered root={root} norm={square_norm}")


if __name__ == "__main__":
    main()
