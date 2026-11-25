"""Exact replay for a one-lag near-64 Golay quadruple of length 599."""

LENGTH = 599
ALL = (1 << LENGTH) - 1
TEMPLATES = ((4,), (2, 1, 1), (4,), (2, 1, 1), (4,), (1, 2, 1), (4,), (1, 2, 1))
COUNTS = (18, 19, 18, 19, 17, 19, 18, 18)
RUNS_AFTER = ((), (1, 5), (), (), (3,), (3,), (3,), ())


def run_word(runs):
    value = length = 0
    for i, run in enumerate(runs):
        if i % 2:
            value |= ((1 << run) - 1) << length
        length += run
    assert length == LENGTH
    return value


def rotate(value, distance):
    return (value >> distance) | ((value & ((1 << distance) - 1)) << (LENGTH - distance))


def source_words():
    s = run_word([run for template, count, after in zip(TEMPLATES, COUNTS, RUNS_AFTER, strict=True)
                  for run in template * count + after])
    return s, run_word((299, 2, 297, 1)), run_word((300, 299))


def verify():
    s, q, tau = source_words()
    eligible = [ALL ^ ((q ^ rotate(q, d)) | (tau ^ rotate(tau, d)))
                for d in range(1, (LENGTH + 1) // 2)]

    def coefficients(value):
        return (4 * (mask.bit_count() - 2 * ((value ^ rotate(value, d)) & mask).bit_count())
                for d, mask in enumerate(eligible, 1))

    def proposed_coefficients():
        errors = {152: 16}
        for i in range(1, 19):
            errors[4 * i] = 64 * (-1)**i * (37 - 2 * i)
        for j in range(18):
            errors[82 + 4 * j] = 64 * (-1)**(17 + j) * (j + 1)
            errors[154 + 4 * j] = 64 * (-1)**(j + 1) * (18 - j)
        return [errors.get(d, 0) for d in range(1, (LENGTH + 1) // 2)]

    got = list(coefficients(s))
    assert got == proposed_coefficients()
    assert [(d, v) for d, v in enumerate(got, 1) if v % 64] == [(152, 16)]

    print("599: only residue failures modulo 64 are cyclic lags ±152 with coefficient +16")


if __name__ == "__main__":
    verify()
