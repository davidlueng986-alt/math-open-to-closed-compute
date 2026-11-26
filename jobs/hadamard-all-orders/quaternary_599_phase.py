"""Solve the modulo-eight phase-signed system for a one-site Paley word."""

from math import isqrt


N = 599
FULL = (1 << N) - 1
QR = sum(1 << j for j in {x*x % N for x in range(1, N)})
NQR = FULL ^ 1 ^ QR
A_PHASE = 1 << (N-1)
A_NEGATIVE = NQR ^ A_PHASE

JOINT_A = 0x57EA344F5403EF40B0483ABE005D96079D2F2C2AF21E03D900B54046F87E8DED987E74CDB5F10760654E4C0745ED44DC887160DFB9EC2458DDF165460821DF558C598169A244FD5FACB0A5
JOINT_B = 0x226A0B9061D045B4AB032F4F6C8430E971A532F1CAD44335559BE69C49864E3599D477510F06003AA52557486AF8EFD0B8E38290C4F7C5E0905502B52DA9DF6F614636DCE26B24A89B74BE

def rotate(value, shift):
    shift %= N
    return (value << shift & FULL) | (value >> (N-shift))


def multiply(left, right):
    result = 0
    while left:
        bit = left & -left
        result ^= right << (bit.bit_length()-1)
        left ^= bit
    return result


def divide(dividend, divisor):
    quotient = 0
    while dividend and dividend.bit_length() >= divisor.bit_length():
        shift = dividend.bit_length()-divisor.bit_length()
        quotient ^= 1 << shift
        dividend ^= divisor << shift
    return quotient, dividend


def gcd(left, right):
    while right:
        left, right = right, divide(left, right)[1]
    return left


def invert(value, modulus):
    left, right = 0, 1
    residual = modulus
    while value:
        quotient, remainder = divide(residual, value)
        residual, value = value, remainder
        left, right = right, left ^ multiply(quotient, right)
    assert residual == 1
    return divide(left, modulus)[1]


def reduction_basis(words):
    pivots = {}
    for value in words:
        while value:
            pivot = value.bit_length()-1
            if pivot not in pivots:
                pivots[pivot] = value
                break
            value ^= pivots[pivot]
    return tuple(pivots.values())


def directed_errors(phase, negative, lag):
    return negative ^ rotate(negative,-lag) ^ ((FULL ^ phase) & rotate(phase,-lag))


def sign_baseline(phase, factor):
    reciprocal = sum(1 << (-i % N) for i in range(N) if phase >> i & 1)
    target = rotate(QR,-1) ^ rotate(NQR,1)
    inverse = invert(divide(reciprocal,factor)[1],factor)
    return divide(multiply(target, inverse),factor)[1]


def find_signs(phase, baseline, generators):
    pivots = {}
    width = len(generators)
    for lag in range(1, N):
        ka = directed_errors(A_PHASE, A_NEGATIVE, lag)
        kb = directed_errors(phase, baseline, lag)
        value = N-ka.bit_count()-kb.bit_count()
        assert value % 2 == 0
        mask = kb ^ rotate(kb,lag)
        row = (((value//2) % 2) << width)
        for j, vector in enumerate(generators):
            row |= ((mask & vector).bit_count() % 2) << j
        while coefficients := row & ((1 << width)-1):
            i = coefficients.bit_length()-1
            if i not in pivots:
                pivots[i] = row
                break
            row ^= pivots[i]
        else:
            if row:
                return (), len(pivots)

    instructions = sorted(pivots.items())
    answers = [1 << width]
    for i in range(width):
        if i not in pivots:
            answers.extend([word | (1 << i) for word in answers])
    masks = []
    for word in answers:
        for i, row in instructions:
            if (word & row).bit_count()%2:
                word |= 1 << i
        candidate = baseline
        for i, vector in enumerate(generators):
            if word >> i & 1:
                candidate ^= vector
        masks.append(candidate)
    return tuple(masks), len(pivots)


def sign_sums(phase, negative):
    real = N-phase.bit_count()-2*(negative & (FULL ^ phase)).bit_count()
    imaginary = phase.bit_count()-2*(negative & phase).bit_count()
    return real, imaginary


def direct_scores(phase, negative, first_negative=A_NEGATIVE):
    def parts(mask, signs):
        real = tuple((-1)**(signs>>i & 1) if not mask>>i & 1 else 0 for i in range(N))
        imag = tuple((-1)**(signs>>i & 1) if mask>>i & 1 else 0 for i in range(N))
        return real, imag

    pairs = (parts(A_PHASE,first_negative), parts(phase,negative))
    real, imaginary = [], []
    for d in range(1, N//2+1):
        real.append(sum(r[i]*r[(i+d)%N]+s[i]*s[(i+d)%N]
                        for i in range(N) for r, s in pairs))
        imaginary.append(sum(s[i]*r[(i+d)%N]-r[i]*s[(i+d)%N]
                             for i in range(N) for r, s in pairs))
    assert all((a+b)%8 == (a-b)%8 == 0 for a, b in zip(real,imaginary,strict=True))
    return (sum(a*a+b*b for a, b in zip(real,imaginary,strict=True)),
            sum(a == b == 0 for a, b in zip(real,imaginary,strict=True)),
            sum(a%8 == b%8 == 0 for a, b in zip(real,imaginary,strict=True)),
            max(map(abs,real+imaginary)))


def verify():
    assert all(N % d for d in range(2, isqrt(N)+1))
    assert N-1 == 2*13*23 and pow(2,299,N) == 1
    assert all(pow(2,d,N) != 1 for d in (13,23))
    assert pow(2,149,N) != N-1
    assert QR.bit_count() == 299
    assert {(QR & rotate(QR,j)).bit_count() for j in range(1,N)} == {149}
    f = gcd(QR, FULL)
    assert f.bit_length() == 300 and divide(FULL, f)[1] == 0
    generators = reduction_basis(rotate(QR,s) for s in range(N))
    assert len(generators) == 300

    candidates, rank = find_signs(QR, sign_baseline(QR,f), generators)
    assert rank == 298 and len(candidates) == 4
    assert sorted(sum(x*x for x in sign_sums(QR,b)) for b in candidates) == [169,169,425,425]
    print("One QR translate: four mod8 sign choices, with squared sums 169 or 425", flush=True)
    families = signs = 0
    for d in range(1,N//2+1):
        phase = QR ^ rotate(QR,d)
        candidates, _ = find_signs(phase, sign_baseline(phase,f), generators)
        families += bool(candidates)
        signs += len(candidates)
        assert all(sum(x*x for x in sign_sums(phase,b)) != 1193 for b in candidates)
    assert (families, signs) == (198,596)
    print("Two QR translates: 299 masks, 198 compatible mod8, 596 signs, zero exact zero-frequency norms")

    phase = QR ^ rotate(QR,427) ^ rotate(QR,572)
    candidates, _ = find_signs(phase, sign_baseline(phase,f), generators)
    chosen = tuple(b for b in candidates if sign_sums(phase,b) == (-32,13))
    assert len(chosen) == 1
    assert sum(x*x for x in sign_sums(A_PHASE,A_NEGATIVE)) == 5
    assert direct_scores(phase, chosen[0]) == (173824,3,161,52)
    print("Three QR translates: exact squared sums 5 and 1193, all Re+Im and Re-Im modulo 8")

    change = JOINT_A ^ A_NEGATIVE
    assert all((change>>i & 1) == (change>>((2*(N-1)-i)%N) & 1) for i in range(N))
    assert divide(JOINT_B ^ (1 << 1),f)[1] == 0
    assert sign_sums(A_PHASE, JOINT_A) == (26,-1)
    assert sign_sums(QR, JOINT_B) == (20,11)
    assert 26**2+1+20**2+11**2 == 1198
    assert direct_scores(QR, JOINT_B, JOINT_A)[:3] == (291_392,6,171)
    print("Joint reflection and QR flips: exact norm 1198, all signed sums mod8, 171 independent pairs with separate mod8")


if __name__ == "__main__":
    verify()
