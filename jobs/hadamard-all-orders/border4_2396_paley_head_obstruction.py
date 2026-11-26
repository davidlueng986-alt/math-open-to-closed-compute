"""Certify two different fixed-head obstructions in the length-299 Paley route."""

from fractions import Fraction
from math import isqrt

from border4_2396_paley_negative_norm import N, periodic, sign_word
from border4_2396_paley_q13_mod16 import AXIS_78, margins

U = 0x48FA398B8B90092D600318FC2CBD4E598AE7FD705135AF96799B60BA07FE955A43193106C
V = 0x62455956FE7B6ACD30D1E8B2CDBE02F8502F1DA4768EE1375324E3BB38320E6FB52F4235638
PRIME = 169831
TRACE = 4723095639


def atan_bounds(inv):
    terms = [Fraction((-1)**k, (2*k+1)*inv**(2*k+1)) for k in range(24)]
    return sum(terms), sum(terms[:-1])


def cosine_bounds():
    five_l, five_u = atan_bounds(5)
    other_l, other_u = atan_bounds(239)
    pi_l = 16*five_l - 4*other_u
    pi_u = 16*five_u - 4*other_l
    assert 3 < pi_l < pi_u < Fraction(22,7)
    scale = 1 << 45

    def cosine(angle):
        power = Fraction(1)
        value = power
        for k in range(1, 13):
            power *= -angle**2 / ((2*k)*(2*k-1))
            value += power
        next_term = power * -angle**2 / (25*26)
        return value + next_term, value

    bounds = [(scale,scale)]
    for j in range(1,N//2+1):
        low = cosine(2*j*pi_u/N)[0] * scale
        high = cosine(2*j*pi_l/N)[1] * scale
        bounds.append((int(low.numerator//low.denominator),
                       int(-((-high.numerator)//high.denominator))))
    return scale,bounds


def power_interval(correlation, frequency, scale, bounds):
    lower = upper = correlation[0]*scale
    for lag in range(1,N//2+1):
        index = frequency*lag % N
        a,b = bounds[min(index,N-index)]
        coeff = 2*correlation[lag]
        if coeff < 0:
            a,b = b,a
        lower += coeff*a
        upper += coeff*b
    return lower,upper


def evaluate_root(coefficients, modulus):
    a=b=0
    for c in reversed(coefficients):
        a,b=(c-b)%modulus,(a+TRACE*b)%modulus
    return a,b


def inert_certificate(head):
    p = PRIME
    assert all(p%d for d in range(2,isqrt(p)+1))
    assert pow((TRACE*TRACE-4)%p,(p-1)//2,p) == p-1
    assert evaluate_root([0]*N+[1],p*p) == (1,0)
    assert all(evaluate_root([0]*q+[1],p)!=(1,0) for q in (13,23))
    residual = [(1196 if not j else 0)-value for j,value in enumerate(head)]
    assert not any(x%2 for x in residual)
    value = evaluate_root([x//2 for x in residual],p*p)
    assert value == (20946955540,0) and not value[0]%p and value[0]%(p*p)


def main():
    source = tuple(map(sign_word,AXIS_78))
    head = tuple(map(sign_word,(U,V)))
    assert all(a*b==c*d for a,b,c,d in zip(*source[:2],*head,strict=True))
    assert margins(head,13) == margins(source[:2],13)
    assert tuple(map(sum,head)) == (17,-5)
    w=source[-1]
    assert periodic(margins(head+(w,w),13)) == [1196]+[0]*12
    assert all(value%8==0 for value in periodic(head+(w,w))[1:])
    scale,bounds=cosine_bounds()
    old=periodic(source[:2])
    lo,high=power_interval(old,131,scale,bounds)
    assert 2818*scale < lo < high < 2819*scale
    new=periodic(head)
    assert all(power_interval(new,j,scale,bounds)[1] < 1143*scale for j in range(150))
    inert_certificate(new)
    print("Fixed axis 78 heads violate the spectral bound at primitive frequency 131")
    print("Another exact C13 head clears all 150 spectral bounds, but an inert prime excludes every W")


if __name__ == "__main__":
    main()
