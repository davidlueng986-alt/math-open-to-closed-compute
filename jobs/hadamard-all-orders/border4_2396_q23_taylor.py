"""Replay the truncated C23 norm parameterization on the joint source."""

from math import comb

from border4_2396 import periodic
from border4_2396_joint_q13_mod16 import joint_words
from border4_2396_shifted_tail import reflect

P = 23


def multiply(a, b):
    z = [0]*P
    for i, left in enumerate(a):
        for j in range(P-i):
            z[i+j] += left*b[j]
    return [v % P for v in z]


def basis():
    # The auxiliary variable x is z-1.  The basis uses tau=z-z^{-1}.
    one = [1]+[0]*(P-1)
    tau = [0, 2]+[(-1)**(i+1) for i in range(2, P)]
    powers = [one]
    for _ in range(1, P):
        powers.append(multiply(powers[-1], tau))
    return powers


def to_taylor(word, powers):
    x_coeffs = [sum(comb(j, i)*word[j] for j in range(i, P)) % P for i in range(P)]
    result = []
    for i, row in enumerate(powers):
        a = x_coeffs[i]*pow(row[i], -1, P) % P
        result.append(a)
        for j in range(i, P):
            x_coeffs[j] = (x_coeffs[j]-a*row[j]) % P
    assert not any(x_coeffs)
    return result


def to_word(taylor, powers):
    x_coeffs = [sum(a*row[i] for a, row in zip(taylor, powers, strict=True)) % P
                for i in range(P)]
    return [sum((-1)**(j-i)*comb(j, i)*x_coeffs[j] for j in range(i, P)) % P
            for i in range(P)]


def norm_coefficient(u, v, d):
    return sum((-1)**j*(u[d-j]*u[j]+v[d-j]*v[j]) for j in range(d+1)) % P


def complete(target, free_u, free_v):
    assert not target[0] and all(not target[d] for d in range(1, P, 2))
    if not any(target):
        half = (P+1)//2
        return [0]*half+free_u[half:], [0]*half+free_v[half:], None
    degree = next(i for i, v in enumerate(target) if v)
    r = degree//2
    leading = [(a,b) for a in range(P) for b in range(P)
               if (-1)**r*(a*a+b*b) % P == target[degree]]
    assert len(leading) == P+1
    a,b = leading[0]
    u, v = [0]*r+[a]+free_u[r+1:], [0]*r+[b]+free_v[r+1:]
    pivot = u if a else v
    derivative = 2*(-1)**r*pivot[r]
    inverse = pow(derivative, -1, P)
    for d in range(degree+2, P, 2):
        error = target[d]-norm_coefficient(u, v, d)
        k = d-r
        pivot[k] = (pivot[k]+error*inverse) % P
    assert [norm_coefficient(u,v,d) for d in range(P)] == target
    return u, v, r


def project(word):
    return [sum(word[j::P]) for j in range(P)]


def main():
    s = joint_words()
    x, y = tuple(tuple((u+sign*v)//2 for u,v in zip(s[2], reflect(s[3]), strict=True))
                 for sign in (1, -1))
    head = periodic(tuple(project(w) for w in s[:2]))
    difference = [(573 if d == 0 else -26)-w for d,w in enumerate(head)]
    assert all(v % 2 == 0 for v in difference)
    target = [v//2 for v in difference]
    powers = basis()
    converted = to_taylor(target, powers)
    assert to_word(converted, powers) == [v % P for v in target]
    u, v = (to_taylor(project(w), powers) for w in (x,y))
    actual = [norm_coefficient(u,v,d) for d in range(P)]
    lifted = periodic(tuple(project(w) for w in (x,y)))
    assert actual == to_taylor(lifted, powers)
    assert actual != converted
    uu, vv, valuation = complete(converted, u, v)
    proposed = periodic((to_word(uu,powers), to_word(vv,powers)))
    assert [w % P for w in proposed] == [w % P for w in target]
    q = [2*(a-b) for a,b in zip(lifted, target, strict=True)]
    assert sum(v*v for v in q) == 41088 < 4*(8*P)**2
    print("Exact C23 target Taylor valuation", 2*valuation, "leading coefficient",
          converted[2*valuation], "verified.")
    print("Constructed modular phase profiles satisfy all 23 coefficients.")


if __name__ == "__main__":
    main()
