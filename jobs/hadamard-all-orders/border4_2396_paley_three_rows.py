"""Invert a primitive norm for corrections supported on three CRT rows."""
from collections import Counter
from itertools import combinations, permutations
import argparse

from sage.all import GF, PolynomialRing, matrix, vector

from border4_2396_dual_mod5_forest import FACTORS_5, check_factors
from border4_2396_paley_directed_gate import SPECTRAL_FIXTURES, SPECTRAL_HEAD
from border4_2396_paley_negative_norm import N, sign_word
from border4_2396_paley_q13_mod16 import margins


def determinant(rows, ring):
    size = len(rows)
    value = ring.zero()
    for perm in permutations(range(size)):
        term = ring.one()
        for row, col in enumerate(perm):
            term *= rows[row][col]
            if not term:
                break
        parity = sum(a>b for i,a in enumerate(perm) for b in perm[i+1:])
        value += (-1 if parity % 2 else 1)*term
    return value


def resultant(f, g, ring):
    m, n = f.degree(), g.degree()
    assert m >= 0 and n >= 0 and m+n <= 5
    a = [ring(f[m-j]) for j in range(m+1)]
    b = [ring(g[n-j]) for j in range(n+1)]
    rows = [
        [ring.zero()]*i + a + [ring.zero()]*(n-1-i) for i in range(n)
    ] + [
        [ring.zero()]*i + b + [ring.zero()]*(m-1-i) for i in range(m)
    ]
    return determinant(rows, ring)


class ThreeRows:
    def __init__(self, coeffs, words):
        self.prime = GF(5)
        modulus = PolynomialRing(self.prime, "z")(coeffs)
        self.field = GF(5**44, "z", modulus=modulus, impl="pari_ffelt")
        root = self.field.gen()
        alpha, beta = root**92, root**208
        self.row_powers = tuple(alpha**x for x in range(13))
        self.negative_row_powers = tuple(1/value for value in self.row_powers)
        self.coordinates = matrix([self.vector(beta**j) for j in range(22)]).transpose()
        assert self.coordinates.rank() == 22
        self.forward = tuple(sum(c*root**i for i,c in enumerate(word)) for word in words)
        self.backward = tuple(sum(c*root**(-i) for i,c in enumerate(word)) for word in words)
        uf,vf,_ = self.forward
        ur,vr,_ = self.backward
        self.target = (1196-uf*ur-vf*vr)/2
        self.grid = tuple(tuple(words[2][(92*x+208*y) % N] for y in range(23)) for x in range(13))
        self.root = root
        self.xr = PolynomialRing(self.field, 'X')
        self.yr = PolynomialRing(self.xr, 'Y')

    def vector(self, value):
        polynomial = value.polynomial()
        return vector(self.prime, [polynomial[j] for j in range(44)])

    def orbit(self, value):
        return value**(5**11)

    def conjugate(self, value):
        return value**(5**22)

    def control(self, w):
        x,y = (0,1)
        a = tuple(self.grid[y][j]-self.grid[x][j] for j in range(23))
        cols = (a.index(2),a.index(-2))
        changed = list(w)
        for j in cols:
            i1,i2 = ((92*r+208*j) % N for r in (x,y))
            changed[i1],changed[i2] = changed[i2],changed[i1]
        assert all(margins((changed,), q) == margins((w,), q) for q in (13,23))
        fwd = sum(c*self.root**i for i,c in enumerate(changed))
        rev = sum(c*self.root**(-i) for i,c in enumerate(changed))
        return fwd*rev, {(r,j) for r in (x,y) for j in cols}

    def parameters(self, tail, rows):
        x0, x1, x2 = rows
        a1, a2 = (self.row_powers[x]-self.row_powers[x0] for x in (x1,x2))
        b1, b2 = (self.negative_row_powers[x]-self.negative_row_powers[x0] for x in (x1,x2))
        a, b = self.orbit(a1), self.orbit(a2)
        aa, bb = map(self.conjugate, (a,b))
        d = a*bb-aa*b
        assert d
        u = (b1*bb-b2*aa)/d
        v = (a*b2-b*b1)/d
        wf, wr = tail
        sf = self.orbit(wf)
        w = wr-u*sf-v*self.conjugate(sf)
        return a1,a2,u,v,w

    def reconstruct(self, z, wf, a, b, rows):
        offset=z-wf
        r, ar, br = map(self.conjugate, (offset,a,b))
        det=a*br-ar*b
        assert det
        ts=((offset*br-r*b)/det,(a*r-ar*offset)/det)
        vectors=[]
        for t in ts:
            coeffs=list(self.coordinates.solve_right(self.vector(t)))+[self.prime.zero()]
            common=sum(coeffs)/self.prime(23)
            values=tuple({0:0,2:2,3:-2}.get(int(c-common)) for c in coeffs)
            if any(value is None for value in values) or sum(values):
                return None
            vectors.append(values)
        v1,v2=vectors
        differences=(tuple(-a-b for a,b in zip(v1,v2)),v1,v2)
        proposed=tuple(tuple(self.grid[x][j]+diff[j] for j in range(23))
                    for x,diff in zip(rows,differences))
        if any(value not in (1,-1) for row in proposed for value in row):
            return None
        changed=tuple((row,j) for row,diff in zip(rows,differences) for j,c in enumerate(diff) if c)
        return changed

    def solve_three(self, rows, target=None):
        if target is None:
            target=self.target
        assert target
        wf,wr=self.forward[2],self.backward[2]
        a,b,u,v,w=self.parameters((wf,wr),rows)
        vals=[(u,v,w,target)]
        for _ in range(3):
            vals.append(tuple(self.orbit(value) for value in vals[-1]))
        (u0,v0,w0,t0),(u1,v1,w1,t1),(u2,v2,w2,t2),(u3,v3,w3,t3)=vals
        x=self.yr(self.xr.gen())
        y=self.yr.gen()
        d0=w0+u0*x+v0*y
        d2=w2+u2*y+v2*x
        common=d0*d2
        f=(w1*x-t1)*common+x*(u1*t2*d0+v1*t0*d2)
        g=(w3*y-t3)*common+y*(u3*t0*d2+v3*t2*d0)
        h=resultant(f,g,self.xr)
        assert h.degree() == 7
        candidates=set()
        for x0 in h.roots(multiplicities=False):
            if not x0:
                continue
            z=self.conjugate(self.orbit(x0))
            y0=self.conjugate(x0)
            if z*(u*x0+v*y0+w)==target:
                candidates.add(z)
        physical=tuple(found for z in candidates if (found:=self.reconstruct(z,wf,a,b,rows)) is not None)
        return h.degree(),len(candidates),physical


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--factor", type=int, choices=range(3))
    args = parser.parse_args()
    check_factors()
    words = tuple(map(sign_word, (*SPECTRAL_HEAD, SPECTRAL_FIXTURES[0][1])))
    expected = ((110,113,43,14,6), (126,101,42,14,3), (119,85,54,25,3))
    indices = range(3) if args.factor is None else (args.factor,)
    for i in indices:
        inv = ThreeRows(FACTORS_5[i], words)
        target, control = inv.control(words[2])
        _, _, physical = inv.solve_three((0,1,2), target)
        assert any(set(value) == control for value in physical)
        counts = Counter()
        for rows in combinations(range(13), 3):
            degree, candidates, physical = inv.solve_three(rows)
            assert degree == 7 and not physical
            counts[candidates] += 1
        assert counts == Counter(dict(enumerate(expected[i])))
        print(f"Factor {i}: algebraic candidate frequencies {tuple(counts[j] for j in range(5))}; "
              "no physical solutions and positive control recovered", flush=True)


if __name__ == "__main__":
    main()
