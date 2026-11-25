"""Verify folded Paley row information sets and the E2112 mod-five support lane."""
from collections import Counter
import json
from pathlib import Path

from stack_1197 import LOWER_FLIPS, LOWER_OMITTED, UPPER_FLIPS, flipped_column, source_matrices
from stack_1198_channels import match_anti_first, signatures
from stack_1198_joint import lower_channels
from verify import paley


def bit_sign(word, i):
    return 2*(word >> i & 1)-1


def raw_pairing(words):
    upper, lower = source_matrices()
    n, m = len(upper), len(lower)
    u = flipped_column(n, UPPER_FLIPS)
    v = flipped_column(m, LOWER_FLIPS)
    x = upper[words['upper_pivot']] ^ sum(1 << i for i in words['upper_flips'])
    lower, y = lower_channels(lower, v, words)
    a, deck_a = signatures(upper, u, x)
    b, deck_b = signatures(lower, v, y)
    residues = [0] * m
    for i, j in match_anti_first(deck_a, deck_b).items():
        a1, a2 = a[i]
        b1, b2 = b[j]
        sign = -1 if (a1 or a2) * (b1 or b2) > 0 else 1
        assert a1 + sign * b1 == 0
        residues[j] = sign * a2 + b2
    return deck_b, residues


class Basis:
    """Incremental Gaussian elimination over a prime field."""
    def __init__(self, size, prime=5):
        self.profile = [None] * size
        self.rank = 0
        self.prime = prime

    def reduce(self, vector):
        p = self.prime
        v = [value % p for value in vector]
        for i, x in enumerate(v):
            if not x:
                continue
            pivot = self.profile[i]
            if pivot is None:
                inv = pow(x, -1, p)
                return i, [d * inv % p for d in v[i:]]
            for j, d in enumerate(pivot, i):
                v[j] = (v[j] - x * d) % p

    def install(self, pivot):
        index, vector = pivot
        assert self.profile[index] is None
        self.profile[index] = vector
        self.rank += 1

    def add(self, vector):
        pivot = self.reduce(vector)
        if pivot is None:
            return False
        self.install(pivot)
        return True


def main():
    src = Path(__file__).with_name('stack_1198_channels_data.json')
    words = json.loads(src.read_text(encoding='ascii'))
    lower_deck, res = raw_pairing(words)
    assert not any(res[600:]) and sum(d*d for d in res)==2112 and max(map(abs,res))==8
    s=[i for i,r in enumerate(res[:600]) if r]
    assert len(s)==117
    p=paley(599)
    def vector(col):return [bit_sign(p[col],i) for i in range(600)]
    basis=Basis(600)
    assert all(basis.add(vector(col)) for col in s)
    assert basis.rank==117
    # Keep the residual support unanchored and add columns with rare first-pair signatures first.
    counts=Counter(lower_deck[:600])
    omitted=set(LOWER_OMITTED)
    extension=sorted(set(range(600))-set(s),key=lambda i:(i in omitted,counts[lower_deck[i]],i))
    chosen=s.copy()
    for col in extension:
        if basis.add(vector(col)):chosen.append(col)
        if basis.rank==300:break
    assert len(chosen)==300 and set(s)<=set(chosen)
    protected=sorted(set(range(600))-set(chosen)-omitted)
    assert not set(s)&set(protected)
    assert len(protected)==297
    assert not set(chosen)&omitted
    transformed=tuple(sum(res[col]//4*bit_sign(p[col],row) for col in s) for row in range(600))
    assert sum(v*v for v in transformed)==600*(2112//16)
    assert any(v%5 for v in transformed)
    print('Paley mod5 support: rank 117 extended to rank 300; 896 protected retained slots')

    # In the normalized matrix, column/row 0 is the added infinity coordinate.
    for rowset in (range(1,301), range(300)):
        image=Basis(600)
        for i in rowset:
            assert image.add([bit_sign(col,i) for col in p])
        assert image.rank==300
    print('Paley mod25: two explicit 300-row information sets checked')


if __name__=='__main__':main()
