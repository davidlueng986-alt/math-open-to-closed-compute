"""Replay the two-sum far-word construction at orders 188 and 4604."""

from hashlib import sha256

from r_paley_far_periodic import PERIODS
from r_paley_isotropic_code import assemble
from verify import goethals_seidel, length_299_words, signs, verify_orthogonal


BASE_SEQUENCES = {
    1: ("+++", "-++", "-+", "-+"),
    3: ("--+++++++++-+", "++--+-+-+--++", "--+++-+-+--+", "--++++--+--+"),
}
DIGESTS = {
    0: "52c3e2cfe33d9186841dd733d866923033d1db23a7c197d88a705cb1510b9d55",
    3: "5279c2eff8275b2c5bee7d1cc2cbef92e3ea3aeb10c7c648fd9122cb57410365",
}


def quaternion_basis(a, b, c, d):
    return ((a,b,c,d), (-b,a,-d,c), (-c,d,a,-b), (-d,-c,b,a))


def selectors(s):
    if s == 0:
        return [(0,1)]
    source = tuple(map(signs,BASE_SEQUENCES[s]))
    n = s*(s+1)
    assert tuple(map(len,source)) == (n+1,n+1,n,n)
    for shift in range(1,n+1):
        assert sum(word[i]*word[i+shift]
                   for word in source for i in range(len(word)-shift)) == 0
    return [(2*pair+int(a!=b), a)
            for pair in range(2)
            for a,b in zip(*source[2*pair:2*pair+2],strict=True)]


def product_words(selector, units):
    words = [[], [], [], []]
    for i in range(23 * len(selector)):
        unit, phase = selector[i % len(selector)]
        for word, value in zip(words, units[i % 23][unit], strict=True):
            word.append(phase * value)
    return words


def verify():
    # The CRT samples have residue 0 modulo 13, where the original selector
    # is the positive identity. They recover the original Williamson words.
    length299 = length_299_words()
    units = [quaternion_basis(*(w[13*(16*y % 23)] for w in length299))
             for y in range(23)]
    words = [tuple(row[0][j] for row in units) for j in range(4)]
    assert all(all(w[y] == w[-y % 23] for y in range(23)) for w in words)
    assert all(sum(w[y]*w[(y+d)%23] for w in words for y in range(23)) == 0
               for d in range(1,23))
    reduced = sum((symbol == "+") << i for i,symbol in enumerate("".join(PERIODS)))
    transforms = [
        goethals_seidel([[row[unit][j] for row in units] for j in range(4)])
        for unit in (0,1)
    ]
    b,c = [[92-2*(reduced ^ col).bit_count() for col in h] for h in transforms]
    assert sum(x == -y and abs(x) == 2 for x,y in zip(b,c,strict=True)) == 49
    assert max(map(abs,b)) == max(map(abs,c)) == 46
    assert any(x == y and abs(x) == 46 for x,y in zip(b,c,strict=True))

    for s in (0,1,3):
        select = selectors(s)
        size = 2*s*(s+1)+1
        assert len(select) == size
        assert [sum(v for k,v in select if k == j) for j in range(4)] == [s+1,s,0,0]
        d = size*23
        m,t = 4*d, 46*size+1
        source = goethals_seidel(product_words(select,units))
        assert len(source) == m and verify_orthogonal(m,source) == m*(m-1)//2
        raw = sum((PERIODS[r//d][(r%d)%23] == "+") << r for r in range(m))
        projected = [m-2*(raw ^ col).bit_count() for col in source]
        indices = [(j//d)*23+(j%d)%23 for j in range(m)]
        assert projected == [(s+1)*b[i]+s*c[i] for i in indices]
        eligible = [j for j,value in enumerate(projected) if abs(value) == 2]
        assert len(eligible) == 49*size >= t+1
        nearest = (m-max(map(abs,projected)))//2
        assert nearest == 92*s*s+46*s+23
        if s not in DIGESTS:
            print(f"Far family raw source: t={t}, {len(eligible)} eligible, signed distance {nearest}")
            continue
        matrix = assemble(t,source,eligible[:t+1],[raw])
        checked = verify_orthogonal(4*t,matrix)
        assert len(matrix) == 2*t+3 and checked == len(matrix)*(len(matrix)-1)//2
        digest = sha256(b"".join(col.to_bytes((4*t+7)//8,"little") for col in matrix)).hexdigest()
        assert digest == DIGESTS[s]
        print(f"Far family: {4*t} x {len(matrix)}, {len(eligible)} eligible, "
              f"signed distance {nearest}, all {checked} pair products zero")


if __name__ == "__main__":
    verify()
