"""Verify forced reserve units, their physical signs, and multiflip controls."""

from collections import Counter
from itertools import combinations
import json
from pathlib import Path

from r_paley_bucket_extension import SELECTED
from r_paley_isotropic_code import assemble, dot, half_projections, maximal_set
from r_paley_order44_classifier import code_signs, reduced_rows
from r_paley_order44_multiclass import DATA as H20_DATA
from r_paley_periodic_skew import DATA as PERIODIC_DATA
from verify import goethals_seidel, length_299_words, paley, rows_from_columns, verify_orthogonal


DATA = Path(__file__).with_name('r_paley_gamma_splitting_data.json')


def sign(word, row):
    return 2*(word >> row & 1)-1


def antipodal(word, height):
    return word if word & 1 else word ^ ((1 << height)-1)


def source_distance(a, b, height):
    distance = (a ^ b).bit_count()
    return min(distance, height-distance)


def reserve_unit(source, unused, row, pivot):
    t = len(source)//2+1
    position = unused.index(pivot)
    z = source[pivot] ^ (1 << row)
    projections = half_projections(source, z)
    w = [projections[j] for j in unused]
    assert w[position] == t-2 and all(abs(x) == 1 for j,x in enumerate(w) if j != position)
    q = [t*(j == position)-x for j,x in enumerate(w)]
    assert dot(q, q) == t
    return z, projections, w, q


def check_fixed_2396():
    t, m = 599, 1196
    source = goethals_seidel(length_299_words())
    prior = next(r for r in json.loads(PERIODIC_DATA.read_text(encoding='ascii'))['extensions']
                 if r['width'] == 1214)
    rows, pivots = prior['inner_rows']+[319], prior['inner_columns']+[344]
    assert len(set(rows)) == len(set(pivots)) == 15
    chosen = [j for j in range(m) if SELECTED >> j & 1]
    unused = [j for j in range(m) if not (SELECTED >> j & 1)]
    assert len(chosen) == 600 and len(unused) == 596
    anchors = [reserve_unit(source, unused, row, pivot) for row,pivot in zip(rows,pivots,strict=True)]
    reserves = [w for _,_,w,_ in anchors]
    units = [q for _,_,_,q in anchors]
    assert all(not dot(q,r) for q,r in combinations(units, 2))
    assert len(reduced_rows(reserves, t)[1]) == 15
    coefficients = [[dot(q,w)//t for w in reserves] for q in units]
    assert all(all(abs(s)==1 for s in row) for row in coefficients)
    for i, (row, pivot, q) in enumerate(zip(rows,pivots,units,strict=True)):
        for j, (z,_,w,_) in enumerate(anchors):
            assert dot(q,w) == t*(sign(source[pivot], row)*sign(z,row) + 2*(i == j))

    x_rows = rows_from_columns(m, [source[j] for j in chosen])
    v_rows = rows_from_columns(m, [source[j] for j in unused])
    old_upper = []
    pivot_positions = [unused.index(j) for j in pivots]
    for (z,projection,_,q), row, pivot, position in zip(anchors,rows,pivots,pivot_positions,strict=True):
        b = [projection[j] for j in chosen]
        assert all(abs(x) == 1 for x in b)
        old_upper.append(b)
        b_bits = sum((value > 0) << j for j,value in enumerate(b))
        q_bits = sum((value > 0) << j for j,value in enumerate(q))
        for i, (xword, vword) in enumerate(zip(x_rows,v_rows,strict=True)):
            vq = len(unused)-2*(vword ^ q_bits).bit_count()+sign(vword,position)
            xb = len(chosen)-2*(xword ^ b_bits).bit_count()
            assert vq == sign(source[pivot],i) + m*sign(source[pivot],row)*(i == row) + xb
    assert all(not dot(b,c) for b,c in combinations(old_upper, 2))

    # K is the skew part of the old unit-coordinate matrix P = I + K.
    skew = [[value-int(i==j) for j,value in enumerate(row)] for i,row in enumerate(coefficients)]
    assert all(skew[i][j] == -skew[j][i] for i in range(15) for j in range(15))
    residual = [tuple(x-sum(coefficients[j][i]*q[h] for j,q in enumerate(units))
                      for h,x in enumerate(w)) for i,w in enumerate(reserves)]
    assert all(not dot(w,q) for w in residual for q in units)
    assert all([j for j,x in enumerate(w) if x % 2] == sorted(pivot_positions) for w in residual)
    for i, a in enumerate(residual):
        for j, b in enumerate(residual):
            expected = 595*(i == j)-dot(skew[i],skew[j])
            assert dot(a,b) == t*expected
    assert (t-1)-(600+15+1)//2 == 290
    print('Order 2396: fifteen forced orthogonal reserve units, physical signs and rank-581 complement verified')


def check_physical_signs_28():
    t, m = 7, 12
    source = paley(11)
    chosen, unused = list(range(8)), list(range(8,12))
    words = [z for z in range(1,1 << m,2) if all(abs(6-(z ^ source[j]).bit_count()) == 1 for j in chosen)]
    projections = [half_projections(source,z) for z in words]
    frame = maximal_set(t, [tuple(w[j] for j in unused) for w in projections], m)
    selected = {words[i] for i in frame}
    assert len(selected) == 12 and verify_orthogonal(28,assemble(t,source,chosen,sorted(selected))) == 378
    for pivot in unused:
        row = next(i for i in range(m) if antipodal(source[pivot]^(1 << i),m) in selected)
        z, _, _, q = reserve_unit(source,unused,row,pivot)
        comparison = selected-{antipodal(z,m)}
        assert sum(all(source_distance(other,word,m)>1 for word in source) for other in comparison) == 4
        for other in comparison:
            w = [half_projections(source,other)[j] for j in unused]
            assert dot(q,w) == t*sign(source[pivot],row)*sign(other,row)
    print('Order 28: four reserve axes recover the physical signs of four genuine multiflip columns')


def check_multiflip_44():
    sources = json.loads(H20_DATA.read_text(encoding='ascii'))
    records = json.loads(DATA.read_text(encoding='ascii'))
    assert [r['source'] for r in records] == [0,1]
    for record in records:
        data = sources[record['source']]
        source = rows_from_columns(20,[int(row,16) for row in data['rows'].split()])
        assert verify_orthogonal(20,source) == 190
        chosen, q, expected = record['chosen'], record['q'], record['words']
        unused = [i for i in range(20) if i not in chosen]
        assert all(dot(c,c) == 11 for c in q) and all(not dot(a,b) for a,b in combinations(q,2))
        assert len(reduced_rows(q,11)[1]) == 4
        assert all(sum(map(abs,row)) == 7 for row in zip(*q,strict=True))
        matrix = []
        for i in range(20):
            row = [sign(c,i) for c in source]
            matrix.append([row[j] for j in chosen]+[dot([row[j] for j in unused],c) for c in q])
        words = []
        for mask in code_signs(matrix):
            word = [1-2*(mask >> i & 1) for i in range(20)]
            lower = [dot(row,word) for row in matrix]
            assert all(abs(x) == 10 for x in lower)
            words.append(antipodal(sum((x > 0) << i for i,x in enumerate(lower)),20))
        assert set(words) == set(expected) and len(words) == 20
        tally = Counter(min(source_distance(z,c,20) for c in source) for z in words)
        assert tally == {3:12,5:8}
        assert verify_orthogonal(44,assemble(11,source,chosen,words)) == 946
        print(f"Order 44 {data['name']}: all 946 products exact, twelve triple-flip and eight quintuple-flip lower lines")


if __name__ == '__main__':
    check_fixed_2396()
    check_physical_signs_28()
    check_multiflip_44()
