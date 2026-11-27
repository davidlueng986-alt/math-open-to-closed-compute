"""Exact pivot-zero selector histograms for the normalized Paley matrices."""
import argparse
from collections import Counter
from hashlib import sha256
from itertools import combinations
import json
import lzma
from math import comb
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "closure-dag"))
from verify_pivot import paley, pivot_matrices, restrict, rows, scatter, supports_intersect


def indexed_design(t):
    columns = paley(4 * t - 1)
    outside_indices = [i for i in range(1, 4 * t) if not (columns[i] & 2)]
    inside_indices = [i for i in range(1, 4 * t) if columns[i] & 2]
    outer = [columns[i] >> 2 for i in outside_indices]
    a, b, positive, negative = pivot_matrices(t, outer, 0)
    inner = {i: (restrict(columns[i] >> 2, positive), restrict(columns[i] >> 2, negative))
             for i in inside_indices}
    return a, b, positive, negative, outside_indices, outer, inner


def packed_rows(columns):
    size = len(columns)
    return [
        sum(((word >> r) & 1) << (4 * (size - 1 - i)) for i, word in enumerate(columns))
        for r in range(size)
    ]


def histogram(column_rows, k):
    # At most k <= 15 ones enter a digit, so adding a row never carries into its neighbor.
    assert 0 <= k < 16
    return Counter(map(sum, combinations(column_rows, k)))


def matching_subsets(packed, k, keys):
    selected = {key: [] for key in keys}
    for support in combinations(range(len(packed)), k):
        key = sum(packed[r] for r in support)
        if key in selected:
            selected[key].append(sum(1 << r for r in support))
    return selected


def file_data(hist, width):
    return ''.join(f'{key:0{width}x}\t{hist[key]}\n' for key in sorted(hist)).encode('ascii')


def inventory(t, destination=None):
    a, b, positive, negative, outside_indices, outside, known = indexed_design(t)
    width, k = len(a), t - 1
    pair = tuple(packed_rows(side) for side in (a, b))
    ha, hb = (histogram(side, k) for side in pair)
    total = comb(width, k)
    assert sum(ha.values()) == sum(hb.values()) == total
    keys = sorted(ha.keys() & hb.keys())
    maps = [matching_subsets(side, k, keys) for side in pair]
    inside_by_vertex = {v: key for key, v in known.items()}
    matches, vertices = [], []
    for key in keys:
        us, vs = (s[key] for s in maps)
        assert (len(us), len(vs)) == (ha[key], hb[key])
        matches.append(dict(signature=f'{key:0{width}x}', a_multiplicity=len(us),
                            b_multiplicity=len(vs), a_masks=us, b_masks=vs))
        vertices.extend((u, v) for u in us for v in vs)
    assert set(inside_by_vertex) <= set(vertices)
    edges = sum(supports_intersect(u, v) == t-2 for u, v in combinations(vertices, 2))
    sides = {}
    for label, count in [('a', ha), ('b', hb)]:
        raw = file_data(count, width)
        entry = dict(subsets=total, distinct=len(count),
                     multiplicity_counts=dict(sorted(Counter(count.values()).items())),
                     uncompressed_bytes=len(raw), sha256=sha256(raw).hexdigest())
        if destination:
            filename = f'h{4*t}-{label}.tsv.xz'
            (destination / filename).write_bytes(lzma.compress(raw, preset=4))
            entry['filename'] = filename
        sides[label] = entry
    def example(vertex):
        u, v = vertex
        mask = scatter(u, positive) | scatter(v, negative)
        assert all((mask & col).bit_count() == k for col in outside)
        return dict(a_rows=rows(u,width), b_rows=rows(v,width),
                    selected_original_zero_based_rows=[r+2 for r in rows(mask, 2*width)],
                    original_inner_column=inside_by_vertex.get(vertex))
    return dict(order=4*t, pivot_index_in_outside=0, original_pivot_column=outside_indices[0],
                original_finite_point_columns=outside_indices[1:],
                positive_original_rows=[r+2 for r in positive], negative_original_rows=[r+2 for r in negative],
                sides=sides, shared_signatures=len(keys), N1=len(vertices), N2=edges,
                known_clique_size=len(known), extra_vertices=len(set(vertices)-set(inside_by_vertex)),
                matches=matches, decoded_examples=[example(vertex) for vertex in vertices[:2]])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=HERE)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    control = inventory(5)
    assert (control['N1'], control['N2']) == (9, 36)
    result = inventory(11, args.output)
    data = dict(order20_control=dict(N1=control['N1'],N2=control['N2']), order44=result)
    (args.output/'atlas.json').write_text(json.dumps(data, indent=2)+'\n')
    print(f"H44 pivot zero: {result['shared_signatures']} shared signatures, "
          f"N1={result['N1']}, N2={result['N2']}, {result['extra_vertices']} extra vertices")
    for name, side in result['sides'].items():
        print(name, side['distinct'], side['sha256'])


if __name__ == '__main__':
    main()
