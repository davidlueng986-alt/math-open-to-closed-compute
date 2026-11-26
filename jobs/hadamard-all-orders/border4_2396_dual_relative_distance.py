"""Replay the exact signed lower bound on relative changes in the two last rows."""

from collections import Counter, defaultdict, deque
from functools import reduce
from operator import xor
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from border4_2396_dual_quotient import MORE_MOD16, dual_words
from border4_2396_full_y_expanded import incident, indices, occupy, reducer, reflect

N, X, Y = 299, 13, 23
EXPECTED = [
    "cycles 4 583 compatible 0",
    "cycles 6 15888 compatible 0",
    "cycles 8 414392 compatible 0",
    "cycles 10 9834135 compatible 1",
    "cycles 12 204298996 compatible 15",
    "union 8 hits (by decomposition) 0",
    "union 10 hits (by decomposition) 0",
    "union 12 hits (by decomposition) 16",
    "union 12 hits (by decomposition) 8",
    "union three-four hits 3",
]
UNIQUE = (7, 47, 95, 122, 178, 187, 190, 277, 282, 293)


def support_cycles(support):
    tree = defaultdict(list)
    roots = list(range(X+Y))

    def root(node):
        while node != roots[node]:
            node = roots[node]
        return node

    chords = []
    for i in sorted(support):
        a, b = i % X, X+i % Y
        u, v = root(a), root(b)
        if u == v:
            chords.append(i)
        else:
            roots[u] = v
            tree[a].append((b, i))
            tree[b].append((a, i))
    masks = []
    for i in chords:
        a, b = i % X, X+i % Y
        stack = [(a, -1, 0)]
        while stack:
            u, parent, mask = stack.pop()
            if u == b:
                masks.append(mask ^ (1 << i))
                break
            stack.extend((v, u, mask ^ (1 << j)) for v, j in tree[u] if v != parent)
        else:
            raise AssertionError("missing tree path")
    return masks


def prepare(rows):
    supports = [occupy(w) for w in rows]
    assert supports[2] == occupy(reflect(rows[3]))
    columns = [{i: incident(p,i) for i in p} for p in supports]
    cycles = [support_cycles(p) for p in supports]
    images = [tuple(reduce(xor,(col[i] for i in indices(a)),0) for a in base)
              for col,base in zip(columns,cycles,strict=True)]
    assert list(map(len, cycles)) == [129, 138, 95, 95]
    assert [reducer(enumerate(row))[0] for row in images] == [79, 83, 95, 95]
    rank, eliminate = reducer(enumerate(images[0]+images[1]))
    assert rank == 107
    assert reducer(enumerate(images[2]+images[3]))[0] == 95
    assert reducer(enumerate(sum(images, ())))[0] == 131
    assert reducer((i, eliminate(c)[0]) for i,c in enumerate(images[2]))[0] == 24

    sites = sorted(supports[2])
    projected = [eliminate(columns[2][i])[0] for i in sites]
    slots = sorted({j for v in projected for j in indices(v)})
    assert len(slots) <= 64
    packed = [sum((v >> j & 1) << k for k,j in enumerate(slots)) for v in projected]
    data = "".join(f"{i % X} {i % Y} {v}\n" for i,v in zip(sites,packed,strict=True))
    return sites, data


def positive_counts(word, support, modulus):
    return [(sum(word[j::modulus])+sum(i % modulus == j for i in support))//2
            for j in range(modulus)]


def transportable(word, support):
    sizes = [sum(i % p == j for i in support) for p in (X,Y) for j in range(p)]
    margins = [sum(word[j::p]) for p in (X,Y) for j in range(p)]
    if any(abs(m) > n or (m+n) % 2 for m,n in zip(margins,sizes,strict=True)):
        return False
    source, sink = X+Y, X+Y+1
    residual = [[0]*(sink+1) for _ in range(sink+1)]
    left, right = (positive_counts(word,support,p) for p in (X,Y))
    assert sum(left) == sum(right)
    for x,q in enumerate(left):
        residual[source][x] = q
    for y,q in enumerate(right):
        residual[X+y][sink] = q
    for i in support:
        residual[i % X][X+i % Y] = 1
    for _ in range(sum(left)):
        parent = {source: -1}
        queue = deque([source])
        while queue and sink not in parent:
            i = queue.popleft()
            for j,cap in enumerate(residual[i]):
                if cap and j not in parent:
                    parent[j] = i
                    queue.append(j)
        if sink not in parent:
            return False
        j = sink
        while j != source:
            i = parent[j]
            residual[i][j] -= 1
            residual[j][i] += 1
            j = i
    return True


def affine_caps(rows):
    result = []
    for row in rows:
        arcs = []
        for i, sign in enumerate(row):
            if sign:
                x, y = i % X, X+i % Y
                arcs.append((x,y) if sign > 0 else (y,x))
        reachable = [{i} for i in range(X+Y)]
        for i,j in arcs:
            reachable[i].add(j)
        for k in range(X+Y):
            for row_reach in reachable:
                if k in row_reach:
                    row_reach.update(reachable[k])
        flexible = [(i,j) for i,j in arcs if i in reachable[j]]
        incoming = Counter(j for i,j in flexible)
        outgoing = Counter(i for i,j in flexible)
        cap_x = sum(min(incoming[i],outgoing[i]) for i in range(X))
        cap_y = sum(min(incoming[i],outgoing[i]) for i in range(X,X+Y))
        result.append((len(flexible),cap_x,cap_y,min(cap_x,cap_y)//2))
    return result


def main():
    rows = dual_words()
    sites, data = prepare(rows)
    with TemporaryDirectory() as directory:
        binary = Path(directory) / "relative-distance"
        subprocess.run(["g++", "-O3", "-std=c++20",
                        str(Path(__file__).with_suffix(".cpp")), "-o", str(binary)], check=True)
        output = subprocess.check_output([str(binary)], input=data, text=True).splitlines()
    hits = [line for line in output if "hit " in line]
    assert [line for line in output if "hit " not in line] == EXPECTED
    masks = Counter()
    for line in hits:
        fields = line.split("hit ")[1].split()
        size, *where = map(int, fields)
        masks[size, tuple(sites[i] for i in where)] += 1
    short = {m for size,m in masks if size < 12}
    assert short == {UNIQUE}

    aligned = reflect(rows[3])
    x, y = (tuple((a+sign*b)//2 for a,b in zip(rows[2],aligned,strict=True)) for sign in (1,-1))
    ys = occupy(y) ^ set(UNIQUE)
    y_counts = positive_counts(y,ys,Y)
    assert positive_counts(y,ys,X)[5] == 5
    assert sum(y_counts[i % Y] > 0 for i in ys if i % X == 5) == 4

    candidates = [m for size,m in masks if size == 12]
    assert len(candidates) == 38
    valid = Counter((transportable(x,occupy(x)^set(m)),
                     transportable(y,occupy(y)^set(m))) for m in candidates)
    assert valid == {(False,False):20, (True,True):3, (False,True):10, (True,False):5}
    print("Minimum relative-tail weight at least 12; 3 weight-12 masks pass both tail flows.")
    expected_caps = [(160,64,64,32), (169,71,69,34), (92,31,28,14), (126,47,45,22)]
    assert affine_caps(rows) == affine_caps(dual_words(MORE_MOD16)) == expected_caps
    assert sum(r[-1] for r in expected_caps) == 102
    print("Fixed-margin physical affine dimension at most 102.")


if __name__ == "__main__":
    main()
