"""Check that the double-far source admits no third periodic-13 line on the fixed pair."""

from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from r_paley_double_far import build_pair, build_source, fibres
from r_paley_periodic_partner import dot, integer_rows, minus_plus, nary


def channel_data():
    source = build_source()
    raw, _ = build_pair(source)
    groups = fibres()
    g = [
        tuple(sum(2 * ((source[col[0]] >> r) & 1) - 1 for r in row)
              for col in groups)
        for row in groups
    ]
    q = tuple(tuple(2 * ((word >> row[0]) & 1) - 1 for row in groups) for word in raw)
    assert dot(*q) == 0
    reflect = tuple(j // 13 * 13 + 12 - j % 13 for j in range(52))
    assert all(g[i][j] == g[reflect[i]][reflect[j]] for i in range(52) for j in range(52))
    assert all(word == tuple(word[j] for j in reflect) for word in q)
    low = tuple(j for j in range(52) if j < reflect[j])
    fixed = tuple(j for j in range(52) if j == reflect[j])
    cols = tuple(zip(*g))
    values = tuple(tuple(dot(word, c) for c in cols) for word in q)
    shared = {j for j, (a, b) in enumerate(zip(*values, strict=True)) if abs(a) == abs(b) == 2}
    assert len(shared) == 32 and not shared.intersection(fixed)
    sectors = [
        tuple(j for j in low if j in shared and values[0][j] == phase * values[1][j])
        for phase in (1, -1)
    ]
    assert tuple(map(len, sectors)) == (8, 8)
    marks = sectors[0] + sectors[1]
    odd = [tuple((g[i][j] - g[reflect[i]][j]) // 2 for j in marks) for i in low]
    even = [tuple(g[i][j] + g[reflect[i]][j] for j in marks) for i in low]
    even.extend(tuple(g[i][j] for j in marks) for i in fixed)

    # The alternate pair is conjugate in the compressed matrix.
    perm = tuple(13 * (j // 13 ^ 1) + j % 13 for j in range(52))
    signs = tuple((1, -1, 1, -1)[j // 13] for j in range(52))
    assert all(g[perm[i]][perm[j]] == signs[i] * signs[j] * g[i][j]
               for i in range(52) for j in range(52))
    for word, pivot in zip(q, (32, 19), strict=True):
        other = tuple(signs[i] * word[i] for i in perm)
        ref = tuple(1 if v > 0 else -1 for v in cols[perm[pivot]])
        assert other in (ref, tuple(-v for v in ref))
    assert (perm[32], perm[19]) == (45, 6)
    return q, reflect, low, fixed, odd, even


def check_symmetric(q, reflect, low, fixed, even, run):
    output = run("symmetric", integer_rows(even))
    assert output[-1] == "symmetric 1217"
    lines = set()
    for row in output[:-1]:
        label, a, b = row.split()
        assert label == "line"
        bits = minus_plus(int(a), 14) + minus_plus(int(b), 14)
        z = [0] * 52
        for i, value in zip(low, bits[:24], strict=True):
            z[i] = z[reflect[i]] = value
        for i, value in zip(fixed, bits[24:], strict=True):
            z[i] = value
        lines.add(tuple(z))
    assert lines == set(q) and len(output) == 7
    print("Paley double-far periodic: only the two original symmetric lines")


def check_mixed(odd, even, run):
    output = run("odd", integer_rows(odd))
    assert output[-1] == "odd 778694687 54"
    lines = set()
    for row in output[:-1]:
        label, a, b = row.split()
        assert label == "line"
        word = tuple(x - 1 for x in nary(int(a), 3, 12) + nary(int(b), 3, 12))
        assert len(word) == 24 and next(x for x in word if x) == 1
        lines.add(word)
    assert len(lines) == 54
    batches = []
    for word in sorted(lines):
        p = tuple(dot(word, col) for col in zip(*odd))
        assert sum(abs(v) <= 1 for v in p[:8]) >= 6
        assert sum(abs(v) <= 1 for v in p[8:]) >= 6
        matrix = [even[i] for i, value in enumerate(word) if not value] + even[24:]
        batches.append(integer_rows([(len(matrix),), p, *matrix]))
    output = run("complete", str(len(batches)) + "\n" + "".join(batches))
    assert output == ["complete 360 0"]
    print("Paley double-far periodic: 778694687 odd matches, 54 possible nonzero odd lines")
    print("Paley double-far periodic: 360 even matches, no third period-13 line")


def verify():
    q, reflect, low, fixed, odd, even = channel_data()
    with TemporaryDirectory() as tmp:
        exe = Path(tmp) / "double-far-periodic"
        worker = Path(__file__).with_suffix(".cpp")
        subprocess.run(["g++", "-O3", "-std=c++17", str(worker), "-o", str(exe)], check=True)

        def run(mode, inp):
            return subprocess.run([str(exe), mode], input=inp, text=True, check=True,
                                  capture_output=True).stdout.splitlines()

        check_symmetric(q, reflect, low, fixed, even, run)
        check_mixed(odd, even, run)


if __name__ == "__main__":
    verify()
