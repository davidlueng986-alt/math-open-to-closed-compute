"""Rebuild the unit-supported short-root exclusion at the width-1215 exterior."""

from pathlib import Path
from subprocess import run
from tempfile import TemporaryDirectory
import json

from r_paley_bucket_extension import SELECTED
from r_paley_isotropic_code import dot, half_projections
from r_paley_lattice_lift import CONTROLS, signs
from r_paley_periodic_skew import DATA
from verify import goethals_seidel, length_299_words, paley, rows_from_columns


def control(t, chosen, lowers):
    m, d = 2*t-2, (t-1)//2
    source = paley(m-1)
    reserve = tuple(i for i in range(m) if i not in chosen)
    decks = [half_projections(source,z) for z in lowers[:6]]
    reordered = [tuple(w[j] for j in chosen+reserve) for w in decks]
    a = tuple((u-v)//2 for u,v in zip(reordered[0],reordered[5],strict=True))
    split = t+1
    assert t*dot(a[:split],a[:split])+dot(a[split:],a[split:]) == 2*t*d
    for i, w in enumerate(reordered[:5]):
        inner = t*dot(a[:split],w[:split])+dot(a[split:],w[split:])
        assert inner == (2*t*d if i == 0 else 0)
    physical = rows_from_columns(m, [source[j] for j in chosen+reserve])
    n = [dot(signs(row,m),a) for row in physical]
    assert all(v % d == 0 for v in n)
    reconstructed = [v - w//d for v,w in zip(signs(lowers[0],m),n,strict=True)]
    assert tuple(reconstructed) == signs(lowers[5],m)
    print(f"Order {4*t}: one norm-two root lifts from five old characteristic lines to a sixth")


def source_data():
    t, m, v = 599, 1196, 596
    old = next(row for row in json.loads(DATA.read_text(encoding="ascii"))["extensions"]
               if row["width"] == 1214)
    rows = old["inner_rows"] + [319]
    pivots = old["inner_columns"] + [344]
    chosen = tuple(j for j in range(m) if SELECTED >> j & 1)
    spare = tuple(j for j in range(m) if not (SELECTED >> j & 1))
    assert len(chosen) == 600 and len(spare) == v
    source = goethals_seidel(length_299_words())
    bottom = [source[g] ^ (1 << r) for r,g in zip(rows,pivots,strict=True)]
    w = [tuple(598-(z^source[j]).bit_count() for j in spare) for z in bottom]
    k = [spare.index(g) for g in pivots]
    assert all(wi[j] == t-2 for wi,j in zip(w,k,strict=True))
    units = [tuple(a-t*(i == j) for i,a in enumerate(wi)) for wi,j in zip(w,k,strict=True)]
    assert all(dot(s,u) == t*(i == j)
               for i,s in enumerate(units) for j,u in enumerate(units))
    assert all(abs(s[j]) == (2 if j == pivot else 1)
               for s,pivot in zip(units,k,strict=True) for j in range(v))
    assert all(dot(s,wi)%t == 0 for s in units for wi in w)
    a0 = [598-(bottom[0]^source[j]).bit_count() for j in chosen]
    assert all(abs(b) == 1 for b in a0)

    x = rows_from_columns(m,[source[j] for j in chosen])
    vrows = rows_from_columns(m,[source[j] for j in spare])
    unit_signs = [sum((b > 0) << j for j,b in enumerate(s)) for s in units]
    lines = [" ".join(map(str,a0))]
    for top, raw in zip(x,vrows,strict=True):
        # The pivot entry is -2 rather than -1.
        prod = [v-2*(raw^s).bit_count()-(2*(raw>>j&1)-1)
                for s,j in zip(unit_signs,k,strict=True)]
        lines.append(" ".join(map(str,(*signs(top,600), *prod))))
    return "\n".join(lines) + "\n"


def verify():
    for t, chosen, lowers in CONTROLS:
        control(t, chosen, lowers)
    src = Path(__file__).with_suffix(".cpp")
    with TemporaryDirectory() as directory:
        binary = Path(directory)/"short_roots"
        run(["g++","-O3","-std=c++20",str(src),"-o",str(binary)],check=True)
        run([str(binary)],input=source_data(),text=True,check=True)


if __name__ == "__main__":
    verify()
