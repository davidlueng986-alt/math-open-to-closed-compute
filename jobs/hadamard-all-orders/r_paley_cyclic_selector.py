"""Verify new cyclic T23 selectors and replay a mixed two-far witness."""

from collections import Counter, defaultdict
from hashlib import sha256
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from r_paley_double_far import WILLIAMSON, build_pair, dot, fibres
from r_paley_double_far_nonperiodic import TARGET_SUMS
from r_paley_far_family import quaternion_basis
from r_paley_isotropic_code import assemble, half_projections, rank_mod
from r_paley_period23_support import affine_representatives, selector_family
from verify import goethals_seidel, signs, verify_orthogonal


PERIOD = 23
MASK = (1 << PERIOD) - 1
EDITED_SELECTOR = (-2, -2, -3, -2, 3, -2, 2, -3, -2, -3, 2, -3, -4,
                   -1, 4, 1, 4, 1, -4, -4, -3, 3, -4)
EDITED_ROWS = (903, 981)
DIGEST = "2f73b18c201bb27e89f745416a8c0bd1e15020bf6a9956822f833f35d3e6b070"
PHASE_MAPS = tuple(tuple((a * x + b) % PERIOD for x in range(PERIOD))
                   for a in range(1, PERIOD) for b in range(PERIOD))


def signed_selector(entries):
    return tuple((abs(v) - 1, 1 if v > 0 else -1) for v in entries)


def phase_code(selector):
    return bytes(2 * unit + (phase > 0) for unit, phase in selector)


def decode_code(code):
    return tuple((v // 2, 2 * (v % 2) - 1) for v in code)


def orbit(code):
    return {bytes(code[i] for i in phase) for phase in PHASE_MAPS}


def cyclic(selector):
    assert len(selector) == PERIOD and all(0 <= u < 4 and s in (-1, 1) for u, s in selector)
    assert tuple(sum(s for j, s in selector if j == u) for u in range(4)) == TARGET_SUMS
    assert all(sum(s * t for (u, s), (v, t) in zip(selector, selector[d:] + selector[:d], strict=True)
                   if u == v) == 0 for d in range(1, 12))


def isometries(unit):
    copies = set()
    reflected = tuple(sum((m >> i & 1) << (-i % PERIOD) for i in range(PERIOD)) for m in unit)
    for word in (unit, reflected):
        for d in range(PERIOD):
            copies.add(tuple((m << d | m >> (PERIOD - d)) & MASK for m in word))
    return copies


def support_codes(selector):
    words = tuple(tuple(sum(1 << i for i, (j, s) in enumerate(selector) if j == u and s == v)
                        for v in (1, -1)) for u in range(4))
    a, b, c, d = sorted(range(4), key=lambda u: sum(m.bit_count() for m in words[u]), reverse=True)
    fixed = words[a][0] | words[a][1]
    middle = [{(p | m, (p, m)) for p, m in isometries(words[u]) if not (fixed & (p | m))}
              for u in (b, c)]
    tail = defaultdict(list)
    for p, m in isometries(words[d]):
        if not (fixed & (p | m)):
            tail[p | m].append((p, m))
    chosen = list(words)
    for first, word_b in middle[0]:
        chosen[b] = word_b
        for second, word_c in middle[1]:
            if first & second:
                continue
            chosen[c] = word_c
            for word_d in tail[MASK ^ (fixed | first | second)]:
                chosen[d] = word_d
                out = bytearray(PERIOD)
                for u, pair in enumerate(chosen):
                    for sign, active in zip((1, 0), pair, strict=True):
                        while active:
                            bit = active & -active
                            out[bit.bit_length() - 1] = 2 * u + sign
                            active ^= bit
                yield bytes(out)


def new_classes(old, candidates):
    remaining = old | candidates
    previous = 0
    novel = []
    for code in sorted(remaining):
        if code not in remaining:
            continue
        same = orbit(code)
        remaining.difference_update(same)
        if same & old:
            previous += 1
        else:
            novel.append(code)
    return previous, novel


def redistributions(representatives):
    old = set(map(phase_code, representatives))
    expanded = set()
    for t in representatives:
        expanded.update(support_codes(t))
    assert old <= expanded and len(expanded) == 5982
    for t in expanded:
        cyclic(decode_code(t))
    previous, novel = new_classes(old, expanded)
    assert previous == 4416 and len(novel) == 16
    return novel


def neighbours(representatives, shifted, worker):
    seeds = list(map(phase_code, representatives)) + shifted
    payload = [str(len(seeds)) + "\n"]
    for i, code in enumerate(seeds):
        entries = " ".join(str((u + 1) * s) for u, s in decode_code(code))
        payload.append(f"{i} {entries}\n")
    run = subprocess.run([str(worker), "all"], text=True, input="".join(payload),
                         check=True, capture_output=True)
    assert run.stderr.strip() == "sources 4432 checked 33605648 passed 5736"
    items = Counter()
    for line in run.stdout.splitlines():
        row = tuple(map(int, line.split()))
        seed, distance, *values = row
        code = phase_code(signed_selector(values))
        assert sum(x != y for x, y in zip(code, seeds[seed], strict=True)) == distance
        assert distance in (2, 3)
        items[code, distance] += 1
    candidates = {word for word, _ in items}
    assert len(candidates) == 3892 and sum(items.values()) == 5736
    for code in candidates:
        cyclic(decode_code(code))
    previous, novel = new_classes(set(seeds), candidates)
    assert previous == 4432 and len(novel) == 60
    witness = phase_code(signed_selector(EDITED_SELECTOR))
    assert witness in candidates and any(witness in orbit(t) for t in novel)
    return novel


def verify_witness():
    selector = signed_selector(EDITED_SELECTOR)
    cyclic(selector)
    assert sum(s * t for (u, s), (v, t) in zip(selector, selector[4:]) if u == v) == 1
    units = [quaternion_basis(*row) for row in zip(*map(signs, WILLIAMSON), strict=True)]
    words = [[s * units[i % 13][u][j] for i in range(299)
              for u, s in (selector[i % PERIOD],)] for j in range(4)]
    assert all(sum(w[i] * w[(i + d) % 299] for w in words for i in range(299)) == 0
               for d in range(1, 299))
    source = goethals_seidel(words)
    assert verify_orthogonal(1196, source) == 714610
    (first, second), _ = build_pair(source)
    first ^= sum(1 << r for r in EDITED_ROWS)
    b = EDITED_ROWS[0] // 299
    assert all(r // 299 == b for r in EDITED_ROWS)
    assert any(len({first >> (299 * b + t) & 1 for t in range(r, 299, 13)}) == 2 for r in range(13))
    assert any(len({first >> (299 * b + t) & 1 for t in range(r, 299, PERIOD)}) == 2
               for r in range(PERIOD))
    decks = [[dot(w, c) for c in source] for w in (first, second)]
    assert tuple((1196 - max(map(abs, d))) // 2 for d in decks) == (481, 483)
    assert dot(first, second) == -4
    same, opposite = [[j for j, (x, y) in enumerate(zip(*decks, strict=True)) if abs(x) == 2 and x == s * y]
                      for s in (1, -1)]
    assert (len(same), len(opposite)) == (304, 312)
    kept = sorted(same[:301] + opposite[:299])
    cols = assemble(599, source, kept, (first, second))
    assert len(cols) == 1202 and verify_orthogonal(2396, cols) == 721801
    reserve = sorted(set(range(1196)) - set(kept))
    values = [tuple(p[i] for i in reserve) for p in (half_projections(source, z) for z in (first, second))]
    assert rank_mod(values, 599) == 2
    assert sha256(b"".join(c.to_bytes(300, "little") for c in cols)).hexdigest() == DIGEST
    print("Cyclic selector witness: 2396 x 1202, 721801 exact pairs, distances 481 and 483", flush=True)
    print("SHA256", DIGEST)


def verify():
    directory = Path(__file__).parent
    with TemporaryDirectory() as temporary:
        base_exe = Path(temporary) / "base-sequences"
        worker = Path(temporary) / "cyclic-selectors"
        for out, src in ((base_exe, directory / "r_paley_period23_support.cpp"),
                         (worker, Path(__file__).with_suffix(".cpp"))):
            subprocess.run(["g++", "-O3", "-std=c++17", str(src), "-o", str(out)], check=True)
        bases = subprocess.run([str(base_exe), "bases"], check=True, text=True, capture_output=True).stdout
        reps = affine_representatives(selector_family(bases))
        shifted = redistributions(reps)
        extra = neighbours(reps, shifted, worker)
        print("Cyclic selector classes: 16 independent redistributions and 60 exact short-edit classes",
              flush=True)
        assert len(shifted) + len(extra) == 76
        verify_witness()


if __name__ == "__main__":
    verify()
