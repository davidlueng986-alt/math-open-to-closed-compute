"""Replay the period-23 support bound and the paired-base selector sweep."""

from itertools import combinations, permutations, product
from math import isqrt
from pathlib import Path
import json
import subprocess
from tempfile import TemporaryDirectory

from r_paley_double_far import BLOCK, SELECTOR, SIDE, WILLIAMSON, build_source, dot, fibres
from r_paley_double_far_nonperiodic import TARGET_SUMS
from r_paley_far_family import quaternion_basis
from verify import signs


SPECIAL = (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12)
SHELL_COUNTS = (0, 3, 13, 44, 131, 348, 845, 1401, 2432, 4182)


def shell(length, norm=529, start=1):
    if length == 1:
        root = isqrt(norm)
        if root >= start and root * root == norm:
            yield (root,)
        return
    for initial in range(start, isqrt(norm // length) + 1):
        for rest in shell(length - 1, norm - initial * initial, initial):
            yield (initial, *rest)


def gauge_masks(patterns, columns):
    pivot, *others = columns
    masks = [0] * (1 << len(others))
    for i, pattern in enumerate(patterns):
        code = sum((pattern[pivot] != pattern[j]) << bit for bit, j in enumerate(others))
        masks[code] |= 1 << i
    return masks


def filter_shell(length):
    patterns = tuple((1, *row) for row in product((-1, 1), repeat=length - 1))
    pairs, triples, quartets = (tuple(combinations(range(length), k)) for k in (2, 3, 4))
    requirements = [tuple(mask for group in groups for mask in gauge_masks(patterns, group))
                    for groups in (pairs, triples, quartets)]
    census = [0, 0, 0, 0]
    good = {}
    low_bits = [(i & -i).bit_length() - 1 for i in range(1, len(patterns))]
    for r in shell(length):
        census[0] += 1
        sums = [r[0] - sum(r[1:])]
        mask = int(abs(sums[0]) == 23)
        for i, bit in enumerate(low_bits, 1):
            value = sums[i & (i - 1)] + 2 * r[-1 - bit]
            sums.append(value)
            if abs(value) == 23:
                mask |= 1 << i
        for level, requirement in enumerate(requirements, 1):
            if any(not (mask & needed) for needed in requirement):
                break
            census[level] += 1
        else:
            allowed = tuple(row for i, row in enumerate(patterns) if mask >> i & 1)
            good[r] = tuple(tuple(row[i] * row[j] for i, j in pairs) for row in allowed), allowed
    return census, good


def verify_shell():
    certificate = json.loads(Path(__file__).with_suffix(".json").read_text(encoding="ascii"))
    for length, expected in enumerate(SHELL_COUNTS, 2):
        seen, good = filter_shell(length)
        assert seen[0] == expected
        if length < 11:
            assert not good
    excluded = {tuple(map(int, k.split(","))): tuple(v) for k, v in certificate["dual"].items()}
    assert len(excluded) == 158 and set(good) == {*excluded, SPECIAL}
    for r, separation in excluded.items():
        assert all(sum(a * b for a, b in zip(separation, vector, strict=True)) > 0
                   for vector in good[r][0])
    [(r, row_counts)] = certificate["primal"]
    assert tuple(r) == SPECIAL and sum(row_counts) == 92 and min(row_counts) >= 0
    deck, allowed = good[SPECIAL]
    assert all(sum(w * v for w, v in zip(row_counts, column, strict=True)) == 0
               for column in zip(*deck, strict=True))
    positive_rows = [row for row, w in zip(allowed, row_counts, strict=True) if w]
    assert all(all(gauge_masks(positive_rows, group)) for group in combinations(range(11), 4))
    print("H92 support: 2 through 10 excluded; at 11 only (1,2,3,4,5,6,7,8,9,10,12)", flush=True)


def selector_family(base_output):
    target = TARGET_SUMS
    all_permutations = tuple(permutations(range(4)))
    base_rows = {tuple(map(int, row.split())) for row in base_output.splitlines()}
    assert len(base_rows) == 4416
    selectors = set()
    for masks in base_rows:
        words = [tuple(2 * (mask >> i & 1) - 1 for i in range(n))
                 for mask, n in zip(masks, (12, 12, 11, 11), strict=True)]
        assert all(sum(x[i] * x[i + shift] for x in words for i in range(len(x) - shift)) == 0
                   for shift in range(1, 12))
        entries = tuple((2 * side + int(a != b), a) for side in range(2)
                        for a, b in zip(*words[2 * side:2 * side + 2], strict=True))
        totals = tuple(sum(s for j, s in entries if j == k) for k in range(4))
        assert sorted(map(abs, totals)) == [1, 2, 3, 3]
        for p in all_permutations:
            if tuple(map(abs, totals)) != tuple(abs(target[j]) for j in p):
                continue
            signed = tuple((p[k], s * target[p[k]] // totals[k]) for k, s in entries)
            assert tuple(sum(s for j, s in signed if j == k) for k in range(4)) == target
            selectors.add(signed)
    assert len(selectors) == 8832 and SELECTOR in selectors
    return sorted(selectors)


def affine_representatives(selectors):
    period = 23
    phase_maps = [tuple((a * i + b) % period for i in range(period))
                  for a in range(1, period) for b in range(period)]
    encoded = {bytes(2 * k + (s > 0) for k, s in selector): selector for selector in selectors}
    remaining = set(encoded)
    representatives = []
    for code, selector in sorted(encoded.items()):
        if code not in remaining:
            continue
        orbit = {bytes(code[i] for i in phase) for phase in phase_maps} & remaining
        assert code in orbit and len(orbit) == 2
        remaining.difference_update(orbit)
        representatives.append(selector)
    assert not remaining and len(representatives) == 4416
    return representatives


def eligible_anchor_weights():
    # Count four individual anchor gates and two simultaneous gates in each
    # period-23 column class. Normalized selector sums fix their period-13 decks.
    assert tuple(sum(signs(word)) for word in WILLIAMSON) == (-3, -3, -3, 5)
    sign_units = quaternion_basis(-1, -1, -1, 1)
    sparse_units = quaternion_basis(0, 0, 0, 1)
    assert quaternion_basis(-3, -3, -3, 5) == tuple(
        tuple(3 * h + 2 * a for h, a in zip(H, A, strict=True))
        for H, A in zip(sign_units, sparse_units, strict=True))
    source = build_source()
    masks = tuple(sum(1 << r for r in group) for group in fibres())
    columns = fibres()
    gates = []
    for pivot in (32, 19, 45, 6):
        ref = source[columns[pivot][0]]
        anchor = sum(mask for mask in masks if 2 * (ref & mask).bit_count() > 23)
        good = tuple(abs(dot(anchor, c)) == 2 for c in source)
        assert sum(good) == 759
        gates.append(good)
    gates.extend(tuple(a and b for a, b in zip(gates[k], gates[k + 1], strict=True)) for k in (0, 2))
    output = [[0] * 6 for _ in range(92)]
    for j in range(SIDE):
        c = 23 * (j // BLOCK) + (j % BLOCK) % 23
        for k, gate in enumerate(gates):
            output[c][k] += gate[j]
    assert tuple(map(sum, zip(*output, strict=True))) == (759, 759, 759, 759, 736, 736)
    assert all(row == output[23 * (i // 23)] for i, row in enumerate(output))
    return (*sign_units, *sparse_units, *output)


def verify():
    verify_shell()
    with TemporaryDirectory() as temp:
        worker = Path(temp) / "period23-support"
        subprocess.run(["g++", "-O3", "-march=native", "-std=c++17", str(Path(__file__).with_suffix(".cpp")),
                        "-o", str(worker)], check=True)
        bases = subprocess.run([str(worker), "bases"], check=True, text=True, capture_output=True).stdout
        selectors = selector_family(bases)
        representatives = affine_representatives(selectors)
        rows = [*eligible_anchor_weights(), (len(representatives),)]
        rows.extend([s * (k + 1) for k, s in selector] for selector in representatives)
        payload = "".join(" ".join(map(str, row)) + "\n" for row in rows)
        result = subprocess.run([str(worker), "check"], input=payload, check=True, text=True,
                                capture_output=True).stdout.splitlines()
        assert len(result) == 2 and result[1] == "overlap 578 580 570 564 568 552"
        assert result[0] == "support 4416 12338988480 12554902 1474274 0"
        print("Paired-base selectors: 8832 in 4416 affine-phase classes")
        print(result[0])
        print(result[1])


if __name__ == "__main__":
    verify()
