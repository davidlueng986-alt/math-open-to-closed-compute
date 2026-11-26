"""Replay successive and joint one-flip extensions of the full92 construction."""

from collections import Counter
from hashlib import sha256
from itertools import combinations, combinations_with_replacement

from r_paley_full92_contrast import (
    AGREE, OPPOSITE, PAIR_FIBRES, PAIR_INDICES, WHOLE_FIBRES,
    centre_column, local_index,
)
from r_paley_full92_skew import build_source, frame
from r_paley_isotropic_code import assemble, half_projections, rank_mod
from r_paley_periodic_skew import check_frame, sign
from verify import verify_orthogonal


STAGES = (
    (972, 1027, int(
        "458040073481dc1710d86421aa4982cfb23db82cd56087a2413bd47ec62961db"
        "b1dd6cbf677aa060b2809f718382c2022d354bba0cc1e59b042baf5c527934ee"
        "bf3de7af0f26f887dc3ef97545a210808ef5149944d896a85501b34836660a6d"
        "7b5e4c3e3dd4d3b87cafa5df55b9e3ceea80d3cc28ec92510720032bc4365c11"
        "48be5ddae49d34b9efcbc6e3f2efb7fdb1ee8f7dfbf",
        16), "43d792c1aab0d822d75c9f389d570ef3a94de72315dead48dd586c565274c3c8"),
    (1013, 907, int(
        "458a48173281dc1710d96431aa4983cb967db82c5560c7b26d33d4e6c60861db"
        "33d96c39655ae070b2849e758382c3826d354a3e0fc1e5f9042ba75c527935fc"
        "bf3dd32f0f66ea871c3afb7545a214808ef5149964d896a85511b74816668a6d"
        "7b5ecc3c39d4d3b86caea1df75b9c38eea80f39c38ac92510620032bcc345425"
        "69be55dae49f34b9efdbcee1d2cfaffdb3aea729db3",
        16), "cfc2f6e45cf69d678856a4b38a8bd5ff1194849f7dd10b1d53035d87c0bf4a74"),
    (1066, 1167, int(
        "558a48173681de171cd96471aa498bdb967dba2cd520c7a2653354e6ca0861d3"
        "33d94c39455aea71b38e9e758383c3a2ed756b3e0e51e5fd242bae1c5a7924bc"
        "b33dc32f1f26ea071c32b97545a214808ef5149964d896a85711b7481e66826d"
        "7b7ecc3c39d4d3386cae20df75b9c38eeac8f39c38ac92510624033bcc345425"
        "69be559ae49b3439efd9cee192cdabfdb1aea728db3",
        16), "3e2295dbe600c946b68056fdc420b68385f0969679b6dd44072483b8793a1858"),
)


BRANCH_ROOTS = (972, 1013, 1066, 1051)
BRANCH_PIVOTS = (935, 852, 523, 1106)
BRANCH_SELECTED = int(
    "449c48172693de1600d97511eac98b695e79d82cd522efb26b3655f6ca0870db"
    "b3c84c69a45be860a28c9c558183c3226d755b3b4a73efdc642be75c507974ec"
    "9f7c53af1546e8058d30bf346aa034022ca512b364cd86aa9791be485e6f9f6d"
    "7b9dcd3c91b4d0bc3c8e24df313ac35c68e1719c3ca4525d9774a3efd4167e25"
    "29b801fac49124b1e8cb4e81b24bbb9dff6e8721fb7",
    16,
)
BRANCH_DIGEST = "708fc9b784f4fd2b14b11a590e5bed5366be86d95a8fde0ccd724c9d42281186"


NEXT_ROOTS = (972, 1013, 1066, 1051, 16)
NEXT_PIVOTS = (1050, 622, 112, 439, 94)
NEXT_SELECTED = int(
    "4c56652570911a160afbf1c2b89d937f9b2da2ef0daea1f66a9e54c2670c5889"
    "155c7668a6ddbc69f18a877d08aa9726a9a748827e71e4be54fae45e5ed333e3"
    "9bf151a8170278a3d53e6f04eb9a55d627e67463630126eb6629aa5c27ef7764"
    "b99f9f26c53569a860012bd9242a8691aa64756bcfa4d6f5902033394d0c3137"
    "2fb360d26d8764e8fc597c00b7893f1f138e4d30b96",
    16,
)
NEXT_DIGEST = "77f87219f5ffeaa473fa1c80505c3c4a74febf5c89dac226a6e68a69a36d9bae"


def verify_rectangle(source, rows, reserves, selected, expected_digest):
    assert len(rows) == len(set(rows)) == len(reserves) == len(set(reserves))
    assert len(selected) == len(set(selected)) == 600
    assert set(selected).isdisjoint(reserves)
    for i, j in combinations(range(len(rows)), 2):
        r, s = rows[i], rows[j]
        g, h = reserves[i], reserves[j]
        target = sign(source[g], r) * sign(source[g], s)
        target += sign(source[h], r) * sign(source[h], s)
        assert sum(sign(source[c], r) * sign(source[c], s) for c in selected) == target

    words = [source[g] ^ (1 << r) for r, g in zip(rows, reserves, strict=True)]
    columns = assemble(599, source, selected, words)
    width = 1200 + len(words)
    pairs = width * (width - 1) // 2
    assert len(columns) == width and verify_orthogonal(2396, columns) == pairs
    outside = [col & ((1 << 2394) - 1) for col in columns[:1198]]
    assert all((a & b).bit_count() == 598 for a, b in combinations(outside, 2))
    unused = sorted(set(range(1196)) - set(selected))
    code = [tuple(q[j] for j in unused) for q in (half_projections(source, w) for w in words)]
    assert all(sum(a * b for a, b in zip(u, v, strict=True)) % 599 == 0
               for u, v in combinations_with_replacement(code, 2))
    assert rank_mod(code, 599) == len(words)
    digest = sha256(b"".join(col.to_bytes(300, "little") for col in columns)).hexdigest()
    assert digest == expected_digest
    return width, pairs, digest


def verify():
    source = build_source()
    assert verify_orthogonal(1196, source) == 714610
    centres, pivots = frame()
    rows = [centres[j] for j in AGREE + OPPOSITE]
    reserves = [pivots[j] for j in AGREE + OPPOSITE]
    check_frame(source, rows, reserves)
    previous = [local_index(c, j) for c in WHOLE_FIBRES for j in range(92)]
    previous.extend(local_index(c, j) for pair in PAIR_INDICES
                    for group, j in zip(PAIR_FIBRES, pair, strict=True) for c in group)
    assert len(previous) == len(set(previous)) == 600

    def profile_counts(columns, observed_rows):
        return Counter(centre_column(source, observed_rows, j) for j in columns)

    first_rows = rows.copy()
    first_reserves = reserves.copy()
    original_counts = profile_counts(previous, first_rows)

    for root, pivot, mask, expected_digest in STAGES:
        assert root not in centres and root not in rows
        assert pivot not in reserves and pivot not in previous
        selected = [j for j in range(1196) if mask >> j & 1]
        assert len(selected) == mask.bit_count() == 600
        changed = len(set(selected).difference(previous))
        assert set(selected).isdisjoint(reserves + [pivot])
        assert profile_counts(previous, rows) == profile_counts(selected, rows)
        rows.append(root)
        reserves.append(pivot)
        width, pairs, digest = verify_rectangle(source, rows, reserves, selected, expected_digest)
        print(f"Full92 unrestricted: 2396 x {width}, all {pairs} pairwise products zero")
        print(f"Row {root}, pivot {pivot}, {changed} reselected columns, "
              f"reserve rank {len(rows)}, SHA256 {digest}")
        previous = selected


    extra_roots = tuple(rows[12:])
    extra_reserves = tuple(reserves[12:])
    joint_branches = (
        (BRANCH_ROOTS, BRANCH_PIVOTS, BRANCH_SELECTED, BRANCH_DIGEST, 122),
        (NEXT_ROOTS, NEXT_PIVOTS, NEXT_SELECTED, NEXT_DIGEST, 216),
    )
    g0, r0 = first_reserves[0], first_rows[0]
    for new_roots, new_pivots, mask, expected_digest, changes in joint_branches:
        assert new_roots[:-1] == extra_roots
        assert set(new_roots).isdisjoint(centres)
        assert set(new_pivots).isdisjoint(extra_reserves)
        selected = [j for j in range(1196) if mask >> j & 1]
        assert len(selected) == mask.bit_count() == 600
        assert profile_counts(selected, first_rows) == original_counts
        assert profile_counts(previous, first_rows) == original_counts
        assert len(set(selected).difference(previous)) == changes
        for r, g in zip(new_roots, new_pivots, strict=True):
            first_contact = sign(source[g0], r) * sign(source[g0], r0)
            for j, h in zip(first_rows, first_reserves, strict=True):
                profile = sign(source[g], j) * sign(source[g], r0)
                assert profile == first_contact * sign(source[h], r) * sign(source[h], j)
        for i, j in combinations(range(len(new_roots)), 2):
            r, s = new_roots[i], new_roots[j]
            g, h = new_pivots[i], new_pivots[j]
            product = sign(source[g], s) * sign(source[g], r0)
            product *= sign(source[h], r) * sign(source[h], r0)
            assert product == -sign(source[g0], r) * sign(source[g0], s)
        width, pairs, digest = verify_rectangle(
            source, first_rows + list(new_roots), first_reserves + list(new_pivots),
            selected, expected_digest,
        )
        print(f"Full92 joint pivot branch: 2396 x {width}, all {pairs} pairwise products zero")
        print(f"Twelve preserved inners, {changes} reselected columns, "
              f"reserve rank {width - 1200}, SHA256 {digest}")
        previous = selected
        extra_roots, extra_reserves = new_roots, new_pivots


if __name__ == "__main__":
    verify()
