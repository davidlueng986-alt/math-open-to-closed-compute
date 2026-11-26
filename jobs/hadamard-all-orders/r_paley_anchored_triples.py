"""Exact anchored triple-flip candidates and two mixed-flip witnesses."""

from hashlib import sha256

from r_paley_projective_lift import build
from verify import goethals_seidel, length_299_words, verify_orthogonal


ANCHORS = (1130, 435)
EXCEPTIONS = (115, 686)
GAMMA = 974
FLIPS = (
    (1051, 216, True), (574, 312, True), (611, 638, True), (880, 542, True),
    (620, 127, False), (584, 751, False),
)

COSELECTED_W = int(
    "700f5fd050a47de8b10d3d3a4fb0303e707da391a6a6502f3657bbf5d59f81652f54"
    "2bba5f7b0c18a6009e7301fa2092511fb7b8a7f910cbeb59eccb79680d16632d1b99"
    "630f1f4082e365ac4bfa3488d895e5a6c0ab91274e7d3ef288c9262dfb24af5040fe"
    "4de3655e895d5f159f2b59d1f162048a9a7adf4d6d7730b37a97f2924e101ef46954"
    "715713a22d424c9cc7289df9584", 16,
)
COSELECTED_SINGLES = (
    (969, 87), (447, 680), (61, 607), (538, 1154), (996, 64),
    (747, 1109), (173, 707), (1043, 279), (221, 564), (1059, 1028), (377, 475),
)


def sign(word, index):
    return 2 * (word >> index & 1) - 1


def mixed_columns(t, source, selected, gamma, flips):
    m = 2 * t - 2
    mask = (1 << m) - 1
    normalized = [mask ^ source[gamma] ^ col for col in source]
    outside, inside = build(t, source, (), w_columns=selected, gamma_index=gamma)
    for g, positions in flips:
        assert g not in selected and g != gamma
        assert len(set(positions)) == len(positions)
        z = normalized[g] ^ sum(1 << x for x in positions)
        assert z.bit_count() == t - 2
        u = tuple(sum(sign(normalized[g], x) * sign(normalized[j], x) for x in positions)
                  for j in selected)
        assert all(abs(x) == 1 for x in u)
        assert all(m - 2 * (normalized[j] ^ z).bit_count() == -2 * x
                   for x, j in zip(u, selected, strict=True))
        top = sum((x > 0) << j for j, x in enumerate(u))
        opposite = top ^ ((1 << t) - 1)
        inside.append(top | (opposite << t) | (z << (2 * t)) | (3 << (4 * t - 2)))
    return outside + inside


def verify():
    t, m = 599, 1196
    mask = (1 << m) - 1
    a, b = ANCHORS
    e, f = EXCEPTIONS
    source = goethals_seidel(length_299_words())
    normalized = [mask ^ source[GAMMA] ^ col for col in source]
    assert normalized[GAMMA] == mask
    agrees = tuple(i for i, col in enumerate(normalized) if sign(col, a) == sign(col, b))
    assert len(agrees) == 598 and GAMMA in agrees and e not in agrees and f not in agrees
    selected = tuple(i for i in agrees if i != GAMMA) + EXCEPTIONS
    assert len(set(selected)) == t

    # A separate column orientation makes the anchor row all positive and
    # exposes the exact count of all allowed single-column triple choices.
    oriented = [col if sign(col, a) > 0 else col ^ mask for col in normalized]
    eligible_rows = [r for r in range(m) if r != b
                     and sign(oriented[e], r) == sign(oriented[f], r) == -1]
    assert len(eligible_rows) == 298 and a not in eligible_rows
    for r in eligible_rows:
        assert sum(sign(col, b) == -1 and sign(col, r) == 1 for col in oriented) == 299
    assert len(eligible_rows) * (m // 4) == 89102

    flips = [(g, (a, b, r) if triple else (r,)) for r, g, triple in FLIPS]
    columns = mixed_columns(t, source, selected, GAMMA, flips)
    assert len(columns) == 1206 and verify_orthogonal(4 * t, columns) == 726615
    digest = sha256(b"".join(col.to_bytes(300, "little") for col in columns)).hexdigest()
    assert digest == "a42aee8ca043c57baff4c927b47a0098b2a36a7fd4bae7e437f7537f15f4cd63"
    print("Anchored flips: 89102 exact triple candidates under the normalized adaptive source")
    print("Hadamard 2396 × 1206: four triples and two singles, all 726615 pair products zero")

    # Co-selecting W permits a three-flip column with eleven old skew one-flip
    # choices, even though the chosen exterior changes.
    selected = tuple(j for j in range(m) if COSELECTED_W >> j & 1)
    assert len(selected) == COSELECTED_W.bit_count() == t
    flips = [(g, (r,)) for r, g in COSELECTED_SINGLES]
    flips.append((376, (868, 1046, 1071)))
    columns = mixed_columns(t, source, selected, 0, flips)
    assert len(columns) == 1212 and verify_orthogonal(4 * t, columns) == 733866
    digest = sha256(b"".join(col.to_bytes(300, "little") for col in columns)).hexdigest()
    assert digest == "732c75516bbcb8daadeba0537e56b982a973b459e0e14c35d92a717b1eeb0f57"
    print("Hadamard 2396 × 1212: one triple and eleven singles on new W, all 733866 pair products zero")


if __name__ == "__main__":
    verify()
