"""Replay two exact completions with nonorthogonal lower pairs."""

from hashlib import sha256

from r_paley_anchored_triples import COSELECTED_SINGLES, mixed_columns
from verify import goethals_seidel, length_299_words, rows_from_columns, verify_orthogonal


NONZERO_W = int(
    "520d5af158b23d48bd053d2a4fb09036713da79186f0403e3617bbf4f55d01652d74"
    "233a467b2ed0a6819f7321fa2082511e97b92f99906bff1974887b640c1661253b91"
    "632d1bc0a2e3752c439a248ad995a1aee6bb91050e5d3bf298c9be25f3a0ab5052fe"
    "6dd3257a855d57359e6bd9f3f568448b3b3e9f4d2d7734b672c3f2d36c181ab46854"
    "f95317c239424cbcef2385fdf8c", 16,
)


def verify():
    t, m = 599, 1196
    source = goethals_seidel(length_299_words())
    gamma, g = 0, 1
    mask = (1 << m) - 1
    normalized = [mask ^ source[gamma] ^ col for col in source]
    r, s = [j for j in range(m) if normalized[g] >> j & 1][:2]
    rows = rows_from_columns(m, normalized)
    different = rows[r] ^ rows[s]
    assert different.bit_count() == t - 1
    assert all(not different >> j & 1 for j in (gamma, g))
    extra = next(j for j in range(m) if j not in (gamma, g) and not different >> j & 1)
    selected = tuple(j for j in range(m) if different >> j & 1 or j == extra)
    assert len(selected) == t
    assert 2 * (2 - t) + (m - 4) + 2 == 0
    columns = mixed_columns(t, source, selected, gamma, [(g, (r,)), (g, (s,))])
    assert len(columns) == 1202 and verify_orthogonal(4 * t, columns) == 721801

    radius = 198
    assert -3 * t + 12 * radius + 8 < t
    assert t - 2 > radius and m - 2 * (t - 3) == 4
    print("Hadamard 2396 × 1202: two flips from one source, lower dot 1192, all 721801 pair products zero")
    print("Full completion: at least four lower words at distance at least 199 from every signed source")

    selected = tuple(j for j in range(m) if NONZERO_W >> j & 1)
    assert len(selected) == NONZERO_W.bit_count() == t
    flips = [(g, (r,)) for r, g in COSELECTED_SINGLES]
    flips.extend(((376, (868, 1046, 1071)), (794, (728,))))
    columns = mixed_columns(t, source, selected, gamma, flips)
    lower = [word >> (2 * t) & mask for word in columns[-len(flips):]]
    assert sorted(m - 2 * (lower[-1] ^ z).bit_count() for z in lower[:-1]) == [-4] * 9 + [4] * 3
    assert len(columns) == 1213 and verify_orthogonal(4 * t, columns) == 735078
    digest = sha256(b"".join(col.to_bytes(300, "little") for col in columns)).hexdigest()
    assert digest == "54c20b70380446ee272a20908215d6a2d991346d603d11e2fadc7a5d13a5cd97"
    print("Hadamard 2396 × 1213: twelve singles and one triple, all 735078 pair products zero")


if __name__ == "__main__":
    verify()
