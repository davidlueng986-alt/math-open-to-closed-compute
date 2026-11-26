"""Verify a wider far mixed rectangle and all one-fibre physical switches."""

from collections import Counter
from hashlib import sha256

from r_paley_far_periodic import MIXED_PIVOTS, MIXED_ROWS, MIXED_SOURCE_MASK, raw_word, row_fibres
from r_paley_isotropic_code import assemble, half_projections, rank_mod
from verify import goethals_seidel, length_299_words, rows_from_columns, verify_orthogonal


M = 1196
X = int(
    "3783f87f07b0de05e1fc1fc3f83f87f07b0fe0fe1fc1fc2f83f87f07f0de07c1fc1f"
    "c3f83f801742042e84085d0810ba1021742042e84084d0810ba1021542042e84085d"
    "0810ba102114213e2f827d5c04fabe49f574936ae927d5f20fabe09d57c93e2d827d"
    "5f24fabe49f57c93eaf927d5f24fabe49f57c93e2f927d5f24fabe49f57c926a7926"
    "d5724fabe49f17c93eab927d5f2", 16,
)
ROWS = (*MIXED_ROWS, 921, 1132, 14, 833)
PIVOTS = (*MIXED_PIVOTS, 576, 438, 645, 594)
DIGEST = "0a671dc989e63ef9eb4d72d3cdcb35059f317aa959006b9302da19dbe54c2890"


def verify_width(source, rows, raw, eligible, profile):
    selected = tuple(j for j in eligible if X >> j & 1)
    assert X.bit_count() == len(selected) == 600
    assert not set(selected).intersection(PIVOTS)
    assert (X & ~MIXED_SOURCE_MASK).bit_count() == 33

    def histogram(indices):
        return Counter(tuple((rows[r] >> j & 1) == (profile >> i & 1)
                             for r in MIXED_ROWS[:4])
                       for i, j in enumerate(eligible) if j in indices)

    old = {j for j in eligible if MIXED_SOURCE_MASK >> j & 1}
    assert histogram(old) == histogram(set(selected))
    words = [raw, *(source[g] ^ (1 << r) for r, g in zip(ROWS, PIVOTS, strict=True))]
    assert Counter(M - 2 * (raw ^ z).bit_count() for z in words[1:]) == {
        -28: 2, -12: 1, -8: 2, 0: 2, 4: 2, 12: 1,
    }
    columns = assemble(599, source, selected, words)
    assert len(columns) == 1211 and verify_orthogonal(2396, columns) == 732655
    packed = b"".join(word.to_bytes(300, "little") for word in columns)
    assert sha256(packed).hexdigest() == DIGEST
    unused = [j for j in range(M) if not X >> j & 1]
    residues = [tuple(p[j] for j in unused) for p in map(lambda z: half_projections(source, z), words)]
    assert rank_mod(residues, 599) == 11
    print("Hadamard 2396 × 1211: one distance-483 word and ten single flips, all 732655 products zero")


def verify_fibre_switches(rows, raw, eligible, profile, fibres):
    e = len(eligible)
    mask = (1 << e) - 1
    positive = []
    for r, row in enumerate(rows):
        projected = sum((row >> j & 1) << i for i, j in enumerate(eligible))
        # profile packs the sign of H_j^T raw/2 on the eligible set.
        # A one bit below denotes a positive term in the signed flip sum.
        same = mask ^ projected ^ profile
        positive.append(same if raw >> r & 1 else same ^ mask)
    assert max(2 * word.bit_count() - e for word in positive) == 53
    assert 53 * 12 < 1198 - 38 * 12

    counts = Counter()
    maxima = [0] * 13
    for fibre in fibres:
        binary_counts = [0] * 4
        previous = 0
        for step in range(1, 1 << len(fibre)):
            subset = step ^ (step >> 1)
            changed = subset ^ previous
            row = fibre[changed.bit_length() - 1]
            add = bool(subset & changed)
            carry = positive[row]
            for i, bits in enumerate(binary_counts):
                binary_counts[i] = bits ^ carry
                carry &= bits if add else bits ^ mask
                if not carry:
                    break
            assert not carry
            previous = subset
            d = subset.bit_count()
            if d % 2:
                continue
            counts[d] += 1
            valid = []
            for target in (d // 2, d // 2 + 1):
                match = mask
                for i, bits in enumerate(binary_counts):
                    match &= bits if target >> i & 1 else bits ^ mask
                valid.append(match.bit_count())
            maxima[d] = max(maxima[d], sum(valid))
    assert sum(counts.values()) == 92 * 4095
    assert maxima[2::2] == [511, 455, 431, 438, 380, 297]
    print("One-fibre physical switches: all 376740 nonempty even subsets, at most 511 common eligible positions")


def verify():
    source = goethals_seidel(length_299_words())
    rows = rows_from_columns(M, source)
    fibres = row_fibres()
    raw = raw_word(source, fibres)
    dots = [M - 2 * (raw ^ word).bit_count() for word in source]
    eligible = tuple(j for j, d in enumerate(dots) if abs(d) == 2)
    profile = sum((dots[j] > 0) << i for i, j in enumerate(eligible))
    assert len(eligible) == 637 and max(map(abs, dots)) == 230
    verify_width(source, rows, raw, eligible, profile)
    verify_fibre_switches(rows, raw, eligible, profile, fibres)


if __name__ == "__main__":
    verify()
