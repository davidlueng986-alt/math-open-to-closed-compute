"""Replay the two-far, nine-single Paley extension at order 2396."""

from hashlib import sha256

from r_paley_double_far import build_pair, build_source, dot
from r_paley_isotropic_code import assemble, half_projections, rank_mod
from verify import verify_orthogonal


SELECTED = int(
    "a02d006009005200401680b405a02d01280b405a00801680b404a02d01600b005a02"
    "501680b7bdfcafcfdf57ebbfdffedf553fbffd7f6a0c7b73f75afcfcf7ffa7bdefef"
    "e57fe3a3dffecdc4bf8ff5fccdb574d18fdffcef97f6beb5ffef7377f9ffddf6bfd7"
    "dabff5ff4d973fb3ff57d01680a405a02d016009405a02901680b405a00c01680b40"
    "5a02501480b404a02d01600b405", 16,
)
ROWS = (822, 1112, 852, 867, 36, 1068, 950, 998, 557)
PIVOTS = (1145, 527, 227, 1175, 261, 1044, 108, 849, 287)
DIGEST = "993b880b7f5681f20d95d8ff378f2385b59e09d8e5a8706be92ca26642f4c0a9"


def verify():
    source = build_source()
    assert verify_orthogonal(1196, source) == 714610
    far, _ = build_pair(source)
    chosen = [j for j in range(1196) if SELECTED >> j & 1]
    assert len(chosen) == SELECTED.bit_count() == 600
    projections = [[dot(z, source[j]) for j in chosen] for z in far]
    assert all(abs(q) == 2 for profile in projections for q in profile)
    assert sum(p == q for p, q in zip(*projections, strict=True)) == 300
    assert len(set(ROWS)) == len(set(PIVOTS)) == 9
    assert not set(PIVOTS).intersection(chosen)

    singles = [source[g] ^ (1 << r) for r, g in zip(ROWS, PIVOTS, strict=True)]
    words = far + singles
    columns = assemble(599, source, chosen, words)
    assert len(columns) == 1211 and verify_orthogonal(2396, columns) == 732655
    assert sha256(b"".join(col.to_bytes(300, "little") for col in columns)).hexdigest() == DIGEST
    unused = [j for j in range(1196) if not SELECTED >> j & 1]
    residues = [tuple(p[j] for j in unused)
                for p in (half_projections(source, z) for z in words)]
    assert rank_mod(residues, 599) == 11
    print("Paley double far mixed: 2396 × 1211, two distance-483 words and nine single flips, 732655 zero products")
    print("Selected equal/opposite sectors 300/300, reserve residue rank 11, SHA256", DIGEST)


if __name__ == "__main__":
    verify()
