"""Replay an exact-C13 source with minimum positive C23 error under raw modulo eight."""

from border4_2396 import periodic
from border4_2396_joint_q13_mod16 import joint_words
from border4_2396_nested import nested_negative_words
from border4_2396_shifted_tail import verify_lift

MASKS = (
    0x392020F4C240C00082840C0141002691000C00582200102880001D0808308886903203100,
    0x10282039D408438806834008222192079040088658290114082840CC200838EA81D04801508,
    0x27104340813C2108084156008044002010000006008840401110840C0601020280601004400,
    0x58411C80088020180501020180C084222008084401800000201000880401AA08404210F204,
)


def candidate_words():
    original = joint_words()
    assert all(mask >> i & 1 == 0 or v != 0
               for row, mask in zip(original, MASKS, strict=True) for i, v in enumerate(row))
    return tuple(tuple(-v if mask >> i & 1 else v for i, v in enumerate(row))
                 for row, mask in zip(original, MASKS, strict=True))


def main():
    s = candidate_words()
    t = nested_negative_words()
    assert periodic(t) == [599] + [0]*298
    patterns = tuple("".join({-1: "-", 0: ".", 1: "+"}[v] for v in row) for row in s)
    verify_lift(patterns, t, [0]*7, 397, 65, 88, 632320)
    assert all((v+2) % 4 == 0 for v in periodic(s)[1:])
    projected = tuple(tuple(sum(row[j::23]) for j in range(23)) for row in s)
    coeffs = periodic(projected)
    errors = [v-(573 if d == 0 else -26) for d, v in enumerate(coeffs)]
    assert errors == [(-4 if d in (2,21) else 4 if d in (10,13) else 0) for d in range(23)]
    assert sum(v*v for v in errors) == 64
    print("Exact T and C13, all raw mod8, C23 error 64, 397 raw mod16, 65 exact.")


if __name__ == "__main__":
    main()
