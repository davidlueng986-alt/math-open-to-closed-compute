"""Verify one order-2396 border source with exact C13 and full original modulo sixteen."""

from border4_2396 import periodic
from border4_2396_nested import nested_negative_words
from border4_2396_raw_mod16_256 import reconstruct
from border4_2396_shifted_tail import verify_lift

CENTERS = (6464, 57)
FRONT = (156966325912113, 985218117643670)
TAIL = (12602424914660141093, 722085977984909923, 0)


def joint_words():
    return reconstruct(FRONT, TAIL, CENTERS)


def main():
    positive = joint_words()
    negative = nested_negative_words()
    assert periodic(negative) == [599] + [0]*298
    patterns = tuple("".join({-1: "-", 0: ".", 1: "+"}[v] for v in row)
                     for row in positive)
    verify_lift(patterns, negative, [0]*7, 597, 105, 80, 552960)
    assert 1 + 2*sum((v + 2) % 16 == 0 for v in periodic(positive)[1:]) == 277
    print("Exact T and C13; all 597 original shifts modulo sixteen, 105 exact.")


if __name__ == "__main__":
    main()
