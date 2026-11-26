"""Reconstruct a raw modulo-sixteen candidate with quotient error 256."""

from border4_2396_565 import source_words
from border4_2396_full_y_expanded import POSITIVE_Y, indices, site, verify_frame
from border4_2396_nested import nested_negative_words
from border4_2396_shifted_tail import compress, reflect, verify_lift

FRONT = (1726928340920861, 924208625444246)
TAIL = (10658394275121615978, 10053951668259954215, 1)
QUOTIENT_HALF = (0, 0, 0, 0, 0, 8, -8)


def switch(row, mask):
    assert all(row[i] for i in mask)
    return tuple(-value if i in mask else value for i, value in enumerate(row))


def reconstruct(front_codes, tail_code, centers=(0, 0)):
    original = source_words()
    transform = verify_frame(original)
    front = []
    for row, code, center in zip(original[:2], front_codes, centers, strict=True):
        assert transform[center] == center
        mask = {site(x, 0) for x in indices(center)}
        for k, y in enumerate(POSITIVE_Y):
            f = (code >> (13*k)) & ((1 << 13)-1)
            mask.update(site(x, y) for x in indices(f))
            mask.update(site(x, (-y) % 23) for x in indices(transform[f]))
        changed = switch(row, mask)
        assert compress(changed) == compress(row)
        front.append(changed)
    active = [i for i, value in enumerate(original[2]) if value]
    assert active == [i for i, value in enumerate(reflect(original[3])) if value]
    packed = sum(v << (64*k) for k, v in enumerate(tail_code))
    mask = {active[j] for j in indices(packed)}
    return (*front, switch(original[2], mask),
            reflect(switch(reflect(original[3]), mask)))


def candidate_words():
    return reconstruct(FRONT, TAIL)


def main():
    source = candidate_words()
    patterns = tuple("".join({-1: "-", 0: ".", 1: "+"}[v] for v in row)
                     for row in source)
    verify_lift(patterns, nested_negative_words(), list(QUOTIENT_HALF), 597, 141, 112, 714752)
    assert 2*sum(v*v for v in QUOTIENT_HALF[1:]) == 256
    print("All 597 original shifts modulo sixteen, 141 exact; C13 error energy 256.")


if __name__ == "__main__":
    main()
