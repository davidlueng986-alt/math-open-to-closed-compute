"""Replay physical four-border sources with both integer quotients exact."""

from border4_2396 import periodic
from border4_2396_joint_q13_mod16 import joint_words
from border4_2396_nested import nested_negative_words
from border4_2396_primitive_field import primitive_factor, remainder
from border4_2396_shifted_tail import verify_lift

MASKS = (
    0x200200000080021010008000000100080840420200200100002020000008000004000001800,
    0x18000002002000000C0000010810400000001000000C0020030008008000002000800,
    0x47125710811801188041D00080440020300000020088404011108008060102028020200DC00,
    0x11D491C400EC01010050102018040042220080844010000003010008804002E080462006204,
)
MORE_MOD16 = (
    0x71300800000046101203040524C5802810049E000827000032A824010000002A85901006848,
    0x5C0028141202202081100483C1100891401F04083600006C0920E7220828E082102082601,
    0x7124790813801188041500080440020300000020188404011108408060102028040200C000,
    0x13C491C0000C01008050102018040842220080846010000003010008804002A080462007204,
)
CHANGED_C13_MARGINS = (
    0x317808003C9006183081140102E18024D9441800082A051032A020111008500006104001408,
    0x102E0838501003D0248140440380130DD1401E0048130400380020070008C88080306003800,
    0x2F120704849D01008849C6008044006000100006010840621010000006010B028040200D080,
    0x41C091E8042C01008050342018000002021180842018000200018008804018E48440202E484,
)


def dual_words(masks=MASKS):
    original = joint_words()
    assert all(not (mask >> i & 1) or value
               for row, mask in zip(original, masks, strict=True)
               for i, value in enumerate(row))
    return tuple(tuple(-value if mask >> i & 1 else value for i, value in enumerate(row))
                 for row, mask in zip(original, masks, strict=True))


def endpoints(d):
    return min(d % 13, -d % 13), 7+min(d % 23, -d % 23)


def inverse_circulation(inverse):
    """Recover the tree entries of a balanced integral circulation from its chords."""
    parents = list(range(19))

    def root(i):
        while parents[i] != i:
            i = parents[i]
        return i

    tree = [set() for _ in parents]
    recovered = [0]*149
    balances = [0]*19
    chord_count = 0
    for d in range(1, 150):
        a, b = endpoints(d)
        u, v = root(a), root(b)
        if u != v:
            parents[u] = v
            tree[a].add((b, d))
            tree[b].add((a, d))
        else:
            recovered[d-1] = w = inverse[d-1]
            balances[a] += w
            balances[b] -= w
            chord_count += 1
    assert chord_count == 131
    for _ in range(18):
        i = next(i for i, adjacent in enumerate(tree) if len(adjacent) == 1)
        j, d = tree[i].pop()
        tree[j].remove((i, d))
        recovered[d-1] = -balances[i] if i < 7 else balances[i]
        balances[j] += balances[i]
        balances[i] = 0
    assert not any(balances) and tuple(recovered) == tuple(inverse)


def replay(s, t, metrics, mod32, amplitude):
    patterns = tuple("".join({-1: "-", 0: ".", 1: "+"}[value] for value in row)
                     for row in s)
    verify_lift(patterns, t, [0]*7, *metrics)
    projected = tuple(tuple(sum(row[j::23]) for j in range(23)) for row in s)
    assert periodic(projected) == [573] + [-26]*22
    raw = periodic(s)
    assert raw[0] == 597 and all((v+2) % 4 == 0 for v in raw[1:])
    assert 1+2*sum((v+2) % 16 == 0 for v in raw[1:]) == mod32
    e = (0,) + tuple((v+2)//4 for v in raw[1:])
    for q in (13, 23):
        assert all(sum(e[j::q]) == 0 for j in range(q))
    inverse_circulation(e[1:150])
    assert max(map(abs, e)) == amplitude
    return e


def main():
    t = nested_negative_words()
    assert periodic(t) == [599] + [0]*298
    low = replay(dual_words(), t, (349, 117, 80, 507392), 189, 10)
    assert any(remainder(low, primitive_factor(11), 11))
    fixed = dual_words(MORE_MOD16)
    changed = dual_words(CHANGED_C13_MARGINS)
    replay(fixed, t, (469, 105, 96, 619520), 233, 12)
    replay(changed, t, (477, 65, 96, 641536), 281, 12)
    def head_profiles(words):
        return [periodic((tuple(sum(w[j::13]) for j in range(13)),)) for w in words[:2]]

    old, new = head_profiles(fixed), head_profiles(changed)
    assert old[0] != new[0] and old[1] != new[1]
    assert tuple(map(sum,zip(*old))) == tuple(map(sum,zip(*new)))
    print("All exact T, C13, C23 and all 597 raw mod8. Mod16/exact: 349/117, 469/105, 477/65.")


if __name__ == "__main__":
    main()
