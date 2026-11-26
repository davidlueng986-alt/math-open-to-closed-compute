"""Exact physical F3 primitive roots on parity-optimal Paley reflection geometry."""

from border4_2396_dual_mod5_forest import reciprocal
from border4_2396_paley_dual_integer import audit_signs
from border4_2396_paley_negative_norm import N, periodic, sign_word
from border4_2396_paley_peak32_gates import FACTORS_3, check_factors_3
from border4_2396_paley_q13_mod16 import margins
from border4_2396_paley_reselected_heads import FIXTURES as HEAD_FIXTURES
from border4_2396_primitive_field import remainder

AXIS = 188
FIXTURES = (
    (
        0x781DBAD3B781900981ADC955A81FF4D4379B12E8DEFC2E596D9136D36E87EF6AF11BB58575E,
        0x7E18BA5337E1B99D87ACC855087FF23C078B12E99FD8AC5969F1F2D366A37F3AF11AB40799E,
        60, (309, 25, 152, 1431552),
    ),
    (
        0x7C5DB852B705C813A0AD4815AA3F5CBA33931373F6DD7C69619B34D2E7D76DF9D119B18BB76,
        0x746DBC529E05EA57A0394835A62F18A67B973227BEDCEC69517BD552E6E76FBC819DB3CCB32,
        64, (325, 33, 128, 1137664),
    ),
    (
        0x6C599A52B79DDC3BB9AD4A518A377D9AB6131079C6F8CC714DB1B651E643EC73D15987AB37E,
        0x6C399A7AB69BFC3FD92D5E518C375718C656307BAEBA8C7159319351E60BAEBBD1CDC6631D6,
        60, (325, 29, 144, 1582080),
    ),
    (
        0x741999539791942989A9C891882F7FFEB29311FBDCD89C6961AAB4D2E703677BF159A1AFFFE,
        0x581BD85317C1D3CB83A8C813C81B582FBA5391F7FED88F6961AAB4D2FE036FFDF179C3BE836,
        64, (277, 45, 136, 1195008),
    ),
)


def main():
    check_factors_3()
    (u, v, w), _, _, _ = HEAD_FIXTURES[2]
    u, v, reference = tuple(map(sign_word, (u, v, w)))
    expected_margins = {q: margins((reference,), q)[0] for q in (13, 23)}
    for q, values in expected_margins.items():
        degrees = tuple((N//q - value)//2 for value in values)
        assert sum(abs(degrees[i]-degrees[(AXIS-i) % q]) for i in range(q)) == 24
    orbits = tuple((i, (AXIS-i) % N) for i in range(N) if i < (AXIS-i) % N)
    assert len(orbits) == 149

    for index, (base, encoded, changes, expected) in enumerate(FIXTURES):
        before, after = (sign_word(word) for word in (base, encoded))
        assert all(margins((row,), q) == (expected_margins[q],)
                   for row in (before, after) for q in (13, 23))
        assert sum(before[i] != before[j] for i, j in orbits) == 12
        assert sum(after[i] != after[j] for i, j in orbits) == 12
        assert (base ^ encoded).bit_count() == changes
        delta = tuple(a-b for a, b in zip(after, before, strict=True))
        assert all(delta[i] == delta[(AXIS-i) % N] for i in range(N))
        assert all(not delta[i] or before[i] == before[(AXIS-i) % N] for i in range(N))
        raw = audit_signs(u, v, after, (17, -5, -21))
        actual = (sum(a % 16 == 0 for a in raw), raw.count(0), max(map(abs, raw)),
                  sum(a*a for a in raw))
        assert actual == expected
        e = periodic((u, v, after, after))
        e[0] -= 1196
        assert all(x % 8 == 0 for x in raw)
        assert all(sum(e[d::q]) == 0 for q in (13, 23) for d in range(q))
        assert not any(remainder(e, FACTORS_3[index], 3))
        assert not any(remainder(e, reciprocal(FACTORS_3[index], 3), 3))
        assert all(any(remainder(e, f, 3)) for j, f in enumerate(FACTORS_3) if j != index)
        print(f"Axis 188, primitive F3 pair {index}: exact two quotients, raw {actual}")


if __name__ == "__main__":
    main()
