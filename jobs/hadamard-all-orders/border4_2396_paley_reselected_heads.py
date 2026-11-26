"""Check three independent peak-32 heads with exact dual quotients."""

from border4_2396_dual_mod5_forest import FACTORS_5, check_factors
from border4_2396_paley_dual_integer import audit_signs
from border4_2396_paley_head_obstruction import cosine_bounds, power_interval
from border4_2396_paley_negative_norm import N, periodic, sign_word
from border4_2396_primitive_field import remainder


FIXTURES = (
    (
        (0xB4C0489B8AD9E004271DCA56C56D4ABFAEB1F912A28504F0DA623EFD300F8D99A94EB3C0C6,
         0x6941A7E6CD5D64C45FC0370F5DC46B1DF34EE5C82CF784D7C8FB5B345135082375F8B038692,
         0x58589E82FFCEB1241698FC2231257025C38459BDC5DCFD95EACB728EDAE7979B9FC874FA6BB),
        (309, 101, 32, 159744), 1166, (34, 36, 35),
    ),
    (
        (0x23DCB2883E590A6261303BAD7E841C99204A87C49EE964FB8CA85BC397626A2F82923BAD583,
         0x41D111E74BA9F0A67C81D0074F16A32F29EF7D9D9836B06349F5231815579AD56DFE60A93D7,
         0x37ACFBE1BCEEFFD1E42D07DD7A8851BE953EDE915C511D726B7BBD1CC242863C168D8CF0913),
        (277, 117, 32, 119808), 1162, (37, 32, 41),
    ),
    (
        (0x21EDF253A329DA21287013096CA3C1C9B0CE15D40E42DABF0EF91BEABB42DAC41F221369545,
         0x43E0513CD6D920E535C1F8A35D317E7FB96BEF8D089D0E27CBA4633139772A3EF04E486D311,
         0x7008FAD3578D913788ED4A91FB37D7F2B09B106AF4FD1C414D98B4D3EEC34E71F1D9958737F),
        (325, 105, 32, 162816), 1171, (31, 38, 37),
    ),
)


def main():
    check_factors()
    scale, bounds = cosine_bounds()
    for masks, expected, spectral_floor, nonzero in FIXTURES:
        u, v, w = map(sign_word, masks)
        raw = audit_signs(u, v, w, (17, -5, -21))
        e = periodic((u, v, w, w))
        e[0] -= 1196
        assert e[0] == 0 and all(value % 8 == 0 for value in e)
        assert raw == tuple((-1)**i*e[i % N] for i in range(1, 2*N))
        assert all(sum(e[i::q]) == 0 for q in (13, 23) for i in range(q))
        stats = (sum(r % 16 == 0 for r in raw), raw.count(0), max(map(abs, raw)), sum(r*r for r in raw))
        assert stats == expected
        corr = periodic((u, v))
        spectrum = [power_interval(corr, d, scale, bounds) for d in range(N//2+1)]
        assert max(lo for lo, _ in spectrum) > spectral_floor*scale
        assert max(hi for _, hi in spectrum) < (spectral_floor+1)*scale
        assert tuple(sum(bool(r) for r in remainder(e, factor, 5)) for factor in FACTORS_5) == nonzero
        assert all(nonzero)
        print(f"Reselected heads: raw {stats}, maximum Fourier power in "
              f"({spectral_floor}, {spectral_floor+1}), mod-5 nonzero coefficients {nonzero}")


if __name__ == "__main__":
    main()
