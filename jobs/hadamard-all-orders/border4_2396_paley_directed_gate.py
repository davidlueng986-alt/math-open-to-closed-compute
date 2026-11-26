"""Verify directed acyclic residual envelopes on exact-dual Paley signs."""

from border4_2396_paley_dual_integer import FIXTURES as DUAL_FIXTURES, W_13, audit_signs
from border4_2396_paley_head_obstruction import cosine_bounds, power_interval
from border4_2396_paley_negative_norm import N, periodic, sign_word
from border4_2396_paley_q13_mod16 import margins, residue_class

ORIGINAL_ORDER = (6, 7, 10, 11, 1, 8, 12, 2, 13, 3, 14, 15, 16, 17, 18, 4, 9, 0, 5)
ORIGINAL_FIXTURES = (
    (5, 0x707C67CBCE6399F18F2C0F490869033B8B24BBB60CE8FF9D756A981DB6E79EBBDDB84E6C58A,
     ORIGINAL_ORDER, (301, 61, 104, 506368), 21),
    (7, 0xFC7E6C5E017B537CF8C75470F13BF21DB55BFB2C0072EB3F549306AA257D7E1E63D64DE423,
     ORIGINAL_ORDER, (317, 65, 80, 753152), 21),
)
SPECTRAL_HEAD = (
    0x469067EFB1D90175978CC2A6DAEB01C0843EEC5D4FA31B702B6AAE25D87F805B460E173082,
    0x6664A5118EED6AD344C927805C3C0FAA01E6149CD225E52FC7EBD239DFB208FF5B0CBA776D6,
)
SPECTRAL_W_23 = (-5, -3, 1, -3, -3, 1, 1, -7, 5, -3, 3, -3, -3, 1, -1, -5, -3, -1, 7, 1, 1, -1, -1)
SPECTRAL_FIXTURES = (
    (5, 0x7F187B979518F25F9E1D53345D993B08D766B2AF18D54CE333DA43F9B281D1149CDC1EAF4BF,
     (11, 5, 2, 18, 10, 9, 4, 17, 16, 1, 15, 14, 13, 3, 12, 8, 7, 6, 0),
     (309, 61, 88, 396288), 18),
    (7, 0x4182DEA33223C07DF43BF9BD8339DC66517E3E3995FC7D3BD2C35F15574F126426758AAECCE,
     (18, 17, 16, 15, 14, 13, 2, 12, 4, 11, 10, 9, 8, 3, 7, 6, 5, 1, 0),
     (261, 45, 80, 488448), 7),
)


def check_field_profile(p):
    degree, reciprocal_pairs = {5: (44, 3), 7: (132, 1)}[p]
    orbit = {pow(p, i, N) for i in range(degree)}
    assert len(orbit) == degree and pow(p, degree, N) == 1
    assert N-1 not in orbit and 12*22 == 2*degree*reciprocal_pairs


def audit(head_masks, w_23, p, w_mask, order, expected, count):
    check_field_profile(p)
    u, v, w = map(sign_word, (*head_masks, w_mask))
    assert margins((w,), 13) == (W_13,) and margins((w,), 23) == (w_23,)
    raw = audit_signs(u, v, w, (17, -5, -21))
    measured = (sum(r%16==0 for r in raw), raw.count(0),
                max(map(abs, raw)), sum(r*r for r in raw))
    assert measured == expected
    e = periodic((u, v, w, w))
    e[0] -= 1196
    assert e[0]==0 and all(e[d]==e[-d] for d in range(1,N))
    assert all(sum(e[i::q])==0 for q in (13,23) for i in range(q))
    assert all(r%8==0 for r in e) and any(r%p for r in e)
    assert raw == tuple((-1)**i*e[i%N] for i in range(1,2*N))

    rank = {node: i for i, node in enumerate(order)}
    assert len(rank)==19 and set(rank)==set(range(19))
    edges = 0
    for d in range(1,N//2+1):
        value = e[d]
        if abs(value)<8*p:
            continue
        a = residue_class(d,13)
        b = 7+residue_class(d,23)
        assert (rank[a]<rank[b])==(value>0)
        edges += 1
    assert edges == count
    print(f"mod {p}: raw {measured}; all {edges} high arcs follow the exact vertex order")


def main():
    _, u, v, w_23, _, _ = DUAL_FIXTURES[0]
    for fixture in ORIGINAL_FIXTURES:
        audit((u, v), w_23, *fixture)
    scale, bounds = cosine_bounds()
    prior = periodic(tuple(map(sign_word, (u,v))))
    lo, hi = power_interval(prior, 106, scale, bounds)
    assert 2495*scale < lo < hi < 2496*scale
    new = periodic(tuple(map(sign_word, SPECTRAL_HEAD)))
    assert all(power_interval(new, d, scale, bounds)[1] < 1136*scale for d in range(150))
    assert any(power_interval(new, d, scale, bounds)[0] > 1135*scale for d in range(150))
    print("New heads: all 150 Fourier bounds pass, with maximum strictly between 1135 and 1136")
    for fixture in SPECTRAL_FIXTURES:
        audit(SPECTRAL_HEAD, SPECTRAL_W_23, *fixture)


if __name__=="__main__":
    main()
