"""Verify directed acyclic residual envelopes on exact-dual Paley signs."""

from border4_2396_paley_dual_integer import FIXTURES as DUAL_FIXTURES, W_13, audit_signs
from border4_2396_paley_negative_norm import N, periodic, sign_word
from border4_2396_paley_q13_mod16 import margins, residue_class

ORDER = (6,7,10,11,1,8,12,2,13,3,14,15,16,17,18,4,9,0,5)
FIXTURES = (
    (5, 0x707C67CBCE6399F18F2C0F490869033B8B24BBB60CE8FF9D756A981DB6E79EBBDDB84E6C58A,
     (301,61,104,506368),44,3),
    (7, 0xFC7E6C5E017B537CF8C75470F13BF21DB55BFB2C0072EB3F549306AA257D7E1E63D64DE423,
     (317,65,80,753152),132,1),
)


def check_field_profile(p, degree, reciprocal_pairs):
    orbit = {pow(p,i,N) for i in range(degree)}
    assert len(orbit) == degree and pow(p,degree,N) == 1
    assert N-1 not in orbit and 12*22 == 2*degree*reciprocal_pairs


def audit(p, w_mask, expected, degree, reciprocal_pairs):
    check_field_profile(p,degree,reciprocal_pairs)
    _, u_mask, v_mask, w_23, sums, _ = DUAL_FIXTURES[0]
    u, v, w = map(sign_word, (u_mask, v_mask, w_mask))
    assert margins((w,), 13) == (W_13,) and margins((w,), 23) == (w_23,)
    raw = audit_signs(u, v, w, sums)
    measured = (sum(r%16==0 for r in raw),raw.count(0),
                max(map(abs,raw)),sum(r*r for r in raw))
    assert measured == expected
    e = periodic((u,v,w,w))
    e[0] -= 1196
    assert e[0]==0 and all(e[d]==e[-d] for d in range(1,N))
    assert all(sum(e[i::q])==0 for q in (13,23) for i in range(q))
    assert all(r%8==0 for r in e) and any(r%p for r in e)
    assert raw == tuple((-1)**i*e[i%N] for i in range(1,2*N))

    rank = {node:i for i,node in enumerate(ORDER)}
    assert len(rank)==19 and set(rank)==set(range(19))
    edges=0
    for d in range(1,N//2+1):
        v=e[d]
        if abs(v)<8*p:
            continue
        a=residue_class(d,13)
        b=7+residue_class(d,23)
        assert (rank[a]<rank[b])==(v>0)
        edges+=1
    assert edges==21
    print(f"mod {p}: raw {measured}; all {edges} high arcs follow the same exact vertex order")


if __name__=="__main__":
    for fixture in FIXTURES:
        audit(*fixture)
