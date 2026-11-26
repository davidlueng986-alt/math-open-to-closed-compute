"""Verify local norm obstructions on eight exact-dual physical Paley words."""

import json
from pathlib import Path

from border4_2396_paley_dual_integer import audit_signs
from border4_2396_paley_head_obstruction import check_inert_valuation_one, cosine_bounds, power_interval
from border4_2396_paley_negative_norm import N, periodic, sign_word


def main():
    fixtures = json.loads(Path(__file__).with_suffix(".json").read_text())
    assert [fixture["seed"] for fixture in fixtures] == [5031, 5055, 5058, 5059, 5065, 5075, 5112, 5128]
    scale, bounds = cosine_bounds()
    for fixture in fixtures:
        u, v, w = (sign_word(int(mask, 16)) for mask in fixture["masks"])
        raw = audit_signs(u, v, w, (17, -5, -21))
        assert all(value % 8 == 0 for value in raw)
        e = periodic((u, v, w, w))
        e[0] -= 1196
        assert all(sum(e[d::q]) == 0 for q in (13, 23) for d in range(q))
        head = periodic((u, v))
        assert max(power_interval(head, d, scale, bounds)[1] for d in range(N//2+1)) < 1196*scale
        prime, trace, value = fixture["norm_certificate"]
        check_inert_valuation_one(head, prime, trace, value)
        print(f'Seed {fixture["seed"]}: physical dual quotients and odd valuation at inert prime {prime}')


if __name__ == "__main__":
    main()
