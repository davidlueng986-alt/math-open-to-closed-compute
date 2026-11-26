"""Replay low-amplitude and lower-energy dual-quotient witnesses."""

from border4_2396 import periodic
from border4_2396_dual_quotient import dual_words, replay
from border4_2396_nested import nested_negative_words
from border4_2396_primitive_field import primitive_factor, product, remainder


N = 299
PEAK48_MASKS = (
    0x71140800208006703283844404C1822899001202082300003EA000110008700A84D01005808,
    0x320918780002700000300C03C0830CD0640E00082200102E00201F024928A000806102C09,
    0x282450080792108805954008844006020100002018000423110884006010A808060300C600,
    0x1448280018C0301804054201800844223108000601000020101800884400AA680442127804,
)
PEAK48_MORE_MOD16_MASKS = (
    0x71140000209006703203840504C1822899041200082300003EA020110008700A84D01005808,
    0x320918780002700000300C03C0830CD0640E00082200102E00201F024928A000806102C09,
    0x682050080792108805954008840006020100002018000423110804006010A808060300C600,
    0x14082C0018C0301804054201800804223108000601000020101800084400AA680442127804,
)
LOW_ENERGY_MASKS = (
    0x315C0800348007B83083D44004C1822C194000020832010038A000950009900085900003808,
    0x10580118240002202081704507C0130010640D00002200802A0020DB0208D8A400D02106E01,
    0x23821580805921008049460088400020300000020180402231108C40060103828040303C000,
    0x3508388000F03008050702018008C42231100806010000003010000844018A480402126804,
)


def check_primitive_norm(words, residual, factor):
    norm = [0] * (len(factor) - 1)
    for word in words:
        a = remainder(word, factor, 7)
        b = remainder((word[0], *word[:0:-1]), factor, 7)
        for i, value in enumerate(remainder(product(a, b, 7), factor, 7)):
            norm[i] += value
    norm[0] -= 599
    reduced = tuple(remainder(residual, factor, 7))
    assert tuple(value % 7 for value in norm) == tuple(4 * value % 7 for value in reduced)
    return sum(value != 0 for value in reduced)


def main():
    negative = nested_negative_words()
    assert periodic(negative) == [599] + [0] * (N - 1)
    factor = primitive_factor(7)
    fixtures = (
        ("Peak 48, lower energy", PEAK48_MASKS, (317, 77, 48, 215552), 145, 77, 120),
        ("Peak 48, more mod16", PEAK48_MORE_MOD16_MASKS, (365, 85, 48, 260608), 181, 85, 112),
        ("Lower energy", LOW_ENERGY_MASKS, (349, 165, 80, 214528), 213, 165, 118),
    )
    for name, masks, metrics, mod32, mod64, nonzero in fixtures:
        positive = dual_words(masks)
        assert tuple(map(sum, positive)) == (0, 1, 0, 0)
        residual = replay(positive, negative, metrics, mod32, metrics[2] // 8)
        assert 1 + 2 * sum(value % 8 == 0 for value in residual[1:]) == mod64
        assert check_primitive_norm(positive, residual, factor) == nonzero
        if metrics[2] == 48:
            assert max(map(abs, residual)) == 6 < 7
        print(f"{name}: mod16/exact/peak/energy {metrics}; "
              f"mod32 {mod32}, mod64 {mod64}, mod7 primitive nonzero {nonzero}.")


if __name__ == "__main__":
    main()
