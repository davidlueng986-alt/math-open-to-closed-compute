// Keep the same exact autocorrelation and interval-bitset routines as the peak-40 census.
#if defined(__GNUC__)
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wreturn-type"
#endif
#define main peak40_reference_main
#include "border4_2396_dual_peak40.cpp"
#undef main
#if defined(__GNUC__)
#pragma GCC diagnostic pop
#endif
#include <unordered_set>

namespace {
struct Head {
    Gram gram;
    Mask mask;
};

std::vector<Head> make_heads(std::istream& in, const Row& row) {
    unsigned count;
    in >> count;
    assert(count > 0 && count <= 12);
    std::vector<Block> blocks(count);
    for (auto& block : blocks) {
        unsigned size;
        in >> size;
        assert(size > 1 && size <= 8192);
        block.resize(size);
        for (auto& option : block) {
            U low, high;
            in >> low >> high;
            option.charge = Key(low) | (Key(high) << 64);
            for (auto& limb : option.mask) in >> limb;
        }
    }
    assert(in);

    unsigned partition = 0;
    U bound = std::numeric_limits<U>::max();
    for (unsigned m = 0; m < (1U << count); ++m) {
        U left = 1, right = 1;
        for (unsigned i = 0; i < count; ++i)
            (m >> i & 1U ? left : right) *= blocks[i].size();
        if (std::max(left, right) >= bound) continue;
        bound = std::max(left, right);
        partition = left <= right ? m : ((1U << count) - 1) ^ m;
    }
    Split left, right;
    for (unsigned j = 0; j < count; ++j)
        (partition >> j & 1U ? left : right).push_back(&blocks[j]);

    std::vector<Local> table;
    visit(left, 0, {}, [&](const Local& x) { table.push_back(x); });
    const auto by_charge = [](const Local& x, const Local& y) { return x.charge < y.charge; };
    std::sort(table.begin(), table.end(), by_charge);

    const auto original = paf(row, {});
    std::vector<Head> heads;
    visit(right, 0, {}, [&](const Local& next) {
        const Key target = Key(0) - next.charge;
        auto p = std::lower_bound(table.begin(), table.end(), Local{target, {}}, by_charge);
        for (; p != table.end() && p->charge == target; ++p) {
            Local candidate = *p;
            candidate += next;
            const auto gram = paf(row, candidate.mask);
            for (unsigned d = 0; d < gram.size(); ++d)
                assert((gram[d] - original[d]) % 4 == 0);
            heads.push_back({gram, candidate.mask});
        }
    });
    return heads;
}

using Residues = std::array<std::uint32_t, 3>;
struct ResidueHash {
    U operator()(const Residues& code) const {
        return U(code[0]) ^ std::rotl(U(code[1]), 23) ^ std::rotl(U(code[2]), 46);
    }
};

Residues pack(const Gram& gram, unsigned length, int p, bool complement) {
    Residues result{};
    for (unsigned d = 0; d < length; ++d) {
        int r = (complement ? -2 - gram[d] : gram[d]) % p;
        if (r < 0) r += p;
        result[d / 8] |= std::uint32_t(r) << (4 * (d % 8));
    }
    return result;
}

Residues field_add(const Residues& left, const Residues& right, unsigned p) {
    Residues result;
    for (unsigned i = 0; i < result.size(); ++i) {
        const std::uint32_t sum = left[i] + right[i];
        const auto flags = ((sum + (8 - p) * 0x11111111U) & 0x88888888U) >> 3;
        result[i] = sum - p * flags;
    }
    return result;
}

void check_prefix(const std::array<std::vector<Head>, 2>& heads,
                  const std::vector<Gram>& tails, int p, unsigned length) {
    std::unordered_multiset<Residues, ResidueHash> lookup;
    for (const auto& tail : tails) lookup.insert(pack(tail, length, p, true));
    std::array<std::vector<Residues>, 2> letters;
    for (unsigned r = 0; r < heads.size(); ++r)
        for (const auto& h : heads[r]) letters[r].push_back(pack(h.gram, length, p, false));

    U matches = 0;
    for (const auto& left : letters[0])
        for (const auto& right : letters[1])
            matches += lookup.count(field_add(left, right, p));
    std::cout << "prefix " << p << ' ' << length << ' ' << matches << '\n';
}

void check_interval(const std::array<std::vector<Head>, 2>& heads, const std::vector<Gram>& tails) {
    constexpr unsigned filter_lags = 24;
    constexpr int cap = 24;
    std::vector<Gram> right;
    for (const auto& h : heads[1]) right.push_back(h.gram);
    std::vector<Filter> filters;
    for (int d = 0; d < lags; ++d) filters.emplace_back(d, right, cap);
    std::vector<U> candidates(filters[0].words);
    unsigned low = 0, high = 0;
    for (unsigned t = 0; t < tails.size(); ++t) for (const auto& a : heads[0]) {
        std::array<std::pair<int, int>, lags> order;
        std::array<int, lags> keys;
        bool possible = true;
        for (int d = 0; d < lags; ++d) {
            const auto& f = filters[d];
            const int k = f.index(-2 - a.gram[d] - tails[t][d]);
            if (k < 0 || f.count[k] == 0) {
                possible = false;
                break;
            }
            keys[d] = k;
            order[d] = {f.count[k], d};
        }
        if (!possible) continue;
        std::partial_sort(order.begin(), order.begin() + filter_lags, order.end());
        const int first = order.front().second;
        const auto* start = filters[first].set(keys[first]);
        std::copy_n(start, candidates.size(), candidates.begin());
        for (unsigned j = 1; j < filter_lags; ++j) {
            const int d = order[j].second;
            const auto* mask = filters[d].set(keys[d]);
            U any = 0;
            for (unsigned k = 0; k < candidates.size(); ++k) {
                candidates[k] &= mask[k];
                any |= candidates[k];
            }
            if (!any) break;
        }
        for (unsigned k = 0; k < candidates.size(); ++k)
            for (U bits = candidates[k]; bits; bits &= bits - 1) {
                const auto& b = heads[1][64 * k + std::countr_zero(bits)];
                bool in_range = true;
                int peak = 0;
                for (int d = 0; d < lags; ++d) {
                    peak = std::max(peak, std::abs(2 + a.gram[d] + b.gram[d] + tails[t][d]));
                    if (peak > cap) {
                        in_range = false;
                        break;
                    }
                }
                if (!in_range) continue;
                low += peak <= 20;
                ++high;
                std::cout << "hit " << t;
                for (const auto& mask : {a.mask, b.mask})
                    for (U limb : mask) std::cout << ' ' << limb;
                std::cout << '\n';
            }
    }
    std::cout << "interval " << low << ' ' << high << '\n';
}
}

int main() {
    std::array<Row, 2> source;
    for (auto& row : source) for (auto& x : row) std::cin >> x;
    int count;
    std::cin >> count;
    assert(count == 816);
    std::vector<Gram> tails;
    const auto a = paf(source[0], {}), b = paf(source[1], {});
    for (int j = 0; j < count; ++j) {
        Row u, v;
        for (auto& x : u) std::cin >> x;
        for (auto& x : v) std::cin >> x;
        auto t = paf(u, {});
        const auto other = paf(v, {});
        for (unsigned d = 0; d < t.size(); ++d) {
            t[d] += other[d];
            assert((2 + a[d] + b[d] + t[d]) % 4 == 0);
        }
        tails.push_back(t);
    }
    const std::array heads{make_heads(std::cin, source[0]), make_heads(std::cin, source[1])};
    std::cout << "decks " << heads[0].size() << ' ' << heads[1].size() << ' ' << tails.size() << '\n';
    check_prefix(heads, tails, 5, 24);
    check_prefix(heads, tails, 7, 16);
    check_interval(heads, tails);
}
