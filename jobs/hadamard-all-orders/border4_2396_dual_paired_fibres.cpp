#include <algorithm>
#include <array>
#include <bit>
#include <bitset>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <unordered_map>
#include <vector>

namespace {
constexpr int length = 299;
constexpr int half = length / 2;
constexpr int prefix = 16;
using U64 = std::uint64_t;
using Bits = std::bitset<length>;
using Word = std::array<int, length>;
using Mask = std::array<U64, 5>;
using Syndrome = std::array<U64, 3>;
using Correlation = std::array<int, half>;

struct Variant {
    Mask mask{};
    Syndrome parity{};
    Correlation change{};
};
using Deck = std::vector<Variant>;

Syndrome operator^(const Syndrome& a, const Syndrome& b) {
    return {a[0] ^ b[0], a[1] ^ b[1], a[2] ^ b[2]};
}

struct SyndromeHash {
    std::size_t operator()(const Syndrome& a) const {
        U64 x = a[0] ^ std::rotl(a[1], 21) ^ std::rotl(a[2], 42);
        x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
        x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
        return x ^ (x >> 31);
    }
};

struct Row {
    Word signs{};
    Bits plus, support;
    Correlation correlation{};

    Correlation autocorrelation(const Bits& positive) const {
        Correlation out;
        const Bits negative = support ^ positive;
        for (int d = 1; d <= half; ++d) {
            const auto a = (positive << d) | (positive >> (length - d));
            const auto b = (negative << d) | (negative >> (length - d));
            out[d-1] = int((positive & a).count() + (negative & b).count())
                     - int((positive & b).count() + (negative & a).count());
        }
        return out;
    }

    bool balanced(const Mask& mask) const {
        std::array<int, 36> margins{};
        for (unsigned w = 0; w < mask.size(); ++w)
            for (U64 bits = mask[w]; bits; bits &= bits - 1) {
                const unsigned i = 64 * w + std::countr_zero(bits);
                if (i >= length || !support[i]) throw std::runtime_error("invalid signed mask");
                margins[i % 13] += signs[i];
                margins[13 + i % 23] += signs[i];
            }
        return std::all_of(margins.begin(), margins.end(), [](int x) { return x == 0; });
    }

    Variant change_at(const Mask& mask) const {
        Variant result;
        result.mask = mask;
        Bits flipped = plus;
        for (unsigned w = 0; w < mask.size(); ++w)
            for (U64 bits = mask[w]; bits; bits &= bits - 1)
                flipped.flip(64 * w + std::countr_zero(bits));
        const auto after = autocorrelation(flipped);
        for (int d = 0; d < half; ++d) {
            const int change = after[d] - correlation[d];
            if (change % 2) throw std::runtime_error("odd correlation change");
            result.change[d] = change;
            if (change % 4) result.parity[d / 64] |= U64(1) << (d % 64);
        }
        return result;
    }
};

struct Source {
    std::array<Row, 4> rows;
    std::array<Deck, 4> decks;
    Correlation residual;

    Source() {
        residual.fill(2);
        for (unsigned r = 0; r < rows.size(); ++r) {
            auto& row = rows[r];
            for (int i = 0; i < length; ++i) {
                if (!(std::cin >> row.signs[i]) || row.signs[i] < -1 || row.signs[i] > 1)
                    throw std::runtime_error("invalid ternary row");
                if (row.signs[i] != 0) row.support.set(i);
                if (row.signs[i] == 1) row.plus.set(i);
            }
            row.correlation = row.autocorrelation(row.plus);
            for (int d = 0; d < half; ++d) residual[d] += row.correlation[d];
            unsigned count;
            if (!(std::cin >> count)) throw std::runtime_error("missing deck");
            decks[r].reserve(count);
            for (unsigned j = 0; j < count; ++j) {
                Mask mask{};
                for (U64& word : mask) std::cin >> word;
                if (!std::cin || !row.balanced(mask)) throw std::runtime_error("invalid deck");
                decks[r].push_back(row.change_at(mask));
            }
        }
        if (std::any_of(residual.begin(), residual.end(), [](int r) { return r % 4 != 0; }))
            throw std::runtime_error("source lacks raw mod8");
    }

    bool norm_mod7(const std::array<const Variant*, 4>& choices, int first) const {
        for (int d = first; d < half; ++d) {
            int value = residual[d];
            for (const Variant* choice : choices) value += choice->change[d];
            if (value % 7 != 0) return false;
        }
        return true;
    }
};

int mod7(int value) {
    const int r = value % 7;
    return r < 0 ? r + 7 : r;
}

U64 prefix_key(const Variant& a, const Variant& b, const Correlation* residual = nullptr) {
    U64 out = 0;
    for (int d = 0; d < prefix; ++d) {
        const int value = a.change[d] + b.change[d];
        const int wanted = residual ? -(*residual)[d] - value : value;
        out |= U64(mod7(wanted)) << (4 * d);
    }
    return out;
}

void check_single(const Source& source) {
    const auto& [a, b, c, d] = source.decks;
    using Entry = std::array<U64, 3>;
    std::vector<Entry> left;
    left.reserve(a.size() * d.size());
    for (unsigned i = 0; i < a.size(); ++i)
        for (unsigned j = 0; j < d.size(); ++j)
            left.push_back({prefix_key(a[i], d[j]), i, j});
    std::sort(left.begin(), left.end());

    U64 prefix_matches = 0, full_matches = 0;
    for (const auto& u : b) for (const auto& v : c) {
        const U64 key = prefix_key(u, v, &source.residual);
        auto it = std::lower_bound(left.begin(), left.end(), Entry{key, 0, 0});
        for (; it != left.end() && (*it)[0] == key; ++it) {
            ++prefix_matches;
            full_matches += source.norm_mod7({&a[(*it)[1]], &u, &v, &d[(*it)[2]]}, prefix);
        }
    }
    std::cout << "single " << left.size() << ' ' << b.size() * c.size()
              << ' ' << prefix_matches << ' ' << full_matches << '\n';
}

class BinarySpan {
public:
    Syndrome reduce(Syndrome value) const {
        for (int i = half - 1; i >= 0; --i)
            if ((value[i / 64] >> (i % 64) & 1) && used[i])
                value = value ^ pivot[i];
        return value;
    }

    void add(Syndrome value) {
        value = reduce(value);
        for (int i = half - 1; i >= 0; --i) {
            if (value[i / 64] >> (i % 64) & 1) {
                pivot[i] = value;
                used[i] = true;
                return;
            }
        }
    }

private:
    std::array<Syndrome, half> pivot{};
    std::array<bool, half> used{};
};

void check_double(const Source& source, int doubled) {
    const auto& heads = source.decks[doubled];
    const auto& other = source.decks[doubled ^ 1];
    const auto& c = source.decks[2];
    const auto& d = source.decks[3];
    BinarySpan span;
    for (const auto& h : heads) span.add(h.parity);

    struct Tail {
        Syndrome parity;
        unsigned c, d;
    };
    std::unordered_map<Syndrome, std::vector<Tail>, SyndromeHash> tails;
    for (unsigned i = 0; i < c.size(); ++i) for (unsigned j = 0; j < d.size(); ++j) {
        auto parity = c[i].parity ^ d[j].parity;
        tails[span.reduce(parity)].push_back({parity, i, j});
    }

    using Other = std::array<unsigned, 3>;
    std::unordered_map<Syndrome, std::vector<Other>, SyndromeHash> targets;
    for (unsigned j = 0; j < other.size(); ++j) {
        const auto it = tails.find(span.reduce(other[j].parity));
        if (it == tails.end()) continue;
        for (const auto& tail : it->second)
            targets[other[j].parity ^ tail.parity].push_back({j, tail.c, tail.d});
    }

    U64 parity_pairs = 0, physical_matches = 0, full_matches = 0;
    const auto& word = source.rows[doubled];
    for (unsigned i = 0; i < heads.size(); ++i) for (unsigned j = 0; j < i; ++j) {
        const Syndrome sum = heads[i].parity ^ heads[j].parity;
        const auto needed = targets.find(sum);
        if (needed == targets.end()) continue;
        ++parity_pairs;
        Mask intersection{}, combined{};
        for (unsigned limb = 0; limb < combined.size(); ++limb) {
            intersection[limb] = heads[i].mask[limb] & heads[j].mask[limb];
            combined[limb] = heads[i].mask[limb] ^ heads[j].mask[limb];
        }
        if (!word.balanced(intersection)) continue;
        const Variant head = word.change_at(combined);
        if (head.parity != sum) throw std::runtime_error("incorrect parity composition");
        for (const auto& [h, u, v] : needed->second) {
            std::array<const Variant*, 4> choices{};
            choices[doubled] = &head;
            choices[doubled ^ 1] = &other[h];
            choices[2] = &c[u];
            choices[3] = &d[v];
            ++physical_matches;
            full_matches += source.norm_mod7(choices, 0);
        }
    }
    const U64 all_pairs = U64(heads.size()) * (heads.size() - 1) / 2;
    std::cout << "double " << doubled << ' ' << all_pairs << ' ' << parity_pairs
              << ' ' << physical_matches << ' ' << full_matches << '\n';
}
}

int main() {
    const Source source;
    check_single(source);
    check_double(source, 0);
    check_double(source, 1);
}
