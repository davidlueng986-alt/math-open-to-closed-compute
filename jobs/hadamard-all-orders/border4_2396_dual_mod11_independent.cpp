#include <algorithm>
#include <array>
#include <bit>
#include <bitset>
#include <cstdint>
#include <iostream>
#include <set>
#include <stdexcept>
#include <vector>

namespace {
constexpr int length = 299;
constexpr int half = length / 2;
constexpr int prefix = 16;
using UInt = std::uint64_t;
using MarginKey = __int128;
using Bits = std::bitset<length>;
using Mask = std::array<UInt, 5>;
using Residues = std::array<int, prefix>;

struct Pair {
    int plus_offset, minus_offset;
    MarginKey margins;
};

struct Subset {
    MarginKey margins;
    unsigned bits;
    bool operator<(const Subset& other) const { return margins < other.margins; }
};

struct Row {
    std::array<int, length> signs{};
    Bits plus, support;
};

struct Variant {
    Bits plus;
    Residues differences;
};

MarginKey margin_key(int offset, int sign) {
    MarginKey result = 0;
    for (int q : {13, 23}) {
        int r = offset % q;
        if (r == 0) continue;
        int digit = (q == 13 ? 0 : 6) + std::min(r, q - r) - 1;
        int coefficient = (2 * r < q ? sign : -sign);
        result += MarginKey(coefficient) * (MarginKey(1) << (6 * digit));
    }
    return result;
}

void include(Mask& mask, const Pair& pair) {
    for (int i : {pair.plus_offset, pair.minus_offset})
        mask[i / 64] |= UInt(1) << (i % 64);
}

void collect_axis(const Row& row, int center, std::set<Mask>& masks,
                  UInt& occurrences, int& max_pairs) {
    std::vector<Pair> pairs;
    for (int d = 1; d <= half; ++d) {
        int a = (center + d) % length;
        int b = (center + length - d) % length;
        if (row.signs[a] != 0 && row.signs[b] == -row.signs[a])
            pairs.push_back({a, b, margin_key(d, row.signs[a])});
    }
    max_pairs = std::max(max_pairs, int(pairs.size()));
    if (pairs.size() > 48) throw std::runtime_error("reflection deck exceeds checked bounds");
    int split = pairs.size() / 2, right = int(pairs.size()) - split;
    std::vector<Subset> left;
    left.reserve(1U << split);
    unsigned mask = 0;
    MarginKey sum = 0;
    for (unsigned i = 0; i < (1U << split); ++i) {
        if (i != 0) {
            int bit = std::countr_zero(i);
            mask ^= 1U << bit;
            sum += (mask >> bit & 1U) ? pairs[bit].margins : -pairs[bit].margins;
        }
        left.push_back({sum, mask});
    }
    std::sort(left.begin(), left.end());
    mask = 0;
    sum = 0;
    for (unsigned i = 0; i < (1U << right); ++i) {
        if (i != 0) {
            int bit = std::countr_zero(i);
            mask ^= 1U << bit;
            sum += (mask >> bit & 1U) ? pairs[split + bit].margins : -pairs[split + bit].margins;
        }
        auto it = std::lower_bound(left.begin(), left.end(), Subset{-sum, 0});
        for (; it != left.end() && it->margins == -sum; ++it) {
            Mask combined{};
            for (unsigned b = it->bits; b != 0; b &= b - 1) include(combined, pairs[std::countr_zero(b)]);
            for (unsigned b = mask; b != 0; b &= b - 1) include(combined, pairs[split + std::countr_zero(b)]);
            masks.insert(combined);
            ++occurrences;
        }
    }
}

int autocorrelation(const Bits& plus, const Bits& support, int lag) {
    const auto minus = support ^ plus;
    const auto a = (plus << lag) | (plus >> (length - lag));
    const auto b = (minus << lag) | (minus >> (length - lag));
    return int((a & plus).count() + (b & minus).count())
         - int((a & minus).count() + (b & plus).count());
}

int mod11(int value) {
    int residue = value % 11;
    return residue < 0 ? residue + 11 : residue;
}

std::vector<Variant> make_deck(const Row& row, unsigned index) {
    std::set<Mask> masks;
    UInt occurrences = 0;
    int max_pairs = 0;
    for (int center = 0; center < length; ++center)
        collect_axis(row, center, masks, occurrences, max_pairs);
    constexpr std::array expected_pairs{36, 43, 30, 29};
    constexpr std::array<UInt, 4> expected_occurrences{6154, 334570, 313, 353};
    constexpr std::array<UInt, 4> expected_masks{5856, 334272, 15, 55};
    if (max_pairs != expected_pairs[index] || occurrences != expected_occurrences[index] ||
        masks.size() != expected_masks[index])
        throw std::runtime_error("unexpected reflection deck counts");
    std::cout << "Row " << index + 1 << ", maximum pairs " << max_pairs
              << ", axis occurrences " << occurrences << ", distinct masks " << masks.size() << '\n';

    Residues base;
    for (int d = 1; d <= prefix; ++d) base[d - 1] = autocorrelation(row.plus, row.support, d);
    std::vector<Variant> deck;
    deck.reserve(masks.size());
    for (const auto& mask : masks) {
        std::array<int, 36> margins{};
        Bits changed = row.plus;
        for (unsigned word = 0; word < mask.size(); ++word)
            for (UInt bits = mask[word]; bits != 0; bits &= bits - 1) {
                unsigned i = 64 * word + std::countr_zero(bits);
                if (i >= length || !row.support[i]) throw std::runtime_error("invalid switch mask");
                changed.flip(i);
                margins[i % 13] += row.signs[i];
                margins[13 + i % 23] += row.signs[i];
            }
        if (std::any_of(margins.begin(), margins.end(), [](int x) { return x != 0; }))
            throw std::runtime_error("invalid signed quotient margins");
        Residues differences;
        for (int d = 1; d <= prefix; ++d)
            differences[d - 1] = mod11(autocorrelation(changed, row.support, d) - base[d - 1]);
        deck.push_back({changed, differences});
    }
    return deck;
}

UInt prefix_key(const Residues& a, const Residues& b, const Residues* target = nullptr) {
    UInt result = 0;
    for (int d = 0; d < prefix; ++d) {
        int sum = a[d] + b[d];
        if (target) sum = (*target)[d] - sum;
        result |= UInt(mod11(sum)) << (4 * d);
    }
    return result;
}

bool meets_all_lags(const std::array<Row, 4>& rows, const std::array<const Variant*, 4>& choices) {
    for (int d = prefix + 1; d <= half; ++d) {
        int total = 2;
        for (int i = 0; i < 4; ++i)
            total += autocorrelation(choices[i]->plus, rows[i].support, d);
        if (mod11(total) != 0) return false;
    }
    return true;
}
}

int main() {
    std::array<Row, 4> rows;
    std::array<std::vector<Variant>, 4> decks;
    Residues target;
    target.fill(-2);
    for (unsigned i = 0; i < rows.size(); ++i) {
        auto& row = rows[i];
        for (int j = 0; j < length; ++j) {
            if (!(std::cin >> row.signs[j]) || row.signs[j] < -1 || row.signs[j] > 1)
                throw std::runtime_error("invalid ternary input row");
            if (row.signs[j] != 0) row.support.set(j);
            if (row.signs[j] == 1) row.plus.set(j);
        }
        decks[i] = make_deck(row, i);
        for (int d = 1; d <= prefix; ++d)
            target[d - 1] -= autocorrelation(row.plus, row.support, d);
    }

    using Entry = std::array<UInt, 3>;
    std::vector<Entry> lookup;
    const auto& [a, b, c, d] = decks;
    lookup.reserve(a.size() * d.size());
    for (unsigned i = 0; i < a.size(); ++i)
        for (unsigned j = 0; j < d.size(); ++j)
            lookup.push_back({prefix_key(a[i].differences, d[j].differences), i, j});
    std::sort(lookup.begin(), lookup.end());

    UInt short_matches = 0, full_matches = 0;
    for (const auto& middle : b) for (const auto& tail : c) {
        UInt need = prefix_key(middle.differences, tail.differences, &target);
        auto first = std::lower_bound(lookup.begin(), lookup.end(), Entry{need, 0, 0});
        for (auto it = first; it != lookup.end() && (*it)[0] == need; ++it) {
            ++short_matches;
            full_matches += meets_all_lags(rows, {&a[(*it)[1]], &middle, &tail, &d[(*it)[2]]});
        }
    }
    std::cout << "Pair decks " << lookup.size() << " and " << b.size() * c.size()
              << ", first 16 matching " << short_matches << ", all matching " << full_matches << '\n';
    return short_matches == 0 ? 0 : 1;
}
