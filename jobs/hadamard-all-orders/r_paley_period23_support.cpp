#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <string_view>
#include <unordered_map>
#include <vector>

constexpr int side = 92;
constexpr int period = 23;
using Word = std::array<uint64_t, 2>;
using Matrix = std::array<Word, side>;
using Units = std::array<std::array<int, 4>, 4>;
using Selector = std::array<int, period>;
using Overlap = std::array<int, 6>;
using Weights = std::array<Overlap, side>;
using Face = std::array<int, 4>;
using Binomial = std::array<std::array<int, 5>, side + 1>;

struct Projection {
    Matrix sign{};
    Matrix positive{};
    Matrix negative{};
};

struct Block {
    int component;
    int sign;
    int type;
};

constexpr Block blocks[4][4] = {
    {{0, 1, 0}, {1, 1, 1}, {2, 1, 1}, {3, 1, 1}},
    {{1, -1, 1}, {0, 1, 0}, {3, -1, 2}, {2, 1, 2}},
    {{2, -1, 1}, {3, 1, 2}, {0, 1, 0}, {1, -1, 2}},
    {{3, -1, 1}, {2, -1, 2}, {1, 1, 2}, {0, 1, 0}},
};

std::vector<uint64_t> correlation_keys(int length) {
    std::vector<uint64_t> out(1 << (length - 1));
    for (int i = 0; i < static_cast<int>(out.size()); ++i) {
        const int word = 2 * i + 1;
        for (int shift = 1; shift <= 10; ++shift) {
            const int size = length - shift;
            const int diff = __builtin_popcount((word ^ (word >> shift)) & ((1 << size) - 1));
            out[i] |= uint64_t(size - 2 * diff + 12) << (6 * (shift - 1));
        }
    }
    return out;
}

void emit_base_sequences() {
    const auto longs = correlation_keys(12);
    const auto shorts = correlation_keys(11);
    std::unordered_map<uint64_t, std::vector<unsigned>> pairs;
    for (unsigned i = 0; i < shorts.size(); ++i)
        for (unsigned j = i; j < shorts.size(); ++j)
            pairs[shorts[i] + shorts[j]].push_back((i << 10) | j);
    uint64_t target = 0;
    for (int s = 0; s < 10; ++s) target |= 48ULL << (6 * s);
    int matched_long = 0;
    int matched_full = 0;
    for (unsigned i = 0; i < longs.size(); ++i) for (unsigned j = i; j < longs.size(); ++j) {
        if (((i ^ j) >> 10) != 1) continue;  // The two shift-11 terms cancel.
        const auto found = pairs.find(target - longs[i] - longs[j]);
        if (found == pairs.end()) continue;
        ++matched_long;
        for (unsigned pair : found->second) {
            ++matched_full;
            std::cout << (2 * i + 1) << ' ' << (2 * j + 1) << ' '
                      << (2 * (pair >> 10) + 1) << ' ' << (2 * (pair & 1023) + 1) << '\n';
        }
    }
    assert(matched_long == 560 && matched_full == 4416);
}

Word xor_words(Word a, Word b) { return {a[0] ^ b[0], a[1] ^ b[1]}; }
int count(Word a) { return __builtin_popcountll(a[0]) + __builtin_popcountll(a[1]); }
int intersection(Word a, Word b) { return count({a[0] & b[0], a[1] & b[1]}); }
void mark(Word& a, int i) { a[i / 64] |= 1ULL << (i % 64); }

Projection project(const Selector& selector, const Units& sign, const Units& sparse) {
    Projection out;
    for (int cb = 0; cb < 4; ++cb) for (int c = 0; c < period; ++c) {
        const int j = cb * period + c;
        for (int rb = 0; rb < 4; ++rb) for (int r = 0; r < period; ++r) {
            const Block block = blocks[rb][cb];
            const int coordinate = block.type == 0 ? c - r + period
                                 : block.type == 1 ? 2 * period - 1 - c - r : 1 + c + r;
            const int symbol = selector[coordinate % period];
            const int unit = std::abs(symbol) - 1;
            const int phase = symbol > 0 ? block.sign : -block.sign;
            const int h = phase * sign[unit][block.component];
            const int a = phase * sparse[unit][block.component];
            const int i = rb * period + r;
            assert(std::abs(h) == 1 && (a == 0 || a == h));
            if (h > 0) mark(out.sign[j], i);
            if (a > 0) mark(out.positive[j], i);
            if (a < 0) mark(out.negative[j], i);
        }
    }
    return out;
}

int sign_sparse(const Projection& data, int i, int j) {
    const int pos = intersection(data.sign[i], data.positive[j]);
    const int neg = intersection(data.sign[i], data.negative[j]);
    return 2 * (pos - neg) - count(data.positive[j]) + count(data.negative[j]);
}

void check_projection(const Projection& data, const Weights& weights, Overlap& maxima) {
    for (int i = 0; i < side; ++i) {
        assert(count(data.positive[i]) + count(data.negative[i]) == 23);
        Overlap overlaps{};
        for (int j = 0; j < side; ++j) {
            const int sign_dot = side - 2 * count(xor_words(data.sign[i], data.sign[j]));
            const int a_dot = intersection(data.positive[i], data.positive[j])
                            + intersection(data.negative[i], data.negative[j])
                            - intersection(data.negative[i], data.positive[j])
                            - intersection(data.positive[i], data.negative[j]);
            const int cross = sign_sparse(data, i, j);
            assert(sign_dot == (i == j ? 92 : 0));
            assert(a_dot == (i == j ? 23 : 0));
            assert(cross + sign_sparse(data, j, i) == (i == j ? 46 : 0));
            if (std::abs(3 * sign_dot + 2 * cross) == 2)
                for (int k = 0; k < 6; ++k) overlaps[k] += weights[j][k];
        }
        for (int k = 0; k < 6; ++k) maxima[k] = std::max(maxima[k], overlaps[k]);
    }
}

Binomial binomial_table() {
    Binomial out{};
    for (int n = 0; n <= side; ++n) {
        out[n][0] = 1;
        for (int k = 1; k <= std::min(n, 4); ++k)
            out[n][k] = out[n - 1][k] + out[n - 1][k - 1];
    }
    return out;
}

int face_index(const Binomial& c, int a, int b, int d, int e) {
    return c[a][1] + c[b][2] + c[d][3] + c[e][4];
}

void check_profile(const Matrix& h, const Binomial& c, std::array<uint64_t, 4>& counts) {
    std::vector<uint8_t> faces(c[side][4]);
    std::vector<Face> largest;
    for (int d = 3; d < side; ++d) for (int k = 2; k < d; ++k)
        for (int b = 1; b < k; ++b) for (int a = 0; a < b; ++a) {
            const Word word = xor_words(xor_words(h[a], h[b]), xor_words(h[k], h[d]));
            const int magnitude = std::abs(side - 2 * count(word));
            if (magnitude <= 36 && magnitude % 8 == 4)
                faces[face_index(c, a, b, k, d)] = 1u << (magnitude / 8);
            if (magnitude == 36) largest.push_back({a, b, k, d});
        }
    counts[0] += faces.size();
    counts[1] += largest.size();
    constexpr std::array<int, 11> profile{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12};
    for (const auto& f : largest) for (int j = 0; j < side; ++j) {
        if (std::find(f.begin(), f.end(), j) != f.end()) continue;
        std::array<int, 5> vertices{f[0], f[1], f[2], f[3], j};
        std::sort(vertices.begin(), vertices.end());
        const auto [a, b, k, d, e] = vertices;
        const int first = faces[face_index(c, a, b, k, d)];
        if (!first) continue;
        const int second = faces[face_index(c, a, b, k, e)];
        if (!second || (second & first)) continue;
        const int third = faces[face_index(c, a, b, d, e)];
        if (!third || (third & (first | second))) continue;
        const int fourth = faces[face_index(c, a, k, d, e)];
        if (!fourth || (fourth & (first | second | third))) continue;
        const int fifth = faces[face_index(c, b, k, d, e)];
        if (!fifth || (fifth & (first | second | third | fourth))) continue;
        ++counts[2];
        const Word word = xor_words(xor_words(xor_words(h[a], h[b]), xor_words(h[k], h[d])), h[e]);
        std::vector<int> deck;
        for (auto col : h) {
            const int magnitude = std::abs(side - 2 * count(xor_words(word, col)));
            assert(magnitude % 4 == 0);
            if (magnitude) deck.push_back(magnitude / 4);
        }
        if (deck.size() != profile.size()) continue;
        std::sort(deck.begin(), deck.end());
        if (std::equal(deck.begin(), deck.end(), profile.begin())) ++counts[3];
    }
}

void check_selectors() {
    Units sign{}, sparse{};
    for (auto* u : {&sign, &sparse}) for (auto& row : *u) for (int& v : row) std::cin >> v;
    Weights weights{};
    for (auto& row : weights) for (int& v : row) std::cin >> v;
    int size;
    std::cin >> size;
    const auto table = binomial_table();
    assert(table[side][4] == 2794155);
    std::array<uint64_t, 4> counts{};
    Overlap maxima{};
    for (int i = 0; i < size; ++i) {
        Selector entries;
        for (int& v : entries) {
            std::cin >> v;
            assert(1 <= std::abs(v) && std::abs(v) <= 4);
        }
        assert(std::cin);
        const auto matrices = project(entries, sign, sparse);
        check_projection(matrices, weights, maxima);
        check_profile(matrices.sign, table, counts);
    }
    std::cout << "support " << size;
    for (uint64_t n : counts) std::cout << ' ' << n;
    std::cout << "\noverlap";
    for (int n : maxima) std::cout << ' ' << n;
    std::cout << '\n';
}

int main(int argc, char** argv) {
    assert(argc == 2);
    if (std::string_view(argv[1]) == "bases") emit_base_sequences();
    else {
        assert(std::string_view(argv[1]) == "check");
        check_selectors();
    }
}
