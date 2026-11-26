#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <string_view>
#include <vector>
#ifdef __AVX2__
#include <immintrin.h>
#endif

using Row = std::array<int16_t, 16>;
using Deck = std::array<Row, 4>;
using Source = std::array<Deck, 52>;
constexpr int signs13 = 1 << 13;

int two_levels(const Row& a, const Row& b, int length) {
    Row values{};
    int best = 0;
#ifdef __AVX2__
    const auto x = _mm256_loadu_si256(reinterpret_cast<const __m256i*>(a.data()));
    const auto y = _mm256_loadu_si256(reinterpret_cast<const __m256i*>(b.data()));
    const auto sum = _mm256_add_epi16(x, y);
    const auto lower = _mm256_sub_epi16(sum, _mm256_set1_epi16(4));
    const uint32_t slots = (1u << (2 * length)) - 1;
    _mm256_storeu_si256(reinterpret_cast<__m256i*>(values.data()), sum);
    for (uint32_t remaining = slots; remaining;) {
        const int i = __builtin_ctz(remaining) / 2;
        const auto base = _mm256_set1_epi16(values[i]);
        const uint32_t same = _mm256_movemask_epi8(_mm256_cmpeq_epi16(sum, base));
        const uint32_t next = _mm256_movemask_epi8(_mm256_cmpeq_epi16(lower, base));
        best = std::max(best, __builtin_popcount((same | next) & slots) / 2);
        remaining &= ~same;
    }
#else
    for (int j = 0; j < length; ++j) values[j] = a[j] + b[j];
    for (int j = 0; j < length; ++j) {
        int count = 0;
        for (int i = 0; i < length; ++i)
            count += values[i] == values[j] || values[i] == values[j] + 4;
        best = std::max(best, count);
    }
#endif
    return best;
}

std::vector<Deck> signed_decks(const Source& source, int block) {
    std::vector<Deck> out(signs13);
    for (int r = 0; r < 13; ++r) for (int b = 0; b < 4; ++b)
        for (int j = 0; j < 16; ++j) out[0][b][j] -= source[13 * block + r][b][j];
    for (int word = 1; word < signs13; ++word) {
        const int r = __builtin_ctz(unsigned(word));
        out[word] = out[word & (word - 1)];
        for (int b = 0; b < 4; ++b) for (int j = 0; j < 16; ++j)
            out[word][b][j] += 2 * source[13 * block + r][b][j];
    }
    return out;
}

void check_alpha() {
    for (int pair = 0; pair < 2; ++pair) {
        std::array<int,4> sizes, sectors;
        for (int& n : sizes) std::cin >> n;
        for (int& s : sectors) std::cin >> s;
        Source cols{};
        for (auto& rows : cols) for (int b = 0; b < 4; ++b)
            for (int j = 0; j < sizes[b]; ++j) std::cin >> rows[b][j];
        assert(std::cin);
        std::array<std::vector<Deck>, 4> decks;
        for (int b = 0; b < 4; ++b) decks[b] = signed_decks(cols, b);
        std::array<std::array<int, 2>, 2> blocks{};
        for (int s = 0; s < 2; ++s) {
            int k = 0;
            for (int b = 0; b < 4; ++b) if (sectors[b] == s) blocks[s][k++] = b;
            assert(k == 2);
            if (sizes[blocks[s][0]] != 12) std::swap(blocks[s][0], blocks[s][1]);
            assert(sizes[blocks[s][0]] == 12 && sizes[blocks[s][1]] == 4);
        }
        int largest = 0;
        for (const auto& d : decks) for (int q = 1; q < signs13 - 1; ++q) {
            int count = 0;
            for (int b = 0; b < 4; ++b) count += two_levels(d[q][b], Row{}, sizes[b]);
            largest = std::max(largest, count);
        }
        std::cout << "one " << pair << ' ' << largest << '\n';
        for (int u = 0; u < 4; ++u) for (int v = u + 1; v < 4; ++v) {
            uint64_t tried = 0, passes = 0;
            for (int p = 1; p < signs13 - 1; p += 2) for (int q = 1; q < signs13 - 1; ++q) {
                ++tried;
                bool possible = true;
                for (auto [a,b] : blocks) {
                    const int heavy = two_levels(decks[u][p][a], decks[v][q][a], 12);
                    if (heavy < 10 || heavy + two_levels(decks[u][p][b], decks[v][q][b], 4) < 14) {
                        possible = false;
                        break;
                    }
                }
                passes += possible;
            }
            std::cout << "two " << pair << ' ' << u << ' ' << v << ' ' << tried << ' ' << passes << '\n';
        }
    }
}

constexpr int period = 23;
constexpr unsigned full = (1u << period) - 1;
using BetaRow = std::array<int16_t, 32>;
using Profile = std::array<BetaRow, 6>;
using Words = std::array<std::array<int, period>, 4>;
// F0, F1, F2, R2, F3, R3. F uses w(c-r); R uses w(r-c).
constexpr std::array<int, 6> component{0, 1, 2, 2, 3, 3};
constexpr std::array<int, 6> direction{1, 1, 1, -1, 1, -1};

std::vector<unsigned> necklaces() {
    std::vector<unsigned> representatives;
    for (unsigned v = 1; v < full; ++v) {
        if (__builtin_popcount(v) > 11) continue;
        unsigned w = v;
        bool canonical = true;
        for (int r = 1; r < period; ++r) {
            w = (w >> 1) | ((w & 1) << (period - 1));
            if (w < v) {
                canonical = false;
                break;
            }
        }
        if (canonical) representatives.push_back(v);
    }
    assert(representatives.size() == 182361);
    return representatives;
}

bool compact(const BetaRow& a, const BetaRow& b) {
#ifdef __AVX2__
    const auto l = _mm256_add_epi16(_mm256_loadu_si256(reinterpret_cast<const __m256i*>(a.data())),
                                   _mm256_loadu_si256(reinterpret_cast<const __m256i*>(b.data())));
    const auto u = _mm256_add_epi16(_mm256_loadu_si256(reinterpret_cast<const __m256i*>(a.data() + 16)),
                                   _mm256_loadu_si256(reinterpret_cast<const __m256i*>(b.data() + 16)));
    const auto tl = _mm256_sub_epi16(l, _mm256_set1_epi16(4));
    const auto tu = _mm256_sub_epi16(u, _mm256_set1_epi16(4));
#endif
    // A set of 18 among 23 positions meets the first six.
    for (int j = 0; j < 6; ++j) for (int delta : {0, 4}) {
        const int base = a[j] + b[j] - delta;
#ifdef __AVX2__
        const auto p = _mm256_set1_epi16(base);
        const uint32_t z = _mm256_movemask_epi8(_mm256_or_si256(_mm256_cmpeq_epi16(l, p), _mm256_cmpeq_epi16(tl, p)));
        const uint32_t t = _mm256_movemask_epi8(_mm256_or_si256(_mm256_cmpeq_epi16(u, p), _mm256_cmpeq_epi16(tu, p)));
        if (__builtin_popcount(z) + __builtin_popcount(t & 16383) >= 36) return true;
#else
        int count = 0;
        for (int i = 0; i < period; ++i) {
            const int value = a[i] + b[i];
            count += value == base || value == base + 4;
        }
        if (count >= 18) return true;
#endif
    }
    return false;
}

std::vector<Profile> subset_sums(const Words& words, int offset, int length, bool base) {
    std::array<Profile, period> steps{};
    for (int r = 0; r < period; ++r) for (int k = 0; k < 6; ++k) for (int j = 0; j < period; ++j)
        steps[r][k][j] = 2 * words[component[k]][(period + direction[k] * (j - r)) % period];
    std::vector<Profile> out(1 << length);
    if (base) for (const auto& step : steps)
        for (int k = 0; k < 6; ++k) for (int j = 0; j < period; ++j)
            out[0][k][j] -= step[k][j] / 2;
    for (unsigned state = 1; state < out.size(); ++state) {
        const auto& last = out[state & (state - 1)];
        const auto& change = steps[offset + __builtin_ctz(state)];
        for (int k = 0; k < 6; ++k) for (int j = 0; j < 32; ++j)
            out[state][k][j] = last[k][j] + change[k][j];
    }
    return out;
}

void check_beta() {
    const auto words = necklaces();
    int sources;
    std::cin >> sources;
    uint64_t n0 = 0, n1 = 0, hits = 0;
    for (int i = 0; i < sources; ++i) {
        Words w;
        for (auto& row : w) for (int& x : row) std::cin >> x;
        assert(std::cin);
        const auto left = subset_sums(w, 0, 11, true);
        const auto right = subset_sums(w, 11, 12, false);
        for (unsigned q : words) {
            const auto& a = left[q & 2047];
            const auto& b = right[q >> 11];
            const bool zero = compact(a[0], b[0]);
            const bool first = compact(a[1], b[1]);
            n0 += zero;
            n1 += first;
            hits += (zero && (compact(a[4], b[4]) || compact(a[5], b[5])))
                 || (first && (compact(a[2], b[2]) || compact(a[3], b[3])));
        }
    }
    std::cout << "beta " << sources << ' ' << words.size() << ' ' << n0 << ' ' << n1 << ' ' << hits << '\n';
}

int main(int argc, char** argv) {
    assert(argc == 2);
    if (std::string_view(argv[1]) == "alpha") check_alpha();
    else {
        assert(std::string_view(argv[1]) == "beta");
        check_beta();
    }
}
