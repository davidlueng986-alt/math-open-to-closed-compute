#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <string>
#include <unordered_set>
#include <vector>

#if defined(__x86_64__) && defined(__GNUC__)
#include <immintrin.h>
#define PALEY_AVX2_CHECK 1
#endif

constexpr int pairs = 16;
using Deck = std::array<int, pairs>;
using Bits = std::uint64_t;

template<class Matrix>
std::vector<Deck> signed_sums(const Matrix& matrix, int start, int count) {
    std::vector<Deck> sums(1U << count);
    for (int i = start; i < start + count; ++i)
        for (int j = 0; j < pairs; ++j) sums[0][j] -= matrix[i][j];
    for (unsigned mask = 1; mask < sums.size(); ++mask) {
        auto bit = __builtin_ctz(mask);
        sums[mask] = sums[mask & (mask - 1)];
        for (int j = 0; j < pairs; ++j) sums[mask][j] += 2 * matrix[start + bit][j];
    }
    return sums;
}

int key(const Deck& row, int i, int j, int phase) {
    int x = 256 + phase * row[i];
    int y = 256 + phase * row[j];
    assert(0 <= x && x < 512 && 0 <= y && y < 512);
    return x | (y << 9);
}

bool meets_budget(const Deck& a, const Deck& b) {
    for (int sector : {0, 8}) {
        int cost = 0;
        for (int j = sector; j < sector + 8; ++j) {
            int value = a[j] + b[j];
            if (value % 4) return false;
            if (value) cost += std::abs(value) == 4 ? 7 : 23;
            if (cost > 34) return false;
        }
    }
    return true;
}

void symmetric_precursor() {
    std::array<Deck, 28> matrix{};
    for (auto& row : matrix)
        for (int& value : row) std::cin >> value;
    auto left = signed_sums(matrix, 0, 14);
    auto right = signed_sums(matrix, 14, 14);
    std::vector<int> head(1U << 18);
    std::vector<int> next(right.size());
    std::uint64_t matched = 0;
    std::uint64_t qualifying = 0;
    for (int i = 0; i < 5; ++i) {
        for (int j = 8; j < 13; ++j) {
            std::fill(head.begin(), head.end(), -1);
            for (unsigned k = 0; k < right.size(); ++k) {
                int address = key(right[k], i, j, 1);
                next[k] = head[address];
                head[address] = k;
            }
            for (unsigned k = 1; k < left.size(); k += 2) {
                int address = key(left[k], i, j, -1);
                for (int l = head[address]; l >= 0; l = next[l]) {
                    ++matched;
                    qualifying += meets_budget(left[k], right[l]);
                }
            }
        }
    }
    std::cout << "symmetric " << matched << " " << qualifying << "\n";
}


constexpr int ternary_count = 531441;
using TernaryDeck = std::array<std::int16_t, pairs>;

std::vector<TernaryDeck> ternary_sums(const std::array<Deck, 24>& matrix, int first) {
    std::vector<TernaryDeck> sums;
    sums.reserve(ternary_count);
    auto collect = [&](auto&& self, int depth, TernaryDeck& sum) -> void {
        if (depth < 0) {
            sums.push_back(sum);
            return;
        }
        const auto& row = matrix[first + depth];
        for (int j = 0; j < pairs; ++j) sum[j] -= row[j];
        for (int sign = -1; sign <= 1; ++sign) {
            self(self, depth - 1, sum);
            for (int j = 0; j < pairs; ++j) sum[j] += row[j];
        }
        for (int j = 0; j < pairs; ++j) sum[j] -= 2 * row[j];
    };
    TernaryDeck zero{};
    collect(collect, 11, zero);
    assert(sums.size() == ternary_count);
    return sums;
}

int ternary_key(const TernaryDeck& row, int start, int phase) {
    int index = 0;
    for (int j = 0; j < 3; ++j) {
        int x = 128 + phase * row[start + j];
        assert(x >= 2 && x <= 253);
        index |= x << (8 * j);
    }
    return index;
}

int orientation(unsigned code) {
    for (int j = 0; j < 12; ++j) {
        unsigned digit = code % 3;
        if (digit != 1) return digit == 2 ? 1 : -1;
        code /= 3;
    }
    return 0;
}

bool odd_scalar(const TernaryDeck& a, const TernaryDeck& b, int first) {
    for (int start : {first, 8 - first}) {
        int cost = 0;
        for (int j = start; j < start + 8; ++j) {
            const int p = std::abs(a[j] + b[j]);
            cost += p <= 2 ? 7 * p : 23;
            if (cost > 68) return false;
        }
    }
    return true;
}

#ifdef PALEY_AVX2_CHECK
__attribute__((target("avx2")))
bool odd_vector(const TernaryDeck& a, const TernaryDeck& b, int) {
    const auto left = _mm256_loadu_si256(reinterpret_cast<const __m256i*>(a.data()));
    const auto right = _mm256_loadu_si256(reinterpret_cast<const __m256i*>(b.data()));
    const auto sum = _mm256_abs_epi16(_mm256_add_epi16(left, right));
    const auto small = _mm256_mullo_epi16(sum, _mm256_set1_epi16(7));
    const auto large = _mm256_cmpgt_epi16(sum, _mm256_set1_epi16(2));
    const auto costs = _mm256_blendv_epi8(small, _mm256_set1_epi16(23), large);
    auto combined = _mm256_madd_epi16(costs, _mm256_set1_epi16(1));
    combined = _mm256_hadd_epi32(combined, combined);
    combined = _mm256_hadd_epi32(combined, combined);
    return _mm256_extract_epi32(combined, 0) <= 68 && _mm256_extract_epi32(combined, 4) <= 68;
}
#endif

void odd_precursors(bool portable) {
    std::array<Deck, 24> matrix{};
    for (auto& row : matrix)
        for (auto& x : row) std::cin >> x;
    const auto left = ternary_sums(matrix, 0);
    const auto right = ternary_sums(matrix, 12);
    std::vector<int> head(1U << 24), next(right.size());
    std::unordered_set<std::uint64_t> lines;
    std::vector<int> phases(ternary_count);
    for (unsigned i = 0; i < phases.size(); ++i) phases[i] = orientation(i);
    std::uint64_t matched = 0;
    auto gate = odd_scalar;
#ifdef PALEY_AVX2_CHECK
    if (!portable && __builtin_cpu_supports("avx2")) gate = odd_vector;
#else
    (void)portable;
#endif
    for (unsigned i = 0; i < left.size(); i += 271) {
        unsigned j = i * 37 % right.size();
        assert(gate(left[i], right[j], 0) == odd_scalar(left[i], right[j], 0));
    }
    for (int first : {0, 3, 6, 9, 12}) {
        std::fill(head.begin(), head.end(), -1);
        for (int j = 0; j < ternary_count; ++j) {
            int address = ternary_key(right[j], first, 1);
            next[j] = head[address];
            head[address] = j;
        }
        const int first_sector = first <= 6 ? 8 : 0;
        for (unsigned i = 0; i < left.size(); ++i) {
            if (phases[i] < 0) continue;
            const bool zero = phases[i] == 0;
            int base = ternary_key(left[i], first, -1);
            for (int c = -2; c <= 2; ++c)
                for (int b = -2; b <= 2; ++b)
                    for (int a = -2; a <= 2; ++a) {
                        int address = base + a + 256 * b + 65536 * c;
                        for (int j = head[address]; j >= 0; j = next[j]) {
                            if (zero && phases[j] != 1) continue;
                            ++matched;
                            if (!gate(left[i], right[j], first_sector)) continue;
                            const std::uint64_t code = std::uint64_t(i) * ternary_count + j;
                            if (lines.insert(code).second) std::cout << "line " << i << " " << j << "\n";
                        }
                    }
        }
    }
    std::cout << "odd " << matched << " " << lines.size() << "\n";
}

bool mixed_budget(const Deck& a, const Deck& b, const Deck& p) {
    for (int start : {0, 8}) {
        int cost = 0;
        for (int j = start; j < start + 8; ++j) {
            for (int phase : {1, -1}) {
                const int q = a[j] + b[j] + 2 * phase * p[j];
                if (q % 4) return false;
                if (q) cost += std::abs(q) == 4 ? 7 : 23;
                if (cost > 68) return false;
            }
        }
    }
    return true;
}

int double_key(int a, int b) {
    a += 256;
    b += 256;
    if (a < 0 || a >= 512 || b < 0 || b >= 512) return -1;
    return a | (b << 9);
}

void mixed_precursors() {
    int cases;
    std::cin >> cases;
    std::uint64_t matched = 0, qualifying = 0;
    std::vector<int> head(1U << 18);
    for (int test = 0; test < cases; ++test) {
        int n;
        std::cin >> n;
        assert(n >= 4 && n <= 27);
        Deck p;
        for (auto& value : p) std::cin >> value;
        std::vector<Deck> matrix(n);
        for (auto& row : matrix)
            for (auto& x : row) std::cin >> x;
        const auto left = signed_sums(matrix, 0, n / 2);
        const auto right = signed_sums(matrix, n / 2, n - n / 2);
        std::vector<int> next(right.size());
        for (int i = 0; i < 5; ++i) {
            for (int j = 8; j < 13; ++j) {
                std::fill(head.begin(), head.end(), -1);
                for (unsigned k = 0; k < right.size(); ++k) {
                    int address = double_key(right[k][i], right[k][j]);
                    assert(address >= 0);
                    next[k] = head[address];
                    head[address] = k;
                }
                for (unsigned k = 0; k < left.size(); ++k) {
                    for (int first : {1, -1}) {
                        if (!p[i] && first < 0) continue;
                        for (int second : {1, -1}) {
                            if (!p[j] && second < 0) continue;
                            int address = double_key(2 * first * p[i] - left[k][i],
                                                     2 * second * p[j] - left[k][j]);
                            if (address < 0) continue;
                            for (int l = head[address]; l >= 0; l = next[l]) {
                                ++matched;
                                qualifying += mixed_budget(left[k], right[l], p);
                            }
                        }
                    }
                }
            }
        }
    }
    std::cout << "mixed " << matched << " " << qualifying << "\n";
}

constexpr Bits full = (Bits{1} << 52) - 1;
using Column = std::array<Bits, 4>;
using Columns = std::array<Column, 32>;

std::vector<Bits> changes(Bits support, int count) {
    std::vector<Bits> result;
    auto collect = [&](auto&& self, Bits left, Bits chosen, int need) -> void {
        if (!need) {
            result.push_back(chosen);
            return;
        }
        while (__builtin_popcountll(left) >= need) {
            Bits current = left & (~left + 1);
            left ^= current;
            self(self, left, chosen | current, need - 1);
        }
    };
    collect(collect, support, 0, count);
    return result;
}

int dot(Bits q, Bits w) {
    return 52 - 2 * __builtin_popcountll(q ^ w);
}

int slope(Bits q, const Column& c) {
    return dot(q, c[1]) + dot(q, c[2]);
}

bool retained_sectors(Bits q, const Columns& cols, int parameter) {
    for (int start : {0, 16}) {
        int misses = 0;
        for (int j = start; j < start + 16; ++j) {
            const auto& c = cols[j];
            int projection = dot(q, c[0]) - 2 * dot(q, c[3]) + parameter * slope(q, c);
            if (std::abs(projection) != 2 && ++misses > 2) return false;
        }
    }
    return true;
}

void family_extrema() {
    Columns columns{};
    for (auto& c : columns)
        for (auto& value : c) std::cin >> value;
    for (int magnitude = 23; magnitude <= 26; ++magnitude) {
        std::uint64_t tested = 0;
        std::array<std::uint64_t, 2> compatible{}, successful{};
        for (const auto& c : columns) {
            const Bits three = c[0] ^ c[3];
            const Bits one = full ^ three;
            const Bits origin = full ^ c[3];
            assert(__builtin_popcountll(three) == 26);
            for (int a : {4 * magnitude - 2, 4 * magnitude + 2}) {
                if (a > 104) continue;
                int distance = (104 - a) / 2;
                for (int k = 0; 3 * k <= distance; ++k) {
                    auto small = changes(one, distance - 3 * k);
                    auto large = changes(three, k);
                    for (Bits mask_one : small) {
                        for (Bits mask_three : large) {
                            Bits raw = origin ^ mask_one ^ mask_three;
                            ++tested;
                            int b = slope(raw, c);
                            if (std::abs(b) != 4) continue;
                            int side = b > 0;
                            ++compatible[side];
                            int parameter = side ? -magnitude : magnitude;
                            successful[side] += retained_sectors(raw, columns, parameter);
                        }
                    }
                }
            }
        }
        std::cout << "family " << magnitude << " " << tested << " "
                  << compatible[0] << " " << compatible[1] << " "
                  << successful[0] << " " << successful[1] << "\n";
    }
}

int main(int argc, char** argv) {
    assert(argc == 2);
    const std::string mode = argv[1];
    if (mode == "symmetric") symmetric_precursor();
    else if (mode == "odd" || mode == "odd-portable") odd_precursors(mode == "odd-portable");
    else if (mode == "mixed") mixed_precursors();
    else {
        assert(mode == "family");
        family_extrema();
    }
    assert(std::cin);
}
