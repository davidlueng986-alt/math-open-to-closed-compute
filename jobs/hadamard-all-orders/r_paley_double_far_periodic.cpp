#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <string>
#include <unordered_set>
#include <utility>
#include <vector>

constexpr int width = 16;
constexpr int ternary_size = 531441;
using Deck = std::array<int, width>;
using SmallDeck = std::array<std::int16_t, width>;
using Key = std::uint64_t;

std::vector<Deck> signed_sums(const std::vector<Deck>& matrix, int first, int count) {
    std::vector<Deck> sums(1U << count);
    for (int row = first; row < first + count; ++row)
        for (int j = 0; j < width; ++j) sums[0][j] -= matrix[row][j];
    for (unsigned mask = 1; mask < sums.size(); ++mask) {
        const auto bit = __builtin_ctz(mask);
        sums[mask] = sums[mask & (mask - 1)];
        for (int j = 0; j < width; ++j) sums[mask][j] += 2 * matrix[first + bit][j];
    }
    return sums;
}

Key binary_key(const Deck& row, const std::vector<int>& columns, int sign) {
    Key key = 0;
    int shift = 0;
    for (int j : columns) {
        int value = sign * row[j] + 256;
        assert(value >= 2 && value < 510);
        key |= Key(value) << shift;
        shift += 9;
    }
    return key;
}

std::vector<Key> targets(const std::vector<int>& columns, const Deck& odd) {
    std::vector<Key> result(1);
    for (std::size_t j = 0; j < columns.size(); ++j) {
        if (odd[columns[j]]) continue;
        const auto size = result.size();
        for (std::size_t k = 0; k < size; ++k) {
            const Key offset = 2ULL << (9 * j);
            const Key old = result[k];
            result[k] = old - offset;
            result.push_back(old + offset);
        }
    }
    return result;
}

std::vector<std::pair<Key, unsigned>> index_right(const std::vector<Deck>& right,
                                                  const std::vector<int>& columns) {
    std::vector<std::pair<Key, unsigned>> index;
    index.reserve(right.size());
    for (unsigned i = 0; i < right.size(); ++i)
        index.emplace_back(binary_key(right[i], columns, 1), i);
    std::sort(index.begin(), index.end());
    return index;
}

void symmetric() {
    std::vector<Deck> matrix(28);
    for (auto& row : matrix)
        for (int& value : row) std::cin >> value;
    const auto left = signed_sums(matrix, 0, 14);
    const auto right = signed_sums(matrix, 14, 14);
    std::uint64_t matched = 0;
    for (int first : {0, 5, 10}) {
        const std::vector<int> columns{first, first + 1, first + 2, first + 3, first + 4};
        const auto index = index_right(right, columns);
        const auto differences = targets(columns, {});
        for (unsigned i = 1; i < left.size(); i += 2) {
            const Key base = binary_key(left[i], columns, -1);
            for (auto offset : differences) {
                const Key key = base + offset;
                auto at = std::lower_bound(index.begin(), index.end(), std::pair{key, 0U});
                for (; at != index.end() && at->first == key; ++at) {
                    ++matched;
                    const auto& other = right[at->second];
                    int same = 0, opposite = 0;
                    for (int j = 0; j < 8; ++j) {
                        same += std::abs(left[i][j] + other[j]) == 2;
                        opposite += std::abs(left[i][8 + j] + other[8 + j]) == 2;
                    }
                    if (same >= 7 && opposite >= 7)
                        std::cout << "line " << i << " " << at->second << "\n";
                }
            }
        }
    }
    std::cout << "symmetric " << matched << "\n";
}

std::vector<SmallDeck> ternary_sums(const std::array<Deck, 24>& matrix, int first) {
    std::vector<SmallDeck> sums;
    sums.reserve(ternary_size);
    auto walk = [&](auto&& self, int depth, SmallDeck& deck) -> void {
        if (depth < 0) {
            sums.push_back(deck);
            return;
        }
        const auto& row = matrix[first + depth];
        for (int j = 0; j < width; ++j) deck[j] -= row[j];
        for (int value = -1; value <= 1; ++value) {
            self(self, depth - 1, deck);
            for (int j = 0; j < width; ++j) deck[j] += row[j];
        }
        for (int j = 0; j < width; ++j) deck[j] -= 2 * row[j];
    };
    SmallDeck zero{};
    walk(walk, 11, zero);
    assert(sums.size() == ternary_size);
    return sums;
}

int ternary_key(const SmallDeck& row, int first, int sign) {
    int key = 0;
    for (int j = 0; j < 3; ++j) {
        const int value = 128 + sign * row[first + j];
        assert(value >= 2 && value <= 253);
        key |= value << (8 * j);
    }
    return key;
}

bool oriented_nonzero(unsigned left, unsigned right) {
    for (auto mask : {left, right}) {
        for (int order = 0; order < 12; ++order) {
            const unsigned digit = mask % 3;
            if (digit != 1) return digit == 2;
            mask /= 3;
        }
    }
    return false;
}

bool odd_counts(const SmallDeck& left, const SmallDeck& right) {
    for (int sector : {0, 8}) {
        int errors = 0;
        for (int j = sector; j < sector + 8; ++j)
            if (std::abs(left[j] + right[j]) > 1 && ++errors > 2) return false;
    }
    return true;
}

void odd() {
    std::array<Deck, 24> matrix;
    for (auto& row : matrix)
        for (auto& x : row) std::cin >> x;
    const auto left = ternary_sums(matrix, 0);
    const auto right = ternary_sums(matrix, 12);
    std::vector<int> head(1 << 24), next(ternary_size);
    std::unordered_set<std::uint64_t> lines;
    std::uint64_t matched = 0;
    for (int first : {0, 3, 6, 9, 12}) {
        std::fill(head.begin(), head.end(), -1);
        for (int j = 0; j < ternary_size; ++j) {
            int key = ternary_key(right[j], first, 1);
            next[j] = head[key];
            head[key] = j;
        }
        for (unsigned i = 0; i < ternary_size; ++i) {
            int base = ternary_key(left[i], first, -1);
            for (int c : {-1, 0, 1}) for (int b : {-1, 0, 1}) for (int a : {-1, 0, 1}) {
                int key = base + a + 256 * b + 65536 * c;
                for (int j = head[key]; j >= 0; j = next[j]) {
                    ++matched;
                    if (!odd_counts(left[i], right[j]) || !oriented_nonzero(i, j)) continue;
                    const std::uint64_t code = std::uint64_t(i) * ternary_size + j;
                    if (lines.insert(code).second) std::cout << "line " << i << " " << j << "\n";
                }
            }
        }
    }
    std::cout << "odd " << matched << " " << lines.size() << "\n";
}

void complete() {
    int cases;
    std::cin >> cases;
    std::uint64_t matched = 0, qualifying = 0;
    for (int test = 0; test < cases; ++test) {
        int n;
        std::cin >> n;
        assert(n >= 4 && n <= 27);
        Deck odd{};
        for (auto& x : odd) std::cin >> x;
        std::vector<Deck> matrix(n);
        for (auto& row : matrix)
            for (auto& x : row) std::cin >> x;
        auto left = signed_sums(matrix, 0, n / 2);
        auto right = signed_sums(matrix, n / 2, n - n / 2);
        std::vector<int> good;
        for (int j = 0; j < width; ++j)
            if (std::abs(odd[j]) <= 1) good.push_back(j);
        const int count = good.size();
        assert(count >= 12);
        const int groups = count - 11;
        const int key_width = std::min(6, count / groups);
        assert(key_width >= 1 && groups * key_width <= count && count - groups < 12);
        for (int group = 0; group < groups; ++group) {
            const auto begin = good.begin() + group * key_width;
            const std::vector<int> columns(begin, begin + key_width);
            const auto index = index_right(right, columns);
            const auto differences = targets(columns, odd);
            for (unsigned i = 0; i < left.size(); ++i) {
                const auto base = binary_key(left[i], columns, -1);
                for (Key diff : differences) {
                    auto key = base + diff;
                    auto at = std::lower_bound(index.begin(), index.end(), std::pair{key, 0U});
                    for (; at != index.end() && at->first == key; ++at) {
                        ++matched;
                        const auto& other = right[at->second];
                        int sectors[2] = {};
                        for (int j = 0; j < width; ++j) {
                            const int x = left[i][j] + other[j];
                            sectors[j / 8] += std::abs(x + 2 * odd[j]) == 2;
                            sectors[j / 8] += std::abs(x - 2 * odd[j]) == 2;
                        }
                        qualifying += sectors[0] >= 14 && sectors[1] >= 14;
                    }
                }
            }
        }
    }
    std::cout << "complete " << matched << " " << qualifying << "\n";
}

int main(int argc, char** argv) {
    assert(argc == 2);
    const std::string mode = argv[1];
    if (mode == "symmetric") symmetric();
    else if (mode == "odd") odd();
    else {
        assert(mode == "complete");
        complete();
    }
    assert(std::cin);
}
