// Exhaustive six-by-five integer factors for a prescribed exterior Gram.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <vector>

namespace {

constexpr int rows = 6;
constexpr int width = 5;
using Column = std::array<int, rows>;
using Gram = std::array<std::array<int, width>, width>;

struct Triple {
    int sum;
    int norm;
    std::array<int, 3> entries;
};

bool key_less(const Triple& left, const Triple& right) {
    return left.sum != right.sum ? left.sum < right.sum : left.norm < right.norm;
}

int dot(const Column& left, const Column& right) {
    return std::inner_product(left.begin(), left.end(), right.begin(), 0);
}

int high_mask(const Column& column) {
    int mask = 0;
    for (int i = 0; i < rows; ++i) {
        mask |= ((static_cast<unsigned>(column[i]) >> 2) & 1u) << i;
    }
    return mask;
}

std::vector<Column> enumerate_column(int sum, int norm, const Column& low, int bound,
                                     const std::array<bool, 1 << rows>& high) {
    std::vector<Column> result;
    for (int mask = 0; mask < (1 << rows); ++mask) {
        if (!high[mask]) {
            continue;
        }
        std::array<std::vector<int>, rows> entries;
        for (int i = 0; i < rows; ++i) {
            const int residue = low[i] + 4 * (mask >> i & 1);
            for (int value = -bound; value <= bound; ++value) {
                const int rest = sum - value;
                if ((static_cast<unsigned>(value) & 7u) == static_cast<unsigned>(residue)
                    && 5 * value * value + rest * rest <= 5 * norm) {
                    entries[i].push_back(value);
                }
            }
        }
        std::vector<Triple> left;
        for (int a : entries[0]) {
            for (int b : entries[1]) {
                for (int c : entries[2]) {
                    const int total = a + b + c;
                    const int squared = a * a + b * b + c * c;
                    const int rest = sum - total;
                    if (3 * squared + rest * rest <= 3 * norm) {
                        left.push_back({total, squared, {a, b, c}});
                    }
                }
            }
        }
        std::sort(left.begin(), left.end(), key_less);
        for (int a : entries[3]) {
            for (int b : entries[4]) {
                for (int c : entries[5]) {
                    const int total = a + b + c;
                    const int squared = a * a + b * b + c * c;
                    const int rest = sum - total;
                    if (3 * squared + rest * rest > 3 * norm) {
                        continue;
                    }
                    const Triple target{rest, norm - squared, {}};
                    const auto matches = std::equal_range(left.begin(), left.end(), target, key_less);
                    for (auto match = matches.first; match != matches.second; ++match) {
                        result.push_back({match->entries[0], match->entries[1],
                                          match->entries[2], a, b, c});
                    }
                }
            }
        }
    }
    return result;
}

std::vector<const Column*> matching_dot(const std::vector<Column>& pool,
                                         const Column& reference, int target) {
    std::vector<const Column*> result;
    for (const auto& candidate : pool) {
        if (dot(reference, candidate) == target) {
            result.push_back(&candidate);
        }
    }
    return result;
}

}  // namespace

int main() {
    Gram gram{};
    std::array<int, width> sums{};
    std::array<Column, width> low{};
    std::array<std::array<bool, 1 << rows>, width> high{};
    int bound = 0;
    int row_sum = 0;
    std::cin >> bound >> row_sum;
    for (auto& row : gram) {
        for (int& value : row) {
            std::cin >> value;
        }
    }
    for (int& value : sums) {
        std::cin >> value;
    }
    for (auto& column : low) {
        for (int& value : column) {
            std::cin >> value;
        }
    }
    for (auto& mask_set : high) {
        int count = 0;
        std::cin >> count;
        for (int i = 0; i < count; ++i) {
            int mask = 0;
            std::cin >> mask;
            if (mask < 0 || mask >= (1 << rows)) {
                return 1;
            }
            mask_set[mask] = true;
        }
    }
    if (!std::cin || bound <= 0 || bound > 600) {
        return 1;
    }

    std::array<std::vector<Column>, width> pool;
    std::cerr << "column choices";
    for (int j = 0; j < width; ++j) {
        pool[j] = enumerate_column(sums[j], gram[j][j], low[j], bound, high[j]);
        std::cerr << ' ' << pool[j].size();
    }
    std::cerr << '\n';
    std::array<int, width> order{0, 1, 2, 3, 4};
    std::stable_sort(order.begin(), order.end(), [&](int left, int right) {
        return pool[left].size() < pool[right].size();
    });
    const auto [a, b, c, d, e] = order;

    std::array<std::uint64_t, 4> counts{};
    for (const auto& first : pool[a]) {
        const auto seconds = matching_dot(pool[b], first, gram[a][b]);
        counts[0] += seconds.size();
        if (seconds.empty()) {
            continue;
        }
        const auto thirds = matching_dot(pool[c], first, gram[a][c]);
        std::vector<const Column*> fourths;
        bool searched_fourths = false;
        for (const auto* second : seconds) {
            for (const auto* third : thirds) {
                if (dot(*second, *third) != gram[b][c]) {
                    continue;
                }
                ++counts[1];
                if (!searched_fourths) {
                    fourths = matching_dot(pool[d], first, gram[a][d]);
                    searched_fourths = true;
                }
                for (const auto* fourth : fourths) {
                    if (dot(*second, *fourth) != gram[b][d] || dot(*third, *fourth) != gram[c][d]) {
                        continue;
                    }
                    ++counts[2];
                    Column last{};
                    bool valid = true;
                    for (int i = 0; i < rows; ++i) {
                        last[i] = row_sum - first[i] - (*second)[i] - (*third)[i] - (*fourth)[i];
                        valid &= std::abs(last[i]) <= bound
                                 && (static_cast<unsigned>(last[i]) & 3u) ==
                                     static_cast<unsigned>(low[e][i]);
                    }
                    if (!valid || !high[e][high_mask(last)]
                        || std::accumulate(last.begin(), last.end(), 0) != sums[e]
                        || dot(last, last) != gram[e][e] || dot(last, first) != gram[e][a]
                        || dot(last, *second) != gram[e][b] || dot(last, *third) != gram[e][c]
                        || dot(last, *fourth) != gram[e][d]) {
                        continue;
                    }
                    ++counts[3];
                    std::array<const Column*, width> factor{};
                    factor[a] = &first;
                    factor[b] = second;
                    factor[c] = third;
                    factor[d] = fourth;
                    factor[e] = &last;
                    for (int i = 0; i < rows; ++i) {
                        for (int j = 0; j < width; ++j) {
                            std::cout << (*factor[j])[i] << ' ';
                        }
                    }
                    std::cout << '\n';
                }
            }
        }
    }
    std::cerr << "exact prefix counts";
    for (const auto count : counts) {
        std::cerr << ' ' << count;
    }
    std::cerr << '\n';
}
