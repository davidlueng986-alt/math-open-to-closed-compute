// Exclude the bounded double-product neighborhoods by necessary integer tests.

#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <functional>
#include <iostream>
#include <numeric>
#include <unordered_set>
#include <utility>
#include <vector>

namespace {

constexpr int WORD_COUNT = 19;
constexpr int HALF_DOT_LIMIT = 600;
constexpr int HALF_DOT_VALUES = 2 * HALF_DOT_LIMIT + 1;
constexpr std::array<int, 11> GROUPS{566, 18, 16, 14, 12, 10, 8, 0, 6, 4, 2};
constexpr std::array<int, 8> SUM_GROUPS{10, 9, 8, 6, 5, 4, 3, 2};
using Word = std::array<std::uint64_t, WORD_COUNT>;

int half_dot(int size, const Word& left, const Word& right) {
    int differences = 0;
    for (int i = 0; i < WORD_COUNT; ++i) {
        differences += __builtin_popcountll(left[i] ^ right[i]);
    }
    return size / 2 - differences;
}

Word multiply(const Word& first, const Word& second, const Word& third) {
    Word result{};
    for (int i = 0; i < WORD_COUNT; ++i) {
        result[i] = first[i] ^ second[i] ^ third[i];
    }
    return result;
}

struct Source {
    int size;
    Word reference;
    std::vector<Word> columns;
};

struct Input {
    Source upper, lower;
    std::array<int, 4> omitted;
    std::vector<std::array<int, 5>> targets;

    explicit Input(const char* path) {
        std::ifstream stream(path, std::ios::binary);
        const auto read = [&](auto& value) {
            stream.read(reinterpret_cast<char*>(&value), sizeof value);
            assert(stream);
        };
        int target_count;
        read(upper.size);
        read(lower.size);
        read(omitted);
        read(target_count);
        assert(upper.size == 1196 && lower.size == 1200 && target_count == 46);
        targets.resize(target_count);
        for (auto& target : targets) read(target);
        read(upper.reference);
        read(lower.reference);
        upper.columns.resize(upper.size);
        lower.columns.resize(lower.size);
        for (auto& column : upper.columns) read(column);
        for (auto& column : lower.columns) read(column);
    }
};

struct OrientedColumn {
    Word word;
    int sign;
};

using Group = std::vector<OrientedColumn>;
using Groups = std::array<Group, GROUPS.size()>;

Groups make_groups(const Source& source, const std::array<int, 4>& omitted) {
    Groups result;
    for (int j = 0; j < source.size; ++j) {
        if (std::find(omitted.begin(), omitted.end(), j) != omitted.end()) continue;
        const int first = half_dot(source.size, source.reference, source.columns[j]);
        const auto group = std::find(GROUPS.begin(), GROUPS.end(), std::abs(first));
        assert(group != GROUPS.end());
        result[group - GROUPS.begin()].push_back({source.columns[j], first >= 0 ? 1 : -1});
    }
    return result;
}

std::vector<int> sorted_signature(int size, const Word& word, const Group& group,
                                  bool oriented, int sign = 1) {
    std::vector<int> result;
    result.reserve(group.size());
    for (const auto& [column, orientation] : group) {
        const int value = half_dot(size, word, column);
        result.push_back(oriented ? sign * orientation * value : std::abs(value));
    }
    std::sort(result.begin(), result.end());
    return result;
}

struct GroupWeight {
    std::array<Word, 10> bit_planes{};
    int total = 0;
    int flip_bound = 0;

    GroupWeight() = default;

    GroupWeight(int size, const Group& group, int radius) {
        std::vector<int> magnitudes;
        for (int row = 0; row < size; ++row) {
            int weight = 0;
            for (const auto& [column, sign] : group) {
                weight += sign * (column[row / 64] >> (row % 64) & 1 ? 1 : -1);
            }
            magnitudes.push_back(std::abs(weight));
            total += weight;
            // Encode each signed row weight with ten two's-complement bit planes.
            assert(weight >= -512 && weight < 512);
            const unsigned bits = static_cast<unsigned>(weight) & 1023;
            for (int bit = 0; bit < 10; ++bit) {
                if (bits >> bit & 1) bit_planes[bit][row / 64] |= std::uint64_t{1} << (row % 64);
            }
        }
        std::sort(magnitudes.begin(), magnitudes.end(), std::greater<>());
        flip_bound = std::accumulate(magnitudes.begin(), magnitudes.begin() + radius, 0);
    }

    int sum(const Word& word) const {
        int positive_sum = 0;
        for (int bit = 0; bit < 10; ++bit) {
            int count = 0;
            for (int j = 0; j < WORD_COUNT; ++j) {
                count += __builtin_popcountll(bit_planes[bit][j] & word[j]);
            }
            positive_sum += count * (bit == 9 ? -512 : 1 << bit);
        }
        assert(total % 2 == 0);
        return positive_sum - total / 2;
    }
};

std::uint64_t projection_key(const std::array<int, 4>& coordinates) {
    std::uint64_t key = 0;
    for (int value : coordinates) {
        assert(std::abs(value) <= HALF_DOT_LIMIT);
        key = HALF_DOT_VALUES * key + value + HALF_DOT_LIMIT;
    }
    return key;
}

std::unordered_set<std::uint64_t> possible_projections(const Input& input, int radius) {
    std::unordered_set<std::uint64_t> result;
    for (const auto& target : input.targets) {
        const bool odd = std::abs(target[4]) == 2;
        if (odd != (radius % 2 == 1) || std::abs(target[4]) / 2 > radius) continue;
        for (int a = -radius; a <= radius; a += 2) {
            for (int b = -radius; b <= radius; b += 2) {
                for (int c = -radius; c <= radius; c += 2) {
                    for (int d = -radius; d <= radius; d += 2) {
                        result.insert(projection_key({target[0] - a, target[1] - b,
                                                      target[2] - c, target[3] - d}));
                    }
                }
            }
        }
    }
    return result;
}

struct Option {
    std::array<int, GROUPS.size()> sums{};
    std::array<std::vector<int>, GROUPS.size()> signatures;
};

using Weights = std::array<GroupWeight, GROUPS.size()>;

std::vector<Option> bottom_options(const Input& input, const Groups& groups,
                                   const Weights& weights, int radius) {
    const auto projections = possible_projections(input, radius);
    const auto& lower = input.lower;
    std::vector<Option> result;
    for (int i = 0; i < lower.size; ++i) {
        for (int j = i + 1; j < lower.size; ++j) {
            const Word word = multiply(lower.reference, lower.columns[i], lower.columns[j]);
            std::array<int, 4> omitted{};
            for (int k = 0; k < 4; ++k) {
                omitted[k] = half_dot(lower.size, word, lower.columns[input.omitted[k]]);
            }
            if (!projections.count(projection_key(omitted))) continue;
            for (int sign : {1, -1}) {
                Option option;
                for (std::size_t k = 0; k < groups.size(); ++k) {
                    if (std::find(SUM_GROUPS.begin(), SUM_GROUPS.end(), k) != SUM_GROUPS.end()) {
                        option.sums[k] = sign * weights[k].sum(word);
                    }
                    option.signatures[k] = sorted_signature(lower.size, word, groups[k], GROUPS[k] != 0, sign);
                }
                result.push_back(std::move(option));
            }
        }
    }
    return result;
}

void verify_radius(const Input& input, const Groups& top, const Groups& bottom, int radius,
                   int expected_pivots) {
    const int tolerance = 2 * radius;
    Weights top_weights, bottom_weights;
    for (int k : SUM_GROUPS) {
        top_weights[k] = GroupWeight(input.upper.size, top[k], radius);
        bottom_weights[k] = GroupWeight(input.lower.size, bottom[k], radius);
    }
    const auto options = bottom_options(input, bottom, bottom_weights, radius);
    assert(options.size() == static_cast<std::size_t>(2 * expected_pivots));

    // First filter the singleton and the two-member group using option bitsets.
    const int chunks = (options.size() + 63) / 64;
    std::vector<std::uint64_t> masks(3 * HALF_DOT_VALUES * chunks);
    const auto mask = [&](int axis, int value) {
        assert(std::abs(value) <= HALF_DOT_LIMIT);
        return masks.data() + (axis * HALF_DOT_VALUES + value + HALF_DOT_LIMIT) * chunks;
    };
    for (std::size_t j = 0; j < options.size(); ++j) {
        const auto& signature = options[j].signatures;
        const std::array<int, 3> values{signature[0][0], signature[1][0], signature[1][1]};
        for (int axis = 0; axis < 3; ++axis) {
            for (int shift = -tolerance; shift <= tolerance; shift += 2) {
                const int value = values[axis] + shift;
                if (std::abs(value) <= HALF_DOT_LIMIT) mask(axis, value)[j / 64] |= std::uint64_t{1} << (j % 64);
            }
        }
    }

    const auto& upper = input.upper;
    std::vector<int> candidates;
    for (int i = 0; i < upper.size; ++i) {
        for (int j = i + 1; j < upper.size; ++j) {
            const Word word = multiply(upper.reference, upper.columns[i], upper.columns[j]);
            const auto first = sorted_signature(upper.size, word, top[0], true);
            const auto second = sorted_signature(upper.size, word, top[1], true);
            const auto* first_mask = mask(0, first[0]);
            const auto* second_mask = mask(1, second[0]);
            const auto* third_mask = mask(2, second[1]);
            candidates.clear();
            for (int k = 0; k < chunks; ++k) {
                auto common = first_mask[k] & second_mask[k] & third_mask[k];
                while (common != 0) {
                    candidates.push_back(64 * k + __builtin_ctzll(common));
                    common &= common - 1;
                }
            }

            // The largest row weights bound the total change within each oriented group.
            for (int group : SUM_GROUPS) {
                if (candidates.empty()) break;
                const int sum = top_weights[group].sum(word);
                const int bound = top_weights[group].flip_bound + bottom_weights[group].flip_bound;
                candidates.erase(std::remove_if(candidates.begin(), candidates.end(), [&](int option) {
                    return std::abs(sum - options[option].sums[group]) > bound;
                }), candidates.end());
            }
            for (std::size_t group = 2; group < GROUPS.size() && !candidates.empty(); ++group) {
                const auto signature = sorted_signature(upper.size, word, top[group], GROUPS[group] != 0);
                candidates.erase(std::remove_if(candidates.begin(), candidates.end(), [&](int option) {
                    const auto& other = options[option].signatures[group];
                    for (std::size_t k = 0; k < signature.size(); ++k) {
                        if (std::abs(signature[k] - other[k]) > tolerance) return true;
                    }
                    return false;
                }), candidates.end());
            }
            assert(candidates.empty());
        }
    }
    std::cout << "1198 radius " << radius << ": " << expected_pivots
              << " lower pivots passed projections, no joint pairing survived\n";
}

}  // namespace

int main(int argc, char** argv) {
    assert(argc == 2);
    const Input input(argv[1]);
    const auto upper = make_groups(input.upper, {-1, -1, -1, -1});
    const auto lower = make_groups(input.lower, input.omitted);
    for (std::size_t group = 0; group < GROUPS.size(); ++group) {
        assert(upper[group].size() == lower[group].size());
    }
    assert(upper[0].size() == 1 && upper[1].size() == 2);
    verify_radius(input, upper, lower, 2, 98);
    verify_radius(input, upper, lower, 3, 398);
    verify_radius(input, upper, lower, 4, 738);
}
