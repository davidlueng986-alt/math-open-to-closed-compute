#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <functional>
#include <iostream>
#include <numeric>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

constexpr int source_order = 1196;
constexpr int width = 600;
constexpr int anchors = 15;
constexpr int margins = anchors - 1;
constexpr int max_radius = 15;
constexpr int limit = 16300;
constexpr int packed_width = (width + 63) / 64;

using Margin = std::array<int16_t, margins>;
using Packed = std::array<uint64_t, packed_width>;
using Counts = std::array<Packed, 4>;

struct Frame {
    std::array<std::array<int8_t, source_order>, source_order> sign;
    std::array<int, width> selected;
    std::array<int, anchors> row, reserve;
    std::array<std::array<int, source_order>, anchors> gram{};

    bool read() {
        for (auto& r : row) {
            if (!(std::cin >> r) || r < 0 || r >= source_order) return false;
        }
        for (auto& g : reserve) {
            if (!(std::cin >> g) || g < 0 || g >= source_order) return false;
        }
        for (auto& j : selected) {
            if (!(std::cin >> j) || j < 0 || j >= source_order) return false;
        }
        for (auto& row_sign : sign) {
            std::string packed;
            if (!(std::cin >> packed) || packed.size() != source_order) return false;
            for (int j = 0; j < source_order; ++j) {
                if (packed[j] != '0' && packed[j] != '1') return false;
                row_sign[j] = packed[j] == '1' ? 1 : -1;
            }
        }
        return true;
    }

    void compute_gram() {
        for (int k = 0; k < anchors; ++k) {
            for (int r = 0; r < source_order; ++r) {
                for (int j : selected) {
                    gram[k][r] += sign[row[k]][j] * sign[r][j];
                }
            }
        }
        for (int i = 0; i < anchors; ++i) {
            assert(gram[i][row[i]] == width);
            assert(std::find(selected.begin(), selected.end(), reserve[i]) == selected.end());
            for (int j = i + 1; j < anchors; ++j) {
                assert(row[i] != row[j] && reserve[i] != reserve[j]);
                assert(gram[i][row[j]] == sign[row[i]][reserve[i]] * sign[row[j]][reserve[i]]
                    + sign[row[i]][reserve[j]] * sign[row[j]][reserve[j]]);
            }
        }
    }

    int score(int k, int r) const {
        return -sign[row[k]][reserve[k]] * sign[r][reserve[k]] * gram[k][r];
    }
};

struct Option {
    int row, cost;
    Margin margin;
};

struct Bounds {
    Margin lower, upper;
};

class Search {
    const Frame& frame;
    const int anchor, radius;
    int cost_width;
    Margin target{};
    std::vector<Option> options;
    std::vector<int> prefix;
    std::vector<Bounds> intervals;
    std::unordered_map<uint64_t, std::vector<int>> single_options;
    std::array<Packed, source_order> positive{};
    std::array<Counts, max_radius + 1> counts{};
    std::array<int, max_radius> chosen{};

    Bounds& interval(int start, int remaining, int cost) {
        return intervals[(start * (radius + 1) + remaining) * cost_width + cost];
    }

    static uint64_t key(int cost, const Margin& values) {
        uint64_t index = static_cast<uint64_t>(cost);
        for (int value : values) {
            index = (index ^ static_cast<uint16_t>(value)) * 1099511628211ULL;
        }
        return index;
    }

    static uint64_t greater(const Counts& state, int word, int threshold) {
        uint64_t equal = ~uint64_t(0), above = 0;
        for (int b = 3; b >= 0; --b) {
            const uint64_t here = state[b][word];
            if (threshold >> b & 1) {
                equal &= here;
            } else {
                above |= equal & here;
                equal &= ~here;
            }
        }
        return above;
    }

    bool prefix_signs(int depth) {
        if (depth == 0) return true;
        const int top = (radius + 1) / 2, bottom = depth - top;
        const auto& before = counts[depth - 1];
        auto& after = counts[depth];
        for (int j = 0; j < packed_width; ++j) {
            uint64_t carry = positive[chosen[depth - 1]][j];
            for (int bit = 0; bit < 4; ++bit) {
                after[bit][j] = before[bit][j] ^ carry;
                carry &= before[bit][j];
            }
            if (bottom > 0) {
                const uint64_t valid_bits = j == packed_width - 1
                    ? (uint64_t(1) << (width - 64 * j)) - 1 : ~uint64_t(0);
                if ((greater(after, j, top) | ~greater(after, j, bottom - 1)) & valid_bits) {
                    return false;
                }
            }
        }
        return true;
    }

    bool all_signs() const {
        const int pivot = frame.reserve[anchor];
        for (int j : frame.selected) {
            int sum = 0;
            for (int i = 0; i < radius; ++i) {
                const int r = chosen[i];
                sum += frame.sign[r][pivot] * frame.sign[r][j];
            }
            if (std::abs(sum) != 1) return false;
        }
        return true;
    }

    bool explore(int start, int remaining, int cost, const Margin& demand) {
        ++visited;
        const int n = options.size();
        if (start + remaining > n || cost < prefix[start + remaining] - prefix[start]
            || cost > prefix[n] - prefix[n - remaining]) {
            return false;
        }
        const auto& range = interval(start, remaining, cost);
        for (int h = 0; h < margins; ++h) {
            if (demand[h] < range.lower[h] || demand[h] > range.upper[h]) return false;
        }
        if (!prefix_signs(radius - remaining)) return false;
        if (remaining == 1) {
            const auto hit = single_options.find(key(cost, demand));
            if (hit == single_options.end()) return false;
            for (int i : hit->second) {
                const auto& option = options[i];
                if (i >= start && option.cost == cost && option.margin == demand) {
                    chosen[radius - 1] = option.row;
                    if (all_signs()) return true;
                }
            }
            return false;
        }
        for (int i = start; i + remaining <= n; ++i) {
            if (prefix[i + remaining] - prefix[i] > cost) break;
            const auto& option = options[i];
            Margin next;
            for (int h = 0; h < margins; ++h) {
                next[h] = demand[h] - option.margin[h];
            }
            chosen[radius - remaining] = option.row;
            if (explore(i + 1, remaining - 1, cost - option.cost, next)) return true;
        }
        return false;
    }

public:
    long long visited = 0;
    Search(const Frame& source, int i, int d) : frame(source), anchor(i), radius(d) {}

    bool find_word() {
        const int score_target = 597 - radius;
        const int g = frame.reserve[anchor];
        std::vector<std::pair<int, int>> scores;
        for (int r = 0; r < source_order; ++r) {
            if (r != frame.row[anchor]) scores.push_back({frame.score(anchor, r), r});
        }
        std::sort(scores.begin(), scores.end(), std::greater<>());
        int top = 0;
        for (int i = 0; i < radius - 1; ++i) top += scores[i].first;
        if (top + scores[radius - 1].first < score_target) return false;

        const int maximum = scores.front().first;
        const int cost = radius * maximum - score_target;
        cost_width = cost + 1;
        for (auto [score, r] : scores) {
            if (score + top < score_target) break;
            Option option{r, maximum - score, {}};
            int h = 0;
            for (int k = 0; k < anchors; ++k) {
                if (k == anchor) continue;
                const int s = frame.row[k], pivot = frame.reserve[k];
                int coefficient = frame.sign[r][g]
                    * (frame.sign[s][pivot] * frame.gram[k][r] - frame.sign[r][pivot]);
                if (r == s) coefficient += 2 * frame.sign[r][g] * frame.sign[r][pivot];
                option.margin[h] = coefficient;
                target[h++] = frame.sign[s][g] * frame.sign[s][pivot];
            }
            options.push_back(option);
            for (int j = 0; j < width; ++j) {
                if (frame.sign[r][g] == frame.sign[r][frame.selected[j]]) {
                    positive[r][j / 64] |= uint64_t(1) << (j % 64);
                }
            }
        }
        const int n = options.size();
        prefix.resize(n + 1);
        for (int i = 0; i < n; ++i) prefix[i + 1] = prefix[i] + options[i].cost;
        Bounds absent;
        absent.lower.fill(limit);
        absent.upper.fill(-limit);
        intervals.assign((n + 1) * (radius + 1) * cost_width, absent);
        for (int i = n; i >= 0; --i) {
            interval(i, 0, 0) = {};
            if (i == n) continue;
            const auto& option = options[i];
            for (int d = 1; d <= std::min(radius, n - i); ++d) {
                for (int c = 0; c <= cost; ++c) {
                    auto& current = interval(i, d, c);
                    current = interval(i + 1, d, c);
                    if (c < option.cost) continue;
                    const auto& tail = interval(i + 1, d - 1, c - option.cost);
                    if (tail.lower[0] == limit) continue;
                    for (int h = 0; h < margins; ++h) {
                        current.lower[h] = std::min<int>(current.lower[h], option.margin[h] + tail.lower[h]);
                        current.upper[h] = std::max<int>(current.upper[h], option.margin[h] + tail.upper[h]);
                    }
                }
            }
            single_options[key(option.cost, option.margin)].push_back(i);
        }
        return explore(0, radius, cost, target);
    }

    void print_word() const {
        std::cout << "Candidate on reserve " << frame.reserve[anchor] << " with flips";
        for (int i = 0; i < radius; ++i) std::cout << ' ' << chosen[i];
        std::cout << '\n';
    }
};

int main() {
    Frame frame;
    if (!frame.read()) return 1;
    frame.compute_gram();
    int maximum = 0;
    for (int i = 0; i < anchors; ++i) {
        std::vector<int> scores;
        for (int r = 0; r < source_order; ++r) {
            if (r != frame.row[i]) scores.push_back(frame.score(i, r));
        }
        std::partial_sort(scores.begin(), scores.begin() + 26, scores.end(), std::greater<int>());
        assert(scores[25] > 0);
        maximum = std::max(maximum, std::accumulate(scores.begin(), scores.begin() + 26, 0));
    }
    assert(maximum == 1150 && maximum < 1198 - 26);
    for (int radius : {13, 15}) {
        long long total = 0;
        for (int i = 0; i < anchors; ++i) {
            Search branch(frame, i, radius);
            if (branch.find_word()) {
                branch.print_word();
                return 2;
            }
            total += branch.visited;
        }
        std::cout << "All 15 previously used reserves: radius " << radius
                  << " excluded, visited " << total << " branches.\n";
    }
}
