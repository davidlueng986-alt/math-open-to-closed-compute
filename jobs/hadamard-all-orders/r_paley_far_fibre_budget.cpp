#include <algorithm>
#include <array>
#include <cassert>
#include <iostream>
#include <numeric>

constexpr int row_fibres = 92;
constexpr int column_fibres = 49;
constexpr int fibre_size = 13;
constexpr int omissions = 37;

using Profile = std::array<int, column_fibres>;

struct Stats {
    long long configurations = 0;
    long long mean_feasible = 0;
    int max_oppositions = 0;
    int max_flips = 0;
};

template <typename Mean>
void check(Stats& stats, int d, Mean fibre_mean) {
    ++stats.configurations;
    int mandatory = 0;
    int oppositions = 0;
    for (int j = 0; j < column_fibres; ++j) {
        int mean = fibre_mean(j);
        int minimum = 0;
        if (mean < 0) {
            minimum = (-mean + d - 1) / d;
        } else if (mean > 2 * fibre_size) {
            assert(d > 2);
            minimum = (mean - 2 * fibre_size + d - 3) / (d - 2);
        }
        mandatory += minimum;
        if (minimum > fibre_size || mandatory > omissions) {
            return;
        }
        oppositions += std::min(fibre_size - minimum, (mean + d * minimum) / 2);
    }
    ++stats.mean_feasible;
    stats.max_flips = std::max(stats.max_flips, d);
    oppositions += (omissions - mandatory) * (d / 2);
    stats.max_oppositions = std::max(stats.max_oppositions, oppositions);
    assert(oppositions < 599 - d / 2);
}

struct CostProfile {
    Profile coefficient;
    int cost;
};

void radius14(Stats& stats, const std::array<CostProfile, row_fibres>& sorted,
              Profile& accumulated, int start, int remaining, int budget) {
    if (remaining == 0) {
        check(stats, 14, [&](int j) { return accumulated[j]; });
        return;
    }
    for (int i = start; i < row_fibres; ++i) {
        const auto& [coefficient, cost] = sorted[i];
        if (remaining * cost > budget) {
            break;
        }
        int limit = std::min(remaining, fibre_size);
        if (cost > 0) {
            limit = std::min(limit, budget / cost);
        }
        for (int count = 1; count <= limit; ++count) {
            for (int j = 0; j < column_fibres; ++j) {
                accumulated[j] += coefficient[j];
            }
            radius14(stats, sorted, accumulated, i + 1, remaining - count, budget - count * cost);
        }
        for (int j = 0; j < column_fibres; ++j) {
            accumulated[j] -= limit * coefficient[j];
        }
    }
}

int main() {
    std::array<Profile, row_fibres> profiles{};
    for (auto& profile : profiles) {
        for (int& value : profile) {
            if (!(std::cin >> value)) {
                return 1;
            }
            int magnitude = std::max(value, -value);
            assert(magnitude == 1 || magnitude == 5);
        }
    }

    Stats two, three;
    for (int a = 0; a < row_fibres; ++a) {
        for (int b = a + 1; b < row_fibres; ++b) {
            for (int u = 1; u <= fibre_size; ++u) {
                for (int v = 1 + ((u + 1) & 1); v <= fibre_size; v += 2) {
                    check(two, u + v, [&](int j) { return u * profiles[a][j] + v * profiles[b][j]; });
                }
            }
            for (int c = b + 1; c < row_fibres; ++c) {
                for (int u = 1; u <= fibre_size; ++u) {
                    for (int v = 1; v <= fibre_size; ++v) {
                        for (int w = 1 + ((u + v + 1) & 1); w <= fibre_size; w += 2) {
                            check(three, u + v + w, [&](int j) {
                                return u * profiles[a][j] + v * profiles[b][j] + w * profiles[c][j];
                            });
                        }
                    }
                }
            }
        }
    }
    assert(two.configurations == 355810 && two.mean_feasible == 1850);
    assert(two.max_oppositions == 300 && two.max_flips == 10);
    assert(three.configurations == 137886840 && three.mean_feasible == 138485);
    assert(three.max_oppositions == 378 && three.max_flips == 16);
    std::cout << "Two fibres: 355810 count choices, at most 300 opposed projections.\n";
    std::cout << "Three fibres: 137886840 count choices, at most 378 opposed projections.\n";

    std::array<CostProfile, row_fibres> ordered{};
    for (int i = 0; i < row_fibres; ++i) {
        int sum = std::accumulate(profiles[i].begin(), profiles[i].end(), 0);
        ordered[i] = {profiles[i], 53 - sum};
    }
    std::sort(ordered.begin(), ordered.end(), [](const CostProfile& a, const CostProfile& b) {
        return a.cost < b.cost;
    });
    assert(ordered.front().cost == 0);
    Stats fourteen;
    Profile accumulated{};
    radius14(fourteen, ordered, accumulated, 0, 14, 76);
    assert(fourteen.configurations == 24749232 && fourteen.mean_feasible == 16908524);
    assert(fourteen.max_oppositions == 589);
    std::cout << "Fourteen flips across arbitrary fibres: 24749232 count choices, at most 589 opposed projections.\n";
}
