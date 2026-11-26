#include <algorithm>
#include <array>
#include <cassert>
#include <iostream>

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

void check(Stats& stats, const Profile& a, const Profile& b, const Profile& c,
           int u, int v, int w) {
    ++stats.configurations;
    int d = u + v + w;
    int mandatory = 0;
    int oppositions = 0;
    for (int j = 0; j < column_fibres; ++j) {
        int mean = u * a[j] + v * b[j] + w * c[j];
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
    const Profile zero{};
    for (int a = 0; a < row_fibres; ++a) {
        for (int b = a + 1; b < row_fibres; ++b) {
            for (int u = 1; u <= fibre_size; ++u) {
                for (int v = 1 + ((u + 1) & 1); v <= fibre_size; v += 2) {
                    check(two, profiles[a], profiles[b], zero, u, v, 0);
                }
            }
            for (int c = b + 1; c < row_fibres; ++c) {
                for (int u = 1; u <= fibre_size; ++u) {
                    for (int v = 1; v <= fibre_size; ++v) {
                        for (int w = 1 + ((u + v + 1) & 1); w <= fibre_size; w += 2) {
                            check(three, profiles[a], profiles[b], profiles[c], u, v, w);
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
}
