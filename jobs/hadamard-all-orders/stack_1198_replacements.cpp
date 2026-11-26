#include <algorithm>
#include <array>
#include <cstdlib>
#include <iostream>
#include <vector>

using Integer = __int128_t;
using Vector = std::array<int, 9>;

struct Entry {
    int index;
    Integer key;
};

int main() {
    Vector target{}, maxima{};
    for (auto& value : target) {
        std::cin >> value;
    }
    int count;
    if (!(std::cin >> count) || count <= 0) {
        return 1;
    }
    std::vector<Vector> moves(count);
    for (auto& move : moves) {
        for (int i = 0; i < 9; ++i) {
            if (!(std::cin >> move[i])) {
                return 1;
            }
            maxima[i] = std::max(maxima[i], std::abs(move[i]));
        }
    }

    // The absolute residual in a digit of any sum of at most three moves is smaller than its radix.
    std::array<Integer, 9> place{};
    Integer radix_product = 1;
    for (int i = 0; i < 9; ++i) {
        const int radix = std::max(2, 3 * maxima[i] + std::abs(target[i]) + 1);
        if (radix_product > (Integer{1} << 116) / radix) {
            return 1;
        }
        place[i] = radix_product;
        radix_product *= radix;
    }
    const auto encode = [&](const Vector& vector) {
        Integer key = 0;
        for (int i = 0; i < 9; ++i) {
            key += vector[i] * place[i];
        }
        return key;
    };
    const Integer goal = encode(target);
    std::vector<Entry> entries;
    entries.reserve(count);
    for (int i = 0; i < count; ++i) {
        entries.push_back({i, encode(moves[i])});
    }
    std::sort(entries.begin(), entries.end(), [](const Entry& a, const Entry& b) {
        return a.key < b.key;
    });
    for (int i = 1; i < count; ++i) {
        if (entries[i - 1].key == entries[i].key) {
            return 1;
        }
    }
    if (goal == 0 || std::binary_search(entries.begin(), entries.end(), Entry{0, goal},
            [](const Entry& a, const Entry& b) { return a.key < b.key; })) {
        return 1;
    }
    for (int first = 0, last = count - 1; first <= last;) {
        const Integer sum = entries[first].key + entries[last].key;
        if (sum == goal) {
            return 1;
        }
        if (sum < goal) {
            ++first;
        } else {
            --last;
        }
    }

    #pragma omp parallel for schedule(dynamic, 32)
    for (int first = 0; first < count; ++first) {
        const Integer needed = goal - entries[first].key;
        for (int middle = first, last = count - 1; middle <= last;) {
            const Integer sum = entries[middle].key + entries[last].key;
            if (sum < needed) {
                ++middle;
            } else if (sum > needed) {
                --last;
            } else {
                #pragma omp critical
                std::cout << entries[first].index << ' ' << entries[middle].index << ' '
                          << entries[last].index << '\n';
                ++middle;
                --last;
            }
        }
    }
}
