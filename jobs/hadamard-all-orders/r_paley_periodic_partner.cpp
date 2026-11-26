#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <string>
#include <utility>
#include <vector>

constexpr int pairs = 24;
using Deck = std::array<int, pairs>;
using Key = std::uint64_t;

std::vector<Deck> binary_decks(const std::vector<Deck>& rows, int first, int count) {
    std::vector<Deck> out(1 << count);
    for (int i = first; i < first + count; ++i)
        for (int j = 0; j < pairs; ++j) out[0][j] -= rows[i][j];
    for (unsigned mask = 1; mask < out.size(); ++mask) {
        unsigned bit = __builtin_ctz(mask);
        out[mask] = out[mask & (mask - 1)];
        for (int j = 0; j < pairs; ++j) out[mask][j] += 2 * rows[first + bit][j];
    }
    return out;
}

void symmetric() {
    Deck weights{};
    for (int& w : weights) std::cin >> w;
    std::vector<Deck> map(pairs);
    for (auto& row : map)
        for (int& x : row) std::cin >> x;
    auto left = binary_decks(map, 0, 12);
    auto right = binary_decks(map, 12, 12);
    for (unsigned a = 1; a < left.size(); a += 2)
        for (unsigned b = 0; b < right.size(); ++b) {
            int squared = 0;
            int j = 0;
            for (; j < pairs; ++j) {
                int v = (left[a][j] + right[b][j] + 299 * 24 + 149) % 299 - 149;
                if (v % 2 == 0 || std::abs(v) > 138) break;
                squared += weights[j] * v * v;
                if (squared > 27460) break;
            }
            if (j == pairs && squared == 27460) std::cout << a << " " << b << "\n";
        }
}

struct Ternary {
    int count = 0;
    std::array<int, 10> moduli{}, lengths{}, zero{};
    std::array<std::array<int, 10>, 23> check{};
    using Entry = std::pair<Key, int>;

    void read() {
        std::cin >> count;
        assert(count >= 1 && count <= 10);
        for (int j = 0; j < count; ++j) {
            std::cin >> moduli[j];
            int p = moduli[j];
            assert(p == 13 || p == 23);
            lengths[j] = p == 13 ? 4 : 5;
            for (auto& row : check) std::cin >> row[j];
        }
    }

    void recurse(int i, int end, int code, int power, int phase, std::array<int, 10>& value,
                 std::vector<Entry>& entries) const {
        if (i == end) {
            Key key = 0;
            int shift = 0;
            for (int j = 0; j < count; ++j) {
                int v = (phase * value[j] + moduli[j] * 12) % moduli[j];
                key |= Key(v) << shift;
                shift += lengths[j];
            }
            entries.emplace_back(key, code);
            return;
        }
        for (int j = 0; j < count; ++j) value[j] -= check[i][j];
        for (int digit = 0; digit < 3; ++digit) {
            recurse(i + 1, end, code + digit * power, 3 * power, phase, value, entries);
            for (int j = 0; j < count; ++j) value[j] += check[i][j];
        }
        for (int j = 0; j < count; ++j) value[j] -= 2 * check[i][j];
    }

    void solve(int branch) {
        std::vector<Entry> right;
        right.reserve(531441);
        recurse(11, 23, 0, 1, -1, zero, right);
        std::sort(right.begin(), right.end());
        std::vector<Entry> left;
        left.reserve(177147);
        recurse(0, 11, 0, 1, 1, zero, left);
        for (auto [k, code] : left) {
            auto p = std::lower_bound(right.begin(), right.end(), Entry{k, 0});
            for (; p != right.end() && p->first == k; ++p)
                std::cout << branch << " " << code << " " << p->second << "\n";
        }
    }
};

Key key_of(const Deck& row, const std::array<int, 4>& coordinates) {
    Key k = 0;
    for (unsigned j = 0; j < coordinates.size(); ++j) {
        int x = row[coordinates[j]];
        assert(x >= -256 && x <= 255);
        k |= Key(x + 256) << (9 * j);
    }
    return k;
}

void complete_even() {
    int cases;
    std::cin >> cases;
    std::uint64_t matched = 0;
    for (int run = 0; run < cases; ++run) {
        int n;
        std::cin >> n;
        assert(n <= 28);
        Deck target;
        for (int& x : target) std::cin >> x;
        std::vector<Deck> rows(n);
        for (auto& row : rows)
            for (int& x : row) std::cin >> x;
        auto left = binary_decks(rows, 0, n / 2);
        auto right = binary_decks(rows, n / 2, n - n / 2);
        std::vector<int> good;
        for (int j = 0; j < pairs; ++j)
            if (target[j] >= 0) good.push_back(j);
        assert(good.size() >= 23);
        // At most one bad pair. One of these two disjoint keys must be exact.
        for (int branch : {1, 2}) {
            std::array<int, 4> coordinates;
            for (int i = 0; i < 4; ++i) coordinates[i] = good[5 * i + branch];
            std::vector<std::pair<Key, unsigned>> index;
            for (unsigned i = 0; i < right.size(); ++i)
                index.emplace_back(key_of(right[i], coordinates), i);
            std::sort(index.begin(), index.end());
            std::vector<Deck> marks(1);
            for (int j : coordinates) if (target[j]) {
                unsigned previous = marks.size();
                for (unsigned i = 0; i < previous; ++i) {
                    marks[i][j] = -2;
                    Deck extra = marks[i];
                    extra[j] = 2;
                    marks.push_back(extra);
                }
            }
            for (unsigned a = 0; a < left.size(); ++a)
                for (Deck code : marks) {
                    for (int j : coordinates) code[j] -= left[a][j];
                    Key value = key_of(code, coordinates);
                    auto p = std::lower_bound(index.begin(), index.end(), std::pair{value, 0U});
                    for (; p != index.end() && p->first == value; ++p) {
                        ++matched;
                        const auto& b = right[p->second];
                        int passed = 0;
                        for (int j = 0; j < pairs; ++j)
                            passed += std::abs(left[a][j] + b[j]) == target[j];
                        if (passed >= 23) std::cout << "hit " << run << " " << a << " " << p->second << "\n";
                    }
                }
        }
    }
    std::cout << "matched " << matched << "\n";
}

int main(int argc, char** argv) {
    assert(argc == 2);
    std::string mode = argv[1];
    if (mode == "symmetric") symmetric();
    else if (mode == "odd") {
        int count;
        std::cin >> count;
        for (int i = 0; i < count; ++i) {
            Ternary m;
            m.read();
            m.solve(i);
        }
    } else {
        assert(mode == "even");
        complete_even();
    }
    assert(std::cin);
}
