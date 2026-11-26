#include <array>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <iostream>

constexpr int Order = 1196;
constexpr int Prime = 599;
constexpr int ReserveCount = 596;
constexpr int AxisCount = 17;
constexpr int ChunkCount = 19;
using Bits = std::array<uint64_t, ChunkCount>;

int hamming(const Bits& first, const Bits& second) {
    int distance = 0;
    for (int i = 0; i < ChunkCount; ++i) {
        distance += __builtin_popcountll(first[i] ^ second[i]);
    }
    return distance;
}

int sign_at(const Bits& bits, int index) {
    return ((bits[index / 64] >> (index % 64)) & 1) ? 1 : -1;
}

void toggle(Bits& bits, int index) {
    bits[index / 64] ^= uint64_t{1} << (index % 64);
}

struct Search {
    std::array<int, ReserveCount> unused;
    std::array<int, AxisCount> rows, pivots;
    std::array<int, Order> reserve_index;
    std::array<Bits, Order> source;
    std::array<Bits, AxisCount> old_words;
    int axis[ReserveCount][AxisCount]{};
    int image[AxisCount][Order]{};
    int passed_energy = 0;
    int possible_words = 0;
    std::array<int, AxisCount> occurrences{};

    void read() {
        reserve_index.fill(-1);
        for (int i = 0; i < ReserveCount; ++i) {
            std::cin >> unused[i];
            assert(unused[i] >= 0 && unused[i] < Order && reserve_index[unused[i]] == -1);
            reserve_index[unused[i]] = i;
        }
        for (int& r : rows) std::cin >> r;
        for (int& g : pivots) std::cin >> g;
        for (Bits& col : source) {
            for (uint64_t& chunk : col) std::cin >> chunk;
        }
        assert(std::cin);
    }

    void build_axes() {
        for (int a = 0; a < AxisCount; ++a) {
            assert(reserve_index[pivots[a]] >= 0);
            for (int b = 0; b < a; ++b) assert(pivots[a] != pivots[b]);
            old_words[a] = source[pivots[a]];
            toggle(old_words[a], rows[a]);
            for (int j = 0; j < ReserveCount; ++j) {
                const int g = unused[j];
                axis[j][a] = Order / 2 - hamming(source[g], old_words[a])
                             - Prime * (g == pivots[a]);
                assert(g == pivots[a] ? axis[j][a] == -2 : std::abs(axis[j][a]) == 1);
                for (int r = 0; r < Order; ++r) {
                    image[a][r] += sign_at(source[g], r) * axis[j][a];
                }
            }
            for (int b = 0; b <= a; ++b) {
                int dot = 0;
                for (int j = 0; j < ReserveCount; ++j) dot += axis[j][a] * axis[j][b];
                assert(dot == Prime * (a == b));
            }
        }
    }

    void replay_word(const Bits& word, const std::array<int, AxisCount>& coeff, int hub) {
        for (int g = 0; g < Order; ++g) {
            const int half_projection = Order / 2 - hamming(word, source[g]);
            const int j = reserve_index[g];
            if (j < 0) {
                if (std::abs(half_projection) != 1) return;
            } else {
                int expected = Prime * (g == pivots[hub]);
                for (int a = 0; a < AxisCount; ++a) expected += axis[j][a] * coeff[a];
                if (half_projection != expected) return;
            }
        }
        assert(word == old_words[hub]);
        ++occurrences[hub];
    }

    void reconstruct(const std::array<int, Order>& projected,
                     const std::array<int, AxisCount>& coeff, int hub) {
        int energy = 0;
        for (const int value : projected) {
            const int residual = std::abs(value) - (Prime - 1);
            if (residual > Prime + 1) return;
            energy += residual * residual;
            if (energy > Order * (Prime + 1)) return;
        }
        ++passed_energy;
        Bits word{};
        std::array<int, 2> ambiguous{};
        int count = 0;
        for (int r = 0; r < Order; ++r) {
            if (std::abs(projected[r]) <= 2) {
                assert(count < 2);
                ambiguous[count++] = r;
            } else if (projected[r] > 0) {
                toggle(word, r);
            }
        }
        possible_words += 1 << count;
        for (int mask = 0; mask < (1 << count); ++mask) {
            Bits candidate = word;
            for (int j = 0; j < count; ++j) {
                if ((mask >> j) & 1) toggle(candidate, ambiguous[j]);
            }
            replay_word(candidate, coeff, hub);
        }
    }

    void search() {
        int total = 0;
        for (int hub = 0; hub < AxisCount; ++hub) {
            std::array<int, AxisCount - 1> others{};
            for (int a = 0, j = 0; a < AxisCount; ++a) {
                if (a != hub) others[j++] = a;
            }
            const int j = reserve_index[pivots[hub]];
            for (const int central : {1, 3}) {
                std::array<int, AxisCount> coeff{};
                coeff[hub] = central;
                std::array<int, Order> projected{};
                for (int r = 0; r < Order; ++r) {
                    projected[r] = Prime * sign_at(source[pivots[hub]], r) + central * image[hub][r];
                }
                for (unsigned mask = 0; mask < (1u << others.size()); ++mask) {
                    if (mask != 0) {
                        const int a = others[__builtin_ctz(mask)];
                        const int previous = coeff[a];
                        coeff[a] = previous != 0 ? 0 : -2 * axis[j][a];
                        const int change = coeff[a] - previous;
                        for (int r = 0; r < Order; ++r) projected[r] += change * image[a][r];
                    }
                    reconstruct(projected, coeff, hub);
                    ++total;
                }
            }
        }
        assert(total == 2228224 && passed_energy == 17 && possible_words == 34);
        for (int count : occurrences) assert(count == 1);
        std::cout << "Fixed exterior: 2228224 lifts, 17 energy survivors, 34 raw checks, "
                  << "17 existing words, zero new words\n";
    }
};

int main() {
    Search problem;
    problem.read();
    problem.build_axes();
    problem.search();
}
