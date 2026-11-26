// Sharp common-positive count for five finite columns of normalized Paley H(600).
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <limits>

constexpr int field_order = 599;
constexpr int word_count = (field_order + 63) / 64;

int main() {
    std::array<bool, field_order> square{};
    for (int value = 1; value < field_order; ++value) {
        square[value * value % field_order] = true;
    }
    std::array<std::array<std::uint64_t, word_count>, field_order> columns{};
    for (int column = 0; column < field_order; ++column) {
        for (int row = 0; row < field_order; ++row) {
            if (square[(column + field_order - row) % field_order]) {
                columns[column][row / 64] |= std::uint64_t{1} << (row % 64);
            }
        }
    }

    // Translation and square dilation, after ordering the two columns, take
    // any pair to (0,1). Count every choice of the other three finite columns.
    std::array<std::uint64_t, word_count> first_pair{};
    for (int w = 0; w < word_count; ++w) {
        first_pair[w] = columns[0][w] & columns[1][w];
    }
    int minimum = std::numeric_limits<int>::max();
    std::uint64_t checked = 0;
    for (int a = 2; a < field_order; ++a) {
        std::array<std::uint64_t, word_count> first_three{};
        for (int w = 0; w < word_count; ++w) {
            first_three[w] = first_pair[w] & columns[a][w];
        }
        for (int b = a + 1; b < field_order; ++b) {
            std::array<std::uint64_t, word_count> first_four{};
            for (int w = 0; w < word_count; ++w) {
                first_four[w] = first_three[w] & columns[b][w];
            }
            for (int c = b + 1; c < field_order; ++c) {
                int count = 0;
                for (int w = 0; w < word_count; ++w) {
                    count += std::popcount(first_four[w] & columns[c][w]);
                }
                ++checked;
                if (count < minimum) {
                    minimum = count;
                }
            }
        }
    }
    std::cout << "Paley H(600): " << checked
              << " five-column choices; minimum common positives " << minimum << '\n';
    return checked == 35284690 && minimum == 4 ? 0 : 1;
}
