#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>

constexpr int n = 92;
constexpr int modulus = 23;
constexpr int width = 6;

struct Rows {
    std::uint64_t low = 0;
    std::uint64_t high = 0;

    Rows operator|(Rows other) const { return {low | other.low, high | other.high}; }
    Rows operator&(Rows other) const { return {low & other.low, high & other.high}; }
    Rows operator~() const { return {~low, ~high}; }
    bool any() const { return low || high; }
};

struct Enumeration {
    std::array<std::array<int, n>, n> matrix{};
    std::array<Rows, n> support{};
    std::array<int, modulus> inverse{};
    std::array<int, width> columns{};
    int size = 0;
    std::uint64_t tested = 0;
    std::uint64_t stopping = 0;

    void read() {
        for (int row = 0; row < n; ++row) {
            for (int col = 0; col < n; ++col) {
                int x;
                std::cin >> x;
                assert(std::cin && x >= -1 && x <= 1);
                matrix[row][col] = (x + modulus) % modulus;
                if (x && row < 64) support[col].low |= std::uint64_t{1} << row;
                if (x && row >= 64) support[col].high |= std::uint64_t{1} << (row - 64);
            }
        }
        for (int x = 1; x < modulus; ++x)
            for (int y = 1; y < modulus; ++y)
                if (x * y % modulus == 1) inverse[x] = y;
    }

    int rank() const {
        int pivots[width][width] = {};
        int count = 0;
        for (int row = 0; row < n && count < size; ++row) {
            int values[width];
            for (int j = 0; j < size; ++j) values[j] = matrix[row][columns[j]];
            for (int j = 0; j < size; ++j) {
                int x = values[j];
                if (!x) continue;
                if (pivots[j][j]) {
                    for (int k = j + 1; k < size; ++k)
                        values[k] = (values[k] + modulus * modulus - x * pivots[j][k]) % modulus;
                } else {
                    for (int k = j; k < size; ++k)
                        pivots[j][k] = values[k] * inverse[x] % modulus;
                    ++count;
                    break;
                }
            }
        }
        return count;
    }

    void scan(int depth, int first, Rows seen, Rows once) {
        if (depth == size - 1) {
            for (int col = first; col < n; ++col) {
                ++tested;
                Rows next = support[col];
                // Every previous singleton must be covered. No new singleton may appear.
                if ((once & ~next).any() || (next & ~seen).any()) continue;
                ++stopping;
                columns[depth] = col;
                assert(rank() == size);
            }
            return;
        }
        for (int col = first; col <= n - (size - depth); ++col) {
            columns[depth] = col;
            Rows next = support[col];
            scan(depth + 1, col + 1, seen | next, (once & ~next) | (next & ~seen));
        }
    }
};

int main() {
    Enumeration proof;
    proof.read();
    for (int size : {5, 6}) {
        proof.size = size;
        proof.tested = proof.stopping = 0;
        proof.scan(0, 0, {}, {});
        assert(proof.tested == (size == 5 ? 49177128 : 713068356));
        assert(proof.stopping == (size == 5 ? 2768 : 1526544));
        std::cout << size << " columns: " << proof.tested << " sets, "
                  << proof.stopping << " stopping sets, all full rank modulo 23\n";
    }
}
