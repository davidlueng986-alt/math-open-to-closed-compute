#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace {
constexpr int length = 299;
constexpr int half = length / 2;
constexpr int prime = 11;
constexpr std::array inverses{0, 1, 6, 4, 3, 9, 2, 8, 7, 5, 10};

using Integer = std::uint64_t;
using Residue = std::uint8_t;
using Equation = std::vector<Residue>;
using Word = std::array<int, length>;
using Words = std::array<Word, 4>;

int reduce(int value) {
    const int residue = value % prime;
    return residue < 0 ? residue + prime : residue;
}

class LinearSystem {
public:
    explicit LinearSystem(int variables) : pivots(variables), width(variables) {}

    void add(Equation equation) {
        for (int i = 0; i < width; ++i) {
            const auto leading = equation[i];
            if (leading == 0) continue;
            if (pivots[i][1].empty()) {
                for (int j = i; j <= width; ++j)
                    equation[j] = reduce(equation[j] * inverses[leading]);
                pivots[i][1] = std::move(equation);
                for (int factor = 2; factor < prime; ++factor) {
                    auto scaled = pivots[i][1];
                    for (int j = i; j <= width; ++j)
                        scaled[j] = reduce(scaled[j] * factor);
                    pivots[i][factor] = std::move(scaled);
                }
                ++rank;
                return;
            }
            const auto& pivot = pivots[i][leading];
            for (int j = i + 1; j <= width; ++j) {
                const int difference = prime + equation[j] - pivot[j];
                equation[j] = difference >= prime ? difference - prime : difference;
            }
        }
        inconsistent = equation[width] != 0;
    }

    bool compatible() const { return !inconsistent; }
    int nullity() const { return width - rank; }

    bool has_binary_assignment() const {
        std::vector<int> values(width);
        const auto assign = [&](auto&& visit, int j) -> bool {
            if (j < 0) return true;
            const auto& pivot = pivots[j][1];
            if (pivot.empty()) {
                for (int bit = 0; bit <= 1; ++bit) {
                    values[j] = bit;
                    if (visit(visit, j - 1)) return true;
                }
                return false;
            }
            int value = pivot[width];
            for (int i = j + 1; i < width; ++i)
                value -= pivot[i] * values[i];
            values[j] = reduce(value);
            return values[j] < 2 && visit(visit, j - 1);
        };
        return assign(assign, width - 1);
    }

private:
    std::vector<std::array<Equation, prime>> pivots;
    int width, rank = 0;
    bool inconsistent = false;
};

struct Site {
    int row, index, sign;
};

class FibreCheck {
public:
    explicit FibreCheck(const Words& source) {
        for (int r = 0; r < 4; ++r)
            for (int i = 0; i < length; ++i)
                if (source[r][i]) sites.push_back({r, i, source[r][i]});
        if (sites.size() != 597) throw std::runtime_error("wrong occupied site count");

        for (int d = 1; d <= half; ++d) {
            auto& coefficients = lag_equations[d];
            for (const auto& [r, i, sign] : sites) {
                const auto& word = source[r];
                coefficients.push_back(reduce(2 * sign *
                    (word[(i + d) % length] + word[(i + length - d) % length])));
            }
            int residual = 2;
            for (const auto& word : source)
                for (int i = 0; i < length; ++i)
                    residual += word[i] * word[(i + d) % length];
            coefficients.push_back(reduce(residual));
        }
    }

    void run(int quotient, int size, bool fixed_margins) const {
        struct Counts {
            Integer cases = 0, linear = 0, binary = 0, unresolved = 0;
            int max_nullity = 0;
        } counts;
        std::vector<int> selected;

        const auto test = [&] {
            unsigned cells = 0, differences = 0;
            for (int u : selected) {
                cells |= 1U << u;
                for (int v : selected)
                    differences |= 1U << ((u - v + quotient) % quotient);
            }
            std::vector<int> variables;
            for (unsigned i = 0; i < sites.size(); ++i)
                if (cells >> (sites[i].index % quotient) & 1U) variables.push_back(i);

            LinearSystem system(variables.size());
            if (fixed_margins) add_margins(system, variables);
            ++counts.cases;
            for (int d = 1; d <= half; ++d) {
                if (differences >> (d % quotient) & 1U) continue;
                const auto& coefficients = lag_equations[d];
                Equation restricted;
                restricted.reserve(variables.size() + 1);
                for (int i : variables) restricted.push_back(coefficients[i]);
                restricted.push_back(coefficients.back());
                system.add(std::move(restricted));
                if (!system.compatible()) return;
            }

            ++counts.linear;
            const int free = system.nullity();
            counts.max_nullity = std::max(counts.max_nullity, free);
            if (free > 24) {
                ++counts.unresolved;
                std::cout << "unresolved";
                for (int y : selected) std::cout << ' ' << y;
                std::cout << '\n';
            } else if (system.has_binary_assignment()) {
                ++counts.binary;
            }
        };

        const auto enumerate = [&](auto&& visit, int from) -> void {
            if (int(selected.size()) == size) {
                test();
                return;
            }
            for (int y = from; y < quotient; ++y) {
                selected.push_back(y);
                visit(visit, y + 1);
                selected.pop_back();
            }
        };
        enumerate(enumerate, 0);
        std::cout << "counts " << counts.cases << ' ' << counts.linear << ' '
                  << counts.binary << ' ' << counts.unresolved << ' '
                  << counts.max_nullity << '\n';
    }

private:
    void add_margins(LinearSystem& system, const std::vector<int>& variables) const {
        for (int q : {13, 23})
            for (int row = 0; row < 4; ++row)
                for (int cell = 0; cell < q; ++cell) {
                    Equation equation(variables.size() + 1);
                    bool populated = false;
                    for (unsigned j = 0; j < variables.size(); ++j) {
                        const auto& site = sites[variables[j]];
                        if (site.row == row && site.index % q == cell) {
                            equation[j] = reduce(site.sign);
                            populated = true;
                        }
                    }
                    if (populated) system.add(std::move(equation));
                }
    }

    std::vector<Site> sites;
    std::array<Equation, half + 1> lag_equations;
};
}

int main(int argc, char** argv) {
    if (argc != 4) return 1;
    const int quotient = std::stoi(argv[1]), size = std::stoi(argv[2]);
    const bool fixed_margins = std::stoi(argv[3]) != 0;
    if ((quotient != 13 && quotient != 23) || size < 1 || size > 4) return 2;

    Words source;
    for (auto& word : source)
        for (int& sign : word)
            if (!(std::cin >> sign) || sign < -1 || sign > 1) return 3;
    FibreCheck(source).run(quotient, size, fixed_margins);
}
