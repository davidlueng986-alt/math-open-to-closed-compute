// Exact finite screens for a changed second fold of the eighth exterior factor.
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <string_view>
#include <utility>
#include <vector>

namespace {
constexpr int prime = 599;
constexpr int blocks = 10;
using Word = std::array<std::uint64_t, blocks>;

void read_word(Word& word) {
    for (auto& block : word) std::cin >> block;
}

int intersection(const Word& first, const Word& second) {
    int result = 0;
    for (int i = 0; i < blocks; ++i) result += std::popcount(first[i] & second[i]);
    return result;
}

int census() {
    int dimension = 0, period = 0, cap = 0;
    std::uint64_t singles = 0, coordinates = 0;
    std::cin >> dimension >> period >> cap >> singles >> coordinates;
    std::vector<std::uint64_t> basis(dimension);
    for (auto& word : basis) std::cin >> word;
    if (!std::cin) return 2;
    std::array<int, prime + 2> counts{};
    std::uint64_t word = 0;
    const auto limit = std::uint64_t{1} << dimension;
    for (std::uint64_t i = 1; i < limit; ++i) {
        word ^= basis[std::countr_zero(i)];
        int weight = period * std::popcount(word & coordinates & ~singles) + std::popcount(word & singles);
        ++counts[weight];
        if (weight <= cap) std::cout << weight << ' ' << word << '\n';
    }
    std::cout << "spectrum";
    for (int n : counts) std::cout << ' ' << n;
    std::cout << '\n';
    return 0;
}

int screen_period() {
    int shapes = 0;
    std::cin >> shapes;
    std::vector<std::vector<int>> seeds(shapes);
    for (auto& seed : seeds) {
        int size = 0;
        std::cin >> size;
        seed.resize(size);
        for (int& x : seed) std::cin >> x;
    }
    const auto read_multipliers = [] {
        int size = 0;
        std::cin >> size;
        std::vector<int> multipliers(size);
        for (int& a : multipliers) std::cin >> a;
        return multipliers;
    };
    const auto affine = read_multipliers();
    const auto projective = read_multipliers();
    std::array<int, 2> slack{}, infinity{};
    std::array<std::array<Word, prime>, 2> gain{}, loss{};
    for (int cut = 0; cut < 2; ++cut) {
        std::array<int, prime> signs{};
        std::cin >> slack[cut] >> infinity[cut];
        for (int& s : signs) std::cin >> s;
        for (int shift = 0; shift < prime; ++shift) {
            for (int x = 0; x < prime; ++x) {
                const auto bit = std::uint64_t{1} << (x % 64);
                int s = signs[(x + shift) % prime];
                if (s == 1) gain[cut][shift][x / 64] |= bit;
                if (s == -1) loss[cut][shift][x / 64] |= bit;
            }
        }
    }
    if (!std::cin) return 2;
    std::array<int, prime> inverse{};
    for (int a = 1; a < prime; ++a) {
        for (int b = 1; b < prime; ++b) {
            if (a * b % prime == 1) {
                inverse[a] = b;
                break;
            }
        }
    }
    std::array<long long, 2> settings{};
    std::array<std::array<long long, 2>, 2> passed{};
    const auto test = [&](const Word& support, bool has_infinity) {
        settings[has_infinity] += prime;
        for (int shift = 0; shift < prime; ++shift) {
            for (int cut = 0; cut < 2; ++cut) {
                int s = slack[cut] + (has_infinity ? infinity[cut] : 0);
                s += intersection(support, gain[cut][shift]) - intersection(support, loss[cut][shift]);
                if (s < 0) break;
                ++passed[has_infinity][cut];
            }
        }
    };
    const auto insert = [](Word& support, int point) {
        support[point / 64] |= std::uint64_t{1} << (point % 64);
    };
    for (const auto& seed : seeds) {
        for (int a : affine) {
            Word support{};
            bool at_infinity = false;
            for (int x : seed) {
                if (x == prime) at_infinity = true;
                else insert(support, a * x % prime);
            }
            test(support, at_infinity);
        }
        for (int a : projective) {
            for (int b = 0; b < prime; ++b) {
                Word support{};
                bool at_infinity = false;
                for (int x : seed) {
                    if (x == prime) insert(support, 0);
                    else {
                        int denominator = (x + b) % prime;
                        if (denominator == 0) at_infinity = true;
                        else insert(support, a * inverse[denominator] % prime);
                    }
                }
                test(support, at_infinity);
            }
        }
    }
    for (int i = 0; i < 2; ++i) {
        std::cout << settings[i] << ' ' << passed[i][0] << ' ' << passed[i][1] << '\n';
    }
    return 0;
}

int screen_shortening() {
    int dimension = 0, classes = 0, cut_count = 0;
    std::cin >> dimension >> classes >> cut_count;
    std::vector<Word> basis(dimension), cosets(classes);
    for (auto& word : basis) read_word(word);
    for (auto& word : cosets) read_word(word);
    struct Cut {
        int slack;
        std::vector<std::pair<int, Word>> terms;
    };
    std::vector<Cut> cuts(cut_count);
    for (auto& cut : cuts) {
        int terms = 0;
        std::cin >> cut.slack >> terms;
        cut.terms.resize(terms);
        for (auto& [price, mask] : cut.terms) {
            std::cin >> price;
            read_word(mask);
        }
    }
    if (!std::cin) return 2;
    std::array<long long, 2> passed{};
    const auto limit = std::uint64_t{1} << dimension;
    for (int c = 0; c < classes; ++c) {
        Word word = cosets[c];
        for (std::uint64_t i = 0; i < limit; ++i) {
            if (i) {
                const auto& generator = basis[std::countr_zero(i)];
                for (int j = 0; j < blocks; ++j) word[j] ^= generator[j];
            } else if (c == 0) {
                continue;
            }
            bool good = true;
            for (const auto& cut : cuts) {
                int s = cut.slack;
                for (const auto& [price, mask] : cut.terms) s += price * intersection(word, mask);
                if (s < 0) {
                    good = false;
                    break;
                }
            }
            if (good) ++passed[c != 0];
        }
    }
    std::cout << passed[0] << ' ' << passed[1] << '\n';
    return 0;
}
}  // namespace

int main(int argc, char** argv) {
    if (argc != 2) return 2;
    const std::string_view mode = argv[1];
    if (mode == "census") return census();
    if (mode == "period") return screen_period();
    if (mode == "shortening") return screen_shortening();
    return 2;
}
