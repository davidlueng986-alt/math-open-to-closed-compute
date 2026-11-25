#include <algorithm>
#include <array>
#include <bit>
#include <bitset>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <vector>

namespace {
constexpr int order = 299;
constexpr int half = order / 2;
constexpr int dimension = half + 2;
using Sites = std::bitset<order>;
using BinaryVector = std::array<std::uint64_t, 3>;
using Columns = std::array<BinaryVector, order>;

void require(bool condition, const char* message) {
    if (!condition)
        throw std::runtime_error(message);
}

int highest_bit(const BinaryVector& value) {
    for (int i = 2; i >= 0; --i)
        if (value[i])
            return 64 * i + 63 - std::countl_zero(value[i]);
    return -1;
}

void add(BinaryVector& left, const BinaryVector& right) {
    for (int i = 0; i < 3; ++i)
        left[i] ^= right[i];
}

void set_bit(BinaryVector& value, int i) {
    value[i / 64] |= std::uint64_t{1} << (i % 64);
}

bool get_bit(const BinaryVector& value, int i) {
    return (value[i / 64] >> (i % 64)) & 1;
}

Sites rotate(const Sites& value, int distance) {
    return (value >> distance) | (value << (order - distance));
}

struct Row {
    Sites positive, negative;

    Sites support() const { return positive | negative; }

    Row switched(const Sites& flips) const {
        return {positive ^ flips, negative ^ flips};
    }

    int sum_on(const Sites& mask) const {
        return int((positive & mask).count()) - int((negative & mask).count());
    }

    int correlation(int distance) const {
        const auto p = rotate(positive, distance);
        const auto m = rotate(negative, distance);
        return int((positive & p).count() + (negative & m).count())
             - int((positive & m).count() + (negative & p).count());
    }
};

void incidence(Columns& result, const Sites& support) {
    for (int distance = 1; distance <= half; ++distance) {
        const auto odd = support & (rotate(support, distance) ^ rotate(support, order - distance));
        // libstdc++ sparse iteration keeps this integer census small.
        for (std::size_t i = odd._Find_first(); i < order; i = odd._Find_next(i))
            set_bit(result[i], distance - 1);
    }
}

struct Reduction {
    std::array<BinaryVector, dimension> pivots{};
    std::array<Sites, dimension> preimages{};
    int rank = 0;

    void insert(BinaryVector value, Sites preimage = {}, bool keep_preimage = false) {
        for (int i = highest_bit(value); i >= 0; i = highest_bit(value)) {
            if (highest_bit(pivots[i]) < 0) {
                pivots[i] = value;
                if (keep_preimage)
                    preimages[i] = preimage;
                ++rank;
                return;
            }
            add(value, pivots[i]);
            if (keep_preimage)
                preimage ^= preimages[i];
        }
    }

    BinaryVector remainder(BinaryVector value, Sites* preimage = nullptr) const {
        for (int i = dimension - 1; i >= 0; --i) {
            if (!get_bit(value, i) || highest_bit(pivots[i]) < 0)
                continue;
            add(value, pivots[i]);
            if (preimage)
                *preimage ^= preimages[i];
        }
        return value;
    }

    std::uint32_t compressed_remainder(BinaryVector value) const {
        value = remainder(value);
        std::uint32_t result = 0;
        int j = 0;
        for (int i = 0; i < half; ++i)
            if (highest_bit(pivots[i]) < 0)
                result |= std::uint32_t(get_bit(value, i)) << j++;
        require(j == 20, "expected twenty mod-four consistency bits");
        return result;
    }
};

struct Swap {
    int row, positive, negative;
    std::uint32_t remainder;
    BinaryVector effect;
};

bool follows(const Swap& left, const Swap& right) {
    return left.row < right.row
        || (left.row == right.row && left.positive < right.positive && left.negative < right.negative);
}

struct Counts {
    std::array<long long, 4> projected{}, even{}, compatible{};
};

class Census {
public:
    explicit Census(std::array<Row, 4> seed) : input(seed), last_support(seed[2].support()) {
        require(last_support == seed[3].support() && last_support.count() == 130,
                "the aligned last supports must coincide");
        Columns columns{};
        incidence(columns, last_support);
        for (int i = 0; i < order; ++i) {
            if (!last_support[i])
                continue;
            Sites unit;
            unit.set(i);
            relative.insert(columns[i], unit, true);
        }
        require(relative.rank == 129, "incorrect last relative rank");
        for (int r = 0; r < 2; ++r)
            add_swaps(r);
        require(swaps.size() == 14206, "unexpected swap count");
    }

    Counts run() const {
        Counts counts;
        check({}, 0, counts);
        std::vector<std::vector<int>> buckets(std::size_t{1} << 20);
        for (int i = 0; i < int(swaps.size()); ++i) {
            const auto& item = swaps[i];
            if (item.remainder == 0)
                check({&item}, 1, counts);
            buckets[item.remainder].push_back(i);
        }
        for (int i = 0; i < int(swaps.size()); ++i) {
            const auto& a = swaps[i];
            for (int j = i + 1; j < int(swaps.size()); ++j) {
                const auto& b = swaps[j];
                if (!follows(a, b))
                    continue;
                const auto remainder = a.remainder ^ b.remainder;
                if (remainder == 0)
                    check({&a, &b}, 2, counts);
                const auto& bucket = buckets[remainder];
                for (auto k = std::upper_bound(bucket.begin(), bucket.end(), j); k != bucket.end(); ++k) {
                    const auto& c = swaps[*k];
                    if (follows(b, c))
                        check({&a, &b, &c}, 3, counts);
                }
            }
        }
        return counts;
    }

private:
    std::array<Row, 4> input;
    Sites last_support;
    Reduction relative;
    std::vector<Swap> swaps;

    void add_swaps(int r) {
        Columns columns{};
        incidence(columns, input[r].support());
        for (int i = 0; i < order; ++i) {
            if (!input[r].positive[i])
                continue;
            for (int j = 0; j < order; ++j) {
                if (!input[r].negative[j])
                    continue;
                auto effect = columns[i];
                add(effect, columns[j]);
                swaps.push_back({r, i, j, relative.compressed_remainder(effect), effect});
            }
        }
    }

    void check(const std::array<const Swap*, 3>& moves, int size, Counts& counts) const {
        ++counts.projected[size];
        std::array<Sites, 2> first_flips{};
        BinaryVector wanted_relative{};
        for (int i = 0; i < size; ++i) {
            const auto& move = *moves[i];
            first_flips[move.row].set(move.positive);
            first_flips[move.row].set(move.negative);
            add(wanted_relative, move.effect);
        }
        Sites second_last_flips;
        require(highest_bit(relative.remainder(wanted_relative, &second_last_flips)) < 0,
                "mod-four projection disagrees with direct elimination");
        const auto a = input[0].switched(first_flips[0]);
        const auto b = input[1].switched(first_flips[1]);
        const auto c = input[2];
        const auto d = input[3].switched(second_last_flips);
        const Sites opposite = c.positive ^ d.positive;
        const Sites same = last_support ^ opposite;
        if (same.count() % 2 || opposite.count() % 2)
            return;
        ++counts.even[size];
        BinaryVector wanted{};
        for (int lag = 1; lag <= half; ++lag) {
            const int residual = a.correlation(lag) + b.correlation(lag)
                               + c.correlation(lag) + d.correlation(lag) + 2;
            require(residual % 4 == 0, "mod-four correlation failed direct replay");
            if ((residual / 4) & 1)
                set_bit(wanted, lag - 1);
        }
        if ((c.sum_on(same) / 2) & 1)
            set_bit(wanted, half);
        if ((c.sum_on(opposite) / 2) & 1)
            set_bit(wanted, half + 1);
        Columns columns{};
        incidence(columns, same);
        incidence(columns, opposite);
        Reduction simultaneous;
        for (int i = 0; i < order; ++i) {
            if (!last_support[i])
                continue;
            set_bit(columns[i], half + int(opposite[i]));
            simultaneous.insert(columns[i]);
        }
        require(simultaneous.rank == 128, "unexpected last simultaneous rank");
        if (highest_bit(simultaneous.remainder(wanted)) < 0)
            ++counts.compatible[size];
    }
};

std::array<Row, 4> read_seed() {
    std::array<Row, 4> input{};
    for (auto& row : input)
        for (int i = 0; i < order; ++i) {
            int entry;
            require(bool(std::cin >> entry) && entry >= -1 && entry <= 1, "invalid seed entry");
            if (entry > 0)
                row.positive.set(i);
            if (entry < 0)
                row.negative.set(i);
        }
    return input;
}
}

int main() {
    try {
        const auto counts = Census(read_seed()).run();
        require(counts.projected == std::array<long long, 4>{1, 0, 71, 184238},
                "unexpected canonical mod-four counts");
        require(counts.even == counts.projected, "unexpected group support parities");
        require(counts.compatible == std::array<long long, 4>{1, 0, 0, 0},
                "unexpected modulo-eight consistency counts");
        std::cout << "Swaps | mod four | even support split | mod eight with group-sum parity\n";
        for (int i = 0; i < 4; ++i)
            std::cout << i << " " << counts.projected[i] << " " << counts.even[i] << " "
                      << counts.compatible[i] << "\n";
    } catch (const std::exception& error) {
        std::cerr << error.what() << "\n";
        return 1;
    }
}
