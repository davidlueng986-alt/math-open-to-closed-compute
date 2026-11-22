#include <algorithm>
#include <array>
#include <cstdint>
#include <gmpxx.h>
#include <iostream>
#include <stdexcept>
#include <vector>

using Word = std::uint64_t;
using Wide = unsigned __int128;
constexpr Word scale = Word(1) << 62;
constexpr Wide scale_squared = Wide(scale) * scale;
constexpr int small_limit = 1190;
constexpr int large_minimum = 2382;
constexpr int b_count = 49, d_count = 10;
constexpr int forced_limit = 157;
constexpr Word tail_upper = (scale + large_minimum - 1) / large_minimum + 1;

struct Prime {
    unsigned value;
    Word lo, hi;
    std::vector<unsigned> inverses;
};

std::vector<Prime> primes;
std::vector<Word> prefix_lo{0}, prefix_hi{0};
std::array<Wide, b_count + 1> max_product, max_derivative;
std::array<unsigned, 59> rank_caps;
constexpr Word x_lo = (Wide(scale) * 948) / 1000 - tail_upper;
constexpr Word x_hi = (Wide(scale) * 1055 + 999) / 1000;

struct Counts {
    Word cores = 0, admissible = 0, nodes = 0, reconstructions = 0;
    Word bounded_fractions = 0, congruent_supports = 0, square_discriminants = 0;
};

Wide inverse(const Prime& prime, Wide modulus) {
    unsigned p = prime.value;
    unsigned residue = modulus % p;
    if (!residue) throw std::logic_error("prime divides modulus");
    unsigned multiplier = p - prime.inverses[residue];
    return (modulus / p) * multiplier + (residue * multiplier + 1) / p;
}

Word inverse_word(Word n, Word modulus) {
    std::int64_t a = 0, b = 1;
    Word r = modulus, s = n % modulus;
    while (s) {
        Word quotient = r / s;
        Word remainder = r % s;
        auto next = a - static_cast<std::int64_t>(quotient)*b;
        r = s;
        s = remainder;
        a = b;
        b = next;
    }
    if (r != 1) throw std::logic_error("noninvertible derivative");
    if (a < 0) a += static_cast<std::int64_t>(modulus);
    return a;
}

Wide sub_mod(Wide a, Wide b, Wide modulus) {
    return a >= b ? a - b : modulus - (b - a);
}

std::pair<Wide,Wide> bounded_fraction(Wide residue, Wide modulus,
                                      Wide max_numerator, Wide max_denominator) {
    Wide previous_denominator = 0, denominator = 1;
    Wide previous_error = modulus, error = residue;
    bool positive = true;
    while (denominator <= max_denominator) {
        if (positive && error && error <= max_numerator) return {error, denominator};
        if (!error) break;
        const Wide next_denominator = previous_denominator + (previous_error / error) * denominator;
        const Wide next_error = previous_error % error;
        previous_denominator = denominator;
        denominator = next_denominator;
        previous_error = error;
        error = next_error;
        positive = !positive;
    }
    return {0, 0};
}

struct Branch {
    Counts counts;
    std::array<int, d_count> d_indices{};
    std::vector<int> forced, free, chosen;
    std::vector<Word> free_lo, free_hi;
    std::vector<Wide> residues;
    Word d, dd, lower, upper;
    Wide modulus;
    int reconstruct_count;

    Branch() {
        forced.reserve(b_count);
        chosen.reserve(b_count);
        free.reserve(primes.size());
        free_lo.reserve(primes.size()+1);
        free_hi.reserve(primes.size()+1);
        residues.reserve(primes.size());
    }

    Word largest_union_mass(int next, int depth) const {
        auto best = d_indices;
        for (int i = depth; i < d_count; ++i) best[i] = next + i - depth;
        int stop = b_count;
        Word extra = 0;
        for (int index : best) {
            if (index < stop) ++stop;
            else extra += primes[index].hi;
        }
        return prefix_hi[stop] + extra;
    }

    void check(const std::vector<int>& final_primes) {
        ++counts.congruent_supports;
        mpz_class b = 1, bd = 0;
        auto append = [&](int i) {
            unsigned p = primes[i].value;
            bd = p*bd + b;
            b *= p;
        };
        for (int i : forced) append(i);
        for (int i : chosen) append(free[i]);
        for (int i : final_primes) append(free[i]);
        if (bd % d != 0) throw std::logic_error("derivative congruence failed");
        const mpz_class product = bd / d;
        const mpz_class sum_numerator = b - dd*product;
        if (sum_numerator % d != 0) throw std::logic_error("sum congruence failed");
        const mpz_class sum = sum_numerator / d;
        if (sum < 2 * large_minimum) return;
        const mpz_class discriminant = sum*sum - 4*product;
        if (discriminant <= 0 || !mpz_perfect_square_p(discriminant.get_mpz_t())) return;
        mpz_class root;
        mpz_sqrt(root.get_mpz_t(), discriminant.get_mpz_t());
        const mpz_class difference = sum - root;
        if (difference < 2 * large_minimum || difference % 2 != 0) return;
        ++counts.square_discriminants;
        #pragma omp critical
        {
            std::cout << "CANDIDATE " << d << ' ' << difference/2 << ' ' << (sum+root)/2 << " B";
            for (int i : forced) std::cout << ' ' << primes[i].value;
            for (int i : chosen) std::cout << ' ' << primes[free[i]].value;
            for (int i : final_primes) std::cout << ' ' << primes[free[i]].value;
            std::cout << '\n' << std::flush;
        }
    }

    void recover_factors(Wide numerator, Wide denominator, int from, int left,
                         Word low, Word high) {
        std::vector<int> recovered;
        Wide remainder = denominator;
        for (int i = from; i < static_cast<int>(free.size()); ++i) {
            unsigned p = primes[free[i]].value;
            if (remainder < p) break;
            if (remainder % p) continue;
            remainder /= p;
            if (remainder % p == 0) return;
            recovered.push_back(i);
            low += primes[free[i]].lo;
            high += primes[free[i]].hi;
            if (static_cast<int>(recovered.size()) > left || low > upper) return;
        }
        if (remainder != 1 || static_cast<int>(recovered.size()) != left || high < lower) return;
        Wide actual_numerator = 0;
        for (int i : recovered) actual_numerator += denominator / primes[free[i]].value;
        if (actual_numerator != numerator) return;
        check(recovered);
    }

    void reconstruct(int from, int left, Wide residue, Word low, Word high) {
        ++counts.reconstructions;
        auto [numerator, denominator] = bounded_fraction(residue, modulus,
                                                         max_derivative[left], max_product[left]);
        if (!denominator) return;
        ++counts.bounded_fractions;
        recover_factors(numerator, denominator, from, left, low, high);
    }

    void search_b(int from, int left, Word low, Word high, Wide residue) {
        ++counts.nodes;
        const int size = free.size();
        if (from + left > size ||
            low + (free_lo[size] - free_lo[size-left]) > upper ||
            high + (free_hi[from+left] - free_hi[from]) < lower) return;
        if (left == 0) {
            if (residue == 0) check({});
            return;
        }
        if (left <= reconstruct_count) {
            reconstruct(from, left, residue, low, high);
            return;
        }
        for (int i = from; i+left <= size; ++i) {
            if (high + (free_hi[i+left] - free_hi[i]) < lower) break;
            const auto& prime = primes[free[i]];
            chosen.push_back(i);
            search_b(i+1, left-1, low + prime.lo, high + prime.hi,
                     sub_mod(residue, residues[i], modulus));
            chosen.pop_back();
        }
    }

    void complete_core(Word prod, Word derivative, Word low, Word high) {
        ++counts.cores;
        const Word a_upper = high + tail_upper;
        if (high < x_lo || low > x_hi) return;

        // The largest attainable complementary reciprocal sum ignores all selected primes.
        int stop = b_count;
        Word omitted = 0;
        for (int index : d_indices) {
            if (index >= stop) break;
            omitted += primes[index].hi;
            ++stop;
        }
        const Word best_b = prefix_hi[stop] - omitted;
        if (Wide(best_b) * a_upper < scale_squared || best_b + a_upper < 2*scale) return;
        while (std::binary_search(d_indices.begin(), d_indices.end(), stop)) ++stop;
        const Word extra = primes[stop].hi;
        lower = scale_squared / a_upper;
        upper = (scale_squared + low - 1) / low;

        ++counts.admissible;
        forced.clear();
        for (int i = 0; i < stop; ++i) {
            if (std::binary_search(d_indices.begin(), d_indices.end(), i)) continue;
            const auto& p = primes[i];
            if (p.value <= forced_limit || best_b + extra - p.hi + a_upper < 2*scale ||
                Wide(best_b + extra - p.hi)*a_upper < scale_squared)
                forced.push_back(i);
        }
        const int left = b_count - static_cast<int>(forced.size());

        d = prod;
        dd = derivative;
        modulus = Wide(d)*d;
        reconstruct_count = 0;
        while (reconstruct_count < left) {
            int next = reconstruct_count + 1;
            if (max_product[next] == 0 ||
                max_derivative[next] > (modulus-1) / 2 / max_product[next]) break;
            reconstruct_count = next;
        }
        if (left && !reconstruct_count) throw std::logic_error("reconstruction bound too weak");
        Wide residue = Wide(d)*inverse_word(dd, d);
        Word forced_lo = 0, forced_hi = 0;
        for (int i : forced) {
            const auto& p = primes[i];
            forced_lo += p.lo;
            forced_hi += p.hi;
            residue = sub_mod(residue, inverse(p, modulus), modulus);
        }
        free.clear();
        free_lo.assign(1, 0);
        free_hi.assign(1, 0);
        residues.clear();
        for (int i = 0; i < static_cast<int>(primes.size()); ++i) {
            if (std::binary_search(d_indices.begin(), d_indices.end(), i) ||
                std::binary_search(forced.begin(), forced.end(), i)) continue;
            const auto& p = primes[i];
            free.push_back(i);
            free_lo.push_back(free_lo.back() + p.lo);
            free_hi.push_back(free_hi.back() + p.hi);
            residues.push_back(inverse(p, modulus));
        }
        search_b(0, left, forced_lo, forced_hi, residue);
    }

    void choose_core(int from, int depth, Word d, Word dd, Word low, Word high) {
        const int left = d_count - depth;
        if (left == 0) {
            complete_core(d, dd, low, high);
            return;
        }
        for (int i = from; i+left <= static_cast<int>(primes.size()); ++i) {
            const auto& p = primes[i];
            if (p.value > rank_caps[59-left] || high + (prefix_hi[i+left]-prefix_hi[i]) < x_lo ||
                largest_union_mass(i, depth) + tail_upper < 2*Word(scale)) break;
            if (low + p.lo > x_hi) continue;
            d_indices[depth] = i;
            auto next_d = Wide(d)*p.value, next_dd = Wide(dd)*p.value+d;
            if (next_d >> 63 || next_dd >> 63) throw std::logic_error("word bound exceeded");
            choose_core(i+1, depth+1, static_cast<Word>(next_d), static_cast<Word>(next_dd),
                        low+p.lo, high+p.hi);
        }
    }

    Counts run(int a, int b, int c) {
        d_indices[0] = a;
        d_indices[1] = b;
        d_indices[2] = c;
        const auto& p = primes[a];
        const auto& q = primes[b];
        const auto& r = primes[c];
        choose_core(c+1, 3, Word(p.value)*q.value*r.value,
                    Word(p.value+q.value)*r.value+Word(p.value)*q.value,
                    p.lo+q.lo+r.lo, p.hi+q.hi+r.hi);
        return counts;
    }
};

int main(int argc, char** argv) {
    static_assert(sizeof(unsigned long) == 8);
    for (unsigned p = 2; p <= small_limit; ++p) {
        bool prime = true;
        for (unsigned q = 2; q*q <= p; ++q) if (p % q == 0) { prime = false; break; }
        if (!prime) continue;
        primes.push_back({p, scale/p, (scale+p-1)/p, std::vector<unsigned>(p)});
        auto& data = primes.back();
        data.inverses[1] = 1;
        for (unsigned i = 2; i < p; ++i)
            data.inverses[i] = p - (p/i * data.inverses[p%i])%p;
        prefix_lo.push_back(prefix_lo.back() + data.lo);
        prefix_hi.push_back(prefix_hi.back() + data.hi);
    }
    if (argc != 3) throw std::invalid_argument("usage: same SHARD SHARDS");
    const int shard = std::stoi(argv[1]), shards = std::stoi(argv[2]);
    if (shards < 1 || shards > 256 || shard < 0 || shard >= shards)
        throw std::invalid_argument("invalid shard");
    mpq_class t = 0;
    const mpq_class tau = mpq_class(1, large_minimum) + mpq_class(1, mpz_class("100000000000000000000"));
    for (int i=0;i<59;++i) {
        mpq_class upper = mpq_class(59-i)/(2-t-tau);
        const mpz_class cap_i = upper.get_num()/upper.get_den();
        rank_caps[i] = std::min<unsigned>(small_limit, static_cast<unsigned>(cap_i.get_ui()));
        t += mpq_class(1, primes[i].value);
    }
    max_product[0] = 1;
    for (int i = 1; i <= b_count; ++i) {
        const unsigned p = rank_caps[59-i];
        if (max_product[i-1] > (~Wide(0))/p ||
            max_derivative[i-1] > (~Wide(0)-max_product[i-1])/p) break;
        max_product[i] = max_product[i-1] * p;
        max_derivative[i] = max_derivative[i-1] * p + max_product[i-1];
    }
    std::vector<int> tasks;
    const int end = static_cast<int>(primes.size());
    for (int c=3; c + d_count - 2 <= end; ++c) {
        if (primes[1].hi + primes[2].hi + (prefix_hi[c + d_count-2] - prefix_hi[c]) < x_lo)
            break;
        tasks.push_back(c);
    }

    #pragma omp parallel for schedule(dynamic, 1)
    for (int i = shard; i < static_cast<int>(tasks.size()); i += shards) {
        const int third = tasks[i];
        const auto result = Branch().run(1,2,third);
        #pragma omp critical
        {
            std::cout << "third=" << primes[third].value << " cores=" << result.cores
                      << " admissible=" << result.admissible << " nodes=" << result.nodes
                      << " reconstructions=" << result.reconstructions << " fractions=" << result.bounded_fractions
                      << " supports=" << result.congruent_supports << " roots=" << result.square_discriminants << '\n';
        }
    }
}
