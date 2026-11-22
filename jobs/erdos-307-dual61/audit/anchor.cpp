#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <gmpxx.h>
#include <iostream>
#include <limits>
#include <numeric>
#include <stdexcept>
#include <vector>

using Word = std::uint64_t;
using Wide = unsigned __int128;
constexpr Word scale = Word(1) << 62;
constexpr Wide scale_squared = Wide(scale) * scale;
constexpr int small_limit = 1190;
constexpr int large_minimum = 2382;
#ifndef SMALL_SIDE
#define SMALL_SIDE 12
#endif
constexpr bool small_even = SMALL_SIDE % 2 == 1;
constexpr int b_count = 60 - SMALL_SIDE;
constexpr int d_count = SMALL_SIDE - 1;
constexpr int forced_limit = 157;
constexpr Word tail_upper = (scale + large_minimum - 1) / large_minimum + 1;

struct Prime {
    unsigned value;
    Word lo, hi;
};

std::vector<Prime> primes;
std::vector<Word> prefix_lo{0}, prefix_hi{0};
std::array<unsigned, 59> rank_caps;
constexpr Word x_lo = (Wide(scale) * 948) / 1000 - 1;
constexpr Word x_hi = (Wide(scale) * 1055 + 999) / 1000;

struct Counts {
    Word cores = 0, admissible = 0, nodes = 0, reconstructions = 0;
    Word bounded_fractions = 0, congruent_supports = 0, square_discriminants = 0;
    std::array<Word, b_count + 1> optional{};
};

mpz_class small_primorial = 1;
std::vector<Word> compulsory_groups;
std::array<mpz_class, b_count+1> upper_product, lower_product, four_cubes;

struct Branch {
    Counts counts;
    std::array<int, d_count> d_indices{};
    std::vector<int> forced, free, chosen;
    std::vector<Word> free_lo, free_hi;
    Word d, dd, lower, upper;
    mpz_class d_squared;
    std::array<mpz_class, b_count+1> K, H;
    mpz_class inv, value, smooth, q, product, derivative, g, rem;
    mpz_class residue, bound, approximation, tmp;
    std::array<mpz_class, 3> errors, denominators;
    bool count_only;

    explicit Branch(bool count) : count_only(count) {
        forced.reserve(b_count);
        chosen.reserve(b_count);
        free.reserve(primes.size());
        free_lo.reserve(primes.size()+1);
        free_hi.reserve(primes.size()+1);
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

    void check(const std::vector<int>& recovered, const mpz_class& tail) {
        mpz_class b = 1, bp = 0;
        auto append = [&](unsigned p) {
            bp = p * bp + b;
            b *= p;
        };
        for (int i : forced) append(primes[i].value);
        for (int i : chosen) append(primes[free[i]].value);
        for (int i : recovered) append(primes[free[i]].value);
        if (tail <= 2381 || !mpz_divisible_ui_p((mpz_class(tail * bp + b)).get_mpz_t(), d)) return;
        const mpz_class large = (tail * bp + b) / d;
        if (large <= 2381 || large == tail || tail * b != d + dd * large) return;

        ++counts.congruent_supports;
        #pragma omp critical
        {
            std::cout << "CANDIDATE D=";
            for (int i : d_indices) std::cout << primes[i].value << ',';
            std::cout << " p=" << large << " q=" << tail << " B=";
            for (int i : forced) std::cout << primes[i].value << ',';
            for (int i : chosen) std::cout << primes[free[i]].value << ',';
            for (int i : recovered) std::cout << primes[free[i]].value << ',';
            std::cout << '\n' << std::flush;
        }
    }

    bool factors(const mpz_class& v, int from, int left, std::vector<int>& recovered) {
        if (v < lower_product[left] || v > upper_product[left]) return false;
        g = v;
        for (int i = from; i < static_cast<int>(free.size()); ++i) {
            if (g == 1) break;
            const unsigned p = primes[free[i]].value;
            if (!mpz_divisible_ui_p(g.get_mpz_t(),p)) continue;
            if (static_cast<int>(recovered.size()) == left) return false;
            g /= p;
            recovered.push_back(i);
        }
        return g == 1 && static_cast<int>(recovered.size()) == left;
    }

    void reconstruct(int from, int left, const mpz_class& h, const mpz_class& k) {
        ++counts.reconstructions;
        // If E < K, the linear congruence determines E exactly.
        if (!mpz_invert(inv.get_mpz_t(), h.get_mpz_t(), k.get_mpz_t()))
            throw std::logic_error("noninvertible anchor");
        value = d_squared * inv % k;
        std::vector<int> recovered;
        if (value > 2381) {
            mpz_gcd(smooth.get_mpz_t(), value.get_mpz_t(), small_primorial.get_mpz_t());
            q = value / smooth;
            if (q > 2381 && factors(smooth,from,left,recovered))
                check(recovered,q);
        }

        // If E >= K, V's reciprocal sum has a unique bounded approximation.
        const mpz_class& U = upper_product[left];
        mpz_cdiv_q(bound.get_mpz_t(), d_squared.get_mpz_t(), k.get_mpz_t());
        bound = U * (U + bound);
        errors[0] = h;
        errors[1] = k;
        denominators[0] = 1;
        denominators[1] = 0;
        bool positive = true;
        for (int i=0, j=1, l=2; errors[j]>0;) {
            mpz_tdiv_qr(tmp.get_mpz_t(), errors[l].get_mpz_t(),
                        errors[i].get_mpz_t(), errors[j].get_mpz_t());
            denominators[l] = denominators[i];
            mpz_addmul(denominators[l].get_mpz_t(), tmp.get_mpz_t(), denominators[j].get_mpz_t());
            const mpz_class& v = denominators[l];
            const mpz_class& error = errors[l];
            if (v > U || error == 0) break;
            if (positive && error <= bound) {
                ++counts.bounded_fractions;
                recovered.clear();
                if (!factors(v,from,left,recovered)) break;
                derivative = 0;
                for (int a : recovered) derivative += v / primes[free[a]].value;
                approximation = v * h - derivative * k;
                if (approximation != error) break;
                product = k * v + d_squared;
                if (!mpz_divisible_p(product.get_mpz_t(), error.get_mpz_t())) break;
                q = product / error;
                if (q * v >= k) check(recovered,q);
                break;
            }
            positive = !positive;
            const int old = i;
            i = j;
            j = l;
            l = old;
        }
    }

    void search_b(int from, int left, Word low, Word high, int depth) {
        ++counts.nodes;
        const int size = static_cast<int>(free.size());
        if (from + left > size || low + (free_lo[size] - free_lo[size-left]) > upper ||
            high + (free_hi[from+left] - free_hi[from]) < lower || H[depth] <= 0) return;
        const auto& k = K[depth];
        if (k > four_cubes[left] && k > d_squared) {
            reconstruct(from,left,H[depth],k);
            return;
        }
        if (left == 0) {
            product = K[depth] + d_squared;
            if (mpz_divisible_p(product.get_mpz_t(), H[depth].get_mpz_t())) {
                q = product/H[depth];
                check({},q);
            }
            return;
        }
        for (int i = from; i+left <= size; ++i) {
            if (high + (free_hi[i+left] - free_hi[i]) < lower) break;
            const auto& p = primes[free[i]];
            chosen.push_back(i);
            K[depth+1] = p.value * k;
            H[depth+1] = p.value * H[depth] - k;
            search_b(i+1, left-1, low + p.lo, high + p.hi, depth+1);
            chosen.pop_back();
        }
    }

    void complete_core(Word prod, Word df, Word low, Word high) {
        ++counts.cores;
        if (high < x_lo || low > x_hi) return;
        for (Word group : compulsory_groups) if (std::gcd(df,group) != 1) return;
        const Word a_upper = high + 1;

        // Best possible smooth portion of the opposite side, independent of the unknown tail.
        int stop = b_count;
        Word omitted = 0;
        for (int index : d_indices) {
            if (index >= stop) break;
            omitted += primes[index].hi;
            ++stop;
        }
        const Word best_b = prefix_hi[stop] - omitted;
        if (Wide(best_b + tail_upper) * a_upper < scale_squared || best_b + high + tail_upper < 2*scale) return;
        while (std::binary_search(d_indices.begin(), d_indices.end(), stop)) ++stop;
        const Word extra = primes[stop].hi;
        lower = std::max(Word(scale_squared / a_upper) - tail_upper, 2*scale - high - tail_upper);
        upper = (scale_squared + low - 1) / low;

        forced.clear();
        for (int i = 0; i < stop; ++i) {
            if (std::binary_search(d_indices.begin(), d_indices.end(), i)) continue;
            const auto& p = primes[i];
            const Word alternative = best_b + extra - p.hi;
            if (p.value <= forced_limit || alternative < lower ||
                Wide(alternative + tail_upper)*a_upper < scale_squared) {
                if (df % p.value == 0) return;
                forced.push_back(i);
            }
        }
        const int left = b_count - static_cast<int>(forced.size());
        if (left < 0) throw std::logic_error("too many forced primes");
        ++counts.admissible;
        ++counts.optional[left];
        if (count_only) return;

        d = prod;
        dd = df;
        d_squared = mpz_class(d)*d;
        K[0] = dd;
        H[0] = d;
        Word forced_lo = 0, forced_hi = 0;
        for (int i : forced) {
            const auto& p = primes[i];
            forced_lo += p.lo;
            forced_hi += p.hi;
            H[0] = p.value*H[0] - K[0];
            K[0] *= p.value;
        }
        free.clear();
        free_lo.assign(1, 0);
        free_hi.assign(1, 0);
        for (int i = 0; i < static_cast<int>(primes.size()); ++i) {
            if (std::binary_search(d_indices.begin(), d_indices.end(), i) ||
                std::binary_search(forced.begin(), forced.end(), i)) continue;
            const auto& p = primes[i];
            if (df % p.value == 0) continue;
            free.push_back(i);
            free_lo.push_back(free_lo.back() + p.lo);
            free_hi.push_back(free_hi.back() + p.hi);
        }
        search_b(0, left, forced_lo, forced_hi, 0);
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
        primes.push_back({p, scale/p, (scale+p-1)/p});
        prefix_lo.push_back(prefix_lo.back() + primes.back().lo);
        prefix_hi.push_back(prefix_hi.back() + primes.back().hi);
        small_primorial *= p;
        if (p <= forced_limit) {
            if (compulsory_groups.empty() || compulsory_groups.back() > std::numeric_limits<Word>::max()/p)
                compulsory_groups.push_back(1);
            compulsory_groups.back() *= p;
        }
    }
    if (argc != 5) throw std::invalid_argument("usage: opposite count|solve shard shards third-prime-cap");
    const std::string mode = argv[1];
    if (mode != "count" && mode != "solve") throw std::invalid_argument("invalid mode");
    const int shard = std::stoi(argv[2]), shards = std::stoi(argv[3]);
    const unsigned cap = std::stoul(argv[4]);
    if (shard < 0 || shard >= shards) throw std::invalid_argument("invalid shard");
    mpq_class t = 0;
    const mpq_class tau = mpq_class(1, large_minimum) + mpq_class(1, mpz_class("100000000000000000000"));
    for (int i=0;i<59;++i) {
        mpq_class upper = mpq_class(59-i)/(2-t-tau);
        const mpz_class cap_i = upper.get_num()/upper.get_den();
        rank_caps[i] = std::min<unsigned>(small_limit, static_cast<unsigned>(cap_i.get_ui()));
        t += mpq_class(1, primes[i].value);
    }
    upper_product[0] = 1;
    lower_product[0] = 1;
    for (int i=0;i<=b_count;++i) {
        if (i>0) {
            upper_product[i] = upper_product[i-1]*rank_caps[59-i];
            lower_product[i] = lower_product[i-1]*primes[i-1].value;
        }
        four_cubes[i] = 4*upper_product[i]*upper_product[i]*upper_product[i];
    }
    const auto begin = std::chrono::steady_clock::now();
    std::vector<std::array<int,3>> tasks;
    int index = 0;
    for (int a = small_even ? 0 : 1; a <= (small_even ? 0 : 1); ++a) {
        for (int b = a+1; b <= (small_even ? 10 : 2); ++b) {
            for (int c = b+1; c+d_count-2 <= static_cast<int>(primes.size()); ++c) {
                if (primes[c].value>cap || primes[a].hi+primes[b].hi+
                    (prefix_hi[c+d_count-2]-prefix_hi[c]) < x_lo) break;
                if (index++%shards==shard) tasks.push_back({a,b,c});
            }
        }
    }
    std::cout << "tasks=" << tasks.size() << " shard=" << shard << " shards=" << shards << '\n' << std::flush;
    #pragma omp parallel for schedule(dynamic, 1)
    for (int i = 0; i < static_cast<int>(tasks.size()); ++i) {
        const auto [j,k,l] = tasks[i];
        const auto started = std::chrono::steady_clock::now();
        const auto result = Branch(mode=="count").run(j,k,l);
        const double seconds = std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count();
        #pragma omp critical
        {
            std::cout << "first_odd=" << primes[j].value << " second_odd=" << primes[k].value << " third=" << primes[l].value << " cores=" << result.cores
                      << " admissible=" << result.admissible << " nodes=" << result.nodes
                      << " reconstructions=" << result.reconstructions << " fractions=" << result.bounded_fractions
                      << " supports=" << result.congruent_supports << " roots=" << result.square_discriminants
                      << " seconds=" << seconds << " optional=";
            for (int i = 0; i <= b_count; ++i) if (result.optional[i]) std::cout << i << ':' << result.optional[i] << ',';
            std::cout << '\n' << std::flush;
        }
    }
    std::cout << "wall_seconds=" << std::chrono::duration<double>(std::chrono::steady_clock::now()-begin).count() << '\n';
}
