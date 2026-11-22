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
constexpr Word scale = Word{1} << 62;
constexpr int core_size = 59, small_size = 11;
constexpr unsigned cutoff = 2381, boundary = 5'000'000;
constexpr Word rounded_tail_mass = (scale + boundary) / (boundary + 1) + 1;
constexpr Word mass_error = (2 * scale + boundary) / (boundary + 1) + small_size + 2;
constexpr Word height = 443759330344295771;
constexpr unsigned small_prime_cap = 1190, large_prime_cap = 794;
constexpr unsigned small_forced = 157, large_forced = 167;

struct Prime {
    unsigned value;
    Word low, high;
};

std::vector<Prime> primes;
std::vector<Word> prefix{0}, mandatory_products;
std::array<unsigned, core_size> rank_cap;

struct State {
    mpz_class D = 1, C = 0;
};

void append(State& out, const State& in, unsigned p) {
    mpz_mul_ui(out.D.get_mpz_t(), in.D.get_mpz_t(), p);
    mpz_mul_ui(out.C.get_mpz_t(), in.C.get_mpz_t(), p);
    out.C += in.D;
}

struct Counts {
    Word cores = 0, convergents = 0, fourth_powers = 0, d_cores = 0, coprime_cores = 0;
    Word pairs = 0, contained = 0, opposite_candidates = 0;

    Counts& operator+=(const Counts& o) {
        cores += o.cores;
        convergents += o.convergents;
        fourth_powers += o.fourth_powers;
        d_cores += o.d_cores;
        coprime_cores += o.coprime_cores;
        pairs += o.pairs;
        contained += o.contained;
        opposite_candidates += o.opposite_candidates;
        return *this;
    }
};

void check(const State& core, const mpz_class& d, const mpz_class& f, const mpz_class& q,
           const std::array<unsigned, core_size>& support, Counts& counts) {
    if (d <= 1 || d > height || mpz_even_p(d.get_mpz_t()) ||
        !mpz_divisible_p(core.D.get_mpz_t(), d.get_mpz_t()) || q <= cutoff) return;
    const mpz_class e = core.D / d;
    mpz_class f_actual = 0, g_actual = 0;
    std::vector<unsigned> a, b;
    for (unsigned r : support) {
        if (mpz_divisible_ui_p(d.get_mpz_t(), r)) {
            a.push_back(r);
            f_actual += d / r;
        } else {
            b.push_back(r);
            g_actual += e / r;
        }
    }
    if (a.size() != small_size || f_actual != f) return;

    const mpz_class p_numerator = e * q - d;
    if (p_numerator <= 0 || !mpz_divisible_p(p_numerator.get_mpz_t(), f.get_mpz_t())) return;
    const mpz_class p = p_numerator / f;
    if (p <= cutoff || p == q || d * p != q * g_actual + e) return;
    ++counts.opposite_candidates;
    #pragma omp critical
    {
        std::cerr << "CANDIDATE p=" << p << " q=" << q << " A_small=";
        for (unsigned r : a) std::cerr << r << ',';
        std::cerr << " B_small=";
        for (unsigned r : b) std::cerr << r << ',';
        std::cerr << '\n' << std::flush;
    }
}

struct Target {
    Word mass;
    std::array<Word, 3> membership{};
    std::array<unsigned, core_size> support;
    State core;
};

struct Supports {
    const bool small;
    const int fixed;
    const Word threshold;
    const mpz_class H = height, error_cap = H * H * H * H;
    const mpz_class denominator_cap = H * H * 1055 * boundary / 1000;
    std::array<State, core_size + 1> states;
    std::array<unsigned, core_size> picked{};
    std::array<int, core_size> indices{};
    std::array<mpz_class, 3> remainders, denominators;
    mpz_class quotient, base;
    int top = 0;
    Counts counts;
    std::vector<Target> targets;

    Supports(bool small_sector, int fixed_count)
        : small(small_sector), fixed(fixed_count),
          threshold(2 * scale - (small ? (scale + cutoff) / (cutoff + 1) + 1 : rounded_tail_mass)) {
        for (int i = 0; i < fixed; ++i) {
            indices[i] = i;
            picked[i] = primes[i].value;
            append(states[i + 1], states[i], picked[i]);
        }
    }

    void examine(const State& core) {
        ++counts.cores;
        if (!small) {
            Target t;
            t.mass = mpz_class((core.C * scale) / core.D).get_ui();
            t.support = picked;
            t.core = core;
            for (int i : indices) t.membership[i / 64] |= Word{1} << (i % 64);
            targets.push_back(std::move(t));
            return;
        }
        remainders[0] = core.C;
        remainders[1] = core.D;
        denominators[0] = 1;
        denominators[1] = 0;
        bool above = false;
        for (int i = 0, j = 1, k = 2; remainders[j] > 0;) {
            mpz_tdiv_qr(quotient.get_mpz_t(), remainders[k].get_mpz_t(),
                        remainders[i].get_mpz_t(), remainders[j].get_mpz_t());
            denominators[k] = denominators[i];
            mpz_addmul(denominators[k].get_mpz_t(), quotient.get_mpz_t(), denominators[j].get_mpz_t());
            const auto& error = remainders[k];
            const auto& vq = denominators[k];
            if (vq > denominator_cap || error == 0) break;
            if (above && error <= error_cap) {
                ++counts.convergents;
                if (mpz_root(base.get_mpz_t(), error.get_mpz_t(), 4)) {
                    ++counts.fourth_powers;
                    if (base > 1 && mpz_odd_p(base.get_mpz_t()) &&
                        mpz_divisible_p(core.D.get_mpz_t(), base.get_mpz_t())) {
                        mpz_class f = 0;
                        for (unsigned r : picked)
                            if (mpz_divisible_ui_p(base.get_mpz_t(), r)) f += base / r;
                        const mpz_class v = base * f;
                        if (v > 0 && mpz_divisible_p(vq.get_mpz_t(), v.get_mpz_t())) {
                            const mpz_class q = vq / v;
                            if (q <= boundary) check(core, base, f, q, picked, counts);
                        }
                    }
                }
            }
            above = !above;
            const int old = i;
            i = j;
            j = k;
            k = old;
        }
    }

    void visit(int from, int left, Word mass) {
        const int depth = core_size - 1 - left;
        if (left == 0) {
            indices[depth] = top;
            picked[depth] = primes[top].value;
            append(states[depth + 1], states[depth], picked[depth]);
            examine(states[depth + 1]);
            return;
        }
        for (int i = from; i + left <= top; ++i) {
            if (mass + (prefix[i + left] - prefix[i]) < threshold) break;
            indices[depth] = i;
            picked[depth] = primes[i].value;
            append(states[depth + 1], states[depth], picked[depth]);
            visit(i + 1, left - 1, mass + primes[i].high);
        }
    }
};

struct IndexedTargets {
    static constexpr unsigned shift = 35;
    const std::vector<Target>& targets;
    const Word base;
    std::vector<std::size_t> offsets;
    IndexedTargets(const std::vector<Target>& t)
        : targets(t), base(t.front().mass >> shift), offsets((t.back().mass >> shift) - base + 2) {
        std::size_t i = 0;
        for (std::size_t b = 0; b < offsets.size(); ++b) {
            while (i < t.size() && (t[i].mass >> shift) < base + b) ++i;
            offsets[b] = i;
        }
    }
    std::pair<std::size_t, std::size_t> range(Word lo, Word hi) const {
        const Word first = lo >> shift, last = hi >> shift;
        if (last < base || first >= base + offsets.size() - 1) return {0, 0};
        return {offsets[std::max(first, base) - base],
                offsets[std::min(last - base + 1, offsets.size() - 1)]};
    }
};

struct FindLarge {
    const IndexedTargets& index;
    const int end;
    std::array<int, small_size> picked{1, 2};
    Counts counts;

    FindLarge(const IndexedTargets& t, int end_index) : index(t), end(end_index) {}

    Word best_union(int next, int depth) const {
        int included = core_size - small_size;
        Word extra = 0;
        for (int i = 0; i < small_size; ++i) {
            const int selected = i < depth ? picked[i] : next + i - depth;
            if (selected < included) ++included;
            else extra += primes[selected].high;
        }
        return prefix[included] + extra;
    }

    void matches(Word d, Word f, Word mass) {
        ++counts.d_cores;
        for (Word group : mandatory_products) if (std::gcd(f, group) != 1) return;
        ++counts.coprime_cores;
        const Word center = mass + static_cast<Word>((Wide(scale) * scale) / mass);
        const Word lo = center - mass_error, hi = center + small_size + 2;
        const auto [start, stop] = index.range(lo, hi);
        std::array<Word, 3> membership{};
        for (int i : picked) membership[i / 64] |= Word{1} << (i % 64);
        const mpz_class dn(d), fn(f);
        const mpz_class u = dn * dn + fn * fn, v = dn * fn, w = dn * dn * dn * dn;
        for (std::size_t i = start; i < stop; ++i) {
            const auto& t = index.targets[i];
            if (t.mass < lo || t.mass > hi) continue;
            ++counts.pairs;
            if (((membership[0] & ~t.membership[0]) | (membership[1] & ~t.membership[1]) |
                 (membership[2] & ~t.membership[2])) != 0) continue;
            ++counts.contained;
            const State& core = t.core;
            const mpz_class denom = core.D * u - core.C * v, numer = core.D * v + w;
            if (denom <= 0 || !mpz_divisible_p(numer.get_mpz_t(), denom.get_mpz_t())) continue;
            const mpz_class q = numer / denom;
            if (q > boundary) check(core,dn,fn,q,t.support,counts);
        }
    }

    void visit(int from, int depth, Word d, Word f, Word mass) {
        constexpr Word lo = (Wide(scale) * 95) / 100;
        constexpr Word hi = (Wide(scale) * 105 + 99) / 100;
        const int left = small_size - depth;
        if (left == 0) {
            if (mass + small_size >= lo) matches(d, f, mass);
            return;
        }
        for (int i = from; i + left <= end; ++i) {
            const auto& p = primes[i];
            if (p.value > rank_cap[core_size-left] ||
                mass + small_size + (prefix[i + left] - prefix[i]) < lo ||
                best_union(i, depth) + rounded_tail_mass < 2 * scale ||
                Wide(d) * p.value > height) break;
            if (mass + p.low > hi) continue;
            picked[depth] = i;
            visit(i + 1, depth + 1, d * p.value, f * p.value + d, mass + p.low);
        }
    }
};

int main(int argc, char** argv) {
    static_assert(sizeof(unsigned long) == 8);
    if (argc != 3) throw std::invalid_argument("usage: opposite SHARD SHARDS");
    const int shard = std::stoi(argv[1]), shards = std::stoi(argv[2]);
    if (shards < 1 || shards > 256 || shard < 0 || shard >= shards) throw std::invalid_argument("invalid shard");
    int fixed_small = 0, fixed_large = 0, end_large = 0;
    for (unsigned p = 2; p <= small_prime_cap; ++p) {
        bool prime = true;
        for (unsigned d = 2; d <= p / d; ++d) if (p % d == 0) { prime = false; break; }
        if (!prime) continue;
        primes.push_back({p, scale / p, (scale + p - 1) / p});
        prefix.push_back(prefix.back() + primes.back().high);
        if (p <= small_forced) ++fixed_small;
        if (p <= large_prime_cap) ++end_large;
        if (p <= large_forced) {
            ++fixed_large;
            if (mandatory_products.empty() || mandatory_products.back() > std::numeric_limits<Word>::max() / p)
                mandatory_products.push_back(1);
            mandatory_products.back() *= p;
        }
    }
    mpq_class T = 0;
    const mpq_class tau = mpq_class(1, boundary + 1) + mpq_class(1, mpz_class("100000000000000000000"));
    for (int i = 0; i < core_size; ++i) {
        const mpq_class quotient = mpq_class(core_size - i) / (2 - T - tau);
        const mpz_class value = quotient.get_num() / quotient.get_den();
        rank_cap[i] = std::min<unsigned>(large_prime_cap, static_cast<unsigned>(value.get_ui()));
        T += mpq_class(1, primes[i].value);
    }
    const auto start = std::chrono::steady_clock::now();
    const int end_small = static_cast<int>(primes.size());
    Counts first, second, match;
    std::vector<Target> targets;
    std::vector<unsigned> small_maxima;
    for (int top = core_size - 1 + shard; top < end_small; top += shards)
        small_maxima.push_back(primes[top].value);

    #pragma omp parallel
    {
        Supports small(true, fixed_small), large(false, fixed_large);
        #pragma omp for schedule(dynamic, 1) nowait
        for (int top = core_size - 1 + shard; top < end_small; top += shards) {
            small.top = top;
            small.visit(fixed_small, core_size - 1 - fixed_small, prefix[fixed_small] + primes[top].high);
        }
        #pragma omp for schedule(dynamic, 1)
        for (int top = core_size - 1; top < end_large; ++top) {
            large.top = top;
            large.visit(fixed_large, core_size - 1 - fixed_large, prefix[fixed_large] + primes[top].high);
        }
        #pragma omp critical
        {
            first += small.counts;
            second += large.counts;
            targets.insert(targets.end(),large.targets.begin(),large.targets.end());
        }
    }
    if (targets.empty()) throw std::logic_error("missing large-q supports");
    std::sort(targets.begin(), targets.end(), [](const Target& a, const Target& b) { return a.mass < b.mass; });
    IndexedTargets index(targets);
    std::vector<std::array<int, 3>> prefixes;
    for (int a = 3; a < end_large; ++a)
        for (int b = a + 1; b < end_large; ++b)
            for (int c = b + 1; c + small_size - 4 <= end_large; ++c) {
                if (primes[a].value > rank_cap[core_size - small_size + 2] ||
                    primes[b].value > rank_cap[core_size - small_size + 3] ||
                    primes[c].value > rank_cap[core_size - small_size + 4]) break;
                prefixes.push_back({a,b,c});
            }

    #pragma omp parallel
    {
        FindLarge search(index, end_large);
        #pragma omp for schedule(dynamic, 16)
        for (int j = shard; j < static_cast<int>(prefixes.size()); j += shards) {
            const auto& pre = prefixes[j];
            Word d = 15, f = 8, mass = primes[1].low + primes[2].low;
            for (int i = 0; i < 3; ++i) {
                search.picked[i + 2] = pre[i];
                const auto& p = primes[pre[i]];
                f = p.value * f + d;
                d *= p.value;
                mass += p.low;
            }
            if (search.best_union(pre.back() + 1, 5) + rounded_tail_mass >= 2 * scale)
                search.visit(pre.back() + 1, 5, d, f, mass);
        }
        #pragma omp critical
        match += search.counts;
    }
    const double seconds = std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
    std::cout << "{\"small_maxima\":[";
    for (std::size_t i = 0; i < small_maxima.size(); ++i) {
        if (i) std::cout << ',';
        std::cout << small_maxima[i];
    }
    std::cout << "],\"small_q_supports\":" << first.cores << ",\"small_q_convergents\":" << first.convergents
              << ",\"fourth_powers\":" << first.fourth_powers << ",\"large_q_supports\":" << targets.size()
              << ",\"d_cores\":" << match.d_cores << ",\"coprime_cores\":" << match.coprime_cores
              << ",\"pairs\":" << match.pairs << ",\"contained\":" << match.contained
              << ",\"prefixes\":" << prefixes.size()
              << ",\"prefixes_processed\":" << (prefixes.size() + shards - 1 - shard) / shards
              << ",\"opposite_candidates\":" << first.opposite_candidates + match.opposite_candidates
              << ",\"seconds\":" << seconds << "}\n";
}
