#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <gmpxx.h>
#include <iostream>
#include <stdexcept>
#include <vector>

using Word = std::uint64_t;
constexpr Word scale = Word{1} << 62;
constexpr int core_size = 60;
constexpr int cutoff = 2381;

struct Input {
    const mpz_class height;
    const mpz_class twice_height_cubed;
    const mpz_class deficit_denominator = mpz_class("1000000000000000000000000000000");
    std::vector<unsigned> primes;
    std::vector<Word> weights, prefix{0};
    int fixed = 0;

    Input(const char* height_arg, int cap)
        : height(height_arg), twice_height_cubed(2 * height * height * height) {
        for (unsigned p = 2; p <= static_cast<unsigned>(cap); ++p) {
            bool prime = true;
            for (unsigned d = 2; d <= p / d; ++d) if (p % d == 0) { prime = false; break; }
            if (!prime) continue;
            primes.push_back(p);
            weights.push_back((scale + p - 1) / p);
            prefix.push_back(prefix.back() + weights.back());
            if (p <= 103) ++fixed;
        }
    }
};

struct Counts {
    Word supports = 0, reciprocity_kills = 0, mass_kills = 0, uncovered = 0;
    Word reconstructed = 0, derivative_matches = 0, composite_tails = 0, candidates = 0;

    Counts& operator+=(const Counts& o) {
        supports += o.supports;
        reciprocity_kills += o.reciprocity_kills;
        mass_kills += o.mass_kills;
        uncovered += o.uncovered;
        reconstructed += o.reconstructed;
        derivative_matches += o.derivative_matches;
        composite_tails += o.composite_tails;
        candidates += o.candidates;
        return *this;
    }
};

struct State {
    mpz_class product = 1, derivative = 0;
    unsigned three_mod_four = 0;
};

void extend(State& result, const State& from, unsigned p) {
    mpz_mul_ui(result.product.get_mpz_t(), from.product.get_mpz_t(), p);
    mpz_mul_ui(result.derivative.get_mpz_t(), from.derivative.get_mpz_t(), p);
    result.derivative += from.product;
    result.three_mod_four = from.three_mod_four + (p % 4 == 3);
}

struct Search {
    const Input& input;
    std::array<State, core_size + 1> states;
    std::array<unsigned, core_size> support{};
    std::array<mpz_class, 3> remainders, denominators;
    mpz_class twice_d, delta, root, limit, quotient, numerator;
    Counts counts;
    int top = 0;

    explicit Search(const Input& in) : input(in) {
        for (int i = 0; i < input.fixed; ++i) {
            support[i] = input.primes[i];
            extend(states[i + 1], states[i], support[i]);
        }
    }

    void check_fraction(const State& state, const mpz_class& d, const mpz_class& d_prime) {
        if (d <= 1 || d > input.height || !mpz_divisible_p(state.product.get_mpz_t(), d.get_mpz_t())) return;
        const mpz_class& D = state.product;
        const mpz_class& C = state.derivative;
        const mpz_class d_squared = d * d;
        if (D * (d_squared + d_prime * d_prime) - C * d * d_prime != d_squared * d_squared) return;

        mpz_class actual_derivative = 0;
        std::vector<unsigned> p, q;
        for (unsigned r : support) {
            if (!mpz_divisible_ui_p(d.get_mpz_t(), r)) {
                q.push_back(r);
            } else {
                p.push_back(r);
                actual_derivative += d / r;
            }
        }
        const bool even_side = mpz_even_p(d.get_mpz_t());
        const auto n = p.size();
        if (actual_derivative != d_prime || (even_side ? n != 10 && n != 12 : n != 11 && n != 13)) return;
        const mpz_class b = D / d, tail_numerator = b - d;
        if (tail_numerator <= 0 || !mpz_divisible_p(tail_numerator.get_mpz_t(), d_prime.get_mpz_t())) return;
        const mpz_class tail = tail_numerator / d_prime;
        const mpz_class a = d * tail;
        mpz_class b_prime = 0;
        for (unsigned r : q) b_prime += b / r;
        if (tail <= cutoff || b_prime != a) return;
        ++counts.derivative_matches;
        if (!mpz_probab_prime_p(tail.get_mpz_t(), 32)) {
            ++counts.composite_tails;
            return;
        }
        ++counts.candidates;
        #pragma omp critical
        {
            std::cerr << "CANDIDATE p=" << tail << " small_same_side=";
            for (unsigned r : p) std::cerr << r << ',';
            std::cerr << " other_side=";
            for (unsigned r : q) std::cerr << r << ',';
            std::cerr << '\n' << std::flush;
        }
    }

    void examine(const State& state) {
        ++counts.supports;
        const unsigned residue = state.three_mod_four % 4;
        // For 60 core primes the two square conditions require this Jacobi sign to be positive.
        if (residue == 0 || residue == 3) { ++counts.reciprocity_kills; return; }
        const mpz_class& D = state.product;
        const mpz_class& C = state.derivative;
        twice_d = 2 * D;
        delta = C - twice_d;
        if (delta <= 0) {
            if ((-delta) * input.deficit_denominator >= D) ++counts.mass_kills;
            else ++counts.uncovered;
            return;
        }
        root = C + twice_d;
        delta *= root;
        mpz_sqrt(root.get_mpz_t(), delta.get_mpz_t());
        limit = twice_d * input.twice_height_cubed;
        mpz_cdiv_q(limit.get_mpz_t(), limit.get_mpz_t(), root.get_mpz_t());
        limit += input.height;
        if (2 * input.height * limit >= twice_d) { ++counts.uncovered; return; }

        numerator = C + root;
        remainders[0] = numerator;
        remainders[1] = twice_d;
        denominators[0] = 1;
        denominators[1] = 0;
        for (int i = 0, j = 1, k = 2; remainders[j] > 0;) {
            mpz_tdiv_qr(quotient.get_mpz_t(), remainders[k].get_mpz_t(),
                        remainders[i].get_mpz_t(), remainders[j].get_mpz_t());
            denominators[k] = denominators[i];
            mpz_addmul(denominators[k].get_mpz_t(), quotient.get_mpz_t(), denominators[j].get_mpz_t());
            const auto& q = denominators[k];
            if (q > input.height) return;
            const auto& error = remainders[k];
            if (error <= limit) {
                ++counts.reconstructed;
                // Exactly one sign makes this quotient integral for the current convergent.
                mpz_class m = numerator * q;
                if (mpz_divisible_p((mpz_class(m - error)).get_mpz_t(), twice_d.get_mpz_t())) m -= error;
                else m += error;
                m /= twice_d;
                check_fraction(state, q, m);
                if (m != q) check_fraction(state, m, q);
                return;
            }
            const int old = i;
            i = j;
            j = k;
            k = old;
        }
    }

    void visit(int from, int left, Word mass) {
        const int depth = core_size - 1 - left;
        if (left == 0) {
            support[depth] = input.primes[top];
            extend(states[depth + 1], states[depth], support[depth]);
            examine(states[depth + 1]);
            return;
        }
        for (int i = from; i + left <= top; ++i) {
            if (mass + (input.prefix[i + left] - input.prefix[i]) < 2 * scale) break;
            support[depth] = input.primes[i];
            extend(states[depth + 1], states[depth], support[depth]);
            visit(i + 1, left - 1, mass + input.weights[i]);
        }
    }
};

int main(int argc, char** argv) {
    if (argc != 5) throw std::invalid_argument("usage: search HEIGHT CAP SHARD SHARDS");
    const int cap = std::stoi(argv[2]), shard = std::stoi(argv[3]), shards = std::stoi(argv[4]);
    if (cap < 281 || cap > cutoff || shard < 0 || shard >= shards || shards > 256)
        throw std::invalid_argument("invalid cap or shard");
    const Input input(argv[1], cap);
    if (input.height <= 0) throw std::invalid_argument("height must be positive");
    const auto start = std::chrono::steady_clock::now();
    const int end = static_cast<int>(input.primes.size());
    Counts total;
    #pragma omp parallel
    {
        Search search(input);
        #pragma omp for schedule(dynamic, 1)
        for (int top = core_size - 1 + shard; top < end; top += shards) {
            search.top = top;
            search.visit(input.fixed, core_size - 1 - input.fixed, input.prefix[input.fixed] + input.weights[top]);
        }
        #pragma omp critical
        total += search.counts;
    }
    std::cout << "{\"supports\":" << total.supports
              << ",\"reciprocity_kills\":" << total.reciprocity_kills
              << ",\"mass_kills\":" << total.mass_kills
              << ",\"uncovered\":" << total.uncovered
              << ",\"reconstructed\":" << total.reconstructed
              << ",\"derivative_matches\":" << total.derivative_matches
              << ",\"composite_tails\":" << total.composite_tails
              << ",\"candidates\":" << total.candidates
              << ",\"seconds\":" << std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count()
              << "}\n";
}
