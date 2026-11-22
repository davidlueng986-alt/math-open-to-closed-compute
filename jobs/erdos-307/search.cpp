#include <algorithm>
#include <atomic>
#include <chrono>
#include <cstdint>
#include <gmpxx.h>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <string>
#include <vector>

using Word = std::uint64_t;
using Clock = std::chrono::steady_clock;
constexpr Word scale = Word{1} << 62;

std::vector<int> primes_up_to(int limit) {
    std::vector<bool> composite(limit + 1);
    std::vector<int> primes;
    for (int p = 2; p <= limit; ++p) {
        if (composite[p]) continue;
        primes.push_back(p);
        if (p <= limit / p) {
            for (int j = p * p; j <= limit; j += p) composite[j] = true;
        }
    }
    return primes;
}

template <typename Integer>
void json_array(std::ostream& output, const std::vector<Integer>& values) {
    output << '[';
    for (std::size_t i = 0; i < values.size(); ++i) {
        if (i) output << ',';
        output << values[i];
    }
    output << ']';
}

struct Counts {
    Word nodes = 0, suffix_queries = 0, signature_hits = 0, exact_tests = 0, square_hits = 0;

    Counts& operator+=(const Counts& other) {
        nodes += other.nodes;
        suffix_queries += other.suffix_queries;
        signature_hits += other.signature_hits;
        exact_tests += other.exact_tests;
        square_hits += other.square_hits;
        return *this;
    }
};

struct Triple {
    std::uint16_t first, middle, last;
};

struct Domain {
    const int size;
    std::vector<int> fixed, pool;
    std::vector<Word> weights, prefix{0};
    std::vector<unsigned> signatures, offsets;
    std::vector<Triple> triples;
    unsigned goal = 0;
    Word fixed_weight = 0;
    mpz_class fixed_product = 1, fixed_derivative = 0;

    Domain(int count, int cap) : size(count) {
        const auto primes = primes_up_to(std::max(cap, 1000));
        mpq_class mass = 0;
        for (int i = 0; i <= count; ++i) mass += mpq_class(1, primes.at(i));
        for (int p : primes) {
            if (mass - mpq_class(1, p) < 2) fixed.push_back(p);
            else break;
        }
        if (fixed.empty() || fixed.front() != 2 || fixed.size() > 23)
            throw std::logic_error("unsupported number of compulsory primes");
        for (int p : fixed) {
            fixed_weight += (scale + p - 1) / p;
            fixed_derivative = p * fixed_derivative + fixed_product;
            fixed_product *= p;
        }
        for (int p : primes) {
            if (p <= fixed.back()) continue;
            if (p > cap) break;
            pool.push_back(p);
            weights.push_back((scale + p - 1) / p);
            prefix.push_back(prefix.back() + weights.back());
        }
        signatures.resize(pool.size());
        for (unsigned bit = 0; bit + 1 < fixed.size(); ++bit) {
            const unsigned r = fixed[bit + 1];
            std::vector<bool> square(r);
            for (unsigned i = 0; i < r; ++i) square[i * i % r] = true;
            unsigned cofactor = 1;
            for (unsigned p : fixed) if (p != r) cofactor = cofactor * p % r;
            if (!square[cofactor]) goal |= 1U << bit;
            for (std::size_t i = 0; i < pool.size(); ++i) {
                if (!square[pool[i] % r]) signatures[i] |= 1U << bit;
            }
        }
        // The odd units modulo 8 are a two-bit XOR group under multiplication.
        int fixed_odd = 1;
        for (int p : fixed) if (p != 2) fixed_odd = fixed_odd * p % 8;
        constexpr int allowed_odd_product[] = {7, 5, 3, 1};
        const unsigned shift = static_cast<unsigned>(fixed.size()) - 1;
        goal |= unsigned((allowed_odd_product[size % 4] * fixed_odd % 8) / 2) << shift;
        for (std::size_t i = 0; i < pool.size(); ++i) signatures[i] |= unsigned((pool[i] % 8) / 2) << shift;
        build_suffix_index(1U << (shift + 2));
    }

    template <typename Callback>
    void for_triples(const Callback& callback) {
        for (unsigned a = 0; a < pool.size(); ++a) {
            for (unsigned b = a + 1; b < pool.size(); ++b) {
                const unsigned base = signatures[a] ^ signatures[b];
                for (unsigned c = b + 1; c < pool.size(); ++c) callback(base ^ signatures[c], a, b, c);
            }
        }
    }

    void build_suffix_index(unsigned keys) {
        offsets.resize(keys + 1);
        for_triples([&](unsigned key, unsigned, unsigned, unsigned) { ++offsets[key + 1]; });
        std::partial_sum(offsets.begin(), offsets.end(), offsets.begin());
        triples.resize(offsets.back());
        auto insertion = offsets;
        for_triples([&](unsigned key, unsigned a, unsigned b, unsigned c) {
            triples[insertion[key]++] = {std::uint16_t(a), std::uint16_t(b), std::uint16_t(c)};
        });
    }
};

struct Work {
    const Domain& domain;
    const int top;
    const Clock::time_point deadline;
    std::atomic<bool>& stop;
    Counts counts;
    std::vector<int> chosen, p, q;
    bool finished = true;

    Work(const Domain& input, int top_index, Clock::time_point end, std::atomic<bool>& halted)
        : domain(input), top(top_index), deadline(end), stop(halted) {
        chosen.reserve(domain.size);
    }

    void check(const Triple& tail) {
        ++counts.signature_hits;
        mpz_class product = domain.fixed_product, derivative = domain.fixed_derivative;
        auto append = [&](int prime) {
            derivative = prime * derivative + product;
            product *= prime;
        };
        for (int i : chosen) append(domain.pool[i]);
        for (int i : {tail.first, tail.middle, tail.last, std::uint16_t(top)}) append(domain.pool[i]);
        if (derivative <= 2 * product) return;
        ++counts.exact_tests;
        const mpz_class plus = derivative + 2 * product;
        const mpz_class minus = derivative - 2 * product;
        if (!mpz_perfect_square_p(plus.get_mpz_t()) || !mpz_perfect_square_p(minus.get_mpz_t())) return;
        ++counts.square_hits;

        mpz_class x, y;
        mpz_sqrt(x.get_mpz_t(), plus.get_mpz_t());
        mpz_sqrt(y.get_mpz_t(), minus.get_mpz_t());
        if (mpz_even_p(x.get_mpz_t()) != mpz_even_p(y.get_mpz_t())) return;
        const mpz_class a = (x - y) / 2, b = (x + y) / 2;
        if (a <= 1 || b <= 1 || a * b != product) return;

        mpz_class a_prime = 0, b_prime = 0;
        auto assign = [&](int prime) {
            if (mpz_divisible_ui_p(a.get_mpz_t(), prime)) {
                a_prime += a / prime;
                p.push_back(prime);
            } else {
                b_prime += b / prime;
                q.push_back(prime);
            }
        };
        for (int prime : domain.fixed) assign(prime);
        for (int i : chosen) assign(domain.pool[i]);
        for (int i : {tail.first, tail.middle, tail.last, std::uint16_t(top)}) assign(domain.pool[i]);
        if (a_prime == b && b_prime == a) {
            stop.store(true, std::memory_order_relaxed);
        } else {
            p.clear();
            q.clear();
        }
    }

    void visit(int from, int left, Word weight, unsigned signature) {
        if (!finished || !p.empty()) return;
        if ((counts.nodes++ & 8191) == 0 && (Clock::now() >= deadline || stop.load(std::memory_order_relaxed))) {
            finished = false;
            return;
        }
        if (from + left > top || weight + (domain.prefix[from + left] - domain.prefix[from]) < 2 * scale) return;
        if (left == 3) {
            ++counts.suffix_queries;
            const auto key = domain.goal ^ signature;
            const auto begin = domain.triples.begin() + domain.offsets[key];
            const auto end = domain.triples.begin() + domain.offsets[key + 1];
            auto triple = std::lower_bound(begin, end, from, [](const Triple& tr, int start) { return tr.first < start; });
            for (; triple != end && triple->first + 2 < top; ++triple) {
                if (triple->last >= top) continue;
                const auto mass = weight + domain.weights[triple->first]
                    + domain.weights[triple->middle] + domain.weights[triple->last];
                if (mass >= 2 * scale) check(*triple);
                if (!p.empty()) return;
            }
            return;
        }
        for (int i = from; i + left <= top; ++i) {
            if (weight + (domain.prefix[i + left] - domain.prefix[i]) < 2 * scale) break;
            chosen.push_back(i);
            visit(i + 1, left - 1, weight + domain.weights[i], signature ^ domain.signatures[i]);
            chosen.pop_back();
            if (!finished || !p.empty()) break;
        }
    }
};

int main(int argc, char** argv) {
    if (argc != 7) throw std::invalid_argument("usage: search SIZE MIN_MAX_PRIME MAX_PRIME SHARD SHARDS SECONDS");
    const int size = std::stoi(argv[1]), lo = std::stoi(argv[2]), hi = std::stoi(argv[3]);
    const int shard = std::stoi(argv[4]), shards = std::stoi(argv[5]), seconds = std::stoi(argv[6]);
    if (size < 61 || size > 90 || lo < 2 || hi < lo || hi > 2381 || shards < 1 || shard < 0 || shard >= shards
        || seconds < 1 || seconds > 20'400) throw std::invalid_argument("invalid search domain or budget");

    const auto start = Clock::now(), deadline = start + std::chrono::seconds(seconds);
    const Domain domain(size, hi);
    const int first = std::max(int(std::lower_bound(domain.pool.begin(), domain.pool.end(), lo) - domain.pool.begin()),
                               size - int(domain.fixed.size()) - 1);
    const int left = size - int(domain.fixed.size()) - 1;
    std::vector<int> assigned;
    for (int i = first + shard; i < static_cast<int>(domain.pool.size()); i += shards) assigned.push_back(i);
    std::vector<bool> finished(assigned.size());
    std::vector<int> found_p, found_q;
    std::atomic<bool> stop(false);
    Counts counts;

    #pragma omp parallel for schedule(dynamic, 1)
    for (int i = 0; i < static_cast<int>(assigned.size()); ++i) {
        const int top = assigned[i];
        Work worker(domain, top, deadline, stop);
        worker.visit(0, left, domain.fixed_weight + domain.weights[top], domain.signatures[top]);
        #pragma omp critical
        {
            counts += worker.counts;
            finished[i] = worker.finished && worker.p.empty();
            if (!worker.p.empty() && found_p.empty()) {
                found_p = std::move(worker.p);
                found_q = std::move(worker.q);
            }
        }
    }

    std::vector<int> completed, pending;
    for (unsigned i = 0; i < assigned.size(); ++i) {
        (finished[i] ? completed : pending).push_back(domain.pool[assigned[i]]);
    }
    std::cout << "{\"size\":" << size << ",\"min_max_prime\":" << lo << ",\"max_prime\":" << hi
              << ",\"shard\":" << shard << ",\"shards\":" << shards << ",\"completed_max_primes\":";
    json_array(std::cout, completed);
    std::cout << ",\"pending_max_primes\":";
    json_array(std::cout, pending);
    std::cout << ",\"nodes\":" << counts.nodes << ",\"suffix_queries\":" << counts.suffix_queries
              << ",\"signature_hits\":" << counts.signature_hits << ",\"exact_tests\":" << counts.exact_tests
              << ",\"square_hits\":" << counts.square_hits
              << ",\"seconds\":" << std::chrono::duration<double>(Clock::now() - start).count();
    if (!found_p.empty()) {
        std::cout << ",\"witness\":{\"P\":";
        json_array(std::cout, found_p);
        std::cout << ",\"Q\":";
        json_array(std::cout, found_q);
        std::cout << '}';
    }
    std::cout << "}\n";
}
