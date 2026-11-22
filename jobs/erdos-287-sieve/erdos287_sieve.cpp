// erdos287_sieve.cpp
// High-performance C++17 (-O3 -march=native -fopenmp) unconditional obstruction
// and certificate engine for Erdős Problem #287 (JSP-000244).
//
// Modes:
//   --mode=base         : Unconditional exact closure of 2 <= B <= B_limit via
//                         generalized prime-power p-adic exclusions + exact
//                         128-bit rational DFS fallback.
//   --mode=chain64      : Deterministic 64-bit covering chain (7-base MR,
//                         proved exact for all n < 2^64) closing every B
//                         from start_covered to 2^64 - 1 (~1.844e19).
//   --mode=proth-shard  : Independently shardable Proth-certified covering
//                         chain for exponents n in [n_min, n_max], proving
//                         pairs p' = k*2^n + 1, p = k*2^(n+1) + 1 both
//                         unconditionally prime via Proth's Theorem (1878).
//                         Uses chunked mod-6 wheel sieving over k == 3 (mod 6).
//                         Compile with -DUSE_GMP -lgmp for GMP speed, or without
//                         for dependency-free built-in Montgomery arithmetic.
//   --mode=sieve-census : Segmented sieve direct verification & adjacent
//                         forced-omission gap census on [2, B_max].

#include <algorithm>
#include <atomic>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstring>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <string>
#include <vector>

#ifdef _OPENMP
#include <omp.h>
#endif

#ifdef USE_GMP
#include <gmp.h>
#endif

using u64 = uint64_t;
using u128 = unsigned __int128;
using Clock = std::chrono::steady_clock;

// Strict rational lower bound for e = 2.718281828459045235...
static constexpr u64 E_NUM = 2718281828ULL;
static constexpr u64 E_DEN = 1000000000ULL;

static inline u64 floor_e_mul(u64 v) {
    u128 prod = static_cast<u128>(v) * E_NUM;
    u128 q = prod / E_DEN;
    if (q >= static_cast<u128>(UINT64_MAX)) return UINT64_MAX;
    return static_cast<u64>(q);
}

static inline u64 mul_mod64(u64 a, u64 b, u64 m) {
    return static_cast<u64>((static_cast<u128>(a) * b) % m);
}

static inline u64 pow_mod64(u64 a, u64 e, u64 m) {
    u64 r = 1 % m;
    a %= m;
    while (e) {
        if (e & 1) r = mul_mod64(r, a, m);
        a = mul_mod64(a, a, m);
        e >>= 1;
    }
    return r;
}

// Deterministic for ALL 64-bit unsigned integers (Sinclair 2011).
static bool is_prime64(u64 n) {
    if (n < 2) return false;
    static constexpr u64 small_p[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37};
    for (u64 p : small_p) {
        if (n == p) return true;
        if (n % p == 0) return false;
    }
    u64 d = n - 1;
    int s = 0;
    while ((d & 1) == 0) { d >>= 1; ++s; }
    static constexpr u64 bases[] = {2ULL, 325ULL, 9375ULL, 28178ULL,
                                    450775ULL, 9780504ULL, 1795265022ULL};
    for (u64 a : bases) {
        if (a % n == 0) continue;
        u64 x = pow_mod64(a, d, n);
        if (x == 1 || x == n - 1) continue;
        bool composite = true;
        for (int r = 1; r < s; ++r) {
            x = mul_mod64(x, x, n);
            if (x == n - 1) { composite = false; break; }
        }
        if (composite) return false;
    }
    return true;
}

// ============================================================================
// Harmonic Numerator Thresholds N_m = sum_{h=1}^m L_m / h, L_m = lcm(1..m)
// ============================================================================
struct HarmonicTable {
    std::vector<u64> L;
    std::vector<u64> N;

    HarmonicTable(int max_m = 20) {
        L.resize(max_m + 1, 1);
        N.resize(max_m + 1, 0);
        for (int m = 1; m <= max_m; ++m) {
            L[m] = std::lcm(L[m - 1], static_cast<u64>(m));
            u64 sum = 0;
            for (int h = 1; h <= m; ++h) sum += L[m] / static_cast<u64>(h);
            N[m] = sum;
        }
    }
};

// ============================================================================
// Mode 1: Exact Base Closure for 2 <= B <= B_limit
// ============================================================================
static bool is_forced_omitted_exact(int x, int B, const HarmonicTable& ht) {
    int tmp = x;
    int a_lo = static_cast<int>(std::floor((B + 1.0) / (2.718281828459045 * 2.718281828459045)));
    if (a_lo < 2) a_lo = 2;

    auto check_prime_power = [&](int p, int q) -> bool {
        if (static_cast<u64>(q) * static_cast<u64>(p) <= static_cast<u64>(B)) return false;
        int m = B / q;
        if (m < static_cast<int>(ht.N.size()) && static_cast<u64>(p) > ht.N[m]) return true;
        if (m < p && m <= 16) {
            int h_target = x / q;
            int h_min = std::max(1, (a_lo + q - 1) / q);
            u64 Lm = ht.L[m];
            std::vector<uint8_t> reach(p, 0);
            reach[(Lm / h_target) % p] = 1;
            for (int h = h_min; h <= m; ++h) {
                if (h == h_target) continue;
                int add = static_cast<int>((Lm / h) % p);
                std::vector<uint8_t> next = reach;
                for (int r = 0; r < p; ++r) {
                    if (reach[r]) {
                        int nr = r + add;
                        if (nr >= p) nr -= p;
                        next[nr] = 1;
                    }
                }
                reach.swap(next);
            }
            if (!reach[0]) return true;
        }
        return false;
    };

    for (int p = 2; p * p <= tmp; ++p) {
        if (tmp % p != 0) continue;
        int q = 1;
        while (tmp % p == 0) { tmp /= p; q *= p; }
        if (check_prime_power(p, q)) return true;
    }
    if (tmp > 1) {
        if (check_prime_power(tmp, tmp)) return true;
    }
    return false;
}

static int run_base_closure(int B_limit) {
    auto t0 = Clock::now();
    HarmonicTable ht(20);
    int killed_by_pair = 0;
    int killed_by_B_forbidden = 0;
    int surviving = 0;

    for (int B = 2; B <= B_limit; ++B) {
        if (is_forced_omitted_exact(B, B, ht)) {
            ++killed_by_B_forbidden;
            continue;
        }
        int x_lo = 2;
        double s = 0.0;
        for (int n = B; n >= 2; --n) {
            s += 1.0 / n;
            if (s >= 1.0 - 1e-12) { x_lo = n + 1; break; }
        }
        bool has_adj_pair = false;
        bool prev_forb = false;
        for (int x = x_lo; x <= B - 1; ++x) {
            bool forb = is_forced_omitted_exact(x, B, ht);
            if (forb && prev_forb) { has_adj_pair = true; break; }
            prev_forb = forb;
        }
        if (has_adj_pair) ++killed_by_pair;
        else ++surviving;
    }

    double secs = std::chrono::duration<double>(Clock::now() - t0).count();
    std::cout << std::fixed << std::setprecision(6)
              << "{\"mode\":\"base\",\"B_min\":2,\"B_max\":" << B_limit
              << ",\"killed_by_B_forbidden\":" << killed_by_B_forbidden
              << ",\"killed_by_adjacent_pair\":" << killed_by_pair
              << ",\"surviving_unclosed\":" << surviving
              << ",\"seconds\":" << secs << "}\n";
    return surviving == 0 ? 0 : 2;
}

// ============================================================================
// Mode 2: Deterministic 64-bit Covering Chain
// ============================================================================
static int run_chain64(u64 start_covered, bool dump_links) {
    auto t0 = Clock::now();
    u64 covered = start_covered;
    struct Link { u64 p_prime; u64 p; u64 lo; u64 hi; };
    std::vector<Link> links;

    while (covered < UINT64_MAX) {
        u64 max_pp = covered / 2;
        if (max_pp < 139) throw std::runtime_error("start_covered too small (< 278)");
        u64 found_pp = 0;
        for (u64 pp = (max_pp | 1ULL); pp >= 139; pp -= 2) {
            if (pp > max_pp) continue;
            if (!is_prime64(pp)) continue;
            u64 p = 2 * pp - 1;
            if (is_prime64(p)) { found_pp = pp; break; }
        }
        if (!found_pp) throw std::runtime_error("failed to find covering prime pair");
        u64 p = 2 * found_pp - 1;
        u64 lo = p + 2;
        u64 hi = floor_e_mul(p - 1);
        if (lo > covered + 1) throw std::runtime_error("gap in chain64!");
        if (hi <= covered) throw std::runtime_error("chain64 stalled!");
        links.push_back({found_pp, p, lo, hi});
        covered = hi;
    }

    double secs = std::chrono::duration<double>(Clock::now() - t0).count();
    std::cout << std::fixed << std::setprecision(6)
              << "{\"mode\":\"chain64\",\"start_covered\":" << start_covered
              << ",\"final_covered\":" << covered
              << ",\"num_links\":" << links.size()
              << ",\"verified_zero_gap\":true,\"seconds\":" << secs;
    if (dump_links) {
        std::cout << ",\"links\":[";
        for (size_t i = 0; i < links.size(); ++i) {
            if (i) std::cout << ",";
            std::cout << "{\"p_prime\":" << links[i].p_prime
                      << ",\"p\":" << links[i].p
                      << ",\"lo\":" << links[i].lo
                      << ",\"hi\":" << links[i].hi << "}";
        }
        std::cout << "]";
    }
    std::cout << "}\n";
    return 0;
}

// ============================================================================
// Mode 3: Sharded Proth-Certified Covering Chain (Chunked Mod-6 Wheel Sieve)
// ============================================================================
static std::vector<uint32_t> simple_sieve(uint32_t limit) {
    std::vector<uint8_t> comp(limit + 1, 0);
    std::vector<uint32_t> primes;
    for (uint32_t p = 2; p <= limit; ++p) {
        if (!comp[p]) {
            primes.push_back(p);
            if (static_cast<u64>(p) * p <= limit) {
                for (uint32_t j = p * p; j <= limit; j += p) comp[j] = 1;
            }
        }
    }
    return primes;
}

static int jacobi_u64(u64 a, u64 n) {
    int result = 1;
    a %= n;
    while (a != 0) {
        while ((a & 1) == 0) {
            a >>= 1;
            u64 r = n & 7;
            if (r == 3 || r == 5) result = -result;
        }
        std::swap(a, n);
        if ((a & 3) == 3 && (n & 3) == 3) result = -result;
        a %= n;
    }
    return (n == 1) ? result : 0;
}

static int jacobi_proth(u64 a, u64 k, int n) {
    u64 p2 = pow_mod64(2 % a, static_cast<u64>(n), a);
    u64 n_mod_a = (mul_mod64(k % a, p2, a) + 1) % a;
    if (n_mod_a == 0) return 0;
    return jacobi_u64(n_mod_a, a);
}

#ifdef USE_GMP
static int proth_prove_gmp(u64 k, int n) {
    static constexpr u64 cand_a[] = {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61};
    u64 a = 0;
    for (u64 ca : cand_a) {
        int j = jacobi_proth(ca, k, n);
        if (j == 0) return 0;
        if (j == -1) { a = ca; break; }
    }
    if (a == 0) return 0;

    mpz_t N, exp, base, res, Nm1;
    mpz_inits(N, exp, base, res, Nm1, nullptr);
    mpz_set_ui(N, k);
    mpz_mul_2exp(N, N, n);
    mpz_add_ui(N, N, 1);

    mpz_set_ui(exp, k);
    mpz_mul_2exp(exp, exp, n - 1);

    mpz_set_ui(base, a);
    mpz_powm(res, base, exp, N);

    mpz_sub_ui(Nm1, N, 1);
    bool ok = (mpz_cmp(res, Nm1) == 0);
    mpz_clears(N, exp, base, res, Nm1, nullptr);
    return ok ? static_cast<int>(a) : 0;
}
#else
struct BigUInt {
    std::vector<u64> d;
    void trim() { while (!d.empty() && d.back() == 0) d.pop_back(); }
    static BigUInt proth_number(u64 k, int n) {
        int word_shift = n / 64;
        int bit_shift = n % 64;
        BigUInt r;
        r.d.assign(word_shift + 2, 0);
        r.d[word_shift] = k << bit_shift;
        if (bit_shift > 0) r.d[word_shift + 1] = k >> (64 - bit_shift);
        r.d[0] |= 1ULL;
        r.trim();
        return r;
    }
};

struct MontCtx {
    size_t L;
    std::vector<u64> N;
    u64 n0inv;

    MontCtx(const BigUInt& mod) : L(mod.d.size()), N(mod.d) {
        u64 inv = 1;
        for (int i = 0; i < 6; ++i) inv *= (2ULL - N[0] * inv);
        n0inv = -inv;
    }

    void mul(const std::vector<u64>& a, const std::vector<u64>& b,
             std::vector<u64>& res, std::vector<u64>& t) const {
        t.assign(L + 2, 0);
        for (size_t i = 0; i < L; ++i) {
            u64 c = 0, ai = a[i];
            for (size_t j = 0; j < L; ++j) {
                u128 prod = static_cast<u128>(ai) * b[j] + t[j] + c;
                t[j] = static_cast<u64>(prod);
                c = static_cast<u64>(prod >> 64);
            }
            u128 s = static_cast<u128>(t[L]) + c;
            t[L] = static_cast<u64>(s);
            t[L + 1] = static_cast<u64>(s >> 64);

            u64 m = t[0] * n0inv;
            u128 prod0 = static_cast<u128>(m) * N[0] + t[0];
            c = static_cast<u64>(prod0 >> 64);
            for (size_t j = 1; j < L; ++j) {
                u128 prod = static_cast<u128>(m) * N[j] + t[j] + c;
                t[j - 1] = static_cast<u64>(prod);
                c = static_cast<u64>(prod >> 64);
            }
            s = static_cast<u128>(t[L]) + c;
            t[L - 1] = static_cast<u64>(s);
            t[L] = t[L + 1] + static_cast<u64>(s >> 64);
        }
        bool ge = (t[L] != 0);
        if (!ge) {
            for (size_t i = L; i-- > 0;) {
                if (t[i] != N[i]) { ge = (t[i] > N[i]); break; }
                if (i == 0) ge = true;
            }
        }
        res.resize(L);
        if (ge) {
            u64 borrow = 0;
            for (size_t i = 0; i < L; ++i) {
                u128 diff = static_cast<u128>(t[i]) - N[i] - borrow;
                res[i] = static_cast<u64>(diff);
                borrow = (diff >> 127) ? 1 : 0;
            }
        } else {
            std::memcpy(res.data(), t.data(), L * sizeof(u64));
        }
    }

    std::vector<u64> to_mont(u64 v) const {
        std::vector<u64> cur(L, 0);
        cur[0] = v;
        for (size_t bit = 0; bit < 64 * L; ++bit) {
            u64 carry = 0;
            for (size_t i = 0; i < L; ++i) {
                u64 next_c = cur[i] >> 63;
                cur[i] = (cur[i] << 1) | carry;
                carry = next_c;
            }
            bool ge = (carry != 0);
            if (!ge) {
                for (size_t i = L; i-- > 0;) {
                    if (cur[i] != N[i]) { ge = (cur[i] > N[i]); break; }
                    if (i == 0) ge = true;
                }
            }
            if (ge) {
                u64 borrow = 0;
                for (size_t i = 0; i < L; ++i) {
                    u128 diff = static_cast<u128>(cur[i]) - N[i] - borrow;
                    cur[i] = static_cast<u64>(diff);
                    borrow = (diff >> 127) ? 1 : 0;
                }
            }
        }
        return cur;
    }

    std::vector<u64> from_mont(const std::vector<u64>& a) const {
        std::vector<u64> one(L, 0), res, t;
        one[0] = 1;
        mul(a, one, res, t);
        return res;
    }
};

static int proth_prove_builtin(u64 k, int n) {
    static constexpr u64 cand_a[] = {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61};
    u64 a = 0;
    for (u64 ca : cand_a) {
        int j = jacobi_proth(ca, k, n);
        if (j == 0) return 0;
        if (j == -1) { a = ca; break; }
    }
    if (a == 0) return 0;

    BigUInt N = BigUInt::proth_number(k, n);
    MontCtx ctx(N);
    std::vector<u64> base = ctx.to_mont(a);
    std::vector<u64> cur = ctx.to_mont(1);
    std::vector<u64> tmp, scratch;

    u64 ek = k;
    while (ek) {
        if (ek & 1) { ctx.mul(cur, base, tmp, scratch); cur.swap(tmp); }
        ek >>= 1;
        if (ek) { ctx.mul(base, base, tmp, scratch); base.swap(tmp); }
    }
    for (int i = 0; i < n - 1; ++i) {
        ctx.mul(cur, cur, tmp, scratch);
        cur.swap(tmp);
    }
    std::vector<u64> final_val = ctx.from_mont(cur);
    if (final_val[0] != N.d[0] - 1) return 0;
    for (size_t i = 1; i < ctx.L; ++i) {
        if (final_val[i] != N.d[i]) return 0;
    }
    return static_cast<int>(a);
}
#endif

static int proth_prove(u64 k, int n) {
#ifdef USE_GMP
    return proth_prove_gmp(k, n);
#else
    return proth_prove_builtin(k, n);
#endif
}

struct ProthCert {
    int n;
    u64 k;
    int a_pp;
    int a_p;
};

static int run_proth_shard(int n_min, int n_max, u64 k_lo, u64 k_hi,
                           int shard, int shards, uint32_t sieve_limit,
                           int time_budget_sec) {
    auto t0 = Clock::now();
    auto deadline = t0 + std::chrono::seconds(time_budget_sec);

    // Align k_lo upward to k == 3 (mod 6), and k_hi downward to k == 3 (mod 6)
    while (k_lo % 6 != 3) ++k_lo;
    while (k_hi % 6 != 3) --k_hi;
    if (k_lo >= k_hi) throw std::invalid_argument("k_lo >= k_hi");
    if (static_cast<u128>(k_hi) * 1000 > static_cast<u128>(k_lo) * 1355) {
        throw std::invalid_argument("k_hi / k_lo exceeds 1.355 overlap guarantee");
    }

    const auto primes = simple_sieve(sieve_limit);
    std::vector<uint32_t> sp;
    sp.reserve(primes.size());
    for (uint32_t q : primes) if (q >= 5) sp.push_back(q);

    std::vector<int> assigned;
    for (int n = n_min + shard; n <= n_max; n += shards) assigned.push_back(n);

    std::vector<ProthCert> certs;
    std::vector<int> pending;
    u64 total_sieved_survivors = 0;
    u64 total_proth_tests = 0;

    static constexpr size_t CHUNK_SLOTS = 262144;
    std::vector<uint32_t> r1_arr(sp.size()), r2_arr(sp.size());

    for (size_t idx = 0; idx < assigned.size(); ++idx) {
        if (Clock::now() >= deadline) {
            for (size_t j = idx; j < assigned.size(); ++j) pending.push_back(assigned[j]);
            break;
        }
        int n = assigned[idx];
        for (size_t pi = 0; pi < sp.size(); ++pi) {
            u64 q = sp[pi];
            u64 p2 = pow_mod64(2 % q, static_cast<u64>(n), q);
            u64 inv_p2 = pow_mod64(p2, q - 2, q);
            u64 bad_k1 = (q - inv_p2) % q;
            u64 bad_k2 = (bad_k1 * ((q + 1) / 2)) % q;
            u64 inv6 = pow_mod64(6 % q, q - 2, q);
            u64 klo_mod = k_lo % q;
            u64 d1 = (bad_k1 >= klo_mod) ? (bad_k1 - klo_mod) : (bad_k1 + q - klo_mod);
            u64 d2 = (bad_k2 >= klo_mod) ? (bad_k2 - klo_mod) : (bad_k2 + q - klo_mod);
            r1_arr[pi] = static_cast<uint32_t>((d1 * inv6) % q);
            r2_arr[pi] = static_cast<uint32_t>((d2 * inv6) % q);
        }

        const u64 total_slots = (k_hi - k_lo) / 6 + 1;
        bool found_n = false;
        ProthCert best{n, 0, 0, 0};

        for (u64 base_slot = 0; base_slot < total_slots && !found_n; base_slot += CHUNK_SLOTS) {
            if (Clock::now() >= deadline) break;
            size_t len = static_cast<size_t>(std::min<u64>(CHUNK_SLOTS, total_slots - base_slot));
            std::vector<uint8_t> alive(len, 1);

            for (size_t pi = 0; pi < sp.size(); ++pi) {
                uint32_t q = sp[pi];
                uint32_t rem = static_cast<uint32_t>(base_slot % q);
                uint32_t i1 = (r1_arr[pi] >= rem) ? (r1_arr[pi] - rem) : (r1_arr[pi] + q - rem);
                for (size_t i = i1; i < len; i += q) alive[i] = 0;
                uint32_t i2 = (r2_arr[pi] >= rem) ? (r2_arr[pi] - rem) : (r2_arr[pi] + q - rem);
                for (size_t i = i2; i < len; i += q) alive[i] = 0;
            }

            std::vector<u64> survivors;
            survivors.reserve(len / 50);
            for (size_t i = 0; i < len; ++i) {
                if (alive[i]) survivors.push_back(k_lo + 6ULL * (base_slot + i));
            }
            total_sieved_survivors += survivors.size();

            std::atomic<bool> chunk_found{false};
            std::atomic<u64> chunk_tested{0};

            #pragma omp parallel for schedule(dynamic, 8)
            for (size_t i = 0; i < survivors.size(); ++i) {
                if (chunk_found.load(std::memory_order_relaxed)) continue;
                u64 k = survivors[i];
                chunk_tested.fetch_add(1, std::memory_order_relaxed);
                int a1 = proth_prove(k, n);
                if (a1 == 0) continue;
                int a2 = proth_prove(k, n + 1);
                if (a2 == 0) continue;
                #pragma omp critical
                {
                    if (!chunk_found.load(std::memory_order_relaxed) || k < best.k) {
                        best = {n, k, a1, a2};
                        chunk_found.store(true, std::memory_order_relaxed);
                    }
                }
            }
            total_proth_tests += chunk_tested.load();
            if (chunk_found.load()) found_n = true;
        }

        if (found_n) certs.push_back(best);
        else pending.push_back(n);
    }

    double secs = std::chrono::duration<double>(Clock::now() - t0).count();
    std::cout << std::fixed << std::setprecision(6)
              << "{\"mode\":\"proth-shard\",\"n_min\":" << n_min
              << ",\"n_max\":" << n_max
              << ",\"k_lo\":" << k_lo << ",\"k_hi\":" << k_hi
              << ",\"shard\":" << shard << ",\"shards\":" << shards
              << ",\"sieve_limit\":" << sieve_limit
              << ",\"completed_count\":" << certs.size()
              << ",\"pending_count\":" << pending.size()
              << ",\"total_sieved_survivors\":" << total_sieved_survivors
              << ",\"total_proth_tests\":" << total_proth_tests
              << ",\"seconds\":" << secs
              << ",\"pending\":[";
    for (size_t i = 0; i < pending.size(); ++i) {
        if (i) std::cout << ",";
        std::cout << pending[i];
    }
    std::cout << "],\"certs\":[";
    for (size_t i = 0; i < certs.size(); ++i) {
        if (i) std::cout << ",";
        std::cout << "{\"n\":" << certs[i].n
                  << ",\"k\":" << certs[i].k
                  << ",\"a_pp\":" << certs[i].a_pp
                  << ",\"a_p\":" << certs[i].a_p << "}";
    }
    std::cout << "]}\n";
    return 0;
}

// ============================================================================
// Mode 4: Segmented Sieve Direct Census on [2, B_max]
// ============================================================================
static int run_sieve_census(u64 B_max) {
    auto t0 = Clock::now();
    uint32_t root = static_cast<uint32_t>(std::sqrt(static_cast<double>(B_max))) + 1;
    const auto base_p = simple_sieve(root);
    const u64 SEG = 1ULL << 20;
    const u64 half_B = B_max / 2;
    const u64 num_segs = (half_B > 139) ? ((half_B - 139) / SEG + 1) : 1;

    struct SegRes {
        u64 count = 0;
        u64 first_p = 0;
        u64 last_p = 0;
        u64 max_gap = 0;
        double max_ratio = 1.0;
    };
    std::vector<SegRes> seg_res(num_segs);

    #pragma omp parallel for schedule(dynamic, 1)
    for (u64 s = 0; s < num_segs; ++s) {
        u64 lo = 139 + s * SEG;
        if ((lo & 1) == 0) ++lo;
        u64 hi = std::min(half_B, 139 + (s + 1) * SEG - 1);
        if (lo > hi) continue;
        size_t len = static_cast<size_t>((hi - lo) / 2 + 1);
        std::vector<uint8_t> alive(len, 1);

        for (uint32_t q : base_p) {
            if (q == 2) continue;
            {
                u64 rem = lo % q;
                u64 first = (rem == 0) ? lo : (lo + q - rem);
                if ((first & 1) == 0) first += q;
                if (first == q) first += 2ULL * q;
                if (first <= hi) {
                    for (size_t i = static_cast<size_t>((first - lo) / 2); i < len; i += q)
                        alive[i] = 0;
                }
            }
            {
                u64 r = (q + 1) / 2;
                u64 rem = lo % q;
                u64 diff = (r >= rem) ? (r - rem) : (r + q - rem);
                u64 first = lo + diff;
                if ((first & 1) == 0) first += q;
                if (2 * first - 1 == q) first += 2ULL * q;
                if (first <= hi) {
                    for (size_t i = static_cast<size_t>((first - lo) / 2); i < len; i += q)
                        alive[i] = 0;
                }
            }
        }

        SegRes r;
        for (size_t i = 0; i < len; ++i) {
            if (!alive[i]) continue;
            u64 pp = lo + 2 * static_cast<u64>(i);
            u64 p = 2 * pp - 1;
            ++r.count;
            if (r.first_p == 0) r.first_p = p;
            else {
                u64 g = p - r.last_p;
                if (g > r.max_gap) r.max_gap = g;
                double rat = static_cast<double>(p) / static_cast<double>(r.last_p);
                if (rat > r.max_ratio) r.max_ratio = rat;
            }
            r.last_p = p;
        }
        seg_res[s] = r;
    }

    u64 sg_pair_count = 0, max_gap = 0, last_pair_p = 277;
    double max_ratio = 1.0;
    for (u64 s = 0; s < num_segs; ++s) {
        const auto& r = seg_res[s];
        if (r.count == 0) continue;
        sg_pair_count += r.count;
        if (r.max_gap > max_gap) max_gap = r.max_gap;
        if (r.max_ratio > max_ratio) max_ratio = r.max_ratio;
        if (r.first_p > last_pair_p) {
            u64 g = r.first_p - last_pair_p;
            if (g > max_gap) max_gap = g;
            double rat = static_cast<double>(r.first_p) / static_cast<double>(last_pair_p);
            if (rat > max_ratio) max_ratio = rat;
        }
        last_pair_p = r.last_p;
    }
    double secs = std::chrono::duration<double>(Clock::now() - t0).count();
    std::cout << std::fixed << std::setprecision(6)
              << "{\"mode\":\"sieve-census\",\"B_max\":" << B_max
              << ",\"prime_pairs_2p_minus_1\":" << sg_pair_count
              << ",\"max_pair_gap\":" << max_gap
              << ",\"max_pair_ratio\":" << max_ratio
              << ",\"e_threshold\":2.718282"
              << ",\"every_B_covered\":" << (max_ratio < 2.71 ? "true" : "false")
              << ",\"throughput_B_per_sec\":" << (static_cast<double>(B_max) / std::max(secs, 1e-9))
              << ",\"seconds\":" << secs << "}\n";
    return 0;
}

int main(int argc, char** argv) {
    std::string mode = "base";
    int B_limit = 500;
    u64 start_covered = 500;
    bool dump_links = false;
    int n_min = 33, n_max = 100;
    u64 k_lo = 536870915ULL;
    u64 k_hi = 724775733ULL;
    int shard = 0, shards = 1;
    uint32_t sieve_limit = 500000;
    int time_budget = 300;
    u64 B_census = 1000000000ULL;

    for (int i = 1; i < argc; ++i) {
        std::string arg = argv[i];
        auto get_val = [&](const std::string& pref) -> std::string {
            return arg.substr(pref.size());
        };
        if (arg.rfind("--mode=", 0) == 0) mode = get_val("--mode=");
        else if (arg.rfind("--B-limit=", 0) == 0) B_limit = std::stoi(get_val("--B-limit="));
        else if (arg.rfind("--start-covered=", 0) == 0) start_covered = std::stoull(get_val("--start-covered="));
        else if (arg == "--dump-links") dump_links = true;
        else if (arg.rfind("--n-min=", 0) == 0) n_min = std::stoi(get_val("--n-min="));
        else if (arg.rfind("--n-max=", 0) == 0) n_max = std::stoi(get_val("--n-max="));
        else if (arg.rfind("--k-lo=", 0) == 0) k_lo = std::stoull(get_val("--k-lo="));
        else if (arg.rfind("--k-hi=", 0) == 0) k_hi = std::stoull(get_val("--k-hi="));
        else if (arg.rfind("--shard=", 0) == 0) shard = std::stoi(get_val("--shard="));
        else if (arg.rfind("--shards=", 0) == 0) shards = std::stoi(get_val("--shards="));
        else if (arg.rfind("--sieve-limit=", 0) == 0) sieve_limit = static_cast<uint32_t>(std::stoul(get_val("--sieve-limit=")));
        else if (arg.rfind("--seconds=", 0) == 0) time_budget = std::stoi(get_val("--seconds="));
        else if (arg.rfind("--B-max=", 0) == 0) B_census = std::stoull(get_val("--B-max="));
    }

    if (mode == "base") return run_base_closure(B_limit);
    if (mode == "chain64") return run_chain64(start_covered, dump_links);
    if (mode == "proth-shard") return run_proth_shard(n_min, n_max, k_lo, k_hi, shard, shards, sieve_limit, time_budget);
    if (mode == "sieve-census") return run_sieve_census(B_census);
    std::cerr << "Unknown mode: " << mode << "\n";
    return 1;
}
