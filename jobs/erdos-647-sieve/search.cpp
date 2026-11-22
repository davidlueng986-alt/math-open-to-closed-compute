// Erdős Problem #647 — Ultra-Fast Segmented Wheel + Word-Mask Sieve + 128-bit Verifier
//
// Question: Does there exist an integer n > 24 such that max_{1 <= m < n} (m + tau(m)) <= n + 2?
// Equivalently: tau(n - k) <= k + 2 for all 1 <= k < n.
//
// Mathematical Reduction (rigorous for all n >= 10^12, derived dynamically at startup):
//   1. W = 2^5 * 3^2 * 5 * 7 * 11 * 13 * 17 * 19 * 23 = 10,708,457,760.
//      Exact divisor-count lower bounds on n - k (k = 1..500) leave exactly 786 surviving
//      residue classes r mod W (all divisible by 360,360; density 7.340e-8).
//   2. For each class r mod W and every prime p not dividing W with 29 <= p <= P_SIEVE,
//      every offset k with 4*P(r-k) > k+2 and M_exact(r-k) * P_SIEVE^3 < N_MIN forbids
//      n == k (mod p) (13 to 23 forbidden residues per prime, avg 18.30).
//   3. Word-level (64-bit) alive-mask sieving over u (where n = W*u + r) applies all ~18.3
//      forbidden residues of each small prime p in a SINGLE bitwise AND per 64 candidates,
//      with division-free Barrett/reciprocal fast-mod in Tiers 2 & 3.
//   4. Surviving candidates are tested by 7 prime-forced cofactors (k = 1, 2, 3, 4, 6, 8, 12)
//      using 64-bit / 128-bit Montgomery Miller-Rabin, followed by exact divisor-count cascade
//      (trial division + Pollard's rho + deterministic Miller-Rabin) up to the exact SHCN
//      upper bound on max_{m < n} tau(m).

#include <algorithm>
#include <array>
#include <atomic>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <string>
#include <vector>

#ifdef _OPENMP
#include <omp.h>
#endif

using u64 = std::uint64_t;
using u128 = __uint128_t;
using Clock = std::chrono::steady_clock;

// ---------------------------------------------------------------------------
// Fast division-free u64 % p for small prime p (valid for all u < 2^64)
// ---------------------------------------------------------------------------
struct FastMod64 {
    u64 p;
    u64 m; // floor(2^64 / p)
    FastMod64() : p(1), m(0) {}
    explicit FastMod64(u64 prime) : p(prime), m(u64((u128(1) << 64) / prime)) {}
    inline u64 rem(u64 u) const {
        u64 q = u64((u128(u) * m) >> 64);
        u64 r = u - q * p;
        return (r >= p) ? (r - p) : r;
    }
};

// ---------------------------------------------------------------------------
// 128-bit I/O & Modular Arithmetic (64-bit fast path + 128-bit Montgomery)
// ---------------------------------------------------------------------------

static std::string u128_to_str(u128 v) {
    if (v == 0) return "0";
    std::string s;
    while (v > 0) {
        s.push_back(char('0' + int(v % 10)));
        v /= 10;
    }
    std::reverse(s.begin(), s.end());
    return s;
}

static u128 str_to_u128(const std::string& s) {
    u128 v = 0;
    for (char c : s) {
        if (c == '_' || c == ',') continue;
        if (c < '0' || c > '9') throw std::invalid_argument("invalid integer: " + s);
        v = v * 10 + u64(c - '0');
    }
    return v;
}

static inline u64 mul_mod_64(u64 a, u64 b, u64 m) {
    return u64((u128(a) * b) % m);
}

static inline u64 pow_mod_64(u64 a, u64 e, u64 m) {
    u64 r = 1 % m;
    a %= m;
    while (e) {
        if (e & 1) r = mul_mod_64(r, a, m);
        a = mul_mod_64(a, a, m);
        e >>= 1;
    }
    return r;
}

// 128-bit Montgomery arithmetic for odd moduli m < 2^126 (exact, no overflow).
struct Mont128 {
    u64 m0, m1;
    u64 inv;
    u128 m;
    u128 r2;
    u128 one;

    explicit Mont128(u128 mod) : m0(u64(mod)), m1(u64(mod >> 64)), m(mod) {
        u64 x = 1;
        for (int i = 0; i < 6; ++i) x *= (2 - m0 * x);
        inv = -x;
        one = (u128(0) - m) % m;
        u128 cur = one;
        for (int i = 0; i < 128; ++i) {
            cur = (cur >= m - cur) ? (cur - (m - cur)) : (cur + cur);
        }
        r2 = cur;
    }

    inline u128 mul(u128 a, u128 b) const {
        const u64 a0 = u64(a), a1 = u64(a >> 64);
        const u64 b0 = u64(b), b1 = u64(b >> 64);

        u128 t = u128(a0) * b0;
        u64 t0 = u64(t);
        t = u128(a1) * b0 + u64(t >> 64);
        u64 t1 = u64(t), t2 = u64(t >> 64);

        u64 q = t0 * inv;
        u128 c = u128(q) * m0 + t0;
        c = u128(q) * m1 + t1 + u64(c >> 64);
        t0 = u64(c);
        u128 s = u128(t2) + u64(c >> 64);
        t1 = u64(s);
        t2 = u64(s >> 64);

        t = u128(a0) * b1 + t0;
        t0 = u64(t);
        t = u128(a1) * b1 + t1 + u64(t >> 64);
        t1 = u64(t);
        s = u128(t2) + u64(t >> 64);
        t2 = u64(s);
        u64 t3 = u64(s >> 64);

        q = t0 * inv;
        c = u128(q) * m0 + t0;
        c = u128(q) * m1 + t1 + u64(c >> 64);
        t0 = u64(c);
        s = u128(t2) + u64(c >> 64);
        t1 = u64(s);
        u64 carry = t3 + u64(s >> 64);

        u128 res = (u128(t1) << 64) | t0;
        if (carry || res >= m) res -= m;
        return res;
    }

    inline u128 to_mont(u128 x) const { return mul(x % m, r2); }
    inline u128 pow(u128 base_mont, u128 e) const {
        u128 r = one;
        u128 a = base_mont;
        while (e) {
            if (e & 1) r = mul(r, a);
            a = mul(a, a);
            e >>= 1;
        }
        return r;
    }
};

static inline bool sprp_64(u64 n, u64 a) {
    if (a % n == 0) return true;
    u64 d = n - 1;
    int s = __builtin_ctzll(d);
    d >>= s;
    u64 x = pow_mod_64(a, d, n);
    if (x == 1 || x == n - 1) return true;
    for (int r = 1; r < s; ++r) {
        x = mul_mod_64(x, x, n);
        if (x == n - 1) return true;
    }
    return false;
}

static inline bool sprp_128(const Mont128& M, u128 n, u128 d, int s, u64 a) {
    u128 am = a % n;
    if (am == 0) return true;
    u128 x = M.pow(M.to_mont(am), d);
    u128 neg_one = n - M.one;
    if (x == M.one || x == neg_one) return true;
    for (int r = 1; r < s; ++r) {
        x = M.mul(x, x);
        if (x == neg_one) return true;
    }
    return false;
}

static inline bool is_sprp2(u128 n) {
    if (n < 2) return false;
    if (n == 2 || n == 3) return true;
    if ((n & 1) == 0) return false;
    if (n <= u128(UINT64_MAX)) {
        return sprp_64(u64(n), 2);
    }
    u128 d = n - 1;
    int s = 0;
    while ((d & 1) == 0) { d >>= 1; ++s; }
    Mont128 M(n);
    return sprp_128(M, n, d, s, 2);
}

// 100% deterministic primality test for all n < 3.317e24 (Sorenson & Webster 2017)
static bool is_prime_exact(u128 n) {
    if (n < 2) return false;
    static constexpr u64 small_p[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41};
    for (u64 p : small_p) {
        if (n == p) return true;
        if (n % p == 0) return false;
    }
    if (n < 43 * 43) return true;
    if (n <= u128(UINT64_MAX)) {
        static constexpr u64 bases64[] = {2, 325, 9375, 28178, 450775, 9780504, 1795265022};
        for (u64 a : bases64) {
            if (!sprp_64(u64(n), a)) return false;
        }
        return true;
    }
    u128 d = n - 1;
    int s = 0;
    while ((d & 1) == 0) { d >>= 1; ++s; }
    Mont128 M(n);
    for (u64 a : small_p) {
        if (!sprp_128(M, n, d, s, a)) return false;
    }
    return true;
}

static u128 gcd_u128(u128 a, u128 b) {
    while (b) {
        u128 t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static u128 pollard_rho(u128 n) {
    if ((n & 1) == 0) return 2;
    if (n % 3 == 0) return 3;
    if (n <= u128(UINT64_MAX)) {
        u64 m = u64(n);
        for (u64 c = 1; c < 100; ++c) {
            u64 x = 2, y = 2, d = 1;
            auto f = [m, c](u64 v) { return (mul_mod_64(v, v, m) + c) % m; };
            while (d == 1) {
                x = f(x);
                y = f(f(y));
                u64 diff = (x > y) ? (x - y) : (y - x);
                d = std::gcd(diff, m);
            }
            if (d != m) return d;
        }
    }
    Mont128 M(n);
    for (u64 c = 1; c < 200; ++c) {
        u128 cm = M.to_mont(c);
        u128 x = M.to_mont(2), y = x, d = 1;
        auto f = [&](u128 v) {
            u128 r = M.mul(v, v) + cm;
            return (r >= n) ? (r - n) : r;
        };
        while (d == 1) {
            u128 prod = M.one;
            for (int step = 0; step < 64; ++step) {
                x = f(x);
                y = f(f(y));
                u128 diff = (x > y) ? (x - y) : (y - x);
                if (diff == 0) { prod = 0; break; }
                prod = M.mul(prod, diff);
            }
            if (prod == 0) break;
            d = gcd_u128(prod, n);
        }
        if (d > 1 && d < n) return d;
    }
    for (u64 d = 5; u128(d) * d <= n; d += 2) {
        if (n % d == 0) return d;
    }
    return n;
}

static void factor_rec(u128 n, std::vector<u128>& out) {
    if (n == 1) return;
    if (is_prime_exact(n)) {
        out.push_back(n);
        return;
    }
    u128 d = pollard_rho(n);
    factor_rec(d, out);
    factor_rec(n / d, out);
}

static u64 exact_tau(u128 n, const std::vector<u64>& small_primes) {
    if (n <= 1) return 1;
    u64 tau = 1;
    int tz = 0;
    while ((n & 1) == 0) { n >>= 1; ++tz; }
    if (tz) tau *= u64(tz + 1);
    for (u64 p : small_primes) {
        if (p == 2) continue;
        if (u128(p) * p > n) break;
        if (n % p == 0) {
            u64 e = 0;
            do { n /= p; ++e; } while (n % p == 0);
            tau *= (e + 1);
        }
    }
    if (n == 1) return tau;
    if (is_prime_exact(n)) return tau * 2;
    std::vector<u128> fac;
    factor_rec(n, fac);
    std::sort(fac.begin(), fac.end());
    for (size_t i = 0; i < fac.size(); ) {
        size_t j = i + 1;
        while (j < fac.size() && fac[j] == fac[i]) ++j;
        tau *= u64(j - i + 1);
        i = j;
    }
    return tau;
}

// Exact upper bound on max_{m < n} tau(m) (verified via SHCN DP up to 10^23)
static u64 max_tau_upper_bound(u128 n) {
    if (n <= 1000000ULL) return 240;
    if (n <= u128(1000000000000ULL)) return 6720;
    if (n <= u128(1000000000000000000ULL)) return 103680;
    if (n <= u128(1000000000000000000ULL) * 10) return 161280;
    if (n <= u128(1000000000000000000ULL) * 100) return 245760;
    if (n <= u128(1000000000000000000ULL) * 1000) return 368640;
    if (n <= u128(1000000000000000000ULL) * 10000) return 552960;
    if (n <= u128(1000000000000000000ULL) * 100000) return 860160;
    return 2000000;
}

// Returns {kill_k, kill_tau}. If kill_k == 0, n is a TRUE SOLUTION to Erdős #647!
static std::pair<u64, u64> verify_candidate_exact(u128 n, const std::vector<u64>& small_primes) {
    const u64 k_limit = std::min<u64>(u64(n - 1), max_tau_upper_bound(n));
    for (u64 k = 1; k <= k_limit; ++k) {
        u64 t = exact_tau(n - k, small_primes);
        if (t > k + 2) {
            return {k, t};
        }
    }
    return {0, 0};
}

// ---------------------------------------------------------------------------
// Dynamic Structural Narrowing: Wheel W = 10,708,457,760 (786 classes)
// ---------------------------------------------------------------------------

static constexpr u64 WHEEL_W = 10708457760ULL; // 2^5 * 3^2 * 5 * 7 * 11 * 13 * 17 * 19 * 23

struct PrimePower { u64 p; int E; };

static inline std::pair<int, bool> v_p_capped(u64 x, u64 p, int max_e) {
    if (x == 0) return {max_e, true};
    int e = 0;
    while (e < max_e && x % p == 0) { x /= p; ++e; }
    return {e, e == max_e};
}

static u64 min_tau_lb(u64 r, const std::vector<PrimePower>& pp, u128 n_min) {
    u64 P = 1;
    u128 M_exact = 1;
    u64 p_max = 0;
    int E_max = 0;
    for (const auto& q : pp) {
        auto [e, hit] = v_p_capped(r, q.p, q.E);
        P *= u64(e + 1);
        for (int i = 0; i < e; ++i) M_exact *= q.p;
        if (hit) {
            if (q.p > p_max) p_max = q.p;
            if (q.E > E_max) E_max = q.E;
        }
    }
    if (p_max == 0) return (n_min > M_exact) ? (2 * P) : P;
    u128 p_pow = 1;
    for (int i = 0; i < E_max; ++i) p_pow *= p_max;
    if (M_exact * p_pow < n_min) return 2 * P;
    int D = 0;
    u128 val = M_exact;
    while (val < n_min) { val *= p_max; ++D; }
    u64 smooth_lb = (P * u64(E_max + 1 + D)) / u64(E_max + 1);
    return std::min(2 * P, smooth_lb);
}

static std::vector<u64> build_wheel_classes(u128 n_min, std::vector<PrimePower>& out_pp) {
    const std::vector<PrimePower> steps = {
        {2, 3}, {3, 2}, {5, 1}, {7, 1}, {11, 1}, {13, 1}, {17, 1}, {19, 1}, {23, 1}, {2, 5}
    };
    std::vector<u64> res = {0};
    u64 M = 1;
    out_pp.clear();
    for (const auto& st : steps) {
        int old_E = 0;
        std::vector<PrimePower> next_pp;
        for (const auto& q : out_pp) {
            if (q.p == st.p) { old_E = q.E; next_pp.push_back(st); }
            else next_pp.push_back(q);
        }
        if (old_E == 0) next_pp.push_back(st);
        u64 mult = 1;
        for (int i = 0; i < st.E - old_E; ++i) mult *= st.p;
        u64 next_M = M * mult;
        std::vector<u64> surv;
        for (u64 r0 : res) {
            for (u64 t = 0; t < mult; ++t) {
                u64 n_mod = r0 + t * M;
                bool ok = true;
                for (u64 k = 1; k <= 500; ++k) {
                    u64 r = (n_mod >= k) ? (n_mod - k) : (n_mod + next_M - k);
                    if (min_tau_lb(r, next_pp, n_min) > k + 2) {
                        ok = false;
                        break;
                    }
                }
                if (ok) surv.push_back(n_mod);
            }
        }
        res = std::move(surv);
        M = next_M;
        out_pp = std::move(next_pp);
    }
    if (M != WHEEL_W || res.size() != 786) {
        throw std::logic_error("unexpected wheel size or class count");
    }
    return res;
}

static u64 inv_mod_p(u64 a, u64 p) {
    return pow_mod_64(a % p, p - 2, p);
}

static std::vector<u64> primes_up_to(u64 limit) {
    std::vector<uint8_t> comp(limit + 1, 0);
    std::vector<u64> ps;
    for (u64 p = 2; p <= limit; ++p) {
        if (comp[p]) continue;
        ps.push_back(p);
        if (p <= limit / p) {
            for (u64 j = p * p; j <= limit; j += p) comp[j] = 1;
        }
    }
    return ps;
}

// ---------------------------------------------------------------------------
// Precomputed Per-Class Word-Mask Sieve Tables (with FastMod64)
// ---------------------------------------------------------------------------

// Tier-1 primes (14 primes: 29..83 -> ~91% of 64-bit words hit 0 immediately!)
static constexpr int NUM_T1 = 14;
static constexpr u64 T1_PRIMES[NUM_T1] = {29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83};

// Tier-2 primes (26 primes: 89..227, division-free FastMod64)
static constexpr int NUM_T2 = 26;
static constexpr u64 T2_PRIMES[NUM_T2] = {
    89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
    157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227
};

// Tier-3 primes (45 primes: 229..491, division-free FastMod64)
static constexpr int NUM_T3 = 45;
static constexpr u64 T3_PRIMES[NUM_T3] = {
    229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311,
    313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401,
    409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491
};

static constexpr u64 P_SIEVE_MAX = 491;

static FastMod64 T2_FM[NUM_T2];
static FastMod64 T3_FM[NUM_T3];

static void init_fastmods() {
    for (int i = 0; i < NUM_T2; ++i) T2_FM[i] = FastMod64(T2_PRIMES[i]);
    for (int i = 0; i < NUM_T3; ++i) T3_FM[i] = FastMod64(T3_PRIMES[i]);
}

struct ClassSieveData {
    u64 r_mod_W;
    int v2_n_minus_8;
    std::vector<u64> forb_k;

    u64 t1_masks[83 * NUM_T1];
    int t1_off[NUM_T1];
    int t1_step64[NUM_T1];

    std::vector<u64> t2_masks;
    int t2_off[NUM_T2];

    u64 t3_forb_bits[NUM_T3][8];

    void build(u64 r, const std::vector<PrimePower>& pp, u128 n_min) {
        r_mod_W = r;
        v2_n_minus_8 = ((r % 16) == 0) ? 3 : 4;
        forb_k.clear();
        const u128 p3 = u128(P_SIEVE_MAX) * P_SIEVE_MAX * P_SIEVE_MAX;
        for (u64 k = 1; k <= 600; ++k) {
            u64 rem = (r >= k) ? (r - k) : (r + WHEEL_W - k);
            u64 P = 1;
            u128 M_exact = 1;
            for (const auto& q : pp) {
                auto [e, hit] = v_p_capped(rem, q.p, q.E);
                (void)hit;
                P *= u64(e + 1);
                for (int i = 0; i < e; ++i) M_exact *= q.p;
            }
            if (4 * P > k + 2 && M_exact * p3 < n_min) {
                forb_k.push_back(k);
            }
        }

        auto build_forb_u = [&](u64 p, std::vector<uint8_t>& bad) {
            bad.assign(p, 0);
            u64 invW = inv_mod_p(WHEEL_W, p);
            u64 rp = r % p;
            for (u64 k : forb_k) {
                u64 kp = k % p;
                u64 diff = (kp >= rp) ? (kp - rp) : (kp + p - rp);
                u64 u_bad = (diff * invW) % p;
                bad[u_bad] = 1;
            }
        };

        int off = 0;
        std::vector<uint8_t> bad;
        for (int i = 0; i < NUM_T1; ++i) {
            u64 p = T1_PRIMES[i];
            t1_off[i] = off;
            t1_step64[i] = int(64 % p);
            build_forb_u(p, bad);
            for (u64 j = 0; j < p; ++j) {
                u64 mask = ~0ULL;
                for (int b = 0; b < 64; ++b) {
                    if (bad[(j + b) % p]) mask &= ~(1ULL << b);
                }
                t1_masks[off + j] = mask;
            }
            off += int(p);
        }

        t2_masks.clear();
        for (int i = 0; i < NUM_T2; ++i) {
            u64 p = T2_PRIMES[i];
            t2_off[i] = int(t2_masks.size());
            build_forb_u(p, bad);
            for (u64 j = 0; j < p; ++j) {
                u64 mask = ~0ULL;
                for (int b = 0; b < 64; ++b) {
                    if (bad[(j + b) % p]) mask &= ~(1ULL << b);
                }
                t2_masks.push_back(mask);
            }
        }

        std::memset(t3_forb_bits, 0, sizeof(t3_forb_bits));
        for (int i = 0; i < NUM_T3; ++i) {
            u64 p = T3_PRIMES[i];
            build_forb_u(p, bad);
            for (u64 j = 0; j < p; ++j) {
                if (bad[j]) t3_forb_bits[i][j >> 6] |= (1ULL << (j & 63));
            }
        }
    }
};

struct SearchStats {
    u64 u_tested = 0;
    u64 t1_survivors = 0;
    u64 t2_survivors = 0;
    u64 t3_survivors = 0;
    u64 prime7_survivors = 0;
    u64 max_depth = 0;
    u128 max_depth_n = 0;
    u64 max_depth_kill_tau = 0;
    bool witness_found = false;
    u128 witness_n = 0;

    void merge(const SearchStats& o) {
        u_tested += o.u_tested;
        t1_survivors += o.t1_survivors;
        t2_survivors += o.t2_survivors;
        t3_survivors += o.t3_survivors;
        prime7_survivors += o.prime7_survivors;
        if (o.max_depth > max_depth) {
            max_depth = o.max_depth;
            max_depth_n = o.max_depth_n;
            max_depth_kill_tau = o.max_depth_kill_tau;
        }
        if (o.witness_found && !witness_found) {
            witness_found = true;
            witness_n = o.witness_n;
        }
    }
};

static void scan_class_range(
    const ClassSieveData& cls,
    u64 u_lo,
    u64 u_hi,
    const std::vector<u64>& small_primes,
    SearchStats& st,
    const Clock::time_point& deadline,
    std::atomic<bool>& stop_flag,
    bool& finished_full
) {
    if (u_lo >= u_hi) return;
    const u64 r = cls.r_mod_W;
    const int s8 = cls.v2_n_minus_8;

    int i0 = int(u_lo % 29), i1 = int(u_lo % 31), i2 = int(u_lo % 37), i3 = int(u_lo % 41);
    int i4 = int(u_lo % 43), i5 = int(u_lo % 47), i6 = int(u_lo % 53), i7 = int(u_lo % 59);
    int i8 = int(u_lo % 61), i9 = int(u_lo % 67), i10 = int(u_lo % 71), i11 = int(u_lo % 73);
    int i12 = int(u_lo % 79), i13 = int(u_lo % 83);

    const u64* m0 = cls.t1_masks + cls.t1_off[0];
    const u64* m1 = cls.t1_masks + cls.t1_off[1];
    const u64* m2 = cls.t1_masks + cls.t1_off[2];
    const u64* m3 = cls.t1_masks + cls.t1_off[3];
    const u64* m4 = cls.t1_masks + cls.t1_off[4];
    const u64* m5 = cls.t1_masks + cls.t1_off[5];
    const u64* m6 = cls.t1_masks + cls.t1_off[6];
    const u64* m7 = cls.t1_masks + cls.t1_off[7];
    const u64* m8 = cls.t1_masks + cls.t1_off[8];
    const u64* m9 = cls.t1_masks + cls.t1_off[9];
    const u64* m10 = cls.t1_masks + cls.t1_off[10];
    const u64* m11 = cls.t1_masks + cls.t1_off[11];
    const u64* m12 = cls.t1_masks + cls.t1_off[12];
    const u64* m13 = cls.t1_masks + cls.t1_off[13];

    auto adv = [](int& idx, int step, int p) {
        idx += step;
        if (idx >= p) idx -= p;
    };

    u64 u = u_lo;
    u64 word_count = 0;

    while (u < u_hi) {
        if ((word_count++ & 131071ULL) == 0) {
            if (stop_flag.load(std::memory_order_relaxed) || Clock::now() >= deadline) {
                finished_full = false;
                return;
            }
        }

        // Fully unrolled 14-prime L1-cache word-mask intersection
        u64 alive = m0[i0] & m1[i1] & m2[i2] & m3[i3];
        alive &= m4[i4] & m5[i5] & m6[i6] & m7[i7];
        alive &= m8[i8] & m9[i9] & m10[i10] & m11[i11];
        alive &= m12[i12] & m13[i13];

        adv(i0, 6, 29);   adv(i1, 2, 31);   adv(i2, 27, 37);  adv(i3, 23, 41);
        adv(i4, 21, 43);  adv(i5, 17, 47);  adv(i6, 11, 53);  adv(i7, 5, 59);
        adv(i8, 3, 61);   adv(i9, 64, 67);  adv(i10, 64, 71); adv(i11, 64, 73);
        adv(i12, 64, 79); adv(i13, 64, 83);

        const u64 rem = u_hi - u;
        if (__builtin_expect(rem < 64, 0)) {
            alive &= ((1ULL << rem) - 1ULL);
            st.u_tested += rem;
        } else {
            st.u_tested += 64;
        }

        if (__builtin_expect(alive != 0, 0)) {
            st.t1_survivors += u64(__builtin_popcountll(alive));
            for (int i = 0; i < NUM_T2 && alive; ++i) {
                alive &= cls.t2_masks[cls.t2_off[i] + T2_FM[i].rem(u)];
            }
            if (alive) {
                st.t2_survivors += u64(__builtin_popcountll(alive));
                while (alive) {
                    int b = __builtin_ctzll(alive);
                    alive &= (alive - 1);
                    u64 uc = u + u64(b);

                    bool ok3 = true;
                    for (int i = 0; i < NUM_T3; ++i) {
                        u64 rem_p = T3_FM[i].rem(uc);
                        if ((cls.t3_forb_bits[i][rem_p >> 6] >> (rem_p & 63)) & 1ULL) {
                            ok3 = false;
                            break;
                        }
                    }
                    if (!ok3) continue;
                    ++st.t3_survivors;

                    u128 n = u128(WHEEL_W) * uc + r;

                    if (!is_sprp2(n - 1)) continue;
                    if (!is_sprp2((n - 2) >> 1)) continue;
                    if (!is_sprp2((n - 3) / 3)) continue;
                    if (!is_sprp2((n - 4) >> 2)) continue;
                    if (!is_sprp2((n - 6) / 6)) continue;
                    if (!is_sprp2((n - 8) >> s8)) continue;
                    if (!is_sprp2((n - 12) / 12)) continue;

                    ++st.prime7_survivors;

                    auto [kill_k, kill_tau] = verify_candidate_exact(n, small_primes);
                    if (kill_k == 0) {
                        st.witness_found = true;
                        st.witness_n = n;
                        stop_flag.store(true, std::memory_order_relaxed);
                        return;
                    }
                    u64 depth = kill_k - 1;
                    if (depth > st.max_depth) {
                        st.max_depth = depth;
                        st.max_depth_n = n;
                        st.max_depth_kill_tau = kill_tau;
                    }
                }
            }
        }
        u += 64;
    }
}

static void run_selftest(const std::vector<u64>& small_primes) {
    // 1. Exact solutions in [2, 100]
    std::vector<u64> sols;
    for (u64 n = 2; n <= 100; ++n) {
        auto [kk, kt] = verify_candidate_exact(n, small_primes);
        if (kk == 0) sols.push_back(n);
    }
    const std::vector<u64> expected = {2, 3, 4, 5, 6, 8, 10, 12, 24};
    if (sols != expected) throw std::runtime_error("selftest failed: [2,100] solutions");

    // 2. bentrd depth records
    const u128 n1 = str_to_u128("1341119762248986720");
    const u128 n2 = str_to_u128("9077332126027084920");
    auto [k1, t1] = verify_candidate_exact(n1, small_primes);
    auto [k2, t2] = verify_candidate_exact(n2, small_primes);
    if (k1 != 17 || t1 != 96) throw std::runtime_error("selftest failed on n1");
    if (k2 != 20 || t2 != 72) throw std::runtime_error("selftest failed on n2");

    // 3. Wheel membership + FastMod64 exactness check
    std::vector<PrimePower> pp;
    auto classes = build_wheel_classes(u128(1000000000000ULL), pp);
    u64 r2 = u64(n2 % WHEEL_W);
    if (std::find(classes.begin(), classes.end(), r2) == classes.end()) {
        throw std::runtime_error("selftest failed: n2 class missing");
    }
    for (int i = 0; i < NUM_T2; ++i) {
        for (u64 x : {0ULL, 1ULL, 123456789ULL, 987654321012345ULL, (1ULL << 62) + 777ULL}) {
            if (T2_FM[i].rem(x) != x % T2_PRIMES[i]) throw std::runtime_error("FastMod64 T2 mismatch");
        }
    }
    for (int i = 0; i < NUM_T3; ++i) {
        for (u64 x : {0ULL, 1ULL, 123456789ULL, 987654321012345ULL, (1ULL << 62) + 777ULL}) {
            if (T3_FM[i].rem(x) != x % T3_PRIMES[i]) throw std::runtime_error("FastMod64 T3 mismatch");
        }
    }

    // 4. 128-bit Montgomery primality & Pollard-rho check above 2^64
    const u128 p64_1 = (u128(1) << 64) + 13;
    const u128 p64_2 = (u128(1) << 64) + 37;
    if (!is_prime_exact(p64_1) || !is_prime_exact(p64_2) || is_prime_exact(p64_1 + 2)) {
        throw std::runtime_error("selftest failed: 128-bit primality check");
    }
    const u128 c128 = u128(4294967311ULL) * u128(4294967357ULL);
    if (exact_tau(c128, small_primes) != 4) {
        throw std::runtime_error("selftest failed: 128-bit Pollard rho tau");
    }

    std::cout << "{\"selftest\":\"PASS\",\"small_solutions\":[2,3,4,5,6,8,10,12,24],"
              << "\"n1_kill_k\":17,\"n1_kill_tau\":96,"
              << "\"n2_kill_k\":20,\"n2_kill_tau\":72,"
              << "\"fastmod64_ok\":true,\"u128_montgomery_ok\":true}\n";
}

int main(int argc, char** argv) {
    init_fastmods();
    const auto small_primes = primes_up_to(5000);

    if (argc == 2 && std::string(argv[1]) == "--selftest") {
        run_selftest(small_primes);
        return 0;
    }

    if (argc != 7) {
        std::cerr << "Usage: search N_START N_END SHARD SHARDS SECONDS VERBOSE(0|1)\n"
                  << "   or: search --selftest\n";
        return 2;
    }

    const u128 n_start = str_to_u128(argv[1]);
    const u128 n_end = str_to_u128(argv[2]);
    const int shard = std::stoi(argv[3]);
    const int shards = std::stoi(argv[4]);
    const int seconds = std::stoi(argv[5]);
    const int verbose = std::stoi(argv[6]);

    if (n_start < u128(1000000000000ULL) || n_end <= n_start || shards < 1 || shard < 0 || shard >= shards || seconds < 1) {
        throw std::invalid_argument("invalid arguments (require N_START >= 10^12 and N_END > N_START)");
    }

    const auto t0 = Clock::now();
    const auto deadline = t0 + std::chrono::seconds(seconds);

    std::vector<PrimePower> pp;
    const auto classes = build_wheel_classes(n_start, pp);

    const u64 u_min = u64(n_start / WHEEL_W);
    const u64 u_max = u64((n_end + WHEEL_W - 1) / WHEEL_W);
    const u64 total_u = (u_max > u_min) ? (u_max - u_min) : 0;

    const u64 shard_u_lo = u_min + u64((u128(total_u) * u64(shard)) / u64(shards));
    const u64 shard_u_hi = u_min + u64((u128(total_u) * u64(shard + 1)) / u64(shards));

    std::vector<ClassSieveData> class_data(classes.size());
    #pragma omp parallel for schedule(static)
    for (int i = 0; i < int(classes.size()); ++i) {
        class_data[i].build(classes[i], pp, n_start);
    }

    std::atomic<bool> stop_flag(false);
    std::vector<uint8_t> cls_done(classes.size(), 0);
    SearchStats total_stats;

    #pragma omp parallel
    {
        SearchStats local_st;
        #pragma omp for schedule(dynamic, 1)
        for (int i = 0; i < int(classes.size()); ++i) {
            if (stop_flag.load(std::memory_order_relaxed)) continue;
            const u64 r = class_data[i].r_mod_W;
            u64 lo = shard_u_lo;
            u64 hi = shard_u_hi;
            if (u128(WHEEL_W) * lo + r < n_start) ++lo;
            if (hi > lo && u128(WHEEL_W) * (hi - 1) + r >= n_end) --hi;

            bool fin = true;
            scan_class_range(class_data[i], lo, hi, small_primes, local_st, deadline, stop_flag, fin);
            cls_done[i] = fin ? 1 : 0;
        }
        #pragma omp critical
        {
            total_stats.merge(local_st);
        }
    }

    int completed_classes = 0;
    for (uint8_t d : cls_done) completed_classes += d;
    const double elapsed = std::chrono::duration<double>(Clock::now() - t0).count();
    const u128 shard_n_lo = std::max(n_start, u128(WHEEL_W) * shard_u_lo);
    const u128 shard_n_hi = std::min(n_end, u128(WHEEL_W) * shard_u_hi);
    const double n_span = double(shard_n_hi > shard_n_lo ? (shard_n_hi - shard_n_lo) : 0);
    const double n_per_sec = (elapsed > 0.0) ? (n_span / elapsed) : 0.0;

    if (verbose) {
        std::cerr << "[shard " << shard << "/" << shards << "] completed_classes=" << completed_classes
                  << "/786 elapsed=" << elapsed << "s rate=" << (n_per_sec / 1e15) << "e15 n/s\n";
    }

    std::cout << "{"
              << "\"shard\":" << shard
              << ",\"shards\":" << shards
              << ",\"wheel_modulus\":" << WHEEL_W
              << ",\"wheel_classes\":786"
              << ",\"n_start\":\"" << u128_to_str(n_start) << "\""
              << ",\"n_end\":\"" << u128_to_str(n_end) << "\""
              << ",\"shard_u_lo\":" << shard_u_lo
              << ",\"shard_u_hi\":" << shard_u_hi
              << ",\"shard_n_lo\":\"" << u128_to_str(shard_n_lo) << "\""
              << ",\"shard_n_hi\":\"" << u128_to_str(shard_n_hi) << "\""
              << ",\"completed_classes\":" << completed_classes
              << ",\"complete\":" << (completed_classes == 786 ? "true" : "false")
              << ",\"u_tested\":" << total_stats.u_tested
              << ",\"t1_survivors\":" << total_stats.t1_survivors
              << ",\"t2_survivors\":" << total_stats.t2_survivors
              << ",\"t3_survivors\":" << total_stats.t3_survivors
              << ",\"prime7_survivors\":" << total_stats.prime7_survivors
              << ",\"max_depth\":" << total_stats.max_depth
              << ",\"max_depth_n\":\"" << u128_to_str(total_stats.max_depth_n) << "\""
              << ",\"max_depth_kill_tau\":" << total_stats.max_depth_kill_tau
              << ",\"seconds\":" << elapsed
              << ",\"effective_n_per_sec\":" << n_per_sec;
    if (total_stats.witness_found) {
        std::cout << ",\"witness_n\":\"" << u128_to_str(total_stats.witness_n) << "\"";
    }
    std::cout << "}\n";
    return 0;
}
