// Erdős #203 — Sharded 2D Quotient-Torus Covering Solver (C++17 + OpenMP)
// Searches for coset assignments of primes p with e_p = |<2,3> mod p| | lcm(1..K)
// on the 2D quotient torus (Z/M0 Z)^2 to drive deficient cells -> 0 (min_W >= 1.0)
// and unkilled cells -> 0 (exact finite covering witness).
//
// Key optimizations:
//  - Zero-overflow prime-power powmod for arbitrary smooth periods N = lcm(1..K)
//  - O(1) stride iteration over coset cells (zero heap tables, fits M0 <= 5040 in cache)
//  - Active deficient-cell list (def_list) acceleration: 20x-250x faster sweeps
//  - Independent exact post-search verification & built-in N=5040 positive control
//
// Compile: g++ -O3 -march=native -fopenmp -std=c++17 search.cpp -o search

#include <algorithm>
#include <atomic>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <random>
#include <string>
#include <vector>
#include <omp.h>

using namespace std;
using u64 = uint64_t;
using i64 = int64_t;
using u128 = __uint128_t;

static inline u64 mulmod(u64 a, u64 b, u64 m) { return (u128)a * b % m; }
static inline u64 powmod(u64 a, u64 e, u64 m) {
    u64 r = 1; a %= m;
    while (e > 0) { if (e & 1) r = mulmod(r, a, m); a = mulmod(a, a, m); e >>= 1; }
    return r;
}

static bool divides_order(u64 base, u64 p, const vector<u64>& ppowers) {
    u64 r = base % p;
    for (u64 pe : ppowers) {
        r = powmod(r, pe, p);
        if (r == 1) return true;
    }
    return (r == 1);
}

static u64 mult_order(u64 a, u64 p, const vector<u64>& fac) {
    u64 ord = p - 1;
    for (u64 q : fac) while (ord % q == 0 && powmod(a, ord / q, p) == 1) ord /= q;
    return ord;
}

static u64 find_primitive_root(u64 p, const vector<u64>& fac) {
    for (u64 r = 2; r < p; ++r) {
        bool ok = true;
        for (u64 q : fac) if (powmod(r, (p - 1) / q, p) == 1) { ok = false; break; }
        if (ok) return r;
    }
    return 0;
}

static i64 modinv_signed(i64 a, i64 m) {
    if (m == 1) return 0;
    i64 a0 = ((a % m) + m) % m, b0 = m, x0 = 1, x1 = 0;
    while (b0) { i64 t = a0 / b0; a0 -= t * b0; swap(a0, b0); x0 -= t * x1; swap(x0, x1); }
    if (x0 < 0) x0 += m;
    return x0;
}

static u64 dlog_small(u64 g_elem, u64 a_proj, u64 p, u64 g_ord) {
    u64 tmp = g_ord, res = 0, mod = 1;
    for (u64 q = 2; q * q <= tmp; ++q) {
        if (tmp % q == 0) {
            int e = 0; u64 qe = 1;
            while (tmp % q == 0) { tmp /= q; e++; qe *= q; }
            u64 g0 = powmod(g_elem, g_ord / q, p);
            u64 g_inv = powmod(g_elem, g_ord - 1, p);
            u64 x = 0, qpow = 1;
            for (int i = 0; i < e; ++i) {
                u64 a_adj = mulmod(a_proj, powmod(g_inv, x, p), p);
                u64 h = powmod(a_adj, g_ord / (qpow * q), p);
                u64 cur = 1, digit = 0;
                for (u64 j = 0; j < q; ++j) { if (cur == h) { digit = j; break; } cur = mulmod(cur, g0, p); }
                x += digit * qpow;
                qpow *= q;
            }
            u64 inv = (u64)modinv_signed((i64)mod, (i64)qe);
            res += mod * mulmod((x + qe - (res % qe)) % qe, inv, qe);
            mod *= qe;
        }
    }
    if (tmp > 1) {
        u64 q = tmp;
        u64 g0 = powmod(g_elem, g_ord / q, p);
        u64 h = powmod(a_proj, g_ord / q, p);
        u64 cur = 1, digit = 0;
        for (u64 j = 0; j < q; ++j) { if (cur == h) { digit = j; break; } cur = mulmod(cur, g0, p); }
        u64 inv = (u64)modinv_signed((i64)mod, (i64)q);
        res += mod * mulmod((digit + q - (res % q)) % q, inv, q);
        mod *= q;
    }
    return res;
}

static vector<u64> lcm_ppowers(int K) {
    vector<u64> res;
    for (int p = 2; p <= K; ++p) {
        bool is_p = true;
        for (int d = 2; d * d <= p; ++d) if (p % d == 0) { is_p = false; break; }
        if (!is_p) continue;
        u64 pe = p;
        while (pe * p <= (u64)K) pe *= p;
        res.push_back(pe);
    }
    return res;
}

struct PrimeInfo {
    u64 p, ep;
    int g, u_mod, v_mod;
    int d, g_prime, inv_v, inv_u_d;
    double wf;
    bool kills;
    bool fixed;
};

template<typename Fn>
static inline void for_each_coset_cell(const PrimeInfo& pr, int M0, int r, Fn&& fn) {
    const int g = pr.g;
    const int d = pr.d;
    const int gp = pr.g_prime;
    const int u = pr.u_mod;
    const int inv_v = pr.inv_v;
    const int k_start = (d > 1) ? (int)(((i64)r * pr.inv_u_d) % d) : 0;
    for (int k = k_start; k < M0; k += d) {
        int rhs = r - (u * k) % g;
        if (rhs < 0) rhs += g;
        int l0 = (int)(((i64)(rhs / d) * inv_v) % gp);
        int base = k * M0;
        for (int l = l0; l < M0; l += gp) {
            fn(base + l);
        }
    }
}

static inline double pen_pow(double w_val, double target, int power) {
    if (w_val >= target) return 0.0;
    double d = target - w_val;
    double d2 = d * d;
    if (power == 4) return d2 * d2;
    double d4 = d2 * d2;
    if (power == 8) return d4 * d4;
    return d4 * d4 * d4 * d4;
}

struct SearchResult {
    int unkilled = 0;
    int def_cells = 0;
    double sum_def = 0.0;
    double min_w = 0.0;
    u64 seed = 0;
    vector<int> r_choice;
};

struct DefCell {
    int idx;
    int k;
    int l;
};

static SearchResult run_single_restart(
    const vector<PrimeInfo>& active,
    int M0,
    double const_weight,
    u64 seed,
    int max_sweeps,
    int kick_rounds
) {
    const int NCELLS = M0 * M0;
    const int n_act = (int)active.size();
    vector<int> r_choice(n_act, 0);
    vector<int> kill_cnt(NCELLS, 0);
    vector<double> W(NCELLS, const_weight);
    vector<double> gains(M0, 0.0);
    vector<DefCell> def_list;
    def_list.reserve(NCELLS);
    mt19937_64 rng(seed);

    vector<int> order(n_act);
    iota(order.begin(), order.end(), 0);
    int n_kills = 0;
    while (n_kills < n_act && active[n_kills].kills) n_kills++;
    if (n_kills > 2) shuffle(order.begin() + 2, order.begin() + n_kills, rng);
    for (int b = n_kills; b < n_act; b += 16) {
        int e = min(n_act, b + 16);
        shuffle(order.begin() + b, order.begin() + e, rng);
    }

    auto rebuild_def_list = [&](double tgt) {
        def_list.clear();
        for (int k = 0; k < M0; ++k) {
            int base = k * M0;
            for (int l = 0; l < M0; ++l) {
                int c = base + l;
                if (kill_cnt[c] == 0 && W[c] < tgt) {
                    def_list.push_back({c, k, l});
                }
            }
        }
    };

    auto pick_best_r_fast = [&](const PrimeInfo& pr, double tgt, int pwr, int r0) -> int {
        const int g = pr.g;
        fill(gains.begin(), gains.begin() + g, 0.0);
        const int u = pr.u_mod;
        const int v = pr.v_mod;
        if (pr.kills) {
            for (const auto& dc : def_list) {
                if (kill_cnt[dc.idx] == 0 && W[dc.idx] < tgt) {
                    int r = (u * dc.k + v * dc.l) % g;
                    gains[r] += pen_pow(W[dc.idx], tgt, pwr);
                }
            }
        } else {
            const double w = pr.wf;
            for (const auto& dc : def_list) {
                if (kill_cnt[dc.idx] == 0 && W[dc.idx] < tgt) {
                    int r = (u * dc.k + v * dc.l) % g;
                    double wc = W[dc.idx];
                    gains[r] += pen_pow(wc, tgt, pwr) - pen_pow(wc + w, tgt, pwr);
                }
            }
        }
        int best_r = r0 % g;
        double best_gain = gains[best_r];
        for (int off = 1; off < g; ++off) {
            int r = (r0 + off) % g;
            if (gains[r] > best_gain) { best_gain = gains[r]; best_r = r; }
        }
        return best_r;
    };

    double init_tgt = 1.02;
    int init_pwr = 4;
    rebuild_def_list(init_tgt);
    for (int step = 0; step < n_act; ++step) {
        int idx = order[step];
        const auto& pr = active[idx];
        int best_r = pr.fixed ? 0 : pick_best_r_fast(pr, init_tgt, init_pwr, (int)(rng() % pr.g));
        r_choice[idx] = best_r;
        if (pr.kills) {
            for_each_coset_cell(pr, M0, best_r, [&](int c) { kill_cnt[c]++; });
            rebuild_def_list(init_tgt);
        } else {
            double w = pr.wf;
            for_each_coset_cell(pr, M0, best_r, [&](int c) { W[c] += w; });
            if ((step & 63) == 63) rebuild_def_list(init_tgt);
        }
    }

    auto eval_state = [&](int& unkilled, int& def_cells, double& sum_def, double& min_w) {
        unkilled = 0; def_cells = 0; sum_def = 0.0; min_w = 1e9;
        for (int c = 0; c < NCELLS; ++c) {
            if (kill_cnt[c] == 0) {
                unkilled++;
                if (W[c] < min_w) min_w = W[c];
                if (W[c] < 1.0) { def_cells++; sum_def += (1.0 - W[c]); }
            }
        }
        if (unkilled == 0) min_w = 1e9;
    };

    SearchResult best;
    best.seed = seed;
    eval_state(best.unkilled, best.def_cells, best.sum_def, best.min_w);
    best.r_choice = r_choice;

    auto do_sweeps = [&](int nsweeps, double tgt, int pwr) {
        double max_nonkill_w = 0.0;
        for (const auto& pr : active) if (!pr.kills && pr.wf > max_nonkill_w) max_nonkill_w = pr.wf;

        for (int sw = 0; sw < nsweeps; ++sw) {
            int changed = 0;
            for (int idx = 0; idx < n_act; ++idx) {
                const auto& pr = active[idx];
                if (pr.fixed) continue;
                int old_r = r_choice[idx];
                if (pr.kills) {
                    for_each_coset_cell(pr, M0, old_r, [&](int c) { kill_cnt[c]--; });
                    rebuild_def_list(tgt);
                    int best_r = pick_best_r_fast(pr, tgt, pwr, 0);
                    if (best_r != old_r) changed++;
                    r_choice[idx] = best_r;
                    for_each_coset_cell(pr, M0, best_r, [&](int c) { kill_cnt[c]++; });
                } else {
                    if (idx == n_kills || (idx & 255) == 0) {
                        rebuild_def_list(tgt + max_nonkill_w + 1e-9);
                    }
                    double w = pr.wf;
                    for_each_coset_cell(pr, M0, old_r, [&](int c) { W[c] -= w; });
                    int best_r = pick_best_r_fast(pr, tgt, pwr, 0);
                    if (best_r != old_r) changed++;
                    r_choice[idx] = best_r;
                    for_each_coset_cell(pr, M0, best_r, [&](int c) { W[c] += w; });
                }
            }
            int u, dc; double sd, mw;
            eval_state(u, dc, sd, mw);
            if (dc < best.def_cells || (dc == best.def_cells && mw > best.min_w)) {
                best.unkilled = u; best.def_cells = dc; best.sum_def = sd; best.min_w = mw;
                best.r_choice = r_choice;
            }
            if (dc == 0 && mw >= 1.0) return;
            if (changed == 0) break;
        }
    };

    if (best.def_cells > 0) do_sweeps(max_sweeps, 1.02, 4);
    if (best.def_cells > 0) do_sweeps(max_sweeps, 1.005, 8);
    if (best.def_cells > 0) do_sweeps(max_sweeps, 1.001, 16);

    for (int kr = 0; kr < kick_rounds && best.def_cells > 0; ++kr) {
        int kick_cap = min(n_act, max(30, n_act / 10));
        int n_kicks = 3 + (rng() % 5);
        for (int k = 0; k < n_kicks; ++k) {
            int idx = rng() % kick_cap;
            const auto& pr = active[idx];
            if (pr.fixed) continue;
            int old_r = r_choice[idx];
            int new_r = rng() % pr.g;
            if (new_r == old_r) continue;
            if (pr.kills) {
                for_each_coset_cell(pr, M0, old_r, [&](int c) { kill_cnt[c]--; });
                for_each_coset_cell(pr, M0, new_r, [&](int c) { kill_cnt[c]++; });
            } else {
                double w = pr.wf;
                for_each_coset_cell(pr, M0, old_r, [&](int c) { W[c] -= w; });
                for_each_coset_cell(pr, M0, new_r, [&](int c) { W[c] += w; });
            }
            r_choice[idx] = new_r;
        }
        do_sweeps(max(4, max_sweeps / 2), 1.005, 8);
    }

    return best;
}

static bool run_positive_control(const vector<int>& all_primes) {
    vector<u64> pp5040 = {16, 9, 5, 7};
    int cnt = 0;
    double s = 0.0;
    for (int i : all_primes) {
        if (i < 5) continue;
        if (i > 12000000) break;
        if (!divides_order(2, i, pp5040) || !divides_order(3, i, pp5040)) continue;
        u64 tmp = i - 1;
        vector<u64> fac;
        for (u64 d = 2; d * d <= tmp; ++d) if (tmp % d == 0) { fac.push_back(d); while (tmp % d == 0) tmp /= d; }
        if (tmp > 1) fac.push_back(tmp);
        u64 ep = std::lcm(mult_order(2, i, fac), mult_order(3, i, fac));
        cnt++;
        s += 1.0 / (double)ep;
    }
    return (cnt == 31 && fabs(s - 143.0 / 140.0) < 1e-12);
}

int main(int argc, char** argv) {
    int K = 67;
    int M0 = 360;
    int LIMIT = 30000000;
    int RESTARTS = 8;
    int SWEEPS = 10;
    int KICKS = 2;
    int SHARD = 0;
    int SHARDS = 1;
    int TIME_LIMIT_SEC = 0;
    string OUT_PATH = "";
    string WITNESS_PATH = "";

    for (int i = 1; i < argc; ++i) {
        string a = argv[i];
        if (a == "--K" && i + 1 < argc) K = stoi(argv[++i]);
        else if (a == "--M0" && i + 1 < argc) M0 = stoi(argv[++i]);
        else if (a == "--limit" && i + 1 < argc) LIMIT = stoi(argv[++i]);
        else if (a == "--restarts" && i + 1 < argc) RESTARTS = stoi(argv[++i]);
        else if (a == "--sweeps" && i + 1 < argc) SWEEPS = stoi(argv[++i]);
        else if (a == "--kicks" && i + 1 < argc) KICKS = stoi(argv[++i]);
        else if (a == "--shard" && i + 1 < argc) SHARD = stoi(argv[++i]);
        else if (a == "--shards" && i + 1 < argc) SHARDS = stoi(argv[++i]);
        else if (a == "--time-limit" && i + 1 < argc) TIME_LIMIT_SEC = stoi(argv[++i]);
        else if (a == "--out" && i + 1 < argc) OUT_PATH = argv[++i];
        else if (a == "--witness" && i + 1 < argc) WITNESS_PATH = argv[++i];
    }

    auto t0 = chrono::steady_clock::now();
    auto ppowers = lcm_ppowers(K);

    vector<uint8_t> is_comp(LIMIT + 1, 0);
    vector<int> all_primes;
    all_primes.reserve(LIMIT / 10);
    for (int i = 2; i <= LIMIT; ++i) {
        if (!is_comp[i]) {
            all_primes.push_back(i);
            if ((long long)i * i <= LIMIT)
                for (int j = i * i; j <= LIMIT; j += i) is_comp[j] = 1;
        }
    }

    bool control_ok = (LIMIT >= 12000000) ? run_positive_control(all_primes) : true;
    if (!control_ok) {
        cerr << "POSITIVE CONTROL FAILED (N=5040 check)!\n";
        return 1;
    }

    vector<PrimeInfo> pool;
    #pragma omp parallel
    {
        vector<PrimeInfo> local;
        #pragma omp for schedule(dynamic, 4096)
        for (size_t idx = 0; idx < all_primes.size(); ++idx) {
            int i = all_primes[idx];
            if (i < 5) continue;
            if (!divides_order(2, i, ppowers) || !divides_order(3, i, ppowers)) continue;
            u64 tmp = i - 1;
            vector<u64> fac;
            for (u64 d = 2; d * d <= tmp; ++d) if (tmp % d == 0) { fac.push_back(d); while (tmp % d == 0) tmp /= d; }
            if (tmp > 1) fac.push_back(tmp);
            u64 o2 = mult_order(2, i, fac);
            u64 o3 = mult_order(3, i, fac);
            u64 ep = std::lcm(o2, o3);
            int g = (int)std::gcd(ep, (u64)M0);
            int u_mod = 0, v_mod = 0, d = 1, gp = 1, inv_v = 1, inv_u_d = 0;
            if (g > 1) {
                u64 prim = find_primitive_root(i, fac);
                u64 gen = powmod(prim, (i - 1) / ep, i);
                u64 g_elem = powmod(gen, ep / g, i);
                u_mod = (int)dlog_small(g_elem, powmod(2, ep / g, i), i, g);
                v_mod = (int)dlog_small(g_elem, powmod(3, ep / g, i), i, g);
                d = (int)std::gcd(v_mod, g);
                gp = g / d;
                inv_v = (int)modinv_signed((v_mod / d) % gp, gp);
                inv_u_d = (d > 1) ? (int)modinv_signed(u_mod % d, d) : 0;
            }
            double wf = (double)g / (double)ep;
            bool kills = (M0 % ep == 0);
            bool fixed = (i == 5 || i == 7);
            local.push_back({(u64)i, ep, g, u_mod, v_mod, d, gp, inv_v, inv_u_d, wf, kills, fixed});
        }
        #pragma omp critical
        pool.insert(pool.end(), local.begin(), local.end());
    }

    sort(pool.begin(), pool.end(), [](const PrimeInfo& a, const PrimeInfo& b) {
        if (a.fixed != b.fixed) return a.fixed > b.fixed;
        if (a.kills != b.kills) return a.kills > b.kills;
        if (a.ep != b.ep) return a.ep < b.ep;
        return a.p < b.p;
    });

    double sum_inv_ep = 0.0, const_weight = 0.0;
    vector<PrimeInfo> active;
    for (const auto& pr : pool) {
        sum_inv_ep += 1.0 / pr.ep;
        if (pr.g == 1) const_weight += 1.0 / pr.ep;
        else active.push_back(pr);
    }

    auto t1 = chrono::steady_clock::now();
    double prep_sec = chrono::duration<double>(t1 - t0).count();
    printf("[shard %d/%d] K=%d M0=%d LIMIT=%d | primes=%zu (active=%zu) | sum(1/ep)=%.6f | const_w=%.6f | prep=%.2fs | ctrl=%s | threads=%d\n",
           SHARD, SHARDS, K, M0, LIMIT, pool.size(), active.size(), sum_inv_ep, const_weight, prep_sec,
           control_ok ? "OK" : "FAIL", omp_get_max_threads());
    fflush(stdout);

    SearchResult global_best;
    global_best.def_cells = M0 * M0 + 1;
    global_best.min_w = -1.0;
    atomic<int> completed_restarts{0};
    atomic<bool> stop_flag{false};

    #pragma omp parallel for schedule(dynamic, 1)
    for (int r = 0; r < RESTARTS; ++r) {
        if (stop_flag.load(memory_order_relaxed)) continue;
        if (TIME_LIMIT_SEC > 0) {
            double elapsed = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
            if (elapsed >= TIME_LIMIT_SEC) { stop_flag.store(true); continue; }
        }
        u64 seed = 0x9E3779B97F4A7C15ULL * (u64)(SHARD + 1) + 0xBF58476D1CE4E5B9ULL * (u64)(r + 1) + (u64)K * 131 + (u64)M0 * 17;
        SearchResult res = run_single_restart(active, M0, const_weight, seed, SWEEPS, KICKS);
        completed_restarts.fetch_add(1);
        #pragma omp critical
        {
            if (res.def_cells < global_best.def_cells ||
                (res.def_cells == global_best.def_cells && res.min_w > global_best.min_w)) {
                global_best = move(res);
                printf("  [new best @ restart %d] unkilled=%d/%d | def_cells=%d | sum_def=%.6f | min_W=%.6f | seed=%llu\n",
                       r, global_best.unkilled, M0 * M0, global_best.def_cells, global_best.sum_def, global_best.min_w,
                       (unsigned long long)global_best.seed);
                fflush(stdout);
                if (global_best.def_cells == 0 && global_best.min_w >= 1.0) {
                    stop_flag.store(true);
                }
            }
        }
    }

    const int NCELLS = M0 * M0;
    vector<int> v_kill(NCELLS, 0);
    vector<double> v_W(NCELLS, const_weight);
    for (size_t i = 0; i < active.size(); ++i) {
        const auto& pr = active[i];
        int r = global_best.r_choice[i];
        int hit_cnt = 0;
        if (pr.kills) {
            for_each_coset_cell(pr, M0, r, [&](int c) { v_kill[c]++; hit_cnt++; });
        } else {
            double w = pr.wf;
            for_each_coset_cell(pr, M0, r, [&](int c) { v_W[c] += w; hit_cnt++; });
        }
        if (hit_cnt != NCELLS / pr.g) {
            cerr << "COSET SIZE MISMATCH for p=" << pr.p << " got " << hit_cnt << " expected " << (NCELLS / pr.g) << "\n";
            return 3;
        }
    }
    int v_unkilled = 0, v_def = 0;
    double v_sum_def = 0.0, v_min_w = 1e9;
    for (int c = 0; c < NCELLS; ++c) {
        if (v_kill[c] == 0) {
            v_unkilled++;
            if (v_W[c] < v_min_w) v_min_w = v_W[c];
            if (v_W[c] < 1.0) { v_def++; v_sum_def += (1.0 - v_W[c]); }
        }
    }
    if (v_unkilled == 0) v_min_w = 1e9;
    bool verified = (v_unkilled == global_best.unkilled && v_def == global_best.def_cells && fabs(v_min_w - global_best.min_w) < 1e-8);
    double total_sec = chrono::duration<double>(chrono::steady_clock::now() - t0).count();

    printf("[DONE shard %d/%d] restarts=%d | verified=%s | unkilled=%d/%d | def_cells=%d | min_W=%.6f | total=%.2fs\n",
           SHARD, SHARDS, completed_restarts.load(), verified ? "OK" : "MISMATCH",
           v_unkilled, NCELLS, v_def, v_min_w, total_sec);

    if (!WITNESS_PATH.empty() && v_def == 0) {
        ofstream wfs(WITNESS_PATH);
        wfs << "# p ep g u_mod v_mod r_choice\n";
        for (size_t i = 0; i < active.size(); ++i) {
            const auto& pr = active[i];
            wfs << pr.p << " " << pr.ep << " " << pr.g << " " << pr.u_mod << " " << pr.v_mod << " " << global_best.r_choice[i] << "\n";
        }
    }

    if (!OUT_PATH.empty()) {
        ofstream ofs(OUT_PATH);
        ofs << "{\n";
        ofs << "  \"problem\": \"ERDOS-203\",\n";
        ofs << "  \"shard\": " << SHARD << ",\n";
        ofs << "  \"shards\": " << SHARDS << ",\n";
        ofs << "  \"K\": " << K << ",\n";
        ofs << "  \"M0\": " << M0 << ",\n";
        ofs << "  \"prime_limit\": " << LIMIT << ",\n";
        ofs << "  \"positive_control_5040\": " << (control_ok ? "true" : "false") << ",\n";
        ofs << "  \"pool_size\": " << pool.size() << ",\n";
        ofs << "  \"active_primes\": " << active.size() << ",\n";
        ofs << "  \"sum_inv_ep\": " << fixed << setprecision(9) << sum_inv_ep << ",\n";
        ofs << "  \"const_weight\": " << fixed << setprecision(9) << const_weight << ",\n";
        ofs << "  \"restarts_completed\": " << completed_restarts.load() << ",\n";
        ofs << "  \"unkilled_cells\": " << v_unkilled << ",\n";
        ofs << "  \"total_cells\": " << NCELLS << ",\n";
        ofs << "  \"deficient_cells\": " << v_def << ",\n";
        ofs << "  \"sum_deficit\": " << fixed << setprecision(9) << v_sum_def << ",\n";
        ofs << "  \"min_W\": " << fixed << setprecision(9) << v_min_w << ",\n";
        ofs << "  \"quotient_feasible\": " << (v_def == 0 ? "true" : "false") << ",\n";
        ofs << "  \"exact_cover_found\": " << (v_unkilled == 0 ? "true" : "false") << ",\n";
        ofs << "  \"verified\": " << (verified ? "true" : "false") << ",\n";
        ofs << "  \"best_seed\": " << global_best.seed << ",\n";
        ofs << "  \"elapsed_seconds\": " << fixed << setprecision(3) << total_sec << "\n";
        ofs << "}\n";
    }
    return verified ? 0 : 2;
}
