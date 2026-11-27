#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <numeric>
#include <omp.h>
#include <random>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

using namespace std;

static constexpr int MAXN = 192;

struct Mask {
    uint64_t w[3];
    inline Mask() { w[0] = w[1] = w[2] = 0; }
    inline void set(int v) { w[v >> 6] |= (1ULL << (v & 63)); }
    inline void clear(int v) { w[v >> 6] &= ~(1ULL << (v & 63)); }
    inline bool test(int v) const { return (w[v >> 6] >> (v & 63)) & 1ULL; }
    inline bool disjoint(const Mask& o) const {
        return ((w[0] & o.w[0]) | (w[1] & o.w[1]) | (w[2] & o.w[2])) == 0;
    }
    inline Mask with(int v) const {
        Mask r = *this;
        r.set(v);
        return r;
    }
};

struct Graph {
    int n = 0;
    int deg[MAXN]{};
    int adj[MAXN][3]{};
    Mask adj_mask[MAXN]{};

    void clear(int n_) {
        n = n_;
        for (int i = 0; i < n; ++i) {
            deg[i] = 0;
            adj_mask[i] = Mask();
        }
    }
    inline bool has_edge(int u, int v) const { return adj_mask[u].test(v); }
    inline void add_edge(int u, int v) {
        adj[u][deg[u]++] = v;
        adj[v][deg[v]++] = u;
        adj_mask[u].set(v);
        adj_mask[v].set(u);
    }
    inline void remove_edge(int u, int v) {
        for (int i = 0; i < deg[u]; ++i) {
            if (adj[u][i] == v) { adj[u][i] = adj[u][--deg[u]]; break; }
        }
        for (int i = 0; i < deg[v]; ++i) {
            if (adj[v][i] == u) { adj[v][i] = adj[v][--deg[v]]; break; }
        }
        adj_mask[u].clear(v);
        adj_mask[v].clear(u);
    }
};

struct Scratch {
    vector<Mask> buckets[MAXN];
    vector<int> touched;
    vector<Mask> b32[MAXN];
    vector<int> touched32;

    Scratch() {
        touched.reserve(MAXN);
        touched32.reserve(MAXN);
        for (int i = 0; i < MAXN; ++i) buckets[i].reserve(32);
    }
    inline void reset_buckets() {
        for (int v : touched) buckets[v].clear();
        touched.clear();
    }
    inline void reset_b32() {
        for (int v : touched32) b32[v].clear();
        touched32.clear();
    }
};

static inline int count_c4_edge(const Graph& g, int u, int v) {
    int cnt = 0;
    for (int i = 0; i < g.deg[u]; ++i) {
        int x = g.adj[u][i];
        if (x == v) continue;
        for (int j = 0; j < g.deg[v]; ++j) {
            int y = g.adj[v][j];
            if (y == u || y == x) continue;
            if (g.has_edge(x, y)) ++cnt;
        }
    }
    return cnt;
}

static void dfs_collect(const Graph& g, int cur, int rem, int forbid_end,
                        const Mask& vis, const Mask& interior, Scratch& sc) {
    const int d = g.deg[cur];
    if (rem == 1) {
        for (int i = 0; i < d; ++i) {
            int nxt = g.adj[cur][i];
            if (nxt == forbid_end || vis.test(nxt)) continue;
            if (sc.buckets[nxt].empty()) sc.touched.push_back(nxt);
            sc.buckets[nxt].push_back(interior);
        }
        return;
    }
    for (int i = 0; i < d; ++i) {
        int nxt = g.adj[cur][i];
        if (nxt == forbid_end || vis.test(nxt)) continue;
        dfs_collect(g, nxt, rem - 1, forbid_end, vis.with(nxt), interior.with(nxt), sc);
    }
}

static int dfs_match(const Graph& g, int cur, int rem, int forbid_end,
                     const Mask& vis, const Mask& interior, const Scratch& sc) {
    const int d = g.deg[cur];
    if (rem == 1) {
        int total = 0;
        for (int i = 0; i < d; ++i) {
            int nxt = g.adj[cur][i];
            if (nxt == forbid_end || vis.test(nxt)) continue;
            for (const Mask& m : sc.buckets[nxt]) {
                if (m.disjoint(interior)) ++total;
            }
        }
        return total;
    }
    int total = 0;
    for (int i = 0; i < d; ++i) {
        int nxt = g.adj[cur][i];
        if (nxt == forbid_end || vis.test(nxt)) continue;
        total += dfs_match(g, nxt, rem - 1, forbid_end, vis.with(nxt), interior.with(nxt), sc);
    }
    return total;
}

static int count_c8_edge(const Graph& g, int u, int v, Scratch& sc) {
    sc.reset_buckets();
    Mask vu; vu.set(u);
    Mask empty;
    dfs_collect(g, u, 3, v, vu, empty, sc);
    if (sc.touched.empty()) return 0;
    Mask vv; vv.set(v);
    return dfs_match(g, v, 4, u, vv, empty, sc);
}

static int count_c16_edge(const Graph& g, int u, int v, Scratch& sc) {
    sc.reset_buckets();
    Mask vu; vu.set(u);
    Mask empty;
    dfs_collect(g, u, 7, v, vu, empty, sc);
    if (sc.touched.empty()) return 0;
    Mask vv; vv.set(v);
    return dfs_match(g, v, 8, u, vv, empty, sc);
}

static void dfs_collect32(const Graph& g, int cur, int rem, int forbid_end,
                          const Mask& vis, const Mask& interior, Scratch& sc) {
    const int d = g.deg[cur];
    if (rem == 1) {
        for (int i = 0; i < d; ++i) {
            int nxt = g.adj[cur][i];
            if (nxt == forbid_end || vis.test(nxt)) continue;
            if (sc.b32[nxt].empty()) sc.touched32.push_back(nxt);
            sc.b32[nxt].push_back(interior);
        }
        return;
    }
    for (int i = 0; i < d; ++i) {
        int nxt = g.adj[cur][i];
        if (nxt == forbid_end || vis.test(nxt)) continue;
        dfs_collect32(g, nxt, rem - 1, forbid_end, vis.with(nxt), interior.with(nxt), sc);
    }
}

static void dfs_match32(const Graph& g, int cur, int rem, int forbid_end,
                        const Mask& vis, const Mask& interior, const Scratch& sc,
                        int cap, int& total) {
    if (cap > 0 && total >= cap) return;
    const int d = g.deg[cur];
    if (rem == 1) {
        for (int i = 0; i < d; ++i) {
            int nxt = g.adj[cur][i];
            if (nxt == forbid_end || vis.test(nxt)) continue;
            for (const Mask& m : sc.b32[nxt]) {
                if (m.disjoint(interior)) {
                    ++total;
                    if (cap > 0 && total >= cap) return;
                }
            }
        }
        return;
    }
    for (int i = 0; i < d; ++i) {
        int nxt = g.adj[cur][i];
        if (nxt == forbid_end || vis.test(nxt)) continue;
        dfs_match32(g, nxt, rem - 1, forbid_end, vis.with(nxt), interior.with(nxt), sc, cap, total);
        if (cap > 0 && total >= cap) return;
    }
}

static int count_c32_edge(const Graph& g, int u, int v, Scratch& sc, int cap = 1) {
    sc.reset_b32();
    Mask vu; vu.set(u);
    Mask empty;
    dfs_collect32(g, u, 15, v, vu, empty, sc);
    if (sc.touched32.empty()) return 0;
    Mask vv; vv.set(v);
    int total = 0;
    dfs_match32(g, v, 16, u, vv, empty, sc, cap, total);
    return total;
}

static void count_all_4_8_16(const Graph& g, long long& c4, long long& c8, long long& c16, Scratch& sc) {
    long long s4 = 0, s8 = 0, s16 = 0;
    for (int u = 0; u < g.n; ++u) {
        for (int i = 0; i < g.deg[u]; ++i) {
            int v = g.adj[u][i];
            if (u < v) {
                s4 += count_c4_edge(g, u, v);
                s8 += count_c8_edge(g, u, v, sc);
                s16 += count_c16_edge(g, u, v, sc);
            }
        }
    }
    c4 = s4 / 4; c8 = s8 / 8; c16 = s16 / 16;
}

static bool is_connected_fast(const Graph& g) {
    bool vis[MAXN]{};
    int q[MAXN];
    int head = 0, tail = 0;
    vis[0] = true; q[tail++] = 0;
    while (head < tail) {
        int u = q[head++];
        for (int i = 0; i < g.deg[u]; ++i) {
            int v = g.adj[u][i];
            if (!vis[v]) { vis[v] = true; q[tail++] = v; }
        }
    }
    return tail == g.n;
}

static bool has_cycle_of_len_dfs(const Graph& g, int target_len, long long node_limit, bool& exhausted) {
    if (g.n < target_len) { exhausted = true; return false; }
    long long nodes = 0;
    exhausted = true;
    bool in_path[MAXN]{};
    for (int s = 0; s < g.n; ++s) {
        in_path[s] = true;
        auto dfs = [&](auto&& self, int cur, int depth) -> bool {
            if (++nodes > node_limit) { exhausted = false; return false; }
            if (depth == target_len - 1) return g.has_edge(cur, s);
            const int d = g.deg[cur];
            for (int i = 0; i < d; ++i) {
                int nxt = g.adj[cur][i];
                if (nxt <= s || in_path[nxt]) continue;
                in_path[nxt] = true;
                if (self(self, nxt, depth + 1)) { in_path[nxt] = false; return true; }
                in_path[nxt] = false;
                if (!exhausted) return false;
            }
            return false;
        };
        if (dfs(dfs, s, 0)) { in_path[s] = false; return true; }
        in_path[s] = false;
        if (!exhausted) return false;
    }
    return false;
}

static bool generate_random_cubic(Graph& g, int n, mt19937_64& rng) {
    if (n % 2 != 0) return false;
    vector<int> stubs(3 * n);
    for (int attempt = 0; attempt < 10000; ++attempt) {
        g.clear(n);
        for (int v = 0; v < n; ++v) {
            stubs[3 * v] = v; stubs[3 * v + 1] = v; stubs[3 * v + 2] = v;
        }
        shuffle(stubs.begin(), stubs.end(), rng);
        bool ok = true;
        for (int i = 0; i < 3 * n; i += 2) {
            int u = stubs[i], v = stubs[i + 1];
            if (u == v || g.has_edge(u, v)) { ok = false; break; }
            g.add_edge(u, v);
        }
        if (ok && is_connected_fast(g)) return true;
    }
    return false;
}

static string graph_to_edgelist(const Graph& g) {
    ostringstream oss;
    oss << "[";
    bool first = true;
    for (int u = 0; u < g.n; ++u) {
        for (int i = 0; i < g.deg[u]; ++i) {
            int v = g.adj[u][i];
            if (u < v) {
                if (!first) oss << ",";
                first = false;
                oss << "(" << u << "," << v << ")";
            }
        }
    }
    oss << "]";
    return oss.str();
}

struct SeedResult {
    int seed = 0;
    long long best_e4816 = 1e18;
    long long best_c4 = 0, best_c8 = 0, best_c16 = 0;
    int best_c32_edges = -1;
    int c64_status = -1;
    int c128_status = -1;
    bool hit_zero_4816 = false;
    bool hit_full_ce = false;
    Graph best_graph;
};

static SeedResult run_seed(int n, int seed, int steps, int c32_polish_steps) {
    mt19937_64 rng(seed);
    Scratch sc;
    Graph g;
    SeedResult res;
    res.seed = seed;
    if (!generate_random_cubic(g, n, rng)) return res;

    long long c4 = 0, c8 = 0, c16 = 0;
    count_all_4_8_16(g, c4, c8, c16, sc);

    auto energy_fn = [](long long x4, long long x8, long long x16) -> long long {
        return 100LL * x4 + 12LL * x8 + 1LL * x16;
    };

    long long curE = energy_fn(c4, c8, c16);
    res.best_e4816 = curE;
    res.best_c4 = c4; res.best_c8 = c8; res.best_c16 = c16;
    res.best_graph = g;

    vector<pair<int,int>> edges;
    edges.reserve(3 * n / 2);
    for (int u = 0; u < n; ++u)
        for (int i = 0; i < g.deg[u]; ++i)
            if (u < g.adj[u][i]) edges.push_back({u, g.adj[u][i]});
    int m = (int)edges.size();

    double T0 = 6.0, T1 = 0.02;
    uniform_real_distribution<double> u01(0.0, 1.0);
    int phase1 = (int)(steps * 0.70);

    for (int step = 0; step < steps; ++step) {
        double T;
        if (step < phase1) {
            T = T0 * pow(T1 / T0, (double)step / (double)phase1);
        } else {
            double f2 = (double)(step - phase1) / (double)(steps - phase1);
            T = 1.5 * pow(0.01 / 1.5, f2);
        }

        int idx1 = (int)(rng() % m);
        int idx2 = (int)(rng() % m);
        if (idx1 == idx2) continue;

        int a = edges[idx1].first, b = edges[idx1].second;
        int c = edges[idx2].first, d = edges[idx2].second;
        if (a == c || a == d || b == c || b == d) continue;
        if (rng() & 1) swap(c, d);
        if (g.has_edge(a, c) || g.has_edge(b, d)) continue;

        long long dc4 = 0, dc8 = 0, dc16 = 0;
        dc4 -= count_c4_edge(g, a, b);
        dc8 -= count_c8_edge(g, a, b, sc);
        dc16 -= count_c16_edge(g, a, b, sc);
        g.remove_edge(a, b);

        dc4 -= count_c4_edge(g, c, d);
        dc8 -= count_c8_edge(g, c, d, sc);
        dc16 -= count_c16_edge(g, c, d, sc);
        g.remove_edge(c, d);

        g.add_edge(a, c);
        dc4 += count_c4_edge(g, a, c);
        dc8 += count_c8_edge(g, a, c, sc);
        dc16 += count_c16_edge(g, a, c, sc);

        g.add_edge(b, d);
        dc4 += count_c4_edge(g, b, d);
        dc8 += count_c8_edge(g, b, d, sc);
        dc16 += count_c16_edge(g, b, d, sc);

        long long n4 = c4 + dc4, n8 = c8 + dc8, n16 = c16 + dc16;
        long long newE = energy_fn(n4, n8, n16);
        long long dE = newE - curE;

        bool accept = (dE <= 0) || (u01(rng) < exp(-(double)dE / T));
        if (accept && !is_connected_fast(g)) accept = false;

        if (accept) {
            c4 = n4; c8 = n8; c16 = n16; curE = newE;
            edges[idx1] = {min(a, c), max(a, c)};
            edges[idx2] = {min(b, d), max(b, d)};

            if (curE < res.best_e4816) {
                res.best_e4816 = curE;
                res.best_c4 = c4; res.best_c8 = c8; res.best_c16 = c16;
                res.best_graph = g;
            }
            if (c4 == 0 && c8 == 0 && c16 == 0) {
                res.hit_zero_4816 = true;
                break;
            }
        } else {
            g.remove_edge(b, d);
            g.remove_edge(a, c);
            g.add_edge(c, d);
            g.add_edge(a, b);
        }
    }

    if (res.hit_zero_4816) {
        g = res.best_graph;
        edges.clear();
        for (int u = 0; u < n; ++u)
            for (int i = 0; i < g.deg[u]; ++i)
                if (u < g.adj[u][i]) edges.push_back({u, g.adj[u][i]});
        m = (int)edges.size();

        auto eval_c32_edges = [&]() -> int {
            int cnt = 0;
            for (const auto& e : edges) {
                if (count_c32_edge(g, e.first, e.second, sc, 1) > 0) ++cnt;
            }
            return cnt;
        };

        int cur32 = eval_c32_edges();
        res.best_c32_edges = cur32;
        res.best_graph = g;

        double Tp0 = 3.0, Tp1 = 0.05;
        for (int ps = 0; ps < c32_polish_steps && cur32 > 0; ++ps) {
            double Tp = Tp0 * pow(Tp1 / Tp0, (double)ps / (double)c32_polish_steps);
            int idx1 = (int)(rng() % m);
            int idx2 = (int)(rng() % m);
            if (idx1 == idx2) continue;
            int a = edges[idx1].first, b = edges[idx1].second;
            int c = edges[idx2].first, d = edges[idx2].second;
            if (a == c || a == d || b == c || b == d) continue;
            if (rng() & 1) swap(c, d);
            if (g.has_edge(a, c) || g.has_edge(b, d)) continue;

            g.remove_edge(a, b);
            g.remove_edge(c, d);
            g.add_edge(a, c);
            bool bad = (count_c4_edge(g, a, c) > 0 || count_c8_edge(g, a, c, sc) > 0 || count_c16_edge(g, a, c, sc) > 0);
            if (!bad) {
                g.add_edge(b, d);
                bad = (count_c4_edge(g, b, d) > 0 || count_c8_edge(g, b, d, sc) > 0 || count_c16_edge(g, b, d, sc) > 0);
                if (!bad && !is_connected_fast(g)) bad = true;
                if (bad) g.remove_edge(b, d);
            }
            if (bad) {
                g.remove_edge(a, c);
                g.add_edge(c, d);
                g.add_edge(a, b);
                continue;
            }

            edges[idx1] = {min(a, c), max(a, c)};
            edges[idx2] = {min(b, d), max(b, d)};
            int new32 = eval_c32_edges();
            int d32 = new32 - cur32;
            if (d32 <= 0 || u01(rng) < exp(-(double)d32 / Tp)) {
                cur32 = new32;
                if (cur32 < res.best_c32_edges) {
                    res.best_c32_edges = cur32;
                    res.best_graph = g;
                }
            } else {
                g.remove_edge(b, d);
                g.remove_edge(a, c);
                g.add_edge(c, d);
                g.add_edge(a, b);
                edges[idx1] = {min(a, b), max(a, b)};
                edges[idx2] = {min(c, d), max(c, d)};
            }
        }

        bool exh64 = false;
        bool f64 = has_cycle_of_len_dfs(res.best_graph, 64, 5000000LL, exh64);
        res.c64_status = f64 ? 1 : (exh64 ? 0 : -1);
        if (n >= 128) {
            bool exh128 = false;
            bool f128 = has_cycle_of_len_dfs(res.best_graph, 128, 5000000LL, exh128);
            res.c128_status = f128 ? 1 : (exh128 ? 0 : -1);
        } else {
            res.c128_status = 0;
        }
        if (res.best_c32_edges == 0 && res.c64_status == 0 && res.c128_status == 0) {
            res.hit_full_ce = true;
        }
    }

    long long vc4 = 0, vc8 = 0, vc16 = 0;
    count_all_4_8_16(res.best_graph, vc4, vc8, vc16, sc);
    res.best_c4 = vc4; res.best_c8 = vc8; res.best_c16 = vc16;
    res.best_e4816 = energy_fn(vc4, vc8, vc16);
    return res;
}

int main(int argc, char** argv) {
    if (argc < 5) {
        cerr << "Usage: " << argv[0] << " <n> <num_seeds> <steps> <c32_polish_steps> [threads]\n";
        return 1;
    }
    int n = atoi(argv[1]);
    int num_seeds = atoi(argv[2]);
    int steps = atoi(argv[3]);
    int c32_polish = atoi(argv[4]);
    int threads = (argc >= 6) ? atoi(argv[5]) : omp_get_max_threads();
    omp_set_num_threads(threads);

    auto t0 = chrono::steady_clock::now();
    vector<SeedResult> results(num_seeds);

    #pragma omp parallel for schedule(dynamic)
    for (int s = 0; s < num_seeds; ++s) {
        int seed = n * 100000 + s + 1;
        results[s] = run_seed(n, seed, steps, c32_polish);
    }

    auto t1 = chrono::steady_clock::now();
    double elapsed = chrono::duration<double>(t1 - t0).count();

    long long minE = 1e18;
    int zero4816_cnt = 0;
    int min_c32_edges = 1e9;
    int full_ce_cnt = 0;
    int best_idx = 0;

    for (int s = 0; s < num_seeds; ++s) {
        const auto& r = results[s];
        cout << "n=" << n << " seed=" << r.seed
             << " bestE=" << r.best_e4816
             << " (C4=" << r.best_c4 << ", C8=" << r.best_c8 << ", C16=" << r.best_c16 << ")"
             << " C32_edges=" << r.best_c32_edges
             << " C64=" << r.c64_status
             << " C128=" << r.c128_status
             << " FULL_CE=" << (r.hit_full_ce ? 1 : 0) << "\n";
        if (r.best_e4816 < minE) { minE = r.best_e4816; best_idx = s; }
        if (r.hit_zero_4816) ++zero4816_cnt;
        if (r.best_c32_edges >= 0 && r.best_c32_edges < min_c32_edges) {
            min_c32_edges = r.best_c32_edges;
            best_idx = s;
        }
        if (r.hit_full_ce) {
            ++full_ce_cnt;
            cout << "!!! CANDIDATE FULL ERDOS #64 COUNTEREXAMPLE !!! n=" << n << " seed=" << r.seed << "\n";
            cout << "EDGES=" << graph_to_edgelist(r.best_graph) << "\n";
        }
    }

    cout << "SUMMARY n=" << n
         << " minE=" << minE
         << " zero4816=" << zero4816_cnt << "/" << num_seeds
         << " minC32_edges=" << (min_c32_edges == (int)1e9 ? -1 : min_c32_edges)
         << " full_CE=" << full_ce_cnt
         << " elapsed=" << elapsed << "s\n";
    if (results[best_idx].best_e4816 == 0) {
        cout << "BEST_ZERO4816_EDGES=" << graph_to_edgelist(results[best_idx].best_graph) << "\n";
    }
    return 0;
}
