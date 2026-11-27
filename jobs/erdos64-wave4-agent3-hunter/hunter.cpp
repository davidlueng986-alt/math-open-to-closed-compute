#include <bits/stdc++.h>
#include <omp.h>
using namespace std;

using u128 = unsigned __int128;
inline int ctz128(u128 x) {
    uint64_t lo = (uint64_t)x;
    if (lo) return __builtin_ctzll(lo);
    return 64 + __builtin_ctzll((uint64_t)(x >> 64));
}

struct Graph {
    int n;
    vector<array<int, 3>> adj;
    vector<u128> mask;
    vector<pair<int,int>> edges;

    Graph(int n_ = 0) : n(n_), adj(n_), mask(n_, 0) {}
    inline bool has_edge(int u, int v) const { return (mask[u] >> v) & (u128)1; }
    inline void add_edge(int u, int v) { mask[u] |= ((u128)1 << v); mask[v] |= ((u128)1 << u); }
    inline void rem_edge(int u, int v) { mask[u] &= ~((u128)1 << v); mask[v] &= ~((u128)1 << u); }

    void rebuild() {
        edges.clear();
        for (int u = 0; u < n; ++u) {
            int idx = 0;
            u128 m = mask[u];
            while (m) {
                int v = ctz128(m);
                adj[u][idx++] = v;
                if (u < v) edges.push_back({u, v});
                m &= m - 1;
            }
        }
    }

    bool is_connected() const {
        u128 vis = (u128)1, q = (u128)1;
        int cnt = 1;
        while (q) {
            int u = ctz128(q); q &= q - 1;
            u128 nxt = mask[u] & ~vis;
            while (nxt) {
                int v = ctz128(nxt); nxt &= nxt - 1;
                vis |= ((u128)1 << v);
                q |= ((u128)1 << v);
                cnt++;
            }
        }
        return cnt == n;
    }

    bool init_random(mt19937_64 &rng) {
        vector<int> stubs(3 * n);
        for (int i = 0; i < n; ++i) stubs[3*i] = stubs[3*i+1] = stubs[3*i+2] = i;
        for (int attempt = 0; attempt < 5000; ++attempt) {
            shuffle(stubs.begin(), stubs.end(), rng);
            fill(mask.begin(), mask.end(), 0);
            bool ok = true;
            for (int i = 0; i < 3 * n; i += 2) {
                int u = stubs[i], v = stubs[i+1];
                if (u == v || has_edge(u, v)) { ok = false; break; }
                add_edge(u, v);
            }
            if (ok && is_connected()) { rebuild(); return true; }
        }
        return false;
    }

    int count_edge_c4(int a, int b) const {
        int cnt = 0;
        u128 ma = mask[a] & ~((u128)1 << b);
        u128 mb = mask[b] & ~((u128)1 << a);
        while (ma) {
            int u = ctz128(ma); ma &= ma - 1;
            u128 common = mask[u] & mb & ~((u128)1 << a);
            cnt += __builtin_popcountll((uint64_t)common) + __builtin_popcountll((uint64_t)(common >> 64));
        }
        return cnt;
    }

    int count_edge_c8(int a, int b) const {
        pair<int, u128> pa[16], pb[32];
        int na = 0, nb = 0;
        u128 forb = ((u128)1 << a) | ((u128)1 << b);
        auto dfs3 = [&](auto&& self, int u, int d, u128 vis) -> void {
            if (d == 3) { pa[na++] = {u, vis}; return; }
            u128 cand = mask[u] & ~vis;
            while (cand) { int v = ctz128(cand); cand &= cand - 1; self(self, v, d + 1, vis | ((u128)1 << v)); }
        };
        dfs3(dfs3, a, 0, forb);
        auto dfs4 = [&](auto&& self, int u, int d, u128 vis) -> void {
            if (d == 4) { pb[nb++] = {u, vis}; return; }
            u128 cand = mask[u] & ~vis;
            while (cand) { int v = ctz128(cand); cand &= cand - 1; self(self, v, d + 1, vis | ((u128)1 << v)); }
        };
        dfs4(dfs4, b, 0, forb);
        int cnt = 0;
        for (int i = 0; i < na; ++i) {
            int m = pa[i].first;
            u128 va = pa[i].second & ~(forb | ((u128)1 << m));
            for (int j = 0; j < nb; ++j)
                if (pb[j].first == m && (va & pb[j].second) == 0) cnt++;
        }
        return cnt;
    }

    int count_edge_c16(int a, int b, vector<vector<u128>> &pa, vector<vector<u128>> &pb) const {
        for (int i = 0; i < n; ++i) { pa[i].clear(); pb[i].clear(); }
        u128 forb = ((u128)1 << a) | ((u128)1 << b);
        auto dfsA = [&](auto&& self, int u, int d, u128 vis) -> void {
            if (d == 7) { pa[u].push_back(vis); return; }
            u128 cand = mask[u] & ~vis;
            while (cand) { int v = ctz128(cand); cand &= cand - 1; self(self, v, d + 1, vis | ((u128)1 << v)); }
        };
        dfsA(dfsA, a, 0, forb);
        auto dfsB = [&](auto&& self, int u, int d, u128 vis) -> void {
            if (d == 8) { pb[u].push_back(vis); return; }
            u128 cand = mask[u] & ~vis;
            while (cand) { int v = ctz128(cand); cand &= cand - 1; self(self, v, d + 1, vis | ((u128)1 << v)); }
        };
        dfsB(dfsB, b, 0, forb);
        int cnt = 0;
        for (int m = 0; m < n; ++m) {
            if (pa[m].empty() || pb[m].empty()) continue;
            u128 fm = forb | ((u128)1 << m);
            for (u128 va : pa[m]) {
                u128 v1 = va & ~fm;
                for (u128 vb : pb[m]) if ((v1 & vb) == 0) cnt++;
            }
        }
        return cnt;
    }

    tuple<int,int,int> total_counts(vector<vector<u128>> &pa, vector<vector<u128>> &pb) const {
        long long s4 = 0, s8 = 0, s16 = 0;
        for (auto [u, v] : edges) {
            s4 += count_edge_c4(u, v);
            s8 += count_edge_c8(u, v);
            s16 += count_edge_c16(u, v, pa, pb);
        }
        return {(int)(s4 / 4), (int)(s8 / 8), (int)(s16 / 16)};
    }

    void apply_2switch_delta(int u, int v, int x, int y,
                             int &dc4, int &dc8, int &dc16,
                             vector<vector<u128>> &pa, vector<vector<u128>> &pb) {
        rem_edge(u, v);
        int l4 = count_edge_c4(u, v), l8 = count_edge_c8(u, v), l16 = count_edge_c16(u, v, pa, pb);
        rem_edge(x, y);
        l4 += count_edge_c4(x, y); l8 += count_edge_c8(x, y); l16 += count_edge_c16(x, y, pa, pb);
        int g4 = count_edge_c4(u, x), g8 = count_edge_c8(u, x), g16 = count_edge_c16(u, x, pa, pb);
        add_edge(u, x);
        g4 += count_edge_c4(v, y); g8 += count_edge_c8(v, y); g16 += count_edge_c16(v, y, pa, pb);
        add_edge(v, y);
        dc4 = g4 - l4; dc8 = g8 - l8; dc16 = g16 - l16;
    }

    void revert_2switch(int u, int v, int x, int y) {
        rem_edge(u, x); rem_edge(v, y);
        add_edge(u, v); add_edge(x, y);
    }

    bool has_c32_quick(int max_nodes_per_start = 5000000) const {
        for (int s = 0; s < n; ++s) {
            u128 allowed = ~(((u128)1 << s) - 1);
            bool found = false;
            int nodes = 0;
            auto dfs = [&](auto&& self, int u, int depth, u128 vis) -> void {
                if (found || ++nodes > max_nodes_per_start) return;
                if (depth == 31) { if (has_edge(u, s)) found = true; return; }
                u128 cand = mask[u] & allowed & ~vis;
                while (cand) {
                    int v = ctz128(cand); cand &= cand - 1;
                    self(self, v, depth + 1, vis | ((u128)1 << v));
                    if (found) return;
                }
            };
            dfs(dfs, s, 0, (u128)1 << s);
            if (found) return true;
        }
        return false;
    }

    string edges_str() const {
        ostringstream oss;
        for (auto [u, v] : edges) oss << "(" << u << "," << v << ") ";
        return oss.str();
    }
};

struct Result {
    int n, seed, bestE, c4, c8, c16;
    bool hit_zero;
    bool has_c32;
    string edges;
};

Result run_trial(int n, int steps_per_cycle, int cycles, int seed) {
    mt19937_64 rng(seed);
    Graph g(n);
    g.init_random(rng);

    vector<vector<u128>> pa(n), pb(n);
    for (int i = 0; i < n; ++i) { pa[i].reserve(32); pb[i].reserve(32); }

    auto [c4, c8, c16] = g.total_counts(pa, pb);
    auto energy = [](int a, int b, int c) { return 30 * a + 10 * b + c; };
    int curE = energy(c4, c8, c16);
    int bestE = curE, bc4 = c4, bc8 = c8, bc16 = c16;
    Graph bestG = g;

    for (int cyc = 0; cyc < cycles; ++cyc) {
        double T0 = (cyc == 0) ? 20.0 : 6.0;
        double T1 = 0.04;
        for (int step = 0; step < steps_per_cycle; ++step) {
            double T = T0 * pow(T1 / T0, (double)step / steps_per_cycle);
            int m = (int)g.edges.size();
            int e1 = rng() % m;
            int e2 = rng() % m;
            if (e1 == e2) continue;
            auto [u, v] = g.edges[e1];
            auto [x, y] = g.edges[e2];
            if (rng() & 1) swap(x, y);
            if (u == x || u == y || v == x || v == y) continue;
            if (g.has_edge(u, x) || g.has_edge(v, y)) continue;

            int dc4, dc8, dc16;
            g.apply_2switch_delta(u, v, x, y, dc4, dc8, dc16, pa, pb);
            int nc4 = c4 + dc4, nc8 = c8 + dc8, nc16 = c16 + dc16;
            int nxtE = energy(nc4, nc8, nc16);
            int delta = nxtE - curE;
            if (delta <= 0 || uniform_real_distribution<double>(0.0, 1.0)(rng) < exp(-delta / T)) {
                if (!g.is_connected()) {
                    g.revert_2switch(u, v, x, y);
                    continue;
                }
                c4 = nc4; c8 = nc8; c16 = nc16; curE = nxtE;
                g.rebuild();
                if (curE < bestE) {
                    bestE = curE; bc4 = c4; bc8 = c8; bc16 = c16;
                    bestG = g;
                    if (bestE == 0) {
                        bool c32 = g.has_c32_quick();
                        return {n, seed, 0, 0, 0, 0, true, c32, g.edges_str()};
                    }
                }
            } else {
                g.revert_2switch(u, v, x, y);
            }
        }
        g = bestG;
        c4 = bc4; c8 = bc8; c16 = bc16; curE = bestE;
    }
    return {n, seed, bestE, bc4, bc8, bc16, false, true, bestG.edges_str()};
}

int main(int argc, char** argv) {
    int n = argc > 1 ? stoi(argv[1]) : 62;
    int trials = argc > 2 ? stoi(argv[2]) : 16;
    int steps = argc > 3 ? stoi(argv[3]) : 300000;
    int cycles = argc > 4 ? stoi(argv[4]) : 5;

    vector<Result> res(trials);
    #pragma omp parallel for schedule(dynamic)
    for (int t = 0; t < trials; ++t) {
        res[t] = run_trial(n, steps, cycles, 10000 * n + t + 1);
    }

    int minE = INT_MAX;
    for (auto &r : res) {
        minE = min(minE, r.bestE);
        cout << "n=" << r.n << " seed=" << r.seed << " bestE=" << r.bestE
             << " (C4=" << r.c4 << ", C8=" << r.c8 << ", C16=" << r.c16 << ")";
        if (r.hit_zero) {
            cout << " *** ZERO C4/C8/C16! has_c32=" << r.has_c32 << " ***\n";
            cout << "EDGES: " << r.edges << "\n";
        } else {
            cout << "\n";
        }
    }
    cout << "SUMMARY n=" << n << " minE=" << minE << "\n";
    return 0;
}
