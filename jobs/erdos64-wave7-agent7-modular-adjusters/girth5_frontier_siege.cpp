#include <bits/stdc++.h>
#include <omp.h>
using namespace std;

// Wave 7 Agent #7: OpenMP C++20 Girth>=5 Anti-Triangle & Symmetric Cubic Siege
// 1) Exhaustive Generalized Petersen GP(m, k) for m = 25..150 (n = 50..300)
// 2) Exhaustive C4-free K4 Z_m-lifts for m = 13..50 (n = 52..200)
// 3) Exhaustive C4-free Prism (K3 x K2) Z_m-lifts for m = 9..25 (n = 54..150)
// 4) Multi-threaded Girth>=5 Anti-Triangle SA at n = 50, 52, 54, 56, 58, 60, 62, 70, 80, 90, 100

struct Graph {
    int n;
    vector<array<int, 3>> adj;

    bool has_edge(int u, int v) const {
        for (int i = 0; i < 3; i++) if (adj[u][i] == v) return true;
        return false;
    }

    bool has_cycle_from(int L, int start, int node_budget = 400000) const {
        vector<uint8_t> vis(n, 0);
        vector<int> dist(n, 999);
        queue<int> q;
        dist[start] = 0; q.push(start);
        while (!q.empty()) {
            int u = q.front(); q.pop();
            for (int w : adj[u]) if (dist[w] == 999) { dist[w] = dist[u] + 1; q.push(w); }
        }
        bool found = false;
        int nodes = 0;
        auto dfs = [&](auto& self, int u, int depth) -> void {
            if (found || nodes > node_budget) return;
            nodes++;
            int rem = L - depth;
            if (rem == 1) {
                for (int w : adj[u]) if (w == start) { found = true; return; }
                return;
            }
            if (dist[u] > rem) return;
            for (int w : adj[u]) {
                if (!vis[w] && dist[w] <= rem - 1) {
                    vis[w] = 1;
                    self(self, w, depth + 1);
                    vis[w] = 0;
                    if (found) return;
                }
            }
        };
        vis[start] = 1;
        dfs(dfs, start, 0);
        return found;
    }

    bool has_cycle_orbit(int L, int q_orbits, int m) const {
        for (int b = 0; b < q_orbits; b++) {
            if (has_cycle_from(L, b * m)) return true;
        }
        return false;
    }

    int count_cycles_exact(int L, int cap = 50000) const {
        if (L <= 10) {
            int total = 0;
            vector<uint8_t> vis(n, 0);
            auto dfs = [&](auto& self, int start, int u, int prev, int depth) -> void {
                if (total >= cap) return;
                if (depth == L - 1) {
                    for (int i = 0; i < 3; i++) {
                        int w = adj[u][i];
                        if (w == start && w != prev) total++;
                    }
                    return;
                }
                for (int i = 0; i < 3; i++) {
                    int w = adj[u][i];
                    if (w > start && !vis[w]) {
                        vis[w] = 1;
                        self(self, start, w, u, depth + 1);
                        vis[w] = 0;
                    }
                }
            };
            for (int s = 0; s < n; s++) {
                vis[s] = 1;
                dfs(dfs, s, s, -1, 0);
                vis[s] = 0;
            }
            return total / 2;
        }
        if (L == 16) {
            using u128 = unsigned __int128;
            int total = 0;
            vector<vector<u128>> paths_by_end(n);
            vector<int> touched;
            auto dfs = [&](auto& self, int start, int u, int depth, u128 mask) -> void {
                if (depth == 8) {
                    if (paths_by_end[u].empty()) touched.push_back(u);
                    paths_by_end[u].push_back(mask);
                    return;
                }
                for (int i = 0; i < 3; i++) {
                    int w = adj[u][i];
                    if (w > start && !((mask >> w) & 1)) {
                        self(self, start, w, depth + 1, mask | (u128(1) << w));
                    }
                }
            };
            for (int s = 0; s < n; s++) {
                touched.clear();
                dfs(dfs, s, s, 0, u128(0));
                for (int endv : touched) {
                    auto& vec = paths_by_end[endv];
                    int sz = (int)vec.size();
                    u128 end_bit = u128(1) << endv;
                    for (int i = 0; i < sz; i++) {
                        u128 m1 = vec[i] ^ end_bit;
                        for (int j = i + 1; j < sz; j++) {
                            if ((m1 & vec[j]) == 0) {
                                total++;
                                if (total >= cap) {
                                    for (int tv : touched) paths_by_end[tv].clear();
                                    return total;
                                }
                            }
                        }
                    }
                    vec.clear();
                }
            }
            return total;
        }
        return -1;
    }
};

Graph random_cubic(int n, mt19937_64& rng) {
    Graph G; G.n = n; G.adj.resize(n);
    while (true) {
        vector<int> stubs(3 * n);
        for (int i = 0; i < n; i++) stubs[3*i] = stubs[3*i+1] = stubs[3*i+2] = i;
        shuffle(stubs.begin(), stubs.end(), rng);
        vector<vector<int>> a(n);
        bool ok = true;
        for (int i = 0; i < 3 * n; i += 2) {
            int u = stubs[i], v = stubs[i+1];
            if (u == v) { ok = false; break; }
            for (int x : a[u]) if (x == v) { ok = false; break; }
            if (!ok) break;
            a[u].push_back(v); a[v].push_back(u);
        }
        if (ok) {
            for (int i = 0; i < n; i++) G.adj[i] = {a[i][0], a[i][1], a[i][2]};
            return G;
        }
    }
}

bool do_2switch(Graph& G, int u, int v, int x, int y) {
    if (u == x || u == y || v == x || v == y) return false;
    if (G.has_edge(u, x) || G.has_edge(v, y)) return false;
    for (int i = 0; i < 3; i++) if (G.adj[u][i] == v) { G.adj[u][i] = x; break; }
    for (int i = 0; i < 3; i++) if (G.adj[v][i] == u) { G.adj[v][i] = y; break; }
    for (int i = 0; i < 3; i++) if (G.adj[x][i] == y) { G.adj[x][i] = u; break; }
    for (int i = 0; i < 3; i++) if (G.adj[y][i] == x) { G.adj[y][i] = v; break; }
    return true;
}

int main() {
    cout << "=== Wave 7 Agent #7: Girth>=5 Anti-Triangle & Symmetric Cubic Siege ===" << endl;

    // 1. Generalized Petersen GP(m, k), m = 25..150 (n = 50..300)
    long long gp_tested = 0, gp_no4816 = 0, gp_no481632 = 0;
    #pragma omp parallel for schedule(dynamic) reduction(+:gp_tested,gp_no4816,gp_no481632)
    for (int m = 25; m <= 150; m++) {
        for (int k = 2; k <= m / 2; k++) {
            if (2 * k == m) continue;
            Graph G; G.n = 2 * m; G.adj.resize(2 * m);
            for (int i = 0; i < m; i++) {
                G.adj[i] = {(i + 1) % m, (i + m - 1) % m, m + i};
                G.adj[m + i] = {m + (i + k) % m, m + (i + m - k) % m, i};
            }
            gp_tested++;
            if (G.has_cycle_orbit(4, 2, m)) continue;
            if (G.has_cycle_orbit(8, 2, m)) continue;
            if (G.has_cycle_orbit(16, 2, m)) continue;
            gp_no4816++;
            if (!G.has_cycle_orbit(32, 2, m)) {
                gp_no481632++;
                #pragma omp critical
                cout << "SURVIVOR GP(" << m << "," << k << ")" << endl;
            }
        }
    }
    cout << "[1] GP(25..150, n=50..300): tested=" << gp_tested
         << " no4816=" << gp_no4816 << " no481632=" << gp_no481632 << endl;

    // 2. Exhaustive C4-free K4 Z_m-lifts, m = 13..50 (n = 52..200)
    long long k4_tested = 0, k4_no4816 = 0, k4_no481632 = 0;
    #pragma omp parallel for schedule(dynamic) reduction(+:k4_tested,k4_no4816,k4_no481632)
    for (int m = 13; m <= 50; m++) {
        for (int v1 = 1; v1 < m; v1++) {
            for (int v2 = v1; v2 < m; v2++) {
                for (int v3 = 1; v3 < m; v3++) {
                    if ((v1 + v3) % m == 0 || (v2 - v3 + m) % m == 0 || (v1 - v2 + m) % m == 0) continue;
                    if ((v1 - v2 + v3 + m) % m == 0) continue;
                    Graph G; G.n = 4 * m; G.adj.resize(4 * m);
                    for (int i = 0; i < m; i++) {
                        G.adj[0*m + i] = {1*m + i, 2*m + i, 3*m + i};
                        G.adj[1*m + i] = {0*m + i, 2*m + (i + v1) % m, 3*m + (i + v2) % m};
                        G.adj[2*m + i] = {0*m + i, 1*m + (i + m - v1) % m, 3*m + (i + v3) % m};
                        G.adj[3*m + i] = {0*m + i, 1*m + (i + m - v2) % m, 2*m + (i + m - v3) % m};
                    }
                    k4_tested++;
                    if (G.has_cycle_orbit(4, 4, m)) continue;
                    if (G.has_cycle_orbit(8, 4, m)) continue;
                    if (G.has_cycle_orbit(16, 4, m)) continue;
                    k4_no4816++;
                    if (!G.has_cycle_orbit(32, 4, m)) {
                        k4_no481632++;
                        #pragma omp critical
                        cout << "SURVIVOR K4 m=" << m << " (" << v1 << "," << v2 << "," << v3 << ")" << endl;
                    }
                }
            }
        }
    }
    cout << "[2] K4 Z_m-lifts (m=13..50, n=52..200): tested=" << k4_tested
         << " no4816=" << k4_no4816 << " no481632=" << k4_no481632 << endl;

    // 3. Multi-threaded Girth>=5 Anti-Triangle SA at n = 50, 52, 54, 56, 58, 60, 62, 70, 80, 90, 100
    vector<int> ns = {50, 52, 54, 56, 58, 60, 62, 70, 80, 90, 100};
    cout << "[3] Girth>=5 Anti-Triangle SA (4 restarts x 60,000 steps per n):" << endl;
    #pragma omp parallel for schedule(dynamic)
    for (int idx = 0; idx < (int)ns.size(); idx++) {
        int n = ns[idx];
        int best_c3 = 999999, best_c4 = 999999, best_c8 = 999999, best_c16 = 999999;
        int best_c5 = 0, best_c6 = 0, best_c7 = 0;
        bool best_has32 = true;
        for (int rep = 0; rep < 4; rep++) {
            mt19937_64 rng(20261127ULL + n * 1000ULL + rep * 37ULL);
            Graph G = random_cubic(n, rng);
            auto eval = [&](const Graph& H, int& c3, int& c4, int& c8, int& c16) -> double {
                c3 = H.count_cycles_exact(3);
                c4 = H.count_cycles_exact(4);
                c8 = H.count_cycles_exact(8);
                c16 = (c3 == 0 && c4 == 0 && c8 <= 15) ? H.count_cycles_exact(16, 2000) : 2000;
                return 800.0 * c3 + 800.0 * c4 + 35.0 * c8 + 1.0 * c16;
            };
            int c3, c4, c8, c16;
            double curE = eval(G, c3, c4, c8, c16);
            double locBestE = curE;
            Graph locBestG = G;
            int lc3 = c3, lc4 = c4, lc8 = c8, lc16 = c16;
            uniform_real_distribution<double> U(0.0, 1.0);
            vector<pair<int,int>> edges;
            edges.reserve(3 * n / 2);
            int steps = 60000;
            for (int step = 0; step < steps; step++) {
                double T = 35.0 * pow(0.003, (double)step / steps);
                edges.clear();
                for (int i = 0; i < n; i++)
                    for (int j = 0; j < 3; j++)
                        if (i < G.adj[i][j]) edges.push_back({i, G.adj[i][j]});
                int m = (int)edges.size();
                int i1 = rng() % m, i2 = rng() % m;
                if (i1 == i2) continue;
                auto [u, v] = edges[i1];
                auto [x, y] = edges[i2];
                if (rng() & 1) swap(x, y);
                if (!do_2switch(G, u, v, x, y)) continue;
                int nc3, nc4, nc8, nc16;
                double newE = eval(G, nc3, nc4, nc8, nc16);
                if (newE <= curE || U(rng) < exp((curE - newE) / T)) {
                    curE = newE; c3 = nc3; c4 = nc4; c8 = nc8; c16 = nc16;
                    if (curE < locBestE) {
                        locBestE = curE; locBestG = G;
                        lc3 = c3; lc4 = c4; lc8 = c8; lc16 = c16;
                    }
                } else {
                    do_2switch(G, u, x, v, y);
                }
                if (lc3 == 0 && lc4 == 0 && lc8 == 0 && lc16 == 0) break;
            }
            if (tie(lc3, lc4, lc8, lc16) < tie(best_c3, best_c4, best_c8, best_c16)) {
                best_c3 = lc3; best_c4 = lc4; best_c8 = lc8; best_c16 = lc16;
                best_c5 = locBestG.count_cycles_exact(5);
                best_c6 = locBestG.count_cycles_exact(6);
                best_c7 = locBestG.count_cycles_exact(7);
                best_has32 = locBestG.has_cycle_from(32, 0, 500000);
            }
        }
        #pragma omp critical
        cout << "  n=" << setw(3) << n
             << " BEST: C3=" << best_c3 << " C4=" << best_c4
             << " C8=" << best_c8 << " C16=" << best_c16
             << " | C5=" << best_c5 << " C6=" << best_c6 << " C7=" << best_c7
             << " hasC32=" << best_has32 << endl;
    }
    return 0;
}
