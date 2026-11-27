#include <bits/stdc++.h>
#include <omp.h>
using namespace std;

struct Graph {
    int n;
    vector<array<int, 3>> adj;
    vector<int> deg;
    Graph(int n = 0) : n(n), adj(n, {-1, -1, -1}), deg(n, 0) {}
    bool has_edge(int u, int v) const {
        for (int i = 0; i < deg[u]; i++) if (adj[u][i] == v) return true;
        return false;
    }
    void add_edge(int u, int v) {
        adj[u][deg[u]++] = v;
        adj[v][deg[v]++] = u;
    }
    void remove_edge(int u, int v) {
        for (int i = 0; i < deg[u]; i++) if (adj[u][i] == v) { adj[u][i] = adj[u][--deg[u]]; break; }
        for (int i = 0; i < deg[v]; i++) if (adj[v][i] == u) { adj[v][i] = adj[v][--deg[v]]; break; }
    }
};

Graph random_cubic(int n, mt19937_64& rng) {
    for (int attempt = 0; attempt < 5000; attempt++) {
        vector<int> stubs(3 * n);
        for (int i = 0; i < n; i++) stubs[3*i] = stubs[3*i+1] = stubs[3*i+2] = i;
        shuffle(stubs.begin(), stubs.end(), rng);
        Graph g(n);
        bool ok = true;
        for (int i = 0; i < 3 * n; i += 2) {
            int u = stubs[i], v = stubs[i+1];
            if (u == v || g.has_edge(u, v)) { ok = false; break; }
            g.add_edge(u, v);
        }
        if (ok) return g;
    }
    return Graph(n);
}

long long count_cycles_len(const Graph& g, int L, long long cap = 100000) {
    int n = g.n;
    long long total = 0;
    vector<uint8_t> vis(n, 0);
    auto dfs = [&](auto&& self, int start, int u, int depth) -> void {
        if (total >= cap) return;
        if (depth == L - 1) {
            for (int i = 0; i < 3; i++) {
                if (g.adj[u][i] == start) {
                    total++;
                    if (total >= cap) return;
                }
            }
            return;
        }
        for (int i = 0; i < 3; i++) {
            int v = g.adj[u][i];
            if (v > start && !vis[v]) {
                vis[v] = 1;
                self(self, start, v, depth + 1);
                vis[v] = 0;
                if (total >= cap) return;
            }
        }
    };
    for (int s = 0; s < n; s++) {
        vis[s] = 1;
        dfs(dfs, s, s, 0);
        vis[s] = 0;
        if (total >= cap) break;
    }
    return total / 2;
}

// Check if graph is connected
bool is_connected(const Graph& g) {
    vector<uint8_t> vis(g.n, 0);
    queue<int> q; q.push(0); vis[0] = 1;
    int cnt = 0;
    while (!q.empty()) {
        int u = q.front(); q.pop(); cnt++;
        for (int i = 0; i < 3; i++) {
            int v = g.adj[u][i];
            if (!vis[v]) { vis[v] = 1; q.push(v); }
        }
    }
    return cnt == g.n;
}

// Pentagon cluster analysis
tuple<int, int, int> analyze_c5_clusters(const Graph& g) {
    int n = g.n;
    vector<array<int, 5>> c5s;
    vector<uint8_t> vis(n, 0);
    array<int, 5> path;
    auto dfs = [&](auto&& self, int start, int u, int d) -> void {
        path[d] = u;
        if (d == 4) {
            if (g.has_edge(u, start) && path[1] < path[4]) c5s.push_back(path);
            return;
        }
        for (int i = 0; i < 3; i++) {
            int v = g.adj[u][i];
            if (v > start && !vis[v]) {
                vis[v] = 1;
                self(self, start, v, d + 1);
                vis[v] = 0;
            }
        }
    };
    for (int s = 0; s < n; s++) { vis[s] = 1; dfs(dfs, s, s, 0); vis[s] = 0; }
    int m = c5s.size();
    if (m == 0) return {0, 0, 0};
    vector<vector<int>> cg(m);
    int single_edge_overlaps = 0;
    for (int i = 0; i < m; i++) {
        for (int j = i + 1; j < m; j++) {
            int shared_v = 0;
            for (int a : c5s[i]) for (int b : c5s[j]) if (a == b) shared_v++;
            if (shared_v > 0) {
                cg[i].push_back(j); cg[j].push_back(i);
                if (shared_v == 2) single_edge_overlaps++;
            }
        }
    }
    vector<uint8_t> seen(m, 0);
    int max_comp = 0;
    for (int i = 0; i < m; i++) {
        if (!seen[i]) {
            int sz = 0; queue<int> q; q.push(i); seen[i] = 1;
            while (!q.empty()) {
                int u = q.front(); q.pop(); sz++;
                for (int v : cg[u]) if (!seen[v]) { seen[v] = 1; q.push(v); }
            }
            max_comp = max(max_comp, sz);
        }
    }
    return {m, max_comp, single_edge_overlaps};
}

// Signed ear/chord adjuster certificate
bool check_signed_adjuster_cert(const Graph& g, mt19937_64& rng, int trials = 30) {
    int n = g.n;
    for (int t = 0; t < trials; t++) {
        int start = rng() % n;
        vector<int> cyc; vector<int> pos(n, -1);
        int cur = start; cyc.push_back(cur); pos[cur] = 0;
        bool found = false;
        while (true) {
            vector<int> cands;
            for (int i = 0; i < 3; i++) {
                int nxt = g.adj[cur][i];
                if (pos[nxt] == -1) cands.push_back(nxt);
            }
            if (!cands.empty()) {
                int nxt = cands[rng() % cands.size()];
                pos[nxt] = cyc.size(); cyc.push_back(nxt); cur = nxt;
            } else {
                int best_p = 1e9;
                for (int i = 0; i < 3; i++) {
                    int nxt = g.adj[cur][i];
                    if (pos[nxt] != -1 && (int)cyc.size() - pos[nxt] >= 5)
                        best_p = min(best_p, pos[nxt]);
                }
                if (best_p < 1e9) {
                    cyc = vector<int>(cyc.begin() + best_p, cyc.end());
                    found = true;
                }
                break;
            }
        }
        if (!found) continue;
        int L = cyc.size();
        if ((L & (L - 1)) == 0 && L >= 4) return true;
        fill(pos.begin(), pos.end(), -1);
        for (int i = 0; i < L; i++) pos[cyc[i]] = i;

        struct Adj { int i, a, b; vector<int> internal; };
        vector<Adj> cands;
        for (int i = 0; i < L; i++) {
            int u = cyc[i];
            for (int j = 0; j < 3; j++) {
                int v = g.adj[u][j];
                if (pos[v] != -1) {
                    int a = (pos[v] - i + L) % L;
                    if (a >= 2 && a <= min(6, L - 3)) cands.push_back({i, a, 1, {}});
                }
            }
            queue<pair<int, vector<int>>> q;
            for (int j = 0; j < 3; j++) {
                int v = g.adj[u][j];
                if (pos[v] == -1) q.push({v, {v}});
            }
            while (!q.empty()) {
                auto [w, path] = q.front(); q.pop();
                int b = path.size() + 1;
                if (b > 5) continue;
                for (int j = 0; j < 3; j++) {
                    int nxt = g.adj[w][j];
                    if (pos[nxt] != -1 && nxt != u) {
                        int a = (pos[nxt] - i + L) % L;
                        if (a >= 1 && a <= min(5, L - 3) && a != b) cands.push_back({i, a, b, path});
                    } else if (pos[nxt] == -1 && b < 5) {
                        bool in_p = false;
                        for (int x : path) if (x == nxt) in_p = true;
                        if (!in_p) { auto p2 = path; p2.push_back(nxt); q.push({nxt, p2}); }
                    }
                }
            }
        }
        sort(cands.begin(), cands.end(), [](const Adj& x, const Adj& y) {
            int dx = abs(x.b - x.a), dy = abs(y.b - y.a);
            if (dx != dy) return dx < dy;
            return (x.b - x.a) < (y.b - y.a);
        });
        vector<uint8_t> used_cyc(L, 0), used_ext(n, 0);
        int L_min = L;
        vector<int> weights;
        for (auto& ad : cands) {
            bool ok = true;
            for (int s = 0; s <= ad.a; s++) if (used_cyc[(ad.i + s) % L]) { ok = false; break; }
            for (int x : ad.internal) if (used_ext[x]) { ok = false; break; }
            if (!ok) continue;
            for (int s = 0; s <= ad.a; s++) used_cyc[(ad.i + s) % L] = 1;
            for (int x : ad.internal) used_ext[x] = 1;
            int delta = ad.b - ad.a;
            if (delta < 0) L_min += delta;
            weights.push_back(abs(delta));
        }
        bitset<512> bs;
        bs[L_min] = 1;
        for (int w : weights) bs |= (bs << w);
        for (int p = 4; p < 512; p <<= 1) if (bs[p]) return true;
    }
    return false;
}

int main() {
    cout << "=== Wave 7 Agent 9: Girth>=5 {4,8,16}-Free Cubic Hunter & Theorem Audit ===" << endl;
    cout << "OpenMP threads: " << omp_get_max_threads() << endl;

    vector<int> orders = {50, 60, 70, 80, 90, 100, 110, 120};
    int total_g5_c8free = 0;
    int total_c5_density_ok = 0;
    int total_c5_cluster_ok = 0;
    int total_c5_no_single_edge = 0;
    int total_adj_cert = 0;
    int total_zero4816 = 0;
    int max_cluster_global = 0;

    for (int n : orders) {
        int restarts = 16;
        int best_c16_for_n = 1e9;
        int found_g5_c8_n = 0;
        int adj_ok_n = 0;
        int zero16_n = 0;
        int max_c5_n = 0;

        #pragma omp parallel for schedule(dynamic)
        for (int r = 0; r < restarts; r++) {
            mt19937_64 rng(2026112700ULL + (uint64_t)n * 1000 + r);
            Graph g = random_cubic(n, rng);

            // Phase 1: Kill C3, C4, C8 strictly
            auto eval_phase1 = [&]() {
                long long c3 = count_cycles_len(g, 3, 2000);
                long long c4 = count_cycles_len(g, 4, 2000);
                long long c8 = count_cycles_len(g, 8, 2000);
                return c3 * 200 + c4 * 200 + c8 * 10;
            };
            long long e1 = eval_phase1();
            for (int step = 0; step < 5000 && e1 > 0; step++) {
                int u1 = rng() % n, v1 = g.adj[u1][rng() % 3];
                int u2 = rng() % n, v2 = g.adj[u2][rng() % 3];
                if (u1 == u2 || u1 == v2 || v1 == u2 || v1 == v2) continue;
                if (g.has_edge(u1, u2) || g.has_edge(v1, v2)) continue;
                g.remove_edge(u1, v1); g.remove_edge(u2, v2);
                g.add_edge(u1, u2); g.add_edge(v1, v2);
                long long ne = eval_phase1();
                if (ne <= e1 || (rng() % 1000) < 8) {
                    e1 = ne;
                } else {
                    g.remove_edge(u1, u2); g.remove_edge(v1, v2);
                    g.add_edge(u1, v1); g.add_edge(u2, v2);
                }
            }

            if (e1 == 0 && is_connected(g)) {
                auto [num_c5, max_cl, se_ov] = analyze_c5_clusters(g);
                bool cert = check_signed_adjuster_cert(g, rng, 35);

                // Phase 2: Drive C16 down while keeping C3=C4=C8=0 strictly
                long long c16 = count_cycles_len(g, 16, 4000);
                long long best_c16 = c16;
                for (int step = 0; step < 600 && best_c16 > 0; step++) {
                    int u1 = rng() % n, v1 = g.adj[u1][rng() % 3];
                    int u2 = rng() % n, v2 = g.adj[u2][rng() % 3];
                    if (u1 == u2 || u1 == v2 || v1 == u2 || v1 == v2) continue;
                    if (g.has_edge(u1, u2) || g.has_edge(v1, v2)) continue;
                    g.remove_edge(u1, v1); g.remove_edge(u2, v2);
                    g.add_edge(u1, u2); g.add_edge(v1, v2);
                    if (count_cycles_len(g, 3, 2) == 0 &&
                        count_cycles_len(g, 4, 2) == 0 &&
                        count_cycles_len(g, 8, 2) == 0) {
                        long long nc16 = count_cycles_len(g, 16, min(best_c16 + 20, 4000LL));
                        if (nc16 <= c16) {
                            c16 = nc16;
                            if (c16 < best_c16) best_c16 = c16;
                            continue;
                        }
                    }
                    g.remove_edge(u1, u2); g.remove_edge(v1, v2);
                    g.add_edge(u1, v1); g.add_edge(u2, v2);
                }

                bool has32 = true;
                if (best_c16 == 0) {
                    has32 = (count_cycles_len(g, 32, 2) > 0);
                }

                #pragma omp critical
                {
                    found_g5_c8_n++;
                    total_g5_c8free++;
                    if (num_c5 * 7 <= 2 * n) total_c5_density_ok++;
                    if (max_cl <= 2) total_c5_cluster_ok++;
                    if (se_ov == 0) total_c5_no_single_edge++;
                    if (cert) { total_adj_cert++; adj_ok_n++; }
                    if (best_c16 == 0) { total_zero4816++; zero16_n++; }
                    max_cluster_global = max(max_cluster_global, max_cl);
                    max_c5_n = max(max_c5_n, num_c5);
                    if (best_c16 < best_c16_for_n) best_c16_for_n = best_c16;
                    if (best_c16 == 0) {
                        cout << "  [ZERO-4,8,16 GIRTH>=5 FOUND!] n=" << n << " r=" << r
                             << " #C5=" << num_c5 << " hasC32=" << has32 << endl;
                    }
                }
            }
        }
        cout << "n=" << setw(3) << n
             << " | girth>=5 C8=0: " << setw(2) << found_g5_c8_n << "/" << restarts
             << " | max_#C5=" << setw(2) << max_c5_n << " (bound " << (2*n/7) << ")"
             << " | SignedAdjCert=" << adj_ok_n << "/" << found_g5_c8_n
             << " | min_C16=" << (best_c16_for_n < 1e8 ? to_string(best_c16_for_n) : "N/A")
             << " | zero4816=" << zero16_n << endl;
    }

    cout << "\n=== FINAL SUMMARY ===" << endl;
    cout << "Total connected girth>=5 C8-free cubic graphs audited: " << total_g5_c8free << endl;
    cout << "Pentagon-Cluster Isolation (max_cl <= 2): " << total_c5_cluster_ok << "/" << total_g5_c8free
         << " (observed max_cl=" << max_cluster_global << ")" << endl;
    cout << "Pentagon Single-Edge Overlap Exclusion (se=0): " << total_c5_no_single_edge << "/" << total_g5_c8free << endl;
    cout << "Pentagon Density Bound (#C5 <= floor(2n/7)): " << total_c5_density_ok << "/" << total_g5_c8free << endl;
    cout << "Signed Ear/Chord Adjuster Certification: " << total_adj_cert << "/" << total_g5_c8free << endl;
    cout << "Triangle-free {4,8,16}-free cubic survivors: " << total_zero4816 << endl;
    return 0;
}
