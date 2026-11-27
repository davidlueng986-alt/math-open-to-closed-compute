#include <bits/stdc++.h>
#include <omp.h>
using namespace std;

// Wave 8 Agent 9: Post-Delsarte High-Girth (g in {9..14}, n in [132, 320])
// Adversarial Counterexample Hunt & Delsarte-Chebyshev SOS Audit

struct CubicGraph {
    int n;
    vector<array<int, 3>> adj;
    vector<int> deg;
    CubicGraph(int n = 0) : n(n), adj(n, {-1, -1, -1}), deg(n, 0) {}
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

int compute_girth(const CubicGraph& g) {
    int n = g.n;
    int best = 1e9;
    vector<int> dist(n), par(n), q(n);
    for (int s = 0; s < n; s++) {
        fill(dist.begin(), dist.end(), -1);
        int qh = 0, qt = 0;
        q[qt++] = s; dist[s] = 0; par[s] = -1;
        while (qh < qt) {
            int u = q[qh++];
            if (2 * dist[u] + 1 >= best) break;
            for (int i = 0; i < g.deg[u]; i++) {
                int v = g.adj[u][i];
                if (dist[v] == -1) {
                    dist[v] = dist[u] + 1; par[v] = u; q[qt++] = v;
                } else if (v != par[u]) {
                    best = min(best, dist[u] + dist[v] + 1);
                }
            }
        }
    }
    return best;
}

bool is_connected(const CubicGraph& g) {
    vector<uint8_t> vis(g.n, 0);
    vector<int> q; q.reserve(g.n);
    q.push_back(0); vis[0] = 1;
    for (size_t i = 0; i < q.size(); i++) {
        int u = q[i];
        for (int j = 0; j < g.deg[u]; j++) {
            int v = g.adj[u][j];
            if (!vis[v]) { vis[v] = 1; q.push_back(v); }
        }
    }
    return (int)q.size() == g.n;
}

long long count_cycles_len(const CubicGraph& g, int L, long long cap = 100000) {
    int n = g.n;
    long long total = 0;
    vector<uint8_t> vis(n, 0);
    vector<int> dist(n), q(n);
    auto dfs = [&](auto&& self, int start, int u, int depth) -> void {
        if (total >= cap) return;
        int rem = L - depth;
        if (dist[u] > rem) return;
        if (depth == L - 1) {
            for (int i = 0; i < g.deg[u]; i++) {
                if (g.adj[u][i] == start) {
                    total++;
                    if (total >= cap) return;
                }
            }
            return;
        }
        for (int i = 0; i < g.deg[u]; i++) {
            int v = g.adj[u][i];
            if (v > start && !vis[v] && dist[v] <= rem - 1) {
                vis[v] = 1;
                self(self, start, v, depth + 1);
                vis[v] = 0;
                if (total >= cap) return;
            }
        }
    };
    for (int s = 0; s < n; s++) {
        fill(dist.begin(), dist.end(), 1e9);
        int qh = 0, qt = 0;
        q[qt++] = s; dist[s] = 0;
        while (qh < qt) {
            int u = q[qh++];
            if (dist[u] >= L / 2 + 1) continue;
            for (int i = 0; i < g.deg[u]; i++) {
                int v = g.adj[u][i];
                if (v > s && dist[v] > dist[u] + 1) {
                    dist[v] = dist[u] + 1;
                    q[qt++] = v;
                }
            }
        }
        vis[s] = 1;
        dfs(dfs, s, s, 0);
        vis[s] = 0;
        if (total >= cap) break;
    }
    return total / 2;
}

long long compute_b16_exact_girth9(const CubicGraph& g) {
    int n = g.n;
    int M = 3 * n;
    vector<int> eu(M), ev(M);
    vector<array<int, 2>> nxt(M);
    int idx = 0;
    for (int u = 0; u < n; u++) {
        for (int j = 0; j < 3; j++) {
            eu[idx] = u; ev[idx] = g.adj[u][j]; idx++;
        }
    }
    for (int e = 0; e < M; e++) {
        int u = eu[e], v = ev[e], c = 0;
        for (int j = 0; j < 3; j++) {
            int w = g.adj[v][j];
            if (w != u) nxt[e][c++] = 3 * v + j;
        }
    }
    long long tr = 0;
    vector<long long> cur(M), nx(M);
    for (int s = 0; s < M; s++) {
        fill(cur.begin(), cur.end(), 0);
        cur[s] = 1;
        for (int step = 0; step < 16; step++) {
            fill(nx.begin(), nx.end(), 0);
            for (int e = 0; e < M; e++) {
                if (cur[e]) {
                    nx[nxt[e][0]] += cur[e];
                    nx[nxt[e][1]] += cur[e];
                }
            }
            cur.swap(nx);
        }
        tr += cur[s];
    }
    return tr;
}

bool has_C32(const CubicGraph& g, int max_nodes = 2000000) {
    int n = g.n;
    vector<uint8_t> vis(n, 0);
    int nodes = 0;
    bool found = false;
    auto dfs = [&](auto&& self, int start, int u, int depth) -> void {
        if (found || ++nodes > max_nodes) return;
        if (depth == 31) {
            for (int i = 0; i < 3; i++) if (g.adj[u][i] == start) { found = true; return; }
            return;
        }
        for (int i = 0; i < 3; i++) {
            int v = g.adj[u][i];
            if (v > start && !vis[v]) {
                vis[v] = 1;
                self(self, start, v, depth + 1);
                vis[v] = 0;
                if (found || nodes > max_nodes) return;
            }
        }
    };
    for (int s = 0; s < n && !found && nodes <= max_nodes; s++) {
        vis[s] = 1;
        dfs(dfs, s, s, 0);
        vis[s] = 0;
    }
    return found;
}

CubicGraph build_lift(const vector<pair<int,int>>& base_edges, int n_base,
                      const vector<int>& volts, int m) {
    CubicGraph g(n_base * m);
    for (size_t e = 0; e < base_edges.size(); e++) {
        int u = base_edges[e].first, v = base_edges[e].second;
        int w = volts[e];
        for (int r = 0; r < m; r++) {
            int a = u * m + r;
            int b = v * m + ((r + w) % m + m) % m;
            if (a == b || g.has_edge(a, b)) return CubicGraph(0);
            g.add_edge(a, b);
        }
    }
    return g;
}

CubicGraph random_cubic(int n, mt19937_64& rng) {
    for (int attempt = 0; attempt < 5000; attempt++) {
        vector<int> stubs(3 * n);
        for (int i = 0; i < n; i++) stubs[3*i] = stubs[3*i+1] = stubs[3*i+2] = i;
        shuffle(stubs.begin(), stubs.end(), rng);
        CubicGraph g(n);
        bool ok = true;
        for (int i = 0; i < 3 * n; i += 2) {
            int u = stubs[i], v = stubs[i+1];
            if (u == v || g.has_edge(u, v)) { ok = false; break; }
            g.add_edge(u, v);
        }
        if (ok) return g;
    }
    return CubicGraph(n);
}

long long penalty_girth9(const CubicGraph& g) {
    long long p = 0;
    p += count_cycles_len(g, 3, 200) * 5000;
    p += count_cycles_len(g, 4, 200) * 2000;
    p += count_cycles_len(g, 5, 200) * 500;
    p += count_cycles_len(g, 6, 200) * 100;
    p += count_cycles_len(g, 7, 200) * 20;
    p += count_cycles_len(g, 8, 200) * 5;
    return p;
}

int main(int argc, char** argv) {
    bool smoke = (argc > 1 && string(argv[1]) == "--smoke");
    cout << "=== Wave 8 Agent 9: Post-Delsarte High-Girth (g>=9, n in [132,320]) Siege ===" << endl;
    cout << "OpenMP threads: " << omp_get_max_threads() << " | mode: " << (smoke ? "SMOKE" : "FULL") << endl;

    vector<pair<int,int>> k33_edges = {
        {0,3},{0,4},{0,5},{1,3},{1,4},{1,5},{2,3},{2,4},{2,5}
    };
    vector<int> k33_chords = {4, 5, 7, 8};

    vector<pair<int,int>> pet_edges = {
        {0,1},{1,2},{2,3},{3,4},{4,0},
        {5,7},{7,9},{9,6},{6,8},{8,5},
        {0,5},{1,6},{2,7},{3,8},{4,9}
    };
    vector<int> pet_chords = {4, 5, 6, 7, 8, 9};

    long long lifts_tested = 0, lifts_g9 = 0, lifts_g10 = 0, lifts_g12 = 0;
    long long lifts_zero_c16 = 0, lifts_zero_c16_c32 = 0;
    long long min_c16_lift = 1e18;
    int best_girth_lift = 0;

    int k33_samples = smoke ? 1500 : 12000;
    vector<int> k33_ms = smoke ? vector<int>{22, 26, 30} : vector<int>{22, 24, 26, 28, 30, 32, 34, 36, 40, 44, 48, 52};

    cout << "\n--- Part A1: K_{3,3} Z_m-Voltage Lifts (Bipartite, n = 6m in [132, 312]) ---" << endl;
    for (int m : k33_ms) {
        long long g9_m = 0, g10_m = 0, g12_m = 0, z16_m = 0;
        long long min_c16_m = 1e18;
        #pragma omp parallel for schedule(dynamic) reduction(+:lifts_tested,g9_m,g10_m,g12_m,z16_m)
        for (int s = 0; s < k33_samples; s++) {
            mt19937_64 rng(890001ULL + m * 100003ULL + s * 7919ULL);
            vector<int> v(9, 0);
            for (int c : k33_chords) v[c] = 1 + (rng() % (m - 1));
            lifts_tested++;
            CubicGraph g = build_lift(k33_edges, 6, v, m);
            if (g.n == 0 || !is_connected(g)) continue;
            int gr = compute_girth(g);
            if (gr >= 10) {
                g9_m++; g10_m++;
                if (gr >= 12) g12_m++;
                long long b16 = compute_b16_exact_girth9(g);
                long long c16 = b16 / 32;
                #pragma omp critical
                {
                    if (c16 < min_c16_m) min_c16_m = c16;
                    if (c16 < min_c16_lift) min_c16_lift = c16;
                    if (gr > best_girth_lift) best_girth_lift = gr;
                }
                if (c16 == 0) {
                    z16_m++;
                    bool h32 = has_C32(g);
                    #pragma omp critical
                    {
                        lifts_zero_c16++;
                        if (!h32) lifts_zero_c16_c32++;
                        cout << "  [ALERT K33 LIFT C16=0!] n=" << g.n << " g=" << gr << " hasC32=" << h32 << endl;
                    }
                }
            }
        }
        lifts_g9 += g9_m; lifts_g10 += g10_m; lifts_g12 += g12_m;
        cout << "  m=" << setw(2) << m << " (n=" << setw(3) << 6*m << "): g>=10=" << setw(5) << g10_m
             << " g>=12=" << setw(4) << g12_m
             << " | min_C16=" << (min_c16_m < 1e17 ? to_string(min_c16_m) : "N/A")
             << " | zero_C16=" << z16_m << endl;
    }

    int pet_samples = smoke ? 1500 : 10000;
    vector<int> pet_ms = smoke ? vector<int>{14, 18, 22} : vector<int>{14, 16, 18, 20, 22, 24, 26, 28, 30, 32};
    cout << "\n--- Part A2: Petersen Z_m-Voltage Lifts (Nonbipartite, n = 10m in [140, 320]) ---" << endl;
    for (int m : pet_ms) {
        long long g9_m = 0, g10_m = 0, g12_m = 0, z16_m = 0;
        long long min_c16_m = 1e18;
        #pragma omp parallel for schedule(dynamic) reduction(+:lifts_tested,g9_m,g10_m,g12_m,z16_m)
        for (int s = 0; s < pet_samples; s++) {
            mt19937_64 rng(990001ULL + m * 100003ULL + s * 7919ULL);
            vector<int> v(15, 0);
            for (int c : pet_chords) v[c] = 1 + (rng() % (m - 1));
            lifts_tested++;
            CubicGraph g = build_lift(pet_edges, 10, v, m);
            if (g.n == 0 || !is_connected(g)) continue;
            int gr = compute_girth(g);
            if (gr >= 9) {
                g9_m++;
                if (gr >= 10) g10_m++;
                if (gr >= 12) g12_m++;
                long long b16 = compute_b16_exact_girth9(g);
                long long c16 = b16 / 32;
                #pragma omp critical
                {
                    if (c16 < min_c16_m) min_c16_m = c16;
                    if (c16 < min_c16_lift) min_c16_lift = c16;
                    if (gr > best_girth_lift) best_girth_lift = gr;
                }
                if (c16 == 0) {
                    z16_m++;
                    bool h32 = has_C32(g);
                    #pragma omp critical
                    {
                        lifts_zero_c16++;
                        if (!h32) lifts_zero_c16_c32++;
                        cout << "  [ALERT PET LIFT C16=0!] n=" << g.n << " g=" << gr << " hasC32=" << h32 << endl;
                    }
                }
            }
        }
        lifts_g9 += g9_m; lifts_g10 += g10_m; lifts_g12 += g12_m;
        cout << "  m=" << setw(2) << m << " (n=" << setw(3) << 10*m << "): g>=9=" << setw(5) << g9_m
             << " g>=10=" << setw(4) << g10_m << " g>=12=" << setw(3) << g12_m
             << " | min_C16=" << (min_c16_m < 1e17 ? to_string(min_c16_m) : "N/A")
             << " | zero_C16=" << z16_m << endl;
    }

    cout << "\n--- Part B: High-Girth (g >= 9) OpenMP Simulated Annealing (n in [132, 240]) ---" << endl;
    vector<int> sa_orders = smoke ? vector<int>{140, 180} : vector<int>{132, 140, 150, 160, 180, 200, 220, 240};
    int sa_restarts = smoke ? 2 : 8;
    int sa_p1_steps = smoke ? 1200 : 4000;
    int sa_p2_steps = smoke ? 150 : 600;
    int sa_g9_found = 0, sa_zero_c16 = 0;

    for (int n : sa_orders) {
        int found_n = 0, z16_n = 0;
        long long best_c16_n = 1e18;
        int max_g_n = 0;

        #pragma omp parallel for schedule(dynamic)
        for (int r = 0; r < sa_restarts; r++) {
            mt19937_64 rng(8955500ULL + (uint64_t)n * 1009 + r * 313);
            CubicGraph g = random_cubic(n, rng);
            long long pen = penalty_girth9(g);
            for (int step = 0; step < sa_p1_steps && pen > 0; step++) {
                int u1 = rng() % n, v1 = g.adj[u1][rng() % 3];
                int u2 = rng() % n, v2 = g.adj[u2][rng() % 3];
                if (u1 == u2 || u1 == v2 || v1 == u2 || v1 == v2) continue;
                if (g.has_edge(u1, u2) || g.has_edge(v1, v2)) continue;
                g.remove_edge(u1, v1); g.remove_edge(u2, v2);
                g.add_edge(u1, u2); g.add_edge(v1, v2);
                long long np = penalty_girth9(g);
                if (np <= pen || (rng() % 1000 < 5)) {
                    pen = np;
                } else {
                    g.remove_edge(u1, u2); g.remove_edge(v1, v2);
                    g.add_edge(u1, v1); g.add_edge(u2, v2);
                }
            }
            if (pen == 0 && is_connected(g)) {
                int gr = compute_girth(g);
                long long c16 = compute_b16_exact_girth9(g) / 32;
                long long best_c16 = c16;
                for (int step = 0; step < sa_p2_steps && best_c16 > 0; step++) {
                    int u1 = rng() % n, v1 = g.adj[u1][rng() % 3];
                    int u2 = rng() % n, v2 = g.adj[u2][rng() % 3];
                    if (u1 == u2 || u1 == v2 || v1 == u2 || v1 == v2) continue;
                    if (g.has_edge(u1, u2) || g.has_edge(v1, v2)) continue;
                    g.remove_edge(u1, v1); g.remove_edge(u2, v2);
                    g.add_edge(u1, u2); g.add_edge(v1, v2);
                    if (compute_girth(g) >= 9) {
                        long long nc16 = compute_b16_exact_girth9(g) / 32;
                        if (nc16 <= c16) {
                            c16 = nc16;
                            if (c16 < best_c16) best_c16 = c16;
                            continue;
                        }
                    }
                    g.remove_edge(u1, u2); g.remove_edge(v1, v2);
                    g.add_edge(u1, v1); g.add_edge(u2, v2);
                }
                #pragma omp critical
                {
                    found_n++; sa_g9_found++;
                    if (gr > max_g_n) max_g_n = gr;
                    if (best_c16 < best_c16_n) best_c16_n = best_c16;
                    if (best_c16 == 0) {
                        z16_n++; sa_zero_c16++;
                        cout << "  [ALERT SA C16=0!] n=" << n << " g=" << gr << " hasC32=" << has_C32(g) << endl;
                    }
                }
            }
        }
        cout << "  SA n=" << setw(3) << n << ": g>=9_found=" << found_n << "/" << sa_restarts
             << " | max_g=" << max_g_n
             << " | min_C16=" << (best_c16_n < 1e17 ? to_string(best_c16_n) : "N/A")
             << " | zero_C16=" << z16_n << endl;
    }

    cout << "\n=== FINAL SUMMARY ===" << endl;
    cout << "Total voltage lifts tested: " << lifts_tested << endl;
    cout << "High-girth lifts found (g>=9 / g>=10 / g>=12): "
         << lifts_g9 << " / " << lifts_g10 << " / " << lifts_g12
         << " (max_girth=" << best_girth_lift << ")" << endl;
    cout << "Lift min_C16: " << (min_c16_lift < 1e17 ? to_string(min_c16_lift) : "N/A")
         << " | zero_C16: " << lifts_zero_c16
         << " | zero_C16_and_C32: " << lifts_zero_c16_c32 << endl;
    cout << "SA g>=9 graphs found: " << sa_g9_found << " | SA zero_C16: " << sa_zero_c16 << endl;
    return 0;
}
