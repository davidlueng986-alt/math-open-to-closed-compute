#include <iostream>
#include <vector>
#include <array>
#include <random>
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstring>
#include <iomanip>
#include <omp.h>

using namespace std;

struct CubicGraph {
    int n;
    vector<array<int, 3>> adj;
    CubicGraph(int n_ = 0) : n(n_), adj(n_) {}

    inline bool has_edge(int u, int v) const {
        return adj[u][0] == v || adj[u][1] == v || adj[u][2] == v;
    }

    bool is_connected() const {
        if (n == 0) return true;
        vector<uint8_t> vis(n, 0);
        vector<int> q;
        q.reserve(n);
        q.push_back(0);
        vis[0] = 1;
        for (size_t i = 0; i < q.size(); ++i)
            for (int v : adj[q[i]])
                if (!vis[v]) { vis[v] = 1; q.push_back(v); }
        return (int)q.size() == n;
    }

    int girth() const {
        int best = n + 1;
        vector<int> dist(n), par(n), q;
        q.reserve(n);
        for (int s = 0; s < n; ++s) {
            fill(dist.begin(), dist.end(), -1);
            fill(par.begin(), par.end(), -1);
            q.clear();
            q.push_back(s);
            dist[s] = 0;
            for (size_t i = 0; i < q.size(); ++i) {
                int u = q[i];
                if (2 * dist[u] + 1 >= best) break;
                for (int v : adj[u]) {
                    if (dist[v] == -1) {
                        dist[v] = dist[u] + 1;
                        par[v] = u;
                        q.push_back(v);
                    } else if (par[u] != v) {
                        int cyc = dist[u] + dist[v] + 1;
                        if (cyc < best) best = cyc;
                    }
                }
            }
        }
        return best;
    }

    bool edge_has_short_cycle(int u, int v, int maxL) const {
        vector<int> dist(n, -1), q;
        q.reserve(n);
        q.push_back(v);
        dist[v] = 0;
        for (size_t i = 0; i < q.size(); ++i) {
            int cur = q[i];
            if (dist[cur] >= maxL - 1) break;
            for (int nxt : adj[cur]) {
                if (cur == v && nxt == u) continue;
                if (nxt == u) return true;
                if (dist[nxt] == -1) {
                    dist[nxt] = dist[cur] + 1;
                    q.push_back(nxt);
                }
            }
        }
        return false;
    }

    int edge_cycles(int u, int v, int L, int cap = 500000) const {
        int cnt = 0;
        vector<uint8_t> vis(n, 0);
        vis[u] = 1; vis[v] = 1;
        auto dfs = [&](auto&& self, int cur, int depth) -> void {
            if (cnt >= cap) return;
            if (depth == L - 2) {
                for (int nxt : adj[cur]) if (nxt == u) { cnt++; return; }
                return;
            }
            for (int nxt : adj[cur]) {
                if (!vis[nxt]) {
                    vis[nxt] = 1;
                    self(self, nxt, depth + 1);
                    vis[nxt] = 0;
                    if (cnt >= cap) return;
                }
            }
        };
        dfs(dfs, v, 0);
        return cnt;
    }

    int pair_edge_cycles(int u1, int v1, int u2, int v2, int L) const {
        int cnt = 0;
        vector<uint8_t> vis(n, 0);
        vis[u1] = 1; vis[v1] = 1;
        auto dfs = [&](auto&& self, int cur, int depth, bool used_e2) -> void {
            if (depth == L - 2) {
                if (used_e2) {
                    for (int nxt : adj[cur]) if (nxt == u1) { cnt++; return; }
                }
                return;
            }
            for (int nxt : adj[cur]) {
                if (!vis[nxt]) {
                    bool hit = used_e2 || (cur == u2 && nxt == v2) || (cur == v2 && nxt == u2);
                    vis[nxt] = 1;
                    self(self, nxt, depth + 1, hit);
                    vis[nxt] = 0;
                }
            }
        };
        dfs(dfs, v1, 0, false);
        return cnt;
    }

    int count_cycles_len(int L, int cap = 500000) const {
        int total = 0;
        vector<uint8_t> vis(n, 0);
        auto dfs = [&](auto&& self, int start, int cur, int depth) -> void {
            if (total >= cap) return;
            if (depth == L - 1) {
                for (int nxt : adj[cur]) if (nxt == start) { total++; return; }
                return;
            }
            for (int nxt : adj[cur]) {
                if (nxt > start && !vis[nxt]) {
                    vis[nxt] = 1;
                    self(self, start, nxt, depth + 1);
                    vis[nxt] = 0;
                    if (total >= cap) return;
                }
            }
        };
        for (int s = 0; s < n; ++s) {
            vis[s] = 1;
            for (int nxt : adj[s]) if (nxt > s) {
                vis[nxt] = 1;
                dfs(dfs, s, nxt, 1);
                vis[nxt] = 0;
                if (total >= cap) break;
            }
            vis[s] = 0;
            if (total >= cap) break;
        }
        return total / 2;
    }

    int count_edges_on_cycle(int L, int budget_per_edge = 25000) const {
        int covered = 0;
        vector<uint8_t> vis(n, 0);
        for (int u = 0; u < n; ++u) {
            for (int v : adj[u]) {
                if (v < u) continue;
                int steps = 0;
                bool found = false;
                vis[u] = 1; vis[v] = 1;
                auto dfs = [&](auto&& self, int cur, int depth) -> void {
                    if (found || steps >= budget_per_edge) return;
                    steps++;
                    if (depth == L - 2) {
                        for (int nxt : adj[cur]) if (nxt == u) { found = true; return; }
                        return;
                    }
                    for (int nxt : adj[cur]) {
                        if (!vis[nxt]) {
                            vis[nxt] = 1;
                            self(self, nxt, depth + 1);
                            vis[nxt] = 0;
                            if (found) return;
                        }
                    }
                };
                dfs(dfs, v, 0);
                vis[u] = 0; vis[v] = 0;
                if (found) covered++;
            }
        }
        return covered;
    }

    int short_cycle_penalty(int target_g) const {
        int pen = 0;
        for (int L = 3; L < target_g; ++L) {
            int w = (L <= 5) ? 20 : ((L <= 7) ? 8 : ((L == 8) ? 4 : 2));
            pen += w * count_cycles_len(L, 4000);
        }
        return pen;
    }
};

inline void replace_nbr(CubicGraph& G, int u, int old_v, int new_v) {
    for (int i = 0; i < 3; ++i) if (G.adj[u][i] == old_v) { G.adj[u][i] = new_v; return; }
}

struct BaseGraph {
    string name;
    int n;
    vector<pair<int, int>> edges;
};

BaseGraph make_petersen() {
    BaseGraph B{"Petersen10", 10, {}};
    for (int i = 0; i < 5; ++i) {
        B.edges.push_back({i, (i + 1) % 5});
        B.edges.push_back({5 + i, 5 + (i + 2) % 5});
        B.edges.push_back({i, 5 + i});
    }
    return B;
}

BaseGraph make_heawood() {
    BaseGraph B{"Heawood14", 14, {}};
    for (int i = 0; i < 14; ++i) {
        B.edges.push_back({i, (i + 1) % 14});
        if (i % 2 == 0) B.edges.push_back({i, (i + 5) % 14});
    }
    return B;
}

BaseGraph make_pappus() {
    BaseGraph B{"Pappus18", 18, {}};
    vector<int> lcf = {5, 7, -7, 7, -7, -5};
    for (int i = 0; i < 18; ++i) {
        B.edges.push_back({i, (i + 1) % 18});
        int j = (i + lcf[i % 6] + 18) % 18;
        if (i < j) B.edges.push_back({i, j});
    }
    return B;
}

CubicGraph build_voltage_lift(const BaseGraph& B, int m, const vector<int>& volt) {
    int N = B.n * m;
    CubicGraph G(N);
    vector<int> deg(N, 0);
    for (size_t e = 0; e < B.edges.size(); ++e) {
        int u = B.edges[e].first, v = B.edges[e].second;
        int w = ((volt[e] % m) + m) % m;
        for (int r = 0; r < m; ++r) {
            int U = u * m + r;
            int V = v * m + ((r + w) % m);
            G.adj[U][deg[U]++] = V;
            G.adj[V][deg[V]++] = U;
        }
    }
    return G;
}

int lift_short_cycles_orb0(const CubicGraph& G, int base_n, int m, int maxL) {
    int cnt = 0;
    vector<uint8_t> vis(G.n, 0);
    for (int u0 = 0; u0 < base_n; ++u0) {
        int s = u0 * m;
        vis[s] = 1;
        auto dfs = [&](auto&& self, int cur, int depth) -> void {
            if (cnt > 2000) return;
            for (int nxt : G.adj[cur]) {
                if (nxt == s && depth >= 2) { cnt++; }
                else if (depth + 1 < maxL && !vis[nxt]) {
                    vis[nxt] = 1;
                    self(self, nxt, depth + 1);
                    vis[nxt] = 0;
                    if (cnt > 2000) return;
                }
            }
        };
        for (int nxt : G.adj[s]) {
            vis[nxt] = 1;
            dfs(dfs, nxt, 1);
            vis[nxt] = 0;
        }
        vis[s] = 0;
    }
    return cnt;
}

int lift_c16_orb0(const CubicGraph& G, int base_n, int m, int cap = 10000) {
    int cnt = 0;
    vector<uint8_t> vis(G.n, 0);
    for (int u0 = 0; u0 < base_n; ++u0) {
        int s = u0 * m;
        vis[s] = 1;
        auto dfs = [&](auto&& self, int cur, int depth) -> void {
            if (cnt >= cap) return;
            if (depth == 15) {
                for (int nxt : G.adj[cur]) if (nxt == s) { cnt++; return; }
                return;
            }
            for (int nxt : G.adj[cur]) {
                if (!vis[nxt]) {
                    vis[nxt] = 1;
                    self(self, nxt, depth + 1);
                    vis[nxt] = 0;
                    if (cnt >= cap) return;
                }
            }
        };
        for (int nxt : G.adj[s]) {
            vis[nxt] = 1;
            dfs(dfs, nxt, 1);
            vis[nxt] = 0;
        }
        vis[s] = 0;
    }
    return cnt;
}

CubicGraph random_cubic(int n, mt19937_64& rng) {
    while (true) {
        vector<int> stubs(3 * n);
        for (int i = 0; i < n; ++i) stubs[3*i] = stubs[3*i+1] = stubs[3*i+2] = i;
        shuffle(stubs.begin(), stubs.end(), rng);
        CubicGraph G(n);
        vector<int> deg(n, 0);
        bool ok = true;
        for (int i = 0; i < 3 * n; i += 2) {
            int u = stubs[i], v = stubs[i+1];
            if (u == v) { ok = false; break; }
            for (int j = 0; j < deg[u]; ++j) if (G.adj[u][j] == v) { ok = false; break; }
            if (!ok) break;
            G.adj[u][deg[u]++] = v;
            G.adj[v][deg[v]++] = u;
        }
        if (ok && G.is_connected()) return G;
    }
}

int main(int argc, char** argv) {
    bool smoke = (argc > 1 && string(argv[1]) == "--smoke");
    int volt_sa_steps = smoke ? 400 : 8000;
    int sa_steps1     = smoke ? 6000 : 80000;
    int sa_steps2     = smoke ? 2500 : 50000;

    cout << "=== WAVE 8 AGENT #10: HIGH-GIRTH (g in [9,14]) COUNTEREXAMPLE HUNT ===" << endl;
    cout << "Mode: " << (smoke ? "SMOKE" : "FULL") << " | OpenMP threads: " << omp_get_max_threads() << endl;

    vector<BaseGraph> bases = {make_petersen(), make_heawood(), make_pappus()};
    struct VJob { int bidx; int m; int target_g; uint64_t seed; };
    vector<VJob> vjobs;
    if (smoke) {
        vjobs = {{0, 15, 9, 101}, {1, 13, 10, 102}, {1, 17, 10, 103}};
    } else {
        for (int m : {13, 15, 17, 19, 23, 29, 31})
            vjobs.push_back({0, m, 9, 1000ULL + m});
        for (int m : {11, 13, 15, 17, 19, 23, 25, 29})
            vjobs.push_back({1, m, 10, 2000ULL + m});
        for (int m : {9, 11, 13, 15, 17, 19, 21})
            vjobs.push_back({2, m, 10, 3000ULL + m});
    }

    struct VRes {
        string base; int m; int N; int target_g; bool ok; int g;
        int best_c16_orb0; int c32_edges; int total_edges;
    };
    vector<VRes> vres(vjobs.size());

    #pragma omp parallel for schedule(dynamic)
    for (size_t idx = 0; idx < vjobs.size(); ++idx) {
        const auto& B = bases[vjobs[idx].bidx];
        int m = vjobs[idx].m;
        int tg = vjobs[idx].target_g;
        int N = B.n * m;
        mt19937_64 rng(vjobs[idx].seed);
        vector<int> volt(B.edges.size(), 0);
        for (size_t e = 0; e < B.edges.size(); ++e) volt[e] = (int)(rng() % m);
        CubicGraph G = build_voltage_lift(B, m, volt);
        int cur_sc = G.is_connected() ? lift_short_cycles_orb0(G, B.n, m, tg) : 999999;

        for (int it = 0; it < volt_sa_steps && cur_sc > 0; ++it) {
            int e = (int)(rng() % B.edges.size());
            int old_v = volt[e];
            volt[e] = (int)(rng() % m);
            if (volt[e] == old_v) continue;
            CubicGraph G2 = build_voltage_lift(B, m, volt);
            int sc2 = G2.is_connected() ? lift_short_cycles_orb0(G2, B.n, m, tg) : 999999;
            double T = 10.0 * pow(0.01, (double)it / volt_sa_steps);
            if (sc2 <= cur_sc || uniform_real_distribution<double>(0, 1)(rng) < exp(-(sc2 - cur_sc) / T)) {
                cur_sc = sc2;
                G = std::move(G2);
            } else {
                volt[e] = old_v;
            }
        }
        if (cur_sc > 0) {
            vres[idx] = {B.name, m, N, tg, false, G.girth(), -1, 0, 3 * N / 2};
            continue;
        }
        int best_c16 = lift_c16_orb0(G, B.n, m, 20000);
        CubicGraph bestG = G;
        int cur_c16 = best_c16;
        int p2_steps = smoke ? 100 : 1200;
        for (int it = 0; it < p2_steps && best_c16 > 0; ++it) {
            int e = (int)(rng() % B.edges.size());
            int old_v = volt[e];
            volt[e] = (int)(rng() % m);
            if (volt[e] == old_v) continue;
            CubicGraph G2 = build_voltage_lift(B, m, volt);
            if (!G2.is_connected() || lift_short_cycles_orb0(G2, B.n, m, tg) > 0) {
                volt[e] = old_v;
                continue;
            }
            int c16_2 = lift_c16_orb0(G2, B.n, m, 20000);
            if (c16_2 <= cur_c16) {
                cur_c16 = c16_2;
                if (c16_2 < best_c16) { best_c16 = c16_2; bestG = std::move(G2); }
            } else {
                volt[e] = old_v;
            }
        }
        int fg = bestG.girth();
        int c32_e = bestG.count_edges_on_cycle(32, 20000);
        vres[idx] = {B.name, m, N, tg, true, fg, best_c16, c32_e, 3 * N / 2};
    }

    cout << "\n--- CAMPAIGN 1 RESULTS (Guided Z_m Voltage Lifts, girth >= 9/10) ---" << endl;
    int v_ok = 0, v_z16 = 0, v_max_g = 0;
    for (const auto& r : vres) {
        if (r.ok) { v_ok++; if (r.best_c16_orb0 == 0) v_z16++; if (r.g > v_max_g) v_max_g = r.g; }
        cout << r.base << " m=" << r.m << " N=" << r.N << " target_g=" << r.target_g
             << " ok=" << r.ok << " g=" << r.g
             << " best_C16_orb0=" << r.best_c16_orb0
             << " C32_edges=" << r.c32_edges << "/" << r.total_edges << endl;
    }
    cout << "CAMPAIGN1_SUMMARY ok=" << v_ok << "/" << vres.size()
         << " max_g=" << v_max_g << " zero_c16=" << v_z16 << endl;

    struct SATask { int n; int target_g; uint64_t seed; };
    vector<SATask> stasks;
    if (smoke) {
        stasks = {{130, 9, 893000}, {160, 10, 896000}};
    } else {
        for (int n : {130, 140, 160, 180, 200, 240})
            for (int r = 0; r < 2; ++r)
                stasks.push_back({n, 9, 880000ULL + n * 100ULL + r});
        for (int n : {160, 180, 200, 220, 240, 260})
            for (int r = 0; r < 2; ++r)
                stasks.push_back({n, 10, 990000ULL + n * 100ULL + r});
    }

    struct SARes {
        int n; int target_g; uint64_t seed; bool ok; int final_g;
        int init_c16; int best_c16; int c32_edges; int total_edges;
    };
    vector<SARes> sres(stasks.size());

    #pragma omp parallel for schedule(dynamic)
    for (size_t idx = 0; idx < stasks.size(); ++idx) {
        int n = stasks[idx].n;
        int tg = stasks[idx].target_g;
        uint64_t seed = stasks[idx].seed;
        mt19937_64 rng(seed);
        CubicGraph G = random_cubic(n, rng);
        int cur_pen = G.short_cycle_penalty(tg);
        for (int it = 0; it < sa_steps1 && cur_pen > 0; ++it) {
            double T = 15.0 * pow(0.005, (double)it / sa_steps1);
            int u1 = rng() % n, v1 = G.adj[u1][rng() % 3];
            int u2 = rng() % n, v2 = G.adj[u2][rng() % 3];
            if (u1 == u2 || u1 == v2 || v1 == u2 || v1 == v2) continue;
            if (G.has_edge(u1, u2) || G.has_edge(v1, v2)) continue;
            replace_nbr(G, u1, v1, u2); replace_nbr(G, u2, v2, u1);
            replace_nbr(G, v1, u1, v2); replace_nbr(G, v2, u2, v1);
            if (!G.is_connected()) {
                replace_nbr(G, u1, u2, v1); replace_nbr(G, u2, u1, v2);
                replace_nbr(G, v1, v2, u1); replace_nbr(G, v2, v1, u2);
                continue;
            }
            int np = G.short_cycle_penalty(tg);
            if (np <= cur_pen || uniform_real_distribution<double>(0, 1)(rng) < exp(-(np - cur_pen) / T)) {
                cur_pen = np;
            } else {
                replace_nbr(G, u1, u2, v1); replace_nbr(G, u2, u1, v2);
                replace_nbr(G, v1, v2, u1); replace_nbr(G, v2, v1, u2);
            }
        }
        int g0 = G.girth();
        if (g0 < tg) {
            sres[idx] = {n, tg, seed, false, g0, -1, -1, 0, 3 * n / 2};
            continue;
        }
        int init_c16 = G.count_cycles_len(16, 500000);
        int cur_c16 = init_c16;
        int best_c16 = cur_c16;
        CubicGraph bestG = G;
        for (int it = 0; it < sa_steps2 && best_c16 > 0; ++it) {
            double T = 20.0 * pow(0.002, (double)it / sa_steps2);
            int u1 = rng() % n, v1 = G.adj[u1][rng() % 3];
            int u2 = rng() % n, v2 = G.adj[u2][rng() % 3];
            if (u1 == u2 || u1 == v2 || v1 == u2 || v1 == v2) continue;
            if (G.has_edge(u1, u2) || G.has_edge(v1, v2)) continue;
            replace_nbr(G, u1, v1, u2); replace_nbr(G, u2, v2, u1);
            replace_nbr(G, v1, u1, v2); replace_nbr(G, v2, u2, v1);
            if (G.edge_has_short_cycle(u1, u2, tg - 1) || G.edge_has_short_cycle(v1, v2, tg - 1) || !G.is_connected()) {
                replace_nbr(G, u1, u2, v1); replace_nbr(G, u2, u1, v2);
                replace_nbr(G, v1, v2, u1); replace_nbr(G, v2, v1, u2);
                continue;
            }
            int added = G.edge_cycles(u1, u2, 16) + G.edge_cycles(v1, v2, 16)
                      - G.pair_edge_cycles(u1, u2, v1, v2, 16);
            replace_nbr(G, u1, u2, v1); replace_nbr(G, u2, u1, v2);
            replace_nbr(G, v1, v2, u1); replace_nbr(G, v2, v1, u2);
            int removed = G.edge_cycles(u1, v1, 16) + G.edge_cycles(u2, v2, 16)
                        - G.pair_edge_cycles(u1, v1, u2, v2, 16);
            int delta = added - removed;
            if (delta <= 0 || uniform_real_distribution<double>(0, 1)(rng) < exp(-delta / T)) {
                replace_nbr(G, u1, v1, u2); replace_nbr(G, u2, v2, u1);
                replace_nbr(G, v1, u1, v2); replace_nbr(G, v2, u2, v1);
                cur_c16 += delta;
                if (cur_c16 < best_c16) { best_c16 = cur_c16; bestG = G; }
            }
        }
        int fg = bestG.girth();
        int c32_e = bestG.count_edges_on_cycle(32, 25000);
        sres[idx] = {n, tg, seed, true, fg, init_c16, best_c16, c32_e, 3 * n / 2};
    }

    cout << "\n--- CAMPAIGN 2 RESULTS (Free Cubic SA, Strict Girth >= 9 / 10) ---" << endl;
    int sa_ok = 0, sa_z16 = 0, min_sa_c16 = 1e9;
    for (const auto& r : sres) {
        if (r.ok) {
            sa_ok++;
            if (r.best_c16 == 0) sa_z16++;
            if (r.best_c16 < min_sa_c16) min_sa_c16 = r.best_c16;
        }
        cout << "n=" << r.n << " target_g=" << r.target_g << " seed=" << r.seed
             << " ok=" << r.ok << " g=" << r.final_g
             << " init_C16=" << r.init_c16 << " best_C16=" << r.best_c16
             << " C32_edges=" << r.c32_edges << "/" << r.total_edges << endl;
    }
    cout << "CAMPAIGN2_SUMMARY ok=" << sa_ok << "/" << sres.size()
         << " zero_c16=" << sa_z16 << " min_c16=" << (sa_ok > 0 ? min_sa_c16 : -1) << endl;
    return 0;
}
