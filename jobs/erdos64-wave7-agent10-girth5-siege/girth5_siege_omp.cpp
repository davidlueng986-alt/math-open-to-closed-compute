#include <iostream>
#include <vector>
#include <array>
#include <random>
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <map>
#include <set>
#include <omp.h>
#include <fstream>

using namespace std;

struct CubicGraph {
    int n;
    vector<array<int, 3>> adj;
    CubicGraph(int n_ = 0) : n(n_), adj(n_) {}

    inline bool has_edge(int u, int v) const {
        return adj[u][0] == v || adj[u][1] == v || adj[u][2] == v;
    }

    int count_c3() const {
        int c = 0;
        for (int u = 0; u < n; ++u)
            for (int i = 0; i < 3; ++i) {
                int v = adj[u][i]; if (v < u) continue;
                for (int j = i + 1; j < 3; ++j) {
                    int w = adj[u][j]; if (w < u) continue;
                    if (has_edge(v, w)) c++;
                }
            }
        return c;
    }

    int count_c4() const {
        int c = 0;
        for (int u = 0; u < n; ++u)
            for (int v = u + 1; v < n; ++v) {
                int cn = 0;
                for (int a : adj[u]) for (int b : adj[v]) if (a == b) cn++;
                c += cn * (cn - 1) / 2;
            }
        return c / 2;
    }

    int edge_cycles(int u, int v, int L) const {
        int cnt = 0;
        vector<uint8_t> vis(n, 0);
        vis[u] = 1; vis[v] = 1;
        auto dfs = [&](auto&& self, int cur, int depth) -> void {
            if (depth == L - 2) {
                for (int nxt : adj[cur]) if (nxt == u) { cnt++; return; }
                return;
            }
            for (int nxt : adj[cur]) {
                if (!vis[nxt]) {
                    vis[nxt] = 1;
                    self(self, nxt, depth + 1);
                    vis[nxt] = 0;
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

    void analyze_c5_clusters(int& num_c5, int& iso_c5, int& theta233, int& other_comp) const {
        vector<vector<int>> c5s;
        vector<uint8_t> vis(n, 0);
        vector<int> path;
        auto dfs = [&](auto&& self, int s, int cur, int depth) -> void {
            if (depth == 4) {
                for (int nxt : adj[cur])
                    if (nxt == s && path[1] < path[4]) c5s.push_back(path);
                return;
            }
            for (int nxt : adj[cur]) {
                if (nxt > s && !vis[nxt]) {
                    vis[nxt] = 1; path.push_back(nxt);
                    self(self, s, nxt, depth + 1);
                    path.pop_back(); vis[nxt] = 0;
                }
            }
        };
        for (int s = 0; s < n; ++s) {
            vis[s] = 1; path = {s};
            for (int nxt : adj[s]) if (nxt > s) {
                vis[nxt] = 1; path.push_back(nxt);
                dfs(dfs, s, nxt, 1);
                path.pop_back(); vis[nxt] = 0;
            }
            vis[s] = 0;
        }
        num_c5 = (int)c5s.size();
        int m = num_c5;
        vector<int> par(m);
        for (int i = 0; i < m; ++i) par[i] = i;
        auto find = [&](auto&& self, int x) -> int { return par[x] == x ? x : par[x] = self(self, par[x]); };
        for (int i = 0; i < m; ++i)
            for (int j = i + 1; j < m; ++j) {
                bool share = false;
                for (int u : c5s[i]) for (int v : c5s[j]) if (u == v) share = true;
                if (share) par[find(find, i)] = find(find, j);
            }
        map<int, vector<int>> comps;
        for (int i = 0; i < m; ++i) comps[find(find, i)].push_back(i);
        iso_c5 = theta233 = other_comp = 0;
        for (auto& [root, idxs] : comps) {
            set<int> vs;
            for (int idx : idxs) for (int v : c5s[idx]) vs.insert(v);
            if (idxs.size() == 1 && vs.size() == 5) iso_c5++;
            else if (idxs.size() == 2 && vs.size() == 7) theta233++;
            else other_comp++;
        }
    }

    int count_edges_on_c32(int budget_per_edge = 50000) const {
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
                    if (depth == 30) {
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

    bool is_connected() const {
        vector<uint8_t> vis(n, 0);
        vector<int> q; q.reserve(n);
        q.push_back(0); vis[0] = 1;
        for (size_t i = 0; i < q.size(); ++i)
            for (int v : adj[q[i]])
                if (!vis[v]) { vis[v] = 1; q.push_back(v); }
        return (int)q.size() == n;
    }
};

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
            G.adj[u][deg[u]++] = v; G.adj[v][deg[v]++] = u;
        }
        if (ok && G.is_connected()) return G;
    }
}

inline void replace_nbr(CubicGraph& G, int u, int old_v, int new_v) {
    for (int i = 0; i < 3; ++i) if (G.adj[u][i] == old_v) { G.adj[u][i] = new_v; return; }
}

struct Task { int n; uint64_t seed; int steps; };
struct Result {
    int n; uint64_t seed; int best_c16; int c5; int iso_c5; int theta233; int other_c5;
    int c6; int c7; int c32_edges; int total_edges; bool phase1_ok;
};

int main() {
    vector<Task> tasks;
    vector<int> sizes = {60, 70, 80, 90, 100, 120, 140};
    for (int n : sizes) {
        for (int r = 0; r < 4; ++r) {
            tasks.push_back({n, (uint64_t)(10000 + n * 100 + r), 60000});
        }
    }
    vector<Result> results(tasks.size());

    #pragma omp parallel for schedule(dynamic)
    for (size_t idx = 0; idx < tasks.size(); ++idx) {
        auto [n, seed, steps] = tasks[idx];
        mt19937_64 rng(seed);
        CubicGraph G = random_cubic(n, rng);
        int cur_c3 = G.count_c3(), cur_c4 = G.count_c4(), cur_c8 = G.count_cycles_len(8, 100000);
        int cur_e = 20*cur_c3 + 20*cur_c4 + 5*cur_c8;
        for (int it = 0; it < 60000 && cur_e > 0; ++it) {
            double T = 12.0 * pow(0.005, (double)it / 60000);
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
            int nc3 = G.count_c3(), nc4 = G.count_c4();
            int nc8 = (nc3 + nc4 <= 4) ? G.count_cycles_len(8, 100000) : G.count_cycles_len(8, 200);
            int ne = 20*nc3 + 20*nc4 + 5*nc8;
            if (ne <= cur_e || uniform_real_distribution<double>(0,1)(rng) < exp(-(ne - cur_e)/T)) {
                cur_c3 = nc3; cur_c4 = nc4; cur_c8 = nc8; cur_e = ne;
            } else {
                replace_nbr(G, u1, u2, v1); replace_nbr(G, u2, u1, v2);
                replace_nbr(G, v1, v2, u1); replace_nbr(G, v2, v1, u2);
            }
        }
        if (cur_e > 0) {
            results[idx] = {n, seed, -1, 0, 0, 0, 0, 0, 0, 0, 3*n/2, false};
            continue;
        }
        int cur_c16 = G.count_cycles_len(16, 500000);
        int best_c16 = cur_c16;
        CubicGraph bestG = G;
        for (int it = 0; it < steps && best_c16 > 0; ++it) {
            double T = 25.0 * pow(0.002, (double)it / steps);
            int u1 = rng() % n, v1 = G.adj[u1][rng() % 3];
            int u2 = rng() % n, v2 = G.adj[u2][rng() % 3];
            if (u1 == u2 || u1 == v2 || v1 == u2 || v1 == v2) continue;
            if (G.has_edge(u1, u2) || G.has_edge(v1, v2)) continue;
            replace_nbr(G, u1, v1, u2); replace_nbr(G, u2, v2, u1);
            replace_nbr(G, v1, u1, v2); replace_nbr(G, v2, u2, v1);
            if (G.edge_cycles(u1, u2, 3) > 0 || G.edge_cycles(v1, v2, 3) > 0 ||
                G.edge_cycles(u1, u2, 4) > 0 || G.edge_cycles(v1, v2, 4) > 0 ||
                G.edge_cycles(u1, u2, 8) > 0 || G.edge_cycles(v1, v2, 8) > 0 ||
                !G.is_connected()) {
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
            if (delta <= 0 || uniform_real_distribution<double>(0,1)(rng) < exp(-delta / T)) {
                replace_nbr(G, u1, v1, u2); replace_nbr(G, u2, v2, u1);
                replace_nbr(G, v1, u1, v2); replace_nbr(G, v2, u2, v1);
                cur_c16 += delta;
                if (cur_c16 < best_c16) { best_c16 = cur_c16; bestG = G; }
            }
        }
        int num_c5, iso_c5, theta233, other_c5;
        bestG.analyze_c5_clusters(num_c5, iso_c5, theta233, other_c5);
        int c6 = bestG.count_cycles_len(6, 50000);
        int c7 = bestG.count_cycles_len(7, 50000);
        int c32_edges = bestG.count_edges_on_c32(50000);
        results[idx] = {n, seed, best_c16, num_c5, iso_c5, theta233, other_c5, c6, c7, c32_edges, 3*n/2, true};
    }

    int total_ok = 0, total_other = 0, zero_c16 = 0;
    for (const auto& r : results) {
        if (r.phase1_ok) {
            total_ok++;
            total_other += r.other_c5;
            if (r.best_c16 == 0) zero_c16++;
        }
        cout << "n=" << r.n << " seed=" << r.seed << " ok=" << r.phase1_ok
             << " C16=" << r.best_c16
             << " C5=" << r.c5 << " (iso=" << r.iso_c5 << ", theta233=" << r.theta233 << ", other=" << r.other_c5 << ")"
             << " C6=" << r.c6 << " C7=" << r.c7
             << " C32_edges=" << r.c32_edges << "/" << r.total_edges << endl;
    }
    cout << "SUMMARY total_ok=" << total_ok << "/" << results.size()
         << " zero_c16=" << zero_c16
         << " total_c5_dichotomy_violations=" << total_other << endl;
    return 0;
}
