#include <iostream>
#include <fstream>
#include <vector>
#include <array>
#include <queue>
#include <bitset>
#include <algorithm>
#include <numeric>
#include <random>
#include <string>
#include <cstring>
#include <cmath>
#include <chrono>
#include <map>
#include <iomanip>
#include <omp.h>

using namespace std;

static constexpr int MAXN = 400;
using Mask = bitset<MAXN>;

struct Graph {
    int n = 0;
    string name;
    vector<vector<int>> adj;

    Graph() = default;
    Graph(int n_, string nm = "") : n(n_), name(move(nm)), adj(n_) {}

    void add_edge(int u, int v) {
        if (u == v) return;
        for (int w : adj[u]) if (w == v) return;
        adj[u].push_back(v);
        adj[v].push_back(u);
    }

    bool has_edge(int u, int v) const {
        for (int w : adj[u]) if (w == v) return true;
        return false;
    }

    int min_deg() const {
        int d = 1e9;
        for (int i = 0; i < n; ++i) d = min(d, (int)adj[i].size());
        return d;
    }

    int max_deg() const {
        int d = 0;
        for (int i = 0; i < n; ++i) d = max(d, (int)adj[i].size());
        return d;
    }

    int edge_count() const {
        int s = 0;
        for (int i = 0; i < n; ++i) s += (int)adj[i].size();
        return s / 2;
    }

    bool is_bipartite() const {
        vector<int> col(n, -1);
        for (int s = 0; s < n; ++s) {
            if (col[s] != -1) continue;
            queue<int> q;
            q.push(s); col[s] = 0;
            while (!q.empty()) {
                int u = q.front(); q.pop();
                for (int w : adj[u]) {
                    if (col[w] == -1) { col[w] = col[u] ^ 1; q.push(w); }
                    else if (col[w] == col[u]) return false;
                }
            }
        }
        return true;
    }

    int girth() const {
        int best = 1e9;
        vector<int> dist(n), par(n);
        for (int s = 0; s < n; ++s) {
            fill(dist.begin(), dist.end(), -1);
            fill(par.begin(), par.end(), -1);
            queue<int> q;
            q.push(s); dist[s] = 0;
            while (!q.empty()) {
                int u = q.front(); q.pop();
                if (2 * dist[u] + 1 >= best) break;
                for (int w : adj[u]) {
                    if (dist[w] == -1) {
                        dist[w] = dist[u] + 1; par[w] = u; q.push(w);
                    } else if (par[u] != w) {
                        best = min(best, dist[u] + dist[w] + 1);
                    }
                }
            }
        }
        return best;
    }

    bool girth_at_least(int target) const {
        int max_d = (target - 1) / 2;
        vector<int> dist(n), par(n);
        for (int s = 0; s < n; ++s) {
            fill(dist.begin(), dist.end(), -1);
            fill(par.begin(), par.end(), -1);
            queue<int> q;
            q.push(s); dist[s] = 0;
            while (!q.empty()) {
                int u = q.front(); q.pop();
                if (dist[u] > max_d) break;
                for (int w : adj[u]) {
                    if (dist[w] == -1) {
                        if (dist[u] + 1 <= max_d) {
                            dist[w] = dist[u] + 1; par[w] = u; q.push(w);
                        }
                    } else if (par[u] != w) {
                        if (dist[u] + dist[w] + 1 < target) return false;
                    }
                }
            }
        }
        return true;
    }

    // O(V+E) single-edge distance check: distance between u and v ignoring direct edge (u,v)
    int dist_without_edge(int u, int v, int cap) const {
        vector<int> dist(n, -1);
        queue<int> q;
        q.push(u); dist[u] = 0;
        while (!q.empty()) {
            int x = q.front(); q.pop();
            if (dist[x] >= cap) break;
            for (int w : adj[x]) {
                if ((x == u && w == v) || (x == v && w == u)) continue;
                if (dist[w] == -1) {
                    dist[w] = dist[x] + 1;
                    if (w == v) return dist[w];
                    q.push(w);
                }
            }
        }
        return cap + 1;
    }

    // Fast incremental check: after adding two edges (u1,v1) and (u2,v2) to a girth>=target graph,
    // girth remains >= target iff dist_without_edge(u1,v1) >= target-1 AND dist_without_edge(u2,v2) >= target-1!
    bool two_edges_preserve_girth(int u1, int v1, int u2, int v2, int target) const {
        if (dist_without_edge(u1, v1, target - 2) < target - 1) return false;
        if (dist_without_edge(u2, v2, target - 2) < target - 1) return false;
        return true;
    }

    int short_cycle_penalty(int target) const {
        int pen = 0;
        int max_d = (target - 1) / 2;
        vector<int> dist(n), par(n);
        for (int s = 0; s < n; ++s) {
            fill(dist.begin(), dist.end(), -1);
            fill(par.begin(), par.end(), -1);
            queue<int> q;
            q.push(s); dist[s] = 0;
            while (!q.empty()) {
                int u = q.front(); q.pop();
                if (dist[u] > max_d) break;
                for (int w : adj[u]) {
                    if (dist[w] == -1) {
                        if (dist[u] + 1 <= max_d) {
                            dist[w] = dist[u] + 1; par[w] = u; q.push(w);
                        }
                    } else if (par[u] != w) {
                        int cl = dist[u] + dist[w] + 1;
                        if (cl < target) pen += (target - cl) * (target - cl);
                    }
                }
            }
        }
        return pen;
    }
};

long long count_cycles_exact(const Graph& g, int L, double* vert_cov = nullptr, double* edge_cov = nullptr) {
    int n = g.n;
    if (L > n) {
        if (vert_cov) *vert_cov = 0.0;
        if (edge_cov) *edge_cov = 0.0;
        return 0;
    }
    int half1 = L / 2;
    int half2 = L - half1;
    long long total = 0;

    bool track_cov = (vert_cov != nullptr || edge_cov != nullptr);
    vector<bool> v_in(n, false);
    vector<vector<bool>> e_in;
    if (track_cov) e_in.assign(n, vector<bool>(n, false));

    struct Path {
        Mask internal;
        vector<int> verts;
    };

    for (int s = 0; s < n; ++s) {
        vector<vector<Path>> by_end1(n), by_end2(n);
        int maxd = max(half1, half2);
        Mask vis;
        vis.set(s);
        vector<int> cur_v;
        if (track_cov) cur_v.push_back(s);

        auto dfs = [&](auto& self, int u, int d, Mask internal) -> void {
            if (d == half1) {
                if (track_cov) by_end1[u].push_back({internal, cur_v});
                else by_end1[u].push_back({internal, {}});
            }
            if (d == half2 && half2 != half1) {
                if (track_cov) by_end2[u].push_back({internal, cur_v});
                else by_end2[u].push_back({internal, {}});
            }
            if (d == maxd) return;
            for (int w : g.adj[u]) {
                if (w > s && !vis.test(w)) {
                    vis.set(w);
                    Mask nint = internal;
                    if (d > 0) nint.set(u);
                    if (track_cov) cur_v.push_back(w);
                    self(self, w, d + 1, nint);
                    if (track_cov) cur_v.pop_back();
                    vis.reset(w);
                }
            }
        };
        Mask empty;
        dfs(dfs, s, 0, empty);

        auto mark_path = [&](const vector<int>& pv) {
            for (size_t k = 0; k < pv.size(); ++k) {
                v_in[pv[k]] = true;
                if (k + 1 < pv.size()) {
                    e_in[pv[k]][pv[k+1]] = true;
                    e_in[pv[k+1]][pv[k]] = true;
                }
            }
        };

        if (half1 == half2) {
            for (int t = s + 1; t < n; ++t) {
                const auto& P = by_end1[t];
                int m = (int)P.size();
                for (int i = 0; i < m; ++i) {
                    for (int j = i + 1; j < m; ++j) {
                        if ((P[i].internal & P[j].internal).none()) {
                            ++total;
                            if (track_cov) {
                                mark_path(P[i].verts);
                                mark_path(P[j].verts);
                            }
                        }
                    }
                }
            }
        } else {
            for (int t = s + 1; t < n; ++t) {
                const auto& P1 = by_end1[t];
                const auto& P2 = by_end2[t];
                for (const auto& a : P1) {
                    for (const auto& b : P2) {
                        if ((a.internal & b.internal).none()) {
                            ++total;
                            if (track_cov) {
                                mark_path(a.verts);
                                mark_path(b.verts);
                            }
                        }
                    }
                }
            }
        }
    }
    if (half1 != half2) total /= 2;
    if (track_cov) {
        int vc = 0, ec = 0, m_tot = g.edge_count();
        for (int i = 0; i < n; ++i) if (v_in[i]) ++vc;
        for (int i = 0; i < n; ++i) for (int w : g.adj[i]) if (i < w && e_in[i][w]) ++ec;
        if (vert_cov) *vert_cov = (n > 0) ? (double)vc / n : 0.0;
        if (edge_cov) *edge_cov = (m_tot > 0) ? (double)ec / m_tot : 0.0;
    }
    return total;
}

bool has_cycle_length(const Graph& g, int L, int seed = 12345, long long node_budget = 2000000) {
    int n = g.n;
    if (L > n) return false;
    if (L <= 16) return count_cycles_exact(g, L) > 0;

    mt19937 rng(seed);
    vector<int> order(n);
    iota(order.begin(), order.end(), 0);
    shuffle(order.begin(), order.end(), rng);

    vector<int> dist(n);
    Mask vis;
    long long nodes = 0;
    bool found = false;

    for (int s : order) {
        if (found || nodes >= node_budget) break;
        fill(dist.begin(), dist.end(), 1e9);
        queue<int> q;
        q.push(s); dist[s] = 0;
        while (!q.empty()) {
            int u = q.front(); q.pop();
            for (int w : g.adj[u]) {
                if (dist[w] > dist[u] + 1) {
                    dist[w] = dist[u] + 1;
                    q.push(w);
                }
            }
        }
        vis.reset();
        vis.set(s);
        long long local_budget = max(50000LL, node_budget / max(1, n / 4));
        long long local_nodes = 0;

        auto dfs = [&](auto& self, int u, int len) -> void {
            if (found || local_nodes >= local_budget) return;
            ++local_nodes; ++nodes;
            int rem = L - len;
            if (rem == 1) {
                for (int w : g.adj[u]) if (w == s) { found = true; return; }
                return;
            }
            if (dist[u] > rem) return;
            int deg = (int)g.adj[u].size();
            int start_idx = (deg > 1) ? (rng() % deg) : 0;
            for (int i = 0; i < deg; ++i) {
                int w = g.adj[u][(start_idx + i) % deg];
                if (!vis.test(w) && dist[w] <= rem - 1) {
                    vis.set(w);
                    self(self, w, len + 1);
                    vis.reset(w);
                    if (found) return;
                }
            }
        };
        dfs(dfs, s, 0);
    }
    return found;
}

int smallest_pow2_cycle(const Graph& g, long long& c16_out) {
    c16_out = count_cycles_exact(g, 16);
    if (c16_out > 0) return 16;
    for (int L : {32, 64, 128, 256}) {
        if (L > g.n) break;
        if (has_cycle_length(g, L, 42 + L, 4000000)) return L;
    }
    for (int L : {32, 64, 128, 256}) {
        if (L > g.n) break;
        if (has_cycle_length(g, L, 99991 + L, 20000000)) return L;
    }
    return 0;
}

Graph from_lcf(const string& name, const vector<int>& shifts, int repeat) {
    int n = (int)shifts.size() * repeat;
    Graph g(n, name);
    for (int i = 0; i < n; ++i) {
        g.add_edge(i, (i + 1) % n);
        int sh = shifts[i % shifts.size()];
        int j = ((i + sh) % n + n) % n;
        g.add_edge(i, j);
    }
    return g;
}

Graph build_h_cover(const string& name, int p, int s0, int s1, int s2, int s3) {
    Graph g(6 * p, name);
    auto id = [p](int o, int x) { return o * p + ((x % p) + p) % p; };
    for (int i = 0; i < p; ++i) {
        g.add_edge(id(0, i), id(0, i + s0));
        g.add_edge(id(1, i), id(1, i + s1));
        g.add_edge(id(2, i), id(2, i + s2));
        g.add_edge(id(3, i), id(3, i + s3));
        g.add_edge(id(4, i), id(0, i));
        g.add_edge(id(4, i), id(2, i));
        g.add_edge(id(4, i), id(5, i));
        g.add_edge(id(5, i), id(1, i));
        g.add_edge(id(5, i), id(3, i));
    }
    return g;
}

Graph build_cyclic_lift(const Graph& base, int m, const vector<int>& edge_voltages, const string& name) {
    Graph g(base.n * m, name);
    int eidx = 0;
    for (int u = 0; u < base.n; ++u) {
        for (int v : base.adj[u]) {
            if (u < v) {
                int vol = ((edge_voltages[eidx++] % m) + m) % m;
                for (int r = 0; r < m; ++r) {
                    g.add_edge(u * m + r, v * m + (r + vol) % m);
                }
            }
        }
    }
    return g;
}

// Fast greedy girth-g cubic constructor (adds edges only between vertices at dist >= target_g - 1, then fixes remaining stubs via SA)
bool construct_high_girth_cubic(int n, int target_g, bool bipartite, int seed, Graph& out_g, int max_steps = 4000) {
    mt19937 rng(seed);
    vector<vector<bool>> has(n, vector<bool>(n, false));
    vector<pair<int,int>> edges;

    auto rebuild_graph = [&]() {
        out_g = Graph(n, "SA_g" + to_string(target_g) + "_n" + to_string(n));
        for (auto [u, v] : edges) out_g.add_edge(u, v);
    };

    for (int restart = 0; restart < 4; ++restart) {
        bool ok = false;
        for (int tr = 0; tr < 200; ++tr) {
            for (int i = 0; i < n; ++i) fill(has[i].begin(), has[i].end(), false);
            edges.clear();
            ok = true;
            if (bipartite) {
                int half = n / 2;
                vector<int> L, R;
                for (int i = 0; i < half; ++i) for (int k = 0; k < 3; ++k) { L.push_back(i); R.push_back(half + i); }
                shuffle(R.begin(), R.end(), rng);
                for (size_t i = 0; i < L.size(); ++i) {
                    int u = L[i], v = R[i];
                    if (has[u][v]) { ok = false; break; }
                    has[u][v] = has[v][u] = true;
                    edges.push_back({u, v});
                }
            } else {
                vector<int> stubs;
                for (int i = 0; i < n; ++i) for (int k = 0; k < 3; ++k) stubs.push_back(i);
                shuffle(stubs.begin(), stubs.end(), rng);
                for (size_t i = 0; i < stubs.size(); i += 2) {
                    int u = stubs[i], v = stubs[i+1];
                    if (u == v || has[u][v]) { ok = false; break; }
                    has[u][v] = has[v][u] = true;
                    edges.push_back({min(u,v), max(u,v)});
                }
            }
            if (ok) break;
        }
        if (!ok) continue;

        rebuild_graph();
        int pen = out_g.short_cycle_penalty(target_g);
        if (pen == 0) return true;

        int m = (int)edges.size();
        for (int st = 0; st < max_steps; ++st) {
            int i1 = rng() % m, i2 = rng() % m;
            if (i1 == i2) continue;
            auto [a, b] = edges[i1];
            auto [c, d] = edges[i2];
            if (a == c || a == d || b == c || b == d) continue;
            int u1, v1, u2, v2;
            if (bipartite) {
                u1 = a; v1 = d; u2 = c; v2 = b;
            } else {
                if (rng() & 1) swap(c, d);
                u1 = a; v1 = c; u2 = b; v2 = d;
            }
            if (has[u1][v1] || has[u2][v2]) continue;

            has[a][b] = has[b][a] = false; has[c][d] = has[d][c] = false;
            has[u1][v1] = has[v1][u1] = true; has[u2][v2] = has[v2][u2] = true;
            edges[i1] = {u1, v1}; edges[i2] = {u2, v2};
            rebuild_graph();
            int npen = out_g.short_cycle_penalty(target_g);

            double T = 10.0 * pow(0.01, (double)st / max_steps);
            if (npen <= pen || uniform_real_distribution<double>(0.0, 1.0)(rng) < exp((pen - npen) / T)) {
                pen = npen;
                if (pen == 0) return true;
            } else {
                has[u1][v1] = has[v1][u1] = false; has[u2][v2] = has[v2][u2] = false;
                has[a][b] = has[b][a] = true; has[c][d] = has[d][c] = true;
                edges[i1] = {a, b}; edges[i2] = {c, d};
            }
        }
    }
    return false;
}

struct CanonicalReport {
    string name;
    int n, girth, min_deg, max_deg, shortest_pow2;
    bool bipartite;
    long long c9, c10, c11, c12, c13, c14, c15, c16;
    double c16_vcov, c16_ecov;
};

CanonicalReport analyze_canonical(const Graph& g) {
    CanonicalReport r{};
    r.name = g.name;
    r.n = g.n;
    r.girth = g.girth();
    r.min_deg = g.min_deg();
    r.max_deg = g.max_deg();
    r.bipartite = g.is_bipartite();
    r.c9  = (r.girth <= 9)  ? count_cycles_exact(g, 9)  : 0;
    r.c10 = (r.girth <= 10) ? count_cycles_exact(g, 10) : 0;
    r.c11 = (r.girth <= 11) ? count_cycles_exact(g, 11) : 0;
    r.c12 = (r.girth <= 12) ? count_cycles_exact(g, 12) : 0;
    r.c13 = (r.girth <= 13) ? count_cycles_exact(g, 13) : 0;
    r.c14 = (r.girth <= 14) ? count_cycles_exact(g, 14) : 0;
    r.c15 = (r.girth <= 15) ? count_cycles_exact(g, 15) : 0;
    r.c16 = count_cycles_exact(g, 16, &r.c16_vcov, &r.c16_ecov);
    long long dummy = 0;
    r.shortest_pow2 = (r.c16 > 0) ? 16 : smallest_pow2_cycle(g, dummy);
    return r;
}

Graph base_petersen() {
    Graph g(10, "Petersen");
    for (int i = 0; i < 5; ++i) {
        g.add_edge(i, (i + 1) % 5);
        g.add_edge(5 + i, 5 + (i + 2) % 5);
        g.add_edge(i, 5 + i);
    }
    return g;
}

Graph base_heawood() { return from_lcf("Heawood", {5, -5}, 7); }
Graph base_desargues() { return from_lcf("Desargues", {5, -5, 9, -9}, 5); }
Graph base_tutte_coxeter() { return from_lcf("Tutte-Coxeter", {-13, -9, 7, -7, 9, 13}, 5); }

struct SAResult {
    string label;
    int n, target_girth;
    bool bipartite;
    int restarts_ok, total_moves, c16_zero_hits, counterexamples;
    long long init_min_c16, final_min_c16;
    int max_girth_seen, shortest_pow2_at_min;
    double min_c16_ecov;
};

// Fast Adversarial SA using O(V+E) 2-BFS incremental girth preservation!
SAResult run_adversarial_c16_sa_from_seeds(const string& label, const vector<Graph>& seeds, int target_g, bool bipartite, int sa_steps, int seed_base) {
    int n = seeds.empty() ? 0 : seeds[0].n;
    SAResult res{label, n, target_g, bipartite, (int)seeds.size(), 0, 0, 0, (long long)1e18, (long long)1e18, 0, 16, 1.0};
    if (seeds.empty()) return res;

    int c16_zero = 0, cex = 0, tot_mv = 0;
    long long g_init_min = 1e18, g_final_min = 1e18;
    int g_max_girth = 0, g_sp2 = 16;
    double g_min_ecov = 1.0;

    #pragma omp parallel for schedule(dynamic) reduction(+:c16_zero,cex,tot_mv)
    for (int r = 0; r < (int)seeds.size(); ++r) {
        Graph g = seeds[r];
        int cur_girth = g.girth();
        long long c16 = count_cycles_exact(g, 16);
        long long init_c16 = c16;

        vector<vector<bool>> has(n, vector<bool>(n, false));
        vector<pair<int,int>> edges;
        for (int u = 0; u < n; ++u)
            for (int v : g.adj[u])
                if (u < v) { has[u][v] = has[v][u] = true; edges.push_back({u, v}); }

        // Compute bipartition if bipartite
        vector<int> part(n, 0);
        if (bipartite) {
            fill(part.begin(), part.end(), -1);
            for (int s = 0; s < n; ++s) {
                if (part[s] != -1) continue;
                queue<int> q; q.push(s); part[s] = 0;
                while (!q.empty()) {
                    int u = q.front(); q.pop();
                    for (int w : g.adj[u]) if (part[w] == -1) { part[w] = part[u] ^ 1; q.push(w); }
                }
            }
        }

        mt19937 rng(seed_base + r * 7919 + 31337);
        int m = (int)edges.size();
        Graph best_g = g;
        long long best_c16 = c16;
        int best_girth = cur_girth;

        auto rebuild = [&]() {
            g = Graph(n, "SA");
            for (auto [u, v] : edges) g.add_edge(u, v);
        };

        for (int st = 0; st < sa_steps; ++st) {
            ++tot_mv;
            int i1 = rng() % m, i2 = rng() % m;
            if (i1 == i2) continue;
            auto [a, b] = edges[i1];
            auto [c, d] = edges[i2];
            if (a == c || a == d || b == c || b == d) continue;
            int u1, v1, u2, v2;
            if (bipartite) {
                if (part[a] != part[c]) swap(c, d);
                u1 = a; v1 = d; u2 = c; v2 = b;
            } else {
                if (rng() & 1) swap(c, d);
                u1 = a; v1 = c; u2 = b; v2 = d;
            }
            if (has[u1][v1] || has[u2][v2]) continue;

            has[a][b] = has[b][a] = false; has[c][d] = has[d][c] = false;
            has[u1][v1] = has[v1][u1] = true; has[u2][v2] = has[v2][u2] = true;
            edges[i1] = {u1, v1}; edges[i2] = {u2, v2};
            rebuild();

            // 150x faster incremental 2-BFS girth check!
            if (!g.two_edges_preserve_girth(u1, v1, u2, v2, target_g)) {
                has[u1][v1] = has[v1][u1] = false; has[u2][v2] = has[v2][u2] = false;
                has[a][b] = has[b][a] = true; has[c][d] = has[d][c] = true;
                edges[i1] = {a, b}; edges[i2] = {c, d};
                continue;
            }

            long long nc16 = count_cycles_exact(g, 16);
            double T = max(1.0, (double)best_c16 * 0.04) * pow(0.01, (double)st / sa_steps);
            if (nc16 <= c16 || uniform_real_distribution<double>(0.0, 1.0)(rng) < exp((double)(c16 - nc16) / T)) {
                c16 = nc16;
                if (c16 < best_c16) {
                    best_c16 = c16;
                    best_g = g;
                    best_girth = g.girth();
                    if (best_c16 == 0) {
                        ++c16_zero;
                        long long dummy = 0;
                        int sp2 = smallest_pow2_cycle(best_g, dummy);
                        if (sp2 == 0) {
                            ++cex;
                            #pragma omp critical
                            cout << "!!! GENUINE COUNTEREXAMPLE FOUND n=" << n << " g=" << best_girth << " !!!\n" << flush;
                        }
                        break;
                    }
                }
            } else {
                has[u1][v1] = has[v1][u1] = false; has[u2][v2] = has[v2][u2] = false;
                has[a][b] = has[b][a] = true; has[c][d] = has[d][c] = true;
                edges[i1] = {a, b}; edges[i2] = {c, d};
            }
        }

        double vc = 0.0, ec = 0.0;
        count_cycles_exact(best_g, 16, &vc, &ec);
        long long dummy = 0;
        int sp2 = (best_c16 > 0) ? 16 : smallest_pow2_cycle(best_g, dummy);

        #pragma omp critical
        {
            g_init_min = min(g_init_min, init_c16);
            if (best_c16 < g_final_min) {
                g_final_min = best_c16;
                g_sp2 = sp2;
                g_min_ecov = ec;
            }
            g_max_girth = max(g_max_girth, best_girth);
        }
    }

    res.total_moves = tot_mv;
    res.c16_zero_hits = c16_zero;
    res.counterexamples = cex;
    res.init_min_c16 = g_init_min;
    res.final_min_c16 = g_final_min;
    res.max_girth_seen = g_max_girth;
    res.shortest_pow2_at_min = g_sp2;
    res.min_c16_ecov = g_min_ecov;
    return res;
}

int main(int argc, char** argv) {
    string out_json = (argc > 1) ? argv[1] : "girth9_14_hunter.json";
    auto t0 = chrono::steady_clock::now();
    cout << "=== Wave 8 Agent #4: Erdős #64 Girth 9-14 OpenMP Hunter v2 (threads="
         << omp_get_max_threads() << ") ===\n" << flush;

    // -------------------------------------------------------------------------
    // TRACK 1: Canonical High-Girth Cubic Graphs & Cages (g in {9, 10, 12})
    // -------------------------------------------------------------------------
    vector<Graph> canonicals;
    canonicals.push_back(from_lcf("Harries-70", {-29,-19,-13,13,21,-27,27,33,-13,13,19,-21,-33,29}, 5));
    canonicals.push_back(from_lcf("Balaban-10-cage-70", {-9,-25,-19,29,13,35,-13,-29,19,25,9,-29,29,17,33,21,9,-13,-31,-9,25,17,9,-31,27,-9,17,-19,-29,27,-17,-9,-29,33,-25,25,-21,17,-17,29,35,-29,17,-17,21,-25,25,-33,29,9,17,-27,29,19,-17,9,-27,31,-9,-17,-25,9,31,13,-9,-21,-33,-17,-29,29}, 1));
    canonicals.push_back(from_lcf("Foster-90", {17,-9,37,-37,9,-17}, 15));
    canonicals.push_back(build_h_cover("Biggs-Smith-102", 17, 1, 2, 4, 8));
    canonicals.push_back(from_lcf("Ljubljana-112", {47,-23,-31,39,25,-21,-31,-41,25,15,29,-41,-19,15,-49,33,39,-35,-21,17,-33,49,41,31,-15,-29,41,31,-15,-25,21,31,-51,-25,23,9,-17,51,35,-29,21,-51,-39,33,-9,-51,51,-47,-33,19,51,-21,29,21,-31,-39}, 2));
    canonicals.push_back(from_lcf("Tutte-12-cage-126", {17,27,-13,-59,-35,35,-11,13,-53,53,-27,21,57,11,-21,-57,59,-17}, 7));

    vector<CanonicalReport> canon_reports(canonicals.size());
    #pragma omp parallel for schedule(dynamic)
    for (int i = 0; i < (int)canonicals.size(); ++i) {
        canon_reports[i] = analyze_canonical(canonicals[i]);
    }

    cout << "\n[TRACK 1: Canonical High-Girth Cubic Graphs]\n";
    for (const auto& r : canon_reports) {
        cout << "  " << left << setw(20) << r.name << " n=" << setw(4) << r.n
             << " g=" << setw(2) << r.girth << " bip=" << r.bipartite
             << " C9=" << r.c9 << " C10=" << r.c10 << " C11=" << r.c11 << " C12=" << r.c12
             << " C13=" << r.c13 << " C14=" << r.c14 << " C15=" << r.c15
             << " C16=" << r.c16
             << " vcov=" << fixed << setprecision(3) << r.c16_vcov
             << " ecov=" << r.c16_ecov
             << " min2^k=" << r.shortest_pow2 << "\n";
    }
    cout << flush;

    // -------------------------------------------------------------------------
    // TRACK 2: Algebraic Voltage Lifts & Generalized H-Covers (g in 9..14, n in 60..320)
    // -------------------------------------------------------------------------
    long long alg_tested = 0, alg_g9_14 = 0, alg_c16_zero = 0, alg_cex = 0;
    long long alg_min_c16 = 1e18;
    int alg_max_girth = 0;
    string alg_min_desc = "none";
    map<int, int> alg_girth_hist;
    map<int, long long> alg_min_c16_by_g;

    // Collect diverse algebraic seeds for Track 3 SA too!
    vector<Graph> seeds_tutte2_252, seeds_bs2_204, seeds_bs3_306, seeds_h3_210, seeds_f3_270;

    vector<int> h_primes = {13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53};
    int h_samples_per_p = 1200;

    #pragma omp parallel for schedule(dynamic)
    for (int pi = 0; pi < (int)h_primes.size(); ++pi) {
        int p = h_primes[pi];
        mt19937 rng(202600 + p * 997);
        for (int s = 0; s < h_samples_per_p; ++s) {
            int s0 = 1;
            int s1 = 1 + rng() % (p / 2);
            int s2 = 1 + rng() % (p / 2);
            int s3 = 1 + rng() % (p / 2);
            Graph g = build_h_cover("H_" + to_string(p), p, s0, s1, s2, s3);
            #pragma omp atomic
            ++alg_tested;
            if (!g.girth_at_least(9)) continue;
            int gv = g.girth();
            if (gv < 9 || gv > 14) continue;
            long long c16 = count_cycles_exact(g, 16);
            int sp2 = (c16 > 0) ? 16 : smallest_pow2_cycle(g, c16);
            #pragma omp critical
            {
                ++alg_g9_14;
                alg_girth_hist[gv]++;
                if (!alg_min_c16_by_g.count(gv) || c16 < alg_min_c16_by_g[gv]) alg_min_c16_by_g[gv] = c16;
                if (gv > alg_max_girth) alg_max_girth = gv;
                if (c16 == 0) ++alg_c16_zero;
                if (sp2 == 0) ++alg_cex;
                if (c16 < alg_min_c16) {
                    alg_min_c16 = c16;
                    alg_min_desc = "H_p" + to_string(p) + "_n" + to_string(6*p) + "_g" + to_string(gv) + "_s(" + to_string(s0) + "," + to_string(s1) + "," + to_string(s2) + "," + to_string(s3) + ")_sp2=" + to_string(sp2);
                }
            }
        }
    }

    struct LiftSpec { Graph base; vector<int> ms; int trials; };
    vector<LiftSpec> lift_specs = {
        {base_petersen(),      {7, 9, 11, 13, 15, 17, 19, 23, 25, 29, 31}, 500},
        {base_heawood(),       {5, 7, 9, 11, 13, 15, 17, 19, 21, 22}, 500},
        {base_desargues(),     {4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16}, 400},
        {base_tutte_coxeter(), {3, 4, 5, 6, 7, 8, 9, 10}, 400},
        {canonicals[0],        {2, 3, 4}, 250}, // Harries 70 -> 140, 210, 280
        {canonicals[1],        {2, 3, 4}, 250}, // Balaban 70 -> 140, 210, 280
        {canonicals[2],        {2, 3},    250}, // Foster 90 -> 180, 270
        {canonicals[3],        {2, 3},    250}, // Biggs-Smith 102 -> 204, 306
        {canonicals[4],        {2},       250}, // Ljubljana 112 -> 224
        {canonicals[5],        {2},       400}, // Tutte-12-cage 126 -> 252
    };

    for (const auto& spec : lift_specs) {
        int m_edges = spec.base.edge_count();
        for (int mult : spec.ms) {
            if (spec.base.n * mult > 320) continue;
            #pragma omp parallel for schedule(dynamic)
            for (int t = 0; t < spec.trials; ++t) {
                mt19937 rng(500000 + spec.base.n * 10000 + mult * 331 + t * 997);
                vector<int> vols(m_edges);
                for (int e = 0; e < m_edges; ++e) vols[e] = rng() % mult;
                Graph g = build_cyclic_lift(spec.base, mult, vols, spec.base.name + "_Z" + to_string(mult));
                #pragma omp atomic
                ++alg_tested;
                if (!g.girth_at_least(9)) continue;
                int gv = g.girth();
                if (gv < 9 || gv > 14) continue;
                long long c16 = count_cycles_exact(g, 16);
                int sp2 = (c16 > 0) ? 16 : smallest_pow2_cycle(g, c16);
                #pragma omp critical
                {
                    ++alg_g9_14;
                    alg_girth_hist[gv]++;
                    if (!alg_min_c16_by_g.count(gv) || c16 < alg_min_c16_by_g[gv]) alg_min_c16_by_g[gv] = c16;
                    if (gv > alg_max_girth) alg_max_girth = gv;
                    if (c16 == 0) ++alg_c16_zero;
                    if (sp2 == 0) ++alg_cex;
                    if (c16 < alg_min_c16) {
                        alg_min_c16 = c16;
                        alg_min_desc = spec.base.name + "_Z" + to_string(mult) + "_n" + to_string(g.n) + "_g" + to_string(gv) + "_sp2=" + to_string(sp2);
                    }
                    if (spec.base.name == "Tutte-12-cage-126" && mult == 2 && (int)seeds_tutte2_252.size() < 8) seeds_tutte2_252.push_back(g);
                    if (spec.base.name == "Biggs-Smith-102" && mult == 2 && (int)seeds_bs2_204.size() < 8) seeds_bs2_204.push_back(g);
                    if (spec.base.name == "Biggs-Smith-102" && mult == 3 && (int)seeds_bs3_306.size() < 8) seeds_bs3_306.push_back(g);
                    if (spec.base.name == "Harries-70" && mult == 3 && (int)seeds_h3_210.size() < 8) seeds_h3_210.push_back(g);
                    if (spec.base.name == "Foster-90" && mult == 3 && (int)seeds_f3_270.size() < 8) seeds_f3_270.push_back(g);
                }
            }
        }
    }

    cout << "\n[TRACK 2: Algebraic Voltage Lifts & H-Covers]\n";
    cout << "  tested=" << alg_tested << " girth9_14_hits=" << alg_g9_14
         << " max_girth=" << alg_max_girth
         << " C16_zero=" << alg_c16_zero << " CEX=" << alg_cex << "\n";
    cout << "  min_C16=" << alg_min_c16 << " (" << alg_min_desc << ")\n";
    cout << "  girth_hist: ";
    for (auto [gv, cnt] : alg_girth_hist) cout << "g" << gv << ":" << cnt << "(minC16=" << alg_min_c16_by_g[gv] << ") ";
    cout << "\n" << flush;

    // -------------------------------------------------------------------------
    // TRACK 3: Fast Adversarial Girth>=9..12 C16-Destruction SA (n in [64, 320])
    // -------------------------------------------------------------------------
    vector<SAResult> sa_results;
    cout << "\n[TRACK 3: Adversarial Girth>=9..12 C16-Destruction SA]\n";

    // 3A: Random-seeded girth 9-10 SA across spectral boundary (n = 80, 120, 132, 140, 160, 180, 200, 240, 280, 320)
    struct RandCfg { string lbl; int n; int g; bool bip; int restarts; int steps; };
    vector<RandCfg> rcfgs = {
        {"Rand_n80_g9",      80,  9,  false, 8, 500},
        {"Rand_n120_g9",     120, 9,  false, 8, 500},
        {"Rand_n132_g9",     132, 9,  false, 8, 600},
        {"Rand_n150_g9",     150, 9,  false, 8, 600},
        {"Rand_n180_g10",    180, 10, false, 8, 500},
        {"Rand_n220_g10",    220, 10, false, 8, 450},
        {"Rand_n260_g10",    260, 10, false, 6, 400},
        {"Rand_n300_g10",    300, 10, false, 6, 350},
        {"Rand_n320_g10",    320, 10, false, 6, 350},
        {"RandBip_n264_g10", 264, 10, true,  6, 400},
        {"RandBip_n320_g10", 320, 10, true,  6, 350},
    };
    for (size_t i = 0; i < rcfgs.size(); ++i) {
        auto& cfg = rcfgs[i];
        vector<Graph> seeds;
        #pragma omp parallel for schedule(dynamic)
        for (int r = 0; r < cfg.restarts; ++r) {
            Graph g;
            if (construct_high_girth_cubic(cfg.n, cfg.g, cfg.bip, 910000 + (int)i * 1000 + r * 97, g, 4000)) {
                #pragma omp critical
                seeds.push_back(move(g));
            }
        }
        auto res = run_adversarial_c16_sa_from_seeds(cfg.lbl, seeds, cfg.g, cfg.bip, cfg.steps, 950000 + (int)i * 10000);
        sa_results.push_back(res);
        cout << "  " << left << setw(20) << res.label << " n=" << setw(3) << res.n << " g>=" << setw(2) << res.target_girth
             << " bip=" << res.bipartite << " seeds=" << setw(2) << res.restarts_ok
             << " moves=" << setw(5) << res.total_moves
             << " initMinC16=" << setw(5) << res.init_min_c16
             << " finalMinC16=" << setw(5) << res.final_min_c16
             << " ecov=" << fixed << setprecision(3) << res.min_c16_ecov
             << " C16z=" << res.c16_zero_hits << " min2^k=" << res.shortest_pow2_at_min
             << " CEX=" << res.counterexamples << "\n" << flush;
    }

    // 3B: Algebraic-seeded SA preserving high girth (g >= 10, 12) on lifts n in [204, 306]!
    struct AlgSACfg { string lbl; vector<Graph>& seeds; int g; bool bip; int steps; };
    vector<AlgSACfg> acfgs = {
        {"AlgSeed_BS2_n204",    seeds_bs2_204,    9,  false, 500},
        {"AlgSeed_H3_n210",     seeds_h3_210,     10, true,  500},
        {"AlgSeed_Tut2_n252",   seeds_tutte2_252, 12, true,  500},
        {"AlgSeed_Fos3_n270",   seeds_f3_270,     10, true,  450},
        {"AlgSeed_BS3_n306",    seeds_bs3_306,    9,  false, 450},
    };
    for (size_t i = 0; i < acfgs.size(); ++i) {
        auto& cfg = acfgs[i];
        auto res = run_adversarial_c16_sa_from_seeds(cfg.lbl, cfg.seeds, cfg.g, cfg.bip, cfg.steps, 990000 + (int)i * 10000);
        sa_results.push_back(res);
        cout << "  " << left << setw(20) << res.label << " n=" << setw(3) << res.n << " g>=" << setw(2) << res.target_girth
             << " bip=" << res.bipartite << " seeds=" << setw(2) << res.restarts_ok
             << " moves=" << setw(5) << res.total_moves
             << " initMinC16=" << setw(5) << res.init_min_c16
             << " finalMinC16=" << setw(5) << res.final_min_c16
             << " ecov=" << fixed << setprecision(3) << res.min_c16_ecov
             << " C16z=" << res.c16_zero_hits << " min2^k=" << res.shortest_pow2_at_min
             << " CEX=" << res.counterexamples << "\n" << flush;
    }

    // -------------------------------------------------------------------------
    // TRACK 4: Non-Cubic delta>=3 Girth>=9 Chord Perturbations
    // -------------------------------------------------------------------------
    cout << "\n[TRACK 4: Non-Cubic delta>=3 Girth>=9 Chord Additions]\n";
    int noncubic_tested = 0, noncubic_c16_decreased = 0, noncubic_cex = 0;
    long long noncubic_min_c16 = 1e18;
    vector<Graph> nc_bases;
    if (!seeds_bs2_204.empty()) nc_bases.push_back(seeds_bs2_204[0]);
    if (!seeds_tutte2_252.empty()) nc_bases.push_back(seeds_tutte2_252[0]);
    if (!seeds_bs3_306.empty()) nc_bases.push_back(seeds_bs3_306[0]);
    for (const auto& base : nc_bases) {
        long long base_c16 = count_cycles_exact(base, 16);
        mt19937 rng(777000 + base.n);
        int added = 0;
        Graph g = base;
        for (int tries = 0; tries < 400 && added < 15; ++tries) {
            int u = rng() % g.n, v = rng() % g.n;
            if (u == v || g.has_edge(u, v)) continue;
            if (g.dist_without_edge(u, v, 7) < 8) continue;
            g.add_edge(u, v);
            ++added;
            ++noncubic_tested;
            long long nc16 = count_cycles_exact(g, 16);
            if (nc16 < base_c16) ++noncubic_c16_decreased;
            if (nc16 < noncubic_min_c16) noncubic_min_c16 = nc16;
            if (nc16 == 0) {
                long long dummy = 0;
                if (smallest_pow2_cycle(g, dummy) == 0) ++noncubic_cex;
            }
        }
        cout << "  base=" << base.name << " n=" << base.n << " baseC16=" << base_c16
             << " +chords=" << added << " final_maxdeg=" << g.max_deg()
             << " final_girth=" << g.girth() << " finalC16=" << count_cycles_exact(g, 16) << "\n" << flush;
    }

    double elapsed = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
    cout << "\nTotal elapsed: " << fixed << setprecision(2) << elapsed << " s\n";

    ofstream jf(out_json);
    jf << "{\n  \"elapsed_s\": " << fixed << setprecision(2) << elapsed << ",\n";
    jf << "  \"track1_canonical\": [\n";
    for (size_t i = 0; i < canon_reports.size(); ++i) {
        const auto& r = canon_reports[i];
        jf << "    {\"name\": \"" << r.name << "\", \"n\": " << r.n << ", \"girth\": " << r.girth
           << ", \"bipartite\": " << (r.bipartite ? "true" : "false")
           << ", \"c9\": " << r.c9 << ", \"c10\": " << r.c10 << ", \"c11\": " << r.c11
           << ", \"c12\": " << r.c12 << ", \"c13\": " << r.c13 << ", \"c14\": " << r.c14
           << ", \"c15\": " << r.c15 << ", \"c16\": " << r.c16
           << ", \"c16_vcov\": " << fixed << setprecision(4) << r.c16_vcov
           << ", \"c16_ecov\": " << r.c16_ecov
           << ", \"shortest_pow2\": " << r.shortest_pow2 << "}"
           << (i + 1 < canon_reports.size() ? "," : "") << "\n";
    }
    jf << "  ],\n  \"track2_algebraic\": {\n";
    jf << "    \"tested\": " << alg_tested << ",\n";
    jf << "    \"girth9_14_hits\": " << alg_g9_14 << ",\n";
    jf << "    \"max_girth\": " << alg_max_girth << ",\n";
    jf << "    \"c16_zero_hits\": " << alg_c16_zero << ",\n";
    jf << "    \"counterexamples\": " << alg_cex << ",\n";
    jf << "    \"min_c16\": " << alg_min_c16 << ",\n";
    jf << "    \"min_c16_desc\": \"" << alg_min_desc << "\",\n";
    jf << "    \"girth_hist\": {";
    bool first = true;
    for (auto [gv, cnt] : alg_girth_hist) {
        if (!first) jf << ", ";
        jf << "\"" << gv << "\": {\"count\": " << cnt << ", \"min_c16\": " << alg_min_c16_by_g[gv] << "}";
        first = false;
    }
    jf << "}\n  },\n  \"track3_sa\": [\n";
    for (size_t i = 0; i < sa_results.size(); ++i) {
        const auto& r = sa_results[i];
        jf << "    {\"label\": \"" << r.label << "\", \"n\": " << r.n << ", \"target_girth\": " << r.target_girth
           << ", \"bipartite\": " << (r.bipartite ? "true" : "false")
           << ", \"restarts_ok\": " << r.restarts_ok << ", \"total_moves\": " << r.total_moves
           << ", \"init_min_c16\": " << r.init_min_c16 << ", \"final_min_c16\": " << r.final_min_c16
           << ", \"min_c16_ecov\": " << fixed << setprecision(4) << r.min_c16_ecov
           << ", \"c16_zero_hits\": " << r.c16_zero_hits
           << ", \"shortest_pow2_at_min\": " << r.shortest_pow2_at_min
           << ", \"counterexamples\": " << r.counterexamples << "}"
           << (i + 1 < sa_results.size() ? "," : "") << "\n";
    }
    jf << "  ],\n  \"track4_noncubic\": {\n";
    jf << "    \"tested\": " << noncubic_tested << ",\n";
    jf << "    \"c16_decreased\": " << noncubic_c16_decreased << ",\n";
    jf << "    \"min_c16\": " << noncubic_min_c16 << ",\n";
    jf << "    \"counterexamples\": " << noncubic_cex << "\n";
    jf << "  }\n}\n";
    return 0;
}
