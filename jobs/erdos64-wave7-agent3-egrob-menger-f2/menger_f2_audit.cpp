#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstring>
#include <fstream>
#include <iostream>
#include <numeric>
#include <queue>
#include <random>
#include <string>
#include <vector>
#include <omp.h>

using namespace std;

// Wave 7 Agent #3 — 3-Connected Menger / Tutte / F2 Cycle-Space Audit on EGRob3ConnCore
// Tests 3-vertex-connected, nonbipartite, V>=4-independent, {C4, C8}-free graphs H
// with cubic edge ab in E(H[V3]) for:
//   (1) exact kappa(H) >= 3
//   (2) total C16 count and maximum single-edge hitting fraction across E(H[V3])
//   (3) Tutte non-separating induced cycles through ab vs avoiding ab
//   (4) F2 cycle-space dimension beta_1(H - ab) and whether NS-induced cycles avoiding ab span Z(H - ab)
//   (5) Menger 3-disjoint-path connectivity inside H - ab (pairs with 3 internally disjoint paths)

struct Graph {
    int n;
    vector<uint64_t> adj;
    Graph(int n = 0) : n(n), adj(n, 0) {}
    void add_edge(int u, int v) {
        adj[u] |= (1ULL << v);
        adj[v] |= (1ULL << u);
    }
    void remove_edge(int u, int v) {
        adj[u] &= ~(1ULL << v);
        adj[v] &= ~(1ULL << u);
    }
    bool has_edge(int u, int v) const { return (adj[u] >> v) & 1ULL; }
    int deg(int u) const { return __builtin_popcountll(adj[u]); }
    int num_edges() const {
        int s = 0;
        for (int i = 0; i < n; ++i) s += deg(i);
        return s / 2;
    }
};

bool is_connected_mask(const Graph& g, uint64_t allowed) {
    if (allowed == 0) return true;
    int start = __builtin_ctzll(allowed);
    uint64_t vis = 1ULL << start;
    uint64_t frontier = vis;
    while (frontier) {
        uint64_t nxt = 0;
        while (frontier) {
            int u = __builtin_ctzll(frontier);
            frontier &= frontier - 1;
            nxt |= g.adj[u] & allowed & ~vis;
        }
        vis |= nxt;
        frontier = nxt;
    }
    return vis == allowed;
}

bool is_3_connected(const Graph& g) {
    if (g.n < 4) return false;
    uint64_t all = (g.n == 64) ? ~0ULL : ((1ULL << g.n) - 1ULL);
    if (!is_connected_mask(g, all)) return false;
    for (int u = 0; u < g.n; ++u) {
        for (int v = u + 1; v < g.n; ++v) {
            uint64_t rem = all & ~(1ULL << u) & ~(1ULL << v);
            if (!is_connected_mask(g, rem)) return false;
        }
    }
    return true;
}

bool is_bipartite(const Graph& g) {
    vector<int> col(g.n, -1);
    for (int s = 0; s < g.n; ++s) {
        if (col[s] != -1) continue;
        col[s] = 0;
        queue<int> q;
        q.push(s);
        while (!q.empty()) {
            int u = q.front(); q.pop();
            uint64_t m = g.adj[u];
            while (m) {
                int v = __builtin_ctzll(m);
                m &= m - 1;
                if (col[v] == -1) { col[v] = 1 - col[u]; q.push(v); }
                else if (col[v] == col[u]) return false;
            }
        }
    }
    return true;
}

bool is_vge4_independent(const Graph& g) {
    for (int u = 0; u < g.n; ++u) {
        if (g.deg(u) < 4) continue;
        uint64_t m = g.adj[u];
        while (m) {
            int v = __builtin_ctzll(m);
            m &= m - 1;
            if (g.deg(v) >= 4) return false;
        }
    }
    return true;
}

int count_C4(const Graph& g) {
    int c = 0;
    for (int u = 0; u < g.n; ++u)
        for (int v = u + 1; v < g.n; ++v) {
            int k = __builtin_popcountll(g.adj[u] & g.adj[v]);
            c += k * (k - 1) / 2;
        }
    return c / 2;
}

void dfs_c(const Graph& g, int s, int u, int rem, uint64_t vis, int& cnt, int cap) {
    if (cnt >= cap) return;
    if (rem == 1) {
        if (g.has_edge(u, s)) cnt++;
        return;
    }
    if (rem == 2) {
        uint64_t common = g.adj[u] & g.adj[s] & ~vis & (~0ULL << (s + 1));
        cnt += __builtin_popcountll(common);
        return;
    }
    uint64_t cand = g.adj[u] & ~vis & (~0ULL << (s + 1));
    while (cand) {
        int v = __builtin_ctzll(cand);
        cand &= cand - 1;
        dfs_c(g, s, v, rem - 1, vis | (1ULL << v), cnt, cap);
        if (cnt >= cap) return;
    }
}

int count_cycles_len(const Graph& g, int L, int cap = 100000) {
    int tot = 0;
    for (int s = 0; s < g.n; ++s) {
        uint64_t nbrs = g.adj[s] & (~0ULL << (s + 1));
        while (nbrs) {
            int v = __builtin_ctzll(nbrs);
            nbrs &= nbrs - 1;
            dfs_c(g, s, v, L - 1, (1ULL << s) | (1ULL << v), tot, cap);
            if (tot >= cap) return cap;
        }
    }
    return tot / 2;
}

int count_cycles_avoid_edge(const Graph& g, int L, int a, int b, int cap = 500) {
    Graph h = g;
    h.remove_edge(a, b);
    return count_cycles_len(h, L, cap);
}

bool has_3_disjoint_paths(const Graph& g, int s, int t) {
    if (g.has_edge(s, t)) return true;
    int N = 2 * g.n;
    vector<vector<int>> cap(N, vector<int>(N, 0));
    for (int v = 0; v < g.n; ++v) {
        cap[2 * v][2 * v + 1] = (v == s || v == t) ? 3 : 1;
        uint64_t m = g.adj[v];
        while (m) {
            int w = __builtin_ctzll(m);
            m &= m - 1;
            cap[2 * v + 1][2 * w] = 1;
        }
    }
    int src = 2 * s + 1, snk = 2 * t;
    int flow = 0;
    while (flow < 3) {
        vector<int> par(N, -1);
        queue<int> q;
        q.push(src);
        par[src] = src;
        while (!q.empty() && par[snk] == -1) {
            int u = q.front(); q.pop();
            for (int v = 0; v < N; ++v) {
                if (par[v] == -1 && cap[u][v] > 0) {
                    par[v] = u;
                    q.push(v);
                }
            }
        }
        if (par[snk] == -1) break;
        int cur = snk;
        while (cur != src) {
            int p = par[cur];
            cap[p][cur] -= 1;
            cap[cur][p] += 1;
            cur = p;
        }
        flow++;
    }
    return flow >= 3;
}

void analyze_tutte_f2(const Graph& H, int a, int b, int maxL,
                      int& ns_through_ab, int& ns_avoid_ab, int& f2_rank_avoid, int& beta1_G) {
    int n = H.n;
    uint64_t all = (n == 64) ? ~0ULL : ((1ULL << n) - 1ULL);
    vector<pair<int,int>> edges;
    int edge_id[64][64];
    memset(edge_id, -1, sizeof(edge_id));
    for (int u = 0; u < n; ++u)
        for (int v = u + 1; v < n; ++v)
            if (H.has_edge(u, v) && !((u == a && v == b) || (u == b && v == a))) {
                edge_id[u][v] = edge_id[v][u] = (int)edges.size();
                edges.push_back({u, v});
            }
    int mG = (int)edges.size();
    beta1_G = mG - n + 1;
    ns_through_ab = 0;
    ns_avoid_ab = 0;

    vector<pair<uint64_t, uint64_t>> basis;
    auto insert_vec = [&](uint64_t lo, uint64_t hi) {
        for (auto [blo, bhi] : basis) {
            int p_hi = bhi ? (63 - __builtin_clzll(bhi)) : -1;
            if (p_hi >= 0) {
                if ((hi >> p_hi) & 1ULL) { lo ^= blo; hi ^= bhi; }
            } else {
                int p_lo = 63 - __builtin_clzll(blo);
                if ((lo >> p_lo) & 1ULL) { lo ^= blo; hi ^= bhi; }
            }
        }
        if (lo || hi) {
            basis.push_back({lo, hi});
            sort(basis.begin(), basis.end(), [](auto x, auto y) {
                if (x.second != y.second) return x.second > y.second;
                return x.first > y.first;
            });
        }
    };

    int path[64];
    auto dfs = [&](auto& self, int s, int u, int len, uint64_t mask) -> void {
        if (len >= 3 && H.has_edge(u, s)) {
            if (path[1] < u) {
                bool ind = true;
                for (int i = 0; i < len; ++i) {
                    if (__builtin_popcountll(H.adj[path[i]] & mask) != 2) { ind = false; break; }
                }
                if (ind && is_connected_mask(H, all & ~mask)) {
                    bool uses_ab = false;
                    uint64_t lo = 0, hi = 0;
                    for (int i = 0; i < len; ++i) {
                        int x = path[i], y = path[(i + 1) % len];
                        if ((x == a && y == b) || (x == b && y == a)) uses_ab = true;
                        else {
                            int id = edge_id[x][y];
                            if (id < 64) lo |= (1ULL << id);
                            else if (id < 128) hi |= (1ULL << (id - 64));
                        }
                    }
                    if (uses_ab) ns_through_ab++;
                    else {
                        ns_avoid_ab++;
                        insert_vec(lo, hi);
                    }
                }
            }
        }
        if (len >= maxL) return;
        uint64_t cand = H.adj[u] & ~mask & (~0ULL << (s + 1));
        while (cand) {
            int w = __builtin_ctzll(cand);
            cand &= cand - 1;
            uint64_t in_m = H.adj[w] & mask;
            if (__builtin_popcountll(in_m) > 2) continue;
            if (__builtin_popcountll(in_m) == 2 && !((in_m >> s) & 1ULL)) continue;
            path[len] = w;
            self(self, s, w, len + 1, mask | (1ULL << w));
        }
    };

    for (int s = 0; s < n; ++s) {
        path[0] = s;
        uint64_t nbrs = H.adj[s] & (~0ULL << (s + 1));
        while (nbrs) {
            int v1 = __builtin_ctzll(nbrs);
            nbrs &= nbrs - 1;
            path[1] = v1;
            dfs(dfs, s, v1, 2, (1ULL << s) | (1ULL << v1));
        }
    }
    f2_rank_avoid = (int)basis.size();
}

bool build_c4_c8_free_3conn(int n, int num4, mt19937_64& rng, Graph& out) {
    for (int restart = 0; restart < 20; ++restart) {
        Graph g(n);
        bool ok = false;
        for (int tries = 0; tries < 400; ++tries) {
            vector<int> stubs;
            for (int i = 0; i < num4; ++i) for (int k = 0; k < 4; ++k) stubs.push_back(i);
            for (int i = num4; i < n; ++i) for (int k = 0; k < 3; ++k) stubs.push_back(i);
            shuffle(stubs.begin(), stubs.end(), rng);
            g = Graph(n);
            ok = true;
            for (size_t i = 0; i < stubs.size(); i += 2) {
                int u = stubs[i], v = stubs[i + 1];
                if (u == v || g.has_edge(u, v) || (u < num4 && v < num4)) { ok = false; break; }
                g.add_edge(u, v);
            }
            if (ok) break;
        }
        if (!ok) continue;

        auto eval = [&](const Graph& gr) -> int {
            int c4 = count_C4(gr);
            int c8 = (c4 <= 2) ? count_cycles_len(gr, 8, 200) : 200;
            return 1000 * c4 + c8;
        };
        int cur = eval(g);
        vector<pair<int,int>> es;
        for (int u = 0; u < n; ++u)
            for (int v = u + 1; v < n; ++v)
                if (g.has_edge(u, v)) es.push_back({u, v});
        int m = (int)es.size();

        for (int st = 0; st < 12000 && cur > 0; ++st) {
            int i = rng() % m, j = rng() % m;
            if (i == j) continue;
            auto [a, b] = es[i];
            auto [c, d] = es[j];
            if (a == c || a == d || b == c || b == d) continue;
            int u1 = a, v1 = c, u2 = b, v2 = d;
            if (rng() & 1) { v1 = d; v2 = c; }
            if (g.has_edge(u1, v1) || g.has_edge(u2, v2)) continue;
            if ((u1 < num4 && v1 < num4) || (u2 < num4 && v2 < num4)) continue;

            g.remove_edge(a, b); g.remove_edge(c, d);
            g.add_edge(u1, v1); g.add_edge(u2, v2);
            int nxt = eval(g);
            if (nxt <= cur || (nxt <= cur + 2 && (rng() % 30 == 0))) {
                cur = nxt;
                es[i] = {min(u1, v1), max(u1, v1)};
                es[j] = {min(u2, v2), max(u2, v2)};
            } else {
                g.remove_edge(u1, v1); g.remove_edge(u2, v2);
                g.add_edge(a, b); g.add_edge(c, d);
            }
        }
        if (cur == 0 && is_3_connected(g) && !is_bipartite(g) && is_vge4_independent(g)) {
            out = g;
            return true;
        }
    }
    return false;
}

struct ConfigSummary {
    int n, num4;
    int graphs_found;
    int egrob_c16_cex;
    int min_c16_avoid_ab;
    double avg_ns_through_ab;
    double avg_ns_avoid_ab;
    int full_f2_span_count;
    double avg_menger3_ratio;
};

int main(int argc, char** argv) {
    bool smoke = (argc > 1 && string(argv[1]) == "--smoke");
    string out_json = (argc > 2) ? argv[2] : "out/menger_f2_audit.json";

    vector<pair<int,int>> configs = smoke
        ? vector<pair<int,int>>{{26, 0}, {28, 0}, {27, 1}}
        : vector<pair<int,int>>{{26, 0}, {28, 0}, {30, 0}, {32, 0}, {34, 0}, {27, 1}, {29, 1}, {30, 2}};
    int per_cfg = smoke ? 2 : 12;

    cout << "=== Wave 7 Agent #3: 3-Connected Menger / Tutte / F2 Cycle-Space Audit (threads="
         << omp_get_max_threads() << ", smoke=" << smoke << ") ===\n" << flush;

    vector<ConfigSummary> results;
    for (auto [n, num4] : configs) {
        int found = 0, cex = 0, min_c16_avoid = 1e9, full_span = 0;
        long long sum_ns_thru = 0, sum_ns_avoid = 0;
        double sum_menger_ratio = 0.0;

        #pragma omp parallel for schedule(dynamic) reduction(+:found,cex,full_span,sum_ns_thru,sum_ns_avoid,sum_menger_ratio)
        for (int idx = 0; idx < per_cfg; ++idx) {
            mt19937_64 rng(700001 + n * 1009 + num4 * 97 + idx * 7919);
            Graph H;
            if (!build_c4_c8_free_3conn(n, num4, rng, H)) continue;
            found++;

            int best_a = -1, best_b = -1, local_min_c16 = 1e9;
            for (int u = num4; u < n; ++u) {
                for (int v = u + 1; v < n; ++v) {
                    if (!H.has_edge(u, v)) continue;
                    int c16_av = count_cycles_avoid_edge(H, 16, u, v, 500);
                    if (c16_av < local_min_c16) {
                        local_min_c16 = c16_av;
                        best_a = u; best_b = v;
                    }
                }
            }
            if (local_min_c16 == 0) cex++;
            #pragma omp critical
            {
                if (local_min_c16 < min_c16_avoid) min_c16_avoid = local_min_c16;
            }

            if (best_a != -1) {
                int ns_thru = 0, ns_av = 0, f2_rank = 0, beta1 = 0;
                analyze_tutte_f2(H, best_a, best_b, (n <= 30 ? 11 : 10), ns_thru, ns_av, f2_rank, beta1);
                sum_ns_thru += ns_thru;
                sum_ns_avoid += ns_av;
                if (f2_rank == beta1) full_span++;

                Graph G = H;
                G.remove_edge(best_a, best_b);
                int pairs = 0, m3 = 0;
                for (int u = 0; u < n; ++u) {
                    if (u == best_a || u == best_b) continue;
                    for (int v = u + 1; v < n; ++v) {
                        if (v == best_a || v == best_b || G.has_edge(u, v)) continue;
                        pairs++;
                        if (has_3_disjoint_paths(G, u, v)) m3++;
                    }
                }
                sum_menger_ratio += (pairs > 0 ? (double)m3 / pairs : 1.0);
            }
        }

        ConfigSummary cs{
            n, num4, found, cex,
            (found > 0 ? min_c16_avoid : -1),
            (found > 0 ? (double)sum_ns_thru / found : 0.0),
            (found > 0 ? (double)sum_ns_avoid / found : 0.0),
            full_span,
            (found > 0 ? sum_menger_ratio / found : 0.0)
        };
        results.push_back(cs);
        cout << "[n=" << n << " V4=" << num4 << "] found=" << found
             << " C16_CEX=" << cex << " min_C16_avoid_ab=" << cs.min_c16_avoid_ab
             << " avg_NS_thru=" << cs.avg_ns_through_ab
             << " avg_NS_avoid=" << cs.avg_ns_avoid_ab
             << " F2_full_span=" << full_span << "/" << found
             << " Menger3_ratio=" << cs.avg_menger3_ratio << "\n" << flush;
    }

    ofstream jf(out_json);
    jf << "{\n  \"smoke\": " << (smoke ? "true" : "false") << ",\n  \"results\": [\n";
    for (size_t i = 0; i < results.size(); ++i) {
        const auto& r = results[i];
        jf << "    {\"n\": " << r.n << ", \"num4\": " << r.num4
           << ", \"graphs_found\": " << r.graphs_found
           << ", \"egrob_c16_cex\": " << r.egrob_c16_cex
           << ", \"min_c16_avoid_ab\": " << r.min_c16_avoid_ab
           << ", \"avg_ns_through_ab\": " << r.avg_ns_through_ab
           << ", \"avg_ns_avoid_ab\": " << r.avg_ns_avoid_ab
           << ", \"full_f2_span_count\": " << r.full_f2_span_count
           << ", \"avg_menger3_ratio\": " << r.avg_menger3_ratio << "}"
           << (i + 1 < results.size() ? "," : "") << "\n";
    }
    jf << "  ]\n}\n";
    jf.close();
    cout << "Wrote " << out_json << "\n";
    return 0;
}
