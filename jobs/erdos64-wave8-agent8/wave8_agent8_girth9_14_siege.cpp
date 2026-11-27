#include <algorithm>
#include <atomic>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <numeric>
#include <omp.h>
#include <random>
#include <string>
#include <vector>

struct CubicGraph {
    int n;
    std::vector<int> adj;
    CubicGraph(int n_ = 0) : n(n_), adj(3 * n_, -1) {}
};

static int compute_girth(const CubicGraph& G, int stop_below = 0) {
    int n = G.n;
    int best = n + 1;
    std::vector<int> dist(n), parent(n), q(n);
    for (int s = 0; s < n; ++s) {
        std::fill(dist.begin(), dist.end(), -1);
        std::fill(parent.begin(), parent.end(), -1);
        int head = 0, tail = 0;
        dist[s] = 0;
        q[tail++] = s;
        while (head < tail) {
            int u = q[head++];
            if (2 * dist[u] + 1 >= best) break;
            for (int j = 0; j < 3; ++j) {
                int v = G.adj[3 * u + j];
                if (v < 0) continue;
                if (dist[v] == -1) {
                    dist[v] = dist[u] + 1;
                    parent[v] = u;
                    q[tail++] = v;
                } else if (parent[u] != v) {
                    int cyc = dist[u] + dist[v] + 1;
                    if (cyc < best) {
                        best = cyc;
                        if (stop_below > 0 && best < stop_below) return best;
                    }
                }
            }
        }
    }
    return best;
}

static int64_t count_cycles_len(const CubicGraph& G, int L, int64_t limit = -1) {
    int n = G.n;
    std::vector<uint8_t> vis(n, 0);
    int64_t count = 0;
    std::vector<int> dist(n), q(n);
    int64_t nodes_visited = 0;
    const int64_t node_cap = (L <= 16) ? 1000000000LL : 2000000LL;
    for (int s = 0; s < n; ++s) {
        std::fill(dist.begin(), dist.end(), 999);
        int head = 0, tail = 0;
        dist[s] = 0;
        q[tail++] = s;
        int max_d = (L <= 16) ? (L / 2 + 1) : (L - 1);
        while (head < tail) {
            int u = q[head++];
            if (dist[u] >= max_d) continue;
            for (int j = 0; j < 3; ++j) {
                int v = G.adj[3 * u + j];
                if (v > s && dist[v] == 999) {
                    dist[v] = dist[u] + 1;
                    q[tail++] = v;
                }
            }
        }
        auto dfs = [&](auto&& self, int u, int depth, int first_nbr) -> void {
            if ((limit > 0 && count >= limit) || nodes_visited > node_cap) return;
            nodes_visited++;
            int rem = L - depth;
            if (rem == 1) {
                for (int j = 0; j < 3; ++j) {
                    if (G.adj[3 * u + j] == s) {
                        if (first_nbr < u) count++;
                        break;
                    }
                }
                return;
            }
            for (int j = 0; j < 3; ++j) {
                int v = G.adj[3 * u + j];
                if (v <= s || vis[v]) continue;
                if (dist[v] > rem - 1) continue;
                vis[v] = 1;
                self(self, v, depth + 1, depth == 0 ? v : first_nbr);
                vis[v] = 0;
                if ((limit > 0 && count >= limit) || nodes_visited > node_cap) return;
            }
        };
        vis[s] = 1;
        dfs(dfs, s, 0, -1);
        vis[s] = 0;
        if ((limit > 0 && count >= limit) || nodes_visited > node_cap) return count;
    }
    return count;
}

struct BaseGraph {
    std::string name;
    int nb;
    std::vector<std::pair<int, int>> edges;
};

static CubicGraph build_cyclic_lift(const BaseGraph& B, int M, const std::vector<int>& volts) {
    CubicGraph G(B.nb * M);
    std::vector<int> deg(G.n, 0);
    for (size_t e = 0; e < B.edges.size(); ++e) {
        int u = B.edges[e].first, v = B.edges[e].second, w = volts[e];
        for (int r = 0; r < M; ++r) {
            int gu = u * M + r;
            int gv = v * M + ((r + w) % M);
            if (gu == gv) return CubicGraph(0);
            for (int j = 0; j < deg[gu]; ++j)
                if (G.adj[3 * gu + j] == gv) return CubicGraph(0);
            G.adj[3 * gu + deg[gu]++] = gv;
            G.adj[3 * gv + deg[gv]++] = gu;
        }
    }
    return G;
}

static bool is_connected(const CubicGraph& G) {
    if (G.n == 0) return false;
    std::vector<uint8_t> vis(G.n, 0);
    std::vector<int> q(G.n);
    int head = 0, tail = 0;
    vis[0] = 1;
    q[tail++] = 0;
    while (head < tail) {
        int u = q[head++];
        for (int j = 0; j < 3; ++j) {
            int v = G.adj[3 * u + j];
            if (!vis[v]) { vis[v] = 1; q[tail++] = v; }
        }
    }
    return tail == G.n;
}

static bool build_high_girth_cubic(int n, int target_g, uint64_t seed, CubicGraph& out) {
    std::mt19937_64 rng(seed);
    std::vector<int> stubs(3 * n);
    for (int i = 0; i < n; ++i) { stubs[3*i] = i; stubs[3*i+1] = i; stubs[3*i+2] = i; }
    for (int attempt = 0; attempt < 50; ++attempt) {
        std::shuffle(stubs.begin(), stubs.end(), rng);
        CubicGraph G(n);
        std::vector<int> deg(n, 0);
        bool simple = true;
        for (int i = 0; i < 3 * n; i += 2) {
            int u = stubs[i], v = stubs[i + 1];
            if (u == v) { simple = false; break; }
            for (int j = 0; j < deg[u]; ++j)
                if (G.adj[3 * u + j] == v) { simple = false; break; }
            if (!simple) break;
            G.adj[3 * u + deg[u]++] = v;
            G.adj[3 * v + deg[v]++] = u;
        }
        if (!simple || !is_connected(G)) continue;
        if (compute_girth(G) >= target_g) { out = G; return true; }
        std::vector<std::pair<int,int>> edges;
        for (int u = 0; u < n; ++u)
            for (int j = 0; j < 3; ++j)
                if (u < G.adj[3 * u + j]) edges.push_back({u, G.adj[3 * u + j]});
        int m = (int)edges.size();
        auto has_edge = [&](int a, int b) {
            for (int j = 0; j < 3; ++j) if (G.adj[3 * a + j] == b) return true;
            return false;
        };
        auto replace_nbr = [&](int u, int old_v, int new_v) {
            for (int j = 0; j < 3; ++j) if (G.adj[3 * u + j] == old_v) { G.adj[3 * u + j] = new_v; return; }
        };
        auto count_bad_verts = [&](int lim) {
            int bad = 0;
            std::vector<int> dist(n), parent(n), q(n);
            for (int s = 0; s < n; ++s) {
                std::fill(dist.begin(), dist.end(), -1);
                std::fill(parent.begin(), parent.end(), -1);
                int head = 0, tail = 0;
                dist[s] = 0; q[tail++] = s;
                bool is_bad = false;
                while (head < tail && !is_bad) {
                    int u = q[head++];
                    if (2 * dist[u] + 1 >= lim) break;
                    for (int j = 0; j < 3; ++j) {
                        int v = G.adj[3 * u + j];
                        if (dist[v] == -1) { dist[v] = dist[u] + 1; parent[v] = u; q[tail++] = v; }
                        else if (parent[u] != v && dist[u] + dist[v] + 1 < lim) { is_bad = true; break; }
                    }
                }
                if (is_bad) bad++;
            }
            return bad;
        };
        int cur_bad = count_bad_verts(target_g);
        for (int step = 0; step < 3000 && cur_bad > 0; ++step) {
            int e1 = rng() % m, e2 = rng() % m;
            if (e1 == e2) continue;
            int a = edges[e1].first, b = edges[e1].second;
            int c = edges[e2].first, d = edges[e2].second;
            if (a == c || a == d || b == c || b == d) continue;
            int x1 = a, y1 = c, x2 = b, y2 = d;
            if (rng() & 1) { y1 = d; y2 = c; }
            if (has_edge(x1, y1) || has_edge(x2, y2)) continue;
            replace_nbr(a, b, y1); replace_nbr(y1, (y1 == c ? d : c), a);
            replace_nbr(b, a, y2); replace_nbr(y2, (y2 == c ? d : c), b);
            int nb = count_bad_verts(target_g);
            if (nb <= cur_bad) {
                cur_bad = nb;
                edges[e1] = {std::min(x1, y1), std::max(x1, y1)};
                edges[e2] = {std::min(x2, y2), std::max(x2, y2)};
            } else {
                replace_nbr(a, y1, b); replace_nbr(y1, a, (y1 == c ? d : c));
                replace_nbr(b, y2, a); replace_nbr(y2, b, (y2 == c ? d : c));
            }
        }
        if (cur_bad == 0 && is_connected(G)) { out = G; return true; }
    }
    return false;
}

int main(int argc, char** argv) {
    int lift_trials = (argc > 1) ? std::atoi(argv[1]) : 40000;
    int sa_steps    = (argc > 2) ? std::atoi(argv[2]) : 3000;
    std::printf("=== Wave 8 Agent #8: High-Girth (g in {9..14}) Adversarial Counterexample Siege ===\n");
    std::printf("Threads: %d | Lift trials/config: %d | SA steps/run: %d\n",
                omp_get_max_threads(), lift_trials, sa_steps);

    std::vector<BaseGraph> bases = {
        {"K4", 4, {{0,1},{0,2},{0,3},{1,2},{1,3},{2,3}}},
        {"K33", 6, {{0,3},{0,4},{0,5},{1,3},{1,4},{1,5},{2,3},{2,4},{2,5}}},
        {"Petersen", 10, {{0,1},{1,2},{2,3},{3,4},{4,0},{5,7},{7,9},{9,6},{6,8},{8,5},{0,5},{1,6},{2,7},{3,8},{4,9}}},
        {"Heawood", 14, {{0,1},{1,2},{2,3},{3,4},{4,5},{5,6},{6,7},{7,8},{8,9},{9,10},{10,11},{11,12},{12,13},{13,0},
                         {0,5},{2,7},{4,9},{6,11},{8,13},{10,1},{12,3}}}
    };

    std::atomic<int64_t> total_lifts_tested{0}, total_g9_plus{0}, total_zero_c16{0}, total_ce{0};
    int64_t global_min_c16 = 1e18;

    std::vector<std::pair<int, int>> configs;
    for (int M : {33, 35, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83}) configs.push_back({0, M});
    for (int M : {23, 25, 27, 29, 31, 35, 37, 41, 43, 47, 53}) configs.push_back({1, M});
    for (int M : {14, 15, 16, 17, 19, 21, 23, 25, 27, 29}) configs.push_back({2, M});
    for (int M : {10, 11, 12, 13, 15, 17, 19, 21}) configs.push_back({3, M});

    #pragma omp parallel for schedule(dynamic)
    for (int ci = 0; ci < (int)configs.size(); ++ci) {
        int bi = configs[ci].first, M = configs[ci].second;
        const BaseGraph& B = bases[bi];
        int ne = (int)B.edges.size();
        std::mt19937_64 rng(0x88080000ULL + ci * 1000003ULL);
        std::vector<int> volts(ne, 0);
        int64_t local_g9 = 0, local_zero16 = 0, local_ce = 0, local_min16 = 1e18;
        int max_g_seen = 0;

        for (int t = 0; t < lift_trials; ++t) {
            for (int e = 0; e < ne; ++e) volts[e] = rng() % M;
            CubicGraph G = build_cyclic_lift(B, M, volts);
            if (G.n == 0) continue;
            int g = compute_girth(G, 9);
            if (g < 9 || !is_connected(G)) continue;
            local_g9++;
            if (g > max_g_seen) max_g_seen = g;
            int64_t c16 = count_cycles_len(G, 16, 100000);
            if (c16 < local_min16) local_min16 = c16;
            if (c16 == 0) {
                local_zero16++;
                if (count_cycles_len(G, 32, 1) == 0 && count_cycles_len(G, 64, 1) == 0) {
                    local_ce++;
                    #pragma omp critical
                    std::printf("!!! COUNTEREXAMPLE: %s x Z_%d (n=%d, g=%d) !!!\n", B.name.c_str(), M, G.n, g);
                }
            }
        }
        total_lifts_tested += lift_trials;
        total_g9_plus += local_g9;
        total_zero_c16 += local_zero16;
        total_ce += local_ce;
        #pragma omp critical
        {
            if (local_min16 < global_min_c16) global_min_c16 = local_min16;
            if (local_g9 > 0)
                std::printf("  [LIFT] %-8s x Z_%-2d (n=%3d): g>=9=%6lld (max_g=%2d), min_C16=%lld, zero16=%lld, CE=%lld\n",
                            B.name.c_str(), M, B.nb * M, (long long)local_g9, max_g_seen,
                            (long long)local_min16, (long long)local_zero16, (long long)local_ce);
        }
    }
    std::printf("[SUMMARY CAMPAIGN 1 - LIFTS] tested=%lld, g>=9=%lld, min_C16=%lld, zero_C16=%lld, counterexamples=%lld\n",
                (long long)total_lifts_tested.load(), (long long)total_g9_plus.load(),
                (long long)global_min_c16, (long long)total_zero_c16.load(), (long long)total_ce.load());

    std::vector<int> sa_orders = {132, 140, 150, 160, 180, 200, 220, 240};
    std::atomic<int64_t> sa_total_moves{0}, sa_zero16{0}, sa_ce{0};
    #pragma omp parallel for schedule(dynamic)
    for (int oi = 0; oi < (int)sa_orders.size(); ++oi) {
        int n = sa_orders[oi];
        CubicGraph G;
        if (!build_high_girth_cubic(n, 9, 0x990000ULL + oi * 7919ULL, G)) {
            #pragma omp critical
            std::printf("  [SA] n=%3d: failed to initialize g>=9 seed\n", n);
            continue;
        }
        int init_g = compute_girth(G);
        int64_t cur_c16 = count_cycles_len(G, 16, 100000), min_c16 = cur_c16;
        std::vector<std::pair<int,int>> edges;
        for (int u = 0; u < n; ++u)
            for (int j = 0; j < 3; ++j)
                if (u < G.adj[3 * u + j]) edges.push_back({u, G.adj[3 * u + j]});
        int m = (int)edges.size();
        std::mt19937_64 rng(0xAA0000ULL + oi * 104729ULL);
        auto has_edge = [&](int a, int b) {
            for (int j = 0; j < 3; ++j) if (G.adj[3 * a + j] == b) return true;
            return false;
        };
        auto replace_nbr = [&](int u, int old_v, int new_v) {
            for (int j = 0; j < 3; ++j) if (G.adj[3 * u + j] == old_v) { G.adj[3 * u + j] = new_v; return; }
        };
        int accepted = 0;
        for (int step = 0; step < sa_steps; ++step) {
            int e1 = rng() % m, e2 = rng() % m;
            if (e1 == e2) continue;
            int a = edges[e1].first, b = edges[e1].second;
            int c = edges[e2].first, d = edges[e2].second;
            if (a == c || a == d || b == c || b == d) continue;
            int x1 = a, y1 = c, x2 = b, y2 = d;
            if (rng() & 1) { y1 = d; y2 = c; }
            if (has_edge(x1, y1) || has_edge(x2, y2)) continue;
            replace_nbr(a, b, y1); replace_nbr(y1, (y1 == c ? d : c), a);
            replace_nbr(b, a, y2); replace_nbr(y2, (y2 == c ? d : c), b);
            if (compute_girth(G, 9) >= 9 && is_connected(G)) {
                int64_t new_c16 = count_cycles_len(G, 16, 100000);
                if (new_c16 <= cur_c16) {
                    cur_c16 = new_c16;
                    edges[e1] = {std::min(x1, y1), std::max(x1, y1)};
                    edges[e2] = {std::min(x2, y2), std::max(x2, y2)};
                    accepted++;
                    if (cur_c16 < min_c16) min_c16 = cur_c16;
                    if (cur_c16 == 0) {
                        sa_zero16++;
                        if (count_cycles_len(G, 32, 1) == 0) sa_ce++;
                        break;
                    }
                } else {
                    replace_nbr(a, y1, b); replace_nbr(y1, a, (y1 == c ? d : c));
                    replace_nbr(b, y2, a); replace_nbr(y2, b, (y2 == c ? d : c));
                }
            } else {
                replace_nbr(a, y1, b); replace_nbr(y1, a, (y1 == c ? d : c));
                replace_nbr(b, y2, a); replace_nbr(y2, b, (y2 == c ? d : c));
            }
        }
        sa_total_moves += sa_steps;
        #pragma omp critical
        std::printf("  [SA] n=%3d (init_g=%2d): moves=%d, accepted=%d, min_C16=%lld\n",
                    n, init_g, sa_steps, accepted, (long long)min_c16);
    }
    std::printf("[SUMMARY CAMPAIGN 2 - SA] total_moves=%lld, zero_C16=%lld, counterexamples=%lld\n",
                (long long)sa_total_moves.load(), (long long)sa_zero16.load(), (long long)sa_ce.load());
    return 0;
}
