// Erdős Problem #64 (Erdős–Gyárfás Conjecture) — Sharded C++17 Search & Exact Cycle Checker
// Targets non-excluded regimes (general n >= 41, cubic n >= 50, bipartite n >= 68, girth >= 5):
//   Track 1: Deterministic sharded exhaustive regular voltage-graph lifts of high-girth cubic
//            base graphs (Petersen, Flower Snark J5, Dodecahedron, Heawood, McGee, Coxeter,
//            Tutte-Coxeter 8-cage) over cyclic, dihedral, and non-nilpotent groups (n in [60, 126]).
//   Track 2: Deterministic seed-partitioned soft-barrier tunneling Simulated Annealing (2-switches)
//            on asymmetric odd near-cubic (n=41..63) and cubic (n=50..80) graphs.
//
// Usage: search SHARD SHARDS LIFT_BUDGET_SEC SA_BUDGET_SEC

#include <algorithm>
#include <array>
#include <atomic>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstring>
#include <iostream>
#include <mutex>
#include <numeric>
#include <omp.h>
#include <random>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

using u64 = uint64_t;
using u128 = unsigned __int128;
using Clock = std::chrono::steady_clock;

static constexpr int MAXN = 128;
static constexpr int MAXD = 6;

struct Graph {
    int n = 0;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    u128 mask[MAXN];

    void clear(int nv) {
        n = nv;
        for (int i = 0; i < n; ++i) {
            deg[i] = 0;
            mask[i] = 0;
        }
    }

    bool add_edge(int u, int v) {
        if (u == v || u < 0 || v < 0 || u >= n || v >= n) return false;
        if ((mask[u] >> v) & 1) return false;
        if (deg[u] >= MAXD || deg[v] >= MAXD) return false;
        adj[u][deg[u]++] = v;
        adj[v][deg[v]++] = u;
        mask[u] |= (u128(1) << v);
        mask[v] |= (u128(1) << u);
        return true;
    }

    bool is_valid_min_deg3() const {
        if (n <= 0 || n > MAXN) return false;
        for (int i = 0; i < n; ++i) {
            if (deg[i] < 3) return false;
            u128 m = 0;
            for (int j = 0; j < deg[i]; ++j) {
                int v = adj[i][j];
                if (v == i || v < 0 || v >= n || ((m >> v) & 1)) return false;
                m |= (u128(1) << v);
                if (!((mask[v] >> i) & 1)) return false;
            }
            if (mask[i] != m) return false;
        }
        return true;
    }
};

static inline int popcnt128(u128 x) {
    return __builtin_popcountll(static_cast<u64>(x)) +
           __builtin_popcountll(static_cast<u64>(x >> 64));
}

bool has_C4(const Graph& g, int fiber_size = 1) {
    for (int u = 0; u < g.n; u += fiber_size) {
        u128 seen2 = 0;
        for (int i = 0; i < g.deg[u]; ++i) {
            int w = g.adj[u][i];
            u128 nbrs = g.mask[w] & ~(u128(1) << u);
            if (seen2 & nbrs) return true;
            seen2 |= nbrs;
        }
    }
    return false;
}

int count_C8(const Graph& g, int cap = 1, int fiber_size = 1) {
    u128 ep_masks[MAXN][64];
    int ep_cnt[MAXN] = {};
    int touched[MAXN];
    int total = 0;

    for (int root = 0; root < g.n; root += fiber_size) {
        int nt = 0;
        u128 root_bit = u128(1) << root;
        for (int i1 = 0; i1 < g.deg[root]; ++i1) {
            int v1 = g.adj[root][i1];
            if (v1 < root) continue;
            u128 m1 = u128(1) << v1;
            for (int i2 = 0; i2 < g.deg[v1]; ++i2) {
                int v2 = g.adj[v1][i2];
                if (v2 < root || v2 == root) continue;
                u128 m2 = m1 | (u128(1) << v2);
                for (int i3 = 0; i3 < g.deg[v2]; ++i3) {
                    int v3 = g.adj[v2][i3];
                    if (v3 < root || (((m2 | root_bit) >> v3) & 1)) continue;
                    u128 m3 = m2 | (u128(1) << v3);
                    for (int i4 = 0; i4 < g.deg[v3]; ++i4) {
                        int v4 = g.adj[v3][i4];
                        if (v4 < root || (((m3 | root_bit) >> v4) & 1)) continue;
                        if (ep_cnt[v4] == 0) touched[nt++] = v4;
                        for (int k = 0; k < ep_cnt[v4]; ++k) {
                            if ((ep_masks[v4][k] & m3) == 0) {
                                ++total;
                                if (total >= cap) {
                                    for (int t = 0; t < nt; ++t) ep_cnt[touched[t]] = 0;
                                    return total;
                                }
                            }
                        }
                        if (ep_cnt[v4] < 64) ep_masks[v4][ep_cnt[v4]++] = m3;
                    }
                }
            }
        }
        for (int t = 0; t < nt; ++t) ep_cnt[touched[t]] = 0;
    }
    return total;
}

struct CycleScratch {
    std::vector<u128> ep_masks[MAXN];
    int touched[MAXN];
    int ep_used[MAXN];
    CycleScratch() {
        std::memset(ep_used, 0, sizeof(ep_used));
        for (int i = 0; i < MAXN; ++i) ep_masks[i].reserve(128);
    }
};

int count_C16(const Graph& g, CycleScratch& sc, int cap = 1, int fiber_size = 1) {
    int total = 0;
    for (int root = 0; root < g.n; root += fiber_size) {
        int nt = 0;
        u128 root_bit = u128(1) << root;
        auto dfs8 = [&](auto&& self, int u, int depth, u128 interior) -> bool {
            if (depth == 7) {
                for (int i = 0; i < g.deg[u]; ++i) {
                    int w = g.adj[u][i];
                    if (w < root || (((interior | root_bit) >> w) & 1)) continue;
                    if (!sc.ep_used[w]) {
                        sc.ep_used[w] = 1;
                        sc.touched[nt++] = w;
                    }
                    for (u128 prev : sc.ep_masks[w]) {
                        if ((prev & interior) == 0) {
                            ++total;
                            if (total >= cap) return true;
                        }
                    }
                    sc.ep_masks[w].push_back(interior);
                }
                return false;
            }
            for (int i = 0; i < g.deg[u]; ++i) {
                int w = g.adj[u][i];
                if (w < root || (((interior | root_bit) >> w) & 1)) continue;
                if (self(self, w, depth + 1, interior | (u128(1) << w))) return true;
            }
            return false;
        };
        bool hit = dfs8(dfs8, root, 0, 0);
        for (int t = 0; t < nt; ++t) {
            int v = sc.touched[t];
            sc.ep_masks[v].clear();
            sc.ep_used[v] = 0;
        }
        if (hit) return total;
    }
    return total;
}

bool find_CL_fast(const Graph& g, int L, int node_budget = 25000, int fiber_size = 1) {
    if (g.n < L) return false;
    int nodes = 0;
    for (int root = 0; root < g.n; root += fiber_size) {
        u128 root_nbrs = g.mask[root];
        u128 visited = u128(1) << root;
        int per_root_budget = std::max(500, node_budget / std::max(1, g.n / fiber_size));
        int local_nodes = 0;
        auto dfs = [&](auto&& self, int u, int len) -> bool {
            if (++local_nodes > per_root_budget) return false;
            if (len == L - 1) return ((root_nbrs >> u) & 1) != 0;
            if (len == L - 2) return (g.mask[u] & root_nbrs & ~visited) != 0;
            for (int i = 0; i < g.deg[u]; ++i) {
                int w = g.adj[u][i];
                if (w < root || ((visited >> w) & 1)) continue;
                visited |= (u128(1) << w);
                if (self(self, w, len + 1)) return true;
                visited &= ~(u128(1) << w);
                if (local_nodes > per_root_budget) return false;
            }
            return false;
        };
        if (dfs(dfs, root, 0)) return true;
        nodes += local_nodes;
        if (nodes > node_budget * 2) break;
    }
    return false;
}

bool has_C32_exact(const Graph& g, CycleScratch& sc, int fiber_size = 1) {
    if (g.n < 32) return false;
    if (find_CL_fast(g, 32, 20000, fiber_size)) return true;
    for (int root = 0; root < g.n; root += fiber_size) {
        int nt = 0;
        u128 root_bit = u128(1) << root;
        auto dfs16 = [&](auto&& self, int u, int depth, u128 interior) -> bool {
            if (depth == 15) {
                for (int i = 0; i < g.deg[u]; ++i) {
                    int w = g.adj[u][i];
                    if (w < root || (((interior | root_bit) >> w) & 1)) continue;
                    if (!sc.ep_used[w]) {
                        sc.ep_used[w] = 1;
                        sc.touched[nt++] = w;
                    }
                    for (u128 prev : sc.ep_masks[w]) {
                        if ((prev & interior) == 0) return true;
                    }
                    sc.ep_masks[w].push_back(interior);
                }
                return false;
            }
            for (int i = 0; i < g.deg[u]; ++i) {
                int w = g.adj[u][i];
                if (w < root || (((interior | root_bit) >> w) & 1)) continue;
                if (self(self, w, depth + 1, interior | (u128(1) << w))) return true;
            }
            return false;
        };
        bool found = dfs16(dfs16, root, 0, 0);
        for (int t = 0; t < nt; ++t) {
            int v = sc.touched[t];
            sc.ep_masks[v].clear();
            sc.ep_used[v] = 0;
        }
        if (found) return true;
    }
    return false;
}

bool has_C64_exact(const Graph& g, int fiber_size = 1) {
    if (g.n < 64) return false;
    if (find_CL_fast(g, 64, 250000, fiber_size)) return true;
    for (int root = 0; root < g.n; root += fiber_size) {
        u128 root_nbrs = g.mask[root];
        u128 visited = u128(1) << root;
        u128 allowed_base = 0;
        for (int v = root; v < g.n; ++v) allowed_base |= (u128(1) << v);

        auto can_reach = [&](int u, int rem) -> bool {
            u128 frontier = u128(1) << u;
            u128 avail = allowed_base & ~visited;
            int reachable_cnt = 0;
            bool hit_root_nbr = false;
            for (int step = 0; step < rem; ++step) {
                u128 next = 0;
                u128 tmp = frontier;
                while (tmp) {
                    int v;
                    u64 lo = static_cast<u64>(tmp);
                    if (lo) {
                        v = __builtin_ctzll(lo);
                    } else {
                        v = 64 + __builtin_ctzll(static_cast<u64>(tmp >> 64));
                    }
                    tmp ^= (u128(1) << v);
                    next |= g.mask[v];
                }
                next &= avail;
                if (!next) break;
                if (next & root_nbrs) hit_root_nbr = true;
                reachable_cnt += popcnt128(next);
                avail &= ~next;
                frontier = next;
            }
            return hit_root_nbr && (reachable_cnt >= rem - 1);
        };

        auto dfs = [&](auto&& self, int u, int len) -> bool {
            int rem = 64 - len;
            if (rem == 1) return ((root_nbrs >> u) & 1) != 0;
            if (rem == 2) return (g.mask[u] & root_nbrs & ~visited) != 0;
            if ((rem == 32 || rem == 16 || rem == 8) && !can_reach(u, rem)) return false;
            for (int i = 0; i < g.deg[u]; ++i) {
                int w = g.adj[u][i];
                if (w < root || ((visited >> w) & 1)) continue;
                visited |= (u128(1) << w);
                if (self(self, w, len + 1)) return true;
                visited &= ~(u128(1) << w);
            }
            return false;
        };
        if (dfs(dfs, root, 0)) return true;
    }
    return false;
}

bool verify_counterexample_exact(const Graph& g, CycleScratch& sc) {
    if (!g.is_valid_min_deg3()) return false;
    if (has_C4(g, 1)) return false;
    if (count_C8(g, 1, 1) > 0) return false;
    if (count_C16(g, sc, 1, 1) > 0) return false;
    if (has_C32_exact(g, sc, 1)) return false;
    if (g.n >= 64 && has_C64_exact(g, 1)) return false;
    return true;
}

struct Group {
    std::string name;
    int order = 0;
    std::vector<std::vector<int>> mul;
};

Group make_cyclic(int m) {
    Group G{"Z" + std::to_string(m), m, std::vector<std::vector<int>>(m, std::vector<int>(m))};
    for (int a = 0; a < m; ++a)
        for (int b = 0; b < m; ++b)
            G.mul[a][b] = (a + b) % m;
    return G;
}

Group make_dihedral(int k) {
    Group G{"D" + std::to_string(k), 2 * k, std::vector<std::vector<int>>(2 * k, std::vector<int>(2 * k))};
    for (int a = 0; a < 2 * k; ++a) {
        int ia = a % k, ea = a / k;
        for (int b = 0; b < 2 * k; ++b) {
            int ib = b % k, eb = b / k;
            int ic = ea ? ((ia - ib) % k + k) % k : (ia + ib) % k;
            G.mul[a][b] = ic + (ea ^ eb) * k;
        }
    }
    return G;
}

Group make_A4() {
    std::vector<std::array<int, 4>> perms;
    std::array<int, 4> p = {0, 1, 2, 3};
    do {
        int inv = 0;
        for (int i = 0; i < 4; ++i)
            for (int j = i + 1; j < 4; ++j)
                if (p[i] > p[j]) ++inv;
        if (inv % 2 == 0) perms.push_back(p);
    } while (std::next_permutation(p.begin(), p.end()));
    Group G{"A4", 12, std::vector<std::vector<int>>(12, std::vector<int>(12))};
    for (int a = 0; a < 12; ++a)
        for (int b = 0; b < 12; ++b) {
            std::array<int, 4> c;
            for (int i = 0; i < 4; ++i) c[i] = perms[a][perms[b][i]];
            G.mul[a][b] = static_cast<int>(std::find(perms.begin(), perms.end(), c) - perms.begin());
        }
    return G;
}

Group make_dicyclic(int k) {
    int n = 4 * k, m = 2 * k;
    Group G{"Dic" + std::to_string(k), n, std::vector<std::vector<int>>(n, std::vector<int>(n))};
    for (int u = 0; u < n; ++u) {
        int iu = u % m, eu = u / m;
        for (int v = 0; v < n; ++v) {
            int iv = v % m, ev = v / m;
            int iw = eu ? ((iu - iv) % m + m) % m : (iu + iv) % m;
            if (eu && ev) iw = (iw + k) % m;
            int ew = eu ^ ev;
            G.mul[u][v] = iw + ew * m;
        }
    }
    return G;
}

struct BaseGraph {
    std::string name;
    int b = 0;
    std::vector<std::pair<int, int>> tree_edges, cotree_edges;
};

BaseGraph make_base(const std::string& name, int b, const std::vector<std::pair<int, int>>& edges) {
    BaseGraph bg{name, b, {}, {}};
    std::vector<std::vector<int>> adj(b);
    for (auto [u, v] : edges) { adj[u].push_back(v); adj[v].push_back(u); }
    std::vector<int> vis(b, 0), q = {0};
    vis[0] = 1;
    std::vector<std::pair<int, int>> ts;
    for (size_t qi = 0; qi < q.size(); ++qi) {
        int u = q[qi];
        for (int v : adj[u]) {
            if (!vis[v]) {
                vis[v] = 1;
                q.push_back(v);
                ts.push_back({std::min(u, v), std::max(u, v)});
            }
        }
    }
    for (auto [u, v] : edges) {
        std::pair<int, int> e = {std::min(u, v), std::max(u, v)};
        if (std::find(ts.begin(), ts.end(), e) != ts.end()) bg.tree_edges.push_back(e);
        else bg.cotree_edges.push_back(e);
    }
    return bg;
}

BaseGraph base_petersen() {
    std::vector<std::pair<int,int>> e;
    for (int i = 0; i < 5; ++i) {
        e.push_back({i, (i + 1) % 5});
        e.push_back({i, i + 5});
        e.push_back({i + 5, ((i + 2) % 5) + 5});
    }
    return make_base("Petersen", 10, e);
}

BaseGraph base_heawood() {
    std::vector<std::pair<int,int>> e;
    for (int i = 0; i < 14; ++i) {
        e.push_back({i, (i + 1) % 14});
        if (i % 2 == 0) e.push_back({i, (i + 5) % 14});
    }
    return make_base("Heawood", 14, e);
}

BaseGraph base_flower_j5() {
    std::vector<std::pair<int,int>> e;
    for (int i = 0; i < 5; ++i) {
        int a = 4 * i, b = 4 * i + 1, c = 4 * i + 2, d = 4 * i + 3;
        e.push_back({a, b}); e.push_back({a, c}); e.push_back({a, d});
        e.push_back({b, 4 * ((i + 1) % 5) + 1});
        if (i < 4) {
            e.push_back({c, 4 * (i + 1) + 2});
            e.push_back({d, 4 * (i + 1) + 3});
        } else {
            e.push_back({c, 3});
            e.push_back({d, 2});
        }
    }
    return make_base("FlowerJ5", 20, e);
}

BaseGraph base_dodecahedron() {
    std::vector<std::pair<int,int>> e;
    for (int i = 0; i < 5; ++i) {
        e.push_back({i, (i + 1) % 5});
        e.push_back({i, 5 + i});
        e.push_back({5 + i, 10 + i});
        e.push_back({10 + i, 5 + ((i + 1) % 5)});
        e.push_back({10 + i, 15 + i});
        e.push_back({15 + i, 15 + ((i + 1) % 5)});
    }
    return make_base("Dodecahedron", 20, e);
}

BaseGraph base_mcgee() {
    std::vector<std::pair<int,int>> e;
    for (int i = 0; i < 24; ++i) {
        e.push_back({i, (i + 1) % 24});
        if (i % 3 == 0 && i < 12) e.push_back({i, i + 12});
        if (i % 3 == 1) e.push_back({i, (i + 7) % 24});
    }
    return make_base("McGee", 24, e);
}

BaseGraph base_coxeter() {
    std::vector<std::pair<int,int>> e;
    for (int i = 0; i < 7; ++i) {
        e.push_back({i, (i + 1) % 7});
        e.push_back({7 + i, 7 + (i + 2) % 7});
        e.push_back({14 + i, 14 + (i + 3) % 7});
        e.push_back({21 + i, i});
        e.push_back({21 + i, 7 + i});
        e.push_back({21 + i, 14 + i});
    }
    return make_base("Coxeter", 28, e);
}

BaseGraph base_tutte_coxeter() {
    std::vector<std::pair<int,int>> e;
    for (int i = 0; i < 30; ++i) {
        e.push_back({i, (i + 1) % 30});
        if (i % 6 == 0) e.push_back({i, (i + 17) % 30});
        if (i % 6 == 1) e.push_back({i, (i + 21) % 30});
        if (i % 6 == 2) e.push_back({i, (i + 7) % 30});
    }
    return make_base("TutteCoxeter", 30, e);
}

void build_lift(const BaseGraph& bg, const Group& G, const std::vector<int>& volts, Graph& out) {
    const int m = G.order;
    out.clear(bg.b * m);
    for (auto [u, v] : bg.tree_edges)
        for (int g = 0; g < m; ++g)
            out.add_edge(u * m + g, v * m + g);
    for (size_t idx = 0; idx < bg.cotree_edges.size(); ++idx) {
        auto [u, v] = bg.cotree_edges[idx];
        int w = volts[idx];
        for (int g = 0; g < m; ++g)
            out.add_edge(u * m + g, v * m + G.mul[g][w]);
    }
}

void self_test_bases() {
    auto Z1 = make_cyclic(1);
    for (const auto& bg : {base_petersen(), base_heawood(), base_flower_j5(),
                           base_dodecahedron(), base_mcgee(), base_coxeter(), base_tutte_coxeter()}) {
        Graph g;
        build_lift(bg, Z1, std::vector<int>(bg.cotree_edges.size(), 0), g);
        if (!g.is_valid_min_deg3() || has_C4(g, 1)) {
            throw std::logic_error("Base graph self-test failed: " + bg.name);
        }
    }
}

void print_graph_json(std::ostream& os, const Graph& g) {
    os << "{\"n\":" << g.n << ",\"adj\":[";
    for (int i = 0; i < g.n; ++i) {
        if (i) os << ',';
        os << '[';
        for (int j = 0; j < g.deg[i]; ++j) {
            if (j) os << ',';
            os << g.adj[i][j];
        }
        os << ']';
    }
    os << "]}";
}

struct LiftFamilyResult {
    std::string name;
    int n = 0;
    u64 total_space = 0;
    u64 shard_assigned = 0;
    u64 tested = 0;
    u64 noC4 = 0, noC4_8 = 0, noC4_8_16 = 0, noC4_32 = 0;
    bool completed = true;
    double seconds = 0.0;
};

struct SAResult {
    int n = 0;
    u64 evals = 0;
    u64 zeroC8 = 0;
    u64 zeroC4_8_16 = 0;
    int minC16_at_0C8 = -1;
    double seconds = 0.0;
};

bool generate_random_girth5(int n, std::mt19937_64& rng, Graph& g) {
    int extra4 = (n & 1) ? 1 : 0;
    std::vector<int> stubs;
    stubs.reserve(3 * n + extra4);
    for (int i = 0; i < n; ++i)
        for (int k = 0; k < (i < extra4 ? 4 : 3); ++k) stubs.push_back(i);
    for (int attempt = 0; attempt < 500; ++attempt) {
        std::shuffle(stubs.begin(), stubs.end(), rng);
        g.clear(n);
        bool ok = true;
        for (size_t i = 0; i < stubs.size(); i += 2) {
            if (!g.add_edge(stubs[i], stubs[i + 1])) { ok = false; break; }
        }
        if (ok && !has_C4(g, 1)) return true;
    }
    return false;
}

bool try_two_switch(Graph& g, int a, int b, int c, int d) {
    if (a == c || a == d || b == c || b == d) return false;
    if (((g.mask[a] >> c) & 1) || ((g.mask[b] >> d) & 1)) return false;
    auto rep = [&](int u, int oldv, int newv) {
        for (int i = 0; i < g.deg[u]; ++i) {
            if (g.adj[u][i] == oldv) { g.adj[u][i] = newv; break; }
        }
        g.mask[u] ^= (u128(1) << oldv) | (u128(1) << newv);
    };
    rep(a, b, c); rep(b, a, d); rep(c, d, a); rep(d, c, b);
    return true;
}

int main(int argc, char** argv) {
    if (argc != 5) {
        throw std::invalid_argument("usage: search SHARD SHARDS LIFT_BUDGET_SEC SA_BUDGET_SEC");
    }
    const int shard = std::stoi(argv[1]);
    const int shards = std::stoi(argv[2]);
    const int lift_budget_sec = std::stoi(argv[3]);
    const int sa_budget_sec = std::stoi(argv[4]);
    if (shards < 1 || shards > 256 || shard < 0 || shard >= shards ||
        lift_budget_sec < 0 || sa_budget_sec < 0) {
        throw std::invalid_argument("invalid arguments");
    }

    self_test_bases();

    const auto global_start = Clock::now();
    const auto lift_deadline = global_start + std::chrono::seconds(lift_budget_sec);

    std::atomic<bool> found_cex{false};
    std::mutex cex_mtx;
    Graph cex_graph;
    std::string cex_source;

    struct FamilySpec {
        BaseGraph bg;
        Group G;
    };
    std::vector<FamilySpec> families;
    families.push_back({base_flower_j5(), make_cyclic(3)});
    families.push_back({base_dodecahedron(), make_cyclic(3)});
    families.push_back({base_mcgee(), make_cyclic(3)});
    families.push_back({base_heawood(), make_dihedral(3)});
    families.push_back({base_heawood(), make_cyclic(6)});
    families.push_back({base_petersen(), make_A4()});
    families.push_back({base_petersen(), make_dihedral(6)});
    families.push_back({base_petersen(), make_dicyclic(3)});
    families.push_back({base_flower_j5(), make_cyclic(4)});
    families.push_back({base_coxeter(), make_cyclic(3)});
    families.push_back({base_tutte_coxeter(), make_cyclic(3)});

    std::vector<LiftFamilyResult> lift_results;
    for (const auto& fam : families) {
        const int r = static_cast<int>(fam.bg.cotree_edges.size());
        const int m = fam.G.order;
        const int n = fam.bg.b * m;
        u64 total = 1;
        for (int i = 0; i < r; ++i) total *= static_cast<u64>(m);
        u64 assigned = (total > static_cast<u64>(shard)) ? ((total - 1 - shard) / shards + 1) : 0;

        LiftFamilyResult res;
        res.name = fam.bg.name + " x " + fam.G.name;
        res.n = n;
        res.total_space = total;
        res.shard_assigned = assigned;

        if (found_cex.load(std::memory_order_relaxed) || Clock::now() >= lift_deadline) {
            res.completed = false;
            lift_results.push_back(res);
            continue;
        }

        auto t0 = Clock::now();
        std::atomic<u64> tested{0}, p4{0}, p8{0}, p16{0}, p32{0};
        std::atomic<bool> timed_out{false};

        #pragma omp parallel
        {
            Graph g;
            CycleScratch sc;
            std::vector<int> volts(r);
            u64 lt = 0, l4 = 0, l8 = 0, l16 = 0, l32 = 0;

            #pragma omp for schedule(dynamic, 512)
            for (u64 k = 0; k < assigned; ++k) {
                if ((k & 1023) == 0) {
                    if (found_cex.load(std::memory_order_relaxed)) continue;
                    if (Clock::now() >= lift_deadline) {
                        timed_out.store(true, std::memory_order_relaxed);
                        continue;
                    }
                }
                if (timed_out.load(std::memory_order_relaxed) ||
                    found_cex.load(std::memory_order_relaxed)) continue;

                u64 idx = static_cast<u64>(shard) + k * static_cast<u64>(shards);
                u64 tmp = idx;
                for (int i = 0; i < r; ++i) {
                    volts[i] = static_cast<int>(tmp % m);
                    tmp /= m;
                }
                build_lift(fam.bg, fam.G, volts, g);
                ++lt;
                if (has_C4(g, m)) continue;
                ++l4;
                if (count_C8(g, 1, m) > 0) continue;
                ++l8;
                if (count_C16(g, sc, 1, m) > 0) continue;
                ++l16;
                if (has_C32_exact(g, sc, m)) continue;
                ++l32;
                if (n >= 64 && has_C64_exact(g, m)) continue;

                if (verify_counterexample_exact(g, sc)) {
                    std::lock_guard<std::mutex> lk(cex_mtx);
                    if (!found_cex.load()) {
                        cex_graph = g;
                        cex_source = res.name + " idx=" + std::to_string(idx);
                        found_cex.store(true);
                    }
                }
            }
            tested += lt; p4 += l4; p8 += l8; p16 += l16; p32 += l32;
        }

        res.tested = tested.load();
        res.noC4 = p4.load();
        res.noC4_8 = p8.load();
        res.noC4_8_16 = p16.load();
        res.noC4_32 = p32.load();
        res.completed = !timed_out.load() && !found_cex.load() && (res.tested == assigned);
        res.seconds = std::chrono::duration<double>(Clock::now() - t0).count();
        lift_results.push_back(res);
    }

    const std::vector<int> sa_orders = {41, 43, 45, 47, 49, 50, 52, 54, 56, 58, 60, 62, 70};
    std::vector<SAResult> sa_results;
    Graph best_near_miss;
    int best_near_miss_c16 = 1e9;
    std::mutex nm_mtx;

    if (!found_cex.load() && sa_budget_sec > 0) {
        const double per_order_sec = std::max(0.5, double(sa_budget_sec) / sa_orders.size());
        for (int n : sa_orders) {
            if (found_cex.load()) break;
            auto t0 = Clock::now();
            auto order_deadline = t0 + std::chrono::milliseconds(static_cast<int>(per_order_sec * 1000.0));
            std::atomic<u64> evals{0}, zero_c8{0}, zero_c8_16{0};
            int best_c16 = 1e9;
            std::mutex mtx;

            #pragma omp parallel
            {
                int tid = omp_get_thread_num();
                u64 seed = 0x9E3779B97F4A7C15ULL ^ (u64(shard) * 1000003ULL) ^
                           (u64(n) * 911382323ULL) ^ (u64(tid) * 1000000007ULL);
                std::mt19937_64 rng(seed);
                CycleScratch sc;
                Graph cur;
                std::uniform_real_distribution<double> U(0.0, 1.0);
                u64 le = 0, lz8 = 0, lz16 = 0;

                while (Clock::now() < order_deadline && !found_cex.load(std::memory_order_relaxed)) {
                    if (!generate_random_girth5(n, rng, cur)) continue;
                    int cur_c8 = count_C8(cur, 200, 1);
                    int cur_c16 = (cur_c8 <= 3) ? count_C16(cur, sc, 15000, 1) : 15000;
                    double cur_E = cur_c8 * 150.0 + cur_c16;

                    constexpr int STEPS = 32000;
                    for (int step = 0; step < STEPS; ++step) {
                        if ((step & 255) == 0 &&
                            (Clock::now() >= order_deadline || found_cex.load(std::memory_order_relaxed))) {
                            break;
                        }
                        int a = static_cast<int>(rng() % n);
                        int b = cur.adj[a][rng() % cur.deg[a]];
                        int c = static_cast<int>(rng() % n);
                        int d = cur.adj[c][rng() % cur.deg[c]];
                        if (a == c || a == d || b == c || b == d) continue;
                        if (((cur.mask[a] >> c) & 1) || ((cur.mask[b] >> d) & 1)) continue;

                        try_two_switch(cur, a, b, c, d);
                        ++le;
                        if (has_C4(cur, 1)) {
                            try_two_switch(cur, a, c, b, d);
                            continue;
                        }

                        int nc8 = count_C8(cur, std::max(cur_c8 + 3, 6), 1);
                        int nc16 = 15000;
                        if (nc8 <= 3) {
                            int cap = std::min(15000, cur_c16 + 400);
                            nc16 = count_C16(cur, sc, cap, 1);
                            if (nc8 == 0) {
                                ++lz8;
                                if (nc16 < best_c16) {
                                    std::lock_guard<std::mutex> lk(mtx);
                                    if (nc16 < best_c16) best_c16 = nc16;
                                }
                                if (nc16 < best_near_miss_c16) {
                                    std::lock_guard<std::mutex> lk(nm_mtx);
                                    if (nc16 < best_near_miss_c16) {
                                        best_near_miss_c16 = nc16;
                                        best_near_miss = cur;
                                    }
                                }
                                if (nc16 == 0) {
                                    ++lz16;
                                    if (verify_counterexample_exact(cur, sc)) {
                                        std::lock_guard<std::mutex> lk(cex_mtx);
                                        if (!found_cex.load()) {
                                            cex_graph = cur;
                                            cex_source = "SoftSA n=" + std::to_string(n) +
                                                         " shard=" + std::to_string(shard);
                                            found_cex.store(true);
                                        }
                                        break;
                                    }
                                }
                            }
                        }

                        double nE = nc8 * 150.0 + nc16;
                        double phase = std::fmod(double(step) / (STEPS / 4.0), 1.0);
                        double temp = 120.0 * std::pow(0.015, phase);
                        if (nE <= cur_E || U(rng) < std::exp((cur_E - nE) / temp)) {
                            cur_c8 = nc8;
                            cur_c16 = nc16;
                            cur_E = nE;
                        } else {
                            try_two_switch(cur, a, c, b, d);
                        }
                    }
                }
                evals += le; zero_c8 += lz8; zero_c8_16 += lz16;
            }

            SAResult sr;
            sr.n = n;
            sr.evals = evals.load();
            sr.zeroC8 = zero_c8.load();
            sr.zeroC4_8_16 = zero_c8_16.load();
            sr.minC16_at_0C8 = (best_c16 < 1e8) ? best_c16 : -1;
            sr.seconds = std::chrono::duration<double>(Clock::now() - t0).count();
            sa_results.push_back(sr);
        }
    }

    double total_sec = std::chrono::duration<double>(Clock::now() - global_start).count();
    std::cout << "{\"shard\":" << shard << ",\"shards\":" << shards
              << ",\"threads\":" << omp_get_max_threads()
              << ",\"seconds\":" << total_sec
              << ",\"lift_families\":[";
    for (size_t i = 0; i < lift_results.size(); ++i) {
        const auto& r = lift_results[i];
        if (i) std::cout << ',';
        std::cout << "{\"name\":\"" << r.name << "\",\"n\":" << r.n
                  << ",\"total_space\":" << r.total_space
                  << ",\"shard_assigned\":" << r.shard_assigned
                  << ",\"tested\":" << r.tested
                  << ",\"noC4\":" << r.noC4
                  << ",\"noC4_8\":" << r.noC4_8
                  << ",\"noC4_8_16\":" << r.noC4_8_16
                  << ",\"noC4_32\":" << r.noC4_32
                  << ",\"completed\":" << (r.completed ? "true" : "false")
                  << ",\"seconds\":" << r.seconds << "}";
    }
    std::cout << "],\"sa_orders\":[";
    for (size_t i = 0; i < sa_results.size(); ++i) {
        const auto& r = sa_results[i];
        if (i) std::cout << ',';
        std::cout << "{\"n\":" << r.n << ",\"evals\":" << r.evals
                  << ",\"zeroC8\":" << r.zeroC8
                  << ",\"zeroC4_8_16\":" << r.zeroC4_8_16
                  << ",\"minC16_at_0C8\":" << r.minC16_at_0C8
                  << ",\"seconds\":" << r.seconds << "}";
    }
    std::cout << "]";
    if (best_near_miss_c16 < 1e8) {
        std::cout << ",\"best_near_miss\":{\"c4\":0,\"c8\":0,\"c16\":" << best_near_miss_c16
                  << ",\"graph\":";
        print_graph_json(std::cout, best_near_miss);
        std::cout << "}";
    }
    if (found_cex.load()) {
        std::cout << ",\"witness\":{\"source\":\"" << cex_source << "\",\"graph\":";
        print_graph_json(std::cout, cex_graph);
        std::cout << "}";
    }
    std::cout << "}\n";
    return 0;
}
