#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <map>
#include <numeric>
#include <omp.h>
#include <random>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

using namespace std;

static constexpr int MAXN = 192;

struct Mask {
    uint64_t w[3];
    inline Mask() { w[0] = w[1] = w[2] = 0; }
    inline void set(int v) { w[v >> 6] |= (1ULL << (v & 63)); }
    inline bool test(int v) const { return (w[v >> 6] >> (v & 63)) & 1ULL; }
    inline bool disjoint(const Mask& o) const {
        return ((w[0] & o.w[0]) | (w[1] & o.w[1]) | (w[2] & o.w[2])) == 0;
    }
    inline Mask with(int v) const { Mask r = *this; r.set(v); return r; }
};

struct Graph {
    int n = 0;
    int deg[MAXN]{};
    int adj[MAXN][3]{};
    Mask adj_mask[MAXN]{};

    void clear(int n_) {
        n = n_;
        for (int i = 0; i < n; ++i) { deg[i] = 0; adj_mask[i] = Mask(); }
    }
    inline bool has_edge(int u, int v) const { return adj_mask[u].test(v); }
    inline bool add_edge_safe(int u, int v) {
        if (u == v || has_edge(u, v) || deg[u] >= 3 || deg[v] >= 3) return false;
        adj[u][deg[u]++] = v;
        adj[v][deg[v]++] = u;
        adj_mask[u].set(v);
        adj_mask[v].set(u);
        return true;
    }
};

struct Scratch {
    vector<Mask> buckets[MAXN];
    vector<int> touched;
    vector<Mask> b32[MAXN];
    vector<int> touched32;

    Scratch() {
        touched.reserve(MAXN);
        touched32.reserve(MAXN);
        for (int i = 0; i < MAXN; ++i) buckets[i].reserve(32);
    }
    inline void reset_buckets() {
        for (int v : touched) buckets[v].clear();
        touched.clear();
    }
    inline void reset_b32() {
        for (int v : touched32) b32[v].clear();
        touched32.clear();
    }
};

static inline bool has_c4_edge(const Graph& g, int u, int v) {
    for (int i = 0; i < g.deg[u]; ++i) {
        int x = g.adj[u][i];
        if (x == v) continue;
        for (int j = 0; j < g.deg[v]; ++j) {
            int y = g.adj[v][j];
            if (y == u || y == x) continue;
            if (g.has_edge(x, y)) return true;
        }
    }
    return false;
}

static void dfs_collect(const Graph& g, int cur, int rem, int forbid_end,
                        const Mask& vis, const Mask& interior, Scratch& sc) {
    const int d = g.deg[cur];
    if (rem == 1) {
        for (int i = 0; i < d; ++i) {
            int nxt = g.adj[cur][i];
            if (nxt == forbid_end || vis.test(nxt)) continue;
            if (sc.buckets[nxt].empty()) sc.touched.push_back(nxt);
            sc.buckets[nxt].push_back(interior);
        }
        return;
    }
    for (int i = 0; i < d; ++i) {
        int nxt = g.adj[cur][i];
        if (nxt == forbid_end || vis.test(nxt)) continue;
        dfs_collect(g, nxt, rem - 1, forbid_end, vis.with(nxt), interior.with(nxt), sc);
    }
}

static bool dfs_exists(const Graph& g, int cur, int rem, int forbid_end,
                       const Mask& vis, const Mask& interior, const Scratch& sc) {
    const int d = g.deg[cur];
    if (rem == 1) {
        for (int i = 0; i < d; ++i) {
            int nxt = g.adj[cur][i];
            if (nxt == forbid_end || vis.test(nxt)) continue;
            for (const Mask& m : sc.buckets[nxt]) {
                if (m.disjoint(interior)) return true;
            }
        }
        return false;
    }
    for (int i = 0; i < d; ++i) {
        int nxt = g.adj[cur][i];
        if (nxt == forbid_end || vis.test(nxt)) continue;
        if (dfs_exists(g, nxt, rem - 1, forbid_end, vis.with(nxt), interior.with(nxt), sc)) return true;
    }
    return false;
}

static bool has_c8_edge(const Graph& g, int u, int v, Scratch& sc) {
    sc.reset_buckets();
    Mask vu; vu.set(u);
    Mask empty;
    dfs_collect(g, u, 3, v, vu, empty, sc);
    if (sc.touched.empty()) return false;
    Mask vv; vv.set(v);
    return dfs_exists(g, v, 4, u, vv, empty, sc);
}

static bool has_c16_edge(const Graph& g, int u, int v, Scratch& sc) {
    sc.reset_buckets();
    Mask vu; vu.set(u);
    Mask empty;
    dfs_collect(g, u, 7, v, vu, empty, sc);
    if (sc.touched.empty()) return false;
    Mask vv; vv.set(v);
    return dfs_exists(g, v, 8, u, vv, empty, sc);
}

static void dfs_collect32(const Graph& g, int cur, int rem, int forbid_end,
                          const Mask& vis, const Mask& interior, Scratch& sc) {
    const int d = g.deg[cur];
    if (rem == 1) {
        for (int i = 0; i < d; ++i) {
            int nxt = g.adj[cur][i];
            if (nxt == forbid_end || vis.test(nxt)) continue;
            if (sc.b32[nxt].empty()) sc.touched32.push_back(nxt);
            sc.b32[nxt].push_back(interior);
        }
        return;
    }
    for (int i = 0; i < d; ++i) {
        int nxt = g.adj[cur][i];
        if (nxt == forbid_end || vis.test(nxt)) continue;
        dfs_collect32(g, nxt, rem - 1, forbid_end, vis.with(nxt), interior.with(nxt), sc);
    }
}

static bool dfs_exists32(const Graph& g, int cur, int rem, int forbid_end,
                         const Mask& vis, const Mask& interior, const Scratch& sc) {
    const int d = g.deg[cur];
    if (rem == 1) {
        for (int i = 0; i < d; ++i) {
            int nxt = g.adj[cur][i];
            if (nxt == forbid_end || vis.test(nxt)) continue;
            for (const Mask& m : sc.b32[nxt]) {
                if (m.disjoint(interior)) return true;
            }
        }
        return false;
    }
    for (int i = 0; i < d; ++i) {
        int nxt = g.adj[cur][i];
        if (nxt == forbid_end || vis.test(nxt)) continue;
        if (dfs_exists32(g, nxt, rem - 1, forbid_end, vis.with(nxt), interior.with(nxt), sc)) return true;
    }
    return false;
}

static bool has_c32_edge(const Graph& g, int u, int v, Scratch& sc) {
    if (g.n < 32) return false;
    sc.reset_b32();
    Mask vu; vu.set(u);
    Mask empty;
    dfs_collect32(g, u, 15, v, vu, empty, sc);
    if (sc.touched32.empty()) return false;
    Mask vv; vv.set(v);
    return dfs_exists32(g, v, 16, u, vv, empty, sc);
}

static bool has_cycle_edge_dfs(const Graph& g, int u, int v, int target_len, long long node_limit, bool& exhausted) {
    if (g.n < target_len) { exhausted = true; return false; }
    long long nodes = 0;
    exhausted = true;
    bool in_path[MAXN]{};
    in_path[u] = true;
    in_path[v] = true;
    auto dfs = [&](auto&& self, int cur, int depth) -> bool {
        if (++nodes > node_limit) { exhausted = false; return false; }
        if (depth == target_len - 2) return g.has_edge(cur, v);
        const int d = g.deg[cur];
        for (int i = 0; i < d; ++i) {
            int nxt = g.adj[cur][i];
            if (in_path[nxt]) continue;
            in_path[nxt] = true;
            if (self(self, nxt, depth + 1)) { in_path[nxt] = false; return true; }
            in_path[nxt] = false;
            if (!exhausted) return false;
        }
        return false;
    };
    return dfs(dfs, u, 0);
}

static bool is_connected(const Graph& g) {
    bool vis[MAXN]{};
    int q[MAXN];
    int head = 0, tail = 0;
    vis[0] = true; q[tail++] = 0;
    while (head < tail) {
        int u = q[head++];
        for (int i = 0; i < g.deg[u]; ++i) {
            int v = g.adj[u][i];
            if (!vis[v]) { vis[v] = true; q[tail++] = v; }
        }
    }
    return tail == g.n;
}

struct Group {
    string name;
    int m = 0;
    vector<vector<int>> mul;
    vector<int> inv;

    void compute_inv() {
        inv.assign(m, 0);
        for (int a = 0; a < m; ++a)
            for (int b = 0; b < m; ++b)
                if (mul[a][b] == 0) inv[a] = b;
    }
};

static Group make_cyclic(int m) {
    Group G; G.name = "Z" + to_string(m); G.m = m;
    G.mul.assign(m, vector<int>(m));
    for (int a = 0; a < m; ++a)
        for (int b = 0; b < m; ++b)
            G.mul[a][b] = (a + b) % m;
    G.compute_inv();
    return G;
}

static Group make_direct(const Group& A, const Group& B) {
    Group G; G.name = A.name + "x" + B.name; G.m = A.m * B.m;
    G.mul.assign(G.m, vector<int>(G.m));
    for (int a1 = 0; a1 < A.m; ++a1)
        for (int b1 = 0; b1 < B.m; ++b1)
            for (int a2 = 0; a2 < A.m; ++a2)
                for (int b2 = 0; b2 < B.m; ++b2)
                    G.mul[a1 * B.m + b1][a2 * B.m + b2] = A.mul[a1][a2] * B.m + B.mul[b1][b2];
    G.compute_inv();
    return G;
}

static Group make_dihedral(int k) {
    Group G; G.name = "D" + to_string(k); G.m = 2 * k;
    G.mul.assign(G.m, vector<int>(G.m));
    for (int r1 = 0; r1 < k; ++r1)
        for (int s1 = 0; s1 < 2; ++s1)
            for (int r2 = 0; r2 < k; ++r2)
                for (int s2 = 0; s2 < 2; ++s2) {
                    int nr = s1 ? (r1 - r2 + k) % k : (r1 + r2) % k;
                    int ns = s1 ^ s2;
                    G.mul[r1 * 2 + s1][r2 * 2 + s2] = nr * 2 + ns;
                }
    G.compute_inv();
    return G;
}

static Group make_dicyclic(int k) {
    int n = 2 * k;
    Group G; G.name = "Dic" + to_string(k); G.m = 4 * k;
    G.mul.assign(G.m, vector<int>(G.m));
    for (int a1 = 0; a1 < n; ++a1)
        for (int x1 = 0; x1 < 2; ++x1)
            for (int a2 = 0; a2 < n; ++a2)
                for (int x2 = 0; x2 < 2; ++x2) {
                    int na = x1 ? (a1 - a2 + n) % n : (a1 + a2) % n;
                    int nx = x1 + x2;
                    if (nx == 2) { na = (na + k) % n; nx = 0; }
                    G.mul[a1 * 2 + x1][a2 * 2 + x2] = na * 2 + nx;
                }
    G.compute_inv();
    return G;
}

static Group make_semidirect(int p, int q, int c) {
    Group G; G.name = "Z" + to_string(p) + "x|Z" + to_string(q); G.m = p * q;
    G.mul.assign(G.m, vector<int>(G.m));
    vector<int> cp(q, 1);
    for (int i = 1; i < q; ++i) cp[i] = (cp[i - 1] * c) % p;
    for (int a1 = 0; a1 < p; ++a1)
        for (int b1 = 0; b1 < q; ++b1)
            for (int a2 = 0; a2 < p; ++a2)
                for (int b2 = 0; b2 < q; ++b2) {
                    int na = (a1 + cp[b1] * a2) % p;
                    int nb = (b1 + b2) % q;
                    G.mul[a1 * q + b1][a2 * q + b2] = na * q + nb;
                }
    G.compute_inv();
    return G;
}

static Group make_perm_group(int k, bool even_only) {
    vector<int> p(k);
    iota(p.begin(), p.end(), 0);
    vector<vector<int>> elems;
    map<vector<int>, int> idx;
    do {
        int invs = 0;
        for (int i = 0; i < k; ++i)
            for (int j = i + 1; j < k; ++j)
                if (p[i] > p[j]) ++invs;
        if (!even_only || (invs % 2 == 0)) {
            idx[p] = (int)elems.size();
            elems.push_back(p);
        }
    } while (next_permutation(p.begin(), p.end()));

    Group G;
    G.name = (even_only ? "A" : "S") + to_string(k);
    G.m = (int)elems.size();
    G.mul.assign(G.m, vector<int>(G.m));
    for (int i = 0; i < G.m; ++i)
        for (int j = 0; j < G.m; ++j) {
            vector<int> c(k);
            for (int t = 0; t < k; ++t) c[t] = elems[i][elems[j][t]];
            G.mul[i][j] = idx[c];
        }
    G.compute_inv();
    return G;
}

static Group make_gl2_3(bool sl_only) {
    vector<array<int,4>> elems;
    map<array<int,4>, int> idx;
    array<int,4> id = {1, 0, 0, 1};
    idx[id] = 0;
    elems.push_back(id);
    for (int a = 0; a < 3; ++a)
        for (int b = 0; b < 3; ++b)
            for (int c = 0; c < 3; ++c)
                for (int d = 0; d < 3; ++d) {
                    int det = (a * d - b * c) % 3;
                    if (det < 0) det += 3;
                    if (det == 0) continue;
                    if (sl_only && det != 1) continue;
                    array<int,4> M = {a, b, c, d};
                    if (idx.count(M)) continue;
                    idx[M] = (int)elems.size();
                    elems.push_back(M);
                }
    Group G;
    G.name = sl_only ? "SL2_3" : "GL2_3";
    G.m = (int)elems.size();
    G.mul.assign(G.m, vector<int>(G.m));
    for (int i = 0; i < G.m; ++i)
        for (int j = 0; j < G.m; ++j) {
            auto A = elems[i], B = elems[j];
            array<int,4> C = {
                (A[0]*B[0] + A[1]*B[2]) % 3,
                (A[0]*B[1] + A[1]*B[3]) % 3,
                (A[2]*B[0] + A[3]*B[2]) % 3,
                (A[2]*B[1] + A[3]*B[3]) % 3
            };
            G.mul[i][j] = idx[C];
        }
    G.compute_inv();
    return G;
}

struct BaseGraph {
    string name;
    int b = 0;
    vector<pair<int,int>> edges;
};

static vector<BaseGraph> get_base_graphs() {
    vector<BaseGraph> res;
    res.push_back({"Theta3", 2, {{0,1}, {0,1}, {0,1}}});
    res.push_back({"K4", 4, {{0,1},{0,2},{0,3}, {1,2},{1,3},{2,3}}});
    res.push_back({"PrismY3", 6, {{0,1},{1,2},{0,3},{1,4},{2,5}, {2,0},{3,4},{4,5},{5,3}}});
    res.push_back({"K33", 6, {{0,3},{0,4},{0,5},{1,3},{2,3}, {1,4},{1,5},{2,4},{2,5}}});
    res.push_back({"CubeQ3", 8, {{0,1},{1,2},{2,3},{0,4},{1,5},{2,6},{3,7}, {3,0},{4,5},{5,6},{6,7},{7,4}}});
    res.push_back({"PetersenP10", 10, {
        {0,1},{1,2},{2,3},{3,4},{0,5},{1,6},{2,7},{3,8},{4,9},
        {4,0},{5,7},{7,9},{9,6},{6,8},{8,5}
    }});
    return res;
}

static bool build_lift(const BaseGraph& B, const Group& G, const vector<int>& free_volts, Graph& out) {
    int n = B.b * G.m;
    if (n > MAXN) return false;
    out.clear(n);
    int tree_edges = B.b - 1;
    for (size_t e = 0; e < B.edges.size(); ++e) {
        int u = B.edges[e].first, v = B.edges[e].second;
        int volt = (e < (size_t)tree_edges) ? 0 : free_volts[e - tree_edges];
        for (int x = 0; x < G.m; ++x) {
            int y = G.mul[x][volt];
            int vu = u * G.m + x;
            int vv = v * G.m + y;
            if (!out.add_edge_safe(vu, vv)) return false;
        }
    }
    return is_connected(out);
}

static int check_lift(const BaseGraph& B, const Group& G, const vector<int>& free_volts,
                      const Graph& g, Scratch& sc, bool& has32, int& c64_stat) {
    int tree_edges = B.b - 1;
    for (size_t e = 0; e < B.edges.size(); ++e) {
        int u = B.edges[e].first * G.m;
        int volt = (e < (size_t)tree_edges) ? 0 : free_volts[e - tree_edges];
        int v = B.edges[e].second * G.m + volt;
        if (has_c4_edge(g, u, v)) return 4;
    }
    for (size_t e = 0; e < B.edges.size(); ++e) {
        int u = B.edges[e].first * G.m;
        int volt = (e < (size_t)tree_edges) ? 0 : free_volts[e - tree_edges];
        int v = B.edges[e].second * G.m + volt;
        if (has_c8_edge(g, u, v, sc)) return 8;
    }
    for (size_t e = 0; e < B.edges.size(); ++e) {
        int u = B.edges[e].first * G.m;
        int volt = (e < (size_t)tree_edges) ? 0 : free_volts[e - tree_edges];
        int v = B.edges[e].second * G.m + volt;
        if (has_c16_edge(g, u, v, sc)) return 16;
    }
    has32 = false;
    for (size_t e = 0; e < B.edges.size(); ++e) {
        int u = B.edges[e].first * G.m;
        int volt = (e < (size_t)tree_edges) ? 0 : free_volts[e - tree_edges];
        int v = B.edges[e].second * G.m + volt;
        if (has_c32_edge(g, u, v, sc)) { has32 = true; break; }
    }
    c64_stat = -1;
    if (!has32) {
        bool found64 = false;
        bool all_exh = true;
        for (size_t e = 0; e < B.edges.size(); ++e) {
            int u = B.edges[e].first * G.m;
            int volt = (e < (size_t)tree_edges) ? 0 : free_volts[e - tree_edges];
            int v = B.edges[e].second * G.m + volt;
            bool exh = false;
            if (has_cycle_edge_dfs(g, u, v, 64, 10000000LL, exh)) { found64 = true; break; }
            if (!exh) all_exh = false;
        }
        c64_stat = found64 ? 1 : (all_exh ? 0 : -1);
    }
    return 0;
}

static vector<Group> build_groups_for_order(int m) {
    vector<Group> gs;
    gs.push_back(make_cyclic(m));
    if (m % 2 == 0 && m >= 6) gs.push_back(make_dihedral(m / 2));
    if (m % 4 == 0 && m >= 8) gs.push_back(make_dicyclic(m / 4));
    for (int a = 2; a * a <= m; ++a) {
        if (m % a == 0) {
            int b = m / a;
            if (gcd(a, b) > 1) gs.push_back(make_direct(make_cyclic(a), make_cyclic(b)));
        }
    }
    if (m == 12) gs.push_back(make_perm_group(4, true));
    if (m == 24) {
        gs.push_back(make_perm_group(4, false));
        gs.push_back(make_gl2_3(true));
        gs.push_back(make_direct(make_perm_group(4, true), make_cyclic(2)));
    }
    if (m == 36) {
        gs.push_back(make_direct(make_perm_group(4, true), make_cyclic(3)));
        gs.push_back(make_direct(make_dihedral(3), make_dihedral(3)));
    }
    if (m == 48) {
        gs.push_back(make_gl2_3(false));
        gs.push_back(make_direct(make_perm_group(4, false), make_cyclic(2)));
    }
    if (m == 60) {
        gs.push_back(make_perm_group(5, true));
        gs.push_back(make_direct(make_perm_group(4, true), make_cyclic(5)));
    }
    struct SemiSpec { int m, p, q, c; };
    vector<SemiSpec> semis = {
        {20, 5, 4, 2}, {21, 7, 3, 2}, {39, 13, 3, 3}, {42, 7, 6, 3},
        {52, 13, 4, 5}, {55, 11, 5, 3}, {57, 19, 3, 7}, {63, 7, 9, 2}, {68, 17, 4, 4}
    };
    for (auto sp : semis) {
        if (sp.m == m) gs.push_back(make_semidirect(sp.p, sp.q, sp.c));
    }
    return gs;
}

int main(int argc, char** argv) {
    if (argc < 4) {
        cerr << "Usage: " << argv[0] << " <base_idx 0=Theta3,1=K4,2=PrismY3,3=K33,4=CubeQ3,5=PetersenP10> <m_min> <m_max> [samples_if_large=500000] [threads]\n";
        return 1;
    }
    int base_idx = atoi(argv[1]);
    int m_min = atoi(argv[2]);
    int m_max = atoi(argv[3]);
    long long max_samples = (argc >= 5) ? atoll(argv[4]) : 500000LL;
    int threads = (argc >= 6) ? atoi(argv[5]) : omp_get_max_threads();
    omp_set_num_threads(threads);

    auto bases = get_base_graphs();
    const BaseGraph& B = bases[base_idx];
    int free_dim = (int)B.edges.size() - (B.b - 1);

    auto t0 = chrono::steady_clock::now();
    long long total_checked = 0;
    long long total_zero4816 = 0;
    long long total_zero481632 = 0;

    for (int m = m_min; m <= m_max; ++m) {
        int n = B.b * m;
        if (n > MAXN) continue;
        auto groups = build_groups_for_order(m);
        for (const Group& G : groups) {
            long long space_size = 1;
            bool exhaustive = true;
            for (int d = 0; d < free_dim; ++d) {
                space_size *= m;
                if (space_size > max_samples) { exhaustive = false; break; }
            }
            long long num_tasks = exhaustive ? space_size : max_samples;
            long long valid_lifts = 0, hits_4816 = 0, hits_481632 = 0;
            vector<string> notable_logs;

            #pragma omp parallel
            {
                Scratch sc;
                Graph g;
                mt19937_64 rng((uint64_t)m * 1000003ULL + (uint64_t)omp_get_thread_num() * 99991ULL + base_idx * 777ULL);
                vector<int> fv(free_dim);
                long long loc_valid = 0, loc_4816 = 0, loc_481632 = 0;
                vector<string> loc_logs;

                #pragma omp for schedule(dynamic, 64)
                for (long long t = 0; t < num_tasks; ++t) {
                    if (exhaustive) {
                        long long tmp = t;
                        for (int d = 0; d < free_dim; ++d) { fv[d] = (int)(tmp % m); tmp /= m; }
                    } else {
                        for (int d = 0; d < free_dim; ++d) fv[d] = (int)(rng() % m);
                    }
                    if (!build_lift(B, G, fv, g)) continue;
                    ++loc_valid;
                    bool has32 = true;
                    int c64_stat = -1;
                    int fail_len = check_lift(B, G, fv, g, sc, has32, c64_stat);
                    if (fail_len == 0) {
                        ++loc_4816;
                        if (!has32) {
                            ++loc_481632;
                            ostringstream oss;
                            oss << "!!! C4=C8=C16=C32=0 LIFT FOUND !!! base=" << B.name
                                << " group=" << G.name << " n=" << n << " volts=[";
                            for (int d = 0; d < free_dim; ++d) oss << (d ? "," : "") << fv[d];
                            oss << "] C64=" << c64_stat;
                            loc_logs.push_back(oss.str());
                        } else if (loc_4816 <= 2) {
                            ostringstream oss;
                            oss << "ZERO4816 base=" << B.name << " group=" << G.name
                                << " n=" << n << " volts=[";
                            for (int d = 0; d < free_dim; ++d) oss << (d ? "," : "") << fv[d];
                            oss << "] hasC32=1";
                            loc_logs.push_back(oss.str());
                        }
                    }
                }
                #pragma omp critical
                {
                    valid_lifts += loc_valid;
                    hits_4816 += loc_4816;
                    hits_481632 += loc_481632;
                    for (auto& s : loc_logs) notable_logs.push_back(move(s));
                }
            }
            total_checked += valid_lifts;
            total_zero4816 += hits_4816;
            total_zero481632 += hits_481632;
            cout << "LIFT base=" << B.name << " group=" << G.name << " m=" << m << " n=" << n
                 << " mode=" << (exhaustive ? "EXHAUSTIVE" : "SAMPLED")
                 << " valid=" << valid_lifts
                 << " zero4816=" << hits_4816
                 << " zero481632=" << hits_481632 << "\n";
            for (const auto& s : notable_logs) cout << "  " << s << "\n";
        }
    }
    auto t1 = chrono::steady_clock::now();
    double elapsed = chrono::duration<double>(t1 - t0).count();
    cout << "SUMMARY base=" << B.name << " m=[" << m_min << "," << m_max << "]"
         << " total_valid=" << total_checked
         << " total_zero4816=" << total_zero4816
         << " total_zero481632=" << total_zero481632
         << " elapsed=" << elapsed << "s\n";
    return 0;
}
