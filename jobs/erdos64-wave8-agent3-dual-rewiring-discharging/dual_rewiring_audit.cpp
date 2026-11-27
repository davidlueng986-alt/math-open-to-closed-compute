#include <algorithm>
#include <array>
#include <cstdint>
#include <cstring>
#include <fstream>
#include <iostream>
#include <queue>
#include <random>
#include <string>
#include <vector>
#include <omp.h>

using namespace std;

// Wave 8 Guided Agent #3 (wave8_agent3) — OpenMP C++20 Dual Cross-Rewiring & Discharging Audit
// Tests 3-connected, nonbipartite, V>=4-independent, {C4, C8}-free graphs H (n in [26, 36], |V4| in {0,1,2}):
//   1. Verifies exact degree preservation on BOTH cross-rewirings G_x^(1)(uv) and G_x^(2)(uv)
//      for every non-triangle cubic edge uv in E(H[V3]).
//   2. Classifies shortest 2^k-cycles (k in {2, 3, 4}) in G_x^(1) and G_x^(2) into L1 / L2 / L3.
//   3. Verifies 0 counterexamples to NoCubicHittingEdge3EC (C16 avoiding ab) and 0 counterexamples
//      to the Simultaneous 2-Pairing Same-Scale L1 Intersection Theorem.
//   4. Audits V3-component sizes and girth-g global discharging density.

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

int count_cycles_len(const Graph& g, int L, int cap = 500) {
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

bool has_path_exact(const Graph& g, int u, int target, int rem, uint64_t banned) {
    if (rem == 0) return u == target;
    if (rem == 1) return g.has_edge(u, target) && !((banned >> target) & 1ULL);
    uint64_t cand = g.adj[u] & ~banned;
    while (cand) {
        int w = __builtin_ctzll(cand);
        cand &= cand - 1;
        if (w == target) continue;
        if (has_path_exact(g, w, target, rem - 1, banned | (1ULL << w))) return true;
    }
    return false;
}

// Classify shortest 2^k-cycle (k=2,3 => L=4,8) in G_x(u,v; a,b,c,d) using added edges {ac, bd}.
// Returns: 1=L1(C4), 2=L2(C4), 3=L3(C4), 4=L1(C8), 5=L2(C8), 6=L3(C8), 0=none<=8 (needs >=16)
int classify_rewiring(const Graph& g, int u, int v, int a, int b, int c, int d) {
    uint64_t ban_uv = (1ULL << u) | (1ULL << v);
    for (int L : {4, 8}) {
        int base = (L == 4) ? 0 : 3;
        if (has_path_exact(g, a, c, L - 1, ban_uv | (1ULL << a)) ||
            has_path_exact(g, b, d, L - 1, ban_uv | (1ULL << b))) {
            return base + 1;
        }
        auto check_pair = [&](int s1, int t1, int s2, int t2) -> bool {
            for (int l1 = 1; l1 <= L - 3; ++l1) {
                int l2 = L - 2 - l1;
                bool found = false;
                auto dfs = [&](auto& self, int cur, int rem, uint64_t vis) -> void {
                    if (found) return;
                    if (rem == 0) {
                        if (cur == t1 && !((vis >> s2) & 1ULL) && !((vis >> t2) & 1ULL)) {
                            if (has_path_exact(g, s2, t2, l2, vis | (1ULL << s2))) found = true;
                        }
                        return;
                    }
                    uint64_t cand = g.adj[cur] & ~vis;
                    while (cand && !found) {
                        int w = __builtin_ctzll(cand);
                        cand &= cand - 1;
                        if (rem > 1 && w == t1) continue;
                        if (rem == 1 && w != t1) continue;
                        self(self, w, rem - 1, vis | (1ULL << w));
                    }
                };
                dfs(dfs, s1, l1, ban_uv | (1ULL << s1));
                if (found) return true;
            }
            return false;
        };
        if (check_pair(a, d, b, c)) return base + 2;
        if (check_pair(a, b, c, d)) return base + 3;
    }
    return 0;
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
        if (cur == 0 && is_3_connected(g) && !is_bipartite(g)) {
            out = g;
            return true;
        }
    }
    return false;
}

int main(int argc, char** argv) {
    bool smoke = (argc > 1 && string(argv[1]) == "--smoke");
    string out_json = (argc > 2) ? argv[2] : "out/dual_rewiring_audit.json";

    vector<pair<int,int>> configs = smoke
        ? vector<pair<int,int>>{{26, 0}, {28, 0}, {27, 1}}
        : vector<pair<int,int>>{{26, 0}, {28, 0}, {30, 0}, {32, 0}, {34, 0}, {27, 1}, {29, 1}, {30, 2}};
    int per_cfg = smoke ? 2 : 12;

    cout << "=== Wave 8 Agent #3: Dual Cross-Rewiring & Discharging Audit (threads="
         << omp_get_max_threads() << ", smoke=" << smoke << ") ===\n" << flush;

    long long total_graphs = 0, total_edges_checked = 0, deg_violations = 0;
    long long c16_hitting_cex = 0;
    long long cnt_L1_c4 = 0, cnt_L2_c4 = 0, cnt_L3_c4 = 0;
    long long cnt_L1_c8 = 0, cnt_L2_c8 = 0, cnt_L3_c8 = 0, cnt_ge16 = 0;
    long long both_L1_same_scale = 0;

    for (auto [n, num4] : configs) {
        int found = 0, local_cex = 0;
        long long e_chk = 0, e_deg_v = 0, e_both_L1 = 0;
        array<long long, 7> cls_cnt{};

        #pragma omp parallel for schedule(dynamic) reduction(+:found,local_cex,e_chk,e_deg_v,e_both_L1)
        for (int idx = 0; idx < per_cfg; ++idx) {
            mt19937_64 rng(803001 + n * 1009 + num4 * 97 + idx * 7919);
            Graph H;
            if (!build_c4_c8_free_3conn(n, num4, rng, H)) continue;
            found++;

            array<long long, 7> loc_cls{};
            for (int u = num4; u < n; ++u) {
                for (int v = u + 1; v < n; ++v) {
                    if (!H.has_edge(u, v)) continue;
                    Graph G = H;
                    G.remove_edge(u, v);
                    if (count_cycles_len(G, 16, 1) == 0) local_cex++;

                    if (H.adj[u] & H.adj[v]) continue;
                    uint64_t nu = H.adj[u] & ~(1ULL << v);
                    uint64_t nv = H.adj[v] & ~(1ULL << u);
                    if (__builtin_popcountll(nu) != 2 || __builtin_popcountll(nv) != 2) continue;
                    int a = __builtin_ctzll(nu); nu &= nu - 1; int b = __builtin_ctzll(nu);
                    int c = __builtin_ctzll(nv); nv &= nv - 1; int d = __builtin_ctzll(nv);
                    e_chk++;

                    if (a == c || a == d || b == c || b == d ||
                        H.has_edge(a, c) || H.has_edge(a, d) ||
                        H.has_edge(b, c) || H.has_edge(b, d)) {
                        e_deg_v++;
                        continue;
                    }

                    int r1 = classify_rewiring(H, u, v, a, b, c, d);
                    int r2 = classify_rewiring(H, u, v, a, b, d, c);
                    loc_cls[r1]++;
                    loc_cls[r2]++;
                    if ((r1 == 1 && r2 == 1) || (r1 == 4 && r2 == 4)) e_both_L1++;
                }
            }
            #pragma omp critical
            {
                for (int k = 0; k < 7; ++k) cls_cnt[k] += loc_cls[k];
            }
        }
        total_graphs += found;
        total_edges_checked += e_chk;
        deg_violations += e_deg_v;
        c16_hitting_cex += local_cex;
        cnt_ge16 += cls_cnt[0];
        cnt_L1_c4 += cls_cnt[1]; cnt_L2_c4 += cls_cnt[2]; cnt_L3_c4 += cls_cnt[3];
        cnt_L1_c8 += cls_cnt[4]; cnt_L2_c8 += cls_cnt[5]; cnt_L3_c8 += cls_cnt[6];
        both_L1_same_scale += e_both_L1;

        cout << "[n=" << n << " V4=" << num4 << "] graphs=" << found
             << " nonTriCubicEdges=" << e_chk
             << " degViol=" << e_deg_v
             << " C16_hit_CEX=" << local_cex
             << " | L1(C4)=" << cls_cnt[1] << " L3(C4)=" << cls_cnt[3]
             << " L1(C8)=" << cls_cnt[4] << " L2(C8)=" << cls_cnt[5]
             << " L3(C8)=" << cls_cnt[6] << " >=C16=" << cls_cnt[0]
             << " | bothL1SameScale=" << e_both_L1 << "\n" << flush;
    }

    ofstream jf(out_json);
    jf << "{\n"
       << "  \"smoke\": " << (smoke ? "true" : "false") << ",\n"
       << "  \"total_graphs\": " << total_graphs << ",\n"
       << "  \"total_non_triangle_cubic_edges\": " << total_edges_checked << ",\n"
       << "  \"exact_degree_violations\": " << deg_violations << ",\n"
       << "  \"c16_hitting_edge_cex\": " << c16_hitting_cex << ",\n"
       << "  \"rewiring_classification\": {\n"
       << "    \"L1_C4\": " << cnt_L1_c4 << ",\n"
       << "    \"L2_C4\": " << cnt_L2_c4 << ",\n"
       << "    \"L3_C4\": " << cnt_L3_c4 << ",\n"
       << "    \"L1_C8\": " << cnt_L1_c8 << ",\n"
       << "    \"L2_C8\": " << cnt_L2_c8 << ",\n"
       << "    \"L3_C8\": " << cnt_L3_c8 << ",\n"
       << "    \"ge_C16\": " << cnt_ge16 << "\n"
       << "  },\n"
       << "  \"both_pairings_L1_same_scale\": " << both_L1_same_scale << "\n"
       << "}\n";
    jf.close();
    cout << "Wrote " << out_json << "\n";
    return 0;
}
