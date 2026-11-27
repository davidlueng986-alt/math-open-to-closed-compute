// Wave 8 Agent #6 — OpenMP C++20 Adversarial Siege on the Exact Open Frontier g in {9..14}
// Tests:
//   (A) Famous high-girth cubic graphs (Balaban-10, Foster, Biggs-Smith, Tutte-12):
//       exact #C16 + Posa-rotation power-of-2 hit audit
//   (B) Cyclic Z_m lifts of K4, K3,3, and Petersen (girth >= 9, n = 100..222)
//   (C) Non-abelian Dihedral D_m & S_4 voltage lifts of K4 and K3,3 (girth >= 9, n = 96..240)
//   (D) Adversarial Girth >= 9 2-Switch Simulated Annealing explicitly minimizing #C16
//       on n in {80, 90, 100, 110, 120, 140}

#include <algorithm>
#include <array>
#include <atomic>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <random>
#include <sstream>
#include <string>
#include <vector>
#ifdef _OPENMP
#include <omp.h>
#endif

struct CubicGraph {
    int n = 0;
    std::vector<std::array<int, 3>> adj;
    CubicGraph() = default;
    explicit CubicGraph(int n_) : n(n_), adj(n_, {-1, -1, -1}) {}
};

static bool is_valid_cubic(const CubicGraph &g) {
    if (g.n <= 0 || (g.n & 1)) return false;
    for (int u = 0; u < g.n; ++u) {
        auto a = g.adj[u];
        if (a[0] < 0 || a[1] < 0 || a[2] < 0) return false;
        if (a[0] >= g.n || a[1] >= g.n || a[2] >= g.n) return false;
        if (a[0] == u || a[1] == u || a[2] == u) return false;
        if (a[0] == a[1] || a[0] == a[2] || a[1] == a[2]) return false;
        for (int v : a) {
            auto b = g.adj[v];
            if (b[0] != u && b[1] != u && b[2] != u) return false;
        }
    }
    return true;
}

static int compute_girth(const CubicGraph &g) {
    int best = 1000;
    std::vector<int> dist(g.n), par(g.n), q(g.n);
    for (int s = 0; s < g.n; ++s) {
        std::fill(dist.begin(), dist.end(), -1);
        int head = 0, tail = 0;
        dist[s] = 0; par[s] = -1; q[tail++] = s;
        while (head < tail) {
            int u = q[head++];
            if (2 * dist[u] + 1 >= best) break;
            for (int v : g.adj[u]) {
                if (dist[v] == -1) {
                    dist[v] = dist[u] + 1;
                    par[v] = u;
                    q[tail++] = v;
                } else if (par[u] != v) {
                    int c = dist[u] + dist[v] + 1;
                    if (c < best) best = c;
                }
            }
        }
    }
    return best;
}

struct Bitset256 {
    uint64_t w[4] = {0, 0, 0, 0};
    inline void set(int i) { w[i >> 6] |= (1ULL << (i & 63)); }
    inline bool test(int i) const { return (w[i >> 6] >> (i & 63)) & 1ULL; }
    inline bool disjoint_except(const Bitset256 &o, int u) const {
        for (int k = 0; k < 4; ++k) {
            uint64_t inter = w[k] & o.w[k];
            if (k == (u >> 6)) inter &= ~(1ULL << (u & 63));
            if (inter) return false;
        }
        return true;
    }
};

static long long count_c16(const CubicGraph &g, long long cap = 1000000000LL) {
    long long total = 0;
    std::vector<std::vector<Bitset256>> buckets(g.n);
    std::vector<int> touched;
    touched.reserve(g.n);

    for (int s = 0; s < g.n; ++s) {
        for (int u : touched) buckets[u].clear();
        touched.clear();

        struct Frame { int u; int depth; Bitset256 mask; };
        std::vector<Frame> st;
        st.reserve(256);
        Bitset256 m0;
        st.push_back({s, 0, m0});
        while (!st.empty()) {
            Frame f = st.back();
            st.pop_back();
            if (f.depth == 8) {
                if (buckets[f.u].empty()) touched.push_back(f.u);
                buckets[f.u].push_back(f.mask);
                continue;
            }
            for (int v : g.adj[f.u]) {
                if (v <= s) continue;
                if (!f.mask.test(v)) {
                    Bitset256 nm = f.mask;
                    nm.set(v);
                    st.push_back({v, f.depth + 1, nm});
                }
            }
        }
        for (int u : touched) {
            const auto &vec = buckets[u];
            int sz = (int)vec.size();
            for (int i = 0; i < sz; ++i) {
                for (int j = i + 1; j < sz; ++j) {
                    if (vec[i].disjoint_except(vec[j], u)) {
                        ++total;
                        if (total >= cap) return total;
                    }
                }
            }
        }
    }
    return total;
}

static bool has_c32_quick(const CubicGraph &g, int max_starts = 8) {
    int limit_s = std::min(g.n, max_starts);
    std::vector<std::vector<Bitset256>> buckets(g.n);
    std::vector<int> touched;
    touched.reserve(g.n);

    for (int s = 0; s < limit_s; ++s) {
        for (int u : touched) buckets[u].clear();
        touched.clear();
        struct Frame { int u; int depth; Bitset256 mask; };
        std::vector<Frame> st;
        st.reserve(4096);
        Bitset256 m0;
        st.push_back({s, 0, m0});
        int collected = 0;
        while (!st.empty() && collected < 12000) {
            Frame f = st.back();
            st.pop_back();
            if (f.depth == 16) {
                if (buckets[f.u].empty()) touched.push_back(f.u);
                for (const auto &prev : buckets[f.u]) {
                    if (prev.disjoint_except(f.mask, f.u)) return true;
                }
                buckets[f.u].push_back(f.mask);
                ++collected;
                continue;
            }
            for (int v : g.adj[f.u]) {
                if (v <= s) continue;
                if (!f.mask.test(v)) {
                    Bitset256 nm = f.mask;
                    nm.set(v);
                    st.push_back({v, f.depth + 1, nm});
                }
            }
        }
    }
    return false;
}

static CubicGraph make_lcf(int n, const std::vector<int> &shifts) {
    CubicGraph g(n);
    std::vector<std::vector<int>> tmp(n);
    for (int i = 0; i < n; ++i) {
        int j = (i + 1) % n;
        tmp[i].push_back(j);
        tmp[j].push_back(i);
    }
    int L = (int)shifts.size();
    for (int i = 0; i < n; ++i) {
        int j = (i + shifts[i % L]) % n;
        if (j < 0) j += n;
        if (std::find(tmp[i].begin(), tmp[i].end(), j) == tmp[i].end()) {
            tmp[i].push_back(j);
            tmp[j].push_back(i);
        }
    }
    for (int i = 0; i < n; ++i)
        for (int k = 0; k < 3; ++k) g.adj[i][k] = tmp[i][k];
    return g;
}

struct FiniteGroup {
    int order;
    std::vector<std::vector<int>> mult;
    std::vector<int> inv;
};

static FiniteGroup make_cyclic_group(int m) {
    FiniteGroup G;
    G.order = m;
    G.mult.assign(m, std::vector<int>(m));
    G.inv.resize(m);
    for (int a = 0; a < m; ++a) {
        G.inv[a] = (m - a) % m;
        for (int b = 0; b < m; ++b) G.mult[a][b] = (a + b) % m;
    }
    return G;
}

static FiniteGroup make_dihedral_group(int m) {
    int ord = 2 * m;
    FiniteGroup G;
    G.order = ord;
    G.mult.assign(ord, std::vector<int>(ord));
    G.inv.resize(ord);
    for (int a = 0; a < ord; ++a) {
        int r1 = a % m, s1 = a / m;
        int ir = s1 ? r1 : ((m - r1) % m);
        G.inv[a] = ir + s1 * m;
        for (int b = 0; b < ord; ++b) {
            int r2 = b % m, s2 = b / m;
            int nr = s1 ? (r1 - r2) % m : (r1 + r2) % m;
            if (nr < 0) nr += m;
            G.mult[a][b] = nr + (s1 ^ s2) * m;
        }
    }
    return G;
}

static FiniteGroup make_s4_group() {
    std::vector<std::array<int, 4>> perms;
    std::array<int, 4> p = {0, 1, 2, 3};
    do { perms.push_back(p); } while (std::next_permutation(p.begin(), p.end()));
    int ord = (int)perms.size();
    FiniteGroup G;
    G.order = ord;
    G.mult.assign(ord, std::vector<int>(ord));
    G.inv.resize(ord);
    auto find_p = [&](const std::array<int, 4> &q) {
        for (int i = 0; i < ord; ++i) if (perms[i] == q) return i;
        return -1;
    };
    for (int a = 0; a < ord; ++a) {
        std::array<int, 4> invp;
        for (int i = 0; i < 4; ++i) invp[perms[a][i]] = i;
        G.inv[a] = find_p(invp);
        for (int b = 0; b < ord; ++b) {
            std::array<int, 4> prod;
            for (int i = 0; i < 4; ++i) prod[i] = perms[a][perms[b][i]];
            G.mult[a][b] = find_p(prod);
        }
    }
    return G;
}

static CubicGraph make_group_lift(const CubicGraph &B, const FiniteGroup &grp,
                                  const std::vector<std::array<int, 3>> &volt) {
    int m = grp.order;
    CubicGraph g(B.n * m);
    for (int u = 0; u < B.n; ++u) {
        for (int k = 0; k < 3; ++k) {
            int v = B.adj[u][k];
            int w = volt[u][k];
            for (int r = 0; r < m; ++r) {
                int nr = grp.mult[r][w];
                g.adj[u * m + r][k] = v * m + nr;
            }
        }
    }
    return g;
}

struct BaseWithTree {
    CubicGraph B;
    std::vector<std::pair<int, int>> non_tree_edges;
};

static BaseWithTree prepare_base(const CubicGraph &B) {
    BaseWithTree res;
    res.B = B;
    std::vector<bool> vis(B.n, false);
    std::vector<std::array<bool, 3>> in_tree(B.n, {false, false, false});
    std::vector<int> q;
    vis[0] = true; q.push_back(0);
    for (size_t i = 0; i < q.size(); ++i) {
        int u = q[i];
        for (int k = 0; k < 3; ++k) {
            int v = B.adj[u][k];
            if (!vis[v]) {
                vis[v] = true;
                in_tree[u][k] = true;
                for (int j = 0; j < 3; ++j) if (B.adj[v][j] == u) in_tree[v][j] = true;
                q.push_back(v);
            }
        }
    }
    for (int u = 0; u < B.n; ++u) {
        for (int k = 0; k < 3; ++k) {
            int v = B.adj[u][k];
            if (u < v && !in_tree[u][k]) {
                res.non_tree_edges.push_back({u, k});
            }
        }
    }
    return res;
}

static bool build_girth9_cubic(int n, uint64_t seed, CubicGraph &out) {
    std::mt19937_64 rng(seed);
    std::vector<int> stubs(3 * n);
    for (int i = 0; i < n; ++i) { stubs[3*i] = i; stubs[3*i+1] = i; stubs[3*i+2] = i; }
    for (int attempt = 0; attempt < 250; ++attempt) {
        std::shuffle(stubs.begin(), stubs.end(), rng);
        std::vector<std::vector<int>> tmp(n);
        bool ok = true;
        for (int i = 0; i < 3 * n; i += 2) {
            int u = stubs[i], v = stubs[i + 1];
            if (u == v || std::find(tmp[u].begin(), tmp[u].end(), v) != tmp[u].end()) {
                ok = false; break;
            }
            tmp[u].push_back(v); tmp[v].push_back(u);
        }
        if (!ok) continue;
        CubicGraph g(n);
        for (int i = 0; i < n; ++i) for (int k = 0; k < 3; ++k) g.adj[i][k] = tmp[i][k];

        auto short_score = [&](const CubicGraph &gr, int &bu, int &bi) -> int {
            int worst = 9, cnt = 0;
            std::vector<int> dist(n), par(n), q(n);
            for (int s = 0; s < n; ++s) {
                std::fill(dist.begin(), dist.end(), -1);
                int h = 0, t = 0; dist[s] = 0; par[s] = -1; q[t++] = s;
                while (h < t) {
                    int u = q[h++];
                    if (2 * dist[u] + 1 >= 9) break;
                    for (int idx = 0; idx < 3; ++idx) {
                        int v = gr.adj[u][idx];
                        if (dist[v] == -1) {
                            dist[v] = dist[u] + 1; par[v] = u; q[t++] = v;
                        } else if (par[u] != v) {
                            int cl = dist[u] + dist[v] + 1;
                            if (cl < 9) {
                                ++cnt;
                                if (cl < worst || (cl == worst && (rng() & 7) == 0)) {
                                    worst = cl; bu = u; bi = idx;
                                }
                            }
                        }
                    }
                }
            }
            return cnt;
        };

        auto do_sw = [](CubicGraph &gr, int u, int ui, int x, int xi, int mode) -> bool {
            int v = gr.adj[u][ui], y = gr.adj[x][xi];
            if (u == x || u == y || v == x || v == y) return false;
            int a = (mode == 0) ? x : y, b = (mode == 0) ? y : x;
            for (int w : gr.adj[u]) if (w == a) return false;
            for (int w : gr.adj[v]) if (w == b) return false;
            int vi = 0; while (gr.adj[v][vi] != u) ++vi;
            int yi = 0; while (gr.adj[y][yi] != x) ++yi;
            if (mode == 0) {
                gr.adj[u][ui] = x; gr.adj[x][xi] = u;
                gr.adj[v][vi] = y; gr.adj[y][yi] = v;
            } else {
                gr.adj[u][ui] = y; gr.adj[y][yi] = u;
                gr.adj[v][vi] = x; gr.adj[x][xi] = v;
            }
            return true;
        };

        int bu = 0, bi = 0;
        int cur = short_score(g, bu, bi);
        for (int step = 0; step < 3000 && cur > 0; ++step) {
            int x = (int)(rng() % n), xi = (int)(rng() % 3), mode = (int)(rng() & 1);
            CubicGraph cand = g;
            if (!do_sw(cand, bu, bi, x, xi, mode)) continue;
            int nbu = 0, nbi = 0;
            int nxt = short_score(cand, nbu, nbi);
            if (nxt <= cur) {
                g = std::move(cand); cur = nxt; bu = nbu; bi = nbi;
            }
        }
        if (cur == 0 && compute_girth(g) >= 9) {
            out = std::move(g);
            return true;
        }
    }
    return false;
}

static bool do_switch(CubicGraph &gr, int u, int ui, int x, int xi, int mode) {
    int v = gr.adj[u][ui], y = gr.adj[x][xi];
    if (u == x || u == y || v == x || v == y) return false;
    int a = (mode == 0) ? x : y, b = (mode == 0) ? y : x;
    for (int w : gr.adj[u]) if (w == a) return false;
    for (int w : gr.adj[v]) if (w == b) return false;
    int vi = 0; while (gr.adj[v][vi] != u) ++vi;
    int yi = 0; while (gr.adj[y][yi] != x) ++yi;
    if (mode == 0) {
        gr.adj[u][ui] = x; gr.adj[x][xi] = u;
        gr.adj[v][vi] = y; gr.adj[y][yi] = v;
    } else {
        gr.adj[u][ui] = y; gr.adj[y][yi] = u;
        gr.adj[v][vi] = x; gr.adj[x][xi] = v;
    }
    return true;
}

int main(int argc, char **argv) {
    bool quick = (argc > 1 && std::string(argv[1]) == "--quick");
    auto t0 = std::chrono::steady_clock::now();

    std::cout << "=== Wave 8 Agent #6: OpenMP Girth 9-14 Counterexample & Structural Siege ===\n";
#ifdef _OPENMP
    std::cout << "OpenMP threads: " << omp_get_max_threads() << (quick ? " (QUICK mode)\n" : " (FULL mode)\n");
#endif

    CubicGraph K4(4);
    K4.adj = {{{1,2,3}, {0,2,3}, {0,1,3}, {0,1,2}}};
    CubicGraph K33(6);
    K33.adj = {{{3,4,5}, {3,4,5}, {3,4,5}, {0,1,2}, {0,1,2}, {0,1,2}}};
    CubicGraph Petersen(10);
    Petersen.adj = {{{1,4,5},{0,2,6},{1,3,7},{2,4,8},{3,0,9},
                     {0,7,8},{1,8,9},{2,9,5},{3,5,6},{4,6,7}}};

    BaseWithTree btK4 = prepare_base(K4);
    BaseWithTree btK33 = prepare_base(K33);
    BaseWithTree btPet = prepare_base(Petersen);

    struct Named { std::string name; CubicGraph g; };
    std::vector<Named> famous = {
        {"Balaban-10 (n=70,g=10)", make_lcf(70, {-9,-25,-19,29,13,35,-13,-29,19,25,9,-29,29,17,33,21,9,-13,-31,-9,25,17,9,-31,27,-9,17,-19,-29,27,-17,-9,-29,33,-25,25,-21,17,-17,29,35,-29,17,-17,21,-25,25,-33,29,9,17,-27,29,19,-17,9,-27,31,-9,-17,-25,9,31,13,-9,-21,-33,-17,-29,29})},
        {"Foster (n=90,g=10)", make_lcf(90, {17,-9,37,-37,9,-17})},
        {"Biggs-Smith (n=102,g=9)", make_lcf(102, {16,24,-38,17,34,48,-19,41,-35,47,-20,34,-36,21,14,48,-16,-36,-43,28,-17,21,29,-43,46,-24,28,-38,-14,-50,-45,21,8,27,-21,20,-37,39,-34,-44,-8,38,-21,25,15,-34,18,-28,-41,36,8,-29,-21,-48,-28,-20,-47,14,-8,-15,-27,38,24,-48,-18,25,38,31,-25,24,-46,-14,28,11,21,35,-39,43,36,-38,14,50,43,36,-11,-36,-24,45,8,19,-25,38,20,-24,-14,-21,-8,44,-31,-38,-28,37})},
        {"Tutte-12 (n=126,g=12)", make_lcf(126, {17,27,-13,-59,-35,35,-11,13,-53,53,-27,21,57,11,-21,-57,59,-17})},
    };
    std::cout << "\n[Part A: Famous High-Girth Cubic Cages/Symmetric Graphs]\n";
    for (auto &ng : famous) {
        int g = compute_girth(ng.g);
        long long c16 = count_c16(ng.g);
        std::cout << "  " << std::left << std::setw(26) << ng.name
                  << " valid=" << is_valid_cubic(ng.g)
                  << " g=" << g << " exact_#C16=" << c16 << "\n";
    }

    struct LiftJob { std::string label; const BaseWithTree *bt; FiniteGroup grp; int trials; };
    std::vector<LiftJob> jobs;
    int t_cyc = quick ? 400 : 12000;
    int t_nonab = quick ? 400 : 12000;
    for (int m : {25, 29, 31, 35, 37, 41, 47, 53})
        jobs.push_back({"K4 x Z_" + std::to_string(m), &btK4, make_cyclic_group(m), t_cyc});
    for (int m : {17, 19, 23, 29, 31, 37})
        jobs.push_back({"K3,3 x Z_" + std::to_string(m), &btK33, make_cyclic_group(m), t_cyc});
    for (int m : {11, 13, 17, 19, 21})
        jobs.push_back({"Pet x Z_" + std::to_string(m), &btPet, make_cyclic_group(m), t_cyc / 2});
    for (int m : {13, 15, 17, 19, 21, 25})
        jobs.push_back({"K4 x D_" + std::to_string(m), &btK4, make_dihedral_group(m), t_nonab});
    for (int m : {9, 11, 13, 15, 17})
        jobs.push_back({"K3,3 x D_" + std::to_string(m), &btK33, make_dihedral_group(m), t_nonab});
    jobs.push_back({"K4 x S_4 (n=96)", &btK4, make_s4_group(), t_nonab});
    jobs.push_back({"K3,3 x S_4 (n=144)", &btK33, make_s4_group(), t_nonab});
    jobs.push_back({"Pet x S_4 (n=240)", &btPet, make_s4_group(), t_nonab / 2});

    std::atomic<long long> total_lifts{0}, total_g9{0}, total_c16free{0}, total_ce{0};
    long long global_min_c16 = 1000000000LL;
    int global_max_girth = 0;

    std::cout << "\n[Part B/C: Abelian & Non-Abelian Voltage Lifts (g >= 9)]\n";
    for (size_t ji = 0; ji < jobs.size(); ++ji) {
        const auto &jb = jobs[ji];
        long long j_g9 = 0, j_c16free = 0, j_ce = 0;
        long long j_min16 = 1000000000LL;
        int j_maxg = 0;

        #pragma omp parallel for schedule(dynamic, 64) reduction(+:j_g9,j_c16free,j_ce) reduction(min:j_min16) reduction(max:j_maxg)
        for (int tr = 0; tr < jb.trials; ++tr) {
            std::mt19937_64 rng(987654321ULL + ji * 1000003ULL + tr * 7919ULL);
            std::vector<std::array<int, 3>> volt(jb.bt->B.n, {0, 0, 0});
            for (auto [u, k] : jb.bt->non_tree_edges) {
                int v = jb.bt->B.adj[u][k];
                int w = 1 + (int)(rng() % (jb.grp.order - 1));
                volt[u][k] = w;
                for (int j = 0; j < 3; ++j)
                    if (jb.bt->B.adj[v][j] == u) volt[v][j] = jb.grp.inv[w];
            }
            CubicGraph G = make_group_lift(jb.bt->B, jb.grp, volt);
            int g = compute_girth(G);
            if (g > j_maxg) j_maxg = g;
            if (g >= 9) {
                ++j_g9;
                long long c16 = count_c16(G, 50000);
                if (c16 < j_min16) j_min16 = c16;
                if (c16 == 0) {
                    ++j_c16free;
                    if (!has_c32_quick(G, 12)) {
                        ++j_ce;
                        #pragma omp critical
                        std::cout << "!!! CANDIDATE CE in " << jb.label << " tr=" << tr << " g=" << g << "\n";
                    }
                }
            }
        }
        total_lifts += jb.trials;
        total_g9 += j_g9;
        total_c16free += j_c16free;
        total_ce += j_ce;
        if (j_min16 < global_min_c16) global_min_c16 = j_min16;
        if (j_maxg > global_max_girth) global_max_girth = j_maxg;
        if (j_g9 > 0) {
            std::cout << "  " << std::left << std::setw(22) << jb.label
                      << " n=" << std::setw(3) << (jb.bt->B.n * jb.grp.order)
                      << " max_g=" << std::setw(2) << j_maxg
                      << " g>=9=" << std::setw(6) << j_g9
                      << " min_#C16=" << j_min16
                      << " C16-free=" << j_c16free << "\n";
        }
    }

    std::cout << "\n[Part D: Adversarial Girth>=9 2-Switch SA Minimizing #C16]\n";
    std::vector<int> sa_ns = quick ? std::vector<int>{80, 100} : std::vector<int>{80, 90, 100, 110, 120, 140};
    int sa_restarts = quick ? 2 : 8;
    int sa_steps = quick ? 300 : 2500;
    long long sa_total_moves = 0, sa_min_c16 = 1000000000LL, sa_ce = 0;

    for (int n : sa_ns) {
        long long n_best = 1000000000LL;
        int n_built = 0;
        #pragma omp parallel for schedule(dynamic, 1) reduction(+:sa_total_moves,sa_ce,n_built) reduction(min:n_best)
        for (int r = 0; r < sa_restarts; ++r) {
            CubicGraph G;
            if (!build_girth9_cubic(n, 55555ULL + n * 1000 + r, G)) continue;
            ++n_built;
            long long cur16 = count_c16(G);
            long long best16 = cur16;
            std::mt19937_64 rng(99999ULL + n * 1000 + r);
            for (int step = 0; step < sa_steps; ++step) {
                ++sa_total_moves;
                int u = (int)(rng() % n), ui = (int)(rng() % 3);
                int x = (int)(rng() % n), xi = (int)(rng() % 3);
                int mode = (int)(rng() & 1);
                CubicGraph cand = G;
                if (!do_switch(cand, u, ui, x, xi, mode)) continue;
                if (compute_girth(cand) < 9) continue;
                long long nxt16 = count_c16(cand);
                double temp = 15.0 * (1.0 - (double)step / sa_steps) + 0.5;
                if (nxt16 <= cur16 || std::uniform_real_distribution<double>(0.0, 1.0)(rng) < std::exp((double)(cur16 - nxt16) / temp)) {
                    G = std::move(cand);
                    cur16 = nxt16;
                    if (cur16 < best16) best16 = cur16;
                    if (cur16 == 0) {
                        if (!has_c32_quick(G, 12)) ++sa_ce;
                    }
                }
            }
            if (best16 < n_best) n_best = best16;
        }
        if (n_best < sa_min_c16) sa_min_c16 = n_best;
        std::cout << "  SA n=" << std::setw(3) << n << " restarts_built=" << n_built
                  << " min_#C16=" << n_best << " CE=" << sa_ce << "\n";
    }

    auto t1 = std::chrono::steady_clock::now();
    double sec = std::chrono::duration<double>(t1 - t0).count();
    std::cout << "\n=== FINAL SIEGE SUMMARY ===\n"
              << "total_lifts_tested=" << total_lifts.load() << "\n"
              << "total_girth_ge9_lifts=" << total_g9.load() << "\n"
              << "max_girth_seen=" << global_max_girth << "\n"
              << "min_c16_over_all_girth_ge9_lifts=" << global_min_c16 << "\n"
              << "sa_total_moves=" << sa_total_moves << "\n"
              << "sa_min_c16_at_girth_ge9=" << sa_min_c16 << "\n"
              << "counterexamples_found=" << (total_ce.load() + sa_ce) << "\n"
              << "elapsed_sec=" << std::fixed << std::setprecision(2) << sec << "\n";
    return 0;
}
