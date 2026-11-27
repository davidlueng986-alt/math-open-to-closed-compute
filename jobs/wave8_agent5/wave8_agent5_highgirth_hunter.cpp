#include <algorithm>
#include <array>
#include <atomic>
#include <chrono>
#include <cstdint>
#include <cstring>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <map>
#include <numeric>
#include <omp.h>
#include <queue>
#include <random>
#include <set>
#include <string>
#include <unordered_map>
#include <vector>

using namespace std;

struct BitSet512 {
    uint64_t w[8] = {0,0,0,0,0,0,0,0};
    inline void set(int i) { w[i >> 6] |= (1ULL << (i & 63)); }
    inline void clear(int i) { w[i >> 6] &= ~(1ULL << (i & 63)); }
    inline bool test(int i) const { return (w[i >> 6] >> (i & 63)) & 1ULL; }
    inline bool disjoint(const BitSet512& o) const {
        return ((w[0] & o.w[0]) | (w[1] & o.w[1]) | (w[2] & o.w[2]) | (w[3] & o.w[3]) |
                (w[4] & o.w[4]) | (w[5] & o.w[5]) | (w[6] & o.w[6]) | (w[7] & o.w[7])) == 0;
    }
};

struct Graph {
    int n = 0;
    vector<array<int, 3>> adj;
    vector<int> deg;
    Graph() = default;
    explicit Graph(int n_) : n(n_), adj(n_, {-1,-1,-1}), deg(n_, 0) {}
    void add_edge(int u, int v) {
        adj[u][deg[u]++] = v;
        adj[v][deg[v]++] = u;
    }
    bool has_edge(int u, int v) const {
        for (int i = 0; i < deg[u]; ++i) if (adj[u][i] == v) return true;
        return false;
    }
};

int girth_from(const Graph& G, int s, int cap = 100) {
    vector<int> dist(G.n, -1), par(G.n, -1);
    queue<int> q;
    dist[s] = 0;
    q.push(s);
    int best = cap;
    while (!q.empty()) {
        int u = q.front(); q.pop();
        if (2 * dist[u] + 1 >= best) break;
        for (int i = 0; i < G.deg[u]; ++i) {
            int v = G.adj[u][i];
            if (dist[v] == -1) {
                dist[v] = dist[u] + 1;
                par[v] = u;
                q.push(v);
            } else if (par[u] != v) {
                best = min(best, dist[u] + dist[v] + 1);
            }
        }
    }
    return best;
}

int graph_girth(const Graph& G, bool vertex_transitive = false) {
    int best = 100;
    int limit = vertex_transitive ? 1 : G.n;
    for (int s = 0; s < limit; ++s) {
        best = min(best, girth_from(G, s, best));
        if (best <= 3) return best;
    }
    return best;
}

long long count_cycles_even(const Graph& G, int L, bool vertex_transitive = false, bool stop_at_first = true) {
    int half = L / 2;
    long long total = 0;
    int u_limit = vertex_transitive ? 1 : G.n;
    for (int u = 0; u < u_limit; ++u) {
        unordered_map<int, vector<BitSet512>> by_end;
        by_end.reserve(512);
        struct Frame { int v; int depth; BitSet512 mask; };
        vector<Frame> st;
        st.reserve(512);
        BitSet512 init; init.set(u);
        st.push_back({u, 0, init});
        while (!st.empty()) {
            Frame cur = st.back(); st.pop_back();
            if (cur.depth == half) {
                BitSet512 inner = cur.mask;
                inner.clear(u);
                inner.clear(cur.v);
                auto& vec = by_end[cur.v];
                for (const auto& om : vec) {
                    if (inner.disjoint(om)) {
                        ++total;
                        if (stop_at_first) return 1;
                    }
                }
                vec.push_back(inner);
                continue;
            }
            for (int i = 0; i < G.deg[cur.v]; ++i) {
                int nxt = G.adj[cur.v][i];
                if (!vertex_transitive && nxt <= u) continue;
                if (vertex_transitive && nxt == u) continue;
                if (!cur.mask.test(nxt)) {
                    BitSet512 nm = cur.mask;
                    nm.set(nxt);
                    st.push_back({nxt, cur.depth + 1, nm});
                }
            }
        }
    }
    return total;
}

struct FiniteGroup {
    string name;
    int order;
    vector<vector<int>> mul;
    vector<int> inv;
};

FiniteGroup make_dihedral(int m) {
    FiniteGroup G;
    G.name = "D_" + to_string(m);
    G.order = 2 * m;
    G.mul.assign(G.order, vector<int>(G.order));
    G.inv.assign(G.order, 0);
    for (int f1 = 0; f1 < 2; ++f1)
      for (int r1 = 0; r1 < m; ++r1) {
        int a = f1 * m + r1;
        for (int f2 = 0; f2 < 2; ++f2)
          for (int r2 = 0; r2 < m; ++r2) {
            int b = f2 * m + r2;
            int nr = (f1 == 0) ? (r1 + r2) % m : (r1 - r2 + m) % m;
            int nf = f1 ^ f2;
            G.mul[a][b] = nf * m + nr;
          }
      }
    for (int a = 0; a < G.order; ++a)
      for (int b = 0; b < G.order; ++b)
        if (G.mul[a][b] == 0) G.inv[a] = b;
    return G;
}

FiniteGroup make_aff(int p, int q, int r) {
    FiniteGroup G;
    G.name = "Aff(" + to_string(p) + "," + to_string(q) + ")";
    G.order = p * q;
    G.mul.assign(G.order, vector<int>(G.order));
    G.inv.assign(G.order, 0);
    vector<int> rp(q, 1);
    for (int i = 1; i < q; ++i) rp[i] = (rp[i-1] * r) % p;
    for (int a1 = 0; a1 < p; ++a1)
      for (int b1 = 0; b1 < q; ++b1) {
        int x = a1 * q + b1;
        for (int a2 = 0; a2 < p; ++a2)
          for (int b2 = 0; b2 < q; ++b2) {
            int y = a2 * q + b2;
            int na = (a1 + rp[b1] * a2) % p;
            int nb = (b1 + b2) % q;
            G.mul[x][y] = na * q + nb;
          }
      }
    for (int a = 0; a < G.order; ++a)
      for (int b = 0; b < G.order; ++b)
        if (G.mul[a][b] == 0) G.inv[a] = b;
    return G;
}

FiniteGroup make_S4() {
    FiniteGroup G;
    G.name = "S_4";
    vector<array<int, 4>> perms;
    array<int, 4> p = {0,1,2,3};
    do { perms.push_back(p); } while (next_permutation(p.begin(), p.end()));
    G.order = (int)perms.size();
    G.mul.assign(G.order, vector<int>(G.order));
    G.inv.assign(G.order, 0);
    map<array<int,4>, int> idx;
    for (int i = 0; i < G.order; ++i) idx[perms[i]] = i;
    for (int i = 0; i < G.order; ++i)
      for (int j = 0; j < G.order; ++j) {
        array<int,4> c;
        for (int k = 0; k < 4; ++k) c[k] = perms[i][perms[j][k]];
        G.mul[i][j] = idx[c];
        if (idx[c] == 0) G.inv[i] = j;
      }
    return G;
}

Graph build_voltage_lift(int base_n, const vector<pair<int,int>>& edges, const FiniteGroup& grp, const vector<int>& volts) {
    int m = grp.order;
    Graph H(base_n * m);
    for (size_t ei = 0; ei < edges.size(); ++ei) {
        int u = edges[ei].first, v = edges[ei].second;
        int w = volts[ei];
        for (int g = 0; g < m; ++g) {
            int ng = grp.mul[g][w];
            H.add_edge(u * m + g, v * m + ng);
        }
    }
    return H;
}

struct Mat2 {
    int a, b, c, d;
    bool operator<(const Mat2& o) const {
        return tie(a,b,c,d) < tie(o.a,o.b,o.c,o.d);
    }
};

FiniteGroup make_PGL2(int p, bool psl_only) {
    auto mod = [p](int x) { x %= p; return x < 0 ? x + p : x; };
    vector<int> invp(p, 0);
    for (int i = 1; i < p; ++i)
      for (int j = 1; j < p; ++j)
        if ((i * j) % p == 1) invp[i] = j;
    vector<bool> is_sq(p, false);
    for (int i = 1; i < p; ++i) is_sq[(i * i) % p] = true;

    auto canon = [&](Mat2 m) {
        int lead = m.a ? m.a : (m.b ? m.b : (m.c ? m.c : m.d));
        int il = invp[lead];
        return Mat2{mod(m.a*il), mod(m.b*il), mod(m.c*il), mod(m.d*il)};
    };
    set<Mat2> elems_set;
    for (int a = 0; a < p; ++a)
      for (int b = 0; b < p; ++b)
        for (int c = 0; c < p; ++c)
          for (int d = 0; d < p; ++d) {
            int det = mod(a*d - b*c);
            if (det == 0) continue;
            if (psl_only && !is_sq[det]) continue;
            elems_set.insert(canon({a,b,c,d}));
          }
    vector<Mat2> elems(elems_set.begin(), elems_set.end());
    for (size_t i = 0; i < elems.size(); ++i) {
        if (elems[i].a==1 && elems[i].b==0 && elems[i].c==0 && elems[i].d==1) {
            swap(elems[0], elems[i]);
            break;
        }
    }
    map<Mat2, int> idx;
    for (size_t i = 0; i < elems.size(); ++i) idx[elems[i]] = (int)i;
    FiniteGroup G;
    G.name = (psl_only ? "PSL(2," : "PGL(2,") + to_string(p) + ")";
    G.order = (int)elems.size();
    G.mul.assign(G.order, vector<int>(G.order));
    G.inv.assign(G.order, 0);
    for (int i = 0; i < G.order; ++i)
      for (int j = 0; j < G.order; ++j) {
        const auto& X = elems[i];
        const auto& Y = elems[j];
        Mat2 Z = canon({mod(X.a*Y.a + X.b*Y.c), mod(X.a*Y.b + X.b*Y.d),
                        mod(X.c*Y.a + X.d*Y.c), mod(X.c*Y.b + X.d*Y.d)});
        int k = idx[Z];
        G.mul[i][j] = k;
        if (k == 0) G.inv[i] = j;
      }
    return G;
}

Graph generate_high_girth_cubic(int n, int target_g, mt19937_64& rng) {
    vector<pair<int,int>> edges;
    while (true) {
        vector<int> stubs(3 * n);
        for (int i = 0; i < n; ++i) stubs[3*i] = stubs[3*i+1] = stubs[3*i+2] = i;
        shuffle(stubs.begin(), stubs.end(), rng);
        edges.clear();
        bool ok = true;
        Graph G(n);
        for (int i = 0; i < 3 * n; i += 2) {
            int u = stubs[i], v = stubs[i+1];
            if (u == v || G.has_edge(u, v)) { ok = false; break; }
            G.add_edge(u, v);
            edges.push_back({u, v});
        }
        if (ok) {
            int cur_g = graph_girth(G);
            int max_steps = 80000;
            for (int step = 0; step < max_steps && cur_g < target_g; ++step) {
                int e1 = (int)(rng() % edges.size());
                int u1 = edges[e1].first, v1 = edges[e1].second;
                auto dist_without = [&](int a, int b, int lim) {
                    vector<int> d(n, -1);
                    queue<int> q;
                    d[a] = 0; q.push(a);
                    while (!q.empty()) {
                        int x = q.front(); q.pop();
                        if (d[x] >= lim) break;
                        for (int k = 0; k < 3; ++k) {
                            int y = G.adj[x][k];
                            if ((x == a && y == b) || (x == b && y == a)) continue;
                            if (y == b) return d[x] + 1;
                            if (d[y] == -1) { d[y] = d[x] + 1; q.push(y); }
                        }
                    }
                    return lim + 1;
                };
                if (dist_without(u1, v1, target_g - 2) >= target_g - 1) continue;
                int e2 = (int)(rng() % edges.size());
                if (e1 == e2) continue;
                int u2 = edges[e2].first, v2 = edges[e2].second;
                if (u1 == u2 || u1 == v2 || v1 == u2 || v1 == v2) continue;
                if (rng() & 1) swap(u2, v2);
                if (G.has_edge(u1, u2) || G.has_edge(v1, v2)) continue;
                auto repl = [&](int x, int old_y, int new_y) {
                    for (int k = 0; k < 3; ++k) if (G.adj[x][k] == old_y) { G.adj[x][k] = new_y; break; }
                };
                repl(u1, v1, u2); repl(u2, v2, u1);
                repl(v1, u1, v2); repl(v2, u2, v1);
                int d1 = dist_without(u1, u2, target_g - 2);
                int d2 = dist_without(v1, v2, target_g - 2);
                if (d1 >= target_g - 1 && d2 >= target_g - 1) {
                    edges[e1] = {u1, u2};
                    edges[e2] = {v1, v2};
                    if (step % 50 == 0) cur_g = graph_girth(G);
                } else {
                    repl(u1, u2, v1); repl(u2, u1, v2);
                    repl(v1, v2, u1); repl(v2, v1, u2);
                }
            }
            if (graph_girth(G) >= target_g) return G;
        }
    }
}

int main(int argc, char** argv) {
    int mode_trials = (argc > 1) ? stoi(argv[1]) : 1200;
    auto t0 = chrono::steady_clock::now();

    cout << "=== WAVE 8 AGENT #5: HIGH-GIRTH (g in [9..14]) ADVERSARIAL COUNTEREXAMPLE HUNTER ===\n";
    cout << "OpenMP max threads: " << omp_get_max_threads() << ", trials_per_family=" << mode_trials << "\n\n";

    vector<pair<int,int>> pet_edges = {
        {0,1},{1,2},{2,3},{3,4},{4,0},
        {5,7},{7,9},{9,6},{6,8},{8,5},
        {0,5},{1,6},{2,7},{3,8},{4,9}
    };
    vector<bool> pet_tree = {1,1,1,1,0, 0,0,0,0,0, 1,1,1,1,1};

    vector<pair<int,int>> hea_edges;
    vector<bool> hea_tree;
    for (int i = 0; i < 14; ++i) {
        int j = (i + 1) % 14;
        hea_edges.push_back({min(i,j), max(i,j)});
        hea_tree.push_back(i < 13);
    }
    for (int i = 0; i < 14; i += 2) {
        int j = (i + 5) % 14;
        hea_edges.push_back({min(i,j), max(i,j)});
        hea_tree.push_back(false);
    }

    vector<FiniteGroup> groups = {
        make_S4(),
        make_dihedral(8), make_dihedral(10), make_dihedral(12), make_dihedral(15),
        make_aff(7, 3, 2), make_aff(13, 3, 3), make_aff(13, 4, 5), make_aff(19, 3, 7)
    };

    long long total_g9 = 0, total_c16_free = 0;
    cout << "--- ENGINE 1: NON-ABELIAN VOLTAGE LIFTS ---\n";
    for (const auto& grp : groups) {
        for (int btype = 0; btype < 2; ++btype) {
            int bn = (btype == 0) ? 10 : 14;
            if (bn * grp.order > 500 || bn * grp.order < 132) continue;
            const auto& bedges = (btype == 0) ? pet_edges : hea_edges;
            const auto& btree = (btype == 0) ? pet_tree : hea_tree;
            string bname = (btype == 0) ? "Petersen" : "Heawood";

            atomic<int> g9_cnt{0}, c16_free_cnt{0}, best_g{0};
            #pragma omp parallel for schedule(dynamic)
            for (int t = 0; t < mode_trials; ++t) {
                mt19937_64 rng(0x9e3779b97f4a7c15ULL ^ (uint64_t)(t * 1000003 + grp.order * 37 + btype * 17));
                vector<int> volts(bedges.size(), 0);
                for (size_t i = 0; i < bedges.size(); ++i)
                    if (!btree[i]) volts[i] = (int)(rng() % grp.order);
                Graph H = build_voltage_lift(bn, bedges, grp, volts);
                int g = graph_girth(H);
                int prev = best_g.load();
                while (g > prev && !best_g.compare_exchange_weak(prev, g)) {}
                if (g >= 9) {
                    ++g9_cnt;
                    if (count_cycles_even(H, 16, false, true) == 0) {
                        ++c16_free_cnt;
                        #pragma omp critical
                        cout << "  [ALERT] C16-FREE FOUND! " << bname << " x " << grp.name << " n=" << H.n << " g=" << g << "\n";
                    }
                }
            }
            total_g9 += g9_cnt.load();
            total_c16_free += c16_free_cnt.load();
            cout << left << setw(10) << bname << " x " << setw(11) << grp.name
                 << " n=" << setw(4) << (bn * grp.order)
                 << " best_g=" << setw(2) << best_g.load()
                 << " g>=9: " << setw(5) << g9_cnt.load() << "/" << mode_trials
                 << " C16-free: " << c16_free_cnt.load() << "\n";
        }
    }

    cout << "\n--- ENGINE 2: NON-ABELIAN CUBIC CAYLEY GRAPHS ---\n";
    vector<FiniteGroup> cay_groups = { make_PGL2(7, true), make_PGL2(7, false) };
    for (const auto& grp : cay_groups) {
        vector<int> invols, non_invols;
        for (int x = 1; x < grp.order; ++x) {
            if (grp.mul[x][x] == 0) invols.push_back(x);
            else if (x < grp.inv[x]) non_invols.push_back(x);
        }
        long long checked = 0, g9 = 0, c16f = 0;
        int best_g = 0;
        #pragma omp parallel for schedule(dynamic) reduction(+:checked,g9,c16f) reduction(max:best_g)
        for (size_t ia = 0; ia < invols.size(); ++ia) {
            int a = invols[ia];
            for (int b : non_invols) {
                int bi = grp.inv[b];
                Graph H(grp.order);
                for (int x = 0; x < grp.order; ++x) {
                    int y1 = grp.mul[x][a], y2 = grp.mul[x][b], y3 = grp.mul[x][bi];
                    if (x < y1) H.add_edge(x, y1);
                    if (x < y2) H.add_edge(x, y2);
                    if (x < y3) H.add_edge(x, y3);
                }
                ++checked;
                int g = graph_girth(H, true);
                if (g > best_g) best_g = g;
                if (g >= 9) {
                    ++g9;
                    if (count_cycles_even(H, 16, true, true) == 0) {
                        ++c16f;
                    }
                }
            }
        }
        total_g9 += g9; total_c16_free += c16f;
        cout << left << setw(12) << grp.name << " n=" << setw(4) << grp.order
             << " (a,b,b^-1) checked=" << setw(6) << checked
             << " best_g=" << setw(2) << best_g
             << " g>=9: " << setw(5) << g9 << " C16-free: " << c16f << "\n";
    }

    cout << "\n--- ENGINE 3: UNSTRUCTURED HIGH-GIRTH (g >= 9) CUBIC GRAPHS ---\n";
    vector<int> ns = {140, 160, 180, 200, 220, 250};
    int per_n = 20;
    for (int n : ns) {
        long long min_c16 = 1e18, max_c16 = 0, c16f = 0;
        #pragma omp parallel for schedule(dynamic) reduction(min:min_c16) reduction(max:max_c16) reduction(+:c16f)
        for (int t = 0; t < per_n; ++t) {
            mt19937_64 rng(0x123456789abcdef0ULL ^ (uint64_t)(n * 997 + t * 31337));
            Graph G = generate_high_girth_cubic(n, 9, rng);
            long long c16 = count_cycles_even(G, 16, false, false);
            if (c16 < min_c16) min_c16 = c16;
            if (c16 > max_c16) max_c16 = c16;
            if (c16 == 0) ++c16f;
        }
        total_g9 += per_n; total_c16_free += c16f;
        cout << "Random cubic n=" << setw(3) << n << " (g>=9): tested=" << setw(3) << per_n
             << " min_C16=" << setw(7) << min_c16 << " max_C16=" << setw(7) << max_c16
             << " C16-free=" << c16f << "\n";
    }

    auto t1 = chrono::steady_clock::now();
    double sec = chrono::duration<double>(t1 - t0).count();
    cout << "\nSUMMARY: total_g>=9_graphs=" << total_g9
         << " total_C16_free=" << total_c16_free
         << " elapsed=" << fixed << setprecision(2) << sec << "s\n";
    return 0;
}
