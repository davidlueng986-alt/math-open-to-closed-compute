#include <iostream>
#include <fstream>
#include <vector>
#include <array>
#include <set>
#include <string>
#include <algorithm>
#include <numeric>
#include <random>
#include <cstring>
#include <cmath>
#include <chrono>
#include <omp.h>

using namespace std;

// Wave 6 Agent #2 — Adversarial OpenMP C++20 Siege on TS-EG
// (4-Regular Transition-System Power-Lifting Conjecture)

static const int PAIR_TABLE[4][4] = {
    {-1, 0, 1, 2},
    { 0,-1, 2, 1},
    { 1, 2,-1, 0},
    { 2, 1, 0,-1}
};

static inline bool is_pow2_ge4(int x) {
    return x >= 4 && (x & (x - 1)) == 0;
}

struct FixedGraph {
    string name;
    int n;
    int girth;
    vector<vector<int>> adj;
    vector<vector<int>> nbr_pos;

    int compute_girth() const {
        int best = 1e9;
        for (int s = 0; s < n; ++s) {
            vector<int> dist(n, -1), par(n, -1);
            vector<int> q;
            q.push_back(s); dist[s] = 0;
            for (size_t head = 0; head < q.size(); ++head) {
                int u = q[head];
                if (2 * dist[u] + 1 >= best) break;
                for (int w : adj[u]) {
                    if (dist[w] == -1) {
                        dist[w] = dist[u] + 1; par[w] = u; q.push_back(w);
                    } else if (par[u] != w) {
                        best = min(best, dist[u] + dist[w] + 1);
                    }
                }
            }
        }
        return best;
    }

    void init(string nm, int N, const vector<pair<int,int>>& edges) {
        name = nm; n = N;
        adj.assign(n, {});
        for (auto [u, v] : edges) {
            adj[u].push_back(v);
            adj[v].push_back(u);
        }
        for (int v = 0; v < n; ++v) {
            sort(adj[v].begin(), adj[v].end());
            adj[v].erase(unique(adj[v].begin(), adj[v].end()), adj[v].end());
            if ((int)adj[v].size() != 4) {
                cerr << "ERROR: " << name << " vertex " << v << " deg=" << adj[v].size() << "\n";
                exit(1);
            }
        }
        nbr_pos.assign(n, vector<int>(n, -1));
        for (int v = 0; v < n; ++v)
            for (int i = 0; i < 4; ++i)
                nbr_pos[v][adj[v][i]] = i;
        girth = compute_girth();
    }

    int count_bad(const vector<int>& p, int len_cap, int cap, int& c4, int& c8, int& c16, int& c32) const {
        c4 = c8 = c16 = c32 = 0;
        int sw[64][4][4];
        for (int v = 0; v < n; ++v)
            for (int i = 0; i < 4; ++i)
                for (int j = 0; j < 4; ++j)
                    sw[v][i][j] = (i == j) ? 0 : (PAIR_TABLE[i][j] == p[v] ? 0 : 1);

        bool vis[64] = {false};
        int path[64];
        int tot = 0;
        int lcap = min(len_cap, n);

        auto dfs = [&](auto& self, int start, int u, int prev_idx, int len, int cur_sw, int first_idx) -> void {
            if (tot >= cap) return;
            for (int iw = 0; iw < 4; ++iw) {
                int w = adj[u][iw];
                if (w == start && len >= 3) {
                    if (path[1] < u) {
                        int L = len + cur_sw + sw[u][prev_idx][iw] + sw[start][nbr_pos[start][u]][first_idx];
                        if (L == 4) { ++c4; ++tot; }
                        else if (L == 8) { ++c8; ++tot; }
                        else if (L == 16) { ++c16; ++tot; }
                        else if (L == 32) { ++c32; ++tot; }
                        else if (L == 64) { ++tot; }
                    }
                } else if (w > start && !vis[w] && len < lcap) {
                    vis[w] = true;
                    path[len] = w;
                    self(self, start, w, nbr_pos[w][u], len + 1, cur_sw + sw[u][prev_idx][iw], first_idx);
                    vis[w] = false;
                    if (tot >= cap) return;
                }
            }
        };

        for (int s = 0; s < n && tot < cap; ++s) {
            vis[s] = true; path[0] = s;
            for (int i1 = 0; i1 < 4 && tot < cap; ++i1) {
                int v1 = adj[s][i1];
                if (v1 > s) {
                    vis[v1] = true; path[1] = v1;
                    dfs(dfs, s, v1, nbr_pos[v1][s], 2, 0, i1);
                    vis[v1] = false;
                }
            }
            vis[s] = false;
        }
        return tot;
    }

    bool has_any_pow2(const vector<int>& p, int& witness_L, int& witness_s) const {
        int c4, c8, c16, c32;
        int stages[] = {8, 12, 16, 20, n};
        for (int st : stages) {
            if (st > n) st = n;
            int tot = count_bad(p, st, 1, c4, c8, c16, c32);
            if (tot > 0) {
                witness_L = c4 ? 4 : (c8 ? 8 : (c16 ? 16 : (c32 ? 32 : 64)));
                witness_s = st;
                return true;
            }
            if (st == n) break;
        }
        return false;
    }
};

struct FixedResult {
    string name;
    int n, girth, len_cap;
    long long moves;
    int best_short_tot, bc4, bc8, bc16, bc32;
    int zero_short_hits;
    int full_counterexamples;
};

FixedResult attack_fixed_graph(const FixedGraph& G, int len_cap, int restarts, int steps, int seed_base) {
    FixedResult res{G.name, G.n, G.girth, len_cap, (long long)restarts * steps, 1000000000, 0, 0, 0, 0, 0, 0};
    int global_best = 1000000000;
    int gb4 = 0, gb8 = 0, gb16 = 0, gb32 = 0;
    int zero_short = 0, full_cex = 0;

    #pragma omp parallel for schedule(dynamic) reduction(+:zero_short,full_cex)
    for (int r = 0; r < restarts; ++r) {
        mt19937 rng(seed_base + r * 9973);
        vector<int> p(G.n);
        for (int i = 0; i < G.n; ++i) p[i] = rng() % 3;
        int c4, c8, c16, c32;
        int tot = G.count_bad(p, len_cap, 2000, c4, c8, c16, c32);
        int cost = 100 * c4 + 15 * c8 + 2 * c16 + c32;

        int local_best = tot, lb4 = c4, lb8 = c8, lb16 = c16, lb32 = c32;
        if (tot == 0) {
            ++zero_short;
            int wL = 0, ws = 0;
            if (!G.has_any_pow2(p, wL, ws)) {
                ++full_cex;
                #pragma omp critical
                {
                    cout << "!!! FULL COUNTEREXAMPLE ON " << G.name << " (n=" << G.n << ") !!! p=";
                    for (int x : p) cout << x;
                    cout << "\n" << flush;
                }
            }
        }

        for (int st = 0; st < steps; ++st) {
            int v = rng() % G.n;
            int old = p[v];
            p[v] = (old + 1 + (rng() & 1)) % 3;
            int nc4, nc8, nc16, nc32;
            int ntot = G.count_bad(p, len_cap, max(tot + 40, 150), nc4, nc8, nc16, nc32);
            int ncost = 100 * nc4 + 15 * nc8 + 2 * nc16 + nc32;
            double T = 3.0 * pow(0.015, (double)st / steps);
            if (ncost <= cost || uniform_real_distribution<double>(0, 1)(rng) < exp((cost - ncost) / T)) {
                cost = ncost; tot = ntot; c4 = nc4; c8 = nc8; c16 = nc16; c32 = nc32;
                if (tot < local_best) {
                    local_best = tot; lb4 = c4; lb8 = c8; lb16 = c16; lb32 = c32;
                    if (tot == 0) {
                        ++zero_short;
                        int wL = 0, ws = 0;
                        if (!G.has_any_pow2(p, wL, ws)) {
                            ++full_cex;
                            #pragma omp critical
                            {
                                cout << "!!! FULL COUNTEREXAMPLE ON " << G.name << " (n=" << G.n << ") !!! p=";
                                for (int x : p) cout << x;
                                cout << "\n" << flush;
                            }
                        }
                    }
                }
            } else {
                p[v] = old;
            }
        }
        #pragma omp critical
        {
            if (local_best < global_best) {
                global_best = local_best; gb4 = lb4; gb8 = lb8; gb16 = lb16; gb32 = lb32;
            }
        }
    }
    res.best_short_tot = global_best;
    res.bc4 = gb4; res.bc8 = gb8; res.bc16 = gb16; res.bc32 = gb32;
    res.zero_short_hits = zero_short;
    res.full_counterexamples = full_cex;
    cout << "[Fixed " << res.name << " n=" << res.n << " g=" << res.girth << " cap=" << len_cap
         << "] moves=" << res.moves << " best_short=" << res.best_short_tot
         << " (c4=" << res.bc4 << ",c8=" << res.bc8 << ",c16=" << res.bc16 << ",c32=" << res.bc32
         << ") zero_short_hits=" << res.zero_short_hits << " FULL_CEX=" << res.full_counterexamples << "\n" << flush;
    return res;
}

FixedGraph make_circulant(int n, int j1, int j2) {
    set<pair<int,int>> es;
    for (int i = 0; i < n; ++i) {
        for (int j : {j1, j2}) {
            int w = (i + j) % n;
            es.insert({min(i, w), max(i, w)});
        }
    }
    FixedGraph G;
    G.init("C" + to_string(n) + "(" + to_string(j1) + "," + to_string(j2) + ")", n, vector<pair<int,int>>(es.begin(), es.end()));
    return G;
}

FixedGraph make_line_graph(string nm, int n0, const vector<pair<int,int>>& e0) {
    (void)n0;
    set<pair<int,int>> es;
    for (auto [u, v] : e0) es.insert({min(u, v), max(u, v)});
    vector<pair<int,int>> me(es.begin(), es.end());
    vector<pair<int,int>> le;
    for (int i = 0; i < (int)me.size(); ++i)
        for (int j = i + 1; j < (int)me.size(); ++j)
            if (me[i].first == me[j].first || me[i].first == me[j].second ||
                me[i].second == me[j].first || me[i].second == me[j].second)
                le.push_back({i, j});
    FixedGraph G;
    G.init(nm, me.size(), le);
    return G;
}

FixedGraph make_pg2_3() {
    vector<array<int,3>> pts;
    for (int x=0;x<3;++x) for (int y=0;y<3;++y) for (int z=0;z<3;++z) {
        if (x==0 && y==0 && z==0) continue;
        int c = x ? x : (y ? y : z);
        int inv = (c == 1) ? 1 : 2;
        array<int,3> nv = {(x*inv)%3, (y*inv)%3, (z*inv)%3};
        if (find(pts.begin(), pts.end(), nv) == pts.end()) pts.push_back(nv);
    }
    vector<pair<int,int>> edges;
    for (int i=0;i<13;++i)
        for (int j=0;j<13;++j)
            if ((pts[i][0]*pts[j][0] + pts[i][1]*pts[j][1] + pts[i][2]*pts[j][2]) % 3 == 0)
                edges.push_back({i, 13 + j});
    FixedGraph G; G.init("PG(2,3)_cage4_6", 26, edges);
    return G;
}

FixedGraph make_q4() {
    vector<pair<int,int>> edges;
    for (int i=0;i<16;++i)
        for (int b=0;b<4;++b)
            if (i < (i ^ (1<<b))) edges.push_back({i, i ^ (1<<b)});
    FixedGraph G; G.init("Q4", 16, edges);
    return G;
}

bool make_high_girth_4reg(int n, int target_girth, bool bipartite, int seed, FixedGraph& out, string nm) {
    mt19937 rng(seed);
    vector<vector<bool>> has(n, vector<bool>(n, false));
    auto count_bad_g = [&](int& c3, int& c4) {
        c3 = 0; c4 = 0;
        vector<vector<int>> adj(n);
        for (int i=0;i<n;++i) for (int j=0;j<n;++j) if (has[i][j]) adj[i].push_back(j);
        if (!bipartite) {
            for (int u=0;u<n;++u)
                for (int v : adj[u]) if (v > u)
                    for (int w : adj[v]) if (w > v && has[u][w]) ++c3;
        }
        if (target_girth >= 5) {
            for (int u=0;u<n;++u)
                for (int w=u+1;w<n;++w) {
                    int common = 0;
                    for (int v : adj[u]) if (has[v][w]) ++common;
                    c4 += common * (common - 1) / 2;
                }
            c4 /= 2;
        }
    };

    for (int restart = 0; restart < 30; ++restart) {
        for (int i=0;i<n;++i) fill(has[i].begin(), has[i].end(), false);
        bool ok = false;
        for (int tries = 0; tries < 500; ++tries) {
            for (int i=0;i<n;++i) fill(has[i].begin(), has[i].end(), false);
            ok = true;
            if (bipartite) {
                int half = n / 2;
                vector<int> L, R;
                for (int i=0;i<half;++i) for (int k=0;k<4;++k) { L.push_back(i); R.push_back(half + i); }
                shuffle(R.begin(), R.end(), rng);
                for (size_t i=0;i<L.size();++i) {
                    if (has[L[i]][R[i]]) { ok = false; break; }
                    has[L[i]][R[i]] = has[R[i]][L[i]] = true;
                }
            } else {
                vector<int> stubs;
                for (int i=0;i<n;++i) for (int k=0;k<4;++k) stubs.push_back(i);
                shuffle(stubs.begin(), stubs.end(), rng);
                for (size_t i=0;i<stubs.size();i+=2) {
                    int u = stubs[i], v = stubs[i+1];
                    if (u == v || has[u][v]) { ok = false; break; }
                    has[u][v] = has[v][u] = true;
                }
            }
            if (ok) break;
        }
        if (!ok) continue;
        int c3, c4; count_bad_g(c3, c4);
        int cost = 10 * c3 + c4;
        if (cost == 0) {
            vector<pair<int,int>> es;
            for (int i=0;i<n;++i) for (int j=i+1;j<n;++j) if (has[i][j]) es.push_back({i, j});
            out.init(nm, n, es);
            if (out.girth >= target_girth) return true;
        }
        vector<pair<int,int>> es;
        for (int step = 0; step < 4000; ++step) {
            es.clear();
            for (int i=0;i<n;++i) for (int j=i+1;j<n;++j) if (has[i][j]) es.push_back({i, j});
            int m = es.size();
            int i1 = rng() % m, i2 = rng() % m;
            if (i1 == i2) continue;
            auto [a, b] = es[i1]; auto [c, d] = es[i2];
            if (a == c || a == d || b == c || b == d) continue;
            if (!bipartite && (rng() & 1)) swap(c, d);
            int u1 = a, v1 = bipartite ? d : c;
            int u2 = bipartite ? c : b, v2 = bipartite ? b : d;
            if (has[u1][v1] || has[u2][v2]) continue;
            has[a][b] = has[b][a] = false;
            has[c][d] = has[d][c] = false;
            has[u1][v1] = has[v1][u1] = true;
            has[u2][v2] = has[v2][u2] = true;
            int nc3, nc4; count_bad_g(nc3, nc4);
            int ncost = 10 * nc3 + nc4;
            if (ncost <= cost || (ncost <= cost + 2 && (rng() % 25 == 0))) {
                cost = ncost;
                if (cost == 0) {
                    vector<pair<int,int>> res_e;
                    for (int i=0;i<n;++i) for (int j=i+1;j<n;++j) if (has[i][j]) res_e.push_back({i, j});
                    out.init(nm, n, res_e);
                    if (out.girth >= target_girth) return true;
                }
            } else {
                has[u1][v1] = has[v1][u1] = false;
                has[u2][v2] = has[v2][u2] = false;
                has[a][b] = has[b][a] = true;
                has[c][d] = has[d][c] = true;
            }
        }
    }
    return false;
}

struct Cubic48Result {
    int n, graphs_found;
    long long matchings_tested;
    int counterexamples;
};

Cubic48Result audit_48_free_cubic(int n, int num_graphs, int max_M_per_graph, int seed_base) {
    Cubic48Result res{n, 0, 0, 0};
    int found_g = 0;
    long long tot_M = 0;
    int tot_cex = 0;

    #pragma omp parallel for schedule(dynamic) reduction(+:found_g,tot_M,tot_cex)
    for (int gidx = 0; gidx < num_graphs; ++gidx) {
        mt19937 rng(seed_base + gidx * 7919);
        bool has[44][44];
        int adj[44][3];
        auto rebuild = [&]() {
            for (int i=0;i<n;++i) {
                int c = 0;
                for (int j=0;j<n;++j) if (has[i][j]) adj[i][c++] = j;
            }
        };
        auto count_len = [&](int L) {
            int cnt = 0; bool vis[44] = {false}; int path[44];
            auto dfs = [&](auto& self, int s, int u, int len) -> void {
                for (int k=0;k<3;++k) {
                    int w = adj[u][k];
                    if (w == s && len == L) { if (path[1] < u) ++cnt; }
                    else if (w > s && !vis[w] && len < L) {
                        vis[w] = true; path[len] = w;
                        self(self, s, w, len + 1);
                        vis[w] = false;
                    }
                }
            };
            for (int s=0;s<n;++s) {
                vis[s] = true; path[0] = s;
                for (int k=0;k<3;++k) {
                    int v1 = adj[s][k];
                    if (v1 > s) { vis[v1] = true; path[1] = v1; dfs(dfs, s, v1, 2); vis[v1] = false; }
                }
                vis[s] = false;
            }
            return cnt;
        };

        bool got = false;
        for (int restart = 0; restart < 25 && !got; ++restart) {
            bool ok = false;
            for (int tr = 0; tr < 300; ++tr) {
                memset(has, 0, sizeof(has));
                vector<int> stubs;
                for (int i=0;i<n;++i) for (int k=0;k<3;++k) stubs.push_back(i);
                shuffle(stubs.begin(), stubs.end(), rng);
                ok = true;
                for (size_t i=0;i<stubs.size();i+=2) {
                    int u = stubs[i], v = stubs[i+1];
                    if (u == v || has[u][v]) { ok = false; break; }
                    has[u][v] = has[v][u] = true;
                }
                if (ok) break;
            }
            if (!ok) continue;
            rebuild();
            int cost = 10 * count_len(3) + 10 * count_len(4) + count_len(8);
            if (cost == 0) { got = true; break; }
            vector<pair<int,int>> es;
            for (int step = 0; step < 3000; ++step) {
                es.clear();
                for (int i=0;i<n;++i) for (int j=i+1;j<n;++j) if (has[i][j]) es.push_back({i, j});
                int m = es.size();
                int i1 = rng() % m, i2 = rng() % m;
                if (i1 == i2) continue;
                auto [a, b] = es[i1]; auto [c, d] = es[i2];
                if (a==c || a==d || b==c || b==d) continue;
                if (rng() & 1) swap(c, d);
                if (has[a][c] || has[b][d]) continue;
                has[a][b] = has[b][a] = false; has[c][d] = has[d][c] = false;
                has[a][c] = has[c][a] = true; has[b][d] = has[d][b] = true;
                rebuild();
                int ncost = 10 * count_len(3) + 10 * count_len(4) + count_len(8);
                if (ncost <= cost || (ncost <= cost + 2 && (rng() % 20 == 0))) {
                    cost = ncost;
                    if (cost == 0) { got = true; break; }
                } else {
                    has[a][c] = has[c][a] = false; has[b][d] = has[d][b] = false;
                    has[a][b] = has[b][a] = true; has[c][d] = has[d][c] = true;
                    rebuild();
                }
            }
        }
        if (!got) continue;
        ++found_g;

        int mate[44]; memset(mate, -1, sizeof(mate));
        int tested = 0;
        auto has_m_chordless = [&]() -> bool {
            bool vis[44] = {false}, in_c[44] = {false};
            int path[44];
            bool found = false;
            auto dfs = [&](auto& self, int s, int u, int len) -> void {
                if (found) return;
                for (int k=0;k<3;++k) {
                    int w = adj[u][k];
                    if (w == s && (len == 16 || len == 32)) {
                        if (path[1] < u) {
                            bool ok = true;
                            for (int i=0;i<len;++i) {
                                int mx = mate[path[i]];
                                if (in_c[mx] && mx != path[(i+1)%len] && mx != path[(i-1+len)%len]) { ok = false; break; }
                            }
                            if (ok) { found = true; return; }
                        }
                    } else if (w > s && !vis[w] && len < 32) {
                        int mw = mate[w];
                        if (in_c[mw] && mw != u && mw != s) continue;
                        vis[w] = true; in_c[w] = true; path[len] = w;
                        self(self, s, w, len + 1);
                        in_c[w] = false; vis[w] = false;
                        if (found) return;
                    }
                }
            };
            for (int s=0;s<n && !found;++s) {
                vis[s] = true; in_c[s] = true; path[0] = s;
                for (int k=0;k<3 && !found;++k) {
                    int v1 = adj[s][k];
                    if (v1 > s) { vis[v1]=true; in_c[v1]=true; path[1]=v1; dfs(dfs, s, v1, 2); in_c[v1]=false; vis[v1]=false; }
                }
                in_c[s] = false; vis[s] = false;
            }
            return found;
        };

        auto bt = [&](auto& self) -> void {
            if (tested >= max_M_per_graph) return;
            int u = -1;
            for (int i=0;i<n;++i) if (mate[i] == -1) { u = i; break; }
            if (u == -1) {
                ++tested;
                ++tot_M;
                if (!has_m_chordless()) {
                    ++tot_cex;
                    #pragma omp critical
                    cout << "!!! {4,8}-FREE CUBIC TS-EG COUNTEREXAMPLE at n=" << n << " !!!\n" << flush;
                }
                return;
            }
            for (int k=0;k<3;++k) {
                int v = adj[u][k];
                if (mate[v] == -1) {
                    mate[u] = v; mate[v] = u;
                    self(self);
                    mate[u] = -1; mate[v] = -1;
                    if (tested >= max_M_per_graph) return;
                }
            }
        };
        bt(bt);
    }
    res.graphs_found = found_g;
    res.matchings_tested = tot_M;
    res.counterexamples = tot_cex;
    cout << "[Track3 48-free cubic n=" << n << "] graphs=" << found_g
         << " matchings_tested=" << tot_M << " CEX=" << tot_cex << "\n" << flush;
    return res;
}

int main(int argc, char** argv) {
    bool smoke = (argc > 1 && string(argv[1]) == "--smoke");
    string out_json = (argc > 2) ? argv[2] : "tseg_siege_results.json";
    int restarts = smoke ? 2 : 16;
    int steps = smoke ? 150 : 2500;

    cout << "=== Wave 6 Agent #2 TS-EG Adversarial OpenMP Siege (threads=" << omp_get_max_threads()
         << ", smoke=" << smoke << ") ===\n" << flush;

    vector<FixedGraph> suite;
    suite.push_back(make_circulant(12, 1, 5));
    suite.push_back(make_circulant(16, 1, 3));
    suite.push_back(make_circulant(20, 1, 3));
    suite.push_back(make_circulant(24, 1, 5));
    suite.push_back(make_circulant(30, 1, 7));
    suite.push_back(make_circulant(40, 1, 9));
    suite.push_back(make_q4());
    suite.push_back(make_pg2_3());
    {
        vector<pair<int,int>> e;
        for (int i=0;i<5;++i) { e.push_back({i,(i+1)%5}); e.push_back({i,i+5}); e.push_back({i+5,((i+2)%5)+5}); }
        suite.push_back(make_line_graph("L(Petersen)", 10, e));
    }
    {
        vector<pair<int,int>> e;
        for (int i=0;i<14;++i) { e.push_back({i,(i+1)%14}); if (i%2==0) e.push_back({i,(i+5)%14}); }
        suite.push_back(make_line_graph("L(Heawood)", 14, e));
    }
    {
        vector<pair<int,int>> e;
        for (int i=0;i<8;++i) { e.push_back({i,(i+1)%8}); e.push_back({i,i+8}); e.push_back({i+8,((i+3)%8)+8}); }
        suite.push_back(make_line_graph("L(Moebius-Kantor)", 16, e));
    }
    {
        int sh[6] = {5, 7, -7, 7, -7, -5};
        vector<pair<int,int>> e;
        for (int i=0;i<18;++i) { e.push_back({i,(i+1)%18}); e.push_back({i,(i+sh[i%6]+18)%18}); }
        suite.push_back(make_line_graph("L(Pappus)", 18, e));
    }
    {
        int sh[4] = {5, -5, 9, -9};
        vector<pair<int,int>> e;
        for (int i=0;i<20;++i) { e.push_back({i,(i+1)%20}); e.push_back({i,(i+sh[i%4]+20)%20}); }
        suite.push_back(make_line_graph("L(Desargues)", 20, e));
    }
    {
        vector<pair<int,int>> e;
        for (int i=0;i<24;++i) {
            e.push_back({i,(i+1)%24});
            if (i%3==0) e.push_back({i,(i+12)%24});
            else if (i%3==1) e.push_back({i,(i+7)%24});
        }
        suite.push_back(make_line_graph("L(McGee)", 24, e));
    }
    for (int n : {20, 22, 24, 28}) {
        FixedGraph hg;
        if (make_high_girth_4reg(n, 5, false, 700 + n, hg, "Girth5_4reg_n" + to_string(n)))
            suite.push_back(hg);
    }
    for (int n : {28, 32, 36, 40}) {
        FixedGraph hg;
        if (make_high_girth_4reg(n, 6, true, 900 + n, hg, "Girth6_Bip4reg_n" + to_string(n)))
            suite.push_back(hg);
    }

    vector<FixedResult> fixed_results;
    for (size_t idx = 0; idx < suite.size(); ++idx) {
        const auto& G = suite[idx];
        int cap = (G.n <= 20) ? 12 : ((G.n <= 28) ? 10 : 8);
        fixed_results.push_back(attack_fixed_graph(G, cap, restarts, steps, 10000 + (int)idx * 1000));
    }

    vector<Cubic48Result> c48_results;
    int ng = smoke ? 2 : 24;
    int maxM = smoke ? 30 : 300;
    for (int n : {28, 30, 32, 34, 36}) {
        c48_results.push_back(audit_48_free_cubic(n, ng, maxM, 50000 + n * 100));
    }

    ofstream jf(out_json);
    jf << "{\n  \"smoke\": " << (smoke ? "true" : "false") << ",\n  \"fixed_graph_siege\": [\n";
    for (size_t i = 0; i < fixed_results.size(); ++i) {
        const auto& r = fixed_results[i];
        jf << "    {\"name\": \"" << r.name << "\", \"n\": " << r.n << ", \"girth\": " << r.girth
           << ", \"len_cap\": " << r.len_cap << ", \"moves\": " << r.moves
           << ", \"best_short_tot\": " << r.best_short_tot
           << ", \"c4\": " << r.bc4 << ", \"c8\": " << r.bc8 << ", \"c16\": " << r.bc16 << ", \"c32\": " << r.bc32
           << ", \"zero_short_hits\": " << r.zero_short_hits
           << ", \"full_counterexamples\": " << r.full_counterexamples << "}"
           << (i + 1 < fixed_results.size() ? "," : "") << "\n";
    }
    jf << "  ],\n  \"cubic_48_free_matching_audit\": [\n";
    for (size_t i = 0; i < c48_results.size(); ++i) {
        const auto& r = c48_results[i];
        jf << "    {\"n\": " << r.n << ", \"graphs_found\": " << r.graphs_found
           << ", \"matchings_tested\": " << r.matchings_tested
           << ", \"counterexamples\": " << r.counterexamples << "}"
           << (i + 1 < c48_results.size() ? "," : "") << "\n";
    }
    jf << "  ]\n}\n";
    jf.close();
    cout << "Done! Wrote " << out_json << "\n";
    return 0;
}
