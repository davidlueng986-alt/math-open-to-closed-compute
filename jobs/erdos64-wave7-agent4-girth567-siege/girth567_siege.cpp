#include <iostream>
#include <fstream>
#include <vector>
#include <array>
#include <set>
#include <algorithm>
#include <numeric>
#include <random>
#include <cstring>
#include <cmath>
#include <map>
#include <omp.h>

using namespace std;

struct CubicRes {
    int n, graphs_found;
    long long matchings_tested;
    long long c8_chorded_only_hits;
    int counterexamples;
};

CubicRes audit_girth5_cubic(int n, int num_graphs, int max_M_per_graph, int seed_base) {
    CubicRes res{n, 0, 0, 0, 0};
    int found_g = 0;
    long long tot_M = 0, tot_c8_chorded = 0;
    int tot_cex = 0;

    #pragma omp parallel for schedule(dynamic) reduction(+:found_g,tot_M,tot_c8_chorded,tot_cex)
    for (int gidx = 0; gidx < num_graphs; ++gidx) {
        mt19937 rng(seed_base + gidx * 7919);
        bool has[44][44];
        int adj[44][3];
        auto rebuild = [&]() {
            for (int i = 0; i < n; ++i) {
                int c = 0;
                for (int j = 0; j < n; ++j) if (has[i][j]) adj[i][c++] = j;
            }
        };
        auto count_c3_c4 = [&]() {
            int c3 = 0, c4 = 0;
            for (int u = 0; u < n; ++u)
                for (int i = 0; i < 3; ++i) {
                    int v = adj[u][i];
                    if (v > u)
                        for (int j = 0; j < 3; ++j) {
                            int w = adj[v][j];
                            if (w > v && has[u][w]) ++c3;
                        }
                }
            for (int u = 0; u < n; ++u)
                for (int w = u + 1; w < n; ++w) {
                    int cn = 0;
                    for (int i = 0; i < 3; ++i) if (has[adj[u][i]][w]) ++cn;
                    c4 += cn * (cn - 1) / 2;
                }
            return 10 * c3 + c4 / 2;
        };

        bool got = false;
        for (int restart = 0; restart < 20 && !got; ++restart) {
            bool ok = false;
            for (int tr = 0; tr < 300; ++tr) {
                memset(has, 0, sizeof(has));
                vector<int> stubs;
                for (int i = 0; i < n; ++i) for (int k = 0; k < 3; ++k) stubs.push_back(i);
                shuffle(stubs.begin(), stubs.end(), rng);
                ok = true;
                for (size_t i = 0; i < stubs.size(); i += 2) {
                    int u = stubs[i], v = stubs[i+1];
                    if (u == v || has[u][v]) { ok = false; break; }
                    has[u][v] = has[v][u] = true;
                }
                if (ok) break;
            }
            if (!ok) continue;
            rebuild();
            int cost = count_c3_c4();
            if (cost == 0) { got = true; break; }
            vector<pair<int,int>> es;
            for (int step = 0; step < 2500; ++step) {
                es.clear();
                for (int i = 0; i < n; ++i) for (int j = i + 1; j < n; ++j) if (has[i][j]) es.push_back({i, j});
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
                int ncost = count_c3_c4();
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
        auto find_min_mchordless = [&]() -> int {
            for (int target : {8, 16, 32}) {
                if (target > n) break;
                bool vis[44] = {false}, in_c[44] = {false};
                int path[44];
                bool found = false;
                auto dfs = [&](auto& self, int s, int u, int len) -> void {
                    if (found) return;
                    for (int k = 0; k < 3; ++k) {
                        int w = adj[u][k];
                        if (w == s && len == target) {
                            if (path[1] < u) {
                                bool ok = true;
                                for (int i = 0; i < len; ++i) {
                                    int mx = mate[path[i]];
                                    if (in_c[mx] && mx != path[(i+1)%len] && mx != path[(i-1+len)%len]) {
                                        ok = false; break;
                                    }
                                }
                                if (ok) { found = true; return; }
                            }
                        } else if (w > s && !vis[w] && len < target) {
                            int mw = mate[w];
                            if (in_c[mw] && mw != u && !(mw == s && len == target - 1)) continue;
                            vis[w] = true; in_c[w] = true; path[len] = w;
                            self(self, s, w, len + 1);
                            in_c[w] = false; vis[w] = false;
                            if (found) return;
                        }
                    }
                };
                for (int s = 0; s < n && !found; ++s) {
                    vis[s] = true; in_c[s] = true; path[0] = s;
                    for (int k = 0; k < 3 && !found; ++k) {
                        int v1 = adj[s][k];
                        if (v1 > s) { vis[v1]=true; in_c[v1]=true; path[1]=v1; dfs(dfs, s, v1, 2); in_c[v1]=false; vis[v1]=false; }
                    }
                    in_c[s] = false; vis[s] = false;
                }
                if (found) return target;
            }
            return 0;
        };

        auto bt = [&](auto& self) -> void {
            if (tested >= max_M_per_graph) return;
            int u = -1;
            for (int i = 0; i < n; ++i) if (mate[i] == -1) { u = i; break; }
            if (u == -1) {
                ++tested;
                ++tot_M;
                int L = find_min_mchordless();
                if (L > 8) ++tot_c8_chorded;
                if (L == 0) {
                    ++tot_cex;
                    #pragma omp critical
                    cout << "!!! GIRTH-5 CUBIC TS-EG COUNTEREXAMPLE n=" << n << " !!!\n" << flush;
                }
                return;
            }
            for (int k = 0; k < 3; ++k) {
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
    res.c8_chorded_only_hits = tot_c8_chorded;
    res.counterexamples = tot_cex;
    cout << "[TrackA Girth5-Cubic n=" << n << "] graphs=" << found_g
         << " matchings=" << tot_M << " c8_all_chorded=" << tot_c8_chorded
         << " CEX=" << tot_cex << "\n" << flush;
    return res;
}

struct BalRes {
    string name;
    int n, restarts, girth5_hits, best_short, bc8, bc16, bc32, cex;
};

BalRes hunt_balanced_omp(int cyc_len, int num_cycs, int restarts, int steps, int seed_base) {
    int n = cyc_len * num_cycs;
    string nm = to_string(num_cycs) + "xC" + to_string(cyc_len);
    vector<vector<int>> c0(num_cycs);
    for (int i = 0; i < num_cycs; ++i)
        for (int j = 0; j < cyc_len; ++j) c0[i].push_back(i * cyc_len + j);

    int g5_hits = 0, gbest = 1e9, gbc8 = 0, gbc16 = 0, gbc32 = 0, gcex = 0;

    #pragma omp parallel for schedule(dynamic) reduction(+:g5_hits,gcex)
    for (int r = 0; r < restarts; ++r) {
        mt19937 rng(seed_base + r * 9973);
        vector<int> perm(n);
        iota(perm.begin(), perm.end(), 0);
        int adj0[64][2], adj1[64][2];
        bool has[64][64];

        auto build = [&](const vector<int>& p) -> bool {
            memset(has, 0, sizeof(has));
            for (auto& cyc : c0) for (int i = 0; i < cyc_len; ++i) {
                int u = cyc[i], v = cyc[(i+1)%cyc_len], w = cyc[(i-1+cyc_len)%cyc_len];
                adj0[u][0] = v; adj0[u][1] = w;
                has[u][v] = has[v][u] = true;
            }
            for (int ci = 0; ci < num_cycs; ++ci) for (int j = 0; j < cyc_len; ++j) {
                int u = p[ci * cyc_len + j];
                int v = p[ci * cyc_len + (j+1)%cyc_len];
                int w = p[ci * cyc_len + (j-1+cyc_len)%cyc_len];
                if (u == v || has[u][v]) return false;
                adj1[u][0] = v; adj1[u][1] = w;
                has[u][v] = has[v][u] = true;
            }
            return true;
        };
        auto bad_girth = [&]() {
            int c3 = 0, c4 = 0;
            int adj[64][4];
            for (int u = 0; u < n; ++u) {
                adj[u][0]=adj0[u][0]; adj[u][1]=adj0[u][1]; adj[u][2]=adj1[u][0]; adj[u][3]=adj1[u][1];
            }
            for (int u = 0; u < n; ++u) for (int i = 0; i < 4; ++i) {
                int v = adj[u][i];
                if (v > u) for (int j = 0; j < 4; ++j) {
                    int w = adj[v][j];
                    if (w > v && has[u][w]) ++c3;
                }
            }
            for (int u = 0; u < n; ++u) for (int w = u+1; w < n; ++w) {
                int cn = 0;
                for (int i = 0; i < 4; ++i) if (has[adj[u][i]][w]) ++cn;
                c4 += cn * (cn - 1) / 2;
            }
            return 10 * c3 + c4 / 2;
        };
        auto count_pow2 = [&](int lcap, int cap, int& c8, int& c16, int& c32) {
            c8 = c16 = c32 = 0; int tot = 0;
            bool vis[64] = {false}; int path[64];
            auto dfs = [&](auto& self, int s, int u, int lc, int fc, int len, int csw) -> void {
                if (tot >= cap) return;
                for (int col = 0; col < 2; ++col) {
                    const int* nb = (col == 0) ? adj0[u] : adj1[u];
                    int asw = (col != lc) ? 1 : 0;
                    for (int k = 0; k < 2; ++k) {
                        int w = nb[k];
                        if (w == s && len >= 4) {
                            if (len % 2 == 0 && path[1] < u) {
                                int L = len + csw + asw + ((col != fc) ? 1 : 0);
                                if (L == 8) { ++c8; ++tot; }
                                else if (L == 16) { ++c16; ++tot; }
                                else if (L == 32) { ++c32; ++tot; }
                                else if (L == 64) { ++tot; }
                            }
                        } else if (w > s && !vis[w] && len < lcap) {
                            vis[w] = true; path[len] = w;
                            self(self, s, w, col, fc, len + 1, csw + asw);
                            vis[w] = false;
                            if (tot >= cap) return;
                        }
                    }
                }
            };
            for (int s = 0; s < n && tot < cap; ++s) {
                vis[s] = true; path[0] = s;
                for (int col = 0; col < 2 && tot < cap; ++col) {
                    const int* nb = (col == 0) ? adj0[s] : adj1[s];
                    for (int k = 0; k < 2 && tot < cap; ++k) {
                        int v1 = nb[k];
                        if (v1 > s) { vis[v1]=true; path[1]=v1; dfs(dfs, s, v1, col, col, 2, 0); vis[v1]=false; }
                    }
                }
                vis[s] = false;
            }
            return tot;
        };

        bool ok = false;
        for (int tr = 0; tr < 500; ++tr) {
            shuffle(perm.begin(), perm.end(), rng);
            if (build(perm)) { ok = true; break; }
        }
        if (!ok) continue;
        int bg = bad_girth();
        int c8 = 0, c16 = 0, c32 = 0;
        int lcap = min(n, 14);
        int tot = (bg == 0) ? count_pow2(lcap, 200, c8, c16, c32) : 200;
        int cost = 1000 * bg + 50 * c8 + 5 * c16 + c32;
        bool ever_g5 = (bg == 0);
        int lbest = (bg == 0) ? tot : 1e9, lb8 = c8, lb16 = c16, lb32 = c32;

        for (int st = 0; st < steps; ++st) {
            int i = rng() % n, j = rng() % n;
            if (i == j) continue;
            swap(perm[i], perm[j]);
            if (!build(perm)) { swap(perm[i], perm[j]); continue; }
            int nbg = bad_girth();
            int nc8 = 0, nc16 = 0, nc32 = 0, ntot = 200;
            if (nbg == 0) ntot = count_pow2(lcap, 200, nc8, nc16, nc32);
            int ncost = 1000 * nbg + 50 * nc8 + 5 * nc16 + nc32;
            double T = 10.0 * pow(0.01, (double)st / steps);
            if (ncost <= cost || uniform_real_distribution<double>(0,1)(rng) < exp((cost - ncost)/T)) {
                cost = ncost; bg = nbg; tot = ntot; c8 = nc8; c16 = nc16; c32 = nc32;
                if (bg == 0) {
                    ever_g5 = true;
                    if (tot < lbest) { lbest = tot; lb8 = c8; lb16 = c16; lb32 = c32; }
                    if (tot == 0) {
                        int fc8, fc16, fc32;
                        if (count_pow2(n, 1, fc8, fc16, fc32) == 0) {
                            ++gcex;
                            #pragma omp critical
                            cout << "!!! BALANCED CEX " << nm << " n=" << n << " !!!\n" << flush;
                        }
                    }
                }
            } else {
                swap(perm[i], perm[j]);
                build(perm);
            }
        }
        if (ever_g5) ++g5_hits;
        #pragma omp critical
        {
            if (lbest < gbest) { gbest = lbest; gbc8 = lb8; gbc16 = lb16; gbc32 = lb32; }
        }
    }
    cout << "[TrackB Balanced " << nm << " n=" << n << "] g5_hits=" << g5_hits << "/" << restarts
         << " best_short=" << gbest << " (c8=" << gbc8 << ",c16=" << gbc16 << ",c32=" << gbc32
         << ") CEX=" << gcex << "\n" << flush;
    return {nm, n, restarts, g5_hits, gbest, gbc8, gbc16, gbc32, gcex};
}

int main(int argc, char** argv) {
    string out_json = (argc > 1) ? argv[1] : "openmp_siege.json";
    cout << "=== Wave 7 Agent #4 OpenMP Girth-5/6/7 Siege (threads=" << omp_get_max_threads() << ") ===\n" << flush;

    vector<CubicRes> cres;
    for (int n : {20, 22, 24, 26, 28, 30, 32, 34, 36}) {
        cres.push_back(audit_girth5_cubic(n, 20, 400, 70000 + n * 100));
    }
    vector<BalRes> bres;
    bres.push_back(hunt_balanced_omp(5, 5, 16, 2000, 1100));
    bres.push_back(hunt_balanced_omp(5, 6, 16, 2000, 1200));
    bres.push_back(hunt_balanced_omp(5, 7, 16, 1500, 1300));
    bres.push_back(hunt_balanced_omp(6, 5, 16, 2000, 1400));
    bres.push_back(hunt_balanced_omp(6, 6, 16, 1500, 1500));

    ofstream jf(out_json);
    jf << "{\n  \"track_a_girth5_cubic\": [\n";
    for (size_t i = 0; i < cres.size(); ++i) {
        auto& r = cres[i];
        jf << "    {\"n\": " << r.n << ", \"graphs_found\": " << r.graphs_found
           << ", \"matchings_tested\": " << r.matchings_tested
           << ", \"c8_all_chorded_hits\": " << r.c8_chorded_only_hits
           << ", \"counterexamples\": " << r.counterexamples << "}"
           << (i + 1 < cres.size() ? "," : "") << "\n";
    }
    jf << "  ],\n  \"track_b_balanced_c5c6\": [\n";
    for (size_t i = 0; i < bres.size(); ++i) {
        auto& r = bres[i];
        jf << "    {\"name\": \"" << r.name << "\", \"n\": " << r.n
           << ", \"restarts\": " << r.restarts << ", \"girth5_hits\": " << r.girth5_hits
           << ", \"best_short\": " << r.best_short << ", \"c8\": " << r.bc8
           << ", \"c16\": " << r.bc16 << ", \"c32\": " << r.bc32
           << ", \"counterexamples\": " << r.cex << "}"
           << (i + 1 < bres.size() ? "," : "") << "\n";
    }
    jf << "  ]\n}\n";
    return 0;
}
