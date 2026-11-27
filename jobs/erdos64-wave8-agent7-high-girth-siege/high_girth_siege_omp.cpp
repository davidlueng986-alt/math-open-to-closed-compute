#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <map>
#include <numeric>
#include <queue>
#include <random>
#include <string>
#include <vector>
#include <omp.h>

using namespace std;

// Wave 8 Agent #7 — High-Girth (g in {9..14}) Non-Abelian Cayley, Voltage-Lift & Strict Girth>=9 SA Siege
// Targets the EXACT open frontier of Erdős Problem #64:
//   (1) Non-nilpotent even-order cubic Cayley graphs (beyond Burkhart 2026 & n=131 Chebyshev ceiling)
//   (2) Non-abelian K4 cubic voltage lifts (g in {9..14}, n in [96, 1344])
//   (3) Strict girth>=9 (C3=C4=C5=C6=C7=C8=0) cubic SA counterexample hunt at n in [132, 200]

struct Group {
    string name;
    int n;
    vector<vector<int>> mul;
    vector<int> inv;
};

Group build_S_k(int k, bool alternating) {
    vector<vector<int>> perms;
    vector<int> p(k);
    iota(p.begin(), p.end(), 0);
    do {
        if (alternating) {
            int invs = 0;
            for (int i = 0; i < k; ++i)
                for (int j = i + 1; j < k; ++j)
                    if (p[i] > p[j]) invs++;
            if (invs & 1) continue;
        }
        perms.push_back(p);
    } while (next_permutation(p.begin(), p.end()));
    map<vector<int>, int> idx;
    for (int i = 0; i < (int)perms.size(); ++i) idx[perms[i]] = i;
    Group G;
    G.name = (alternating ? "A" : "S") + to_string(k);
    G.n = (int)perms.size();
    G.mul.assign(G.n, vector<int>(G.n));
    G.inv.assign(G.n, 0);
    for (int i = 0; i < G.n; ++i) {
        for (int j = 0; j < G.n; ++j) {
            vector<int> q(k);
            for (int t = 0; t < k; ++t) q[t] = perms[i][perms[j][t]];
            G.mul[i][j] = idx[q];
            if (G.mul[i][j] == 0) G.inv[i] = j;
        }
    }
    return G;
}

int mod_inv(int a, int p) {
    a = (a % p + p) % p;
    for (int x = 1; x < p; ++x) if ((a * x) % p == 1) return x;
    return 0;
}

Group build_PGL2_or_PSL2(int p, bool pgl) {
    auto norm = [&](array<int,4> m) -> array<int,4> {
        for (int i = 0; i < 4; ++i) m[i] = (m[i] % p + p) % p;
        for (int i = 0; i < 4; ++i) {
            if (m[i] != 0) {
                int inv = mod_inv(m[i], p);
                for (int j = 0; j < 4; ++j) m[j] = (m[j] * inv) % p;
                break;
            }
        }
        return m;
    };
    vector<bool> is_sq(p, false);
    for (int x = 1; x < p; ++x) is_sq[(x * x) % p] = true;

    vector<array<int,4>> elems;
    map<array<int,4>, int> idx;
    for (int a = 0; a < p; ++a)
      for (int b = 0; b < p; ++b)
        for (int c = 0; c < p; ++c)
          for (int d = 0; d < p; ++d) {
              int det = ((a * d - b * c) % p + p) % p;
              if (det == 0) continue;
              if (!pgl && !is_sq[det]) continue;
              auto m = norm({a, b, c, d});
              if (!idx.count(m)) {
                  idx[m] = (int)elems.size();
                  elems.push_back(m);
              }
          }
    array<int,4> id = norm({1,0,0,1});
    int id_pos = idx[id];
    if (id_pos != 0) {
        swap(elems[0], elems[id_pos]);
        idx[elems[0]] = 0;
        idx[elems[id_pos]] = id_pos;
    }
    Group G;
    G.name = (pgl ? "PGL(2," : "PSL(2,") + to_string(p) + ")";
    G.n = (int)elems.size();
    G.mul.assign(G.n, vector<int>(G.n));
    G.inv.assign(G.n, 0);
    for (int i = 0; i < G.n; ++i) {
        for (int j = 0; j < G.n; ++j) {
            auto& A = elems[i];
            auto& B = elems[j];
            array<int,4> C = {
                (A[0]*B[0] + A[1]*B[2]) % p,
                (A[0]*B[1] + A[1]*B[3]) % p,
                (A[2]*B[0] + A[3]*B[2]) % p,
                (A[2]*B[1] + A[3]*B[3]) % p
            };
            G.mul[i][j] = idx[norm(C)];
            if (G.mul[i][j] == 0) G.inv[i] = j;
        }
    }
    return G;
}

int girth_from_v(const vector<array<int,3>>& adj, int n, int start, int cap = 30) {
    vector<int> dist(n, -1), par(n, -1);
    queue<int> q;
    dist[start] = 0;
    q.push(start);
    int best = cap;
    while (!q.empty()) {
        int u = q.front(); q.pop();
        if (2 * dist[u] + 1 >= best) break;
        for (int v : adj[u]) {
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

bool is_connected_cubic(const vector<array<int,3>>& adj, int n) {
    vector<uint8_t> vis(n, 0);
    queue<int> q;
    vis[0] = 1; q.push(0); int cnt = 1;
    while (!q.empty()) {
        int u = q.front(); q.pop();
        for (int v : adj[u]) if (!vis[v]) { vis[v] = 1; cnt++; q.push(v); }
    }
    return cnt == n;
}

bool has_cycle_len_from_v(const vector<array<int,3>>& adj, int n, int start, int L, long long max_nodes = 4000000) {
    vector<int> dist(n, 1000000);
    {
        queue<int> q;
        dist[start] = 0;
        q.push(start);
        while (!q.empty()) {
            int u = q.front(); q.pop();
            if (dist[u] >= L - 1) continue;
            for (int v : adj[u]) {
                if (dist[v] > dist[u] + 1) {
                    dist[v] = dist[u] + 1;
                    q.push(v);
                }
            }
        }
    }
    vector<uint8_t> vis(n, 0);
    vis[start] = 1;
    bool found = false;
    long long nodes = 0;
    auto dfs = [&](auto& self, int u, int rem) -> void {
        if (found || ++nodes > max_nodes) return;
        if (dist[u] > rem) return;
        if (rem == 1) {
            for (int v : adj[u]) if (v == start) { found = true; return; }
            return;
        }
        for (int v : adj[u]) {
            if (!vis[v] && dist[v] <= rem - 1) {
                vis[v] = 1;
                self(self, v, rem - 1);
                vis[v] = 0;
                if (found || nodes > max_nodes) return;
            }
        }
    };
    for (int v : adj[start]) {
        vis[v] = 1;
        dfs(dfs, v, L - 1);
        vis[v] = 0;
        if (found) return true;
    }
    return false;
}

struct CayleyStats {
    string name;
    int n;
    long long tested_3inv = 0, conn_3inv = 0, g9_3inv = 0, no_c16_3inv = 0, no_c16_32_3inv = 0;
    long long tested_xt = 0, conn_xt = 0, g9_xt = 0, no_c16_xt = 0, no_c16_32_xt = 0;
    int max_g = 0;
    map<int, long long> girth_hist;
};

CayleyStats run_cayley_group(const Group& G, int max_3inv, int max_xt, uint64_t seed) {
    vector<int> invols, non_invols;
    for (int i = 1; i < G.n; ++i) {
        if (G.inv[i] == i) invols.push_back(i);
        else if (i < G.inv[i]) non_invols.push_back(i);
    }
    CayleyStats st;
    st.name = G.name;
    st.n = G.n;

    vector<pair<int,int>> good_inv_pairs;
    for (size_t i = 0; i < invols.size(); ++i) {
        for (size_t j = i + 1; j < invols.size(); ++j) {
            int a = invols[i], b = invols[j];
            int ab = G.mul[a][b];
            int cur = ab, ord = 1;
            while (cur != 0 && ord <= 12) { cur = G.mul[cur][ab]; ord++; }
            if (ord >= 5) good_inv_pairs.push_back({a, b});
        }
    }

    int n_inv = (int)invols.size();
    int n_pairs = (int)good_inv_pairs.size();

    #pragma omp parallel
    {
        mt19937_64 rng(seed + 1009ULL * (omp_get_thread_num() + 1));
        vector<array<int,3>> adj(G.n);
        long long l_tested = 0, l_conn = 0, l_g9 = 0, l_noc16 = 0, l_noc1632 = 0;
        int l_maxg = 0;
        map<int, long long> l_hist;

        #pragma omp for schedule(dynamic, 32)
        for (int t = 0; t < max_3inv; ++t) {
            if (n_pairs == 0 || n_inv < 3) continue;
            auto [a, b] = good_inv_pairs[rng() % n_pairs];
            int c = invols[rng() % n_inv];
            if (c == a || c == b) continue;
            l_tested++;
            for (int u = 0; u < G.n; ++u)
                adj[u] = {G.mul[u][a], G.mul[u][b], G.mul[u][c]};
            if (!is_connected_cubic(adj, G.n)) continue;
            l_conn++;
            int g = girth_from_v(adj, G.n, 0, 24);
            if (g > l_maxg) l_maxg = g;
            if (g >= 9) {
                l_g9++;
                l_hist[g]++;
                bool c16 = has_cycle_len_from_v(adj, G.n, 0, 16);
                if (!c16) {
                    l_noc16++;
                    bool c32 = has_cycle_len_from_v(adj, G.n, 0, 32);
                    if (!c32) {
                        bool c64 = has_cycle_len_from_v(adj, G.n, 0, 64);
                        if (!c64) {
                            l_noc1632++;
                            #pragma omp critical
                            cout << "!!! COUNTEREXAMPLE CANDIDATE " << G.name
                                 << " 3inv (" << a << "," << b << "," << c << ") g=" << g
                                 << " NO C16, NO C32, NO C64!\n" << flush;
                        }
                    }
                }
            }
        }
        #pragma omp critical
        {
            st.tested_3inv += l_tested;
            st.conn_3inv += l_conn;
            st.g9_3inv += l_g9;
            st.no_c16_3inv += l_noc16;
            st.no_c16_32_3inv += l_noc1632;
            if (l_maxg > st.max_g) st.max_g = l_maxg;
            for (auto [k, v] : l_hist) st.girth_hist[k] += v;
        }
    }

    int n_noninv = (int)non_invols.size();
    #pragma omp parallel
    {
        mt19937_64 rng(seed + 7919ULL * (omp_get_thread_num() + 1));
        vector<array<int,3>> adj(G.n);
        long long l_tested = 0, l_conn = 0, l_g9 = 0, l_noc16 = 0, l_noc1632 = 0;
        int l_maxg = 0;
        map<int, long long> l_hist;

        #pragma omp for schedule(dynamic, 32)
        for (int t = 0; t < max_xt; ++t) {
            if (n_noninv == 0 || n_inv == 0) continue;
            int x = non_invols[rng() % n_noninv];
            int xi = G.inv[x];
            int inv_t = invols[rng() % n_inv];
            l_tested++;
            for (int u = 0; u < G.n; ++u)
                adj[u] = {G.mul[u][x], G.mul[u][xi], G.mul[u][inv_t]};
            if (!is_connected_cubic(adj, G.n)) continue;
            l_conn++;
            int g = girth_from_v(adj, G.n, 0, 24);
            if (g > l_maxg) l_maxg = g;
            if (g >= 9) {
                l_g9++;
                l_hist[g]++;
                bool c16 = has_cycle_len_from_v(adj, G.n, 0, 16);
                if (!c16) {
                    l_noc16++;
                    bool c32 = has_cycle_len_from_v(adj, G.n, 0, 32);
                    if (!c32) {
                        bool c64 = has_cycle_len_from_v(adj, G.n, 0, 64);
                        if (!c64) {
                            l_noc1632++;
                            #pragma omp critical
                            cout << "!!! COUNTEREXAMPLE CANDIDATE " << G.name
                                 << " (x,x^-1,t)=(" << x << "," << inv_t << ") g=" << g
                                 << " NO C16, NO C32, NO C64!\n" << flush;
                        }
                    }
                }
            }
        }
        #pragma omp critical
        {
            st.tested_xt += l_tested;
            st.conn_xt += l_conn;
            st.g9_xt += l_g9;
            st.no_c16_xt += l_noc16;
            st.no_c16_32_xt += l_noc1632;
            if (l_maxg > st.max_g) st.max_g = l_maxg;
            for (auto [k, v] : l_hist) st.girth_hist[k] += v;
        }
    }

    return st;
}

struct LiftStats {
    string group_name;
    int lift_n;
    long long tested = 0, conn = 0, g9plus = 0, no_c16 = 0, no_c16_32 = 0;
    int max_g = 0;
    map<int, long long> girth_hist;
};

LiftStats run_k4_lifts(const Group& G, int trials, uint64_t seed) {
    LiftStats st;
    st.group_name = G.name;
    st.lift_n = 4 * G.n;

    #pragma omp parallel
    {
        mt19937_64 rng(seed + 31337ULL * (omp_get_thread_num() + 1));
        vector<array<int,3>> adj(4 * G.n);
        long long l_tested = 0, l_conn = 0, l_g9 = 0, l_noc16 = 0, l_noc1632 = 0;
        int l_maxg = 0;
        map<int, long long> l_hist;

        #pragma omp for schedule(dynamic, 16)
        for (int t = 0; t < trials; ++t) {
            int g1 = 1 + (rng() % (G.n - 1));
            int g2 = 1 + (rng() % (G.n - 1));
            int g3 = 1 + (rng() % (G.n - 1));
            int g1i = G.inv[g1], g2i = G.inv[g2], g3i = G.inv[g3];
            l_tested++;
            for (int x = 0; x < G.n; ++x) {
                adj[0 * G.n + x] = {1 * G.n + x, 2 * G.n + x, 3 * G.n + x};
                adj[1 * G.n + x] = {0 * G.n + x, 2 * G.n + G.mul[x][g1], 3 * G.n + G.mul[x][g3i]};
                adj[2 * G.n + x] = {0 * G.n + x, 1 * G.n + G.mul[x][g1i], 3 * G.n + G.mul[x][g2]};
                adj[3 * G.n + x] = {0 * G.n + x, 2 * G.n + G.mul[x][g2i], 1 * G.n + G.mul[x][g3]};
            }
            if (!is_connected_cubic(adj, 4 * G.n)) continue;
            l_conn++;
            int g = 24;
            for (int r = 0; r < 4; ++r) {
                g = min(g, girth_from_v(adj, 4 * G.n, r * G.n, g));
                if (g < 9) break;
            }
            if (g > l_maxg) l_maxg = g;
            if (g >= 9) {
                l_g9++;
                l_hist[g]++;
                bool c16 = false;
                for (int r = 0; r < 4 && !c16; ++r)
                    c16 = has_cycle_len_from_v(adj, 4 * G.n, r * G.n, 16);
                if (!c16) {
                    l_noc16++;
                    bool c32 = false;
                    for (int r = 0; r < 4 && !c32; ++r)
                        c32 = has_cycle_len_from_v(adj, 4 * G.n, r * G.n, 32);
                    if (!c32) {
                        bool c64 = false;
                        for (int r = 0; r < 4 && !c64; ++r)
                            c64 = has_cycle_len_from_v(adj, 4 * G.n, r * G.n, 64);
                        if (!c64) {
                            l_noc1632++;
                            #pragma omp critical
                            cout << "!!! K4 LIFT CANDIDATE " << G.name
                                 << " (" << g1 << "," << g2 << "," << g3 << ") n=" << 4*G.n
                                 << " g=" << g << " NO C16, NO C32, NO C64!\n" << flush;
                        }
                    }
                }
            }
        }
        #pragma omp critical
        {
            st.tested += l_tested;
            st.conn += l_conn;
            st.g9plus += l_g9;
            st.no_c16 += l_noc16;
            st.no_c16_32 += l_noc1632;
            if (l_maxg > st.max_g) st.max_g = l_maxg;
            for (auto [k, v] : l_hist) st.girth_hist[k] += v;
        }
    }
    return st;
}

// Part 3: Strict Girth>=9 Cubic SA Counterexample Hunt (n in {132, 140, 150, 160, 180, 200})
struct SAStats {
    int n;
    int restarts;
    int girth9_reached;
    int best_girth;
    int min_c16_at_g9;
    int has_c32_count;
};

int count_short_cycles_le8(const vector<array<int,3>>& adj, int n) {
    // Count vertices whose local girth <= 8 (fast proxy to drive girth >= 9)
    int bad = 0;
    vector<int> dist(n), par(n);
    for (int s = 0; s < n; ++s) {
        fill(dist.begin(), dist.end(), -1);
        fill(par.begin(), par.end(), -1);
        queue<int> q;
        dist[s] = 0; q.push(s);
        bool hit = false;
        while (!q.empty() && !hit) {
            int u = q.front(); q.pop();
            if (dist[u] >= 4) break;
            for (int v : adj[u]) {
                if (dist[v] == -1) {
                    dist[v] = dist[u] + 1;
                    par[v] = u;
                    q.push(v);
                } else if (par[u] != v) {
                    if (dist[u] + dist[v] + 1 <= 8) { hit = true; break; }
                }
            }
        }
        if (hit) bad++;
    }
    return bad;
}

int global_girth(const vector<array<int,3>>& adj, int n) {
    int g = 30;
    for (int s = 0; s < n; ++s) {
        g = min(g, girth_from_v(adj, n, s, g));
        if (g <= 3) return g;
    }
    return g;
}

int count_c16_capped(const vector<array<int,3>>& adj, int n, int cap = 200) {
    // Count simple C16 cycles (up to cap) across starting vertices s with min-vertex symmetry breaking
    int total = 0;
    vector<uint8_t> vis(n, 0);
    for (int s = 0; s < n && total < cap; ++s) {
        vis[s] = 1;
        auto dfs = [&](auto& self, int u, int rem) -> void {
            if (total >= cap) return;
            if (rem == 1) {
                for (int v : adj[u]) if (v == s) { total++; return; }
                return;
            }
            for (int v : adj[u]) {
                if (v > s && !vis[v]) {
                    vis[v] = 1;
                    self(self, v, rem - 1);
                    vis[v] = 0;
                    if (total >= cap) return;
                }
            }
        };
        for (int v : adj[s]) {
            if (v > s) {
                vis[v] = 1;
                dfs(dfs, v, 15);
                vis[v] = 0;
                if (total >= cap) break;
            }
        }
        vis[s] = 0;
    }
    return total / 2;
}

bool has_edge_cubic(const vector<array<int,3>>& adj, int u, int v) {
    return adj[u][0] == v || adj[u][1] == v || adj[u][2] == v;
}

void replace_nbr(vector<array<int,3>>& adj, int u, int old_v, int new_v) {
    for (int k = 0; k < 3; ++k) if (adj[u][k] == old_v) { adj[u][k] = new_v; return; }
}

SAStats run_girth9_sa(int n, int restarts, int steps_phase1, int steps_phase2, uint64_t seed) {
    SAStats st{n, restarts, 0, 0, 1000000, 0};
    #pragma omp parallel for schedule(dynamic)
    for (int r = 0; r < restarts; ++r) {
        mt19937_64 rng(seed + 10007ULL * r + 97ULL * n);
        // Generate random simple cubic graph
        vector<array<int,3>> adj(n);
        vector<pair<int,int>> edges;
        while (true) {
            vector<int> stubs;
            stubs.reserve(3 * n);
            for (int i = 0; i < n; ++i) for (int k = 0; k < 3; ++k) stubs.push_back(i);
            shuffle(stubs.begin(), stubs.end(), rng);
            vector<int> deg(n, 0);
            edges.clear();
            bool ok = true;
            for (int i = 0; i < 3 * n; i += 2) {
                int u = stubs[i], v = stubs[i + 1];
                if (u == v) { ok = false; break; }
                for (int k = 0; k < deg[u]; ++k) if (adj[u][k] == v) { ok = false; break; }
                if (!ok) break;
                adj[u][deg[u]++] = v;
                adj[v][deg[v]++] = u;
                edges.push_back({u, v});
            }
            if (ok) break;
        }
        int m = (int)edges.size();
        int bad = count_short_cycles_le8(adj, n);

        // Phase 1: drive bad -> 0 (strict girth >= 9)
        for (int step = 0; step < steps_phase1 && bad > 0; ++step) {
            int i = rng() % m, j = rng() % m;
            if (i == j) continue;
            auto [a, b] = edges[i];
            auto [c, d] = edges[j];
            if (a == c || a == d || b == c || b == d) continue;
            int u1 = a, v1 = c, u2 = b, v2 = d;
            if (rng() & 1) { v1 = d; v2 = c; }
            if (has_edge_cubic(adj, u1, v1) || has_edge_cubic(adj, u2, v2)) continue;

            replace_nbr(adj, a, b, v1); replace_nbr(adj, b, a, v2);
            replace_nbr(adj, v1, (v1 == c ? d : c), a);
            replace_nbr(adj, v2, (v2 == d ? c : d), b);
            int nxt = count_short_cycles_le8(adj, n);
            if (nxt <= bad || (nxt == bad + 1 && (rng() % 25 == 0))) {
                bad = nxt;
                edges[i] = {u1, v1};
                edges[j] = {u2, v2};
            } else {
                replace_nbr(adj, a, v1, b); replace_nbr(adj, b, v2, a);
                replace_nbr(adj, v1, a, (v1 == c ? d : c));
                replace_nbr(adj, v2, b, (v2 == d ? c : d));
            }
        }

        int g = global_girth(adj, n);
        int c16 = -1;
        bool has32 = false;
        if (g >= 9) {
            c16 = count_c16_capped(adj, n, 200);
            // Phase 2: minimize C16 while strictly maintaining girth >= 9
            for (int step = 0; step < steps_phase2 && c16 > 0; ++step) {
                int i = rng() % m, j = rng() % m;
                if (i == j) continue;
                auto [a, b] = edges[i];
                auto [c, d] = edges[j];
                if (a == c || a == d || b == c || b == d) continue;
                int u1 = a, v1 = c, u2 = b, v2 = d;
                if (rng() & 1) { v1 = d; v2 = c; }
                if (has_edge_cubic(adj, u1, v1) || has_edge_cubic(adj, u2, v2)) continue;

                replace_nbr(adj, a, b, v1); replace_nbr(adj, b, a, v2);
                replace_nbr(adj, v1, (v1 == c ? d : c), a);
                replace_nbr(adj, v2, (v2 == d ? c : d), b);
                if (count_short_cycles_le8(adj, n) == 0) {
                    int nc16 = count_c16_capped(adj, n, c16 + 1);
                    if (nc16 <= c16) {
                        c16 = nc16;
                        edges[i] = {u1, v1};
                        edges[j] = {u2, v2};
                        continue;
                    }
                }
                replace_nbr(adj, a, v1, b); replace_nbr(adj, b, v2, a);
                replace_nbr(adj, v1, a, (v1 == c ? d : c));
                replace_nbr(adj, v2, b, (v2 == d ? c : d));
            }
            for (int s = 0; s < min(n, 8) && !has32; ++s)
                has32 = has_cycle_len_from_v(adj, n, s, 32, 1000000);
        }

        #pragma omp critical
        {
            if (g > st.best_girth) st.best_girth = g;
            if (g >= 9) {
                st.girth9_reached++;
                if (c16 < st.min_c16_at_g9) st.min_c16_at_g9 = c16;
                if (has32) st.has_c32_count++;
            }
        }
    }
    if (st.girth9_reached == 0) st.min_c16_at_g9 = -1;
    return st;
}

int main(int argc, char** argv) {
    string out_json = (argc > 1) ? argv[1] : "out/high_girth_siege.json";
    auto t0 = chrono::steady_clock::now();

    cout << "=== Wave 8 Agent #7: High-Girth (g in {9..14}) Siege (threads="
         << omp_get_max_threads() << ") ===\n" << flush;

    auto S4 = build_S_k(4, false);
    auto A5 = build_S_k(5, true);
    auto S5 = build_S_k(5, false);
    auto PSL7 = build_PGL2_or_PSL2(7, false);
    auto PGL7 = build_PGL2_or_PSL2(7, true);
    auto A6 = build_S_k(6, true);
    auto PSL11 = build_PGL2_or_PSL2(11, false);
    auto S6 = build_S_k(6, false);
    auto PSL13 = build_PGL2_or_PSL2(13, false);

    vector<pair<Group, pair<int,int>>> cayley_jobs = {
        {S5,    {6000, 6000}},
        {PSL7,  {6000, 6000}},
        {PGL7,  {15000, 10000}},
        {A6,    {15000, 10000}},
        {PSL11, {12000, 12000}},
        {S6,    {12000, 8000}},
        {PSL13, {8000, 8000}}
    };

    vector<CayleyStats> c_results;
    for (size_t i = 0; i < cayley_jobs.size(); ++i) {
        auto st = run_cayley_group(cayley_jobs[i].first,
                                   cayley_jobs[i].second.first,
                                   cayley_jobs[i].second.second,
                                   800001ULL + i * 10007ULL);
        c_results.push_back(st);
        cout << "[Cayley " << st.name << " n=" << st.n << "] "
             << "3inv(conn=" << st.conn_3inv << ", g>=9=" << st.g9_3inv
             << ", noC16=" << st.no_c16_3inv << ", noC16_32_64=" << st.no_c16_32_3inv << ") "
             << "xt(conn=" << st.conn_xt << ", g>=9=" << st.g9_xt
             << ", noC16=" << st.no_c16_xt << ", noC16_32_64=" << st.no_c16_32_xt << ") "
             << "max_g=" << st.max_g << " hist={";
        bool first = true;
        for (auto [k, v] : st.girth_hist) {
            if (!first) cout << ",";
            cout << k << ":" << v;
            first = false;
        }
        cout << "}\n" << flush;
    }

    vector<pair<Group, int>> lift_jobs = {
        {S4, 6000}, {A5, 10000}, {S5, 10000}, {PSL7, 10000}, {PGL7, 6000}
    };
    vector<LiftStats> l_results;
    for (size_t i = 0; i < lift_jobs.size(); ++i) {
        auto st = run_k4_lifts(lift_jobs[i].first, lift_jobs[i].second, 900001ULL + i * 10007ULL);
        l_results.push_back(st);
        cout << "[K4-Lift " << st.group_name << " n=" << st.lift_n << "] "
             << "conn=" << st.conn << " g>=9=" << st.g9plus
             << " noC16=" << st.no_c16 << " noC16_32_64=" << st.no_c16_32
             << " max_g=" << st.max_g << " hist={";
        bool first = true;
        for (auto [k, v] : st.girth_hist) {
            if (!first) cout << ",";
            cout << k << ":" << v;
            first = false;
        }
        cout << "}\n" << flush;
    }

    vector<int> sa_orders = {132, 140, 150, 160, 180, 200};
    vector<SAStats> sa_results;
    for (int n : sa_orders) {
        auto st = run_girth9_sa(n, 8, 8000, 1500, 777001ULL + n * 131ULL);
        sa_results.push_back(st);
        cout << "[Girth>=9 SA n=" << st.n << "] restarts=" << st.restarts
             << " g>=9_reached=" << st.girth9_reached << " best_g=" << st.best_girth
             << " min_C16_at_g9=" << st.min_c16_at_g9
             << " has_C32=" << st.has_c32_count << "/" << st.girth9_reached << "\n" << flush;
    }

    auto t1 = chrono::steady_clock::now();
    double elapsed = chrono::duration<double>(t1 - t0).count();
    cout << "Total elapsed: " << fixed << setprecision(2) << elapsed << "s\n";

    ofstream jf(out_json);
    jf << "{\n  \"elapsed_sec\": " << fixed << setprecision(2) << elapsed << ",\n";
    jf << "  \"cayley\": [\n";
    for (size_t i = 0; i < c_results.size(); ++i) {
        auto& s = c_results[i];
        jf << "    {\"group\": \"" << s.name << "\", \"n\": " << s.n
           << ", \"conn_3inv\": " << s.conn_3inv << ", \"g9_3inv\": " << s.g9_3inv
           << ", \"no_c16_3inv\": " << s.no_c16_3inv << ", \"no_c16_32_64_3inv\": " << s.no_c16_32_3inv
           << ", \"conn_xt\": " << s.conn_xt << ", \"g9_xt\": " << s.g9_xt
           << ", \"no_c16_xt\": " << s.no_c16_xt << ", \"no_c16_32_64_xt\": " << s.no_c16_32_xt
           << ", \"max_g\": " << s.max_g << "}" << (i + 1 < c_results.size() ? "," : "") << "\n";
    }
    jf << "  ],\n  \"k4_lifts\": [\n";
    for (size_t i = 0; i < l_results.size(); ++i) {
        auto& s = l_results[i];
        jf << "    {\"group\": \"" << s.group_name << "\", \"n\": " << s.lift_n
           << ", \"conn\": " << s.conn << ", \"g9plus\": " << s.g9plus
           << ", \"no_c16\": " << s.no_c16 << ", \"no_c16_32_64\": " << s.no_c16_32
           << ", \"max_g\": " << s.max_g << "}" << (i + 1 < l_results.size() ? "," : "") << "\n";
    }
    jf << "  ],\n  \"girth9_sa\": [\n";
    for (size_t i = 0; i < sa_results.size(); ++i) {
        auto& s = sa_results[i];
        jf << "    {\"n\": " << s.n << ", \"restarts\": " << s.restarts
           << ", \"girth9_reached\": " << s.girth9_reached << ", \"best_girth\": " << s.best_girth
           << ", \"min_c16_at_g9\": " << s.min_c16_at_g9
           << ", \"has_c32_count\": " << s.has_c32_count << "}" << (i + 1 < sa_results.size() ? "," : "") << "\n";
    }
    jf << "  ]\n}\n";
    jf.close();
    return 0;
}
