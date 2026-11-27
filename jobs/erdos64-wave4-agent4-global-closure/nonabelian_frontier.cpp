#include <bits/stdc++.h>
#include <omp.h>
using namespace std;

struct Graph {
    int n;
    vector<vector<int>> adj;
    vector<pair<int,int>> edges;
    Graph(int n = 0) : n(n), adj(n) {}
    void add_edge(int u, int v) {
        adj[u].push_back(v);
        adj[v].push_back(u);
    }
    bool has_edge(int u, int v) const {
        for (int x : adj[u]) if (x == v) return true;
        return false;
    }
    void rebuild_edges() {
        edges.clear();
        for (int u = 0; u < n; ++u)
            for (int v : adj[u]) if (u < v) edges.push_back({u, v});
    }
};

int count_C3(const Graph& g) {
    int c3 = 0;
    for (int u = 0; u < g.n; ++u)
        for (int v : g.adj[u]) if (v > u)
            for (int w : g.adj[v]) if (w > v && g.has_edge(u, w)) c3++;
    return c3;
}

int count_C4(const Graph& g) {
    int n = g.n, c4 = 0;
    vector<int> cnt(n, 0);
    for (int u = 0; u < n; ++u) {
        for (int v : g.adj[u]) if (v > u)
            for (int w : g.adj[v]) if (w > u) { c4 += cnt[w]; cnt[w]++; }
        for (int v : g.adj[u]) if (v > u)
            for (int w : g.adj[v]) if (w > u) cnt[w] = 0;
    }
    return c4;
}

int count_cycles_len(const Graph& g, int L, int cap) {
    int n = g.n;
    if (L > n) return 0;
    int found = 0;
    vector<int> dist(n), q(n);
    vector<uint8_t> vis(n, 0);

    for (int s = 0; s <= n - L; ++s) {
        fill(dist.begin() + s, dist.end(), 1000);
        int head = 0, tail = 0;
        dist[s] = 0;
        q[tail++] = s;
        while (head < tail) {
            int u = q[head++];
            if (dist[u] >= L - 1) continue;
            for (int v : g.adj[u]) {
                if (v > s && dist[v] == 1000) {
                    dist[v] = dist[u] + 1;
                    q[tail++] = v;
                }
            }
        }
        vector<int> nbrs;
        for (int v : g.adj[s]) if (v > s) nbrs.push_back(v);
        if (nbrs.size() < 2) continue;

        vis[s] = 1;
        function<bool(int, int, int)> dfs = [&](int u, int depth, int first_nbr) -> bool {
            int rem = L - depth;
            if (rem == 1) {
                if (u > first_nbr) {
                    for (int v : g.adj[u]) {
                        if (v == s) {
                            found++;
                            if (found >= cap) return true;
                        }
                    }
                }
                return false;
            }
            for (int v : g.adj[u]) {
                if (v > s && !vis[v] && dist[v] <= rem - 1) {
                    vis[v] = 1;
                    if (dfs(v, depth + 1, first_nbr)) {
                        vis[v] = 0;
                        return true;
                    }
                    vis[v] = 0;
                }
            }
            return false;
        };

        for (int fn : nbrs) {
            vis[fn] = 1;
            if (dfs(fn, 1, fn)) {
                vis[fn] = 0;
                vis[s] = 0;
                return found;
            }
            vis[fn] = 0;
        }
        vis[s] = 0;
    }
    return found;
}

Graph random_cubic(int n, mt19937& rng) {
    vector<int> stubs(3 * n);
    for (int i = 0; i < n; ++i) stubs[3*i] = stubs[3*i+1] = stubs[3*i+2] = i;
    while (true) {
        shuffle(stubs.begin(), stubs.end(), rng);
        Graph g(n);
        bool ok = true;
        for (int i = 0; i < 3 * n; i += 2) {
            int u = stubs[i], v = stubs[i+1];
            if (u == v || g.has_edge(u, v)) { ok = false; break; }
            g.add_edge(u, v);
        }
        if (ok) return g;
    }
}

Graph find_trifree_c4c8_free(int n, mt19937& rng) {
    for (int restart = 0; restart < 40; ++restart) {
        Graph g = random_cubic(n, rng);
        auto eval = [&](const Graph& gr) {
            int c3 = count_C3(gr);
            int c4 = count_C4(gr);
            if (c3 + c4 > 0) return 10000 + (c3 + c4) * 100;
            return count_cycles_len(gr, 8, 200);
        };
        int cur = eval(g);
        for (int step = 0; step < 6000 && cur > 0; ++step) {
            int u = rng() % n, v = g.adj[u][rng() % 3];
            int x = rng() % n, y = g.adj[x][rng() % 3];
            if (u == x || u == y || v == x || v == y) continue;
            if (g.has_edge(u, x) || g.has_edge(v, y)) continue;
            auto rem = [&](int a, int b) {
                g.adj[a].erase(find(g.adj[a].begin(), g.adj[a].end(), b));
                g.adj[b].erase(find(g.adj[b].begin(), g.adj[b].end(), a));
            };
            rem(u, v); rem(x, y);
            g.add_edge(u, x); g.add_edge(v, y);
            int ne = eval(g);
            if (ne <= cur || (rng() % 100 < 3 && ne <= cur + 2)) cur = ne;
            else { rem(u, x); rem(v, y); g.add_edge(u, v); g.add_edge(x, y); }
        }
        if (cur == 0) { g.rebuild_edges(); return g; }
    }
    return Graph(0);
}

Graph build_perm_cover(const Graph& base, int d, const vector<vector<int>>& perms) {
    Graph L(base.n * d);
    for (size_t e = 0; e < base.edges.size(); ++e) {
        int u = base.edges[e].first, v = base.edges[e].second;
        for (int r = 0; r < d; ++r)
            L.add_edge(u * d + r, v * d + perms[e][r]);
    }
    return L;
}

int main() {
    cout << "Wave 4 Agent #4 Non-Abelian Cover & Class H Frontier Probe\n";
    int total_covers_checked = 0;
    int survivors = 0;

    #pragma omp parallel for reduction(+:total_covers_checked,survivors) schedule(dynamic)
    for (int seed = 1; seed <= 16; ++seed) {
        mt19937 rng(1000 + seed);
        int base_n = (seed % 2 == 0) ? 28 : 30;
        Graph base = find_trifree_c4c8_free(base_n, rng);
        if (base.n == 0) continue;
        for (int d : {3, 4, 5}) {
            int E = base.edges.size();
            vector<vector<int>> perms(E, vector<int>(d));
            for (int trial = 0; trial < 25; ++trial) {
                for (int e = 0; e < E; ++e) {
                    iota(perms[e].begin(), perms[e].end(), 0);
                    shuffle(perms[e].begin(), perms[e].end(), rng);
                }
                Graph L = build_perm_cover(base, d, perms);
                total_covers_checked++;
                // Automatically C3, C4, C8-free because base is C3, C4, C8-free!
                int c16 = count_cycles_len(L, 16, 1);
                if (c16 == 0) {
                    int c32 = count_cycles_len(L, 32, 1);
                    int c64 = (L.n >= 64) ? count_cycles_len(L, 64, 1) : 0;
                    int c128 = (L.n >= 128) ? count_cycles_len(L, 128, 1) : 0;
                    if (c32 == 0 && c64 == 0 && c128 == 0) {
                        survivors++;
                        #pragma omp critical
                        cout << "!!! COUNTEREXAMPLE FOUND seed=" << seed << " base_n=" << base_n
                             << " d=" << d << " order=" << L.n << " !!!\n";
                    }
                }
            }
        }
    }
    cout << "TOTAL_NONABELIAN_COVERS_CHECKED=" << total_covers_checked
         << " SURVIVORS=" << survivors << "\n";
    return 0;
}
