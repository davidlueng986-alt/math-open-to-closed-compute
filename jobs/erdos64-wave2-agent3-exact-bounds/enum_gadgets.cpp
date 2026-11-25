#include <bits/stdc++.h>
#include <omp.h>
using namespace std;

// Exact lossless exhaustive enumerator for power-free cubic k-port gadgets (k in {2, 3}),
// both general (C4, C8, C16-free) and triangle-free (C3, C4, C8, C16-free).
//
// Symmetry breaking (100% mathematically lossless):
//   - Ports are vertices 0 .. NUM_PORTS-1 (degree 2).
//   - Non-port vertices are NUM_PORTS .. N-1 (degree 3).
//   - Edges are added in lexicographic order of endpoints (u, v) with u < v.
//   - Whenever a brand-new non-port vertex (deg[v] == 0, v >= NUM_PORTS) is touched,
//     it MUST be max_used_nonport + 1. (Every connected gadget has a unique canonical
//     non-port relabeling by order of first appearance.)
//   - Forward checking: if any vertex w with 0 < deg[w] < target_deg[w] has fewer
//     valid available neighbors than target_deg[w] - deg[w], prune immediately.
//   - Parallelization: expand the exact search tree to depth SPLIT_DEPTH sequentially,
//     then solve all frontier states independently across OpenMP threads.

struct State {
    int cur_u;
    int edges_added;
    int max_used_nonport;
    int deg[32];
    uint32_t adj[32];
    int last_nbr[32];
};

struct Config {
    int N;
    int NUM_PORTS;
    bool TRI_FREE;
    int target_deg[32];
};

inline bool creates_c4(const uint32_t* adj, int u, int v) {
    uint32_t nv = adj[v];
    uint32_t nu = adj[u];
    while (nu) {
        int x = __builtin_ctz(nu);
        nu &= nu - 1;
        if (adj[x] & (nv & ~(1u << x))) return true;
    }
    return false;
}

inline bool creates_c3(const uint32_t* adj, int u, int v) {
    return (adj[u] & adj[v]) != 0;
}

bool has_path_len(const uint32_t* adj, int curr, int target, int rem, uint32_t vis) {
    if (rem == 1) return (adj[curr] & (1u << target)) != 0;
    if (rem == 2) return (adj[curr] & adj[target] & ~vis) != 0;
    uint32_t m = adj[curr] & ~vis & ~(1u << target);
    while (m) {
        int nxt = __builtin_ctz(m);
        m &= m - 1;
        if (has_path_len(adj, nxt, target, rem - 1, vis | (1u << nxt)))
            return true;
    }
    return false;
}

inline bool forward_check(const Config& cfg, const State& st, int u, int max_used_nonport) {
    int unused_cnt = (cfg.N - 1) - max_used_nonport;
    for (int p = u; p < cfg.NUM_PORTS; ++p)
        if (st.deg[p] == 0) unused_cnt++;
    for (int w = u; w <= max_used_nonport; ++w) {
        int need = cfg.target_deg[w] - st.deg[w];
        if (need <= 0) continue;
        if (unused_cnt >= need) continue;
        int avail = unused_cnt;
        for (int v = u; v <= max_used_nonport; ++v) {
            if (v == w || st.deg[v] >= cfg.target_deg[v] || st.deg[v] == 0) continue;
            if (st.adj[w] & (1u << v)) continue;
            if (w == u && v <= st.last_nbr[u]) continue;
            if (cfg.TRI_FREE && creates_c3(st.adj, w, v)) continue;
            if (creates_c4(st.adj, w, v)) continue;
            avail++;
            if (avail >= need) break;
        }
        if (avail < need) return false;
    }
    return true;
}

void dfs_worker(const Config& cfg, State& st, uint64_t& nodes, uint64_t& sols,
                vector<vector<pair<int,int>>>& found_examples, int max_examples) {
    nodes++;
    int u = st.cur_u;
    while (u < cfg.N && st.deg[u] == cfg.target_deg[u]) u++;
    if (u == cfg.N) {
        uint32_t vis = 1u, q = 1u;
        while (q) {
            int x = __builtin_ctz(q);
            q &= q - 1;
            uint32_t nxt = st.adj[x] & ~vis;
            vis |= nxt;
            q |= nxt;
        }
        if (__builtin_popcount(vis) != cfg.N) return;
        sols++;
        if ((int)found_examples.size() < max_examples) {
            vector<pair<int,int>> es;
            for (int i = 0; i < cfg.N; ++i)
                for (int j = i + 1; j < cfg.N; ++j)
                    if (st.adj[i] & (1u << j)) es.push_back({i, j});
            found_examples.push_back(move(es));
        }
        return;
    }

    int start_v = max(u + 1, st.last_nbr[u] + 1);
    int limit_v = min(cfg.N - 1, st.max_used_nonport + 1);
    int old_cur_u = st.cur_u;
    st.cur_u = u;

    for (int v = start_v; v <= limit_v; ++v) {
        if (st.deg[v] >= cfg.target_deg[v]) continue;
        if (st.adj[u] & (1u << v)) continue;
        bool is_new = (st.deg[v] == 0);
        if (!is_new) {
            if (cfg.TRI_FREE && creates_c3(st.adj, u, v)) continue;
            if (creates_c4(st.adj, u, v)) continue;
            if (st.edges_added >= 7 && has_path_len(st.adj, u, v, 7, (1u << u) | (1u << v))) continue;
            if (st.edges_added >= 15 && has_path_len(st.adj, u, v, 15, (1u << u) | (1u << v))) continue;
        }
        st.adj[u] |= (1u << v);
        st.adj[v] |= (1u << u);
        st.deg[u]++; st.deg[v]++;
        int old_last = st.last_nbr[u];
        int old_max = st.max_used_nonport;
        st.last_nbr[u] = v;
        st.edges_added++;
        if (v >= cfg.NUM_PORTS && v > st.max_used_nonport) st.max_used_nonport = v;

        if (forward_check(cfg, st, u, st.max_used_nonport)) {
            dfs_worker(cfg, st, nodes, sols, found_examples, max_examples);
        }

        st.edges_added--;
        st.max_used_nonport = old_max;
        st.last_nbr[u] = old_last;
        st.deg[u]--; st.deg[v]--;
        st.adj[u] &= ~(1u << v);
        st.adj[v] &= ~(1u << u);
    }
    st.cur_u = old_cur_u;
}

void collect_frontier(const Config& cfg, State& st, int split_depth,
                      vector<State>& frontier, uint64_t& pre_nodes, uint64_t& pre_sols) {
    pre_nodes++;
    int u = st.cur_u;
    while (u < cfg.N && st.deg[u] == cfg.target_deg[u]) u++;
    if (u == cfg.N) {
        uint32_t vis = 1u, q = 1u;
        while (q) {
            int x = __builtin_ctz(q);
            q &= q - 1;
            uint32_t nxt = st.adj[x] & ~vis;
            vis |= nxt;
            q |= nxt;
        }
        if (__builtin_popcount(vis) == cfg.N) pre_sols++;
        return;
    }
    if (st.edges_added >= split_depth) {
        State copy = st;
        copy.cur_u = u;
        frontier.push_back(copy);
        return;
    }

    int start_v = max(u + 1, st.last_nbr[u] + 1);
    int limit_v = min(cfg.N - 1, st.max_used_nonport + 1);
    int old_cur_u = st.cur_u;
    st.cur_u = u;

    for (int v = start_v; v <= limit_v; ++v) {
        if (st.deg[v] >= cfg.target_deg[v]) continue;
        if (st.adj[u] & (1u << v)) continue;
        bool is_new = (st.deg[v] == 0);
        if (!is_new) {
            if (cfg.TRI_FREE && creates_c3(st.adj, u, v)) continue;
            if (creates_c4(st.adj, u, v)) continue;
            if (st.edges_added >= 7 && has_path_len(st.adj, u, v, 7, (1u << u) | (1u << v))) continue;
            if (st.edges_added >= 15 && has_path_len(st.adj, u, v, 15, (1u << u) | (1u << v))) continue;
        }
        st.adj[u] |= (1u << v);
        st.adj[v] |= (1u << u);
        st.deg[u]++; st.deg[v]++;
        int old_last = st.last_nbr[u];
        int old_max = st.max_used_nonport;
        st.last_nbr[u] = v;
        st.edges_added++;
        if (v >= cfg.NUM_PORTS && v > st.max_used_nonport) st.max_used_nonport = v;

        if (forward_check(cfg, st, u, st.max_used_nonport)) {
            collect_frontier(cfg, st, split_depth, frontier, pre_nodes, pre_sols);
        }

        st.edges_added--;
        st.max_used_nonport = old_max;
        st.last_nbr[u] = old_last;
        st.deg[u]--; st.deg[v]--;
        st.adj[u] &= ~(1u << v);
        st.adj[v] &= ~(1u << u);
    }
    st.cur_u = old_cur_u;
}

void run_exact(int n, int ports, bool tri_free, int split_depth) {
    Config cfg;
    cfg.N = n; cfg.NUM_PORTS = ports; cfg.TRI_FREE = tri_free;
    for (int i = 0; i < n; ++i) cfg.target_deg[i] = (i < ports) ? 2 : 3;

    State init{};
    init.cur_u = 0;
    init.edges_added = 0;
    init.max_used_nonport = ports - 1;
    for (int i = 0; i < 32; ++i) { init.deg[i] = 0; init.adj[i] = 0; init.last_nbr[i] = -1; }

    auto t0 = chrono::steady_clock::now();
    vector<State> frontier;
    uint64_t total_nodes = 0, total_sols = 0;
    collect_frontier(cfg, init, split_depth, frontier, total_nodes, total_sols);

    vector<vector<pair<int,int>>> all_examples;
    #pragma omp parallel
    {
        uint64_t loc_nodes = 0, loc_sols = 0;
        vector<vector<pair<int,int>>> loc_ex;
        #pragma omp for schedule(dynamic, 1)
        for (size_t i = 0; i < frontier.size(); ++i) {
            State st = frontier[i];
            dfs_worker(cfg, st, loc_nodes, loc_sols, loc_ex, 3);
        }
        #pragma omp critical
        {
            total_nodes += loc_nodes;
            total_sols += loc_sols;
            for (auto& ex : loc_ex)
                if (all_examples.size() < 5) all_examples.push_back(move(ex));
        }
    }

    auto t1 = chrono::steady_clock::now();
    double dt = chrono::duration<double>(t1 - t0).count();
    cout << "[EXACT] n=" << n << " ports=" << ports
         << " mode=" << (tri_free ? "triangle-free" : "general")
         << " frontier=" << frontier.size()
         << " nodes=" << total_nodes
         << " solutions=" << total_sols
         << " time=" << fixed << setprecision(3) << dt << "s" << endl;
    for (size_t i = 0; i < all_examples.size(); ++i) {
        cout << "  example #" << (i+1) << ": ";
        for (auto [a, b] : all_examples[i]) cout << "(" << a << "," << b << ") ";
        cout << endl;
    }
}

int main(int argc, char** argv) {
    cout << "OpenMP max threads: " << omp_get_max_threads() << endl;
    if (argc >= 6 && string(argv[1]) == "single") {
        int n = stoi(argv[2]);
        int ports = stoi(argv[3]);
        bool tri_free = (stoi(argv[4]) != 0);
        int split_depth = stoi(argv[5]);
        // Quick sanity tests first
        run_exact(3, 3, false, 2);
        run_exact(7, 3, false, 4);
        run_exact(n, ports, tri_free, split_depth);
        return 0;
    }
    run_exact(3, 3, false, 2);
    run_exact(5, 3, false, 4);
    run_exact(7, 3, false, 4);
    return 0;
}
