#include <bits/stdc++.h>
#include <omp.h>
using namespace std;

// Exact, sound, multi-threaded bitboard exhaustive search for connected power-free
// cubic k-port gadgets (all vertices degree 3 except k ports of degree 2;
// no simple cycle of length 4, 8, 16, 32).
// Ports are vertices 0..K-1 (degree 2); internal vertices are K..N-1 (degree 3).

static int N_VERTS;
static int K_PORTS;
static bool TRI_FREE;
static int TOTAL_EDGES;
static int max_deg[32];

struct State {
    uint32_t adj[32];
    uint8_t deg[32];
    int cur_u;
    int min_v;
    int next_port;
    int next_int;
    int edges_left;
};

inline bool has_path_len3(const uint32_t* adj, int u, int v) {
    uint32_t nv = adj[v];
    uint32_t m = adj[u];
    while (m) {
        int a = __builtin_ctz(m);
        m &= m - 1;
        if (adj[a] & nv & ~(1u << u)) return true;
    }
    return false;
}

bool has_path_exact(const uint32_t* adj, int cur, int target, int rem, uint32_t visited) {
    if (rem == 1) return (adj[cur] & (1u << target)) != 0;
    if (rem == 2) return (adj[cur] & adj[target] & ~visited) != 0;
    if (rem == 3) {
        uint32_t m = adj[cur] & ~visited;
        uint32_t nt = adj[target] & ~visited;
        while (m) {
            int a = __builtin_ctz(m);
            m &= m - 1;
            if (adj[a] & nt & ~(1u << a)) return true;
        }
        return false;
    }
    uint32_t m = adj[cur] & ~visited;
    while (m) {
        int nxt = __builtin_ctz(m);
        m &= m - 1;
        if (has_path_exact(adj, nxt, target, rem - 1, visited | (1u << nxt)))
            return true;
    }
    return false;
}

inline bool creates_forbidden_cycle(const uint32_t* adj, int u, int v, int edges_added) {
    if (TRI_FREE && (adj[u] & adj[v])) return true;
    if (edges_added >= 3 && has_path_len3(adj, u, v)) return true;
    if (edges_added >= 7 && has_path_exact(adj, u, v, 7, (1u << u) | (1u << v))) return true;
    if (N_VERTS >= 16 && edges_added >= 15 && has_path_exact(adj, u, v, 15, (1u << u) | (1u << v))) return true;
    if (N_VERTS >= 32 && edges_added >= 31 && has_path_exact(adj, u, v, 31, (1u << u) | (1u << v))) return true;
    return false;
}

void collect_tasks(State& st, int depth_limit, vector<State>& tasks, uint64_t& sols, vector<string>& witnesses) {
    if (st.edges_left == 0) {
        sols++;
        return;
    }
    int edges_added = TOTAL_EDGES - st.edges_left;
    if (edges_added >= depth_limit) {
        tasks.push_back(st);
        return;
    }
    int u = st.cur_u;
    int min_v = st.min_v;
    if (u == -1 || st.deg[u] == max_deg[u]) {
        u = -1;
        for (int i = 0; i < N_VERTS; i++) {
            if ((i == 0 || st.deg[i] > 0) && st.deg[i] < max_deg[i]) {
                u = i;
                break;
            }
        }
        if (u == -1) return;
        min_v = 0;
    }

    int cand[32], nc = 0;
    int p_lim = min(K_PORTS, st.next_port + 1);
    for (int v = max(min_v, 1); v < p_lim; v++) {
        if (v != u && st.deg[v] < max_deg[v] && !(st.adj[u] & (1u << v))) cand[nc++] = v;
    }
    int i_lim = min(N_VERTS, st.next_int + 1);
    for (int v = max(min_v, K_PORTS); v < i_lim; v++) {
        if (v != u && st.deg[v] < max_deg[v] && !(st.adj[u] & (1u << v))) cand[nc++] = v;
    }
    int need = max_deg[u] - st.deg[u];
    int rem_fresh_p = (st.next_port < K_PORTS) ? (K_PORTS - st.next_port - 1) : 0;
    int rem_fresh_i = (st.next_int < N_VERTS) ? (N_VERTS - st.next_int - 1) : 0;
    if (nc + rem_fresh_p + rem_fresh_i < need) return;

    for (int idx = 0; idx < nc; idx++) {
        int v = cand[idx];
        if (creates_forbidden_cycle(st.adj, u, v, edges_added)) continue;
        State nxt = st;
        nxt.adj[u] |= (1u << v);
        nxt.adj[v] |= (1u << u);
        nxt.deg[u]++;
        nxt.deg[v]++;
        if (v == nxt.next_port) nxt.next_port++;
        if (v == nxt.next_int) nxt.next_int++;
        nxt.edges_left--;
        if (nxt.deg[u] == max_deg[u]) {
            nxt.cur_u = -1;
            nxt.min_v = 0;
        } else {
            nxt.cur_u = u;
            nxt.min_v = v + 1;
        }
        collect_tasks(nxt, depth_limit, tasks, sols, witnesses);
    }
}

void dfs_worker(uint32_t* adj, uint8_t* deg, int cur_u, int min_v, int next_port, int next_int,
                int edges_left, uint64_t& nodes, uint64_t& sols, vector<string>& witnesses) {
    nodes++;
    if (edges_left == 0) {
        sols++;
        if (witnesses.size() < 5) {
            ostringstream oss;
            for (int i = 0; i < N_VERTS; i++) {
                for (int j = i + 1; j < N_VERTS; j++) {
                    if (adj[i] & (1u << j)) oss << i << "-" << j << " ";
                }
            }
            witnesses.push_back(oss.str());
        }
        return;
    }

    int u = cur_u;
    if (u == -1 || deg[u] == max_deg[u]) {
        u = -1;
        for (int i = 0; i < N_VERTS; i++) {
            if ((i == 0 || deg[i] > 0) && deg[i] < max_deg[i]) {
                u = i;
                break;
            }
        }
        if (u == -1) return;
        min_v = 0;
    }

    int cand[32], nc = 0;
    int p_lim = min(K_PORTS, next_port + 1);
    for (int v = max(min_v, 1); v < p_lim; v++) {
        if (v != u && deg[v] < max_deg[v] && !(adj[u] & (1u << v))) cand[nc++] = v;
    }
    int i_lim = min(N_VERTS, next_int + 1);
    for (int v = max(min_v, K_PORTS); v < i_lim; v++) {
        if (v != u && deg[v] < max_deg[v] && !(adj[u] & (1u << v))) cand[nc++] = v;
    }

    int need = max_deg[u] - deg[u];
    int rem_fresh_p = (next_port < K_PORTS) ? (K_PORTS - next_port - 1) : 0;
    int rem_fresh_i = (next_int < N_VERTS) ? (N_VERTS - next_int - 1) : 0;
    if (nc + rem_fresh_p + rem_fresh_i < need) return;

    int edges_added = TOTAL_EDGES - edges_left;
    for (int idx = 0; idx < nc; idx++) {
        int v = cand[idx];
        if (creates_forbidden_cycle(adj, u, v, edges_added)) continue;
        adj[u] |= (1u << v);
        adj[v] |= (1u << u);
        deg[u]++;
        deg[v]++;
        int np = (v == next_port) ? next_port + 1 : next_port;
        int ni = (v == next_int) ? next_int + 1 : next_int;
        if (deg[u] == max_deg[u]) {
            dfs_worker(adj, deg, -1, 0, np, ni, edges_left - 1, nodes, sols, witnesses);
        } else {
            dfs_worker(adj, deg, u, v + 1, np, ni, edges_left - 1, nodes, sols, witnesses);
        }
        adj[u] ^= (1u << v);
        adj[v] ^= (1u << u);
        deg[u]--;
        deg[v]--;
    }
}

int main(int argc, char** argv) {
    if (argc < 4) {
        cerr << "Usage: " << argv[0] << " N K_PORTS TRI_FREE(0/1) [SPLIT_DEPTH=12]\n";
        return 1;
    }
    N_VERTS = atoi(argv[1]);
    K_PORTS = atoi(argv[2]);
    TRI_FREE = atoi(argv[3]) != 0;
    int split_depth = (argc >= 5) ? atoi(argv[4]) : 12;

    int sum_deg = 0;
    for (int i = 0; i < N_VERTS; i++) {
        max_deg[i] = (i < K_PORTS) ? 2 : 3;
        sum_deg += max_deg[i];
    }
    if (sum_deg % 2 != 0) {
        cerr << "Parity error!\n";
        return 1;
    }
    TOTAL_EDGES = sum_deg / 2;

    State init;
    memset(&init, 0, sizeof(init));
    init.cur_u = 0;
    init.min_v = 1;
    init.next_port = 1;
    init.next_int = K_PORTS;
    init.edges_left = TOTAL_EDGES;

    auto t0 = chrono::steady_clock::now();
    vector<State> tasks;
    uint64_t total_sols = 0;
    vector<string> all_witnesses;
    collect_tasks(init, min(split_depth, TOTAL_EDGES), tasks, total_sols, all_witnesses);

    uint64_t total_nodes = 0;
    #pragma omp parallel
    {
        uint64_t local_nodes = 0;
        uint64_t local_sols = 0;
        vector<string> local_witnesses;
        #pragma omp for schedule(dynamic, 4)
        for (size_t i = 0; i < tasks.size(); i++) {
            uint32_t adj[32];
            uint8_t deg[32];
            memcpy(adj, tasks[i].adj, sizeof(adj));
            memcpy(deg, tasks[i].deg, sizeof(deg));
            dfs_worker(adj, deg, tasks[i].cur_u, tasks[i].min_v,
                       tasks[i].next_port, tasks[i].next_int, tasks[i].edges_left,
                       local_nodes, local_sols, local_witnesses);
        }
        #pragma omp critical
        {
            total_nodes += local_nodes;
            total_sols += local_sols;
            for (auto& w : local_witnesses) {
                if (all_witnesses.size() < 10) all_witnesses.push_back(w);
            }
        }
    }

    auto t1 = chrono::steady_clock::now();
    double sec = chrono::duration<double>(t1 - t0).count();
    cout << "SUMMARY N=" << N_VERTS << " K=" << K_PORTS << " tri_free=" << TRI_FREE
         << " tasks=" << tasks.size() << " nodes=" << total_nodes
         << " sols=" << total_sols << " threads=" << omp_get_max_threads()
         << " time=" << fixed << setprecision(3) << sec << "s\n";
    for (size_t i = 0; i < all_witnesses.size(); i++) {
        cout << "WITNESS[" << i << "]: " << all_witnesses[i] << "\n";
    }
    return 0;
}
