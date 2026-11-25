#include <iostream>
#include <vector>
#include <cstdint>
#include <chrono>
#include <cstring>
#include <string>
#include <atomic>
#ifdef _OPENMP
#include <omp.h>
#endif

using namespace std;

struct State {
    uint32_t adj[32];
    int deg[32];
    int first_unfilled;
};

struct PortEnumerator {
    int N;
    bool tri_free;
    int num_ports; // 2 or 3
    int target_deg[32];

    PortEnumerator(int n, bool tf, int ports) : N(n), tri_free(tf), num_ports(ports) {
        for (int i = 0; i < N; ++i) target_deg[i] = (i < ports) ? 2 : 3;
    }

    static inline void add_edge(State& s, int u, int v) {
        s.adj[u] |= (1u << v);
        s.adj[v] |= (1u << u);
        s.deg[u]++;
        s.deg[v]++;
    }

    static inline void rem_edge(State& s, int u, int v) {
        s.adj[u] &= ~(1u << v);
        s.adj[v] &= ~(1u << u);
        s.deg[u]--;
        s.deg[v]--;
    }

    inline bool creates_tri_or_c4(const State& s, int u, int v) const {
        if (tri_free && (s.adj[u] & s.adj[v])) return true;
        uint32_t nu = s.adj[u];
        uint32_t nv = s.adj[v];
        while (nu) {
            int a = __builtin_ctz(nu);
            nu &= nu - 1;
            if (s.adj[a] & (nv & ~(1u << a))) return true;
        }
        return false;
    }

    static bool creates_c8(const State& s, int u, int v) {
        struct Path3 { uint32_t mask; uint8_t end; };
        Path3 pu[16];
        int cu = 0;
        uint32_t forbid = (1u << u) | (1u << v);
        uint32_t n1 = s.adj[u] & ~forbid;
        while (n1) {
            int a = __builtin_ctz(n1); n1 &= n1 - 1;
            uint32_t m1 = forbid | (1u << a);
            uint32_t n2 = s.adj[a] & ~m1;
            while (n2) {
                int b = __builtin_ctz(n2); n2 &= n2 - 1;
                uint32_t m2 = m1 | (1u << b);
                uint32_t n3 = s.adj[b] & ~m2;
                while (n3) {
                    int c = __builtin_ctz(n3); n3 &= n3 - 1;
                    pu[cu++] = { (1u << a) | (1u << b) | (1u << c), (uint8_t)c };
                }
            }
        }
        if (cu == 0) return false;

        uint32_t v1 = s.adj[v] & ~forbid;
        while (v1) {
            int a = __builtin_ctz(v1); v1 &= v1 - 1;
            uint32_t ma = forbid | (1u << a);
            uint32_t v2 = s.adj[a] & ~ma;
            while (v2) {
                int b = __builtin_ctz(v2); v2 &= v2 - 1;
                uint32_t mb = ma | (1u << b);
                uint32_t v3 = s.adj[b] & ~mb;
                while (v3) {
                    int c = __builtin_ctz(v3); v3 &= v3 - 1;
                    uint32_t vm = (1u << a) | (1u << b) | (1u << c);
                    uint32_t adj_c = s.adj[c];
                    for (int i = 0; i < cu; ++i) {
                        if ((adj_c & (1u << pu[i].end)) && ((vm & pu[i].mask) == 0)) {
                            return true;
                        }
                    }
                }
            }
        }
        return false;
    }

    static bool has_cycle_len_dfs(const State& s, int start, int cur, int rem, uint32_t visited) {
        if (rem == 1) {
            return (s.adj[cur] & (1u << start)) != 0;
        }
        uint32_t cand = s.adj[cur] & ~visited;
        while (cand) {
            int nxt = __builtin_ctz(cand);
            cand &= cand - 1;
            if (nxt > start) {
                if (has_cycle_len_dfs(s, start, nxt, rem - 1, visited | (1u << nxt)))
                    return true;
            }
        }
        return false;
    }

    bool has_c16(const State& s) const {
        if (N < 16) return false;
        for (int st = 0; st <= N - 16; ++st) {
            if (has_cycle_len_dfs(s, st, st, 16, (1u << st))) return true;
        }
        return false;
    }

    bool is_connected(const State& s) const {
        uint32_t vis = 1u;
        uint32_t q = 1u;
        while (q) {
            int u = __builtin_ctz(q);
            q &= q - 1;
            uint32_t nxt = s.adj[u] & ~vis;
            vis |= nxt;
            q |= nxt;
        }
        return vis == ((1u << N) - 1u);
    }

    void collect_frontier(State& s, int stop_u, vector<State>& frontier) const {
        int u = s.first_unfilled;
        while (u < N && s.deg[u] == target_deg[u]) u++;
        if (u >= stop_u || u == N) {
            State copy = s;
            copy.first_unfilled = u;
            frontier.push_back(copy);
            return;
        }
        int min_v = u + 1;
        if (s.adj[u]) {
            int max_nbr = 31 - __builtin_clz(s.adj[u]);
            if (max_nbr + 1 > min_v) min_v = max_nbr + 1;
        }
        int need = target_deg[u] - s.deg[u];
        if (N - min_v < need) return;

        bool tried_fresh_internal = false;
        for (int v = min_v; v < N; ++v) {
            if (s.deg[v] == target_deg[v]) continue;
            if (num_ports == 2 && u == 0 && v == 1) continue; // non-adjacent ports for 2-port
            bool is_fresh_internal = (v >= num_ports && s.deg[v] == 0);
            if (is_fresh_internal) {
                if (tried_fresh_internal) continue;
                tried_fresh_internal = true;
            } else {
                if (creates_tri_or_c4(s, u, v)) continue;
                if (creates_c8(s, u, v)) continue;
            }
            int old_fu = s.first_unfilled;
            add_edge(s, u, v);
            s.first_unfilled = u;
            collect_frontier(s, stop_u, frontier);
            rem_edge(s, u, v);
            s.first_unfilled = old_fu;
        }
    }

    void dfs_worker(State& s, uint64_t& nodes, uint64_t& c4c8_free, uint64_t& pf_found, bool print_witness) const {
        nodes++;
        int u = s.first_unfilled;
        while (u < N && s.deg[u] == target_deg[u]) u++;
        if (u == N) {
            c4c8_free++;
            if (!has_c16(s) && is_connected(s)) {
                pf_found++;
                if (print_witness && pf_found <= 5) {
                    #pragma omp critical
                    {
                        cout << "FOUND POWER-FREE " << num_ports << "-PORT GADGET N=" << N << ":\n";
                        for (int i = 0; i < N; ++i) {
                            cout << "  " << i << ":";
                            for (int j = 0; j < N; ++j) if (s.adj[i] & (1u << j)) cout << " " << j;
                            cout << "\n";
                        }
                        cout.flush();
                    }
                }
            }
            return;
        }

        int min_v = u + 1;
        if (s.adj[u]) {
            int max_nbr = 31 - __builtin_clz(s.adj[u]);
            if (max_nbr + 1 > min_v) min_v = max_nbr + 1;
        }
        int need = target_deg[u] - s.deg[u];
        if (N - min_v < need) return;

        bool tried_fresh_internal = false;
        for (int v = min_v; v < N; ++v) {
            if (s.deg[v] == target_deg[v]) continue;
            if (num_ports == 2 && u == 0 && v == 1) continue;
            bool is_fresh_internal = (v >= num_ports && s.deg[v] == 0);
            if (is_fresh_internal) {
                if (tried_fresh_internal) continue;
                tried_fresh_internal = true;
            } else {
                if (creates_tri_or_c4(s, u, v)) continue;
                if (creates_c8(s, u, v)) continue;
            }
            int old_fu = s.first_unfilled;
            add_edge(s, u, v);
            s.first_unfilled = u;
            dfs_worker(s, nodes, c4c8_free, pf_found, print_witness);
            rem_edge(s, u, v);
            s.first_unfilled = old_fu;
        }
    }

    void run(int stop_u, bool print_witness = true) {
        auto t0 = chrono::steady_clock::now();
        vector<State> frontier;
        if (num_ports == 2) {
            // Case A: dist(0, 1) = 2 -> N(0) = {2, 3}, N(1) = {2, 4}
            State sA;
            memset(&sA, 0, sizeof(sA));
            add_edge(sA, 0, 2); add_edge(sA, 0, 3);
            add_edge(sA, 1, 2); add_edge(sA, 1, 4);
            sA.first_unfilled = 2;
            collect_frontier(sA, stop_u, frontier);

            // Case B: dist(0, 1) >= 3 -> N(0) = {2, 3}, N(1) = {4, 5}
            State sB;
            memset(&sB, 0, sizeof(sB));
            add_edge(sB, 0, 2); add_edge(sB, 0, 3);
            add_edge(sB, 1, 4); add_edge(sB, 1, 5);
            sB.first_unfilled = 2;
            collect_frontier(sB, stop_u, frontier);
        } else {
            State s0;
            memset(&s0, 0, sizeof(s0));
            s0.first_unfilled = 0;
            collect_frontier(s0, stop_u, frontier);
        }

        uint64_t total_nodes = 0, total_c4c8 = 0, total_pf = 0;
        #pragma omp parallel for schedule(dynamic, 1) reduction(+:total_nodes,total_c4c8,total_pf)
        for (size_t i = 0; i < frontier.size(); ++i) {
            State local_s = frontier[i];
            uint64_t n_loc = 0, c_loc = 0, p_loc = 0;
            dfs_worker(local_s, n_loc, c_loc, p_loc, print_witness);
            total_nodes += n_loc;
            total_c4c8 += c_loc;
            total_pf += p_loc;
        }
        auto t1 = chrono::steady_clock::now();
        double sec = chrono::duration<double>(t1 - t0).count();
        cout << "RESULT ports=" << num_ports
             << " N=" << N
             << " tri_free=" << tri_free
             << " frontier=" << frontier.size()
             << " nodes=" << total_nodes
             << " c4c8_free=" << total_c4c8
             << " power_free=" << total_pf
             << " time=" << sec << "s" << endl;
    }
};

int main(int argc, char** argv) {
    if (argc < 4) {
        cerr << "Usage: " << argv[0] << " <ports:2|3> <N> <tri_free:0|1> [stop_u]\n";
        return 1;
    }
    int ports = stoi(argv[1]);
    int N = stoi(argv[2]);
    bool tf = (stoi(argv[3]) != 0);
    int stop_u = (argc >= 5) ? stoi(argv[4]) : 7;
    PortEnumerator E(N, tf, ports);
    E.run(stop_u);
    return 0;
}
