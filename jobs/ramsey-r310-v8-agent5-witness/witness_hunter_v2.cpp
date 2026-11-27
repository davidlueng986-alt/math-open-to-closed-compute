#include <bits/stdc++.h>
using namespace std;
using U = uint64_t;
using I = int64_t;

constexpr int N = 40;
constexpr U FULL = (1ULL << N) - 1;
static inline int pc(U x) { return __builtin_popcountll(x); }
static inline int ctz(U x) { return __builtin_ctzll(x); }

struct Graph {
    array<U, N> a{};
    int edges = 0;

    inline int deg(int i) const { return pc(a[i]); }
    inline bool has(int i, int j) const { return (a[i] >> j) & 1ULL; }
    inline void add_edge(int i, int j) { a[i] |= (1ULL << j); a[j] |= (1ULL << i); edges++; }
    inline void del_edge(int i, int j) { a[i] &= ~(1ULL << j); a[j] &= ~(1ULL << i); edges--; }

    I count_indep(U p, int k) const {
        int c = pc(p);
        if (c < k) return 0;
        if (k == 0) return 1;
        if (k == 1) return c;
        if (k == 2) {
            I z = 0;
            while (p) { int i = ctz(p); p &= p - 1; z += pc(p & ~a[i]); }
            return z;
        }
        if (k == 3) {
            I z = 0;
            while (pc(p) >= 3) {
                int i = ctz(p); p &= p - 1;
                U q = p & ~a[i];
                while (pc(q) >= 2) { int j = ctz(q); q &= q - 1; z += pc(q & ~a[j]); }
            }
            return z;
        }
        I z = 0;
        while (pc(p) >= k) {
            int i = ctz(p); p &= p - 1;
            z += count_indep(p & ~a[i], k - 1);
        }
        return z;
    }

    inline I edge_delta_abs(int u, int v) const {
        return count_indep(FULL & ~(a[u] | a[v] | (1ULL << u) | (1ULL << v)), 8);
    }
    inline void add_edge_inc(int u, int v, I& i10) { i10 -= edge_delta_abs(u, v); add_edge(u, v); }
    inline void del_edge_inc(int u, int v, I& i10) { del_edge(u, v); i10 += edge_delta_abs(u, v); }

    void collect_i10s(U p, int k, U cur, vector<U>& out, size_t limit) const {
        if (out.size() >= limit) return;
        int c = pc(p);
        if (c < k) return;
        if (k == 0) { out.push_back(cur); return; }
        if (k == 1) {
            while (p && out.size() < limit) { int i = ctz(p); p &= p - 1; out.push_back(cur | (1ULL << i)); }
            return;
        }
        while (pc(p) >= k && out.size() < limit) {
            int i = ctz(p); p &= p - 1;
            collect_i10s(p & ~a[i], k - 1, cur | (1ULL << i), out, limit);
        }
    }

    bool sample_i10(U p, int k, U& out, mt19937_64& rng) const {
        if (k == 0) { out = 0; return true; }
        while (pc(p) >= k) {
            int c = pc(p), r = rng() % c;
            U t = p; while (r--) t &= t - 1;
            int i = ctz(t); p ^= (1ULL << i);
            U rest = 0;
            if (sample_i10(p & ~a[i], k - 1, rest, rng)) { out = rest | (1ULL << i); return true; }
        }
        return false;
    }

    bool valid(int max_deg = 9) const {
        int e = 0;
        for (int i = 0; i < N; i++) {
            if (has(i, i) || deg(i) > max_deg) return false;
            e += deg(i);
            for (int j = i + 1; j < N; j++) {
                if (has(i, j) != has(j, i)) return false;
                if (has(i, j) && (a[i] & a[j])) return false;
            }
        }
        return e / 2 == edges;
    }

    void save(const string& path) const {
        ofstream f(path);
        for (int i = 0; i < N; i++) {
            for (int j = 0; j < N; j++) f << has(i, j);
            f << '\n';
        }
    }

    void greedy_refill(I& i10, mt19937_64& rng, int max_adds = 40) {
        for (int step = 0; step < max_adds; step++) {
            int bu = -1, bv = -1; I bd = -1; int ties = 0;
            for (int u = 0; u < N; u++) {
                if (deg(u) >= 9) continue;
                U cand = FULL & ~((1ULL << (u + 1)) - 1) & ~a[u];
                while (cand) {
                    int v = ctz(cand); cand &= cand - 1;
                    if (deg(v) >= 9 || (a[u] & a[v])) continue;
                    I d = edge_delta_abs(u, v);
                    if (d > bd) { bd = d; bu = u; bv = v; ties = 1; }
                    else if (d == bd && rng() % (++ties) == 0) { bu = u; bv = v; }
                }
            }
            if (bu < 0) break;
            i10 -= bd; add_edge(bu, bv);
            if (i10 == 0) break;
        }
    }
};

Graph load_matrix(const string& path) {
    Graph g; ifstream f(path); string line; int r = 0;
    while (getline(f, line) && r < N) {
        if (line.size() < N) continue;
        for (int c = r + 1; c < N; c++) if (line[c] == '1') g.add_edge(r, c);
        r++;
    }
    return g;
}

Graph load_g6(const string& path, int expected_n) {
    ifstream f(path); string s; getline(f, s);
    while (!s.empty() && (s.back() == '\r' || s.back() == '\n')) s.pop_back();
    int n = s[0] - 63;
    if (n != expected_n) throw runtime_error("bad g6");
    Graph g; int b = 0;
    for (int j = 0; j < n; j++)
        for (int i = 0; i < j; i++, b++)
            if (((s[1 + b / 6] - 63) >> (5 - b % 6)) & 1) g.add_edge(i, j);
    return g;
}

Graph random_tf_start(mt19937_64& rng) {
    Graph g;
    vector<pair<int,int>> pairs;
    for (int i = 0; i < N; i++) for (int j = i + 1; j < N; j++) pairs.emplace_back(i, j);
    shuffle(pairs.begin(), pairs.end(), rng);
    for (auto [u, v] : pairs)
        if (g.deg(u) < 9 && g.deg(v) < 9 && !(g.a[u] & g.a[v])) g.add_edge(u, v);
    return g;
}

void audit_2switch_barrier(const Graph& g0, const string& name) {
    Graph g = g0;
    I base = g.count_indep(FULL, 10);
    vector<pair<int,int>> es;
    for (int i = 0; i < N; i++) {
        U nb = g.a[i] >> (i + 1);
        while (nb) { int j = i + 1 + ctz(nb); nb &= nb - 1; es.emplace_back(i, j); }
    }
    int valid_sw = 0;
    I min_i10 = 1e18, max_i10 = -1;
    for (size_t i = 0; i < es.size(); i++) {
        auto [a, b] = es[i];
        for (size_t j = i + 1; j < es.size(); j++) {
            auto [c, d] = es[j];
            if (a == c || a == d || b == c || b == d) continue;
            for (int flip = 0; flip < 2; flip++) {
                int x = flip ? d : c, y = flip ? c : d;
                if (g.has(a, x) || g.has(b, y) || g.has(b, x) || g.has(a, y)) continue;
                U na = g.a[a] & ~(1ULL << b), nb = g.a[b] & ~(1ULL << a);
                U nx = g.a[x] & ~(1ULL << y), ny = g.a[y] & ~(1ULL << x);
                if ((na & nx) || (nb & ny)) continue;
                valid_sw++;
                I cur = base;
                g.del_edge_inc(a, b, cur); g.del_edge_inc(c, d, cur);
                g.add_edge_inc(a, x, cur); g.add_edge_inc(b, y, cur);
                g.del_edge(a, x); g.del_edge(b, y); g.add_edge(a, b); g.add_edge(c, d);
                min_i10 = min(min_i10, cur); max_i10 = max(max_i10, cur);
            }
        }
    }
    cout << "[2-Switch Barrier Audit: " << name << "] base_I10=" << base
         << " valid_2switches=" << valid_sw
         << " min_neighbor_I10=" << min_i10 << " max_neighbor_I10=" << max_i10 << "\n" << flush;
}

mutex g_mtx;
atomic<I> g_best_i10{1000000000LL};
atomic<bool> g_found_witness{false};
string g_best_tag;

void report_candidate(const Graph& g, I i10, const string& tag) {
    lock_guard<mutex> lk(g_mtx);
    if (i10 < g_best_i10.load()) {
        if (!g.valid(9)) return;
        I exact = g.count_indep(FULL, 10);
        if (exact != i10) return;
        g_best_i10.store(exact); g_best_tag = tag;
        g.save("best_v2.txt");
        cout << "[NEW GLOBAL BEST] I10=" << exact << " edges=" << g.edges << " tag=" << tag << endl;
        if (exact == 0) { g_found_witness.store(true); g.save("WITNESS_40.txt"); }
    }
}

bool try_best_3switch(Graph& g, I& i10, mt19937_64& rng, int trials, double temp) {
    vector<pair<int,int>> es; es.reserve(180);
    for (int i = 0; i < N; i++) {
        U nb = g.a[i] >> (i + 1);
        while (nb) { int j = i + 1 + ctz(nb); nb &= nb - 1; es.emplace_back(i, j); }
    }
    if (es.size() < 3) return false;
    int best_v[6]; I best_delta = 1e18; bool found = false;
    for (int t = 0; t < trials; t++) {
        auto [a1, b1] = es[rng() % es.size()];
        auto [a2, b2] = es[rng() % es.size()];
        auto [a3, b3] = es[rng() % es.size()];
        if (rng() & 1) swap(a1, b1);
        if (rng() & 1) swap(a2, b2);
        if (rng() & 1) swap(a3, b3);
        U m = (1ULL<<a1)|(1ULL<<b1)|(1ULL<<a2)|(1ULL<<b2)|(1ULL<<a3)|(1ULL<<b3);
        if (pc(m) != 6) continue;
        if (g.has(a1, b2) || g.has(a2, b3) || g.has(a3, b1)) continue;
        g.del_edge(a1, b1); g.del_edge(a2, b2); g.del_edge(a3, b3);
        bool tf = !(g.a[a1] & g.a[b2]);
        if (tf) { g.add_edge(a1, b2); tf = !(g.a[a2] & g.a[b3]); }
        else { g.add_edge(a1, b1); g.add_edge(a2, b2); g.add_edge(a3, b3); continue; }
        if (tf) { g.add_edge(a2, b3); tf = !(g.a[a3] & g.a[b1]); }
        else { g.del_edge(a1, b2); g.add_edge(a1, b1); g.add_edge(a2, b2); g.add_edge(a3, b3); continue; }
        g.del_edge(a2, b3); g.del_edge(a1, b2);
        g.add_edge(a1, b1); g.add_edge(a2, b2); g.add_edge(a3, b3);
        if (!tf) continue;

        I cur = i10;
        g.del_edge_inc(a1, b1, cur); g.del_edge_inc(a2, b2, cur); g.del_edge_inc(a3, b3, cur);
        g.add_edge_inc(a1, b2, cur); g.add_edge_inc(a2, b3, cur); g.add_edge_inc(a3, b1, cur);
        I delta = cur - i10;
        g.del_edge(a1, b2); g.del_edge(a2, b3); g.del_edge(a3, b1);
        g.add_edge(a1, b1); g.add_edge(a2, b2); g.add_edge(a3, b3);

        if (delta < best_delta) {
            best_delta = delta; found = true;
            best_v[0]=a1; best_v[1]=b1; best_v[2]=a2; best_v[3]=b2; best_v[4]=a3; best_v[5]=b3;
            if (delta < 0) break;
        }
    }
    if (!found) return false;
    if (best_delta <= 0 || generate_canonical<double, 53>(rng) < exp(-double(best_delta) / max(0.3, temp))) {
        g.del_edge_inc(best_v[0], best_v[1], i10);
        g.del_edge_inc(best_v[2], best_v[3], i10);
        g.del_edge_inc(best_v[4], best_v[5], i10);
        g.add_edge_inc(best_v[0], best_v[3], i10);
        g.add_edge_inc(best_v[2], best_v[5], i10);
        g.add_edge_inc(best_v[4], best_v[1], i10);
        return true;
    }
    return false;
}

bool try_best_2switch(Graph& g, I& i10, mt19937_64& rng, U focus_mask, int trials,
                      const array<array<uint64_t, N>, N>& tabu, uint64_t iter, double temp) {
    vector<pair<int,int>> es; es.reserve(180);
    for (int i = 0; i < N; i++) {
        U nb = g.a[i] >> (i + 1);
        while (nb) { int j = i + 1 + ctz(nb); nb &= nb - 1; es.emplace_back(i, j); }
    }
    if (es.size() < 2) return false;
    int ba = -1, bb = -1, bc = -1, bd = -1; I best_delta = 1e18;
    for (int t = 0; t < trials; t++) {
        auto [a, b] = es[rng() % es.size()];
        auto [c, d] = es[rng() % es.size()];
        if (a == c || a == d || b == c || b == d) continue;
        if (focus_mask && (t % 3 != 0))
            if (!(((focus_mask >> a) | (focus_mask >> b) | (focus_mask >> c) | (focus_mask >> d)) & 1ULL)) continue;
        if (rng() & 1) swap(c, d);
        if (g.has(a, c) || g.has(b, d) || g.has(b, c) || g.has(a, d)) continue;
        U na = g.a[a] & ~(1ULL << b), nb = g.a[b] & ~(1ULL << a);
        U nc = g.a[c] & ~(1ULL << d), nd = g.a[d] & ~(1ULL << c);
        if ((na & nc) || (nb & nd)) continue;
        bool is_tabu = (tabu[a][c] > iter || tabu[b][d] > iter);

        I cur = i10;
        g.del_edge_inc(a, b, cur); g.del_edge_inc(c, d, cur);
        g.add_edge_inc(a, c, cur); g.add_edge_inc(b, d, cur);
        I delta = cur - i10;
        g.del_edge(a, c); g.del_edge(b, d); g.add_edge(a, b); g.add_edge(c, d);

        if (is_tabu && i10 + delta >= g_best_i10.load()) continue;
        if (delta < best_delta) {
            best_delta = delta; ba = a; bb = b; bc = c; bd = d;
            if (delta < 0) break;
        }
    }
    if (ba < 0) return false;
    if (best_delta <= 0 || generate_canonical<double, 53>(rng) < exp(-double(best_delta) / max(0.3, temp))) {
        g.del_edge_inc(ba, bb, i10); g.del_edge_inc(bc, bd, i10);
        g.add_edge_inc(ba, bc, i10); g.add_edge_inc(bb, bd, i10);
        return true;
    }
    return false;
}

bool try_i10_break(Graph& g, I& i10, mt19937_64& rng, double temp,
                   array<array<uint64_t, N>, N>& tabu, uint64_t iter) {
    U w = 0;
    if (!g.sample_i10(FULL, 10, w, rng)) { i10 = 0; return true; }
    int vs[10], cnt = 0;
    for (U t = w; t; t &= t - 1) vs[cnt++] = ctz(t);
    vector<tuple<int,int,int>> cands;
    for (int i = 0; i < cnt; i++)
        for (int j = i + 1; j < cnt; j++)
            cands.emplace_back(pc(g.a[vs[i]] & g.a[vs[j]]), vs[i], vs[j]);
    sort(cands.begin(), cands.end());
    int pick_range = min<int>(cands.size(), (rng() % 3 == 0) ? 15 : 5);
    auto [cn, u, v] = cands[rng() % pick_range];

    Graph h = g; I hi10 = i10;
    U common = h.a[u] & h.a[v];
    while (common) {
        int z = ctz(common); common &= common - 1;
        I du = h.edge_delta_abs(u, z), dv = h.edge_delta_abs(v, z);
        if (du < dv || (du == dv && (rng() & 1))) h.del_edge_inc(u, z, hi10);
        else h.del_edge_inc(v, z, hi10);
    }
    auto trim = [&](int x) {
        if (h.deg(x) >= 9) {
            int bz = -1; I bd = 1e18;
            for (U nb = h.a[x]; nb; nb &= nb - 1) {
                int z = ctz(nb); I d = h.edge_delta_abs(x, z);
                if (d < bd || (d == bd && (rng() & 1))) { bd = d; bz = z; }
            }
            if (bz >= 0) h.del_edge_inc(x, bz, hi10);
        }
    };
    trim(u); trim(v);
    h.add_edge_inc(u, v, hi10);
    h.greedy_refill(hi10, rng, 15);

    double eff_delta = double(hi10 - i10) + 0.25 * double(g.edges - h.edges);
    if (eff_delta <= 0 || generate_canonical<double, 53>(rng) < exp(-eff_delta / max(0.35, temp))) {
        g = h; i10 = hi10;
        tabu[u][v] = tabu[v][u] = iter + 10 + (rng() % 15);
        return true;
    }
    return false;
}

void ruin_and_recreate(Graph& g, I& i10, mt19937_64& rng, int k_del) {
    vector<pair<int,int>> es;
    for (int i = 0; i < N; i++) {
        U nb = g.a[i] >> (i + 1);
        while (nb) { int j = i + 1 + ctz(nb); nb &= nb - 1; es.emplace_back(i, j); }
    }
    shuffle(es.begin(), es.end(), rng);
    int n_del = min<int>(k_del, es.size());
    for (int i = 0; i < n_del; i++) g.del_edge_inc(es[i].first, es[i].second, i10);
    g.greedy_refill(i10, rng, n_del + 12);
}

void worker(int tid, uint64_t seed_val, int seconds, const string& mode,
            const Graph& seed31002, const Graph& exoo39, const Graph& kalb35, const Graph& bc4x10) {
    mt19937_64 rng(seed_val);
    auto deadline = chrono::steady_clock::now() + chrono::seconds(seconds);

    auto make_start = [&](int r) -> Graph {
        if (mode == "seed31002_deep") {
            Graph g = seed31002; I sc = g.count_indep(FULL, 10);
            ruin_and_recreate(g, sc, rng, 8 + (r % 6) * 5);
            return g;
        } else {
            int sub = r % 4;
            if (sub == 0) { Graph g = exoo39; I sc = g.count_indep(FULL, 10); g.greedy_refill(sc, rng, 15); return g; }
            if (sub == 1) { Graph g = bc4x10; I sc = g.count_indep(FULL, 10); ruin_and_recreate(g, sc, rng, 10 + (rng() % 12)); return g; }
            if (sub == 2) { Graph g = kalb35; I sc = g.count_indep(FULL, 10); g.greedy_refill(sc, rng, 50); return g; }
            return random_tf_start(rng);
        }
    };

    Graph g = make_start(0);
    I i10 = g.count_indep(FULL, 10);
    Graph local_best = g; I local_best_i10 = i10;
    report_candidate(g, i10, mode + "_t" + to_string(tid) + "_start");

    array<array<uint64_t, N>, N> tabu{};
    uint64_t iter = 0, acc = 0, last_imp = 0;
    int restarts = 0;

    while (chrono::steady_clock::now() < deadline && !g_found_witness.load()) {
        iter++;
        U focus = 0;
        if (i10 > 0 && i10 <= 80) {
            vector<U> sets; g.collect_i10s(FULL, 10, 0, sets, 25);
            for (U s : sets) focus |= s;
        }
        double phase = double(iter % 2500) / 2500.0;
        double base_t = (i10 <= 25) ? 3.0 : max(2.5, 0.035 * i10);
        double temp = base_t * (0.04 + 1.6 * (1.0 - phase));

        int op = rng() % 100;
        bool ok = false;
        if (op < 48) ok = try_i10_break(g, i10, rng, temp, tabu, iter);
        else if (op < 78) ok = try_best_2switch(g, i10, rng, focus, 50, tabu, iter, temp);
        else ok = try_best_3switch(g, i10, rng, 35, temp);
        if (ok) acc++;

        if (i10 < local_best_i10) {
            local_best = g; local_best_i10 = i10; last_imp = iter;
            report_candidate(g, i10, mode + "_t" + to_string(tid) + "_it" + to_string(iter));
        }
        if (iter - last_imp > 4500) {
            restarts++; last_imp = iter;
            if (restarts % 2 == 0) { g = make_start(restarts); i10 = g.count_indep(FULL, 10); }
            else { g = local_best; i10 = local_best_i10; ruin_and_recreate(g, i10, rng, 8 + (rng() % 18)); }
        }
    }
    lock_guard<mutex> lk(g_mtx);
    cout << "[Worker " << tid << " " << mode << "] iters=" << iter << " acc=" << acc
         << " restarts=" << restarts << " local_best_I10=" << local_best_i10 << endl;
}

int main(int argc, char** argv) {
    int seconds = (argc >= 2) ? stoi(argv[1]) : 120;
    Graph seed31002 = load_matrix("seed31002.txt");
    Graph exoo39 = load_g6("exoo39.g6", 39);
    Graph kalb35 = load_g6("kalbfleisch35.g6", 35);
    Graph bc4x10 = load_matrix("best_bc_4x10.txt");
    audit_2switch_barrier(seed31002, "seed31002");
    audit_2switch_barrier(bc4x10, "best_bc_4x10");
    thread t0(worker, 0, 987654321ULL, seconds, "seed31002_deep", cref(seed31002), cref(exoo39), cref(kalb35), cref(bc4x10));
    thread t1(worker, 1, 123456789ULL, seconds, "portfolio_fresh", cref(seed31002), cref(exoo39), cref(kalb35), cref(bc4x10));
    t0.join(); t1.join();
    return 0;
}
