#include <bits/stdc++.h>
using namespace std;
using U = uint64_t;
using I = int64_t;

constexpr int N = 40;
constexpr U FULL = (1ULL << N) - 1;
static inline int pc(U x) { return __builtin_popcountll(x); }
static inline int ctz(U x) { return __builtin_ctzll(x); }

struct SoftGraph {
    array<U, N> a{};
    int edges = 0, triangles = 0, deg_excess = 0;

    inline int deg(int i) const { return pc(a[i]); }
    inline bool has(int i, int j) const { return (a[i] >> j) & 1ULL; }

    I count_indep(U p, int k) const {
        int c = pc(p);
        if (c < k) return 0;
        if (k == 0) return 1;
        if (k == 1) return c;
        if (k == 2) { I z = 0; while (p) { int i = ctz(p); p &= p - 1; z += pc(p & ~a[i]); } return z; }
        if (k == 3) {
            I z = 0;
            while (pc(p) >= 3) {
                int i = ctz(p); p &= p - 1; U q = p & ~a[i];
                while (pc(q) >= 2) { int j = ctz(q); q &= q - 1; z += pc(q & ~a[j]); }
            }
            return z;
        }
        I z = 0;
        while (pc(p) >= k) { int i = ctz(p); p &= p - 1; z += count_indep(p & ~a[i], k - 1); }
        return z;
    }

    inline I edge_i10_delta_abs(int u, int v) const {
        return count_indep(FULL & ~(a[u] | a[v] | (1ULL << u) | (1ULL << v)), 8);
    }

    void flip_edge(int u, int v, I& i10) {
        int cn = pc(a[u] & a[v]);
        I di10 = edge_i10_delta_abs(u, v);
        int du = deg(u), dv = deg(v);
        if (has(u, v)) {
            a[u] &= ~(1ULL << v); a[v] &= ~(1ULL << u);
            edges--; triangles -= cn;
            if (du > 9) deg_excess--; if (dv > 9) deg_excess--;
            i10 += di10;
        } else {
            a[u] |= (1ULL << v); a[v] |= (1ULL << u);
            edges++; triangles += cn;
            if (du >= 9) deg_excess++; if (dv >= 9) deg_excess++;
            i10 -= di10;
        }
    }

    bool sample_i10(U p, int k, U& out, mt19937_64& rng) const {
        if (k == 0) { out = 0; return true; }
        while (pc(p) >= k) {
            int c = pc(p), r = rng() % c;
            U t = p; while (r--) t &= t - 1;
            int i = ctz(t); p ^= (1ULL << i); U rest = 0;
            if (sample_i10(p & ~a[i], k - 1, rest, rng)) { out = rest | (1ULL << i); return true; }
        }
        return false;
    }

    bool verify_strict(I expected_i10) const {
        int e = 0, t = 0;
        for (int i = 0; i < N; i++) {
            if (has(i, i) || deg(i) > 9) return false;
            e += deg(i);
            for (int j = i + 1; j < N; j++) {
                if (has(i, j) != has(j, i)) return false;
                if (has(i, j)) t += pc(a[i] & a[j]);
            }
        }
        return (t == 0 && e / 2 == edges && count_indep(FULL, 10) == expected_i10);
    }

    void save(const string& path) const {
        ofstream f(path);
        for (int i = 0; i < N; i++) { for (int j = 0; j < N; j++) f << has(i, j); f << '\n'; }
    }
};

SoftGraph load_matrix(const string& path) {
    SoftGraph g; ifstream f(path); string line; int r = 0;
    while (getline(f, line) && r < N) {
        if (line.size() < N) continue;
        for (int c = r + 1; c < N; c++)
            if (line[c] == '1') { g.a[r] |= (1ULL << c); g.a[c] |= (1ULL << r); g.edges++; }
        r++;
    }
    return g;
}

SoftGraph random_180_graph(mt19937_64& rng) {
    SoftGraph g;
    vector<pair<int,int>> all;
    for (int i = 0; i < N; i++) for (int j = i + 1; j < N; j++) all.emplace_back(i, j);
    shuffle(all.begin(), all.end(), rng);
    for (int i = 0; i < 180; i++) {
        auto [u, v] = all[i];
        g.triangles += pc(g.a[u] & g.a[v]);
        if (g.deg(u) >= 9) g.deg_excess++;
        if (g.deg(v) >= 9) g.deg_excess++;
        g.a[u] |= (1ULL << v); g.a[v] |= (1ULL << u); g.edges++;
    }
    return g;
}

mutex g_mtx;
atomic<I> g_best_tf_i10{1000000000LL};
atomic<bool> g_found_witness{false};

void report_tf(const SoftGraph& g, I i10, const string& tag) {
    if (g.triangles != 0 || g.deg_excess != 0 || i10 >= g_best_tf_i10.load()) return;
    lock_guard<mutex> lk(g_mtx);
    if (i10 < g_best_tf_i10.load() && g.verify_strict(i10)) {
        g_best_tf_i10.store(i10); g.save("best_soft_tf.txt");
        cout << "[SOFT-TF NEW BEST] I10=" << i10 << " edges=" << g.edges << " tag=" << tag << endl;
        if (i10 == 0) { g_found_witness.store(true); g.save("WITNESS_40.txt"); }
    }
}

void soft_worker(int tid, uint64_t seed_val, int seconds, bool start_from_seed, const SoftGraph& seed31002) {
    mt19937_64 rng(seed_val);
    auto deadline = chrono::steady_clock::now() + chrono::seconds(seconds);
    auto init_graph = [&](int r, SoftGraph& g, I& i10) {
        if (start_from_seed && (r % 3 != 2)) {
            g = seed31002; i10 = g.count_indep(FULL, 10);
            int kick = 10 + (r % 5) * 6;
            for (int k = 0; k < kick; k++) { int u = rng() % N, v = rng() % N; if (u != v) g.flip_edge(u, v, i10); }
        } else { g = random_180_graph(rng); i10 = g.count_indep(FULL, 10); }
    };

    SoftGraph g; I i10 = 0; init_graph(0, g, i10);
    I local_best_tf = 1e18; uint64_t iter = 0, acc = 0, tf_hits = 0; int restarts = 0;
    const int CYCLE = 80000;
    while (chrono::steady_clock::now() < deadline && !g_found_witness.load()) {
        iter++; int step = iter % CYCLE;
        if (step == 0) { restarts++; init_graph(restarts, g, i10); }
        double phase = double(step) / CYCLE;
        double w_tri = 20.0 + 2500.0 * phase * phase * phase;
        double w_deg = 25.0 + 2000.0 * phase * phase * phase;
        double temp = 30.0 * pow(0.008, phase);
        double cur_E = w_tri * g.triangles + w_deg * g.deg_excess + double(i10);

        int u = -1, v = -1, r_op = rng() % 100;
        if (r_op < 40 && g.triangles > 0) {
            for (int tries = 0; tries < 20; tries++) {
                int x = rng() % N; U nb = g.a[x]; if (!nb) continue;
                int k = rng() % pc(nb); U t = nb; while (k--) t &= t - 1;
                int y = ctz(t);
                if (g.a[x] & g.a[y]) { u = x; v = y; break; }
            }
        } else if (r_op < 70 && g.triangles == 0 && i10 > 0) {
            U w = 0;
            if (g.sample_i10(FULL, 10, w, rng)) {
                int vs[10], cnt = 0; for (U t = w; t; t &= t - 1) vs[cnt++] = ctz(t);
                int a = rng() % cnt, b = rng() % (cnt - 1); if (b >= a) b++;
                u = vs[a]; v = vs[b];
            }
        }
        if (u < 0) { u = rng() % N; v = rng() % (N - 1); if (v >= u) v++; }

        bool present = g.has(u, v);
        int cn = pc(g.a[u] & g.a[v]);
        int new_tri = present ? (g.triangles - cn) : (g.triangles + cn);
        int du = g.deg(u), dv = g.deg(v), new_de = g.deg_excess;
        if (present) { if (du > 9) new_de--; if (dv > 9) new_de--; }
        else { if (du >= 9) new_de++; if (dv >= 9) new_de++; }
        if (present && (w_tri * new_tri + w_deg * new_de) - cur_E > 15.0 * temp) continue;

        I di10 = g.edge_i10_delta_abs(u, v);
        I new_i10 = present ? (i10 + di10) : (i10 - di10);
        double dE = (w_tri * new_tri + w_deg * new_de + double(new_i10)) - cur_E;
        if (dE <= 0.0 || generate_canonical<double, 53>(rng) < exp(-dE / temp)) {
            if (present) { g.a[u] &= ~(1ULL << v); g.a[v] &= ~(1ULL << u); g.edges--; }
            else { g.a[u] |= (1ULL << v); g.a[v] |= (1ULL << u); g.edges++; }
            g.triangles = new_tri; g.deg_excess = new_de; i10 = new_i10; acc++;
            if (g.triangles == 0 && g.deg_excess == 0) {
                tf_hits++;
                if (i10 < local_best_tf) { local_best_tf = i10; report_tf(g, i10, "soft_t" + to_string(tid)); }
            }
        }
    }
    lock_guard<mutex> lk(g_mtx);
    cout << "[Soft-TF Worker " << tid << "] iters=" << iter << " acc=" << acc
         << " tf_hits=" << tf_hits << " local_best_tf_I10=" << local_best_tf << endl;
}

int main(int argc, char** argv) {
    int seconds = (argc >= 2) ? stoi(argv[1]) : 60;
    SoftGraph seed31002 = load_matrix("seed31002.txt");
    thread t0(soft_worker, 0, 2026112701ULL, seconds, true, cref(seed31002));
    thread t1(soft_worker, 1, 2026112702ULL, seconds, false, cref(seed31002));
    t0.join(); t1.join();
    return 0;
}
