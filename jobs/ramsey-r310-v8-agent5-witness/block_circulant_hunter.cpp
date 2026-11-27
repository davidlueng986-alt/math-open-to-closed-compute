#include <bits/stdc++.h>
using namespace std;
using U = uint64_t;
using I = int64_t;

constexpr int N = 40;
constexpr U FULL = (1ULL << N) - 1;
static inline int pc(U x) { return __builtin_popcountll(x); }
static inline int ctz(U x) { return __builtin_ctzll(x); }

I count_indep(const U* a, U p, int k) {
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
        z += count_indep(a, p & ~a[i], k - 1);
    }
    return z;
}

bool is_tf_and_deg9(const U* a) {
    for (int i = 0; i < N; i++) {
        if (pc(a[i]) > 9 || ((a[i] >> i) & 1ULL)) return false;
        U nb = a[i] >> (i + 1);
        while (nb) {
            int j = i + 1 + ctz(nb); nb &= nb - 1;
            if (a[i] & a[j]) return false;
        }
    }
    return true;
}

void save_adj(const string& path, const array<U, N>& a) {
    ofstream f(path);
    for (int i = 0; i < N; i++) {
        for (int j = 0; j < N; j++) f << ((a[i] >> j) & 1ULL);
        f << '\n';
    }
}

struct OrbitMove {
    bool same_block;
    int b1, b2, d;
    array<U, N> mask{};
    int deg_inc[N]{};
};

vector<OrbitMove> build_orbits(int B, int M) {
    vector<OrbitMove> obs;
    for (int b = 0; b < B; b++) {
        for (int d = 1; d <= M / 2; d++) {
            OrbitMove om; om.same_block = true; om.b1 = b; om.b2 = b; om.d = d;
            for (int x = 0; x < M; x++) {
                int u = b * M + x;
                om.mask[u] |= (1ULL << (b * M + (x + d) % M)) | (1ULL << (b * M + (x + M - d) % M));
            }
            for (int i = 0; i < N; i++) om.deg_inc[i] = pc(om.mask[i]);
            obs.push_back(om);
        }
    }
    for (int b1 = 0; b1 < B; b1++) {
        for (int b2 = b1 + 1; b2 < B; b2++) {
            for (int d = 0; d < M; d++) {
                OrbitMove om; om.same_block = false; om.b1 = b1; om.b2 = b2; om.d = d;
                for (int x = 0; x < M; x++) {
                    int u = b1 * M + x, v = b2 * M + (x + d) % M;
                    om.mask[u] |= (1ULL << v); om.mask[v] |= (1ULL << u);
                }
                for (int i = 0; i < N; i++) om.deg_inc[i] = pc(om.mask[i]);
                obs.push_back(om);
            }
        }
    }
    return obs;
}

void search_block_circulant(int B, int M, int seconds, uint64_t seed) {
    auto obs = build_orbits(B, M);
    int K = obs.size();
    mt19937_64 rng(seed);
    auto deadline = chrono::steady_clock::now() + chrono::seconds(seconds);

    auto can_add = [&](const array<U, N>& a, const OrbitMove& o) -> bool {
        if (pc(a[o.b1 * M]) + o.deg_inc[o.b1 * M] > 9) return false;
        if (!o.same_block && pc(a[o.b2 * M]) + o.deg_inc[o.b2 * M] > 9) return false;
        int u = o.b1 * M;
        U nu_new = o.mask[u], nu_all = a[u] | nu_new;
        for (U t = nu_new; t; t &= t - 1) {
            int v = ctz(t);
            if (nu_all & (a[v] | o.mask[v])) return false;
        }
        return true;
    };

    I best_i10 = 1e18;
    array<U, N> best_a{};
    int best_edges = 0;
    uint64_t evals = 0, restarts = 0;

    while (chrono::steady_clock::now() < deadline && best_i10 > 0) {
        restarts++;
        array<U, N> a{};
        vector<uint8_t> active(K, 0);
        int edges = 0;
        vector<int> perm(K); iota(perm.begin(), perm.end(), 0);
        shuffle(perm.begin(), perm.end(), rng);
        for (int idx : perm) {
            if (can_add(a, obs[idx])) {
                active[idx] = 1;
                for (int i = 0; i < N; i++) a[i] |= obs[idx].mask[i];
                edges += (obs[idx].same_block && obs[idx].d * 2 == M) ? (M / 2) : M;
            }
        }
        I cur_i10 = count_indep(a.data(), FULL, 10); evals++;
        if (cur_i10 < best_i10) { best_i10 = cur_i10; best_a = a; best_edges = edges; }

        for (int step = 0; step < 600 && chrono::steady_clock::now() < deadline && best_i10 > 0; step++) {
            array<U, N> h = a; vector<uint8_t> hact = active; int hedges = edges;
            int op = rng() % 3;
            if (op == 0) {
                vector<int> inact;
                for (int i = 0; i < K; i++) if (!hact[i]) inact.push_back(i);
                if (inact.empty()) continue;
                int pick = inact[rng() % inact.size()];
                vector<int> act_list;
                for (int i = 0; i < K; i++) if (hact[i]) act_list.push_back(i);
                shuffle(act_list.begin(), act_list.end(), rng);
                for (int rem : act_list) {
                    if (can_add(h, obs[pick])) break;
                    if (obs[rem].b1 == obs[pick].b1 || obs[rem].b2 == obs[pick].b1 ||
                        obs[rem].b1 == obs[pick].b2 || obs[rem].b2 == obs[pick].b2 || (rng() % 3 == 0)) {
                        hact[rem] = 0;
                        for (int i = 0; i < N; i++) h[i] &= ~obs[rem].mask[i];
                        hedges -= (obs[rem].same_block && obs[rem].d * 2 == M) ? (M / 2) : M;
                    }
                }
                if (can_add(h, obs[pick])) {
                    hact[pick] = 1;
                    for (int i = 0; i < N; i++) h[i] |= obs[pick].mask[i];
                    hedges += (obs[pick].same_block && obs[pick].d * 2 == M) ? (M / 2) : M;
                }
            } else {
                vector<int> act_list;
                for (int i = 0; i < K; i++) if (hact[i]) act_list.push_back(i);
                shuffle(act_list.begin(), act_list.end(), rng);
                int nrem = min<int>(act_list.size(), 1 + (rng() % 3));
                for (int r = 0; r < nrem; r++) {
                    int rem = act_list[r]; hact[rem] = 0;
                    for (int i = 0; i < N; i++) h[i] &= ~obs[rem].mask[i];
                    hedges -= (obs[rem].same_block && obs[rem].d * 2 == M) ? (M / 2) : M;
                }
            }
            shuffle(perm.begin(), perm.end(), rng);
            for (int idx : perm) {
                if (!hact[idx] && can_add(h, obs[idx])) {
                    hact[idx] = 1;
                    for (int i = 0; i < N; i++) h[i] |= obs[idx].mask[i];
                    hedges += (obs[idx].same_block && obs[idx].d * 2 == M) ? (M / 2) : M;
                }
            }
            I hi10 = count_indep(h.data(), FULL, 10); evals++;
            double phase = double(step) / 600.0;
            double temp = max(1.0, 0.05 * max<I>(20, cur_i10)) * (0.05 + 1.5 * (1.0 - phase));
            double eff_d = double(hi10 - cur_i10) + 0.5 * double(edges - hedges);
            if (eff_d <= 0 || generate_canonical<double, 53>(rng) < exp(-eff_d / temp)) {
                a = h; active = hact; edges = hedges; cur_i10 = hi10;
                if (cur_i10 < best_i10) { best_i10 = cur_i10; best_a = a; best_edges = edges; }
            }
        }
    }
    cout << "[Block-Circulant " << B << "x" << M << "] orbits=" << K
         << " evals=" << evals << " restarts=" << restarts
         << " best_I10=" << best_i10 << " edges=" << best_edges
         << " valid=" << is_tf_and_deg9(best_a.data()) << "\n" << flush;
    save_adj("best_bc_" + to_string(B) + "x" + to_string(M) + ".txt", best_a);
}

int main() {
    { thread t0(search_block_circulant, 4, 10, 20, 1001); thread t1(search_block_circulant, 5, 8, 20, 1002); t0.join(); t1.join(); }
    { thread t0(search_block_circulant, 8, 5, 25, 1003); thread t1(search_block_circulant, 10, 4, 25, 1004); t0.join(); t1.join(); }
    return 0;
}
