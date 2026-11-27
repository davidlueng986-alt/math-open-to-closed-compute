#include <bits/stdc++.h>
using namespace std;
using U = uint64_t;
using I = int64_t;

constexpr int N = 40;
constexpr U FULL = (1ULL << N) - 1;

static inline int pc(U x) { return __builtin_popcountll(x); }
static inline int ctz(U x) { return __builtin_ctzll(x); }

I count_indep(const U* a, U p, int k) {
    if (k == 0) return 1;
    int c = pc(p);
    if (c < k) return 0;
    if (k == 1) return c;
    if (k == 2) {
        I z = 0;
        while (p) {
            int i = ctz(p);
            p &= p - 1;
            z += pc(p & ~a[i]);
        }
        return z;
    }
    I z = 0;
    while (pc(p) >= k) {
        int i = ctz(p);
        p &= p - 1;
        z += count_indep(a, p & ~a[i], k - 1);
    }
    return z;
}

bool has_indep(const U* a, U p, int k) {
    if (k == 0) return true;
    int c = pc(p);
    if (c < k) return false;
    if (k == 1) return true;
    if (k == 2) {
        while (p) {
            int i = ctz(p);
            p &= p - 1;
            if (p & ~a[i]) return true;
        }
        return false;
    }
    while (pc(p) >= k) {
        int i = ctz(p);
        p &= p - 1;
        if (has_indep(a, p & ~a[i], k - 1)) return true;
    }
    return false;
}

I count_i10_vt(const U* a) {
    return 4 * count_indep(a, FULL & ~(1ULL | a[0]), 9);
}

bool is_triangle_free(const U* a, int n = 40) {
    for (int i = 0; i < n; i++) {
        if ((a[i] >> i) & 1ULL) return false;
        U nb = a[i];
        while (nb) {
            int j = ctz(nb);
            nb &= nb - 1;
            if (j > i && (a[i] & a[j])) return false;
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

struct Group40 {
    string name;
    int mul[40][40];
    int inv[40];

    bool verify_group() {
        for (int a = 0; a < 40; a++)
            if (mul[0][a] != a || mul[a][0] != a) return false;
        for (int a = 0; a < 40; a++) {
            int found = -1;
            for (int b = 0; b < 40; b++)
                if (mul[a][b] == 0 && mul[b][a] == 0) { found = b; break; }
            if (found < 0) return false;
            inv[a] = found;
        }
        for (int a = 0; a < 40; a++)
            for (int b = 0; b < 40; b++)
                for (int c = 0; c < 40; c++)
                    if (mul[mul[a][b]][c] != mul[a][mul[b][c]]) return false;
        return true;
    }
};

struct Group8 {
    string name;
    int mul[8][8];
};

vector<Group8> make_groups8() {
    vector<Group8> gs;
    {
        Group8 g; g.name = "C8";
        for (int a = 0; a < 8; a++)
            for (int b = 0; b < 8; b++) g.mul[a][b] = (a + b) % 8;
        gs.push_back(g);
    }
    {
        Group8 g; g.name = "C4xC2";
        for (int a1 = 0; a1 < 4; a1++) for (int b1 = 0; b1 < 2; b1++)
            for (int a2 = 0; a2 < 4; a2++) for (int b2 = 0; b2 < 2; b2++)
                g.mul[a1*2+b1][a2*2+b2] = ((a1+a2)%4)*2 + ((b1+b2)%2);
        gs.push_back(g);
    }
    {
        Group8 g; g.name = "C2^3";
        for (int a = 0; a < 8; a++)
            for (int b = 0; b < 8; b++) g.mul[a][b] = a ^ b;
        gs.push_back(g);
    }
    {
        Group8 g; g.name = "D4";
        for (int a1 = 0; a1 < 4; a1++) for (int b1 = 0; b1 < 2; b1++)
            for (int a2 = 0; a2 < 4; a2++) for (int b2 = 0; b2 < 2; b2++) {
                int a3 = b1 ? (a1 + 4 - a2) % 4 : (a1 + a2) % 4;
                int b3 = b1 ^ b2;
                g.mul[a1*2+b1][a2*2+b2] = a3*2 + b3;
            }
        gs.push_back(g);
    }
    {
        Group8 g; g.name = "Q8";
        auto qmul = [](int x, int y) {
            int bx = x / 2, sx = x % 2;
            int by = y / 2, sy = y % 2;
            int s = sx ^ sy, b = 0;
            if (bx == 0) b = by;
            else if (by == 0) b = bx;
            else if (bx == by) { b = 0; s ^= 1; }
            else if (bx == 1 && by == 2) b = 3;
            else if (bx == 2 && by == 3) b = 1;
            else if (bx == 3 && by == 1) b = 2;
            else if (bx == 2 && by == 1) { b = 3; s ^= 1; }
            else if (bx == 3 && by == 2) { b = 1; s ^= 1; }
            else if (bx == 1 && by == 3) { b = 2; s ^= 1; }
            return b * 2 + s;
        };
        for (int a = 0; a < 8; a++)
            for (int b = 0; b < 8; b++) g.mul[a][b] = qmul(a, b);
        gs.push_back(g);
    }
    return gs;
}

Group40 make_semidirect(const string& name, const Group8& H, const array<int, 8>& phi) {
    Group40 G; G.name = name;
    for (int c1 = 0; c1 < 5; c1++) for (int h1 = 0; h1 < 8; h1++)
        for (int c2 = 0; c2 < 5; c2++) for (int h2 = 0; h2 < 8; h2++)
            G.mul[c1*8 + h1][c2*8 + h2] = ((c1 + phi[h1] * c2) % 5)*8 + H.mul[h1][h2];
    if (!G.verify_group()) { cerr << "INVALID GROUP: " << name << endl; exit(1); }
    return G;
}

vector<Group40> make_all_14_groups40() {
    auto H = make_groups8();
    vector<Group40> res;
    array<int, 8> triv = {1,1,1,1,1,1,1,1};
    res.push_back(make_semidirect("1: C40 (C5 x C8)", H[0], triv));
    res.push_back(make_semidirect("2: C20 x C2 (C5 x C4 x C2)", H[1], triv));
    res.push_back(make_semidirect("3: C10 x C2^2 (C5 x C2^3)", H[2], triv));
    {
        array<int, 8> p2; for (int i = 0; i < 8; i++) p2[i] = (i % 2 == 0) ? 1 : 4;
        res.push_back(make_semidirect("4: C5 |x_2 C8", H[0], p2));
        array<int, 8> p4; int v = 1; for (int i = 0; i < 8; i++) { p4[i] = v; v = (v * 2) % 5; }
        res.push_back(make_semidirect("5: C5 |x_4 C8", H[0], p4));
    }
    {
        array<int, 8> p;
        for (int a = 0; a < 4; a++) for (int b = 0; b < 2; b++) p[a*2+b] = (a % 2 == 0) ? 1 : 4;
        res.push_back(make_semidirect("6: (C5 |x_2 C4) x C2", H[1], p));
        for (int a = 0; a < 4; a++) for (int b = 0; b < 2; b++) p[a*2+b] = (b == 0) ? 1 : 4;
        res.push_back(make_semidirect("7: C4 x D5", H[1], p));
        int pw[4] = {1, 2, 4, 3};
        for (int a = 0; a < 4; a++) for (int b = 0; b < 2; b++) p[a*2+b] = pw[a];
        res.push_back(make_semidirect("8: (C5 |x_4 C4) x C2", H[1], p));
    }
    {
        array<int, 8> p; for (int i = 0; i < 8; i++) p[i] = (i & 1) ? 4 : 1;
        res.push_back(make_semidirect("9: D5 x C2^2", H[2], p));
    }
    {
        res.push_back(make_semidirect("10: C5 x D4", H[3], triv));
        array<int, 8> p;
        for (int a = 0; a < 4; a++) for (int b = 0; b < 2; b++) p[a*2+b] = (b == 0) ? 1 : 4;
        res.push_back(make_semidirect("11: D20 (C5 |x_{s->-1} D4)", H[3], p));
        for (int a = 0; a < 4; a++) for (int b = 0; b < 2; b++) p[a*2+b] = (a % 2 == 0) ? 1 : 4;
        res.push_back(make_semidirect("12: C5 |x_{r->-1,s->1} D4", H[3], p));
    }
    {
        res.push_back(make_semidirect("13: C5 x Q8", H[4], triv));
        array<int, 8> p;
        for (int b = 0; b < 4; b++) for (int s = 0; s < 2; s++) p[b*2+s] = (b == 0 || b == 1) ? 1 : 4;
        res.push_back(make_semidirect("14: C5 |x Q8", H[4], p));
    }
    return res;
}

void scan_cayley(const vector<Group40>& groups) {
    cout << "=== PART 1: EXHAUSTIVE CAYLEY GRAPH SCAN ON ALL 14 GROUPS OF ORDER 40 ===\n";
    I global_best = 1e18;
    array<U, N> global_best_adj{};
    string global_best_desc;

    for (const auto& G : groups) {
        vector<U> pairs;
        vector<int> pair_sz;
        U seen = 1ULL;
        for (int g = 1; g < 40; g++) {
            if ((seen >> g) & 1ULL) continue;
            int gi = G.inv[g];
            U m = (1ULL << g) | (1ULL << gi);
            seen |= m;
            pairs.push_back(m);
            pair_sz.push_back(pc(m));
        }
        int P = pairs.size();
        vector<vector<U>> prod(P, vector<U>(P, 0));
        for (int i = 0; i < P; i++) {
            for (int j = 0; j < P; j++) {
                U m = 0;
                for (U a = pairs[i]; a; a &= a - 1) {
                    int x = ctz(a);
                    for (U b = pairs[j]; b; b &= b - 1) {
                        int y = ctz(b);
                        m |= (1ULL << G.mul[x][y]) | (1ULL << G.mul[y][x]);
                    }
                }
                prod[i][j] = m;
            }
        }
        vector<U> self_forbid(P, 0);
        vector<vector<U>> pair_forbid(P, vector<U>(P, 0));
        for (int i = 0; i < P; i++)
            for (int j = 0; j < P; j++)
                if ((prod[i][i] & pairs[j]) || (prod[i][j] & pairs[i]) || (prod[i][j] & pairs[j]))
                    self_forbid[i] |= (1ULL << j);
        for (int i = 0; i < P; i++)
            for (int j = i + 1; j < P; j++) {
                U f = 0;
                for (int k = 0; k < P; k++)
                    if ((prod[i][j] & pairs[k]) || (prod[i][k] & pairs[j]) || (prod[j][k] & pairs[i]))
                        f |= (1ULL << k);
                pair_forbid[i][j] = pair_forbid[j][i] = f;
            }

        uint64_t total_deg79 = 0;
        I best_i10 = 1e18;
        int best_deg = 0;

        vector<int> chosen;
        auto dfs = [&](auto&& self, int idx, int deg, U S, U avail) -> void {
            if (deg >= 7 && deg <= 9) {
                total_deg79++;
                array<U, N> a{};
                for (int x = 0; x < 40; x++) {
                    U m = 0;
                    for (U s = S; s; s &= s - 1) m |= (1ULL << G.mul[x][ctz(s)]);
                    a[x] = m;
                }
                I i10 = count_i10_vt(a.data());
                if (i10 < best_i10) {
                    best_i10 = i10; best_deg = deg;
                    if (i10 < global_best) {
                        global_best = i10; global_best_adj = a;
                        global_best_desc = G.name + " deg=" + to_string(deg);
                    }
                    if (i10 == 0) {
                        cout << "!!! WITNESS FOUND IN " << G.name << " deg=" << deg << " !!!\n";
                        save_adj("witness_cayley.txt", a);
                    }
                }
            }
            if (deg == 9) return;
            for (int i = idx; i < P; i++) {
                if (!((avail >> i) & 1ULL)) continue;
                int ndeg = deg + pair_sz[i];
                if (ndeg > 9) continue;
                U navail = avail & ~self_forbid[i] & ~((1ULL << (i + 1)) - 1);
                for (int c : chosen) navail &= ~pair_forbid[c][i];
                chosen.push_back(i);
                self(self, i + 1, ndeg, S | pairs[i], navail);
                chosen.pop_back();
            }
        };

        U init_avail = (P == 64) ? ~0ULL : ((1ULL << P) - 1);
        dfs(dfs, 0, 0, 0, init_avail);
        cout << left << setw(28) << G.name
             << " | pairs=" << setw(2) << P
             << " | deg7..9_tf=" << setw(7) << total_deg79
             << " | best_I10=" << (best_i10 < 1e17 ? to_string(best_i10) : "NONE")
             << " (deg=" << best_deg << ")\n";
    }
    cout << "Best Cayley overall: I10=" << global_best << " (" << global_best_desc << ")\n";
    if (global_best < 1e17) {
        I exact = count_indep(global_best_adj.data(), FULL, 10);
        cout << "Verified exact I10=" << exact << ", triangle_free=" << is_triangle_free(global_best_adj.data()) << "\n";
        save_adj("best_cayley.txt", global_best_adj);
    }
}

void scan_bicirculant_2x20() {
    cout << "\n=== PART 2: EXHAUSTIVE 2x20 BICIRCULANT SCAN (C20, 2 orbits of 20) ===\n";
    vector<U> pairs;
    for (int d = 1; d <= 9; d++) pairs.push_back((1ULL << d) | (1ULL << (20 - d)));
    pairs.push_back(1ULL << 10);

    struct OrbitSet { U S; int sz; array<U, 20> a20; };
    vector<OrbitSet> good_S;
    for (int mask = 1; mask < (1 << 10); mask++) {
        U S = 0;
        for (int i = 0; i < 10; i++) if ((mask >> i) & 1) S |= pairs[i];
        int sz = pc(S);
        if (sz > 8) continue;
        bool ok = true;
        for (U x = S; x && ok; x &= x - 1) {
            int a = ctz(x);
            for (U y = S; y && ok; y &= y - 1)
                if ((S >> ((a + ctz(y)) % 20)) & 1ULL) ok = false;
        }
        if (!ok) continue;
        array<U, 20> a20{};
        for (int v = 0; v < 20; v++) {
            U m = 0;
            for (U x = S; x; x &= x - 1) m |= (1ULL << ((v + ctz(x)) % 20));
            a20[v] = m;
        }
        if (has_indep(a20.data(), (1ULL << 20) - 1, 10)) continue;
        good_S.push_back({S, sz, a20});
    }
    cout << "Valid triangle-free S in Z_20 with alpha<=9 and |S|<=8: " << good_S.size() << "\n";

    uint64_t tested = 0;
    I best_i10 = 1e18;
    array<U, N> best_adj{};
    string best_desc;

    for (size_t i = 0; i < good_S.size(); i++) {
        for (size_t j = i; j < good_S.size(); j++) {
            const auto& g0 = good_S[i];
            const auto& g1 = good_S[j];
            int minT = max(1, max(6 - g0.sz, 6 - g1.sz));
            int maxT = min(9 - g0.sz, 9 - g1.sz);
            if (minT > maxT) continue;
            U aU[20];
            for (int v = 0; v < 20; v++) aU[v] = g0.a20[v] | g1.a20[v];

            auto dfsT = [&](auto&& self, int szT, U T, U cand) -> void {
                if (szT >= minT && szT <= maxT) {
                    tested++;
                    array<U, N> a{};
                    for (int v = 0; v < 20; v++) {
                        U cross01 = 0, cross10 = 0;
                        for (U t = T; t; t &= t - 1) {
                            int d = ctz(t);
                            cross01 |= (1ULL << ((v + d) % 20));
                            cross10 |= (1ULL << ((v + 20 - d) % 20));
                        }
                        a[v] = g0.a20[v] | (cross01 << 20);
                        a[20 + v] = cross10 | (g1.a20[v] << 20);
                    }
                    if (!has_indep(a.data(), FULL, 10)) {
                        cout << "!!! WITNESS FOUND IN 2x20 BICIRCULANT !!!\n";
                        save_adj("witness_2x20.txt", a);
                        best_i10 = 0; best_adj = a; return;
                    }
                    if (g0.sz + szT >= 8 && g1.sz + szT >= 8) {
                        I i10 = count_indep(a.data(), FULL, 10);
                        if (i10 < best_i10) {
                            best_i10 = i10; best_adj = a;
                            best_desc = "S0_sz=" + to_string(g0.sz) + " S1_sz=" + to_string(g1.sz) + " T_sz=" + to_string(szT);
                        }
                    }
                }
                if (szT == maxT) return;
                while (cand) {
                    int v = ctz(cand); cand &= cand - 1;
                    self(self, szT + 1, T | (1ULL << v), cand & ~aU[v]);
                }
            };
            U init_cand = (((1ULL << 20) - 1) ^ 1ULL) & ~aU[0];
            dfsT(dfsT, 1, 1ULL, init_cand);
        }
    }
    cout << "Exhausted ALL 2x20 bicirculants (deg 6..9): tested=" << tested
         << ", best_I10=" << best_i10 << " (" << best_desc << ")\n";
    if (best_i10 < 1e17) save_adj("best_2x20.txt", best_adj);
}

int main() {
    auto groups = make_all_14_groups40();
    scan_cayley(groups);
    scan_bicirculant_2x20();
    return 0;
}
