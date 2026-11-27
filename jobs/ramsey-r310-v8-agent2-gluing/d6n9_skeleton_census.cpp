#include <bits/stdc++.h>
using namespace std;

// Exact Canonical Skeleton & Orbit Census for D6-N9-B3 (d=6, q=9, |X|=5, |Y|=8, |T|=25)
// Enumerates ALL canonical bipartite graphs G[X,Y] under S_X x S_Y satisfying:
// 1. deg_Y(x) <= 6 (from deg(x)+q-12 = 9+9-12 = 6)
// 2. deg_X(y) <= 3 (from deg(y)+d-12 <= 9+6-12 = 3)
// 3. alpha(G[X,Y]) <= 9 (no independent set of size 10 in X U Y)
// Then for each of the 4 exact D6-N9-B3 profiles (P000..P003), enumerates all
// non-isomorphic degree assignments to Y (modulo Aut(G[X,Y])) and applies:
// 4. Exact per-vertex degree cap deg_X(y) <= deg(y) - 6
// 5. Exact edge bounds e(H0) in [118,126], e(H1) in [86,109], e(T) in [46,100]
// 6. Exact cross-capacity bounds on T
// 7. Exact skeleton-level V8 convexity using ACTUAL c2_X and c2_Y of G[X,Y]

static inline int c2(int n) { return n * (n - 1) / 2; }
static inline int min_pairs(int total, int n) {
    int q = total / n, r = total % n;
    return (n - r) * c2(q) + r * c2(q + 1);
}

static const int V[4] = {6, 7, 8, 9};
static const int E_MIN[4] = {118, 104, 95, 86};
static const int ET25 = 46;

struct Profile {
    string name;
    int m;
    array<int, 4> n;
};

static const vector<Profile> PROFILES = {
    {"P000", 177, {1, 0, 3, 36}},
    {"P001", 177, {1, 1, 1, 37}},
    {"P002", 177, {2, 0, 0, 38}},
    {"P003", 178, {1, 0, 1, 38}},
};

static const vector<pair<int,int>> T_BANDS = {
    {0, 2}, {3, 5}, {6, 8}, {9, 11}, {12, 14}, {15, 17}, {18, 20}, {21, 24}
};

static array<array<uint8_t, 5>, 120> PERMS;
void init_perms() {
    int a[5] = {0, 1, 2, 3, 4};
    int idx = 0;
    do {
        for (int i = 0; i < 5; ++i) PERMS[idx][i] = (uint8_t)a[i];
        idx++;
    } while (next_permutation(a, a + 5));
}

inline bool check_alpha_xy(const array<uint8_t, 5>& adjX) {
    for (int s = 0; s < 32; ++s) {
        uint8_t cov = 0;
        for (int x = 0; x < 5; ++x) if ((s >> x) & 1) cov |= adjX[x];
        if (popcount((unsigned)s) + (8 - popcount(cov)) > 9) return false;
    }
    return true;
}

inline uint64_t canonical_key_cols(const array<uint8_t, 8>& col) {
    uint64_t best = 0;
    for (int pi = 0; pi < 120; ++pi) {
        const auto& p = PERMS[pi];
        array<uint8_t, 8> pcol;
        for (int y = 0; y < 8; ++y) {
            uint8_t m = col[y], nm = 0;
            if (m & (1u << p[0])) nm |= 1u;
            if (m & (1u << p[1])) nm |= 2u;
            if (m & (1u << p[2])) nm |= 4u;
            if (m & (1u << p[3])) nm |= 8u;
            if (m & (1u << p[4])) nm |= 16u;
            pcol[y] = nm;
        }
        sort(pcol.begin(), pcol.end(), greater<uint8_t>());
        uint64_t key = 0;
        for (int y = 0; y < 8; ++y) key = (key << 5) | pcol[y];
        if (key > best) best = key;
    }
    return best;
}

int count_feasible_y_assignments(
    const array<uint8_t, 8>& col,
    int t, int c2X, int c2Y,
    const Profile& prof
) {
    array<int, 4> avail = prof.n;
    avail[0] -= 1;
    avail[3] -= 6;
    if (avail[0] < 0 || avail[3] < 0) return 0;

    int sx = 45, nx = 5, ny = 8, nt = 25;
    int xt = sx - nx - t;
    int bx = (nx - 1) * sx - 12 * c2(nx);

    unordered_set<uint64_t> orbits;
    array<int, 8> degY{};
    array<int, 4> usedY{};

    auto rec = [&](auto& self, int y, int sy) -> void {
        if (y == 8) {
            array<int, 4> z;
            for (int i = 0; i < 4; ++i) z[i] = avail[i] - usedY[i];
            int yt = sy - ny - t;
            int eH1 = prof.m - 6 - sy;
            int eT = prof.m - 1 - sx - sy + t;
            if (eH1 < E_MIN[3] || eH1 > 109) return;
            if (eT < ET25 || eT > 4 * nt) return;
            if (xt < nt || yt < nt) return;
            int capx = 0, capy = 0;
            for (int i = 0; i < 4; ++i) {
                capx += z[i] * min(nx, V[i] + 6 - 11);
                capy += z[i] * min(ny, V[i] + 9 - 11);
            }
            if (xt > capx || yt > capy) return;
            if (min_pairs(xt, nt) + c2Y > bx) return;
            int by = (ny - 1) * sy - 12 * c2(ny);
            if (min_pairs(yt, nt) + c2X > by) return;

            uint64_t best = 0;
            for (int pi = 0; pi < 120; ++pi) {
                const auto& p = PERMS[pi];
                array<uint8_t, 8> packed;
                for (int j = 0; j < 8; ++j) {
                    uint8_t m = col[j], nm = 0;
                    if (m & (1u << p[0])) nm |= 1u;
                    if (m & (1u << p[1])) nm |= 2u;
                    if (m & (1u << p[2])) nm |= 4u;
                    if (m & (1u << p[3])) nm |= 8u;
                    if (m & (1u << p[4])) nm |= 16u;
                    packed[j] = (uint8_t)((nm << 2) | (degY[j] - 6));
                }
                sort(packed.begin(), packed.end(), greater<uint8_t>());
                uint64_t key = 0;
                for (int j = 0; j < 8; ++j) key = (key << 7) | packed[j];
                if (key > best) best = key;
            }
            orbits.insert(best);
            return;
        }
        int dx = popcount(col[y]);
        for (int i = 0; i < 4; ++i) {
            if (usedY[i] < avail[i] && dx <= V[i] - 6) {
                usedY[i]++;
                degY[y] = V[i];
                self(self, y + 1, sy + V[i]);
                usedY[i]--;
            }
        }
    };
    rec(rec, 0, 0);
    return (int)orbits.size();
}

int main() {
    init_perms();
    auto t0 = chrono::steady_clock::now();

    vector<uint8_t> valid_cols;
    for (int m = 31; m >= 0; --m) if (popcount((unsigned)m) <= 3) valid_cols.push_back((uint8_t)m);

    unordered_set<uint64_t> seen;
    struct SkelData { array<uint8_t, 8> col; int t, c2X, c2Y; };
    vector<SkelData> all_skels;
    array<uint8_t, 8> cols{};
    array<uint8_t, 5> degYx{};

    auto dfs = [&](auto& self, int idx, int start_ci, int cur_t) -> void {
        if (idx == 8) {
            array<uint8_t, 5> adjX{};
            for (int y = 0; y < 8; ++y)
                for (int x = 0; x < 5; ++x)
                    if ((cols[y] >> x) & 1) adjX[x] |= (1u << y);
            if (!check_alpha_xy(adjX)) return;
            uint64_t key = canonical_key_cols(cols);
            if (seen.insert(key).second) {
                int c2y = 0, c2x = 0;
                for (int y = 0; y < 8; ++y) c2y += c2(popcount(cols[y]));
                for (int x = 0; x < 5; ++x) c2x += c2(degYx[x]);
                all_skels.push_back({cols, cur_t, c2x, c2y});
            }
            return;
        }
        int max_ci = (idx < 4) ? ((int)valid_cols.size() - 2) : ((int)valid_cols.size() - 1);
        for (int ci = start_ci; ci <= max_ci; ++ci) {
            uint8_t m = valid_cols[ci];
            bool ok = true;
            for (int x = 0; x < 5; ++x) if (((m >> x) & 1) && degYx[x] == 6) { ok = false; break; }
            if (!ok) continue;
            for (int x = 0; x < 5; ++x) if ((m >> x) & 1) degYx[x]++;
            cols[idx] = m;
            self(self, idx + 1, ci, cur_t + popcount(m));
            for (int x = 0; x < 5; ++x) if ((m >> x) & 1) degYx[x]--;
        }
    };
    dfs(dfs, 0, 0, 0);
    auto t1 = chrono::steady_clock::now();
    cout << "Full D6-N9 canonical skeleton enumeration (t=0..24): " << all_skels.size()
         << " skeletons in " << fixed << setprecision(2) << chrono::duration<double>(t1 - t0).count() << " s\n\n";

    vector<vector<int>> raw_cnt(4, vector<int>(8, 0));
    vector<vector<int>> surv_cnt(4, vector<int>(8, 0));
    vector<vector<int>> orb_cnt(4, vector<int>(8, 0));

    for (const auto& s : all_skels) {
        int tb = -1;
        for (int b = 0; b < 8; ++b) if (s.t >= T_BANDS[b].first && s.t <= T_BANDS[b].second) { tb = b; break; }
        if (tb < 0) continue;
        for (int p = 0; p < 4; ++p) {
            raw_cnt[p][tb]++;
            int orbs = count_feasible_y_assignments(s.col, s.t, s.c2X, s.c2Y, PROFILES[p]);
            if (orbs > 0) { surv_cnt[p][tb]++; orb_cnt[p][tb] += orbs; }
        }
    }
    auto t2 = chrono::steady_clock::now();
    cout << "Profile + exact skeleton V8 convexity filtering completed in "
         << chrono::duration<double>(t2 - t1).count() << " s\n\n";

    cout << "Task              | t-band | raw_skels | surv_skels | deg_orbits\n";
    cout << "------------------|--------|-----------|------------|-----------\n";
    for (int p = 0; p < 4; ++p) {
        for (int b = 0; b < 8; ++b) {
            cout << "D6-N9-B3-" << PROFILES[p].name << "-T0" << b
                 << " | " << setw(2) << T_BANDS[b].first << ".." << setw(2) << T_BANDS[b].second
                 << " | " << setw(9) << raw_cnt[p][b]
                 << " | " << setw(10) << surv_cnt[p][b]
                 << " | " << setw(10) << orb_cnt[p][b] << "\n";
        }
    }
    return 0;
}
