#include <iostream>
#include <vector>
#include <array>
#include <set>
#include <algorithm>
#include <cstdint>
using namespace std;

const int V[4] = {6, 7, 8, 9};
const int E9[10] = {0,0,0,0,0,0, 118, 104, 95, 86};
const int E8[28] = {0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, 35, 42, 49, 56, 65, 73, 85};
const int E8MAX[28] = {0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, 73, 77, 80, 84, 87, 91, 94};

inline int c2(int n) { return n * (n - 1) / 2; }
inline int min_pairs(int total, int n) {
    if (n == 0) return total == 0 ? 0 : 1000000000;
    int q = total / n, r = total % n;
    return (n - r) * c2(q) + r * c2(q + 1);
}
inline int dot4(const array<int,4>& a) {
    return 6*a[0] + 7*a[1] + 8*a[2] + 9*a[3];
}

vector<array<int,4>> comps4(int n) {
    vector<array<int,4>> out;
    for (int a=0; a<=n; ++a)
      for (int b=0; b<=n-a; ++b)
        for (int c=0; c<=n-a-b; ++c)
          out.push_back({a, b, c, n-a-b-c});
    return out;
}

struct Profile {
    array<int,4> n;
    int m;
    int Tmask;
};

vector<array<int,4>> get_types_cap(const array<int,4>& n, int m, int k_deg, const int cap[4][4]) {
    vector<array<int,4>> out;
    int i = k_deg - 6;
    if (n[i] == 0) return out;
    int h = 39 - k_deg;
    int eH_hi = min(4 * h, (7 * h + k_deg * (10 - k_deg)) / 2);
    int cross_lo = 2 * h - k_deg * (10 - k_deg);
    for (auto& a : comps4(k_deg)) {
        bool ok = true;
        for (int j=0; j<4; ++j) if (a[j] > n[j] - (j == i ? 1 : 0)) { ok = false; break; }
        if (!ok) continue;
        int sx = dot4(a);
        int cross = sx - k_deg;
        int eH = m - sx;
        if (eH < E9[k_deg] || eH > eH_hi) continue;
        if (cross < cross_lo || cross < h) continue;
        int hn[4];
        int cap_sum = 0, sing_sum = 0;
        for (int j=0; j<4; ++j) {
            hn[j] = n[j] - a[j] - (j == i ? 1 : 0);
            if (hn[j] > 0 && cap[i][j] < 1) { ok = false; break; }
            cap_sum += hn[j] * cap[i][j];
            if (cap[i][j] == 1) sing_sum += hn[j];
        }
        if (!ok) continue;
        if (cross > cap_sum) continue;
        if (sing_sum > k_deg * (10 - k_deg)) continue;
        out.push_back(a);
    }
    return out;
}

pair<int, pair<int,int>> na_feasible(const Profile& P, int du, int dv, int c, int eT_cap, const int cap[4][4]) {
    int nt = 38 - du - dv + c;
    if (c < 1 || c > du || nt < 23 || nt > 27) return {0, {999, -1}};
    int nx = du - c, ny = dv - c;
    int eT_hi_bound = min(E8MAX[nt], eT_cap);
    if (E8[nt] > eT_hi_bound) return {0, {999, -1}};
    array<int,4> avail = P.n;
    avail[du-6]--; avail[dv-6]--;
    for (int j=0; j<4; ++j) if (avail[j] < 0) return {0, {999, -1}};

    auto types_u = get_types_cap(P.n, P.m, du, cap);
    auto types_v = get_types_cap(P.n, P.m, dv, cap);
    if (types_u.empty() || types_v.empty()) return {0, {999, -1}};

    uint64_t t_mask = 0;
    int eT_lo = 999, eT_hi = -1;
    int iu = du - 6, iv = dv - 6;

    for (auto& s : comps4(c)) {
        bool sok = true;
        for (int j=0; j<4; ++j) if (s[j] > avail[j]) { sok = false; break; }
        if (!sok) continue;
        int ss = dot4(s);
        int st = ss - 2 * c;
        vector<pair<array<int,4>, int>> xs, ys;
        for (auto& a : types_u) {
            array<int,4> x; bool ok = true;
            for (int j=0; j<4; ++j) {
                x[j] = a[j] - s[j];
                if (x[j] < 0 || x[j] + s[j] > avail[j]) { ok = false; break; }
            }
            if (ok) xs.push_back({x, dot4(x)});
        }
        if (xs.empty()) continue;
        for (auto& a : types_v) {
            array<int,4> y; bool ok = true;
            for (int j=0; j<4; ++j) {
                y[j] = a[j] - s[j];
                if (y[j] < 0 || y[j] + s[j] > avail[j]) { ok = false; break; }
            }
            if (ok) ys.push_back({y, dot4(y)});
        }
        if (ys.empty()) continue;

        for (auto& [x, sx] : xs) {
            for (auto& [y, sy] : ys) {
                int z[4]; bool ok = true;
                for (int j=0; j<4; ++j) {
                    z[j] = avail[j] - s[j] - x[j] - y[j];
                    if (z[j] < 0) { ok = false; break; }
                }
                if (!ok) continue;
                int t_lo_xy = max(nx, ny);
                int c_xy1 = 0, c_xy2 = 0;
                for (int j=0; j<4; ++j) {
                    c_xy1 += x[j] * min(ny, cap[j][iv]);
                    c_xy2 += y[j] * min(nx, cap[j][iu]);
                }
                int t_hi_xy = min({nx * ny, c_xy1, c_xy2});
                if (t_lo_xy > t_hi_xy) continue;

                int base = P.m - ss - sx - sy;
                int t_lo = max(t_lo_xy, E8[nt] - base);
                int t_hi = min(t_hi_xy, eT_hi_bound - base);
                if (t_lo > t_hi) continue;

                int cap_sx = 0, cap_sy = 0, cap_all = 0;
                for (int j=0; j<4; ++j) {
                    cap_sx += z[j] * min(du, cap[iu][j]);
                    cap_sy += z[j] * min(dv, cap[iv][j]);
                    cap_all += z[j] * (V[j] - (nt - 23));
                }
                t_lo = max({t_lo, st + sx - nx - cap_sx, st + sy - ny - cap_sy,
                            (st + sx - nx + sy - ny - cap_all + 1) / 2});
                t_hi = min({t_hi, st + sx - nx - nt, st + sy - ny - nt});
                if (t_lo > t_hi) continue;

                int ux[4], uy[4];
                for (int j=0; j<4; ++j) { ux[j] = s[j] + x[j]; uy[j] = s[j] + y[j]; }
                int bu = -c2(du) - c2(c);
                int bv = -c2(dv) - c2(c);
                for (int j1=0; j1<4; ++j1) {
                    bu += c2(ux[j1]) * cap[j1][j1];
                    bv += c2(uy[j1]) * cap[j1][j1];
                    for (int j2=j1+1; j2<4; ++j2) {
                        bu += ux[j1] * ux[j2] * cap[j1][j2];
                        bv += uy[j1] * uy[j2] * cap[j1][j2];
                    }
                }
                for (int t = t_lo; t <= t_hi; ++t) {
                    int xt = sx - nx - t, yt = sy - ny - t;
                    if (xt < 0 || yt < 0) continue;
                    if (min_pairs(st + xt, nt) + min_pairs(t, ny) > bu) continue;
                    if (min_pairs(st + yt, nt) + min_pairs(t, nx) > bv) continue;
                    t_mask |= (1ULL << t);
                    int eT = base + t;
                    if (eT < eT_lo) eT_lo = eT;
                    if (eT > eT_hi) eT_hi = eT;
                }
            }
        }
    }
    return {__builtin_popcountll(t_mask), {eT_lo, eT_hi}};
}

int main() {
    int np; cin >> np;
    vector<Profile> profs(np);
    for (int i=0; i<np; ++i)
        cin >> profs[i].n[0] >> profs[i].n[1] >> profs[i].n[2] >> profs[i].n[3] >> profs[i].m >> profs[i].Tmask;

    int cap27[4][4];
    for (int i=0; i<4; ++i) for (int j=0; j<4; ++j) cap27[i][j] = min({V[i], V[j], V[i]+V[j]-11});

    cout << "=== TIER 1: DEGREE-6 ELIMINATION (INNER WM, 333 n6>0 PROFILES) ===\n";
    int t1_br = 0, t1_pr = 0, t1_tr = 0;
    for (int r : {5, 6, 7}) {
        int nt = 32 - r, eT_cap = 132 - 8 * r;
        for (int q = r + 1; q <= 9; ++q) {
            int c = q - r, pc = 0, tc = 0, elo = 999, ehi = -1;
            for (auto& P : profs) {
                if (P.n[0] == 0) continue;
                auto [cnt, rng] = na_feasible(P, 6, q, c, eT_cap, cap27);
                if (cnt > 0) { pc++; tc += cnt; elo = min(elo, rng.first); ehi = max(ehi, rng.second); }
            }
            if (pc > 0) {
                t1_br++; t1_pr += pc; t1_tr += tc;
                cout << "  T1-D6 (r=" << r << ", q=" << q << ", c=" << c << ", nT=" << nt
                     << "): " << pc << " profs, " << tc << " triples, e(T) in [" << elo << "," << ehi << "]\n";
            }
        }
    }
    cout << "TOTAL TIER 1: " << t1_br << " branches, " << t1_pr << " (branch,prof), " << t1_tr << " triples\n";

    cout << "\n=== TIER 2: D78 (n6=0, 209 PROFILES) GLOBAL MAX-|T| + LEX-MAX TIE-BREAKING ===\n";
    vector<pair<int,int>> d78_pairs = {{9,9},{8,9},{8,8},{7,9},{7,8},{7,7}};
    int t2_br = 0, t2_pr = 0, t2_tr = 0;
    for (int Tstar : {27, 26, 25, 24}) {
        int bit = 1 << (Tstar - 24), shift = 38 - Tstar;
        for (auto [du, dv] : d78_pairs) {
            int c = du + dv - shift;
            if (c < 1 || c > du) continue;
            int cap[4][4];
            for (int i=0; i<4; ++i) for (int j=0; j<4; ++j) {
                int a = min(V[i], V[j]), b = max(V[i], V[j]);
                int sh = ((a > du) || (a == du && b > dv)) ? (shift + 1) : shift;
                cap[i][j] = min({V[i], V[j], V[i] + V[j] - sh});
            }
            int pc = 0, tc = 0, elo = 999, ehi = -1;
            for (auto& P : profs) {
                if (P.n[0] > 0 || !(P.Tmask & bit)) continue;
                auto [cnt, rng] = na_feasible(P, du, dv, c, E8MAX[Tstar], cap);
                if (cnt > 0) { pc++; tc += cnt; elo = min(elo, rng.first); ehi = max(ehi, rng.second); }
            }
            if (pc > 0) {
                t2_br++; t2_pr += pc; t2_tr += tc;
                cout << "  T2-D78 T*=" << Tstar << " (du=" << du << ", dv=" << dv << ", c=" << c
                     << "): " << pc << " profs, " << tc << " triples, e(T) in [" << elo << "," << ehi << "]\n";
            }
        }
    }
    cout << "TOTAL TIER 2: " << t2_br << " branches, " << t2_pr << " (branch,prof), " << t2_tr << " triples\n";
    cout << "COMBINED: " << (t1_br + t2_br) << " branches, " << (t1_pr + t2_pr) << " (branch,prof), " << (t1_tr + t2_tr) << " triples\n";
    return 0;
}
