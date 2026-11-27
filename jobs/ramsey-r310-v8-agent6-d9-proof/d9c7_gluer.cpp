#include <bits/stdc++.h>
using namespace std;
using u32 = uint32_t;
using u64 = uint64_t;

static constexpr int N = 27;
static constexpr int MAX_W = 2048;
static constexpr int WORDS = MAX_W / 64;

struct Bitset {
    u64 w[WORDS]{};
    inline bool intersects(const Bitset& o, int nwords) const {
        for (int i = 0; i < nwords; ++i)
            if (w[i] & o.w[i]) return true;
        return false;
    }
};

array<u32, N> decode_g6(const string& raw) {
    string s = raw;
    if (s.rfind(">>graph6<<", 0) == 0) s = s.substr(10);
    while (!s.empty() && (s.back() == '\n' || s.back() == '\r' || s.back() == ' ')) s.pop_back();
    int n = int(s[0]) - 63;
    if (n != N) throw runtime_error("Expected 27 vertices");
    array<u32, N> adj{};
    int k = 0;
    for (int j = 0; j < N; ++j) {
        for (int i = 0; i < j; ++i) {
            if (((int(s[1 + k / 6]) - 63) >> (5 - (k % 6))) & 1) {
                adj[i] |= (1u << j);
                adj[j] |= (1u << i);
            }
            k++;
        }
    }
    return adj;
}

vector<u32> enum_ik(const array<u32, N>& adj, int k) {
    vector<u32> res;
    auto dfs = [&](auto&& self, u32 cand, int rem, u32 cur) -> void {
        if (rem == 0) { res.push_back(cur); return; }
        int pop = __builtin_popcount(cand);
        if (pop < rem) return;
        while (pop >= rem) {
            int v = __builtin_ctz(cand);
            cand ^= (1u << v);
            pop--;
            self(self, cand & ~adj[v], rem - 1, cur | (1u << v));
        }
    };
    dfs(dfs, (1u << N) - 1, k, 0);
    return res;
}

int main(int argc, char** argv) {
    if (argc < 2) {
        cerr << "Usage: " << argv[0] << " <graph6>\n";
        return 1;
    }
    auto t0 = chrono::steady_clock::now();
    auto adj = decode_g6(argv[1]);

    int edges = 0;
    array<int, N> deg{}, rem{}, min_dS{}, max_dS{};
    for (int i = 0; i < N; ++i) {
        deg[i] = __builtin_popcount(adj[i]);
        rem[i] = 9 - deg[i];
        min_dS[i] = max(1, rem[i] - 2);
        max_dS[i] = rem[i];
        edges += deg[i];
        for (int j = i + 1; j < N; ++j) {
            if (((adj[i] >> j) & 1) && (adj[i] & adj[j])) {
                cerr << "Not triangle-free!\n";
                return 2;
            }
        }
    }
    edges /= 2;
    if (edges != 85) { cerr << "Edges != 85: " << edges << "\n"; return 2; }
    if (!enum_ik(adj, 8).empty()) { cerr << "Has I8!\n"; return 2; }

    auto I7 = enum_ik(adj, 7);
    auto I6 = enum_ik(adj, 6);
    int M7 = (int)I7.size();
    int M6 = (int)I6.size();
    if (M7 > MAX_W) { cerr << "Increase MAX_W!\n"; return 2; }
    int nwords = (M7 + 63) / 64;

    vector<Bitset> miss7(M7);
    for (int i = 0; i < M7; ++i) {
        for (int w = 0; w < M7; ++w) {
            if ((I7[i] & I7[w]) == 0) {
                miss7[i].w[w >> 6] |= (1ULL << (w & 63));
            }
        }
    }

    vector<vector<u64>> compat7(M7, vector<u64>(nwords, 0));
    for (int i = 0; i < M7; ++i) {
        for (int j = 0; j < M7; ++j) {
            if (i != j && __builtin_popcount(I7[i] & I7[j]) <= 5) {
                compat7[i][j >> 6] |= (1ULL << (j & 63));
            }
        }
    }

    array<vector<u64>, N> has_v;
    for (int v = 0; v < N; ++v) {
        has_v[v].assign(nwords, 0);
        for (int i = 0; i < M7; ++i) {
            if ((I7[i] >> v) & 1) has_v[v][i >> 6] |= (1ULL << (i & 63));
        }
    }

    array<array<int, N>, N> tcap{};
    for (int i = 0; i < N; ++i)
        for (int j = 0; j < N; ++j)
            tcap[i][j] = 100;
    for (int i = 0; i < N; ++i) {
        for (int j = i + 1; j < N; ++j) {
            if (!((adj[i] >> j) & 1)) {
                int c = 7 - __builtin_popcount(adj[i] & adj[j]);
                tcap[i][j] = tcap[j][i] = c;
            }
        }
    }

    u64 nodes = 0, valid_S = 0, valid_full = 0;
    u32 all_mask = (1u << N) - 1;
    vector<u32> ext6(M6, 0);
    vector<Bitset> miss6(M6);
    for (int i = 0; i < M6; ++i) {
        u32 cov = I6[i], tmp = I6[i];
        while (tmp) {
            int v = __builtin_ctz(tmp);
            tmp ^= (1u << v);
            cov |= adj[v];
        }
        ext6[i] = all_mask ^ cov;
        for (int w = 0; w < M7; ++w) {
            if ((I6[i] & I7[w]) == 0) {
                miss6[i].w[w >> 6] |= (1ULL << (w & 63));
            }
        }
    }

    auto solve_XY = [&](const array<int, N>& dS, const Bitset& m1, const Bitset& m2, const array<array<int,N>,N>& pcnt) -> bool {
        u32 need2 = 0, need1 = 0;
        for (int v = 0; v < N; ++v) {
            int d = rem[v] - dS[v];
            if (d == 2) need2 |= (1u << v);
            else if (d == 1) need1 |= (1u << v);
            else if (d != 0) return false;
        }
        u32 nonzero = need1 | need2;
        vector<int> cands;
        for (int i = 0; i < M6; ++i) {
            if ((I6[i] & ~nonzero) != 0) continue;
            if ((ext6[i] & ~nonzero) != 0) continue;
            if (m2.intersects(miss6[i], nwords)) continue;
            cands.push_back(i);
        }
        int K = (int)cands.size();
        if (K < 4) return false;
        vector<pair<int,int>> pairs_xy;
        for (int a = 0; a < K; ++a) {
            int i = cands[a];
            u32 j1 = I6[i], e1 = ext6[i];
            for (int b = a + 1; b < K; ++b) {
                int j = cands[b];
                u32 j2 = I6[j], e2 = ext6[j];
                u32 inter = j1 & j2;
                if (__builtin_popcount(inter) > 4) continue;
                if (inter & ~need2) continue;
                u32 uni = j1 | j2;
                if ((uni ^ inter) & need2) continue;
                u32 euni = e1 | e2;
                if (euni & uni) continue;
                bool ok = true;
                for (int w = 0; w < nwords; ++w) {
                    if (m1.w[w] & miss6[i].w[w] & miss6[j].w[w]) { ok = false; break; }
                }
                if (!ok) continue;
                pairs_xy.push_back({i, j});
            }
        }
        if (pairs_xy.size() < 2) return false;
        unordered_map<u32, vector<int>> by_uni;
        for (int idx = 0; idx < (int)pairs_xy.size(); ++idx) {
            u32 u = I6[pairs_xy[idx].first] | I6[pairs_xy[idx].second];
            by_uni[u].push_back(idx);
        }
        for (int idx = 0; idx < (int)pairs_xy.size(); ++idx) {
            auto [x1, x2] = pairs_xy[idx];
            u32 ux = I6[x1] | I6[x2];
            u32 uy = nonzero ^ ux;
            if (ux > uy) continue;
            auto it = by_uni.find(uy);
            if (it == by_uni.end()) continue;
            u32 ex = ext6[x1] | ext6[x2];
            if ((ex & ~uy) != 0) continue;
            for (int jdx : it->second) {
                auto [y1, y2] = pairs_xy[jdx];
                u32 ey = ext6[y1] | ext6[y2];
                if ((ey & ~ux) != 0) continue;
                bool ok = true;
                u32 sets4[4] = {I6[x1], I6[x2], I6[y1], I6[y2]};
                for (int u = 0; u < N && ok; ++u) {
                    for (int v = u + 1; v < N; ++v) {
                        if (tcap[u][v] >= 11) continue;
                        int add = 0;
                        u32 uv = (1u << u) | (1u << v);
                        for (int q = 0; q < 4; ++q) if ((sets4[q] & uv) == uv) add++;
                        if (pcnt[u][v] + add > tcap[u][v]) { ok = false; break; }
                    }
                }
                if (ok) {
                    valid_full++;
                    return true;
                }
            }
        }
        return false;
    };

    array<int, N> dS{};
    array<array<int, N>, N> pcnt{};
    vector<int> chosen;
    vector<u64> init_avail(nwords, 0);
    for (int i = 0; i < M7; ++i) init_avail[i >> 6] |= (1ULL << (i & 63));
    Bitset init_m1{}, init_m2{};

    auto dfs = [&](auto&& self, int depth, vector<u64> avail, const Bitset& m1, const Bitset& m2) -> void {
        nodes++;
        int rem_sets = 7 - depth;
        if (rem_sets == 0) {
            for (int v = 0; v < N; ++v) if (dS[v] < min_dS[v]) return;
            valid_S++;
            solve_XY(dS, m1, m2, pcnt);
            return;
        }
        int best_v = -1, best_cnt = 1e9, total_min_need = 0;
        for (int v = 0; v < N; ++v) {
            int need = min_dS[v] - dS[v];
            if (need > rem_sets) return;
            if (need > 0) {
                total_min_need += need;
                int cnt = 0;
                for (int w = 0; w < nwords; ++w)
                    cnt += __builtin_popcountll(avail[w] & has_v[v][w]);
                if (cnt < need) return;
                if (cnt < best_cnt) { best_cnt = cnt; best_v = v; }
            }
        }
        if (total_min_need > 7 * rem_sets) return;

        vector<u64> cur_avail = avail;
        for (int w = 0; w < nwords; ++w) {
            u64 bits = (best_v == -1) ? avail[w] : (avail[w] & has_v[best_v][w]);
            while (bits) {
                int b = __builtin_ctzll(bits);
                bits ^= (1ULL << b);
                int idx = (w << 6) | b;
                cur_avail[w] &= ~(1ULL << b);

                u32 mask = I7[idx];
                Bitset nm1, nm2;
                for (int k = 0; k < nwords; ++k) {
                    nm2.w[k] = m2.w[k] | (m1.w[k] & miss7[idx].w[k]);
                    nm1.w[k] = m1.w[k] | miss7[idx].w[k];
                }
                vector<u64> next_avail(nwords, 0);
                for (int k = 0; k < nwords; ++k) next_avail[k] = cur_avail[k] & compat7[idx][k];

                bool ok = true;
                vector<int> vs;
                u32 tmp = mask;
                while (tmp) {
                    int v = __builtin_ctz(tmp);
                    tmp ^= (1u << v);
                    vs.push_back(v);
                    dS[v]++;
                    if (dS[v] == max_dS[v]) {
                        for (int k = 0; k < nwords; ++k) next_avail[k] &= ~has_v[v][k];
                    }
                }
                for (size_t a = 0; a < vs.size() && ok; ++a) {
                    for (size_t c = a + 1; c < vs.size(); ++c) {
                        int u = vs[a], v = vs[c];
                        pcnt[u][v]++; pcnt[v][u]++;
                        if (pcnt[u][v] > tcap[u][v]) ok = false;
                        else if (pcnt[u][v] == tcap[u][v]) {
                            for (int k = 0; k < nwords; ++k)
                                next_avail[k] &= ~(has_v[u][k] & has_v[v][k]);
                        }
                    }
                }
                if (ok) {
                    if (depth + 1 < 7) {
                        for (int k = 0; k < nwords; ++k) {
                            u64 x = next_avail[k], keep = 0;
                            while (x) {
                                int bb = __builtin_ctzll(x);
                                x ^= (1ULL << bb);
                                int j = (k << 6) | bb;
                                if (!nm2.intersects(miss7[j], nwords)) keep |= (1ULL << bb);
                            }
                            next_avail[k] = keep;
                        }
                    }
                    chosen.push_back(idx);
                    self(self, depth + 1, move(next_avail), nm1, nm2);
                    chosen.pop_back();
                }
                for (size_t a = 0; a < vs.size(); ++a) {
                    for (size_t c = a + 1; c < vs.size(); ++c) {
                        int u = vs[a], v = vs[c];
                        pcnt[u][v]--; pcnt[v][u]--;
                    }
                }
                for (int v : vs) dS[v]--;

                if (best_v != -1) {
                    int rem_v = 0;
                    for (int k = 0; k < nwords; ++k)
                        rem_v += __builtin_popcountll(cur_avail[k] & has_v[best_v][k]);
                    if (rem_v < min_dS[best_v] - dS[best_v]) return;
                }
            }
        }
    };

    dfs(dfs, 0, init_avail, init_m1, init_m2);
    double elapsed = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
    cout << "DONE! nodes=" << nodes << " valid_S=" << valid_S << " valid_full=" << valid_full
         << " elapsed=" << fixed << setprecision(3) << elapsed << "s\n";
    return 0;
}
