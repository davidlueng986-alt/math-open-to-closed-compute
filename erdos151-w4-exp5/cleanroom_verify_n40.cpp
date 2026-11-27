// Clean-room independent verifier for Erdős #151 n=40 closure (Wave 4 Explorer 5)
// Independently verifies:
//   (1) Exhaustive classification of ALL 8-vertex mc-unextendable links with e=10 (all Delta <= 7)
//       => EXACTLY 3 links (L26, L35, L36), all triangle-free with delta = 2.
//   (2) Exhaustive classification & non-(3,3)-Ramsey certification of ALL connected 8-regular
//       {L26, L35, L36}-local graphs of order n <= 39 using a clean-room grower
//       (NO verts_by_sig, simple max-degree vertex selection, independent triangle-free 2-coloring witness verifier).

#include <bits/stdc++.h>
using namespace std;

struct Link8 {
    uint8_t adj[8];
    int e;
    int tris;
    array<int,8> deg;
    vector<array<uint8_t,8>> auts;
};

uint64_t canon8(const uint8_t adj[8]) {
    array<vector<int>, 8> b;
    for (int i = 0; i < 8; i++) b[__builtin_popcount(adj[i])].push_back(i);
    vector<int> p;
    vector<pair<int,int>> rng;
    for (int d = 7; d >= 0; d--) {
        if (!b[d].empty()) {
            int s = p.size();
            for (int v : b[d]) p.push_back(v);
            rng.push_back({s, (int)p.size()});
        }
    }
    uint64_t best = ~0ULL;
    function<void(int)> rec = [&](int idx) {
        if (idx == (int)rng.size()) {
            uint64_t code = 0; int bit = 0;
            for (int i = 0; i < 8; i++)
                for (int j = i + 1; j < 8; j++, bit++)
                    if ((adj[p[i]] >> p[j]) & 1) code |= (1ULL << bit);
            if (code < best) best = code;
            return;
        }
        int l = rng[idx].first, r = rng[idx].second;
        sort(p.begin() + l, p.begin() + r);
        do { rec(idx + 1); } while (next_permutation(p.begin() + l, p.begin() + r));
    };
    rec(0);
    return best;
}

bool is_mc_unextendable_8(const uint8_t adj[8]) {
    vector<uint8_t> mc;
    function<void(uint8_t, uint8_t, uint8_t)> bk = [&](uint8_t R, uint8_t P, uint8_t X) {
        if (P == 0 && X == 0) { mc.push_back(R); return; }
        int u = __builtin_ctz(P | X);
        uint8_t cand = P & ~adj[u];
        while (cand) {
            int v = __builtin_ctz(cand);
            uint8_t bit = 1 << v;
            bk(R | bit, P & adj[v], X & adj[v]);
            P &= ~bit; X |= bit; cand &= ~bit;
        }
    };
    bk(0, 0xFF, 0);

    vector<pair<int,int>> edges;
    int eidx[8][8]; memset(eidx, -1, sizeof(eidx));
    for (int i = 0; i < 8; i++)
        for (int j = i + 1; j < 8; j++)
            if ((adj[i] >> j) & 1) {
                eidx[i][j] = eidx[j][i] = (int)edges.size();
                edges.push_back({i, j});
            }
    int m = edges.size();
    vector<array<int,3>> tris;
    for (int i = 0; i < 8; i++)
        for (int j = i + 1; j < 8; j++) if ((adj[i] >> j) & 1)
            for (int k = j + 1; k < 8; k++) if (((adj[i] >> k) & 1) && ((adj[j] >> k) & 1))
                tris.push_back({eidx[i][j], eidx[i][k], eidx[j][k]});

    vector<uint32_t> mc_em(mc.size(), 0);
    for (size_t ci = 0; ci < mc.size(); ci++)
        for (int ei = 0; ei < m; ei++)
            if (((mc[ci] >> edges[ei].first) & 1) && ((mc[ci] >> edges[ei].second) & 1))
                mc_em[ci] |= (1u << ei);

    for (uint32_t R = 0; R < (1u << m); R++) {
        bool tri = false;
        for (auto &t : tris)
            if (((R >> t[0]) & 1) && ((R >> t[1]) & 1) && ((R >> t[2]) & 1)) { tri = true; break; }
        if (tri) continue;
        uint8_t radj[8] = {0};
        for (int ei = 0; ei < m; ei++) if ((R >> ei) & 1) {
            radj[edges[ei].first] |= (1 << edges[ei].second);
            radj[edges[ei].second] |= (1 << edges[ei].first);
        }
        vector<uint8_t> unhit;
        for (size_t ci = 0; ci < mc.size(); ci++)
            if ((mc_em[ci] & R) == 0) unhit.push_back(mc[ci]);
        bool okA = false;
        function<void(int, uint8_t, uint8_t)> dfsA = [&](int idx, uint8_t A, uint8_t forb) {
            if (okA) return;
            if (idx == (int)unhit.size()) { okA = true; return; }
            if (unhit[idx] & A) { dfsA(idx + 1, A, forb); return; }
            uint8_t cand = unhit[idx] & ~forb;
            while (cand && !okA) {
                int v = __builtin_ctz(cand);
                uint8_t bit = 1 << v;
                dfsA(idx + 1, A | bit, forb | bit | radj[v]);
                cand &= ~bit;
            }
        };
        dfsA(0, 0, 0);
        if (!okA) return true;
    }
    return false;
}

vector<Link8> enumerate_e10_links() {
    vector<array<int,8>> dseqs;
    array<int,8> cur;
    function<void(int, int, int)> gen_ds = [&](int idx, int maxv, int rem) {
        if (idx == 8) { if (rem == 0) dseqs.push_back(cur); return; }
        int left = 8 - idx;
        if (rem > left * maxv) return;
        for (int v = min(maxv, rem); v >= 0; v--) {
            cur[idx] = v;
            gen_ds(idx + 1, v, rem - v);
        }
    };
    gen_ds(0, 7, 20);

    unordered_set<uint64_t> seen;
    vector<Link8> unext;
    for (auto ds : dseqs) {
        uint8_t adj[8] = {0};
        int rem[8]; for (int i = 0; i < 8; i++) rem[i] = ds[i];
        function<void(int, int)> bt = [&](int u, int v) {
            while (u < 8 && rem[u] == 0) { u++; v = u + 1; }
            if (u == 8) {
                uint64_t code = canon8(adj);
                if (seen.insert(code).second) {
                    if (is_mc_unextendable_8(adj)) {
                        Link8 L;
                        memcpy(L.adj, adj, 8);
                        L.e = 10; L.tris = 0;
                        for (int i = 0; i < 8; i++) L.deg[i] = __builtin_popcount(adj[i]);
                        for (int i = 0; i < 8; i++)
                            for (int j = i + 1; j < 8; j++) if ((adj[i] >> j) & 1)
                                for (int k = j + 1; k < 8; k++) if (((adj[i] >> k) & 1) && ((adj[j] >> k) & 1))
                                    L.tris++;
                        array<uint8_t,8> p = {0,1,2,3,4,5,6,7};
                        do {
                            bool ok = true;
                            for (int i = 0; i < 8 && ok; i++)
                                for (int j = i + 1; j < 8; j++)
                                    if (((adj[i] >> j) & 1) != ((adj[p[i]] >> p[j]) & 1)) ok = false;
                            if (ok) L.auts.push_back(p);
                        } while (next_permutation(p.begin(), p.end()));
                        unext.push_back(L);
                    }
                }
                return;
            }
            if (v == 8) return;
            int avail = 0;
            for (int w = v; w < 8; w++) if (rem[w] > 0) avail++;
            if (avail < rem[u]) return;
            if (rem[v] > 0) {
                adj[u] |= (1 << v); adj[v] |= (1 << u);
                rem[u]--; rem[v]--;
                bt(u, v + 1);
                adj[u] &= ~(1 << v); adj[v] &= ~(1 << u);
                rem[u]++; rem[v]++;
            }
            if (avail - (rem[v] > 0 ? 1 : 0) >= rem[u]) bt(u, v + 1);
        };
        bt(0, 1);
    }
    cout << "[PART 1] Total non-isomorphic 8-vertex e=10 graphs (all Delta<=7): " << seen.size()
         << ", mc-unextendable: " << unext.size() << "\n";
    for (size_t i = 0; i < unext.size(); i++) {
        cout << "  Link #" << i << ": deg=[";
        for (int j = 0; j < 8; j++) cout << unext[i].deg[j] << (j==7?"]":",");
        cout << " tris=" << unext[i].tris << " |Aut|=" << unext[i].auts.size() << "\n";
    }
    return unext;
}

mt19937 rng_clean(20261127);

bool verify_non_ramsey_k4free(int n, const uint64_t adj[64]) {
    int eidx[64][64]; memset(eidx, -1, sizeof(eidx));
    vector<pair<int,int>> edges;
    for (int i = 0; i < n; i++) {
        if (__builtin_popcountll(adj[i]) != 8) return false;
        for (int j = i + 1; j < n; j++)
            if ((adj[i] >> j) & 1ULL) {
                eidx[i][j] = eidx[j][i] = (int)edges.size();
                edges.push_back({i, j});
            }
    }
    int M = edges.size();
    vector<array<int,3>> tris;
    vector<vector<int>> et(M);
    for (int i = 0; i < n; i++)
        for (int j = i + 1; j < n; j++) if ((adj[i] >> j) & 1ULL) {
            uint64_t cn = adj[i] & adj[j];
            for (int k = j + 1; k < n; k++) if ((cn >> k) & 1ULL) {
                if (cn & adj[k]) return false;
                int tid = tris.size();
                int e1 = eidx[i][j], e2 = eidx[i][k], e3 = eidx[j][k];
                tris.push_back({e1, e2, e3});
                et[e1].push_back(tid); et[e2].push_back(tid); et[e3].push_back(tid);
            }
        }
    for (int e = 0; e < M; e++) if (et[e].empty()) return false;
    int T = tris.size();
    vector<int> col(M), tsum(T), bad, bpos(T, -1);
    for (int r = 0; r < 10; r++) {
        for (int e = 0; e < M; e++) col[e] = rng_clean() & 1;
        bad.clear(); fill(bpos.begin(), bpos.end(), -1);
        for (int t = 0; t < T; t++) {
            tsum[t] = col[tris[t][0]] + col[tris[t][1]] + col[tris[t][2]];
            if (tsum[t] == 0 || tsum[t] == 3) { bpos[t] = bad.size(); bad.push_back(t); }
        }
        for (int step = 0; step < 8000 && !bad.empty(); step++) {
            int t = bad[rng_clean() % bad.size()];
            int ce = tris[t][rng_clean() % 3];
            if ((rng_clean() % 10) < 7) {
                int best = 1e9;
                for (int k = 0; k < 3; k++) {
                    int e = tris[t][k], d = col[e] ? -1 : 1, del = 0;
                    for (int tid : et[e]) {
                        int ob = (tsum[tid] == 0 || tsum[tid] == 3);
                        int nb = (tsum[tid] + d == 0 || tsum[tid] + d == 3);
                        del += nb - ob;
                    }
                    if (del < best) { best = del; ce = e; }
                }
            }
            int d = col[ce] ? -1 : 1; col[ce] ^= 1;
            for (int tid : et[ce]) {
                int ob = (tsum[tid] == 0 || tsum[tid] == 3);
                tsum[tid] += d;
                int nb = (tsum[tid] == 0 || tsum[tid] == 3);
                if (ob && !nb) {
                    int p = bpos[tid], last = bad.back();
                    bad[p] = last; bpos[last] = p; bad.pop_back(); bpos[tid] = -1;
                } else if (!ob && nb) {
                    bpos[tid] = bad.size(); bad.push_back(tid);
                }
            }
        }
        if (bad.empty()) {
            for (int i = 0; i < n; i++)
                for (int j = i + 1; j < n; j++) if ((adj[i] >> j) & 1ULL)
                    for (int k = j + 1; k < n; k++) if (((adj[i] >> k) & 1ULL) && ((adj[j] >> k) & 1ULL)) {
                        int s = col[eidx[i][j]] + col[eidx[i][k]] + col[eidx[j][k]];
                        if (s == 0 || s == 3) return false;
                    }
            return true;
        }
    }
    return false;
}

struct CleanState {
    int n;
    uint64_t adj[64];
    uint64_t forb[64];
    uint8_t deg[64];
    bool closed[64];
};

struct CleanStats {
    uint64_t nodes = 0, cap = 0, found = 0, cert = 0, unres = 0;
    map<int, uint64_t> by_n;
};

void run_clean_grower(const vector<Link8> &allowed, int root_idx, int nmax, CleanStats &stats) {
    CleanState st0; memset(&st0, 0, sizeof(st0));
    st0.n = 9; st0.closed[0] = true;
    for (int i = 1; i <= 8; i++) {
        st0.adj[0] |= (1ULL << i); st0.adj[i] |= (1ULL << 0);
        st0.deg[0]++; st0.deg[i]++;
    }
    const auto &R = allowed[root_idx];
    for (int a = 0; a < 8; a++)
        for (int b = a + 1; b < 8; b++) {
            if ((R.adj[a] >> b) & 1) {
                st0.adj[a+1] |= (1ULL << (b+1)); st0.adj[b+1] |= (1ULL << (a+1));
                st0.deg[a+1]++; st0.deg[b+1]++;
            } else {
                st0.forb[a+1] |= (1ULL << (b+1)); st0.forb[b+1] |= (1ULL << (a+1));
            }
        }

    function<void(const CleanState&)> dfs = [&](const CleanState &st) {
        stats.nodes++;
        int u = -1, best_d = -1;
        for (int i = 0; i < st.n; i++) {
            if (!st.closed[i] && st.deg[i] > best_d) { best_d = st.deg[i]; u = i; }
        }
        if (u == -1) {
            stats.found++;
            stats.by_n[st.n]++;
            if (verify_non_ramsey_k4free(st.n, st.adj)) stats.cert++;
            else stats.unres++;
            return;
        }
        int S[8], k = 0;
        uint64_t m = st.adj[u];
        while (m) { S[k++] = __builtin_ctzll(m); m &= m - 1; }
        int r = 8 - k;

        uint8_t se[8] = {0}, sf[8] = {0};
        int sd[8] = {0};
        for (int i = 0; i < k; i++)
            for (int j = i + 1; j < k; j++) {
                if ((st.adj[S[i]] >> S[j]) & 1ULL) {
                    se[i] |= (1 << j); se[j] |= (1 << i); sd[i]++; sd[j]++;
                } else if ((st.forb[S[i]] >> S[j]) & 1ULL) {
                    sf[i] |= (1 << j); sf[j] |= (1 << i);
                }
            }

        int cands[64], ncands = 0;
        uint64_t bad = st.adj[u] | st.forb[u] | (1ULL << u);
        for (int w = 0; w < st.n; w++)
            if (!st.closed[w] && !((bad >> w) & 1ULL)) cands[ncands++] = w;

        for (size_t li = 0; li < allowed.size(); li++) {
            const auto &L = allowed[li];
            uint8_t phi[8];
            function<void(int, uint8_t)> mapS = [&](int idx, uint8_t used) {
                if (idx == k) {
                    for (const auto &aut : L.auts) {
                        int cmp = 0;
                        for (int i = 0; i < k; i++) {
                            if (aut[phi[i]] < phi[i]) { cmp = -1; break; }
                            if (aut[phi[i]] > phi[i]) { cmp = 1; break; }
                        }
                        if (cmp < 0) return;
                    }
                    for (int i = 0; i < k; i++) {
                        int addS = __builtin_popcount(L.adj[phi[i]] & used) - sd[i];
                        if (st.deg[S[i]] + addS > 8) return;
                    }
                    vector<array<uint8_t,8>> stab;
                    for (const auto &aut : L.auts) {
                        bool fix = true;
                        for (int i = 0; i < k; i++) if (aut[phi[i]] != phi[i]) { fix = false; break; }
                        if (fix) stab.push_back(aut);
                    }
                    uint8_t remL[8]; int nr = 0;
                    for (int x = 0; x < 8; x++) if (!((used >> x) & 1)) remL[nr++] = x;
                    int assign[8];
                    for (int i = 0; i < k; i++) assign[phi[i]] = S[i];

                    uint64_t used_c = 0;
                    function<void(int, int)> assignR = [&](int j, int cur_n) {
                        if (j == r) {
                            if (stab.size() > 1) {
                                for (const auto &aut : stab) {
                                    int cmp = 0;
                                    for (int t = 0; t < r; t++) {
                                        int x = remL[t];
                                        if (assign[aut[x]] < assign[x]) { cmp = -1; break; }
                                        if (assign[aut[x]] > assign[x]) { cmp = 1; break; }
                                    }
                                    if (cmp < 0) return;
                                }
                            }
                            CleanState nxt = st;
                            nxt.n = cur_n; nxt.closed[u] = true;
                            for (int t = 0; t < r; t++) {
                                int w = assign[remL[t]];
                                if (w >= st.n) {
                                    nxt.adj[w] = 0; nxt.forb[w] = 0; nxt.deg[w] = 0; nxt.closed[w] = false;
                                    for (int z = 0; z < st.n; z++) if (st.closed[z]) {
                                        nxt.forb[z] |= (1ULL << w); nxt.forb[w] |= (1ULL << z);
                                    }
                                }
                                if ((nxt.forb[u] >> w) & 1ULL) return;
                                if (!((nxt.adj[u] >> w) & 1ULL)) {
                                    nxt.adj[u] |= (1ULL << w); nxt.adj[w] |= (1ULL << u);
                                    nxt.deg[u]++; nxt.deg[w]++;
                                    if (nxt.deg[w] > 8) return;
                                }
                            }
                            uint64_t allm = (cur_n == 64 ? ~0ULL : ((1ULL << cur_n) - 1ULL));
                            uint64_t nonu = allm & ~nxt.adj[u] & ~(1ULL << u);
                            nxt.forb[u] |= nonu;
                            uint64_t tmp = nonu;
                            while (tmp) { int z = __builtin_ctzll(tmp); nxt.forb[z] |= (1ULL << u); tmp &= tmp - 1; }

                            for (int a = 0; a < 8; a++) {
                                int va = assign[a];
                                for (int b = a + 1; b < 8; b++) {
                                    int vb = assign[b];
                                    bool want = (L.adj[a] >> b) & 1;
                                    bool has = (nxt.adj[va] >> vb) & 1ULL;
                                    if (want) {
                                        if (!has) {
                                            if ((nxt.forb[va] >> vb) & 1ULL) return;
                                            nxt.adj[va] |= (1ULL << vb); nxt.adj[vb] |= (1ULL << va);
                                            nxt.deg[va]++; nxt.deg[vb]++;
                                            if (nxt.deg[va] > 8 || nxt.deg[vb] > 8) return;
                                        }
                                    } else {
                                        if (has) return;
                                        nxt.forb[va] |= (1ULL << vb); nxt.forb[vb] |= (1ULL << va);
                                    }
                                }
                            }
                            for (int a = 0; a < 8; a++) {
                                int va = assign[a];
                                uint64_t na = nxt.adj[va], t = na;
                                int ein = 0;
                                while (t) {
                                    int w = __builtin_ctzll(t);
                                    uint64_t cn = na & nxt.adj[w];
                                    int c = __builtin_popcountll(cn);
                                    if (c > 4) return;
                                    uint64_t c2 = cn;
                                    while (c2) {
                                        int z = __builtin_ctzll(c2);
                                        if (nxt.adj[z] & cn) return;
                                        c2 &= c2 - 1;
                                    }
                                    ein += c;
                                    t &= t - 1;
                                }
                                if (ein / 2 > 10) return;
                            }
                            dfs(nxt);
                            return;
                        }
                        int x = remL[j];
                        for (int ci = 0; ci < ncands; ci++) {
                            int w = cands[ci];
                            if ((used_c >> w) & 1ULL) continue;
                            bool ok = true; int addw = 1;
                            for (int i = 0; i < k && ok; i++) {
                                bool want = (L.adj[x] >> phi[i]) & 1;
                                bool has = (st.adj[w] >> S[i]) & 1ULL;
                                if (want) {
                                    if (!has) { if ((st.forb[w] >> S[i]) & 1ULL) ok = false; else addw++; }
                                } else if (has) ok = false;
                            }
                            for (int p = 0; p < j && ok; p++) {
                                int vy = assign[remL[p]];
                                bool want = (L.adj[x] >> remL[p]) & 1;
                                if (vy >= st.n) { if (want) addw++; }
                                else {
                                    bool has = (st.adj[w] >> vy) & 1ULL;
                                    if (want) {
                                        if (!has) { if ((st.forb[w] >> vy) & 1ULL) ok = false; else addw++; }
                                    } else if (has) ok = false;
                                }
                            }
                            if (ok && st.deg[w] + addw <= 8) {
                                assign[x] = w; used_c |= (1ULL << w);
                                assignR(j + 1, cur_n);
                                used_c &= ~(1ULL << w);
                            }
                        }
                        if (cur_n < nmax) {
                            bool ok = true;
                            for (int i = 0; i < k; i++)
                                if (st.closed[S[i]] && ((L.adj[x] >> phi[i]) & 1)) { ok = false; break; }
                            if (ok) {
                                assign[x] = cur_n;
                                assignR(j + 1, cur_n + 1);
                            }
                        } else {
                            stats.cap++;
                        }
                    };
                    assignR(0, st.n);
                    return;
                }
                uint8_t cand = (~used) & 0xFF;
                for (int prev = 0; prev < idx && cand; prev++) {
                    if ((se[idx] >> prev) & 1) cand &= L.adj[phi[prev]];
                    else if ((sf[idx] >> prev) & 1) cand &= ~L.adj[phi[prev]];
                }
                while (cand) {
                    int x = __builtin_ctz(cand); cand &= cand - 1;
                    if (st.closed[S[idx]] && __builtin_popcount(L.adj[x]) != sd[idx]) continue;
                    if (!st.closed[S[idx]] && __builtin_popcount(L.adj[x]) < sd[idx]) continue;
                    phi[idx] = x;
                    mapS(idx + 1, used | (1 << x));
                }
            };
            mapS(0, 0);
        }
    };
    dfs(st0);
}

int main() {
    auto t0 = chrono::steady_clock::now();
    auto links = enumerate_e10_links();
    assert(links.size() == 3);
    int idx_44 = -1;
    vector<int> idx_33;
    for (int i = 0; i < 3; i++) {
        if (links[i].deg[0] == 4) idx_44 = i;
        else idx_33.push_back(i);
    }
    assert(idx_44 != -1 && idx_33.size() == 2);

    {
        auto ts = chrono::steady_clock::now();
        CleanStats st;
        run_clean_grower(links, idx_44, 39, st);
        double sec = chrono::duration<double>(chrono::steady_clock::now() - ts).count();
        cout << "[PART 2.1] Root=[4,4,2^6] in all 3 links (nmax=39): nodes=" << st.nodes
             << " cap=" << st.cap << " found=" << st.found << " cert=" << st.cert
             << " unres=" << st.unres << " time=" << fixed << setprecision(3) << sec << "s\n";
        assert(st.cap == 0 && st.found == 0 && st.unres == 0);
    }

    vector<Link8> two = {links[idx_33[0]], links[idx_33[1]]};
    {
        auto ts = chrono::steady_clock::now();
        CleanStats st;
        run_clean_grower(two, 1, 39, st);
        double sec = chrono::duration<double>(chrono::steady_clock::now() - ts).count();
        cout << "[PART 2.2] Root=two[1] in {two[0],two[1]} (nmax=39): nodes=" << st.nodes
             << " cap=" << st.cap << " found=" << st.found << " cert=" << st.cert
             << " unres=" << st.unres << " time=" << fixed << setprecision(3) << sec << "s";
        for (auto &[n, c] : st.by_n) cout << " [n=" << n << ":" << c << "]";
        cout << "\n";
        assert(st.unres == 0);
    }

    {
        auto ts = chrono::steady_clock::now();
        vector<Link8> one = {two[0]};
        CleanStats st;
        run_clean_grower(one, 0, 39, st);
        double sec = chrono::duration<double>(chrono::steady_clock::now() - ts).count();
        cout << "[PART 2.3] Root=two[0] in {two[0]} (nmax=39): nodes=" << st.nodes
             << " cap=" << st.cap << " found=" << st.found << " cert=" << st.cert
             << " unres=" << st.unres << " time=" << fixed << setprecision(3) << sec << "s";
        for (auto &[n, c] : st.by_n) cout << " [n=" << n << ":" << c << "]";
        cout << "\n";
        assert(st.unres == 0);
    }

    double tot = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
    cout << "=== CLEAN-ROOM VERIFICATION PASSED 100% (unresolved=0) in " << fixed << setprecision(3) << tot << "s ===\n";
    return 0;
}
