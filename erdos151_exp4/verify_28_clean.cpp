#include <bits/stdc++.h>
using namespace std;

struct Link {
    int id, e, tris, k4s, alpha;
    string ds;
    uint64_t code;
    uint8_t adj[8];
    int deg[8];
    vector<array<int,8>> auts;
};

vector<Link> load_links() {
    vector<Link> links;
    ifstream fin("erdos151_exp4/mc37_links.txt");
    Link L;
    while (fin >> L.id >> L.e >> L.ds >> L.code >> L.tris >> L.k4s >> L.alpha) {
        memset(L.adj, 0, 8); L.auts.clear();
        int bit = 0;
        for (int i = 0; i < 8; i++)
            for (int j = i + 1; j < 8; j++, bit++)
                if ((L.code >> bit) & 1) { L.adj[i] |= (1 << j); L.adj[j] |= (1 << i); }
        for (int i = 0; i < 8; i++) L.deg[i] = __builtin_popcount(L.adj[i]);
        array<int,8> p = {0,1,2,3,4,5,6,7};
        do {
            bool ok = true;
            for (int i = 0; i < 8 && ok; i++) {
                if (L.deg[p[i]] != L.deg[i]) { ok = false; break; }
                for (int j = i + 1; j < 8; j++)
                    if (((L.adj[i] >> j) & 1) != ((L.adj[p[i]] >> p[j]) & 1)) { ok = false; break; }
            }
            if (ok) L.auts.push_back(p);
        } while (next_permutation(p.begin(), p.end()));
        links.push_back(L);
    }
    return links;
}

// CLEAN-ROOM VERIFIER: NO matching pruning (purely n + sum(8 - deg[i]) >= 30)
struct CleanBall2Verifier {
    vector<Link> links;
    vector<int> allowed_ids;
    int max_delta = 4, max_n = 40, min_b2_size = 30;
    long long nodes = 0, node_limit = 5000000;
    bool found_valid = false, hit_limit = false;
    int max_n_seen = 0;

    static const int MAXV = 52;
    uint64_t adj1[MAXV], adj0[MAXV];
    int deg[MAXV]; bool closed[MAXV]; int n;
    struct Change { int u, v; };
    vector<Change> undo_stack;

    inline int8_t get_e(int u, int v) const {
        if ((adj1[u] >> v) & 1ULL) return 1;
        if ((adj0[u] >> v) & 1ULL) return 0;
        return -1;
    }
    bool set_edge(int u, int v, int8_t val) {
        if (u == v) return val == 0;
        int8_t cur = get_e(u, v);
        if (cur == val) return true;
        if (cur != -1) return false;
        if (val == 1) {
            if (deg[u] >= 8 || deg[v] >= 8 || closed[u] || closed[v]) return false;
            uint64_t cn = adj1[u] & adj1[v];
            if (__builtin_popcountll(cn) > max_delta) return false;
            uint64_t m = cn;
            while (m) {
                int w = __builtin_ctzll(m); m &= m - 1;
                if (__builtin_popcountll(adj1[u] & adj1[w]) + 1 > max_delta) return false;
                if (__builtin_popcountll(adj1[v] & adj1[w]) + 1 > max_delta) return false;
            }
            deg[u]++; deg[v]++;
            adj1[u] |= (1ULL << v); adj1[v] |= (1ULL << u);
        } else {
            adj0[u] |= (1ULL << v); adj0[v] |= (1ULL << u);
        }
        undo_stack.push_back({u, v});
        return true;
    }
    void rollback(size_t mark) {
        while (undo_stack.size() > mark) {
            auto c = undo_stack.back(); undo_stack.pop_back();
            if ((adj1[c.u] >> c.v) & 1ULL) {
                deg[c.u]--; deg[c.v]--;
                adj1[c.u] &= ~(1ULL << c.v); adj1[c.v] &= ~(1ULL << c.u);
            } else {
                adj0[c.u] &= ~(1ULL << c.v); adj0[c.v] &= ~(1ULL << c.u);
            }
        }
    }
    int trivial_ub_excl(int skip_u = -1) const {
        int rem = 0;
        for (int i = 1; i <= 8; i++)
            if (!closed[i] && i != skip_u) rem += (8 - deg[i]);
        return n + rem;
    }
    struct CloseOpt { int lid; int map_v[8]; int added_new; };
    bool test_apply(int u, const CloseOpt& co) {
        const Link& L = links[co.lid];
        int old_n = n; size_t mark = undo_stack.size();
        n += co.added_new;
        for (int x = old_n; x < n; x++) { deg[x] = 0; closed[x] = false; adj1[x] = 0; adj0[x] = (1ULL << x); }
        bool ok = true;
        uint64_t nu_mask = 0; for (int p = 0; p < 8; p++) nu_mask |= (1ULL << co.map_v[p]);
        for (int w = 0; w < n && ok; w++) if (w != u && !set_edge(u, w, ((nu_mask >> w) & 1ULL) ? 1 : 0)) ok = false;
        for (int a = 0; a < 8 && ok; a++)
            for (int b = a + 1; b < 8 && ok; b++)
                if (!set_edge(co.map_v[a], co.map_v[b], ((L.adj[a] >> b) & 1) ? 1 : 0)) ok = false;
        rollback(mark); n = old_n;
        return ok;
    }
    vector<CloseOpt> get_close_opts(int u, int limit = 100000) {
        vector<CloseOpt> opts;
        int nb[8], k = 0; uint64_t m = adj1[u];
        while (m) { int w = __builtin_ctzll(m); m &= m - 1; nb[k++] = w; }
        uint8_t s1[8] = {0}, s0[8] = {0}; int sdeg[8] = {0}, maxd[8];
        uint64_t cand_mask = 0;
        for (int w = 0; w < n; w++)
            if (w != u && !closed[w] && get_e(u, w) == -1 && deg[w] < 8) cand_mask |= (1ULL << w);
        for (int i = 0; i < k; i++) {
            for (int j = 0; j < k; j++) {
                if ((adj1[nb[i]] >> nb[j]) & 1ULL) { s1[i] |= (1 << j); sdeg[i]++; }
                else if ((adj0[nb[i]] >> nb[j]) & 1ULL) { s0[i] |= (1 << j); }
            }
            maxd[i] = closed[nb[i]] ? sdeg[i] + __builtin_popcountll(adj1[nb[i]] & cand_mask) : max_delta;
        }
        int base_other = trivial_ub_excl(u) - n;
        for (int lid : allowed_ids) {
            const Link& L = links[lid];
            set<array<int,8>> seen_emb;
            int map_v[8]; for (int i = 0; i < 8; i++) map_v[i] = -1;
            int mp[8]; uint8_t used_p = 0;
            function<void(int)> match_nb = [&](int idx) {
                if ((int)opts.size() >= limit) return;
                if (idx == k) {
                    array<int,8> canon_mv; canon_mv.fill(1000000);
                    for (auto &aut : L.auts) {
                        array<int,8> cur; for (int p = 0; p < 8; p++) cur[aut[p]] = map_v[p];
                        if (cur < canon_mv) canon_mv = cur;
                    }
                    if (!seen_emb.insert(canon_mv).second) return;
                    vector<int> rem_pos;
                    for (int p = 0; p < 8; p++) if (map_v[p] == -1) rem_pos.push_back(p);
                    int r_tot = rem_pos.size();
                    sort(rem_pos.begin(), rem_pos.end(), [&](int a, int b) {
                        int ca = 0, cb = 0;
                        for (int p = 0; p < 8; p++) if (map_v[p] != -1 && closed[map_v[p]]) {
                            if ((L.adj[a] >> p) & 1) ca++;
                            if ((L.adj[b] >> p) & 1) cb++;
                        }
                        return ca > cb;
                    });
                    set<array<int,8>> seen_full;
                    function<void(int, int, uint64_t)> fill_rem = [&](int ridx, int added_new, uint64_t used_w) {
                        if ((int)opts.size() >= limit) return;
                        if (n + added_new + (r_tot - ridx) + base_other < min_b2_size) return;
                        if (ridx == r_tot) {
                            CloseOpt co; co.lid = lid; co.added_new = added_new;
                            for (int p = 0; p < 8; p++) co.map_v[p] = map_v[p];
                            if (!test_apply(u, co)) return;
                            array<int,8> best_f; best_f.fill(1000000);
                            for (auto &aut : L.auts) {
                                array<int,8> cur; int new_map[8], nxt_new = n;
                                memset(new_map, -1, sizeof(new_map));
                                for (int p = 0; p < 8; p++) cur[aut[p]] = map_v[p];
                                for (int q = 0; q < 8; q++) if (cur[q] >= n) {
                                    int id = cur[q] - n;
                                    if (new_map[id] == -1) new_map[id] = nxt_new++;
                                    cur[q] = new_map[id];
                                }
                                if (cur < best_f) best_f = cur;
                            }
                            if (!seen_full.insert(best_f).second) return;
                            opts.push_back(co);
                            return;
                        }
                        int pos = rem_pos[ridx];
                        uint64_t valid_c = cand_mask & ~used_w;
                        bool must_adj_closed = false;
                        for (int p = 0; p < 8; p++) {
                            if (map_v[p] == -1 || map_v[p] >= n) continue;
                            int vp = map_v[p];
                            if ((L.adj[pos] >> p) & 1) {
                                if (closed[vp]) { valid_c &= adj1[vp]; must_adj_closed = true; }
                                else valid_c &= ~adj0[vp];
                            } else valid_c &= ~adj1[vp];
                        }
                        uint64_t cm = valid_c;
                        while (cm) {
                            int w = __builtin_ctzll(cm); cm &= cm - 1;
                            int add_d = 1;
                            for (int p = 0; p < 8; p++)
                                if (map_v[p] != -1 && ((L.adj[pos] >> p) & 1))
                                    if (map_v[p] >= n || !((adj1[w] >> map_v[p]) & 1ULL)) add_d++;
                            if (deg[w] + add_d > 8) continue;
                            map_v[pos] = w; fill_rem(ridx + 1, added_new, used_w | (1ULL << w)); map_v[pos] = -1;
                        }
                        if (!must_adj_closed && n + added_new + 1 <= max_n) {
                            map_v[pos] = n + added_new;
                            fill_rem(ridx + 1, added_new + 1, used_w);
                            map_v[pos] = -1;
                        }
                    };
                    fill_rem(0, 0, 0);
                    return;
                }
                for (int p = 0; p < 8; p++) {
                    if ((used_p >> p) & 1) continue;
                    if (L.deg[p] < sdeg[idx] || L.deg[p] > maxd[idx]) continue;
                    bool ok = true;
                    for (int j = 0; j < idx; j++) {
                        int eL = (L.adj[p] >> mp[j]) & 1;
                        if ((((s1[idx] >> j) & 1) && !eL) || (((s0[idx] >> j) & 1) && eL)) { ok = false; break; }
                    }
                    if (!ok) continue;
                    used_p |= (1 << p); mp[idx] = p; map_v[p] = nb[idx];
                    match_nb(idx + 1);
                    map_v[p] = -1; used_p &= ~(1 << p);
                }
            };
            match_nb(0);
        }
        return opts;
    }
    void dfs() {
        if (found_valid || hit_limit) return;
        nodes++;
        if (nodes > node_limit) { hit_limit = true; return; }
        if (trivial_ub_excl(-1) < min_b2_size) return;
        int best_u = -1, best_cnt = 1e9;
        vector<CloseOpt> best_opts;
        int open_n1 = 0;
        for (int i = 1; i <= 8; i++) {
            if (closed[i]) continue;
            open_n1++;
            auto opts = get_close_opts(i, best_cnt);
            if ((int)opts.size() < best_cnt) {
                best_cnt = opts.size(); best_u = i; best_opts = move(opts);
                if (best_cnt == 0) return;
                if (best_cnt == 1) break;
            }
        }
        if (open_n1 == 0) {
            if (n > max_n_seen) max_n_seen = n;
            if (n >= min_b2_size) found_valid = true;
            return;
        }
        for (auto &co : best_opts) {
            if (found_valid || hit_limit) return;
            const Link& L = links[co.lid];
            int old_n = n; size_t mark = undo_stack.size();
            n += co.added_new;
            for (int x = old_n; x < n; x++) { deg[x] = 0; closed[x] = false; adj1[x] = 0; adj0[x] = (1ULL << x); }
            bool ok = true;
            uint64_t nu_mask = 0; for (int p = 0; p < 8; p++) nu_mask |= (1ULL << co.map_v[p]);
            for (int w = 0; w < n && ok; w++) if (w != best_u && !set_edge(best_u, w, ((nu_mask >> w) & 1ULL) ? 1 : 0)) ok = false;
            for (int a = 0; a < 8 && ok; a++)
                for (int b = a + 1; b < 8 && ok; b++)
                    if (!set_edge(co.map_v[a], co.map_v[b], ((L.adj[a] >> b) & 1) ? 1 : 0)) ok = false;
            if (ok) { closed[best_u] = true; dfs(); closed[best_u] = false; }
            rollback(mark); n = old_n;
        }
    }
    bool test_root(int root_lid) {
        memset(adj1, 0, sizeof(adj1)); memset(adj0, 0, sizeof(adj0));
        memset(deg, 0, sizeof(deg)); memset(closed, 0, sizeof(closed));
        undo_stack.clear(); nodes = 0; found_valid = false; hit_limit = false; max_n_seen = 0;
        n = 9; for (int i = 0; i < 9; i++) adj0[i] = (1ULL << i);
        const Link& L0 = links[root_lid];
        for (int i = 0; i < 8; i++) set_edge(0, i + 1, 1);
        for (int i = 0; i < 8; i++)
            for (int j = i + 1; j < 8; j++)
                set_edge(i + 1, j + 1, ((L0.adj[i] >> j) & 1) ? 1 : 0);
        closed[0] = true;
        dfs();
        return found_valid;
    }
};

int main() {
    auto links = load_links();
    CleanBall2Verifier S; S.links = links;
    int total_ok = 0;
    auto run_stage = [&](const string& name, vector<int> allowed, vector<int> targets) {
        S.allowed_ids = allowed;
        cout << "=== " << name << " (|allowed|=" << allowed.size() << ") ===\n";
        int ok = 0;
        for (int id : targets) {
            bool f = S.test_root(id);
            cout << "ID=" << setw(2) << id << " e=" << links[id].e << " ds=" << links[id].ds
                 << " | found=" << f << " max_n=" << S.max_n_seen << " nodes=" << S.nodes << " lim=" << S.hit_limit << "\n" << flush;
            if (!f && !S.hit_limit) { ok++; total_ok++; }
        }
        cout << name << " verified: " << ok << "/" << targets.size() << "\n" << flush;
    };
    vector<int> f37; for (int i = 0; i < 37; i++) f37.push_back(i);
    vector<int> f24; for (int i = 0; i < 24; i++) f24.push_back(i);
    vector<int> f13 = {0,1,2,3,4,5,6,7,8,9,19,22,23};
    vector<int> f10 = {0,1,2,3,4,5,6,7,8,9};
    run_stage("STAGE 1: e=13 vs F_37", f37, {24,25,26,27,28,29,30,31,32,33,34,35,36});
    run_stage("STAGE 2: e=12 (11 links) vs F_24", f24, {10,11,12,13,14,15,16,17,18,20,21});
    run_stage("STAGE 3: e=12 (19,22,23) vs F_13", f13, {19,22,23});
    run_stage("STAGE 4: ID=5 (e=11) vs F_10", f10, {5});
    cout << "TOTAL CLEAN-ROOM VERIFIED: " << total_ok << "/28\n";
    return (total_ok == 28) ? 0 : 1;
}
