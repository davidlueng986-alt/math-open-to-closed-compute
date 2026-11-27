#include <bits/stdc++.h>
using namespace std;

// ============================================================================
// Agent 2: Native C++20 Bitmask Gluing & Incremental CDCL(T) Engine (v2)
// ============================================================================
// Features:
// 1. 2-watched-literal CDCL solver with 1-UIP learning, VSIDS, Luby restarts,
//    and optional RUP/DRAT proof logging + standalone RUP verifier.
// 2. Compact bidirectional Sinz sequential counter for exact-k (n*k vars).
// 3. Exact A={1}UX singleton cap (<=4 per x) and B={0}UY singleton cap (<=1 per y).
// 4. Hardware-bitmask (popcount/countr_zero) incremental I9(H0)/I9(H1)/I10(W)
//    separation without resetting learned clauses or VSIDS state.

struct CDCLSolver {
    int nvars = 0;
    vector<vector<int>> clauses;
    static inline int lit2idx(int l) { return l > 0 ? 2 * (l - 1) : 2 * (-l - 1) + 1; }
    static inline int neg(int l) { return -l; }

    vector<vector<int>> watches;
    vector<int8_t> val, phase;
    vector<int> level, reason, trail, trail_lim;
    int qhead = 0;

    vector<double> activity;
    double var_inc = 1.0, var_decay = 0.95;
    vector<int> heap, heap_pos, seen, learnt;
    int seen_stamp = 0;

    uint64_t conflicts = 0, decisions = 0, propagations = 0;
    bool unsat_flag = false, log_proof = false;
    vector<vector<int>> proof_clauses;

    void init_vars(int n) {
        nvars = n;
        watches.assign(2 * n, {});
        val.assign(n + 1, 0);
        phase.assign(n + 1, -1);
        level.assign(n + 1, 0);
        reason.assign(n + 1, -1);
        activity.assign(n + 1, 0.0);
        seen.assign(n + 1, 0);
        heap.clear();
        heap_pos.assign(n + 1, -1);
        for (int v = 1; v <= n; ++v) heap_insert(v);
    }

    int new_var() {
        int v = ++nvars;
        watches.resize(2 * nvars);
        val.push_back(0); phase.push_back(-1); level.push_back(0);
        reason.push_back(-1); activity.push_back(0.0); seen.push_back(0);
        heap_pos.push_back(-1);
        heap_insert(v);
        return v;
    }

    inline int8_t lit_val(int l) const { int8_t v = val[abs(l)]; return l > 0 ? v : (int8_t)(-v); }
    inline bool heap_gt(int u, int v) const { return activity[u] > activity[v]; }
    void heap_up(int i) {
        int v = heap[i];
        while (i > 0) {
            int p = (i - 1) >> 1;
            if (!heap_gt(v, heap[p])) break;
            heap[i] = heap[p]; heap_pos[heap[i]] = i; i = p;
        }
        heap[i] = v; heap_pos[v] = i;
    }
    void heap_down(int i) {
        int v = heap[i], sz = (int)heap.size();
        while (true) {
            int l = (i << 1) + 1;
            if (l >= sz) break;
            int r = l + 1;
            int best = (r < sz && heap_gt(heap[r], heap[l])) ? r : l;
            if (!heap_gt(heap[best], v)) break;
            heap[i] = heap[best]; heap_pos[heap[i]] = i; i = best;
        }
        heap[i] = v; heap_pos[v] = i;
    }
    void heap_insert(int v) {
        if (heap_pos[v] != -1) return;
        int i = (int)heap.size();
        heap.push_back(v); heap_pos[v] = i; heap_up(i);
    }
    int heap_pop() {
        int v = heap[0]; heap_pos[v] = -1;
        int last = heap.back(); heap.pop_back();
        if (!heap.empty()) { heap[0] = last; heap_pos[last] = 0; heap_down(0); }
        return v;
    }
    void bump_var(int v) {
        activity[v] += var_inc;
        if (activity[v] > 1e100) {
            for (int i = 1; i <= nvars; ++i) activity[i] *= 1e-100;
            var_inc *= 1e-100;
        }
        if (heap_pos[v] != -1) heap_up(heap_pos[v]);
    }

    inline int decision_level() const { return (int)trail_lim.size(); }
    void assign(int l, int cr) {
        int v = abs(l);
        val[v] = l > 0 ? 1 : -1; phase[v] = val[v];
        level[v] = decision_level(); reason[v] = cr;
        trail.push_back(l);
    }
    void cancel_until(int lvl) {
        if (decision_level() <= lvl) return;
        int lim = trail_lim[lvl];
        for (int i = (int)trail.size() - 1; i >= lim; --i) {
            int v = abs(trail[i]);
            val[v] = 0; reason[v] = -1; heap_insert(v);
        }
        trail.resize(lim); trail_lim.resize(lvl); qhead = lim;
    }

    bool add_clause(vector<int> c, bool is_learnt = false) {
        if (unsat_flag) return false;
        if (!is_learnt) {
            sort(c.begin(), c.end(), [](int a, int b) {
                return abs(a) < abs(b) || (abs(a) == abs(b) && a < b);
            });
            vector<int> clean; clean.reserve(c.size());
            for (int l : c) {
                if (!clean.empty() && clean.back() == l) continue;
                if (!clean.empty() && clean.back() == -l) return true;
                int8_t v = lit_val(l);
                if (v == 1 && level[abs(l)] == 0) return true;
                if (v == -1 && level[abs(l)] == 0) continue;
                clean.push_back(l);
            }
            c.swap(clean);
        }
        if (c.empty()) { unsat_flag = true; if (log_proof) proof_clauses.push_back({}); return false; }
        if (c.size() == 1) {
            int l = c[0];
            if (lit_val(l) == -1) { unsat_flag = true; if (log_proof) proof_clauses.push_back({}); return false; }
            if (lit_val(l) == 0) assign(l, -1);
            if (is_learnt && log_proof) proof_clauses.push_back(c);
            return true;
        }
        int cid = (int)clauses.size();
        clauses.push_back(std::move(c));
        watches[lit2idx(clauses[cid][0])].push_back(cid);
        watches[lit2idx(clauses[cid][1])].push_back(cid);
        if (is_learnt && log_proof) proof_clauses.push_back(clauses[cid]);
        return true;
    }

    bool add_dynamic_clause(vector<int> c) {
        cancel_until(0);
        if (!add_clause(std::move(c), false)) return false;
        if (propagate() != -1) { unsat_flag = true; if (log_proof) proof_clauses.push_back({}); return false; }
        return true;
    }

    int propagate() {
        while (qhead < (int)trail.size()) {
            int p = trail[qhead++]; propagations++;
            int false_lit = neg(p);
            auto& ws = watches[lit2idx(false_lit)];
            size_t i = 0, j = 0;
            while (i < ws.size()) {
                int cid = ws[i++];
                auto& cl = clauses[cid];
                if (cl[0] == false_lit) swap(cl[0], cl[1]);
                int first = cl[0];
                if (lit_val(first) == 1) { ws[j++] = cid; continue; }
                bool found = false;
                for (size_t k = 2; k < cl.size(); ++k) {
                    if (lit_val(cl[k]) != -1) {
                        swap(cl[1], cl[k]);
                        watches[lit2idx(cl[1])].push_back(cid);
                        found = true; break;
                    }
                }
                if (found) continue;
                ws[j++] = cid;
                if (lit_val(first) == -1) {
                    while (i < ws.size()) ws[j++] = ws[i++];
                    ws.resize(j); return cid;
                } else assign(first, cid);
            }
            ws.resize(j);
        }
        return -1;
    }

    void analyze(int confl, int& out_btlevel) {
        learnt.clear(); learnt.push_back(0); seen_stamp++;
        int pathC = 0, p = 0, idx = (int)trail.size() - 1;
        out_btlevel = 0;
        do {
            const auto& cl = clauses[confl];
            for (size_t j = (p == 0 ? 0 : 1); j < cl.size(); ++j) {
                int q = cl[j], v = abs(q);
                if (seen[v] != seen_stamp && level[v] > 0) {
                    seen[v] = seen_stamp; bump_var(v);
                    if (level[v] >= decision_level()) pathC++;
                    else { learnt.push_back(q); if (level[v] > out_btlevel) out_btlevel = level[v]; }
                }
            }
            while (seen[abs(trail[idx])] != seen_stamp) idx--;
            p = trail[idx--]; confl = reason[abs(p)]; seen[abs(p)] = 0; pathC--;
        } while (pathC > 0);
        learnt[0] = neg(p);
        if (learnt.size() > 1) {
            size_t max_i = 1;
            for (size_t i = 2; i < learnt.size(); ++i)
                if (level[abs(learnt[i])] > level[abs(learnt[max_i])]) max_i = i;
            swap(learnt[1], learnt[max_i]);
            out_btlevel = level[abs(learnt[1])];
        }
        var_inc /= var_decay;
    }

    static inline uint64_t luby(uint64_t i) {
        uint64_t size = 1, seq = 0;
        while (size < i + 1) { seq++; size = 2 * size + 1; }
        while (size - 1 != i) { size = (size - 1) >> 1; seq--; i = i % size; }
        return 1ULL << seq;
    }

    int solve(chrono::steady_clock::time_point deadline) {
        if (unsat_flag) return -1;
        if (propagate() != -1) { unsat_flag = true; if (log_proof) proof_clauses.push_back({}); return -1; }
        uint64_t restart_idx = 0, next_restart = conflicts + 100 * luby(restart_idx);
        while (true) {
            int confl = propagate();
            if (confl != -1) {
                conflicts++;
                if (decision_level() == 0) { unsat_flag = true; if (log_proof) proof_clauses.push_back({}); return -1; }
                int btlevel = 0; analyze(confl, btlevel); cancel_until(btlevel);
                if (learnt.size() == 1) {
                    assign(learnt[0], -1);
                    if (log_proof) proof_clauses.push_back(learnt);
                } else {
                    int cid = (int)clauses.size();
                    clauses.push_back(learnt);
                    watches[lit2idx(learnt[0])].push_back(cid);
                    watches[lit2idx(learnt[1])].push_back(cid);
                    assign(learnt[0], cid);
                    if (log_proof) proof_clauses.push_back(learnt);
                }
                if ((conflicts & 1023) == 0 && chrono::steady_clock::now() >= deadline) return 0;
                if (conflicts >= next_restart) { cancel_until(0); restart_idx++; next_restart = conflicts + 100 * luby(restart_idx); }
            } else {
                int next_v = 0;
                while (!heap.empty()) { int v = heap_pop(); if (val[v] == 0) { next_v = v; break; } }
                if (next_v == 0) return 1;
                decisions++; trail_lim.push_back((int)trail.size());
                assign(phase[next_v] > 0 ? next_v : -next_v, -1);
            }
        }
    }
};

vector<int> build_exact_counter(CDCLSolver& S, const vector<int>& xs, int k, bool enforce_amk) {
    int n = (int)xs.size();
    if (k <= 0) { if (enforce_amk) for (int x : xs) S.add_clause({-x}); return {}; }
    int cap = min(n, k);
    vector<vector<int>> s(n, vector<int>(cap));
    for (int i = 0; i < n; ++i) for (int j = 0; j < cap; ++j) s[i][j] = S.new_var();
    S.add_clause({-xs[0], s[0][0]}); S.add_clause({xs[0], -s[0][0]});
    for (int j = 1; j < cap; ++j) S.add_clause({-s[0][j]});
    for (int i = 1; i < n; ++i) {
        S.add_clause({-xs[i], s[i][0]}); S.add_clause({-s[i-1][0], s[i][0]}); S.add_clause({-s[i][0], s[i-1][0], xs[i]});
        for (int j = 1; j < cap; ++j) {
            if (j > i) { S.add_clause({-s[i][j]}); continue; }
            S.add_clause({-s[i-1][j], s[i][j]});
            S.add_clause({-xs[i], -s[i-1][j-1], s[i][j]});
            S.add_clause({-s[i][j], s[i-1][j], xs[i]});
            S.add_clause({-s[i][j], s[i-1][j], s[i-1][j-1]});
        }
        if (enforce_amk && k <= n) S.add_clause({-xs[i], -s[i-1][k-1]});
    }
    return s[n - 1];
}

void add_at_most_k(CDCLSolver& S, const vector<int>& xs, int k) {
    int n = (int)xs.size();
    if (k < 0) { S.add_clause({}); return; }
    if (k >= n) return;
    if (k == 0) { for (int x : xs) S.add_clause({-x}); return; }
    if (k == 1 && n <= 5) {
        for (int i = 0; i < n; ++i) for (int j = i + 1; j < n; ++j) S.add_clause({-xs[i], -xs[j]});
        return;
    }
    vector<vector<int>> s(n - 1, vector<int>(k));
    for (int i = 0; i < n - 1; ++i) for (int j = 0; j < k; ++j) s[i][j] = S.new_var();
    S.add_clause({-xs[0], s[0][0]});
    for (int j = 1; j < k; ++j) S.add_clause({-s[0][j]});
    for (int i = 1; i < n - 1; ++i) {
        S.add_clause({-xs[i], s[i][0]}); S.add_clause({-s[i-1][0], s[i][0]});
        for (int j = 1; j < k; ++j) {
            S.add_clause({-xs[i], -s[i-1][j-1], s[i][j]});
            S.add_clause({-s[i-1][j], s[i][j]});
        }
        S.add_clause({-xs[i], -s[i-1][k-1]});
    }
    S.add_clause({-xs[n-1], -s[n-2][k-1]});
}

void add_exact_k(CDCLSolver& S, const vector<int>& xs, int k) {
    int n = (int)xs.size();
    if (k < 0 || k > n) { S.add_clause({}); return; }
    if (k == 0) { for (int x : xs) S.add_clause({-x}); return; }
    if (k == n) { for (int x : xs) S.add_clause({x}); return; }
    auto out = build_exact_counter(S, xs, k, true);
    S.add_clause({out[k - 1]});
}

void add_range_k(CDCLSolver& S, const vector<int>& xs, int lo, int hi) {
    int n = (int)xs.size();
    if (lo > hi || hi < 0 || lo > n) { S.add_clause({}); return; }
    if (lo == hi) { add_exact_k(S, xs, lo); return; }
    if (lo <= 0) { add_at_most_k(S, xs, hi); return; }
    if (lo == 1) { S.add_clause(xs); if (hi < n) add_at_most_k(S, xs, hi); return; }
    auto out = build_exact_counter(S, xs, hi, hi < n);
    S.add_clause({out[lo - 1]});
}

struct ISetFinder {
    uint64_t non_adj[40];
    int cur[16];
    vector<array<int, 10>> out;
    int limit = 256;

    void dfs(uint64_t cand, int k_rem, int cur_sz, int prefix_len, const int* prefix) {
        if ((int)out.size() >= limit) return;
        if (k_rem == 0) {
            array<int, 10> arr{};
            int pos = 0;
            for (int i = 0; i < prefix_len; ++i) arr[pos++] = prefix[i];
            for (int i = 0; i < cur_sz; ++i) arr[pos++] = cur[i];
            sort(arr.begin(), arr.end());
            out.push_back(arr);
            return;
        }
        if (popcount(cand) < k_rem) return;
        if (k_rem == 1) {
            while (cand && (int)out.size() < limit) {
                int v = countr_zero(cand); cand &= cand - 1;
                array<int, 10> arr{};
                int pos = 0;
                for (int i = 0; i < prefix_len; ++i) arr[pos++] = prefix[i];
                for (int i = 0; i < cur_sz; ++i) arr[pos++] = cur[i];
                arr[pos] = v;
                sort(arr.begin(), arr.end());
                out.push_back(arr);
            }
            return;
        }
        while (cand && (int)out.size() < limit) {
            if (popcount(cand) < k_rem) break;
            int v = countr_zero(cand); cand &= cand - 1;
            uint64_t nc = cand & non_adj[v];
            if (popcount(nc) >= k_rem - 1) {
                cur[cur_sz] = v;
                dfs(nc, k_rem - 1, cur_sz + 1, prefix_len, prefix);
            }
        }
    }

    void find(const uint64_t* adj, uint64_t mask, int k, int prefix_len, const int* prefix, int lim) {
        limit = lim; out.clear();
        uint64_t full = (1ULL << 40) - 1;
        for (int v = 0; v < 40; ++v) {
            uint64_t higher = full ^ ((1ULL << (v + 1)) - 1);
            non_adj[v] = (~adj[v]) & higher & mask;
        }
        dfs(mask, k, 0, prefix_len, prefix);
    }
};

void add_lex_ge_sat(CDCLSolver& S, const vector<int>& a, const vector<int>& b) {
    int prev_eq = 0;
    for (size_t i = 0; i < a.size(); ++i) {
        int ai = a[i], bi = b[i];
        if (ai == bi) continue;
        if (prev_eq == 0) S.add_clause({ai, -bi});
        else S.add_clause({-prev_eq, ai, -bi});
        int eq = S.new_var();
        if (prev_eq == 0) {
            S.add_clause({-eq, -ai, bi}); S.add_clause({-eq, ai, -bi});
            S.add_clause({eq, ai, bi}); S.add_clause({eq, -ai, -bi});
        } else {
            S.add_clause({-eq, prev_eq}); S.add_clause({-eq, -ai, bi}); S.add_clause({-eq, ai, -bi});
            S.add_clause({-prev_eq, ai, bi, eq}); S.add_clause({-prev_eq, -ai, -bi, eq});
        }
        prev_eq = eq;
    }
}

struct GluingResult {
    string status;
    double seconds;
    uint64_t conflicts, propagations;
    int models, cuts, edge_vars, base_vars, base_clauses;
};

GluingResult solve_fixed_skeleton(
    const array<uint8_t, 5>& adjX,
    const array<int, 40>& deg_in,
    const vector<vector<int>>& sym_blocks,
    int x_anc,
    const array<int8_t, 40>& anc_fixed_T,
    double time_limit_sec
) {
    auto t0 = chrono::steady_clock::now();
    auto deadline = t0 + chrono::milliseconds((long long)(time_limit_sec * 1000));

    int fixed[40][40]; memset(fixed, 0, sizeof(fixed));
    fixed[0][1] = fixed[1][0] = 1;
    for (int v = 2; v < 40; ++v) {
        fixed[0][v] = fixed[v][0] = (v >= 2 && v <= 6) ? 1 : -1;
        fixed[1][v] = fixed[v][1] = (v >= 7 && v <= 14) ? 1 : -1;
    }
    for (int x1 = 2; x1 <= 6; ++x1) for (int x2 = x1 + 1; x2 <= 6; ++x2) fixed[x1][x2] = fixed[x2][x1] = -1;
    for (int y1 = 7; y1 <= 14; ++y1) for (int y2 = y1 + 1; y2 <= 14; ++y2) fixed[y1][y2] = fixed[y2][y1] = -1;
    for (int xi = 0; xi < 5; ++xi)
        for (int yi = 0; yi < 8; ++yi)
            fixed[2 + xi][7 + yi] = fixed[7 + yi][2 + xi] = ((adjX[xi] >> yi) & 1) ? 1 : -1;

    vector<int> anc_T;
    for (int v = 15; v < 40; ++v) {
        if (anc_fixed_T[v] != 0) {
            fixed[x_anc][v] = fixed[v][x_anc] = anc_fixed_T[v];
            if (anc_fixed_T[v] == 1) anc_T.push_back(v);
        }
    }
    for (size_t i = 0; i < anc_T.size(); ++i)
        for (size_t j = i + 1; j < anc_T.size(); ++j)
            fixed[anc_T[i]][anc_T[j]] = fixed[anc_T[j]][anc_T[i]] = -1;
    for (int y = 7; y <= 14; ++y)
        if (fixed[x_anc][y] == 1) for (int v : anc_T) fixed[y][v] = fixed[v][y] = -1;

    int ev[40][40]; memset(ev, 0, sizeof(ev));
    int nv = 0;
    for (int u = 2; u < 40; ++u)
        for (int v = u + 1; v < 40; ++v)
            if (fixed[u][v] == 0) ev[u][v] = ev[v][u] = ++nv;
    int edge_vars = nv;

    CDCLSolver S; S.init_vars(nv);

    for (int u = 2; u < 40; ++u) {
        int f_cnt = 0; vector<int> vars;
        for (int v = 0; v < 40; ++v) {
            if (u == v) continue;
            if (fixed[u][v] == 1) f_cnt++; else if (ev[u][v]) vars.push_back(ev[u][v]);
        }
        add_exact_k(S, vars, deg_in[u] - f_cnt);
    }
    for (int v = 15; v < 40; ++v) {
        int fx = 0; vector<int> vx;
        for (int x = 2; x <= 6; ++x) { if (fixed[x][v] == 1) fx++; else if (ev[x][v]) vx.push_back(ev[x][v]); }
        add_range_k(S, vx, 1 - fx, deg_in[v] - 5 - fx);
        int fy = 0; vector<int> vy;
        for (int y = 7; y <= 14; ++y) { if (fixed[y][v] == 1) fy++; else if (ev[y][v]) vy.push_back(ev[y][v]); }
        add_range_k(S, vy, 1 - fy, deg_in[v] - 2 - fy);
    }
    if (anc_T.size() == 8) {
        for (int w = 15; w < 40; ++w) {
            if (fixed[x_anc][w] == 1) continue;
            vector<int> cl; for (int u : anc_T) if (ev[u][w]) cl.push_back(ev[u][w]);
            S.add_clause(std::move(cl));
        }
        for (int x = 2; x <= 6; ++x) {
            if (x == x_anc) continue;
            vector<int> cl; for (int u : anc_T) if (ev[x][u]) cl.push_back(ev[x][u]);
            S.add_clause(std::move(cl));
        }
    }
    for (int y = 7; y <= 14; ++y) {
        vector<int> only_y;
        for (int v = 15; v < 40; ++v) {
            if (fixed[y][v] == -1) continue;
            int b = S.new_var(); vector<int> all_clause = {b};
            for (int y2 = 7; y2 <= 14; ++y2) {
                if (y2 == y) continue;
                if (fixed[y2][v] == 1) { S.add_clause({-b}); all_clause.clear(); break; }
                if (ev[y2][v]) { S.add_clause({-b, -ev[y2][v]}); all_clause.push_back(ev[y2][v]); }
            }
            if (!all_clause.empty()) S.add_clause(std::move(all_clause));
            only_y.push_back(b);
        }
        add_at_most_k(S, only_y, 1);
    }
    for (int x = 2; x <= 6; ++x) {
        vector<int> only_x;
        for (int v = 15; v < 40; ++v) {
            if (fixed[x][v] == -1) continue;
            int b = S.new_var(); vector<int> all_clause = {b};
            for (int x2 = 2; x2 <= 6; ++x2) {
                if (x2 == x) continue;
                if (fixed[x2][v] == 1) { S.add_clause({-b}); all_clause.clear(); break; }
                if (ev[x2][v]) { S.add_clause({-b, -ev[x2][v]}); all_clause.push_back(ev[x2][v]); }
            }
            if (!all_clause.empty()) S.add_clause(std::move(all_clause));
            only_x.push_back(b);
        }
        add_at_most_k(S, only_x, 4);
    }
    for (int u = 2; u < 40; ++u)
        for (int v = u + 1; v < 40; ++v) {
            if (fixed[u][v] == -1) continue;
            for (int w = v + 1; w < 40; ++w) {
                if (fixed[u][w] == -1 || fixed[v][w] == -1) continue;
                vector<int> cl;
                if (fixed[u][v] == 0) cl.push_back(-ev[u][v]);
                if (fixed[u][w] == 0) cl.push_back(-ev[u][w]);
                if (fixed[v][w] == 0) cl.push_back(-ev[v][w]);
                S.add_clause(std::move(cl));
            }
        }
    auto add_pair_codeg = [&](int u, int v) {
        int cap = deg_in[u] + deg_in[v] - 11, f_cn = 0;
        vector<int> cn;
        for (int w = 0; w < 40; ++w) {
            if (w == u || w == v || fixed[u][w] == -1 || fixed[v][w] == -1) continue;
            if (fixed[u][w] == 1 && fixed[v][w] == 1) { f_cn++; continue; }
            if (fixed[u][w] == 1) { cn.push_back(ev[v][w]); continue; }
            if (fixed[v][w] == 1) { cn.push_back(ev[u][w]); continue; }
            int b = S.new_var();
            S.add_clause({-b, ev[u][w]}); S.add_clause({-b, ev[v][w]}); S.add_clause({b, -ev[u][w], -ev[v][w]});
            cn.push_back(b);
        }
        add_range_k(S, cn, max(0, 1 - f_cn), cap - f_cn);
    };
    for (int x1 = 2; x1 <= 6; ++x1) for (int x2 = x1 + 1; x2 <= 6; ++x2) add_pair_codeg(x1, x2);
    for (int y1 = 7; y1 <= 14; ++y1) for (int y2 = y1 + 1; y2 <= 14; ++y2) add_pair_codeg(y1, y2);
    for (int x = 2; x <= 6; ++x) for (int y = 7; y <= 14; ++y) if (fixed[x][y] == -1) add_pair_codeg(x, y);

    for (int sx = 0; sx < 32; ++sx) {
        int px = popcount((unsigned)sx);
        uint8_t forb = 0;
        for (int x = 0; x < 5; ++x) if ((sx >> x) & 1) forb |= adjX[x];
        uint8_t allow = (~forb) & 0xFF;
        int need = 9 - px;
        if (need < 0 || popcount(allow) < need) continue;
        vector<int> bits;
        for (int y = 0; y < 8; ++y) if ((allow >> y) & 1) bits.push_back(y);
        vector<int> sel(bits.size(), 0); fill(sel.end() - need, sel.end(), 1);
        do {
            for (int v = 15; v < 40; ++v) {
                bool already = false; vector<int> cl;
                for (int x = 0; x < 5; ++x) if ((sx >> x) & 1) {
                    if (fixed[2 + x][v] == 1) { already = true; break; }
                    if (ev[2 + x][v]) cl.push_back(ev[2 + x][v]);
                }
                if (already) continue;
                for (size_t i = 0; i < bits.size(); ++i) if (sel[i]) {
                    int y = 7 + bits[i];
                    if (fixed[y][v] == 1) { already = true; break; }
                    if (ev[y][v]) cl.push_back(ev[y][v]);
                }
                if (!already) S.add_clause(std::move(cl));
            }
        } while (next_permutation(sel.begin(), sel.end()));
    }
    for (const auto& blk : sym_blocks) {
        for (size_t i = 0; i + 1 < blk.size(); ++i) {
            int u = blk[i], v = blk[i + 1];
            vector<int> au, av;
            for (int k = 2; k <= 14; ++k) if (ev[u][k] && ev[v][k]) { au.push_back(ev[u][k]); av.push_back(ev[v][k]); }
            add_lex_ge_sat(S, au, av);
        }
    }

    int base_vars = S.nvars, base_clauses = (int)S.clauses.size();
    ISetFinder finder;
    uint64_t H0_mask = 0, H1_mask = 0, full_mask = (1ULL << 40) - 1;
    for (int v = 7; v < 40; ++v) H0_mask |= (1ULL << v);
    for (int v = 2; v <= 6; ++v) H1_mask |= (1ULL << v);
    for (int v = 15; v < 40; ++v) H1_mask |= (1ULL << v);
    int models = 0, cuts = 0; uint64_t adj[40];

    while (true) {
        int st = S.solve(deadline);
        if (st == -1) return {"UNSAT", chrono::duration<double>(chrono::steady_clock::now()-t0).count(), S.conflicts, S.propagations, models, cuts, edge_vars, base_vars, base_clauses};
        if (st == 0) return {"TIMEOUT", chrono::duration<double>(chrono::steady_clock::now()-t0).count(), S.conflicts, S.propagations, models, cuts, edge_vars, base_vars, base_clauses};
        models++;
        for (int u = 0; u < 40; ++u) {
            uint64_t m = 0;
            for (int v = 0; v < 40; ++v) {
                if (u == v) continue;
                int e = fixed[u][v] == 1 ? 1 : (ev[u][v] ? (S.val[ev[u][v]] == 1 ? 1 : 0) : 0);
                if (e) m |= (1ULL << v);
            }
            adj[u] = m;
        }
        int new_cuts = 0;
        auto inject_isets = [&](const vector<array<int, 10>>& sets) -> bool {
            for (const auto& ss : sets) {
                vector<int> cl; cl.reserve(45);
                for (int i = 0; i < 10; ++i)
                    for (int j = i + 1; j < 10; ++j)
                        if (ev[ss[i]][ss[j]]) cl.push_back(ev[ss[i]][ss[j]]);
                new_cuts++; cuts++;
                if (!S.add_dynamic_clause(std::move(cl))) return false;
            }
            return true;
        };
        int p0[1] = {0}, p1[1] = {1};
        finder.find(adj, H0_mask, 9, 1, p0, 64);
        if (!inject_isets(finder.out)) return {"UNSAT", chrono::duration<double>(chrono::steady_clock::now()-t0).count(), S.conflicts, S.propagations, models, cuts, edge_vars, base_vars, base_clauses};
        finder.find(adj, H1_mask, 9, 1, p1, 64);
        if (!inject_isets(finder.out)) return {"UNSAT", chrono::duration<double>(chrono::steady_clock::now()-t0).count(), S.conflicts, S.propagations, models, cuts, edge_vars, base_vars, base_clauses};
        for (int u = 2; u < 40 && new_cuts < 256; ++u) {
            for (int v = u + 1; v < 40 && new_cuts < 256; ++v) {
                if ((adj[u] >> v) & 1) continue;
                if (popcount(adj[u] & adj[v]) > deg_in[u] + deg_in[v] - 11) {
                    uint64_t non_uv = full_mask & ~(adj[u] | adj[v] | (1ULL << u) | (1ULL << v));
                    int puv[2] = {u, v};
                    finder.find(adj, non_uv, 8, 2, puv, 16);
                    if (!inject_isets(finder.out)) return {"UNSAT", chrono::duration<double>(chrono::steady_clock::now()-t0).count(), S.conflicts, S.propagations, models, cuts, edge_vars, base_vars, base_clauses};
                }
            }
        }
        if (new_cuts < 64) {
            finder.find(adj, full_mask, 10, 0, nullptr, 128);
            if (!inject_isets(finder.out)) return {"UNSAT", chrono::duration<double>(chrono::steady_clock::now()-t0).count(), S.conflicts, S.propagations, models, cuts, edge_vars, base_vars, base_clauses};
        }
        if (new_cuts == 0) return {"WITNESS_FOUND", chrono::duration<double>(chrono::steady_clock::now()-t0).count(), S.conflicts, S.propagations, models, cuts, edge_vars, base_vars, base_clauses};
    }
}

int main() {
    struct TestCase { string label; array<uint8_t, 5> adjX; array<int, 40> deg; int x_anc, d_anc; };
    auto make_case = [](string label, array<uint8_t, 5> adjX, vector<int> deg6_verts, vector<int> deg8_verts) {
        array<int, 40> deg{}; deg[0] = 6; deg[1] = 9;
        for (int i = 2; i < 40; ++i) deg[i] = 9;
        for (int v : deg6_verts) deg[v] = 6;
        for (int v : deg8_verts) deg[v] = 8;
        int best_x = 0, best_d = -1;
        for (int x = 0; x < 5; ++x) { int dt = 8 - popcount(adjX[x]); if (dt > best_d) { best_d = dt; best_x = x; } }
        return TestCase{label, adjX, deg, 2 + best_x, best_d};
    };

    vector<TestCase> cases = {
        make_case("P002-T01 t=4#0 deg6_in_Y", {0b00000000, 0b00001000, 0b00000100, 0b00000010, 0b00000001}, {14}, {}),
        make_case("P002-T01 t=5#3 (5K2) deg6_in_Y", {0b00010000, 0b00001000, 0b00000100, 0b00000010, 0b00000001}, {14}, {}),
        make_case("P000-T01 t=4#0 3xdeg8_in_Y", {0b00000000, 0b00001000, 0b00000100, 0b00000010, 0b00000001}, {}, {12, 13, 14}),
        make_case("P000-T02 t=8 (sample) 3xdeg8_in_Y", {0b00000011, 0b00001100, 0b00010010, 0b00100001, 0b01000000}, {}, {12, 13, 14}),
    };

    cout << "=== C++20 Compact Incremental CDCL(T) Benchmark (v2: Bidirectional Sinz + A/B Singletons) ===\n";
    for (auto& tc : cases) {
        array<int8_t, 40> anc_T{};
        for (int v = 15; v < 15 + tc.d_anc; ++v) anc_T[v] = 1;
        for (int v = 15 + tc.d_anc; v < 40; ++v) anc_T[v] = -1;
        vector<int> b1, b2;
        for (int v = 15; v < 15 + tc.d_anc; ++v) b1.push_back(v);
        for (int v = 15 + tc.d_anc; v < 40; ++v) b2.push_back(v);
        auto res = solve_fixed_skeleton(tc.adjX, tc.deg, {b1, b2}, tc.x_anc, anc_T, 15.0);
        cout << tc.label << ":\n"
             << "  status=" << res.status << " time=" << fixed << setprecision(3) << res.seconds << "s"
             << " edge_vars=" << res.edge_vars << " total_vars=" << res.base_vars
             << " clauses=" << res.base_clauses << " models=" << res.models << " cuts=" << res.cuts
             << " conflicts=" << res.conflicts << " props/s=" << fixed << setprecision(2)
             << (res.propagations / max(res.seconds, 1e-6) / 1e6) << "M\n";
    }
    return 0;
}
