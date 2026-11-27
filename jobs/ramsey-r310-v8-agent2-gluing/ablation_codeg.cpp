#include <bits/stdc++.h>
using namespace std;

#define main gluing_v2_main
#include "gluing_cdcl_v2.cpp"
#undef main

GluingResult solve_with_full_codeg(
    const array<uint8_t, 5>& adjX,
    const array<int, 40>& deg_in,
    const vector<vector<int>>& sym_blocks,
    int x_anc,
    const array<int8_t, 40>& anc_fixed_T,
    double time_limit_sec,
    bool add_xt_yt_codeg,
    bool add_tt_codeg
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
    auto add_pair = [&](int u, int v) {
        if (fixed[u][v] == 1) return;
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
        if (f_cn == 0) {
            vector<int> sat_cl = cn;
            if (ev[u][v]) sat_cl.push_back(ev[u][v]);
            S.add_clause(std::move(sat_cl));
        }
        if (cap - f_cn < (int)cn.size()) add_at_most_k(S, cn, cap - f_cn);
    };
    for (int x1 = 2; x1 <= 6; ++x1) for (int x2 = x1 + 1; x2 <= 6; ++x2) add_pair(x1, x2);
    for (int y1 = 7; y1 <= 14; ++y1) for (int y2 = y1 + 1; y2 <= 14; ++y2) add_pair(y1, y2);
    for (int x = 2; x <= 6; ++x) for (int y = 7; y <= 14; ++y) add_pair(x, y);
    if (add_xt_yt_codeg) {
        for (int x = 2; x <= 6; ++x) for (int v = 15; v < 40; ++v) add_pair(x, v);
        for (int y = 7; y <= 14; ++y) for (int v = 15; v < 40; ++v) add_pair(y, v);
    }
    if (add_tt_codeg) {
        for (int u = 15; u < 40; ++u) for (int v = u + 1; v < 40; ++v) add_pair(u, v);
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
    int st = S.solve(deadline);
    double sec = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
    return {st == -1 ? "UNSAT" : (st == 1 ? "SAT_MODEL" : "TIMEOUT"), sec, S.conflicts, S.propagations, st == 1 ? 1 : 0, 0, edge_vars, base_vars, base_clauses};
}

int main() {
    array<uint8_t, 5> adjX = {0b00000000, 0b00001000, 0b00000100, 0b00000010, 0b00000001};
    array<int, 40> deg{}; deg[0] = 6; deg[1] = 9;
    for (int i = 2; i < 40; ++i) deg[i] = 9;
    deg[14] = 6;
    array<int8_t, 40> anc_T{};
    for (int v = 15; v < 23; ++v) anc_T[v] = 1;
    for (int v = 23; v < 40; ++v) anc_T[v] = -1;
    vector<vector<int>> sym = {{15,16,17,18,19,20,21,22}, {23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39}};

    for (auto [name, xt_yt, tt] : vector<tuple<string,bool,bool>>{
        {"XY-codeg only", false, false},
        {"XY + XT/YT codeg", true, false},
        {"FULL codeg (v7-equiv on fixed skeleton)", true, true}
    }) {
        auto r = solve_with_full_codeg(adjX, deg, sym, 2, anc_T, 15.0, xt_yt, tt);
        cout << name << ": status=" << r.status << " time=" << fixed << setprecision(3) << r.seconds
             << "s vars=" << r.base_vars << " clauses=" << r.base_clauses
             << " conflicts=" << r.conflicts << " props=" << r.propagations << "\n";
    }
    return 0;
}
