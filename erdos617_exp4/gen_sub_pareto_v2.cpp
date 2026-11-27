#include <bits/stdc++.h>
using namespace std;

int e_min(int n, int r=6) {
    int q = n / r, rem = n % r;
    return rem * (q + 1) * q / 2 + (r - rem) * q * (q - 1) / 2;
}

int greedy_min_edges(const int r_map[6], const int U[6][6], const int* nodes, int sz) {
    pair<int, int> pairs[10];
    int np = 0;
    for (int a = 0; a < sz; a++)
        for (int b = a + 1; b < sz; b++) {
            int j = nodes[a], k = nodes[b];
            pairs[np++] = {r_map[j] * r_map[k], U[j][k]};
        }
    sort(pairs, pairs + np);
    double rem = 1.0 - 1e-12;
    int used = 0;
    for (int p = 0; p < np; p++) {
        int prod = pairs[p].first, cap = pairs[p].second;
        if (cap <= 0) continue;
        double mc = (double)cap / prod;
        if (mc >= rem) {
            used += (int)ceil(rem * prod - 1e-12);
            rem = 0.0;
            break;
        } else {
            used += cap;
            rem -= mc;
        }
    }
    return (rem > 1e-9) ? 9999 : used;
}

int main() {
    int prof[6], m[6], part_i;
    for (int i = 0; i < 6; i++) cin >> prof[i];
    for (int i = 0; i < 6; i++) cin >> m[i];
    cin >> part_i;

    int S = 0, base[6], m_in = 0;
    for (int i = 0; i < 6; i++) {
        S += prof[i]*(prof[i]-1)/2;
        base[i] = 5 * e_min(prof[i], 6);
        m_in += m[i];
    }
    int max_m_out = 111 - S + m_in;

    int U[6][6], M[6][6];
    for (int i = 0; i < 6; i++) {
        for (int j = 0; j < 6; j++) {
            if (i == j) { U[i][j] = M[i][j] = 0; continue; }
            int ub = prof[i]*prof[j] - 5*e_min(prof[i]+prof[j], 6) + m[i] + m[j];
            if (prof[i] >= 6) ub = min(ub, prof[j]*(prof[i]-5) + (m[i]-base[i]) + m[j]);
            if (prof[j] >= 6) ub = min(ub, prof[i]*(prof[j]-5) + (m[j]-base[j]) + m[i]);
            if (prof[i] == 5 && m[i] == 0) {
                int ec = 0; while (e_min(ec + 1, 5) <= m[j]) ec++;
                ub = min(ub, ec);
            }
            if (prof[j] == 5 && m[j] == 0) {
                int ec = 0; while (e_min(ec + 1, 5) <= m[i]) ec++;
                ub = min(ub, ec);
            }
            ub = max(0, min(ub, max_m_out));
            U[i][j] = ub;
            int mk = prof[j];
            if (prof[j] >= 6) mk = min(mk, (prof[j] - 5) + (m[j] - base[j]));
            mk = min(mk, ub);
            M[i][j] = mk;
        }
    }

    int others[5], oi = 0, cmax[5];
    for (int j = 0; j < 6; j++) {
        if (j != part_i) {
            others[oi] = j;
            int cm = min(prof[j] - 1, min(2 * M[part_i][j], U[part_i][j]));
            // PROVED Multi-Color Clique-Collision Theorem:
            if (prof[j] >= 6) cm = min(cm, 2*(prof[j]-5) + (m[j]-base[j]) + 1);
            cmax[oi] = cm;
            oi++;
        }
    }

    vector<int> masks;
    for (int mask = 0; mask < 32; mask++) {
        if (__builtin_popcount(mask) >= 2) masks.push_back(mask);
    }

    int d0 = cmax[0]+1, d1 = cmax[1]+1, d2 = cmax[2]+1, d3 = cmax[3]+1, d4 = cmax[4]+1;
    int tot = d0*d1*d2*d3*d4;
    static const int perms6[6][3] = {{0,1,2},{0,2,1},{1,0,2},{1,2,0},{2,0,1},{2,1,0}};

    for (int mask : masks) {
        int t_nodes[5], tsz = 0;
        int c_nodes[5], csz = 0;
        for (int k = 0; k < 5; k++) {
            if (mask & (1 << k)) t_nodes[tsz++] = others[k];
            else c_nodes[csz++] = others[k];
        }
        int max_sum_t = 0;
        for (int a = 0; a < tsz; a++)
            for (int b = a+1; b < tsz; b++)
                max_sum_t += U[t_nodes[a]][t_nodes[b]];
        max_sum_t = min(max_sum_t, max_m_out);

        vector<int> req(tot, 0);
        int r_map[6];
        bool any_nonzero = false;
        for (int c0 = 0; c0 <= cmax[0]; c0++) {
            r_map[others[0]] = prof[others[0]] - c0;
            for (int c1 = 0; c1 <= cmax[1]; c1++) {
                r_map[others[1]] = prof[others[1]] - c1;
                for (int c2 = 0; c2 <= cmax[2]; c2++) {
                    r_map[others[2]] = prof[others[2]] - c2;
                    for (int c3 = 0; c3 <= cmax[3]; c3++) {
                        r_map[others[3]] = prof[others[3]] - c3;
                        for (int c4 = 0; c4 <= cmax[4]; c4++) {
                            r_map[others[4]] = prof[others[4]] - c4;
                            int best = 0;
                            if (csz == 0) {
                                best = greedy_min_edges(r_map, U, t_nodes, tsz);
                            } else if (csz == 1) {
                                int x = c_nodes[0];
                                int r1[6]; bool ok = true;
                                for (int a = 0; a < tsz; a++) {
                                    int y = t_nodes[a];
                                    r1[y] = r_map[y] - M[x][y];
                                    if (r1[y] <= 0) { ok = false; break; }
                                }
                                if (ok) best = greedy_min_edges(r1, U, t_nodes, tsz);
                            } else if (csz == 2) {
                                for (int sw = 0; sw < 2; sw++) {
                                    int x = c_nodes[sw], y = c_nodes[1-sw];
                                    if (r_map[y] <= M[x][y]) continue;
                                    int r2[6]; bool ok = true;
                                    for (int a = 0; a < tsz; a++) {
                                        int z = t_nodes[a];
                                        r2[z] = r_map[z] - M[x][z] - M[y][z];
                                        if (r2[z] <= 0) { ok = false; break; }
                                    }
                                    if (ok) best = max(best, greedy_min_edges(r2, U, t_nodes, tsz));
                                }
                            } else if (csz == 3) {
                                int p = t_nodes[0], q = t_nodes[1];
                                for (int pi = 0; pi < 6; pi++) {
                                    int x = c_nodes[perms6[pi][0]], y = c_nodes[perms6[pi][1]], z = c_nodes[perms6[pi][2]];
                                    if (r_map[y] > M[x][y] && r_map[z] > M[x][z] + M[y][z]) {
                                        int rp = r_map[p] - M[x][p] - M[y][p] - M[z][p];
                                        int rq = r_map[q] - M[x][q] - M[y][q] - M[z][q];
                                        if (rp >= 1 && rq >= 1) best = max(best, rp * rq);
                                    }
                                }
                            }
                            if (best > max_sum_t) best = max_sum_t + 1;
                            if (best > 0) any_nonzero = true;
                            int idx = (((c0*d1 + c1)*d2 + c2)*d3 + c3)*d4 + c4;
                            req[idx] = best;
                        }
                    }
                }
            }
        }
        if (!any_nonzero) continue;

        map<array<int,5>, int> best_T;
        for (int T = 1; T <= max_sum_t + 1; T++) {
            for (int c0 = 0; c0 <= cmax[0]; c0++)
            for (int c1 = 0; c1 <= cmax[1]; c1++)
            for (int c2 = 0; c2 <= cmax[2]; c2++)
            for (int c3 = 0; c3 <= cmax[3]; c3++)
            for (int c4 = 0; c4 <= cmax[4]; c4++) {
                int idx = (((c0*d1 + c1)*d2 + c2)*d3 + c3)*d4 + c4;
                if (req[idx] < T) continue;
                bool is_max = true;
                if (c0 < cmax[0] && req[idx + d1*d2*d3*d4] >= T) is_max = false;
                else if (c1 < cmax[1] && req[idx + d2*d3*d4] >= T) is_max = false;
                else if (c2 < cmax[2] && req[idx + d3*d4] >= T) is_max = false;
                else if (c3 < cmax[3] && req[idx + d4] >= T) is_max = false;
                else if (c4 < cmax[4] && req[idx + 1] >= T) is_max = false;
                if (is_max) best_T[{c0, c1, c2, c3, c4}] = T;
            }
        }
        for (auto& kv : best_T) {
            cout << mask << " " << kv.first[0] << " " << kv.first[1] << " " << kv.first[2] << " "
                 << kv.first[3] << " " << kv.first[4] << " " << kv.second << "\n";
        }
    }
    return 0;
}
