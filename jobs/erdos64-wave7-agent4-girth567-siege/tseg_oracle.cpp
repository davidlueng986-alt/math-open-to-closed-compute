#include <vector>
#include <algorithm>
#include <cstring>

extern "C" {

static const int PAIR_TABLE[4][4] = {
    {-1, 0, 1, 2},
    { 0,-1, 2, 1},
    { 1, 2,-1, 0},
    { 2, 1, 0,-1}
};

int find_pow2_cycles(
    int n, const int* deg, const int* adj_flat, const int* p,
    int max_len, int max_out, int* out_len, int* out_verts
) {
    int nbr_pos[64][64];
    memset(nbr_pos, -1, sizeof(nbr_pos));
    for (int v = 0; v < n; ++v)
        for (int i = 0; i < deg[v]; ++i)
            nbr_pos[v][adj_flat[v*4 + i]] = i;

    int sw[64][4][4];
    memset(sw, 0, sizeof(sw));
    for (int v = 0; v < n; ++v) {
        if (deg[v] == 4) {
            for (int i = 0; i < 4; ++i)
                for (int j = 0; j < 4; ++j)
                    sw[v][i][j] = (i == j) ? 0 : (PAIR_TABLE[i][j] == p[v] ? 0 : 1);
        } else if (deg[v] == 2) {
            sw[v][0][1] = sw[v][1][0] = p[v];
        }
    }

    bool vis[64] = {false};
    int path[64];
    int found = 0;
    auto is_pow2 = [](int x) { return x >= 4 && (x & (x - 1)) == 0; };

    auto dfs = [&](auto& self, int s, int u, int prev_idx, int len, int cur_sw, int first_idx) -> void {
        if (found >= max_out) return;
        for (int iw = 0; iw < deg[u]; ++iw) {
            int w = adj_flat[u*4 + iw];
            if (w == s && len >= 3) {
                if (path[1] < u) {
                    int L = len + cur_sw + sw[u][prev_idx][iw] + sw[s][nbr_pos[s][u]][first_idx];
                    if (is_pow2(L)) {
                        out_len[found] = len;
                        for (int i = 0; i < len; ++i) out_verts[found*64 + i] = path[i];
                        ++found;
                        if (found >= max_out) return;
                    }
                }
            } else if (w > s && !vis[w] && len < max_len) {
                vis[w] = true; path[len] = w;
                self(self, s, w, nbr_pos[w][u], len + 1, cur_sw + sw[u][prev_idx][iw], first_idx);
                vis[w] = false;
                if (found >= max_out) return;
            }
        }
    };

    for (int s = 0; s < n && found < max_out; ++s) {
        vis[s] = true; path[0] = s;
        for (int i1 = 0; i1 < deg[s] && found < max_out; ++i1) {
            int v1 = adj_flat[s*4 + i1];
            if (v1 > s) {
                vis[v1] = true; path[1] = v1;
                dfs(dfs, s, v1, nbr_pos[v1][s], 2, 0, i1);
                vis[v1] = false;
            }
        }
        vis[s] = false;
    }
    return found;
}

}
