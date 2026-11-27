#include <cstdint>
#include <vector>
#include <algorithm>
#include <random>
#include <set>
#include <array>

static inline int popcnt64(uint64_t x) {
    return __builtin_popcountll(x);
}
static inline int ctz64(uint64_t x) {
    return __builtin_ctzll(x);
}

static void dfs_det(const uint64_t* non_nbr, uint64_t cand, int* chosen, int depth, int need,
                    std::vector<std::array<int, 7>>& out, int max_out) {
    if ((int)out.size() >= max_out) return;
    if (need == 0) {
        std::array<int, 7> a;
        for (int i = 0; i < 7; ++i) a[i] = chosen[i];
        out.push_back(a);
        return;
    }
    if (popcnt64(cand) < need) return;
    uint64_t c = cand;
    while (c) {
        int v = ctz64(c);
        c &= (c - 1);
        if (popcnt64(c) + 1 < need) break;
        chosen[depth] = v;
        dfs_det(non_nbr, c & non_nbr[v], chosen, depth + 1, need - 1, out, max_out);
        if ((int)out.size() >= max_out) return;
    }
}

static void dfs_rand(const uint64_t* non_nbr, const int* verts, uint64_t cand, int* chosen,
                     int depth, int need, std::vector<std::array<int, 7>>& out, int max_out,
                     int& nodes, int max_nodes) {
    if ((int)out.size() >= max_out || nodes >= max_nodes) return;
    ++nodes;
    if (need == 0) {
        std::array<int, 7> a;
        for (int i = 0; i < 7; ++i) a[i] = verts[chosen[i]];
        std::sort(a.begin(), a.end());
        out.push_back(a);
        return;
    }
    if (popcnt64(cand) < need) return;
    uint64_t c = cand;
    while (c) {
        int idx = ctz64(c);
        c &= (c - 1);
        if (popcnt64(c) + 1 < need) break;
        chosen[depth] = idx;
        dfs_rand(non_nbr, verts, c & non_nbr[idx], chosen, depth + 1, need - 1, out, max_out, nodes, max_nodes);
        if ((int)out.size() >= max_out || nodes >= max_nodes) return;
    }
}

extern "C" int find_is7(const uint64_t* adj, int n, int max_det, int num_trials, int per_trial,
                        uint32_t seed, int* out_buf, int max_total) {
    uint64_t full = (n == 64) ? ~0ULL : ((1ULL << n) - 1ULL);
    uint64_t non_nbr[64];
    for (int v = 0; v < n; ++v) {
        uint64_t higher = full ^ ((1ULL << (v + 1)) - 1ULL);
        non_nbr[v] = higher & ~adj[v];
    }
    std::vector<std::array<int, 7>> det_out;
    int chosen[7];
    dfs_det(non_nbr, full, chosen, 0, 7, det_out, max_det);
    if (det_out.empty()) {
        return 0; // Exact certification: alpha(G_1) <= 6!
    }

    std::set<std::array<int, 7>> unique_sets(det_out.begin(), det_out.end());
    std::mt19937 rng(seed);
    std::vector<int> verts(n);
    for (int i = 0; i < n; ++i) verts[i] = i;

    for (int t = 0; t < num_trials && (int)unique_sets.size() < max_total; ++t) {
        std::shuffle(verts.begin(), verts.end(), rng);
        uint64_t s_non[64];
        for (int i = 0; i < n; ++i) {
            int u = verts[i];
            uint64_t mask = 0;
            for (int j = i + 1; j < n; ++j) {
                int v = verts[j];
                if (!((adj[u] >> v) & 1ULL)) mask |= (1ULL << j);
            }
            s_non[i] = mask;
        }
        std::vector<std::array<int, 7>> rand_out;
        int nodes = 0;
        dfs_rand(s_non, verts.data(), full, chosen, 0, 7, rand_out, per_trial, nodes, 5000);
        for (const auto& s : rand_out) {
            unique_sets.insert(s);
            if ((int)unique_sets.size() >= max_total) break;
        }
    }

    int count = 0;
    for (const auto& s : unique_sets) {
        if (count >= max_total) break;
        for (int i = 0; i < 7; ++i) out_buf[count * 7 + i] = s[i];
        ++count;
    }
    return count;
}
