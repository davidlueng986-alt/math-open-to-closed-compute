// Fast bitset independent-set separator for N=40 graphs.
// Finds up to `limit` independent sets of size `k` within a vertex subset `mask`.
#include <cstdint>
#include <algorithm>

struct State {
    uint64_t adj[40];
    int* out;
    int k;
    int limit;
    int count;
    int cur[12];
};

static void dfs(State& st, uint64_t cand, int rem, int depth) {
    if (st.count >= st.limit) return;
    if (rem == 0) {
        int* dst = st.out + st.count * st.k;
        for (int i = 0; i < st.k; ++i) dst[i] = st.cur[i];
        st.count++;
        return;
    }
    while (__builtin_popcountll(cand) >= rem && st.count < st.limit) {
        int v = __builtin_ctzll(cand);
        cand &= cand - 1;
        st.cur[depth] = v;
        dfs(st, cand & ~st.adj[v], rem - 1, depth + 1);
    }
}

extern "C" int find_indep_sets(const uint64_t* adj_in, uint64_t mask, int k, int limit, int* out_buf) {
    State st;
    for (int i = 0; i < 40; ++i) st.adj[i] = adj_in[i];
    st.out = out_buf;
    st.k = k;
    st.limit = limit;
    st.count = 0;
    dfs(st, mask, k, 0);
    return st.count;
}
