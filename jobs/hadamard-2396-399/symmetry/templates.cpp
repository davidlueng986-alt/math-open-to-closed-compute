#include <algorithm>
#include <array>
#include <bitset>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <unordered_set>
#include <vector>
using namespace std;
using W = uint64_t;
const W mask = (W(1) << 63) - 1;
int pop(W a) { return __builtin_popcountll(a); }
W rot(W a, int k) { return k ? (a >> k) | ((a << (63 - k)) & mask) : a; }
vector<int> pos(W a) {
    vector<int> v;
    while (a) {
        v.push_back(__builtin_ctzll(a));
        a &= a - 1;
    }
    return v;
}
W necklace(W a) {
    if (!a)
        return 0;
    W low = a;
    for (W v = a; v; v &= v - 1)
        low = min(low, rot(a, __builtin_ctzll(v)));
    return low;
}
W parity(W a) {
    W ans = 0;
    for (int t = 1; t <= 31; t++)
        if (pop(a & rot(a, t)) % 2)
            ans |= W(1) << (t - 1);
    return ans;
}
struct Signed {
    W neg;
    int sum;
    array<int, 31> paf;
};
vector<Signed> signings(W supp) {
    vector<Signed> v;
    for (W neg = supp;; neg = (neg - 1) & supp) {
        if (!supp || !(neg & (supp & -supp))) {
            Signed s;
            s.neg = neg;
            s.sum = pop(supp) - 2 * pop(neg);
            for (int t = 1; t <= 31; t++) {
                W intersection = supp & rot(supp, t);
                s.paf[t - 1] = pop(intersection) - 2 * pop(intersection & (neg ^ rot(neg, t)));
            }
            v.push_back(s);
        }
        if (neg == 0)
            break;
    }
    return v;
}
struct Small {
    W support, p;
    vector<Signed> opts;
};
int main() {
    vector<int> units;
    for (int u = 1; u < 63; u++)
        if (gcd(u, 63) == 1)
            units.push_back(u);
    array<vector<Small>, 4> shortRows;
    vector<W> all{0};
    for (int k = 0; k <= 3; k++) {
        for (W s : all)
            shortRows[k].push_back({s, parity(s), signings(s)});
        unordered_set<W> next;
        for (W s : all)
            for (int i = 0; i < 63; i++)
                if (!(s >> i & 1))
                    next.insert(necklace(s | (W(1) << i)));
        all.assign(next.begin(), next.end());
        sort(all.begin(), all.end());
    }
    vector<W> reps{0};
    for (int k = 1; k <= 7; k++) {
        vector<W> next;
        unordered_set<W> seen;
        for (W s : reps)
            for (int i = 0; i < 63; i++)
                if (!(s >> i & 1)) {
                    W u = necklace(s | (W(1) << i));
                    if (seen.count(u))
                        continue;
                    auto bits = pos(u);
                    for (int a : units) {
                        W v = 0;
                        for (int j : bits)
                            v |= W(1) << (a * j % 63);
                        seen.insert(necklace(v));
                    }
                    next.push_back(u);
                }
        reps = move(next);
        sort(reps.begin(), reps.end());
        if (k < 4)
            continue;
        uint64_t paired = 0, pass = 0;
        for (W a : reps) {
            W p = parity(a);
            vector<Signed> sa;
            for (const auto &b : shortRows[7 - k]) {
                int h = pop(p ^ b.p);
                if (h != 1 && h != 3)
                    continue;
                paired++;
                if (sa.empty())
                    sa = signings(a);
                for (const auto &x : sa)
                    for (const auto &y : b.opts) {
                        if (x.sum * x.sum + y.sum * y.sum != 7 - 2 * h)
                            continue;
                        bool valid = true;
                        for (int t = 0; t < 31; t++) {
                            int d = x.paf[t] + y.paf[t];
                            if (d != 0 && d != -1) {
                                valid = false;
                                break;
                            }
                        }
                        if (valid) {
                            cout << k << " " << a << " " << x.neg << " " << b.support << " "
                                 << y.neg << " " << h << "\n";
                            pass++;
                        }
                    }
            }
        }
        cerr << k << " reps=" << reps.size() << " paired=" << paired << " signed=" << pass << "\n";
    }
}
