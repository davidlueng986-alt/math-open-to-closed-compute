#include <algorithm>
#include <array>
#include <string>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <unordered_set>
#include <vector>
using namespace std;
using W = uint64_t;
const W mask = (W(1) << 63) - 1;
int pop(W a) { return __builtin_popcountll(a); }
bool plane = false;
array<W, 3> carry{};
vector<int> lags;
int plus63(int i, int j) { return (i + j + 63 - (plane && i % 3 + j % 3 >= 3 ? 21 : 0)) % 63; }
int minus63(int i) { return (63 - i + (plane && i % 3 != 0 ? 21 : 0)) % 63; }
W cyclicRotate(W a, int k) { return k ? (a >> k) | ((a << (63 - k)) & mask) : a; }
W rot(W a, int k) {
    W v = cyclicRotate(a, k);
    if (!plane || k % 3 == 0)
        return v;
    W c = carry[k % 3];
    return (v & ~c) | (cyclicRotate(a, (k + 42) % 63) & c);
}
vector<array<int, 63>> automorphisms() {
    vector<array<int, 63>> perms;
    if (!plane) {
        for (int u = 1; u < 63; u++)
            if (gcd(u, 63) == 1) {
                array<int, 63> v{};
                for (int i = 0; i < 63; i++)
                    v[i] = u * i % 63;
                perms.push_back(v);
            }
    } else {
        int index[3][3][7]{};
        for (int i = 0; i < 63; i++)
            index[i % 9 / 3][i % 3][i % 7] = i;
        for (int a = 0; a < 3; a++)
            for (int b = 0; b < 3; b++)
                for (int c = 0; c < 3; c++)
                    for (int d = 0; d < 3; d++)
                        if ((a * d - b * c) % 3)
                            for (int u = 1; u < 7; u++) {
                                array<int, 63> v{};
                                for (int i = 0; i < 63; i++) {
                                    int x = i % 9 / 3, y = i % 3;
                                    v[i] =
                                        index[(a * x + b * y) % 3][(c * x + d * y) % 3][u * i % 7];
                                }
                                perms.push_back(v);
                            }
    }
    return perms;
}
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
    for (int t = 0; t < 31; t++)
        if (pop(a & rot(a, lags[t])) % 2)
            ans |= W(1) << t;
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
            for (int t = 0; t < 31; t++) {
                W intersection = supp & rot(supp, lags[t]);
                s.paf[t] = pop(intersection) - 2 * pop(intersection & (neg ^ rot(neg, lags[t])));
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
int main(int argc, char **argv) {
    if (argc > 2 || (argc == 2 && string(argv[1]) != "plane"))
        return 2;
    plane = argc == 2;
    for (int h = 0; h < 3; h++)
        for (int i = 0; i < 63; i++)
            if (i % 3 + h >= 3)
                carry[h] |= W(1) << i;
    for (int i = 1; i < 63; i++)
        if (i < minus63(i))
            lags.push_back(i);
    auto permutations = automorphisms();
    if (lags.size() != 31 || permutations.size() != (plane ? 288 : 36))
        return 3;
    for (int i = 0; i < 63; i++)
        for (int k = 0; k < 63; k++)
            if (rot(W(1) << plus63(i, k), k) != (W(1) << i))
                return 4;
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
                    for (const auto &perm : permutations) {
                        W v = 0;
                        for (int j : bits)
                            v |= W(1) << perm[j];
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
