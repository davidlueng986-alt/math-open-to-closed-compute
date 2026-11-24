// Exact paired singleton exchange and bounded-distance meet-in-the-middle on the 63-point quotient.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <random>
#include <stdexcept>
#include <string>
#include <vector>
using namespace std;
using Word = array<int, 63>;
using Pair = array<Word, 2>;
using Vec = array<int, 32>;
using Hash = uint64_t;
int distance63(int a, int b) {
    int d = abs(a - b);
    return min(d, 63 - d);
}
int singleton(int x) { return abs(x) > 1 ? x - (x > 0 ? 18 : -18) : x; }
Vec residual(const Pair &rows) {
    Vec e{};
    for (int t = 0; t < 32; t++) {
        e[t] = 38 - (t == 0 ? 2396 : 0);
        for (auto &v : rows)
            for (int i = 0; i < 63; i++)
                e[t] += v[i] * v[(i + t) % 63];
    }
    return e;
}
int score(const Vec &v) {
    int s = 0;
    for (int t = 0; t < 32; t++)
        s += (t ? 2 : 1) * v[t] * v[t];
    return s;
}
void flip(Word &v, Hash h) {
    while (h) {
        int i = __builtin_ctzll(h);
        v[i] -= 2 * singleton(v[i]);
        h &= h - 1;
    }
}
Vec single(const Word &v, int i) {
    Vec e{};
    int z = -2 * singleton(v[i]);
    for (int t = 0; t < 32; t++)
        e[t] = z * (v[(i + t) % 63] + v[(i + 63 - t) % 63]);
    e[0] += 4;
    return e;
}
struct Exchange {
    Hash bits = 0;
    Vec delta{};
    int cost = 0;
};
vector<Exchange> trades(const Word &v, const Vec &e) {
    vector<Exchange> out(1);
    array<Vec, 63> changes{};
    for (int i = 0; i < 63; i++)
        changes[i] = single(v, i);
    for (int i = 0; i < 63; i++)
        if (singleton(v[i]) > 0)
            for (int j = 0; j < 63; j++)
                if (singleton(v[j]) < 0) {
                    Exchange x;
                    x.bits = (Hash(1) << i) | (Hash(1) << j);
                    for (int t = 0; t < 32; t++)
                        x.delta[t] = changes[i][t] + changes[j][t];
                    x.delta[distance63(i, j)] -= 4;
                    for (int t = 0; t < 32; t++)
                        x.cost += (t ? 2 : 1) * (2 * e[t] + x.delta[t]) * x.delta[t];
                    out.push_back(x);
                }
    return out;
}
bool descent(Pair &v) {
    auto e = residual(v);
    auto A = trades(v[0], e), B = trades(v[1], e);
    for (auto &x : A)
        for (int t = 0; t < 32; t++)
            x.delta[t] *= (t ? 4 : 2);
    int gain = 0;
    Hash a = 0, b = 0;
    for (auto &x : A)
        for (auto &y : B) {
            int val = x.cost + y.cost;
            for (int t = 0; t < 32; t++)
                val += x.delta[t] * y.delta[t];
            if (val < gain) {
                gain = val;
                a = x.bits;
                b = y.bits;
            }
        }
    if (!gain)
        return false;
    flip(v[0], a);
    flip(v[1], b);
    if (score(residual(v)) != score(e) + gain)
        throw runtime_error("bad paired descent");
    return true;
}
struct Pick {
    Hash bits = 0, h = 0;
    array<int, 3> pos{};
};
struct WordHashes {
    array<Hash, 63> main{};
    array<array<Hash, 63>, 63> cross{};
    array<vector<Pick>, 4> positive, negative;
    WordHashes(const Word &v, const array<Hash, 32> &coeff, int radius) {
        for (int i = 0; i < 63; i++) {
            auto s = single(v, i);
            for (int t = 0; t < 32; t++)
                main[i] += coeff[t] * s[t];
            for (int j = 0; j < 63; j++)
                cross[i][j] = coeff[distance63(i, j)] * (4 * singleton(v[i]) * singleton(v[j]));
        }
        for (int sign : {1, -1}) {
            auto &out = (sign > 0 ? positive : negative);
            out[0].push_back(Pick{});
            for (int k = 1; k <= radius; k++)
                for (const auto &p : out[k - 1])
                    for (int i = (k > 1 ? p.pos[k - 2] + 1 : 0); i < 63; i++)
                        if (singleton(v[i]) == sign) {
                            Pick a = p;
                            a.pos[k - 1] = i;
                            a.bits |= Hash(1) << i;
                            a.h += main[i];
                            for (int j = 0; j < k - 1; j++)
                                a.h += cross[a.pos[j]][i];
                            out[k].push_back(a);
                        }
        }
    }
    uint64_t count(int radius) const {
        uint64_t n = 0;
        for (int k = 0; k <= radius; k++)
            n += positive[k].size() * negative[k].size();
        return n;
    }
    template <class Fn> void each(int radius, Fn run) const {
        for (int k = 0; k <= radius; k++)
            for (const Pick &a : positive[k]) {
                array<Hash, 63> interact{};
                for (int i = 0; i < 63; i++)
                    for (int j = 0; j < k; j++)
                        interact[i] += cross[a.pos[j]][i];
                for (const Pick &b : negative[k]) {
                    Hash h = a.h + b.h;
                    for (int i = 0; i < k; i++)
                        h += interact[b.pos[i]];
                    run(h, a.bits | b.bits);
                }
            }
    }
};
void meet(const Pair &v, int radius, bool control) {
    Vec wanted{};
    if (control) {
        Pair planted = v;
        for (auto &w : planted) {
            int pos = 0, neg = 0;
            for (int i = 0; i < 63; i++) {
                int sign = singleton(w[i]);
                if ((sign == 1 && pos < radius) || (sign == -1 && neg < radius)) {
                    (sign == 1 ? pos : neg)++;
                    w[i] -= 2 * sign;
                }
            }
        }
        wanted = residual(planted);
    }
    mt19937_64 rng(193);
    array<Hash, 32> coeff{};
    for (auto &x : coeff)
        x = rng();
    WordHashes a(v[0], coeff, radius), b(v[1], coeff, radius);
    Hash target = 0;
    auto e = residual(v);
    for (int t = 0; t < 32; t++)
        target += coeff[t] * (wanted[t] - e[t]);
    bool reverse = a.count(radius) > b.count(radius);
    auto &sm = reverse ? b : a, &lg = reverse ? a : b;
    vector<pair<Hash, Hash>> stored;
    stored.reserve(sm.count(radius));
    sm.each(radius, [&](Hash h, Hash bits) { stored.emplace_back(h, bits); });
    sort(stored.begin(), stored.end());
    uint64_t hits = 0, exact = 0;
    lg.each(radius, [&](Hash h, Hash bits) {
        auto it = lower_bound(stored.begin(), stored.end(), make_pair(target - h, Hash(0)));
        while (it != stored.end() && it->first == target - h) {
            hits++;
            Pair w = v;
            flip(w[reverse ? 1 : 0], it->second);
            flip(w[reverse ? 0 : 1], bits);
            if (residual(w) == wanted) {
                exact++;
                if (exact == 1 && !control) {
                    cerr << "exact flips " << it->second << " " << bits << " swapped=" << reverse
                         << "\n";
                    for (auto &r : w) {
                        for (int x : r)
                            cerr << x << " ";
                        cerr << "\n";
                    }
                }
            }
            ++it;
        }
    });
    cout << "{\"radius\":" << radius << ",\"row_counts\":[" << a.count(radius) << ","
         << b.count(radius) << "],\"candidates\":" << a.count(radius) * b.count(radius)
         << ",\"hash_matches\":" << hits << ",\"exact\":" << exact << "}\n";
}
int main(int argc, char **argv) {
    if (argc < 3)
        return 2;
    Pair v{};
    for (auto &r : v)
        for (int &x : r)
            if (!(cin >> x) || abs(singleton(x)) != 1)
                return 2;
    if (string(argv[1]) == "meet") {
        int radius = stoi(argv[2]);
        if (radius < 0 || radius > 3)
            return 2;
        meet(v, radius, argc == 4 && string(argv[3]) == "control");
        return 0;
    }
    if (argc != 5 || string(argv[1]) != "descent")
        return 2;
    mt19937 rng(stoul(argv[2]));
    int rounds = stoi(argv[3]), depth = stoi(argv[4]);
    while (descent(v)) {
    }
    Pair best = v;
    int low = score(residual(v));
    for (int j = 0; j < rounds; j++) {
        v = best;
        for (int k = 0; k < depth; k++) {
            auto &r = v[rng() % 2];
            int i = rng() % 63, u;
            do {
                u = rng() % 63;
            } while (singleton(r[u]) == singleton(r[i]));
            flip(r, (Hash(1) << i) | (Hash(1) << u));
        }
        while (descent(v)) {
        }
        int val = score(residual(v));
        if (val < low) {
            low = val;
            best = v;
        }
    }
    cout << "{\"quotient_energy_all_shifts\":" << low << ",\"projections\":[";
    for (int r = 0; r < 2; r++) {
        cout << (r ? ",[" : "[");
        for (int i = 0; i < 63; i++)
            cout << (i ? "," : "") << best[r][i];
        cout << "]";
    }
    cout << "]}\n";
}
