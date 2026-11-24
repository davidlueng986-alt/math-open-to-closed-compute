// Exact meet-in-the-middle for two equal-size multiplier-orbit exchanges per word.
// A candidate preserving all previously exact lag classes must have zero joint fingerprint.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <map>
#include <random>
#include <stdexcept>
#include <vector>
using namespace std;
using Hash = uint64_t;
constexpr int n = 1197;
using Bits = array<int, n>;
struct Swap {
    int from, to, size;
    Hash h;
};
struct Moves {
    vector<Swap> swaps;
    vector<vector<Hash>> cross;
    const vector<int> &cell;
    Moves(const Bits &row, const vector<int> &cells, const vector<vector<int>> &orbits,
          const vector<int> &lags, const vector<Hash> &weight)
        : cell(cells) {
        int c = orbits.size();
        cross.assign(c, vector<Hash>(c));
        vector<Hash> linear(c);
        vector<int> direction(c);
        for (int a = 0; a < c; a++)
            direction[a] = 1 - 2 * row[orbits[a][0]];
        for (size_t k = 0; k < lags.size(); k++)
            for (int i = 0; i < n; i++) {
                int j = (i + lags[k]) % n, a = cell[i], b = cell[j];
                Hash w = weight[k];
                linear[a] += w * (direction[a] * row[j]);
                linear[b] += w * (direction[b] * row[i]);
                if (a == b) {
                    linear[a] += w;
                    continue;
                }
                Hash mix = w * (direction[a] * direction[b]);
                cross[a][b] += mix;
                cross[b][a] += mix;
            }
        for (int a = 0; a < c; a++)
            if (direction[a] < 0)
                for (int b = 0; b < c; b++)
                    if (direction[b] > 0 && orbits[a].size() == orbits[b].size())
                        swaps.push_back(
                            {a, b, int(orbits[a].size()), linear[a] + linear[b] + cross[a][b]});
        if (swaps.size() >= 65535)
            throw runtime_error("too many single exchanges");
    }
    template <class Fn> void each(int radius, Fn use) const {
        use(Hash(0), uint32_t(0));
        for (size_t i = 0; i < swaps.size(); i++) {
            const auto &a = swaps[i];
            uint32_t first = uint32_t(i + 1);
            use(a.h, first);
            if (radius < 2)
                continue;
            for (size_t j = i + 1; j < swaps.size(); j++) {
                const auto &b = swaps[j];
                if (a.from == b.from || a.to == b.to)
                    continue;
                // For two exchanges in the same bucket match ordered removals to ordered additions
                // once.
                if (a.size == b.size && ((a.from < b.from) != (a.to < b.to)))
                    continue;
                Hash h = a.h + b.h + cross[a.from][b.from] + cross[a.from][b.to] +
                         cross[a.to][b.from] + cross[a.to][b.to];
                use(h, first | (uint32_t(j + 1) << 16));
            }
        }
    }
    Bits apply(const Bits &orig, uint32_t id, const vector<vector<int>> &orbits) const {
        Bits v = orig;
        for (uint32_t k : {id & 65535, id >> 16})
            if (k) {
                const auto &s = swaps.at(k - 1);
                for (int a : {s.from, s.to})
                    for (int x : orbits[a])
                        v[x] ^= 1;
            }
        return v;
    }
};
int intersection(const Bits &row, int s) {
    int a = 0;
    for (int i = 0; i < n; i++)
        a += row[i] * row[(i + s) % n];
    return a;
}
int main(int argc, char **argv) {
    if (argc < 2)
        return 2;
    int radius = stoi(argv[1]);
    if (radius < 1 || radius > 2)
        return 2;
    bool control = argc > 2 && string(argv[2]) == "control";
    vector<int> group(9);
    for (auto &g : group)
        cin >> g;
    array<Bits, 2> bits{};
    for (auto &row : bits)
        for (auto &x : row)
            if (!(cin >> x) || (x != 0 && x != 1))
                return 2;
    int count;
    cin >> count;
    vector<int> lags(count);
    for (auto &t : lags)
        cin >> t;
    vector<vector<int>> orbits;
    vector<int> cell(n, -1);
    for (int i = 0; i < n; i++)
        if (cell[i] < 0) {
            vector<int> orb;
            for (int u : group)
                orb.push_back(u * i % n);
            sort(orb.begin(), orb.end());
            orb.erase(unique(orb.begin(), orb.end()), orb.end());
            for (int j : orb)
                cell[j] = orbits.size();
            orbits.push_back(orb);
        }
    for (auto &row : bits)
        for (auto &orb : orbits)
            for (int j : orb)
                if (row[j] != row[orb[0]])
                    throw runtime_error("bad symmetry");
    mt19937_64 rng(50103);
    vector<Hash> coeff(count);
    for (auto &w : coeff)
        w = rng();
    Moves A(bits[0], cell, orbits, lags, coeff), B(bits[1], cell, orbits, lags, coeff);
    Bits ca = bits[0], cb = bits[1];
    Hash target = 0;
    if (control) {
        // Plant two disjoint exchanges in each word. The target is recomputed by scalar overlaps.
        auto planted = [&](const Moves &m) {
            uint32_t result = 0;
            m.each(radius, [&](Hash, uint32_t id) {
                if (!result && (radius == 1 ? id != 0 : (id >> 16) != 0))
                    result = id;
            });
            return result;
        };
        ca = A.apply(ca, planted(A), orbits);
        cb = B.apply(cb, planted(B), orbits);
    }
    vector<int> targetOverlap(count);
    for (int k = 0; k < count; k++) {
        int t = lags[k];
        targetOverlap[k] = intersection(ca, t) + intersection(cb, t);
        target +=
            coeff[k] * (targetOverlap[k] - intersection(bits[0], t) - intersection(bits[1], t));
    }
    vector<pair<Hash, uint32_t>> left;
    A.each(radius, [&](Hash h, uint32_t id) { left.emplace_back(h, id); });
    sort(left.begin(), left.end());
    uint64_t nb = 0, hits = 0, exact = 0;
    B.each(radius, [&](Hash h, uint32_t id) {
        nb++;
        auto it = lower_bound(left.begin(), left.end(), make_pair(target - h, uint32_t(0)));
        while (it != left.end() && it->first == target - h) {
            hits++;
            auto a = A.apply(bits[0], it->second, orbits), b = B.apply(bits[1], id, orbits);
            bool ok = true;
            for (int k = 0; k < count; k++)
                if (intersection(a, lags[k]) + intersection(b, lags[k]) != targetOverlap[k]) {
                    ok = false;
                    break;
                }
            if (ok) {
                exact++;
                if (!control && (id || it->second))
                    cerr << "nonidentity match " << it->second << " " << id << "\n";
            }
            ++it;
        }
    });
    cout << "{\"row_neighborhoods\":[" << left.size() << "," << nb
         << "],\"word_pairs\":" << left.size() * nb << ",\"fingerprint_matches\":" << hits
         << ",\"exact_matches\":" << exact << "}\n";
}
