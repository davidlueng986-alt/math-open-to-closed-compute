#pragma once

// Search invariant sign words on Z/63 x Z/19. Bit x is one for a negative sign.
#include <algorithm>
#include <array>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <random>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>
using namespace std;
using Bits = uint64_t;
using State = array<array<Bits, 7>, 2>;
using Columns = array<array<Bits, 19>, 2>;
using Profile = array<int, 14>;
struct ProfileHash {
    size_t operator()(const Profile &v) const {
        uint64_t h = 0;
        for (int a : v)
            h = h * 0x9e3779b97f4a7c15ULL + uint64_t(a);
        return h;
    }
};
constexpr array<int, 3> yShifts{1, 2, 4};
constexpr array<int, 7> columns{1, 2, 4, 5, 8, 10, 0};
constexpr Bits mask63 = (Bits(1) << 63) - 1;
int pop(Bits x) { return __builtin_popcountll(x); }
int mismatches(Bits x, int t) { return pop(x ^ (((x << t) & mask63) | (x >> (63 - t)))); }
struct Move {
    int f = 0;
    array<Bits, 7> masks{};
};
struct Engine {
    mt19937_64 rng;
    State initial{}, s{}, best{};
    bool mixed;
    int orbit[19]{};
    int address[3][7]{}, weight[7] = {3, 3, 3, 3, 3, 3, 1};
    array<array<array<int, 21>, 7>, 2> triples{};
    array<array<array<int, 11>, 7>, 2> local{};
    Profile coarse{};
    array<array<int, 3>, 2> cross{};
    int energy = 0;
    explicit Engine(unsigned seed, bool mixed) : rng(seed), mixed(mixed) {
        for (int x = 0; x < 21; x++)
            address[x % 3][x % 7] = x;
        for (int k = 0; k < 7; k++) {
            int y = columns[k];
            for (int j = 0; j < weight[k]; j++) {
                orbit[y] = k;
                y = y * 7 % 19;
            }
        }
    }
    unsigned draw(unsigned n) { return rng() % n; }
    static Bits decimate(Bits b) {
        Bits out = 0;
        while (b) {
            int x = __builtin_ctzll(b);
            out |= Bits(1) << ((22 * x) % 63);
            b &= b - 1;
        }
        return out;
    }
    Columns expand(const State &v) const {
        Columns out{};
        for (int f = 0; f < 2; f++)
            for (int k = 0; k < 7; k++) {
                int y = columns[k];
                Bits b = v[f][k];
                for (int i = 0; i < weight[k]; i++) {
                    out[f][y] = b;
                    y = y * 7 % 19;
                    b = decimate(b);
                }
            }
        return out;
    }
    void load() {
        Columns input{};
        for (auto &r : input)
            for (int i = 0; i < 1197; i++) {
                int x;
                if (!(cin >> x) || (x != 1 && x != -1))
                    throw runtime_error("expected signed input");
                if (x < 0)
                    r[i % 19] |= Bits(1) << (i % 63);
            }
        for (int f = 0; f < 2; f++)
            for (int k = 0; k < 7; k++)
                initial[f][k] = input[f][columns[k]];
        if (expand(initial) != input)
            throw runtime_error("input not invariant under 463");
        s = best = initial;
    }
    void profile(int f, int k) {
        auto &u = triples[f][k];
        auto &v = local[f][k];
        Bits w = s[f][k];
        for (int i = 0; i < 21; i++)
            u[i] =
                3 - 2 * pop(w & ((Bits(1) << i) | (Bits(1) << (i + 21)) | (Bits(1) << (i + 42))));
        for (int t = 0; t <= 10; t++) {
            int h = 0;
            for (int i = 0; i < 21; i++)
                h += u[i] * u[(i + t) % 21];
            v[t] = h * weight[k];
        }
    }
    // Under x -> 22x, x mod 21 is fixed, so all three columns in an orbit
    // have exactly the same 21 triple sums. Compute mixed coarse correlations on Z/19.
    array<int, 3> crossProfile(int f) const {
        array<int, 3> out{};
        for (int t = 0; t < 3; t++)
            for (int y = 0; y < 19; y++) {
                const auto &a = triples[f][orbit[y]], &b = triples[f][orbit[(y + yShifts[t]) % 19]];
                for (int r = 0; r < 21; r++)
                    out[t] += a[r] * b[r];
            }
        return out;
    }
    void initialize() {
        coarse.fill(0);
        coarse[0] = -2390;
        for (int t = 1; t <= 10; t++)
            coarse[t] = 6;
        for (int f = 0; f < 2; f++)
            for (int k = 0; k < 7; k++) {
                profile(f, k);
                for (int t = 0; t <= 10; t++)
                    coarse[t] += local[f][k][t];
            }
        if (mixed) {
            for (int f = 0; f < 2; f++)
                cross[f] = crossProfile(f);
            for (int j = 0; j < 3; j++)
                coarse[11 + j] = cross[0][j] + cross[1][j] + 6;
        }
    }
    int coarseScore() const {
        int z = 0;
        for (unsigned t = 0; t < coarse.size(); t++) {
            int h = coarse[t];
            int unit = t < 11 ? 12 : 4;
            if (h % unit)
                throw runtime_error("coarse residue cannot reach zero");
            int v = h / unit;
            z += v * v;
        }
        return z;
    }
    void update(const Move &m) {
        for (int k = 0; k < 6; k++)
            if (m.masks[k]) {
                for (int t = 0; t < 11; t++)
                    coarse[t] -= local[m.f][k][t];
                s[m.f][k] ^= m.masks[k];
                profile(m.f, k);
                for (int t = 0; t < 11; t++)
                    coarse[t] += local[m.f][k][t];
            }
        if (mixed) {
            auto now = crossProfile(m.f);
            for (int j = 0; j < 3; j++)
                coarse[11 + j] += now[j] - cross[m.f][j];
            cross[m.f] = now;
        }
    }
    bool bitsForCell(int f, int a, int b, int r, bool want, Move &m) {
        int x = address[r % 3][r % 7];
        int p = draw(3), q = draw(3);
        for (int u = 0; u < 3; u++) {
            int i = x + 21 * ((p + u) % 3);
            if (bool((s[f][a] >> i) & 1) != want)
                continue;
            for (int v = 0; v < (r % 3 ? 3 : 1); v++) {
                int j = r % 3 ? x + 21 * ((q + v) % 3) : i;
                if (bool((s[f][b] >> j) & 1) == want)
                    continue;
                m.masks[a] |= Bits(1) << i;
                m.masks[b] |= Bits(1) << j;
                return true;
            }
        }
        return false;
    }
    bool transfer(Move &m, int fixed = -1) {
        int f = fixed < 0 ? draw(2) : fixed, a = draw(6), b = (a + 1 + draw(5)) % 6, r = draw(3),
            h = (r + 1 + draw(2)) % 3, j = draw(7), l = (j + 1 + draw(6)) % 7;
        bool sign = draw(2);
        m.f = f;
        return bitsForCell(f, a, b, address[r][j], sign, m) &&
               bitsForCell(f, a, b, address[h][j], !sign, m) &&
               bitsForCell(f, a, b, address[h][l], sign, m) &&
               bitsForCell(f, a, b, address[r][l], !sign, m);
    }
    // Rectangle moves in (x mod 3, x mod 7) preserve all three prescribed projections.
    void coarseSearch(int limit) {
        initialize();
        energy = coarseScore();
        int low = energy;
        best = s;
        for (int i = 0; low && i < limit; i++) {
            if (i && i % 5000 == 0) {
                s = best;
                initialize();
                energy = low;
            }
            Move m;
            int tries = 0;
            while (!transfer(m)) {
                m = Move{};
                if (++tries > 100000)
                    throw runtime_error("no coarse moves");
            }
            update(m);
            int e = coarseScore();
            const double initialTemperature = mixed ? 5.0 : 1.7;
            double temp = initialTemperature * pow(0.05, double(i % 5000) / 5000);
            if (e <= energy || generate_canonical<double, 52>(rng) < exp((energy - e) / temp)) {
                energy = e;
                if (e < low) {
                    low = e;
                    best = s;
                }
            } else
                update(m);
        }
        s = best;
        initialize();
        energy = coarseScore();
        cerr << "coarse " << energy << '\n';
    }
    // Match independent changes to the two words against the exact integer defect vector.
    bool coarseRepair(int count) {
        if (!energy)
            return true;
        const State root = s;
        auto original = coarse;
        unordered_map<Profile, array<Bits, 7>, ProfileHash> found;
        found.reserve(count);
        for (int word = 0; word < 2; word++) {
            for (int i = 0; i < count; i++) {
                Move moves[6];
                int n = (i == 0 ? 0 : 1 + draw(6));
                for (int j = 0; j < n; j++) {
                    while (!transfer(moves[j], word))
                        moves[j] = Move{};
                    update(moves[j]);
                }
                if (!word)
                    found.emplace(coarse, s[0]);
                else {
                    Profile key{};
                    for (size_t j = 0; j < coarse.size(); j++)
                        key[j] = original[j] - coarse[j];
                    auto it = found.find(key);
                    if (it != found.end()) {
                        State trial = s;
                        trial[0] = it->second;
                        s = trial;
                        initialize();
                        energy = coarseScore();
                        if (energy)
                            throw runtime_error("false coarse signature");
                        best = s;
                        return true;
                    }
                }
                for (int j = n; j-- > 0;)
                    update(moves[j]);
            }
        }
        if (s != root || coarse != original)
            throw runtime_error("failed to restore");
        return false;
    }

    // Permute entries within a triple; compensate in another column when x is fixed by 22.
    bool phase(Move &m, int fixed = -1) {
        int f = fixed < 0 ? int(draw(2)) : fixed, r = draw(21), a = draw(6), h = draw(3),
            k = (h + 1 + draw(2)) % 3;
        int i = r + 21 * h, j = r + 21 * k;
        bool x = (s[f][a] >> i) & 1, y = (s[f][a] >> j) & 1;
        if (x == y)
            return false;
        m.f = f;
        Bits flip = (Bits(1) << i) | (Bits(1) << j);
        m.masks[a] = flip;
        if (r % 3 == 0) {
            int b = (a + 1 + draw(5)) % 6;
            if (bool((s[f][b] >> i) & 1) == x || bool((s[f][b] >> j) & 1) != x)
                return false;
            m.masks[b] = flip;
        }
        return true;
    }
    array<int, 19> axisDefects(const State &v) const {
        array<int, 19> d{};
        for (int t = 0; t < 10; t++) {
            int h = 0;
            for (int f = 0; f < 2; f++)
                for (int k = 0; k < 7; k++)
                    h += weight[k] * mismatches(v[f][k], 3 * (t + 1));
            int diff = 1198 - h;
            if (diff % 6)
                throw runtime_error("singleton PAF congruence invalid");
            d[t] = diff / 6;
        }
        Columns all = expand(v);
        int tail = 10;
        for (int t : {1, 2, 4}) {
            int h = 0;
            for (auto &w : all)
                for (int k = 0; k < 19; k++)
                    h += pop(w[k] ^ w[(k + t) % 19]);
            int diff = 1198 - h;
            if (diff % 2)
                throw runtime_error("odd mismatch count");
            d[tail++] = diff / 2;
        }
        if (mixed)
            for (int t : {1, 2, 4, 5, 8, 10}) {
                int h = 0;
                for (auto &word : all)
                    for (int y = 0; y < 19; y++) {
                        Bits b = word[(y + t) % 19];
                        Bits rotated = (b >> 21) | ((b << 42) & mask63);
                        h += pop(word[y] ^ rotated);
                    }
                int diff = 1198 - h;
                if (diff % 2)
                    throw runtime_error("odd mixed difference");
                d[tail++] = diff / 2;
            }
        return d;
    }
    static int phaseScore(const array<int, 19> &d) {
        int z = 0;
        for (int v : d)
            z += v * v;
        return z;
    }
    void flip(const Move &m) {
        for (int k = 0; k < 6; k++)
            s[m.f][k] ^= m.masks[k];
    }
    void phaseSearch(int limit) {
        int e = phaseScore(axisDefects(s)), low = e;
        best = s;
        for (int i = 0; low && i < limit; i++) {
            if (i && i % 5000 == 0) {
                s = best;
                e = low;
            }
            Move m;
            while (!phase(m))
                m = Move{};
            flip(m);
            int next = phaseScore(axisDefects(s));
            double temp = 2.9 * pow(0.045, double(i % 5000) / 5000);
            if (next <= e || generate_canonical<double, 52>(rng) < exp((e - next) / temp)) {
                e = next;
                if (e < low) {
                    low = e;
                    best = s;
                }
            } else
                flip(m);
        }
        s = best;
        energy = phaseScore(axisDefects(s));
        cerr << "phases " << energy << '\n';
    }
    // A meet-in-the-middle repair in the two independent words preserves every triple sum.
    void phaseRepair(int count) {
        if (energy == 0)
            return;
        const State root = s;
        const auto base = axisDefects(s);
        struct Hash {
            size_t operator()(const array<int, 19> &v) const {
                uint64_t h = 0;
                for (int a : v)
                    h = h * 0x9e3779b97f4a7c15ULL + uint64_t(a);
                return h;
            }
        };
        unordered_map<array<int, 19>, array<Bits, 7>, Hash> found;
        found.reserve(count);
        for (int f = 0; f < 2; f++)
            for (int i = 0; i < count; i++) {
                s = root;
                int n = i ? 1 + draw(6) : 0;
                for (int j = 0; j < n; j++) {
                    Move m;
                    while (!phase(m, f))
                        m = Move{};
                    flip(m);
                }
                auto d = axisDefects(s);
                if (f == 0) {
                    found.emplace(d, s[0]);
                    continue;
                }
                for (int j = 0; j < 19; j++)
                    d[j] = base[j] - d[j];
                auto it = found.find(d);
                if (it != found.end()) {
                    s[0] = it->second;
                    energy = phaseScore(axisDefects(s));
                    if (energy)
                        throw runtime_error("phase repair inconsistency");
                    best = s;
                    return;
                }
            }
        s = root;
    }
    void result() const {
        auto v = expand(s);
        cout << "{\"coarse_score\":" << coarseScore()
             << ",\"phase_score\":" << phaseScore(axisDefects(s)) << ",\"rows\":[";
        for (int f = 0; f < 2; f++) {
            cout << (f ? ",\"" : "\"");
            for (int i = 0; i < 1197; i++)
                cout << ((v[f][i % 19] >> (i % 63)) & 1);
            cout << '"';
        }
        cout << "]}\n";
    }
};
