// Exact Fourier decomposition on Z/63 x Z/19 with the square action on the second factor.
#include <algorithm>
#include <array>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <random>
#include <stdexcept>
#include <vector>
using namespace std;
using Word = array<int, 63>;
using Pair = array<Word, 2>;
using Lags = array<int, 32>;
using Spectrum = array<Lags, 3>;
struct Search {
    mt19937_64 rng;
    Pair m{}, a{}, d{}, X{}, F{};
    Spectrum err{};
    array<array<int, 63>, 32> plus{}, minus{};
    array<vector<int>, 2> light;
    vector<array<int, 2>> dSums;
    int draw(int n) { return int(rng() % n); }
    explicit Search(unsigned seed) : rng(seed) {
        for (int t = 0; t < 32; t++)
            for (int i = 0; i < 63; i++) {
                plus[t][i] = (i + t) % 63;
                minus[t][i] = (i - t + 63) % 63;
            }
        for (int f = 0; f < 2; f++) {
            uint64_t supp, neg;
            int orientation;
            cin >> supp >> neg >> orientation;
            if (!cin || neg & ~supp || abs(orientation) != 1)
                throw runtime_error("bad input template");
            for (int i = 0; i < 63; i++) {
                m[f][i] = ((supp >> i) & 1) ? (((neg >> i) & 1) ? -orientation : orientation) : 0;
                if (m[f][i] == 0)
                    light[f].push_back(i);
            }
        }
        array<int, 2> z{};
        for (int f = 0; f < 2; f++)
            z[f] = accumulate(m[f].begin(), m[f].end(), 0);
        int need = 126 + 2 * (z[0] + z[1]) - 19 * (z[0] * z[0] + z[1] * z[1]);
        for (int x = -11; x <= 11; x++)
            for (int y = -11; y <= 11; y++)
                if (x * x + y * y == need && (x + int(light[0].size())) % 2 == 0 &&
                    (y + int(light[1].size())) % 2 == 0)
                    dSums.push_back({x, y});
        if (dSums.empty())
            throw runtime_error("infeasible vertical norm");
        auto sums = dSums[draw(dSums.size())];
        for (int f = 0; f < 2; f++) {
            for (int i = 0; i < 63; i++)
                a[f][i] = i < (63 + 1 - 18 * z[f]) / 2 ? 1 : -1;
            shuffle(a[f].begin(), a[f].end(), rng);
            shuffle(light[f].begin(), light[f].end(), rng);
            for (size_t i = 0; i < light[f].size(); i++)
                d[f][light[f][i]] = int(i) < (int(light[f].size()) + sums[f]) / 2 ? 1 : -1;
        }
        rebuild();
    }
    void rebuild() {
        err = {};
        for (int f = 0; f < 2; f++) {
            for (int i = 0; i < 63; i++) {
                X[f][i] = a[f][i] + 18 * m[f][i];
                F[f][i] = a[f][i] - m[f][i];
            }
            for (int t = 0; t < 32; t++)
                for (int i = 0; i < 63; i++) {
                    int j = plus[t][i];
                    err[0][t] += X[f][i] * X[f][j];
                    err[1][t] += F[f][i] * F[f][j] + 19 * d[f][i] * d[f][j];
                    err[2][t] += F[f][i] * d[f][j] - d[f][i] * F[f][j];
                }
        }
        err[0][0] -= 2396;
        err[1][0] -= 2396;
        for (int &v : err[0])
            v += 38;
    }
    long long score(const Spectrum &e, bool quotient) const {
        long long n = 0;
        for (int t = 0; t < 32; t++) {
            long long r = e[0][t], u = e[1][t], s = e[2][t];
            n += (t ? 2 : 1) * (r * r + (quotient ? 0 : 18 * u * u + 342 * s * s));
        }
        return n;
    }
    Spectrum after(int f, int i, int j, bool changeD) const {
        Spectrum v = err;
        const auto &xf = X[f];
        const auto &ff = F[f];
        const auto &df = d[f];
        int h = -2 * (changeD ? df[i] : a[f][i]);
        int tpair = min(abs(i - j), 63 - abs(i - j));
        for (int t = 0; t < 32; t++) {
            int ip = plus[t][i], im = minus[t][i], jp = plus[t][j], jm = minus[t][j];
            int quad = t == 0 ? 8 : t == tpair ? -4 : 0;
            if (changeD) {
                v[1][t] += 19 * (h * (df[ip] + df[im] - df[jp] - df[jm]) + quad);
                v[2][t] += h * (ff[im] - ff[ip] - ff[jm] + ff[jp]);
            } else {
                v[0][t] += h * (xf[ip] + xf[im] - xf[jp] - xf[jm]) + quad;
                v[1][t] += h * (ff[ip] + ff[im] - ff[jp] - ff[jm]) + quad;
                v[2][t] += h * (df[ip] - df[im] - df[jp] + df[jm]);
            }
        }
        return v;
    }
    void walk(int steps, bool quotient, int period, int scale) {
        Pair saveA = a, saveD = d;
        long long current = score(err, quotient), best = current;
        for (int k = 0; k < steps && best; k++) {
            if (k && k % period == 0) {
                a = saveA;
                d = saveD;
                rebuild();
                current = best;
            }
            int f = draw(2);
            bool changeD = !quotient && draw(2);
            int i = 0, j = 0;
            auto &v = changeD ? d[f] : a[f];
            do {
                i = changeD ? light[f][draw(light[f].size())] : draw(63);
                j = changeD ? light[f][draw(light[f].size())] : draw(63);
            } while (v[i] == v[j]);
            Spectrum next = after(f, i, j, changeD);
            long long cost = score(next, quotient);
            double temp = scale * pow(.012, double(k % period) / period);
            if (cost <= current ||
                generate_canonical<double, 52>(rng) < exp(double(current - cost) / temp)) {
                swap(v[i], v[j]);
                err = next;
                current = cost;
                if (!changeD)
                    for (int h : {i, j}) {
                        X[f][h] = a[f][h] + 18 * m[f][h];
                        F[f][h] = a[f][h] - m[f][h];
                    }
                if (current < best) {
                    saveA = a;
                    saveD = d;
                    best = current;
                }
            }
        }
        a = saveA;
        d = saveD;
        rebuild();
        if (score(err, quotient) != best)
            throw runtime_error("incremental score mismatch");
    }
    void print() const {
        long long full = score(err, false);
        if (full % 38)
            throw runtime_error("full score is not integral");
        cout << "{\"raw_energy\":" << full / 38 << ",\"quotient_energy_all_shifts\":" << score(err, true)
             << ",\"rows\":[";
        array<int, 19> chi{};
        chi.fill(-1);
        chi[0] = 0;
        for (int j = 1; j < 19; j++)
            chi[j * j % 19] = 1;
        for (int f = 0; f < 2; f++) {
            cout << (f ? ",\"" : "\"");
            for (int i = 0; i < 1197; i++) {
                int x = i % 63, k = i % 19;
                int s = k ? m[f][x] + chi[k] * d[f][x] : a[f][x];
                if (abs(s) != 1)
                    throw runtime_error("invalid binary lift");
                cout << (s < 0);
            }
            cout << '"';
        }
        cout << "]}\n";
    }
};
int main(int argc, char **argv) {
    if (argc < 3 || (argc - 3) % 4)
        return 2;
    Search s(stoul(argv[1]));
    if (string(argv[2]) == "signs") {
        for (int f = 0; f < 2; f++) {
            for (int &v : s.a[f])
                cin >> v;
            for (int &v : s.d[f])
                cin >> v;
        }
        if (!cin)
            throw runtime_error("missing signs");
        s.rebuild();
    } else if (string(argv[2]) != "random")
        return 2;
    for (int k = 3; k < argc; k += 4)
        s.walk(stoi(argv[k]), string(argv[k + 1]) == "quotient", stoi(argv[k + 2]),
               stoi(argv[k + 3]));
    s.print();
}
