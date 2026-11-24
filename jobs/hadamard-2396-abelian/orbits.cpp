// Direct original-length search on the two abelian groups of order 1197.
#include <algorithm>
#include <array>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <random>
#include <stdexcept>
#include <string>
#include <vector>
using namespace std;
constexpr int n = 1197, rowWeight = 598;
struct Edge {
    short lag, coefficient;
};
struct Change {
    int cell, delta;
};
struct Move {
    int row, size;
    array<Change, 4> bits;
};
using Row = array<vector<int>, 2>;
struct Search {
    bool plane;
    mt19937_64 rng;
    vector<int> group, representatives, weight, cell;
    array<vector<int>, 10> buckets;
    vector<vector<int>> members;
    vector<vector<vector<Edge>>> hessian;
    array<vector<vector<short>>, 2> gradient;
    Row state;
    vector<int> residual;
    int add(int a, int b) const {
        return (a + b + n - (plane && a % 3 + b % 3 >= 3 ? 399 : 0)) % n;
    }
    int inverse(int a) const { return (n - a + (plane && a % 3 ? 399 : 0)) % n; }
    int draw(int size) { return int(rng() % size); }
    Search(bool plane, unsigned seed) : plane(plane), rng(seed) {
        int size;
        cin >> size;
        if (size <= 0 || size > 9)
            throw runtime_error("bad multiplier group size");
        group.resize(size);
        for (int &u : group) {
            cin >> u;
            if (u < 1 || u >= n || u % 3 != 1 || gcd(u, n) != 1)
                throw runtime_error("bad multiplier");
        }
        sort(group.begin(), group.end());
        if (group.front() != 1 || adjacent_find(group.begin(), group.end()) != group.end())
            throw runtime_error("not a group");
        for (int a : group)
            for (int b : group)
                if (!binary_search(group.begin(), group.end(), a * b % n))
                    throw runtime_error("group not closed");
        cell.assign(n, -1);
        vector<int> labels(n, -1);
        for (int i = 0; i < n; i++) {
            if (cell[i] == -1) {
                int k = members.size();
                vector<int> points;
                for (int u : group)
                    points.push_back(i * u % n);
                sort(points.begin(), points.end());
                points.erase(unique(points.begin(), points.end()), points.end());
                for (int j : points)
                    cell[j] = k;
                buckets[points.size()].push_back(k);
                members.push_back(points);
            }
            if (i && labels[i] == -1) {
                int k = representatives.size();
                representatives.push_back(i);
                for (int u : group) {
                    labels[u * i % n] = k;
                    labels[inverse(u * i % n)] = k;
                }
            }
        }
        int c = members.size(), l = representatives.size();
        weight.assign(l, 0);
        for (int i = 1; i < n; i++)
            weight[labels[i]]++;
        for (int &w : weight)
            w /= 2;
        for (int i = 0; i < c; i++)
            hessian.emplace_back(c);
        for (int k = 0; k < l; k++)
            for (int i = 0; i < n; i++) {
                int a = cell[i], b = cell[add(i, representatives[k])];
                auto record = [k](vector<Edge> &edges) {
                    if (edges.empty() || edges.back().lag != k)
                        edges.push_back({short(k), 0});
                    edges.back().coefficient++;
                };
                record(hessian[a][b]);
                record(hessian[b][a]);
            }
        string input;
        cin >> input;
        for (int f = 0; f < 2; f++) {
            state[f].assign(c, 0);
            gradient[f].assign(c, vector<short>(l));
            if (input == "random")
                randomRow(f);
            else if (input == "signs") {
                int total = 0;
                vector<int> bits(n);
                for (int i = 0; i < n; i++) {
                    int z;
                    if (!(cin >> z) || (z != 1 && z != -1))
                        throw runtime_error("bad signs");
                    bits[i] = (z < 0);
                    state[f][cell[i]] = bits[i];
                    total += bits[i];
                }
                for (int i = 0; i < n; i++)
                    if (bits[i] != state[f][cell[i]])
                        throw runtime_error("input breaks the given multiplier");
                if (total != rowWeight)
                    throw runtime_error("input is not normalized");
            } else
                throw runtime_error("expected random or signs");
        }
        rebuild();
    }
    void randomRow(int f) {
        vector<array<int, 3>> options;
        vector<double> logits;
        auto logChoose = [](int a, int b) {
            return lgamma(a + 1.0) - lgamma(b + 1.0) - lgamma(a - b + 1.0);
        };
        for (int a = 0; a <= int(buckets[9].size()); a++)
            for (int b = 0; b <= int(buckets[3].size()); b++) {
                int c = rowWeight - 9 * a - 3 * b;
                if (c < 0 || c > int(buckets[1].size()))
                    continue;
                options.push_back({c, b, a});
                logits.push_back(logChoose(buckets[1].size(), c) + logChoose(buckets[3].size(), b) +
                                 logChoose(buckets[9].size(), a));
            }
        if (options.empty())
            throw runtime_error("no normalized orbit union");
        double high = *max_element(logits.begin(), logits.end());
        for (auto &v : logits)
            v = exp(v - high);
        auto chosen = options[discrete_distribution<int>(logits.begin(), logits.end())(rng)];
        int j = 0;
        for (int w : {1, 3, 9}) {
            auto ids = buckets[w];
            shuffle(ids.begin(), ids.end(), rng);
            for (int k = 0; k < chosen[j]; k++)
                state[f][ids[k]] = 1;
            j++;
        }
    }
    void rebuild() {
        int c = members.size(), l = representatives.size();
        residual.assign(l, -597);
        for (int f = 0; f < 2; f++) {
            for (auto &v : gradient[f])
                fill(v.begin(), v.end(), 0);
            for (int a = 0; a < c; a++)
                for (int b = 0; b < c; b++)
                    if (state[f][b])
                        for (auto e : hessian[a][b])
                            gradient[f][a][e.lag] += e.coefficient;
            for (int k = 0; k < l; k++)
                for (int i = 0; i < n; i++)
                    residual[k] += state[f][cell[i]] * state[f][cell[add(i, representatives[k])]];
        }
    }
    bool sample(Move &m) {
        m.row = draw(2);
        auto &s = state[m.row];
        int a = draw(members.size()), w = members[a].size();
        int direction = s[a] ? -1 : 1;
        m.bits[0] = {a, direction};
        m.size = 1;
        bool split = w > 1 && !buckets[w / 3].empty() && draw(18) == 0;
        int nChanges = split ? 3 : 1;
        auto &pool = buckets[split ? w / 3 : w];
        for (int j = 0; j < nChanges; j++) {
            int b = pool[draw(pool.size())];
            if (s[b] == s[a])
                return false;
            for (int h = 1; h < m.size; h++)
                if (m.bits[h].cell == b)
                    return false;
            m.bits[m.size++] = {b, -direction};
        }
        // The inverse split is also available, with the large orbit having the opposite sign.
        return true;
    }
    void propose(const Move &m, vector<int> &next) const {
        next = residual;
        for (int i = 0; i < m.size; i++) {
            auto [a, d] = m.bits[i];
            const auto &g = gradient[m.row][a];
            for (size_t k = 0; k < next.size(); k++)
                next[k] += d * g[k];
            for (auto e : hessian[a][a])
                next[e.lag] += e.coefficient / 2;
            for (int j = 0; j < i; j++) {
                auto [b, db] = m.bits[j];
                for (auto e : hessian[a][b])
                    next[e.lag] += d * db * e.coefficient;
            }
        }
    }
    void accept(const Move &m, vector<int> &next) {
        residual.swap(next);
        for (int j = 0; j < m.size; j++) {
            auto [a, d] = m.bits[j];
            state[m.row][a] += d;
            for (size_t b = 0; b < members.size(); b++)
                for (auto e : hessian[a][b])
                    gradient[m.row][b][e.lag] += d * e.coefficient;
        }
    }
    int energy(const vector<int> &v) const {
        int e = 0;
        for (size_t k = 0; k < v.size(); k++)
            e += weight[k] * v[k] * v[k];
        return e;
    }
    void walk(int steps, double scale, int period) {
        auto best = state;
        int curr = energy(residual), low = curr;
        vector<int> next(residual.size());
        for (int i = 0; i < steps && low; i++) {
            if (i && i % period == 0) {
                state = best;
                rebuild();
                curr = low;
            }
            Move m{};
            while (!sample(m)) {
            }
            propose(m, next);
            int e = energy(next);
            double temp = scale * pow(0.015, double(i % period) / period);
            if (e <= curr || generate_canonical<double, 52>(rng) < exp(double(curr - e) / temp)) {
                accept(m, next);
                curr = e;
                if (e < low) {
                    best = state;
                    low = e;
                }
            }
            if (i % 65536 == 0) {
                auto expected = residual;
                rebuild();
                if (expected != residual)
                    throw runtime_error("incremental autocorrelation mismatch");
            }
        }
        state = best;
        rebuild();
        if (low != energy(residual))
            throw runtime_error("best score mismatch");
    }
    struct Candidate {
        Move move{};
        vector<short> change;
        int gain = 0;
    };
    bool exchange(int cap) {
        int initial = energy(residual), dim = residual.size();
        array<vector<Candidate>, 2> pool;
        vector<int> next(dim);
        auto cheaper = [](const Candidate &a, const Candidate &b) { return a.gain < b.gain; };
        for (int f = 0; f < 2; f++) {
            for (int w : {1, 3, 9})
                for (int a : buckets[w])
                    if (state[f][a])
                        for (int b : buckets[w])
                            if (!state[f][b]) {
                                Move m{};
                                m.row = f;
                                m.size = 2;
                                m.bits[0] = {a, -1};
                                m.bits[1] = {b, 1};
                                propose(m, next);
                                int gain = energy(next) - initial;
                                if (int(pool[f].size()) == cap && gain >= pool[f].front().gain)
                                    continue;
                                if (int(pool[f].size()) == cap) {
                                    pop_heap(pool[f].begin(), pool[f].end(), cheaper);
                                    pool[f].pop_back();
                                }
                                Candidate v;
                                v.move = m;
                                v.gain = gain;
                                v.change.resize(dim);
                                for (int k = 0; k < dim; k++)
                                    v.change[k] = (next[k] - residual[k]) * (f ? 1 : weight[k]);
                                pool[f].push_back(move(v));
                                push_heap(pool[f].begin(), pool[f].end(), cheaper);
                            }
            Candidate zero;
            zero.move.row = f;
            zero.change.resize(dim);
            pool[f].push_back(move(zero));
        }
        int gain = 0;
        array<Move, 2> fix{};
        for (auto &a : pool[0])
            for (auto &b : pool[1]) {
                int mix = 0;
                for (int k = 0; k < dim; k++)
                    mix += a.change[k] * b.change[k];
                int total = a.gain + b.gain + 2 * mix;
                if (total < gain) {
                    gain = total;
                    fix = {a.move, b.move};
                }
            }
        if (!gain)
            return false;
        for (auto &m : fix)
            if (m.size) {
                propose(m, next);
                accept(m, next);
            }
        if (energy(residual) != initial + gain)
            throw runtime_error("two-word exchange mismatch");
        return true;
    }
    void kicks(int rounds, int depth, int cap) {
        while (exchange(cap)) {
        }
        Row best = state;
        int low = energy(residual);
        for (int i = 0; i < rounds; i++) {
            state = best;
            rebuild();
            vector<int> next(residual.size());
            for (int j = 0; j < depth; j++) {
                Move m{};
                while (!sample(m)) {
                }
                propose(m, next);
                accept(m, next);
            }
            while (exchange(cap)) {
            }
            int val = energy(residual);
            if (val < low) {
                best = state;
                low = val;
            }
        }
        state = best;
        rebuild();
    }
    void print() const {
        cout << "{\"raw_energy\":" << 16LL * energy(residual)
             << ",\"lag_classes\":" << representatives.size()
             << ",\"word_orbits\":" << members.size() << ",\"rows\":[";
        for (int f = 0; f < 2; f++) {
            cout << (f ? ",\"" : "\"");
            for (int i = 0; i < n; i++)
                cout << state[f][cell[i]];
            cout << '"';
        }
        cout << "]}\n";
    }
};
int main(int argc, char **argv) {
    if (argc < 6 || argc % 3)
        return 2;
    string law = argv[1];
    if (law != "cyclic" && law != "plane")
        return 2;
    Search s(law == "plane", stoul(argv[2]));
    for (int i = 3; i < argc; i += 3)
        if (stoi(argv[i]) < 0)
            s.kicks(-stoi(argv[i]), stoi(argv[i + 1]), stoi(argv[i + 2]));
        else
            s.walk(stoi(argv[i]), stod(argv[i + 1]), stoi(argv[i + 2]));
    s.print();
}
