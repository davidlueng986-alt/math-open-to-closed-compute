// Optimize the full 399-point quotient, retaining an explicit binary lift after every move.
#include "../hadamard-2396-diagonal/engine.hpp"
#include <limits>
using Vector = array<int, 74>;
constexpr int cells = 21 * 7;
struct Edge {
    int shift, coefficient;
};
struct Change {
    int cell, direction;
};
struct Trade {
    Move moves;
    array<Change, 8> changes;
};
struct Quotient {
    Engine signs;
    int cellAt[399]{}, label[399]{};
    vector<int> shifts;
    Vector weight{}, error{}, selected{};
    array<array<int, cells>, 2> table{};
    array<array<Vector, cells>, 2> derivative{};
    array<array<vector<Edge>, cells>, cells> hessian;
    explicit Quotient(unsigned seed) : signs(seed, true) {
        signs.load();
        for (int i = 0; i < 399; i++)
            cellAt[i] = 21 * signs.orbit[i % 19] + i % 21;
        for (int i = 0; i < 399; i++) {
            int canonical = 399;
            for (int m : {1, 64, 106})
                for (int sign : {1, -1})
                    canonical = min(canonical, (399 + sign * (m * i % 399)) % 399);
            if (canonical == i)
                shifts.push_back(i);
            auto it = find(shifts.begin(), shifts.end(), canonical);
            if (it == shifts.end())
                throw runtime_error("missing shift orbit");
            label[i] = int(it - shifts.begin());
            weight[label[i]]++;
        }
        if (shifts.size() != 74)
            throw runtime_error("wrong number of quotient orbits");
        for (int &w : weight)
            w = max(1, w / 2);
        // Coarse constraints for the two original subgroups, plus all lifts of shift 1.
        for (int i = 0; i < 399; i++)
            if (i % 19 == 0 || i % 21 == 0)
                selected[label[i]] = 1;
        selected[label[1]] = 1;
        for (int l = 0; l < 74; l++) {
            array<array<int, cells>, cells> counts{};
            for (int i = 0; i < 399; i++) {
                int u = cellAt[i], v = cellAt[(i + shifts[l]) % 399];
                counts[u][v]++;
                counts[v][u]++;
            }
            for (int u = 0; u < cells; u++)
                for (int v = 0; v < cells; v++)
                    if (counts[u][v])
                        hessian[u][v].push_back({l, counts[u][v]});
        }
        rebuild();
    }
    void rebuild() {
        for (auto &row : derivative)
            for (auto &column : row)
                column.fill(0);
        error.fill(0);
        error[0] = -2390;
        for (int l = 1; l < 74; l++)
            error[l] = 6;
        for (int f = 0; f < 2; f++) {
            for (int k = 0; k < 7; k++)
                for (int r = 0; r < 21; r++) {
                    Bits mask = (Bits(1) << r) | (Bits(1) << (r + 21)) | (Bits(1) << (r + 42));
                    table[f][21 * k + r] = 3 - 2 * pop(signs.s[f][k] & mask);
                }
            for (int u = 0; u < cells; u++)
                for (int v = 0; v < cells; v++)
                    for (auto e : hessian[u][v])
                        derivative[f][u][e.shift] += table[f][v] * e.coefficient;
            for (int l = 0; l < 74; l++)
                for (int i = 0; i < 399; i++)
                    error[l] += table[f][cellAt[i]] * table[f][cellAt[(i + shifts[l]) % 399]];
        }
        for (int &e : error) {
            if (e % 4)
                throw runtime_error("invalid PAF residue");
            e /= 4;
        }
    }
    Trade randomTrade() {
        Trade t{};
        while (!signs.transfer(t.moves))
            t.moves = Move{};
        int n = 0;
        int f = t.moves.f;
        for (int k = 0; k < 6; k++) {
            Bits b = t.moves.masks[k];
            while (b) {
                int i = __builtin_ctzll(b);
                b &= b - 1;
                // direction is half the change to this triple sum.
                t.changes.at(n++) = {21 * k + i % 21, ((signs.s[f][k] >> i) & 1) ? 1 : -1};
            }
        }
        if (n != 8)
            throw runtime_error("rectangle size mismatch");
        return t;
    }
    Vector changed(const Trade &t) const {
        // If W changes by 2v, (P(W+2v)-P(W))/4 = ((H W).v)/2 + v.H.v/2.
        Vector delta{};
        int f = t.moves.f;
        for (int i = 0; i < 8; i++) {
            auto [u, a] = t.changes[i];
            const Vector &d = derivative[f][u];
            for (int l = 0; l < 74; l++)
                delta[l] += a * d[l];
            for (auto e : hessian[u][u])
                delta[e.shift] += e.coefficient;
            for (int j = 0; j < i; j++) {
                auto [v, b] = t.changes[j];
                for (auto e : hessian[u][v])
                    delta[e.shift] += 2 * a * b * e.coefficient;
            }
        }
        for (int l = 0; l < 74; l++)
            delta[l] = error[l] + delta[l] / 2;
        return delta;
    }
    void accept(const Trade &t, const Vector &next) {
        signs.flip(t.moves);
        int f = t.moves.f;
        error = next;
        for (auto [u, a] : t.changes) {
            table[f][u] += 2 * a;
            for (int v = 0; v < cells; v++)
                for (auto e : hessian[u][v])
                    derivative[f][v][e.shift] += 2 * a * e.coefficient;
        }
    }
    pair<int, int> scores(const Vector &v) const {
        int all = 0, focus = 0;
        for (int i = 0; i < 74; i++) {
            all += weight[i] * v[i] * v[i];
            if (selected[i]) {
                int w = (shifts[i] % 19 == 0 ? 3 : 1);
                focus += (v[i] / w) * (v[i] / w);
            }
        }
        return {all, focus};
    }
    void restore(const State &s) {
        signs.s = s;
        rebuild();
    }
    void anneal(int steps, int penalty) {
        auto score = [&](const Vector &v) {
            auto [all, focus] = scores(v);
            return all + penalty * focus;
        };
        State best = signs.s;
        int curr = score(error), low = curr;
        int period = 12000;
        for (int i = 0; low && i < steps; i++) {
            if (i && i % period == 0) {
                restore(best);
                curr = low;
            }
            auto t = randomTrade();
            auto next = changed(t);
            int now = score(next);
            double temp = (penalty < 4 ? 110.0 : 110.0 + penalty * 3.0) *
                          pow(0.022, double(i % period) / period);
            if (now <= curr ||
                generate_canonical<double, 52>(signs.rng) < exp((curr - now) / temp)) {
                accept(t, next);
                curr = now;
                if (curr < low) {
                    low = curr;
                    best = signs.s;
                }
            }
            if (i % 2048 == 0) {
                auto exact = error;
                rebuild();
                if (exact != error)
                    throw runtime_error("incremental PAF mismatch");
            }
        }
        restore(best);
    }
    vector<Trade> rectangles(int f) {
        vector<Trade> list;
        for (int a = 0; a < 6; a++)
            for (int b = a + 1; b < 6; b++)
                for (int row = 0; row < 3; row++)
                    for (int h = row + 1; h < 3; h++)
                        for (int j = 0; j < 7; j++)
                            for (int k = j + 1; k < 7; k++)
                                for (int direction : {0, 1}) {
                                    Move m;
                                    m.f = f;
                                    if (!signs.bitsForCell(f, a, b, signs.address[row][j],
                                                           direction, m) ||
                                        !signs.bitsForCell(f, a, b, signs.address[h][j], !direction,
                                                           m) ||
                                        !signs.bitsForCell(f, a, b, signs.address[h][k], direction,
                                                           m) ||
                                        !signs.bitsForCell(f, a, b, signs.address[row][k],
                                                           !direction, m))
                                        continue;
                                    Trade t;
                                    t.moves = m;
                                    int n = 0;
                                    for (int col : {a, b})
                                        for (Bits bit = m.masks[col]; bit; bit &= bit - 1) {
                                            int i = __builtin_ctzll(bit);
                                            t.changes[n++] = {21 * col + i % 21,
                                                              ((signs.s[f][col] >> i) & 1) ? 1
                                                                                           : -1};
                                        }
                                    list.push_back(t);
                                }
        return list;
    }
    using Pair = array<int, 2>;
    void repair() {
        const State root = signs.s;
        State best = root;
        const Vector base = error;
        auto [bestAll, bestFocus] = scores(base);
        array<uint64_t, 74> hashWeights{};
        mt19937_64 hashing(7313317);
        for (int l = 0; l < 74; l++)
            if (selected[l])
                hashWeights[l] = hashing();
        auto fingerprint = [&](const Vector &vec) {
            uint64_t key = 0;
            for (int l = 0; l < 74; l++)
                key += hashWeights[l] * uint64_t(vec[l]);
            return key;
        };
        uint64_t target = 0 - fingerprint(base);
        array<array<uint64_t, cells>, cells> crossHash{};
        for (int u = 0; u < cells; u++)
            for (int v = 0; v < cells; v++)
                for (auto e : hessian[u][v])
                    crossHash[u][v] += e.coefficient * hashWeights[e.shift];
        array<vector<Trade>, 2> lists{rectangles(0), rectangles(1)};
        unordered_map<uint64_t, Pair> saved;
        for (int f = 0; f < 2; f++) {
            auto &list = lists[f];
            int n = list.size();
            vector<uint64_t> single(n);
            vector<array<uint64_t, cells>> cross(n);
            for (int i = 0; i < n; i++) {
                single[i] = fingerprint(changed(list[i])) - fingerprint(base);
                for (auto [u, a] : list[i].changes)
                    for (int v = 0; v < cells; v++)
                        cross[i][v] += uint64_t(a) * crossHash[u][v];
            }
            auto visit = [&](uint64_t hash, Pair ids) {
                if (f == 0) {
                    saved.emplace(hash, ids);
                    return;
                }
                auto it = saved.find(target - hash);
                if (it == saved.end())
                    return;
                signs.s = root;
                for (int i : it->second)
                    if (i >= 0)
                        signs.flip(lists[0][i].moves);
                for (int i : ids)
                    if (i >= 0)
                        signs.flip(lists[1][i].moves);
                rebuild();
                auto [all, focus] = scores(error);
                if (focus == 0 && (bestFocus || all < bestAll)) {
                    best = signs.s;
                    bestAll = all;
                    bestFocus = 0;
                }
                restore(root);
            };
            visit(0, {-1, -1});
            for (int i = 0; i < n; i++) {
                visit(single[i], {i, -1});
                for (int j = i + 1; j < n; j++) {
                    bool ok = true;
                    for (int k = 0; k < 6; k++)
                        if (list[i].moves.masks[k] & list[j].moves.masks[k])
                            ok = false;
                    if (!ok)
                        continue;
                    uint64_t hash = single[i] + single[j];
                    for (auto [v, b] : list[j].changes)
                        hash += uint64_t(b) * cross[i][v];
                    visit(hash, {i, j});
                }
            }
        }
        restore(best);
    }
    void print() {
        if (scores(error).second == 0 && error[label[1]] != 0)
            throw runtime_error("focussed score mismatch");
        auto all = signs.expand(signs.s);
        auto [global, focus] = scores(error);
        cout << "{\"quotient_energy\":" << 16 * global << ",\"focus_score\":" << focus
             << ",\"rows\":[";
        for (int f = 0; f < 2; f++) {
            cout << (f ? ",\"" : "\"");
            for (int i = 0; i < 1197; i++)
                cout << ((all[f][i % 19] >> (i % 63)) & 1);
            cout << '"';
        }
        cout << "]}\n";
    }
};
int main(int argc, char **argv) {
    if (argc < 4 || argc % 2 != 0) {
        cerr << "usage: search SEED STEPS PENALTY [STEPS PENALTY ...]\n";
        return 2;
    }
    Quotient q(stoul(argv[1]));
    for (int i = 2; i < argc; i += 2) {
        int steps = stoi(argv[i]);
        if (steps)
            q.anneal(steps, stoi(argv[i + 1]));
        else
            q.repair();
    }
    q.print();
}
