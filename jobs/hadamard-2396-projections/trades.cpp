#include <algorithm>
#include <array>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <map>
#include <random>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>

using namespace std;
// CRT coordinates are (index mod 9, index mod 7, index mod 19).
// One balanced rectangle preserves the 63- and 133-point sums. When it
// changes the 57-point sums, a second rectangle cancels that change.
constexpr int length = 1197;
using Row = array<int, length>;
using Pair = array<Row, 2>;
struct Move {
    int word = 0, count = 0;
    array<int, 8> index{};
};
struct Search {
    mt19937_64 rng;
    Pair rows{}, bestRows{};
    int position[9][7][19]{}, shiftIndex[599]{};
    vector<int> shifts, residuals, delta;
    long long bestEnergy = 0, energy = 0;
    int draw(int k) { return int(rng() % k); }
    explicit Search(unsigned seed) : rng(seed) {
        for (int i = 0; i < length; i++)
            position[i % 9][i % 7][i % 19] = i;
    }
    vector<int> defects(const Pair &x) const {
        vector<int> out;
        for (int shift : shifts) {
            int p = 2;
            for (const Row &r : x)
                for (int i = 0; i < length; i++)
                    p += r[i] * r[(i + shift) % length];
            if (p % 4)
                throw runtime_error("invalid sign residual");
            out.push_back(p / 4);
        }
        return out;
    }
    static long long squaredNorm(const vector<int> &a) {
        long long t = 0;
        for (int x : a)
            t += x * x;
        return t;
    }
    void initialize(const Pair &p, vector<int> target) {
        rows = bestRows = p;
        shifts = target;
        fill(begin(shiftIndex), end(shiftIndex), -1);
        for (unsigned i = 0; i < target.size(); i++)
            shiftIndex[target[i]] = i;
        residuals = defects(rows);
        delta.resize(residuals.size());
        energy = bestEnergy = squaredNorm(residuals);
    }
    bool proposal(Move &move) {
        move.word = draw(2);
        int j = draw(7), k = draw(19), l = (k + 1 + draw(18)) % 19;
        int i = draw(9), a = i % 3;
        bool paired = draw(3) != 0;
        int b = paired ? (a + 1 + draw(2)) % 3 : a;
        int h = b + 3 * draw(3);
        if (i == h)
            return false;
        const Row &x = rows[move.word];
        auto square = [&](int u, int v, int g, int offset) {
            int a0 = position[u][g][k], b0 = position[u][g][l], c0 = position[v][g][k],
                d0 = position[v][g][l];
            if (x[a0] == x[b0] || x[a0] == x[c0] || x[a0] != x[d0])
                return false;
            move.index[offset] = a0;
            move.index[offset + 1] = b0;
            move.index[offset + 2] = c0;
            move.index[offset + 3] = d0;
            return true;
        };
        if (!square(i, h, j, 0))
            return false;
        move.count = 4;
        if (!paired)
            return true;
        int startj = (j + 1 + draw(6)) % 7, offseta = draw(3), offsetb = draw(3);
        for (int k2 = 0; k2 < 7; k2++) {
            int g = (startj + k2) % 7;
            if (g == j)
                continue;
            for (int u = 0; u < 3; u++) {
                int aa = a + 3 * ((offseta + u) % 3);
                if (x[position[aa][g][k]] == x[move.index[0]])
                    continue;
                for (int v = 0; v < 3; v++) {
                    int bb = b + 3 * ((offsetb + v) % 3);
                    if (square(aa, bb, g, 4)) {
                        move.count = 8;
                        return true;
                    }
                }
            }
        }
        return false;
    }
    long long scoreMove(const Move &m) {
        fill(delta.begin(), delta.end(), 0);
        auto &x = rows[m.word];
        for (int k = 0; k < m.count; k++) {
            int p = m.index[k], v = -2 * x[p];
            for (unsigned ix = 0; ix < shifts.size(); ix++) {
                int shift = shifts[ix], j = p + shift, h = p - shift;
                delta[ix] += v * (x[j >= length ? j - length : j] + x[h < 0 ? h + length : h]);
            }
            for (int z = 0; z < k; z++) {
                int l = m.index[z], dist = abs(l - p);
                int h = shiftIndex[min(dist, length - dist)];
                if (h >= 0)
                    delta[h] += 4 * x[p] * x[l];
            }
        }
        long long total = 0;
        for (unsigned i = 0; i < residuals.size(); i++) {
            delta[i] /= 4;
            long long value = residuals[i] + delta[i];
            total += value * value;
        }
        return total;
    }
    void accept(const Move &m, long long cost) {
        for (int k = 0; k < m.count; k++)
            rows[m.word][m.index[k]] *= -1;
        for (unsigned i = 0; i < residuals.size(); i++)
            residuals[i] += delta[i];
        energy = cost;
        if (energy < bestEnergy) {
            bestEnergy = energy;
            bestRows = rows;
        }
    }
    void run(int valid, double lowTemperature, double highTemperature) {
        if (!bestEnergy || valid == 0)
            return;
        const int cycle = min(20000, max(1000, valid / 10));
        int attempts = 0;
        for (int k = 0; k < valid;) {
            const int phase = k % cycle;
            if (phase == 0 && k > 0 && energy > bestEnergy) {
                rows = bestRows;
                residuals = defects(rows);
                energy = bestEnergy;
            }
            Move m;
            while (!proposal(m))
                if (++attempts > valid * 1000LL)
                    throw runtime_error("no switch");
            const double temp =
                highTemperature * pow(lowTemperature / highTemperature, double(phase) / cycle);
            const long long nextEnergy = scoreMove(m);
            ++k;
            if (delta[shiftIndex[399]] != 0)
                continue;
            if (nextEnergy <= energy ||
                generate_canonical<double, 53>(rng) < exp(-double(nextEnergy - energy) / temp))
                accept(m, nextEnergy);
            if (!bestEnergy)
                break;
        }
        if (squaredNorm(defects(bestRows)) != bestEnergy)
            throw runtime_error("bad incremental objective");
    }
};
struct ExactMoves {
    // The largest supported repair has 22 shifts (orders 7, 9, 19 and 21).
    static constexpr int capacity = 22;
    using Delta = array<int, capacity>;
    struct Entry {
        Move move;
        Delta delta{};
    };
    static uint64_t key(const Delta &a) {
        uint64_t r = 1469598103934665603ULL;
        for (auto x : a) {
            r ^= uint8_t(x);
            r *= 1099511628211ULL;
        }
        return r;
    }
    template <class Visit>
    static void visitMoves(const Search &search, int word, Visit recordMove) {
        auto &row = search.rows[word];
        for (int k = 0; k < 19; k++)
            for (int l = k + 1; l < 19; l++) {
                struct Rect {
                    int a, b, j, orient;
                    Move m;
                };
                vector<Rect> rectangles;
                for (int j = 0; j < 7; j++)
                    for (int i = 0; i < 9; i++)
                        for (int h = i + 1; h < 9; h++) {
                            int p = search.position[i][j][k], q = search.position[i][j][l],
                                r = search.position[h][j][k], shift = search.position[h][j][l];
                            if (row[p] == row[q] || row[p] == row[r] || row[p] != row[shift])
                                continue;
                            Move m;
                            m.word = word;
                            m.count = 4;
                            m.index = {p, q, r, shift, 0, 0, 0, 0};
                            if (i % 3 == h % 3) {
                                recordMove(m);
                                continue;
                            }
                            rectangles.push_back({min(i % 3, h % 3), max(i % 3, h % 3), j,
                                                  (i % 3 < h % 3 ? 1 : -1) * row[p], m});
                        }
                for (unsigned i = 0; i < rectangles.size(); i++)
                    for (unsigned j = 0; j < i; j++) {
                        auto &a = rectangles[i];
                        auto &b = rectangles[j];
                        if (a.j == b.j || a.a != b.a || a.b != b.b || a.orient == b.orient)
                            continue;
                        Move m = a.m;
                        m.count = 8;
                        copy_n(b.m.index.begin(), 4, m.index.begin() + 4);
                        recordMove(m);
                    }
            }
    }
    static vector<Entry> enumerate(Search &search, int word) {
        vector<Entry> out;
        Move identity;
        identity.word = word;
        out.push_back({identity, {}});
        auto recordMove = [&](Move m) {
            search.scoreMove(m);
            Entry v;
            v.move = m;
            for (size_t i = 0; i < search.shifts.size(); i++)
                v.delta[i] = search.delta[i];
            out.push_back(v);
        };
        visitMoves(search, word, recordMove);
        return out;
    }
    // Deterministic steepest descent on the full 598-shift objective.
    static void descend(Search &search, int limit) {
        for (int step = 0; step <= limit; ++step) {
            long long minimum = search.energy;
            Move choice;
            int legal = 0, ties = 0;
            auto scan = [&](const Move &move) {
                const auto cost = search.scoreMove(move);
                if (search.delta[search.shiftIndex[399]] != 0)
                    return;
                ++legal;
                if (cost == search.energy)
                    ++ties;
                if (cost < minimum) {
                    minimum = cost;
                    choice = move;
                }
            };
            for (int word = 0; word < 2; ++word)
                visitMoves(search, word, scan);
            if (minimum == search.energy || step == limit) {
                cerr << "descents=" << step << " legal=" << legal << " equal=" << ties
                     << " smallest_energy_including_current=" << minimum * 16 << '\n';
                break;
            }
            const auto cost = search.scoreMove(choice);
            search.accept(choice, cost);
            if (search.defects(search.rows) != search.residuals)
                throw runtime_error("wrong descent residual");
        }
    }
    // One simultaneous trade on each row has additive correlation changes.
    // Group by the shift-399 change and check every compatible product.
    static void pairedDescent(Search &search, int limit) {
        constexpr int shifts = 598;
        struct Candidate {
            Move move;
            long long cost;
            array<int16_t, shifts> delta;
        };
        using Groups = map<int, vector<Candidate>>;
        auto makeSide = [&](int word) {
            Groups groups;
            auto record = [&](const Move &move) {
                long long cost = search.scoreMove(move);
                auto &items = groups[search.delta[search.shiftIndex[399]]];
                Candidate candidate{move, cost, {}};
                copy_n(search.delta.begin(), shifts, candidate.delta.begin());
                items.push_back(candidate);
            };
            Move identity;
            identity.word = word;
            record(identity);
            visitMoves(search, word, record);
            return groups;
        };
        int step = 0;
        for (; step < limit; ++step) {
            auto left = makeSide(0), right = makeSide(1);
            long long best = search.energy;
            Move first, second;
            long long neighbors = 0, equal = 0, smallest = numeric_limits<long long>::max();
            for (auto &[change, group] : left) {
                auto it = right.find(-change);
                if (it == right.end())
                    continue;
                for (auto &a : group)
                    for (auto &b : it->second) {
                        if (a.move.count == 0 && b.move.count == 0)
                            continue;
                        ++neighbors;
                        int dot = 0;
                        for (int i = 0; i < shifts; ++i)
                            dot += int(a.delta[i]) * int(b.delta[i]);
                        const auto total = a.cost + b.cost - search.energy + 2 * dot;
                        smallest = min(smallest, total);
                        if (total == search.energy)
                            ++equal;
                        if (total < best) {
                            best = total;
                            first = a.move;
                            second = b.move;
                        }
                    }
            }
            if (best == search.energy) {
                cerr << "cross-word neighbors=" << neighbors << " equal=" << equal
                     << " best neighbor=" << smallest * 16 << '\n';
                break;
            }
            for (const Move *m : {&first, &second})
                for (int z = 0; z < m->count; ++z)
                    search.rows[m->word][m->index[z]] *= -1;
            search.residuals = search.defects(search.rows);
            search.energy = Search::squaredNorm(search.residuals);
            if (search.energy != best || search.residuals[search.shiftIndex[399]] != 0)
                throw runtime_error("wrong paired descent");
            search.bestRows = search.rows;
            search.bestEnergy = best;
        }
        cerr << "paired descents=" << step << " energy=" << search.energy * 16 << '\n';
    }
    // Exact two-switch changes on one row. Each interaction across the two supports
    // contributes x[p]*x[q] to the quarter-residual at their cyclic distance.
    template <class Visit>
    static bool pairs(const Search &search, const vector<Entry> &side, const uint64_t *coeff,
                      Visit visit) {
        const Row &row = search.rows[side[0].move.word];
        vector<uint64_t> singles(side.size());
        for (size_t i = 0; i < side.size(); ++i)
            for (size_t j = 0; j < search.shifts.size(); ++j)
                singles[i] += coeff[j] * uint64_t(side[i].delta[j]);
        if (visit(uint64_t(0), 0, 0))
            return true;
        for (size_t i = 1; i < side.size(); ++i) {
            array<bool, length> used{};
            array<uint64_t, length> interaction{};
            const Move &first = side[i].move;
            for (int z = 0; z < first.count; ++z) {
                int p = first.index[z];
                used[p] = true;
                for (size_t j = 0; j < search.shifts.size(); ++j) {
                    int shift = search.shifts[j];
                    for (int q : {(p + shift) % length, (p + length - shift) % length})
                        interaction[q] += coeff[j] * uint64_t(row[p] * row[q]);
                }
            }
            for (size_t j = 0; j < i; ++j) {
                const Move &second = side[j].move;
                uint64_t key = singles[i] + singles[j];
                bool overlap = false;
                for (int z = 0; z < second.count; ++z) {
                    int p = second.index[z];
                    if (used[p]) {
                        overlap = true;
                        break;
                    }
                    key += interaction[p];
                }
                if (!overlap && visit(key, i, j))
                    return true;
            }
        }
        return false;
    }

    static bool repairFour(Search &search, vector<Entry> &left, vector<Entry> &right,
                           const uint64_t *coeff) {
        if (left.size() > right.size())
            left.swap(right);
        struct Record {
            uint64_t key;
            uint32_t first, second;
        };
        vector<Record> stored;
        stored.reserve(left.size() * (left.size() - 1) / 2 + 1);
        pairs(search, left, coeff, [&](uint64_t key, uint32_t i, uint32_t j) {
            stored.push_back({key, i, j});
            return false;
        });
        sort(stored.begin(), stored.end(),
             [](const Record &a, const Record &b) { return a.key < b.key; });
        constexpr unsigned bits = 18;
        vector<size_t> slices((1U << bits) + 1, stored.size());
        size_t cursor = 0;
        for (size_t i = 0; i < stored.size(); ++i) {
            const size_t prefix = stored[i].key >> (64 - bits);
            while (cursor <= prefix)
                slices[cursor++] = i;
        }
        uint64_t goal = 0;
        for (size_t j = 0; j < search.shifts.size(); j++)
            goal -= coeff[j] * uint64_t(search.residuals[j]);
        return pairs(search, right, coeff, [&](uint64_t key, uint32_t i, uint32_t j) {
            uint64_t wanted = goal - key;
            const size_t prefix = wanted >> (64 - bits);
            auto end = stored.begin() + slices[prefix + 1];
            auto it =
                lower_bound(stored.begin() + slices[prefix], end, wanted,
                            [](const Record &entry, uint64_t value) { return entry.key < value; });
            for (; it != end && it->key == wanted; ++it) {
                Pair tested = search.bestRows;
                for (const Move *m : {&left[it->first].move, &left[it->second].move, &right[i].move,
                                      &right[j].move})
                    for (int z = 0; z < m->count; z++)
                        tested[m->word][m->index[z]] *= -1;
                if (Search::squaredNorm(search.defects(tested)) != 0)
                    continue;
                search.rows = search.bestRows = tested;
                search.residuals = search.defects(tested);
                search.energy = search.bestEnergy = 0;
                return true;
            }
            return false;
        });
    }

    static bool repair(Search &search, bool four) {
        search.rows = search.bestRows;
        search.residuals = search.defects(search.rows);
        search.energy = search.bestEnergy;
        if (search.residuals.size() > capacity)
            throw runtime_error("too many shifts for repair");
        auto left = enumerate(search, 0), right = enumerate(search, 1);
        unordered_multimap<uint64_t, int> lookup;
        for (unsigned i = 0; i < left.size(); i++)
            lookup.emplace(key(left[i].delta), i);
        for (auto &r : right) {
            Delta wanted{};
            for (size_t i = 0; i < search.shifts.size(); i++)
                wanted[i] = -search.residuals[i] - r.delta[i];
            auto [it, end] = lookup.equal_range(key(wanted));
            for (; it != end; it++) {
                auto &l = left[it->second];
                if (l.delta != wanted)
                    continue;
                for (auto *m : {&l.move, &r.move})
                    for (int k = 0; k < m->count; k++)
                        search.rows[m->word][m->index[k]] *= -1;
                search.residuals = search.defects(search.rows);
                if (Search::squaredNorm(search.residuals) != 0)
                    throw runtime_error("wrong pair repair");
                search.bestRows = search.rows;
                search.energy = search.bestEnergy = 0;
                return true;
            }
        }
        // Two switches on one row can interact. The hash only proposes moves.
        // Directly evaluate every proposed triple before accepting it.
        const uint64_t coeff[capacity] = {
            16557753173798211147ULL, 14153720793793293251ULL, 10248656616623355743ULL,
            9142077697007683791ULL,  11018064080954064191ULL, 16778934360964517299ULL,
            952796319921756201ULL,   3380898926691183881ULL,  10293487637111973881ULL,
            74211623098603479ULL,    6902370628193926713ULL,  14939391668171738861ULL,
            6201256278225611337ULL,  12888875503816779707ULL, 15534229345393296813ULL,
            8101530000954397101ULL,  15738311147693350757ULL, 5388089056701126197ULL,
            18095870052379885409ULL, 14469101022516684111ULL, 626725951732105621ULL,
            3381128858010655949ULL};
        auto dot = [&](const auto &v) {
            uint64_t x = 0;
            for (size_t i = 0; i < search.shifts.size(); i++)
                x += coeff[i] * uint64_t(v[i]);
            return x;
        };
        for (int reverseSides : {0, 1}) {
            auto &side = reverseSides ? right : left;
            auto &other = reverseSides ? left : right;
            vector<uint64_t> values;
            unordered_multimap<uint64_t, int> small;
            for (auto &e : side)
                values.push_back(dot(e.delta));
            for (unsigned i = 0; i < other.size(); i++)
                small.emplace(dot(other[i].delta), int(i));
            uint64_t target = 0 - dot(search.residuals);
            for (unsigned i = 1; i < side.size(); i++)
                for (unsigned j = 0; j < i; j++) {
                    auto [it, end] = small.equal_range(target - values[i] - values[j]);
                    for (; it != end; it++) {
                        Pair tested = search.bestRows;
                        const Move *m1 = &side[i].move, *m2 = &side[j].move,
                                   *m3 = &other[it->second].move;
                        bool disjoint = true;
                        for (int x = 0; x < m1->count; x++)
                            for (int y = 0; y < m2->count; y++)
                                if (m1->index[x] == m2->index[y])
                                    disjoint = false;
                        if (!disjoint)
                            continue;
                        for (auto m : {m1, m2, m3})
                            for (int k = 0; k < m->count; k++)
                                tested[m->word][m->index[k]] *= -1;
                        if (Search::squaredNorm(search.defects(tested)))
                            continue;
                        search.bestRows = search.rows = tested;
                        search.residuals = search.defects(search.rows);
                        search.energy = search.bestEnergy = 0;
                        return true;
                    }
                }
        }
        return four && repairFour(search, left, right, coeff);
    }
};

int main(int argc, char **argv) {
    if (argc != 4) {
        cerr << "usage: trades SEED axis|axis21|quad21|all|descent|paired|perturb STEPS < "
                "signs.txt\n";
        return 2;
    }
    const string mode = argv[2];
    const int proposals = stoi(argv[3]);
    if (proposals < 0 || (mode != "axis" && mode != "axis21" && mode != "quad21" && mode != "all" &&
                          mode != "descent" && mode != "paired" && mode != "perturb"))
        return 2;
    Search run(stoul(argv[1]));
    Pair initial;
    for (auto &r : initial)
        for (auto &x : r)
            if (!(cin >> x) || (x != 1 && x != -1))
                return 3;
    vector<int> target;
    for (int shift = 1; shift <= 598; shift++)
        if (mode == "all" || mode == "descent" || mode == "paired" || mode == "perturb" ||
            9 * shift % length == 0 || 7 * shift % length == 0 || 19 * shift % length == 0 ||
            ((mode == "axis21" || mode == "quad21") && 21 * shift % length == 0))
            target.push_back(shift);
    run.initialize(initial, target);
    if (run.residuals[run.shiftIndex[399]] != 0)
        throw runtime_error("starting signs must satisfy shift 399");
    if (mode == "perturb") {
        for (int step = 0; step < proposals;) {
            Move move;
            if (!run.proposal(move))
                continue;
            const auto cost = run.scoreMove(move);
            if (run.delta[run.shiftIndex[399]] != 0)
                continue;
            run.accept(move, cost);
            ++step;
        }
        for (const Row &row : run.rows) {
            for (int value : row)
                cout << value << ' ';
            cout << '\n';
        }
        return 0;
    }
    if (mode == "paired")
        ExactMoves::pairedDescent(run, proposals);
    else if (mode == "descent")
        ExactMoves::descend(run, proposals);
    else {
        run.run(proposals, 0.7, mode == "all" ? 140 : 6);
        if (mode != "all" && run.bestEnergy)
            ExactMoves::repair(run, mode == "quad21");
    }
    cout << "{\"score\":" << run.bestEnergy * 16 << ",\"shifts\":[";
    for (size_t i = 0; i < target.size(); i++)
        cout << (i ? "," : "") << target[i];
    cout << "],\"rows\":[";
    for (int word = 0; word < 2; word++) {
        cout << (word ? ",\"" : "\"");
        for (int x : run.bestRows[word])
            cout << (x < 0 ? '1' : '0');
        cout << '"';
    }
    cout << "]}\n";
}
