// Choose signs inside the triples with all 399-point sums held fixed.
#include "../hadamard-2396-diagonal/engine.hpp"
struct Phases {
    Engine signs;
    vector<int> extra;
    explicit Phases(unsigned seed, vector<int> residues, bool order133, int prefix)
        : signs(seed, true) {
        signs.load();
        for (int r : residues)
            for (int j = 0; j < 3; j++)
                extra.push_back(r + 399 * j);
        if (order133)
            for (int x : {9, 18, 27})
                for (int y : {1, 2, 4, 5, 8, 10})
                    for (int s = 0; s < 1197; s++)
                        if (s % 63 == x && s % 19 == y) {
                            extra.push_back(s);
                            break;
                        }
        auto label = [](int s) {
            int best = 1197;
            for (int u : {1, 106, 463})
                for (int k : {-1, 1})
                    best = min(best, (1197 + k * (u * s % 1197)) % 1197);
            return best;
        };
        for (int s = 1; s <= prefix; s++) {
            if (!(63 * s % 1197) || !(57 * s % 1197))
                continue;
            bool known = false;
            for (int t : extra)
                if (label(t) == label(s))
                    known = true;
            if (!known)
                extra.push_back(s);
        }
    }
    using Defect = vector<int>;
    Defect defects(const State &state) const {
        auto axis = signs.axisDefects(state);
        Defect d(axis.begin(), axis.end());
        auto all = signs.expand(state);
        for (int s : extra) {
            int shift = s % 63, total = 0;
            for (auto &word : all)
                for (int y = 0; y < 19; y++) {
                    Bits b = word[(y + s) % 19];
                    total += pop(word[y] ^ ((b >> shift) | ((b << (63 - shift)) & mask63)));
                }
            d.push_back((1198 - total) / 2);
        }
        return d;
    }
    int score() const {
        int e = 0;
        for (int v : defects(signs.s))
            e += v * v;
        return e;
    }
    void anneal(int steps) {
        int curr = score(), low = curr;
        State best = signs.s;
        for (int i = 0; i < steps && low; i++) {
            if (i && i % 7500 == 0) {
                signs.s = best;
                curr = low;
            }
            Move m;
            while (!signs.phase(m))
                m = Move{};
            signs.flip(m);
            int next = score();
            double temp = 3.0 * pow(0.045, double(i % 7500) / 7500);
            if (next <= curr ||
                generate_canonical<double, 52>(signs.rng) < exp((curr - next) / temp)) {
                curr = next;
                if (curr < low) {
                    low = curr;
                    best = signs.s;
                }
            } else
                signs.flip(m);
        }
        signs.s = best;
    }
    // Search all disjoint pairs of elementary phase moves per word. Word contributions
    // add, so nearest-neighbour search on exact integer vectors gives the best joint move.
    using Coordinates = array<short, 96>;
    struct Point {
        Coordinates delta{};
        array<int, 2> moves{-1, -1};
    };
    struct Node {
        Coordinates lo{}, hi{};
        int begin, end, left = -1, right = -1;
    };
    bool nearestRepair() {
        const State root = signs.s;
        auto before = defects(root);
        int dimensions = before.size(), bestScore = score(), old = bestScore;
        if (!old)
            return false;
        if (dimensions > 96)
            throw runtime_error("phase objective too wide");
        array<vector<Move>, 2> moves{signs.phaseMoves(0), signs.phaseMoves(1)};
        array<vector<Point>, 2> points;
        for (int f = 0; f < 2; f++) {
            auto keep = [&](int a, int b) {
                auto v = defects(signs.s);
                Point p;
                p.moves = {a, b};
                for (int k = 0; k < dimensions; k++)
                    p.delta[k] = v[k] - before[k];
                points[f].push_back(p);
            };
            keep(-1, -1);
            for (int i = 0; i < int(moves[f].size()); i++) {
                signs.flip(moves[f][i]);
                keep(i, -1);
                for (int j = i + 1; j < int(moves[f].size()); j++) {
                    bool ok = true;
                    for (int k = 0; k < 6; k++)
                        if (moves[f][i].masks[k] & moves[f][j].masks[k])
                            ok = false;
                    if (!ok)
                        continue;
                    signs.flip(moves[f][j]);
                    keep(i, j);
                    signs.flip(moves[f][j]);
                }
                signs.flip(moves[f][i]);
            }
        }
        vector<Node> tree;
        auto &pts = points[0];
        tree.reserve(pts.size());
        auto build = [&](auto &&rec, int begin, int end) -> int {
            int n = tree.size();
            tree.push_back({{}, {}, begin, end});
            auto &node = tree[n];
            node.lo = node.hi = pts[begin].delta;
            for (int i = begin + 1; i < end; i++)
                for (int k = 0; k < dimensions; k++) {
                    node.lo[k] = min(node.lo[k], pts[i].delta[k]);
                    node.hi[k] = max(node.hi[k], pts[i].delta[k]);
                }
            if (end - begin <= 16)
                return n;
            int axis = 0;
            for (int k = 1; k < dimensions; k++)
                if (node.hi[k] - node.lo[k] > node.hi[axis] - node.lo[axis])
                    axis = k;
            if (node.hi[axis] == node.lo[axis]) {
                node.end = begin + 1;
                return n;
            }
            int mid = (begin + end) / 2;
            nth_element(pts.begin() + begin, pts.begin() + mid, pts.begin() + end,
                        [axis](auto &a, auto &b) { return a.delta[axis] < b.delta[axis]; });
            int left = rec(rec, begin, mid), right = rec(rec, mid, end);
            tree[n].left = left;
            tree[n].right = right;
            return n;
        };
        build(build, 0, pts.size());
        array<array<int, 2>, 2> winner{};
        for (auto &p : points[1]) {
            Coordinates target{};
            for (int i = 0; i < dimensions; i++)
                target[i] = -before[i] - p.delta[i];
            auto bound = [&](int idx) {
                const auto &n = tree[idx];
                int result = 0;
                for (int i = 0; i < dimensions; i++) {
                    int d = max({0, n.lo[i] - target[i], target[i] - n.hi[i]});
                    result += d * d;
                }
                return result;
            };
            auto query = [&](auto &&rec, int idx) -> void {
                auto &n = tree[idx];
                if (n.left < 0) {
                    for (int j = n.begin; j < n.end; j++) {
                        int e = 0;
                        for (int i = 0; i < dimensions; i++) {
                            int a = target[i] - pts[j].delta[i];
                            e += a * a;
                        }
                        if (e < bestScore) {
                            bestScore = e;
                            winner = {pts[j].moves, p.moves};
                        }
                    }
                    return;
                }
                int a = n.left, b = n.right, da = bound(a), db = bound(b);
                if (da > db) {
                    swap(a, b);
                    swap(da, db);
                }
                if (da < bestScore)
                    rec(rec, a);
                if (db < bestScore)
                    rec(rec, b);
            };
            if (bound(0) < bestScore)
                query(query, 0);
            if (!bestScore)
                break;
        }
        if (bestScore == old)
            return false;
        for (int f = 0; f < 2; f++)
            for (int j : winner[f])
                if (j >= 0)
                    signs.flip(moves[f][j]);
        if (score() != bestScore)
            throw runtime_error("nearest phase mismatch");
        return true;
    }
    using Subset = array<int, 3>;
    bool repair() {
        if (!score())
            return true;
        const State root = signs.s;
        auto base = defects(root);
        vector<uint64_t> weights(base.size());
        mt19937_64 hashRng(196433395);
        for (auto &w : weights)
            w = hashRng();
        auto hash = [&]() {
            auto d = defects(signs.s);
            uint64_t h = 0;
            for (size_t j = 0; j < d.size(); j++)
                h += weights[j] * uint64_t(d[j]);
            return h;
        };
        uint64_t initialHash = hash();
        array<vector<Move>, 2> moves{signs.phaseMoves(0), signs.phaseMoves(1)};
        unordered_multimap<uint64_t, Subset> stored;
        for (int f = 0; f < 2; f++) {
            const auto &v = moves[f];
            int n = v.size();
            vector<uint64_t> single(n);
            vector<vector<uint64_t>> cross(n, vector<uint64_t>(n));
            vector<vector<bool>> disjoint(n, vector<bool>(n));
            for (int i = 0; i < n; i++) {
                signs.flip(v[i]);
                single[i] = hash() - initialHash;
                signs.flip(v[i]);
            }
            for (int i = 0; i < n; i++) {
                signs.flip(v[i]);
                for (int j = i + 1; j < n; j++) {
                    bool valid = true;
                    for (int k = 0; k < 6; k++)
                        if (v[i].masks[k] & v[j].masks[k])
                            valid = false;
                    disjoint[i][j] = valid;
                    if (!valid)
                        continue;
                    signs.flip(v[j]);
                    cross[i][j] = hash() - initialHash - single[i] - single[j];
                    signs.flip(v[j]);
                }
                signs.flip(v[i]);
            }
            auto test = [&](uint64_t delta, Subset subset) {
                if (f == 0) {
                    stored.emplace(delta, subset);
                    return false;
                }
                auto hits = stored.equal_range(0 - initialHash - delta);
                for (auto it = hits.first; it != hits.second; ++it) {
                    signs.s = root;
                    for (int j : it->second)
                        if (j >= 0)
                            signs.flip(moves[0][j]);
                    for (int j : subset)
                        if (j >= 0)
                            signs.flip(moves[1][j]);
                    if (score() == 0)
                        return true;
                    signs.s = root;
                }
                return false;
            };
            if (test(0, {-1, -1, -1}))
                return true;
            for (int i = 0; i < n; i++) {
                if (test(single[i], {i, -1, -1}))
                    return true;
                for (int j = i + 1; j < n; j++)
                    if (disjoint[i][j]) {
                        auto duo = single[i] + single[j] + cross[i][j];
                        if (test(duo, {i, j, -1}))
                            return true;
                        for (int k = j + 1; k < n; k++)
                            if (disjoint[i][k] && disjoint[j][k])
                                if (test(duo + single[k] + cross[i][k] + cross[j][k], {i, j, k}))
                                    return true;
                    }
            }
        }
        return false;
    }
};
int main(int argc, char **argv) {
    if (argc < 3)
        return 2;
    vector<int> residues;
    bool order133 = false, deep = false;
    int prefix = 0;
    for (int i = 3; i < argc; i++) {
        string flag = argv[i];
        if (flag == "--order133")
            order133 = true;
        else if (flag == "--nearest")
            deep = true;
        else if (flag.rfind("--prefix=", 0) == 0)
            prefix = stoi(flag.substr(9));
        else
            residues.push_back(stoi(flag));
    }
    Phases p(stoul(argv[1]), residues, order133, prefix);
    if (p.score() > 25 || !p.repair()) {
        p.anneal(stoi(argv[2]));
        p.repair();
    }
    if (deep) {
        while (p.nearestRepair()) {
        }
        p.repair();
    }
    auto rows = p.signs.expand(p.signs.s);
    cout << "{\"phase_score\":" << p.score() << ",\"rows\":[";
    for (int f = 0; f < 2; f++) {
        cout << (f ? ",\"" : "\"");
        for (int i = 0; i < 1197; i++)
            cout << ((rows[f][i % 19] >> (i % 63)) & 1);
        cout << '"';
    }
    cout << "]}\n";
}
