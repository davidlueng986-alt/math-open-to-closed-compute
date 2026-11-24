// Choose signs inside the triples with all 399-point sums held fixed.
#include "../hadamard-2396-diagonal/engine.hpp"
struct Phases {
    Engine signs;
    vector<int> extra;
    explicit Phases(unsigned seed, vector<int> residues) : signs(seed, true) {
        signs.load();
        for (int r : residues)
            for (int j = 0; j < 3; j++)
                extra.push_back(r + 399 * j);
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
    vector<Move> alternatives(int f) const {
        vector<Move> moves;
        for (int r = 0; r < 21; r++)
            for (int h = 0; h < 3; h++)
                for (int k = h + 1; k < 3; k++) {
                    int i = r + 21 * h, j = r + 21 * k;
                    Bits pair = (Bits(1) << i) | (Bits(1) << j);
                    for (int a = 0; a < 6; a++) {
                        if (pop(signs.s[f][a] & pair) != 1)
                            continue;
                        Move m;
                        m.f = f;
                        m.masks[a] = pair;
                        if (r % 3)
                            moves.push_back(m);
                        else
                            for (int b = a + 1; b < 6; b++) {
                                if (((signs.s[f][a] ^ signs.s[f][b]) & pair) != pair)
                                    continue;
                                m.masks[b] = pair;
                                moves.push_back(m);
                                m.masks[b] = 0;
                            }
                    }
                }
        return moves;
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
        array<vector<Move>, 2> moves{alternatives(0), alternatives(1)};
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
    for (int i = 3; i < argc; i++)
        residues.push_back(stoi(argv[i]));
    Phases p(stoul(argv[1]), residues);
    if (p.score() > 25 || !p.repair()) {
        p.anneal(stoi(argv[2]));
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
