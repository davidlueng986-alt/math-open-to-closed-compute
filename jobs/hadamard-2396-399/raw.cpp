// Optimize all original PAF equations on the two actual length-1197 sign words.
#include "../hadamard-2396-diagonal/engine.hpp"
using Distances = array<int, 206>;
struct Orbit {
    int position, dx, dy, weight;
    bool target;
};
struct Raw {
    Engine signs;
    vector<Orbit> orbits;
    array<Distances, 2> distance{};
    size_t orderThree = 0;
    explicit Raw(unsigned seed) : signs(seed, true) {
        signs.load();
        array<int, 1197> count{};
        for (int s = 1; s < 1197; s++) {
            int r = 1197;
            for (int u : {1, 106, 463})
                for (int k : {-1, 1})
                    r = min(r, (1197 + k * (u * s % 1197)) % 1197);
            count[r]++;
        }
        for (int r = 1; r < 1197; r++)
            if (count[r]) {
                bool target = 57 * r % 1197 == 0 || 63 * r % 1197 == 0;
                for (int u : {1, 64, 106})
                    if (r % 399 == u || r % 399 == 399 - u)
                        target = true;
                if (r == 399)
                    orderThree = orbits.size();
                orbits.push_back({r, r % 63, r % 19, count[r] / 2, target});
            }
        if (orbits.size() != 206)
            throw runtime_error("wrong full shift orbit count");
        rebuild();
    }
    Distances measure(int f) const {
        array<Bits, 38> rows{};
        for (int k = 0; k < 7; k++) {
            Bits word = signs.s[f][k];
            int y = columns[k];
            for (int h = 0; h < signs.weight[k]; h++) {
                rows[y] = rows[y + 19] = word;
                y = y * 7 % 19;
                word = Engine::decimate(word);
            }
        }
        Distances d{};
        for (size_t i = 0; i < orbits.size(); i++) {
            auto o = orbits[i];
            int s = 0;
            for (int y = 0; y < 19; y++) {
                Bits b = rows[y + o.dy];
                s += pop(rows[y] ^ ((b >> o.dx) | ((b << (63 - o.dx)) & mask63)));
            }
            d[i] = s;
        }
        return d;
    }
    void rebuild() {
        for (int f = 0; f < 2; f++)
            distance[f] = measure(f);
    }
    pair<int, int> energy(const Distances &a, const Distances &b) const {
        int full = 0, focus = 0;
        for (int i = 0; i < 206; i++) {
            int err = (1198 - a[i] - b[i]) / 2;
            int e = orbits[i].weight * err * err;
            full += e;
            if (orbits[i].target)
                focus += e;
        }
        return {full, focus};
    }
    void walk(const string &mode, int steps, int penalty) {
        bool fixed = mode == "fixed", balanced = mode == "balanced";
        if (balanced && distance[0][orderThree] + distance[1][orderThree] != 1198)
            throw runtime_error("balanced mode requires shift 399 at entry");
        auto objective = [&](const Distances &a, const Distances &b) {
            auto [whole, subset] = energy(a, b);
            return static_cast<long long>(whole) + static_cast<long long>(penalty) * subset;
        };
        auto curr = objective(distance[0], distance[1]), low = curr;
        State best = signs.s;
        int period = 14000;
        for (int i = 0; i < steps && low; i++) {
            if (i && i % period == 0) {
                signs.s = best;
                rebuild();
                curr = low;
            }
            Move m;
            if (fixed || signs.draw(100) < 85) {
                while (!signs.phase(m))
                    m = Move{};
            } else {
                while (!signs.transfer(m))
                    m = Move{};
            }
            signs.flip(m);
            auto next = measure(m.f);
            if (balanced && next[orderThree] + distance[1 - m.f][orderThree] != 1198) {
                signs.flip(m);
                continue;
            }
            auto val = objective(next, distance[1 - m.f]);
            double temp =
                (190.0 + (penalty ? 2.8 * penalty : 0)) * pow(0.02, double(i % period) / period);
            if (val <= curr ||
                generate_canonical<double, 52>(signs.rng) < exp(double(curr - val) / temp)) {
                curr = val;
                distance[m.f] = next;
                if (val < low) {
                    low = val;
                    best = signs.s;
                }
            } else
                signs.flip(m);
        }
        signs.s = best;
        rebuild();
    }
    struct Neighbour {
        Move move;
        array<short, 206> delta{};
        int gain = 0;
    };
    bool pairDescent(bool balanced) {
        const auto current = energy(distance[0], distance[1]).first;
        array<vector<Neighbour>, 2> neighbours;
        for (int f = 0; f < 2; f++) {
            vector<Move> list = signs.phaseMoves(f);
            auto rectangles = signs.rectangleMoves(f);
            list.insert(list.end(), rectangles.begin(), rectangles.end());
            Move identity;
            identity.f = f;
            list.push_back(identity);
            for (const auto &m : list) {
                signs.flip(m);
                auto next = measure(f);
                signs.flip(m);
                Neighbour n;
                n.move = m;
                n.gain = energy(next, distance[1 - f]).first - current;
                for (int k = 0; k < 206; k++) {
                    int d = (distance[f][k] - next[k]) / 2;
                    n.delta[k] = f ? d : orbits[k].weight * d;
                }
                neighbours[f].push_back(n);
            }
        }
        int best = 0;
        array<Move, 2> chosen;
        for (const auto &a : neighbours[0])
            for (const auto &b : neighbours[1]) {
                // Shift 399 has orbit weight one.
                if (balanced && a.delta[orderThree] + b.delta[orderThree])
                    continue;
                int cross = 0;
                for (int k = 0; k < 206; k++)
                    cross += a.delta[k] * b.delta[k];
                int gain = a.gain + b.gain + 2 * cross;
                if (gain < best) {
                    best = gain;
                    chosen = {a.move, b.move};
                }
            }
        if (!best)
            return false;
        signs.flip(chosen[0]);
        signs.flip(chosen[1]);
        rebuild();
        if (energy(distance[0], distance[1]).first != current + best)
            throw runtime_error("paired full-energy update mismatch");
        return true;
    }
    void escapes(bool balanced, int restarts, int depth) {
        if (balanced && distance[0][orderThree] + distance[1][orderThree] != 1198)
            throw runtime_error("incorrect balanced entry");
        while (pairDescent(balanced)) {
        }
        State best = signs.s;
        int low = energy(distance[0], distance[1]).first;
        for (int i = 0; i < restarts; i++) {
            signs.s = best;
            for (int j = 0; j < depth; j++) {
                Move m;
                while (!signs.phase(m))
                    m = Move{};
                signs.flip(m);
            }
            rebuild();
            while (pairDescent(balanced)) {
            }
            int e = energy(distance[0], distance[1]).first;
            if (e < low) {
                low = e;
                best = signs.s;
            }
        }
        signs.s = best;
        rebuild();
    }
    void print() {
        auto [all, focus] = energy(distance[0], distance[1]);
        auto w = signs.expand(signs.s);
        cout << "{\"raw_energy\":" << 16 * all << ",\"target_energy\":" << 16 * focus
             << ",\"rows\":[";
        for (int f = 0; f < 2; f++) {
            cout << (f ? ",\"" : "\"");
            for (int i = 0; i < 1197; i++)
                cout << ((w[f][i % 19] >> (i % 63)) & 1);
            cout << '"';
        }
        cout << "]}\n";
    }
};
int main(int argc, char **argv) {
    if (argc < 5 || argc % 3 != 2)
        return 2;
    Raw engine(stoul(argv[1]));
    for (int i = 2; i < argc; i += 3) {
        string mode = argv[i];
        if (mode == "paired" || mode == "paired-balanced") {
            engine.escapes(mode == "paired-balanced", stoi(argv[i + 1]), stoi(argv[i + 2]));
            continue;
        }
        if (mode != "fixed" && mode != "free" && mode != "balanced")
            return 2;
        engine.walk(mode, stoi(argv[i + 1]), stoi(argv[i + 2]));
    }
    engine.print();
}
