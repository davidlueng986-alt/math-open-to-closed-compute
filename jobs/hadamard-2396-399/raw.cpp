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
        if (mode != "fixed" && mode != "free" && mode != "balanced")
            return 2;
        engine.walk(mode, stoi(argv[i + 1]), stoi(argv[i + 2]));
    }
    engine.print();
}
