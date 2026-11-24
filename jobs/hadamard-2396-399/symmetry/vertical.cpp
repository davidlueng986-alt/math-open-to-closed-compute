// Exact length-57 quotient for a cyclic pair fixed by all squares modulo 19.
// Each sign row gives three triples (X,F,D), with X=a+18M and F=a-M.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <vector>
using namespace std;
using Row = array<int, 3>;
using Key = uint64_t;
int sum(Row v) { return v[0] + v[1] + v[2]; }
int norm(Row v) { return v[0] * v[0] + v[1] * v[1] + v[2] * v[2]; }
Key pack(int x, int f, int z, int anti) {
    return Key(x) | (Key(f) << 12) | (Key(z) << 24) | (Key(anti) << 36);
}
vector<Key> enumerate(Row m, Row w) {
    vector<Key> keys;
    int z = sum(m), sumA = 1 - 18 * z, sumF = 1 - 19 * z;
    if (sumF * sumF > 2396)
        return keys;
    vector<Row> differences;
    for (int x = -11; x <= 11; x++)
        for (int y = -11; y <= 11; y++)
            for (int z = -11; z <= 11; z++) {
                Row d{x, y, z};
                bool ok = true;
                for (int i = 0; i < 3; i++)
                    if (abs(d[i]) > 21 - w[i] || (21 - w[i] - d[i]) % 2)
                        ok = false;
                if (ok && 19 * norm(d) <= 2396 && sumF * sumF + 19 * sum(d) * sum(d) <= 2396)
                    differences.push_back(d);
            }
    for (int a = -21; a <= 21; a += 2)
        for (int b = -21; b <= 21; b += 2) {
            Row sing{a, b, sumA - a - b}, X{}, F{};
            if (abs(sing[2]) > 21)
                continue;
            for (int i = 0; i < 3; i++) {
                X[i] = sing[i] + 18 * m[i];
                F[i] = sing[i] - m[i];
            }
            int nx = norm(X), nf = norm(F);
            if (nx > 1598 || nf > 2396)
                continue;
            for (Row d : differences) {
                int v = nf + 19 * norm(d);
                if (v > 2396)
                    continue;
                int skew = 0;
                for (int i = 0; i < 3; i++)
                    skew += F[i] * (d[(i + 1) % 3] - d[(i + 2) % 3]);
                keys.push_back(pack(nx, v, sumF * sumF + 19 * sum(d) * sum(d), abs(skew)));
            }
        }
    sort(keys.begin(), keys.end());
    keys.erase(unique(keys.begin(), keys.end()), keys.end());
    return keys;
}
int main() {
    int n, p;
    cin >> n >> p;
    vector<vector<Key>> keys(n);
    for (int i = 0; i < n; i++) {
        Row m{}, w{};
        for (int &v : m)
            cin >> v;
        for (int &v : w)
            cin >> v;
        keys[i] = enumerate(m, w);
    }
    for (int j = 0; j < p; j++) {
        int a, b;
        cin >> a >> b;
        if (keys[a].size() > keys[b].size())
            swap(a, b);
        bool found = false;
        for (Key v : keys[a]) {
            int x = v & 4095, f = (v >> 12) & 4095, z = (v >> 24) & 4095, skew = v >> 36;
            Key target = pack(1598 - x, 2396 - f, 2396 - z, skew);
            if (binary_search(keys[b].begin(), keys[b].end(), target)) {
                found = true;
                break;
            }
        }
        cout << found << '\n';
    }
}
