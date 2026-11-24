// Enumerate one word at a time above the fixed projected sparse row. Full integer
// autocorrelation signatures fit in four 13-bit fields at q <= 9.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <set>
#include <stdexcept>
#include <vector>
using namespace std;
using Key = uint64_t;
constexpr int offset = 2600;
struct Profiles {
    int q, d, limit;
    vector<int> spike, word, minNorm, minSum, maxSum;
    vector<Key> keys;
    explicit Profiles(vector<int> inputs)
        : q(inputs.size()), d(63 / q), limit(2396 - 2 * (1197 / q)), spike(move(inputs)), word(q),
          minNorm(q + 1), minSum(q + 1), maxSum(q + 1) {
        for (int j = q; j-- > 0;) {
            int lo = 18 * spike[j] - d, hi = 18 * spike[j] + d,
                small = lo > 0   ? lo
                        : hi < 0 ? -hi
                                 : 1;
            minNorm[j] = minNorm[j + 1] + small * small;
            minSum[j] = minSum[j + 1] + lo;
            maxSum[j] = maxSum[j + 1] + hi;
        }
    }
    void generate(int j, int sum, int norm) {
        if (norm + minNorm[j] > limit || sum + minSum[j] > 1 || sum + maxSum[j] < 1)
            return;
        if (j == q) {
            Key key = 0;
            for (int t = 1; t <= q / 2; t++) {
                int h = 0;
                for (int i = 0; i < q; i++)
                    h += word[i] * word[(i + t) % q];
                key |= Key(h + offset) << (13 * (t - 1));
            }
            keys.push_back(key);
            return;
        }
        int lo = 18 * spike[j] - d, hi = 18 * spike[j] + d;
        if (j == q - 1) {
            if (1 - sum < lo || 1 - sum > hi || (1 - sum - lo) % 2)
                return;
            lo = hi = 1 - sum;
        }
        for (int v = lo; v <= hi; v += 2) {
            word[j] = v;
            generate(j + 1, sum + v, norm + v * v);
        }
    }
};
int main() {
    int q, n, p;
    cin >> q >> n >> p;
    if (q != 3 && q != 7 && q != 9)
        return 2;
    vector<vector<Key>> signatures(n);
    for (auto &sig : signatures) {
        vector<int> spike(q);
        for (auto &v : spike)
            cin >> v;
        Profiles s(spike);
        s.generate(0, 0, 0);
        sort(s.keys.begin(), s.keys.end());
        s.keys.erase(unique(s.keys.begin(), s.keys.end()), s.keys.end());
        sig.assign(s.keys.begin(), s.keys.end());
    }
    // Diagonal follows from sum 1 and all the nonzero autocorrelations.
    for (int j = 0; j < p; j++) {
        int a, b;
        cin >> a >> b;
        if (signatures[a].size() > signatures[b].size())
            swap(a, b);
        bool hit = false;
        for (auto key : signatures[a]) {
            Key wanted = 0;
            bool valid = true;
            for (int k = 0; k < q / 2; k++) {
                int v = 2 * offset - 2 * (1197 / q) - int((key >> (13 * k)) & 8191);
                if (v < 0 || v >= 8192) {
                    valid = false;
                    break;
                }
                wanted |= Key(v) << (13 * k);
            }
            if (valid && binary_search(signatures[b].begin(), signatures[b].end(), wanted)) {
                hit = true;
                break;
            }
        }
        cout << hit << '\n';
    }
}
