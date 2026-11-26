#include <algorithm>
#include <array>
#include <iostream>
#include <numeric>
#include <set>
#include <vector>

constexpr int n = 299;
using Word = std::array<int, n>;

int power(int root, int exponent, int modulus) {
    int out = 1;
    while (exponent) {
        if (exponent & 1) out = out * root % modulus;
        root = root * root % modulus;
        exponent >>= 1;
    }
    return out;
}

int character(int value) {
    value = (value + 1198) % 599;
    if (!value) return 0;
    return power(value, 299, 599) == 1 ? 1 : -1;
}

std::vector<int> orbit(int i) {
    std::vector<int> points = {i};
    for (int j = 2*i % n; j != i; j = 2*j % n) points.push_back(j);
    return points;
}

std::vector<Word> cells(const Word& support, const std::vector<int>& points, bool self) {
    std::set<Word> distinct;
    const int length = points.size();
    for (const int sign: {1,-1}) for (int complement = 0; complement <= !self; ++complement)
        for (int k = 0; k < length; ++k) {
            Word d = {};
            for (int j = 0; j < length; ++j) {
                const int a = points[j], b = points[(k+sign*j+length)%length];
                d[a] = support[b] ^ complement;
                d[n-a] = 1 - d[a];
            }
            distinct.insert(d);
        }
    return {distinct.begin(), distinct.end()};
}

bool exact(const Word& a) {
    for (int d = 1; d <= n/2; ++d) {
        int correlation = 0;
        for (int i = 0; i < n-d; ++i) correlation += a[i]*a[i+d];
        for (int i = n-d; i < n; ++i) correlation += a[i]*a[i+d-n];
        if (2*correlation != -1-a[d]-a[n-d]) return false;
    }
    return true;
}

std::vector<Word> orientations(const std::vector<int>& representatives) {
    std::vector<Word> deck(1 << representatives.size());
    for (int mask = 0; mask < static_cast<int>(deck.size()); ++mask) {
        for (int bit = 0; bit < static_cast<int>(representatives.size()); ++bit) {
            const int a = representatives[bit];
            deck[mask][a] = (mask >> bit) & 1;
            deck[mask][n-a] = 1-deck[mask][a];
        }
    }
    return deck;
}

int main(int argc, char**) {
    Word support = {}, original = {};
    for (int j = 1; j < n; ++j) {
        const int u = power(2,j,599);
        original[j] = -(character(u-1)+character(-u-1))/2;
        support[j] = original[j] != 0;
    }
    if (!exact(original)) return 1;
    const auto primitive = orbit(1);
    auto p = cells(support, primitive, false);
    auto q = cells(support, orbit(13), false);
    auto r = cells(support, orbit(23), true);
    if (argc > 1) {
        p.clear();
        // Global multiplication by 2 is a symmetry and balances all axes. With
        // the short orientations unrestricted, normalize the long rotation to 0.
        for (int sign: {1,-1}) for (int complement: {0,1}) {
            Word d = {};
            for (int j = 0; j < static_cast<int>(primitive.size()); ++j) {
                const int a = primitive[j], b = primitive[(132+sign*j)%132];
                d[a] = support[b] ^ complement;
                d[n-a] = 1-d[a];
            }
            p.push_back(d);
        }
        q = orientations(orbit(13));
        auto half = orbit(23);
        half.resize(6);
        r = orientations(half);
    }
    std::set<Word> known;
    for (int u = 1; u < n; ++u) if (std::gcd(u,n) == 1) {
        Word a;
        for (int j = 0; j < n; ++j) a[u*j%n] = original[j];
        known.insert(a);
    }
    int passes = 0, novel = 0;
    for (const auto& x:p) for (const auto& y:q) for (const auto& z:r) {
        Word a, v;
        for (int j = 0; j < n; ++j) v[j] = x[j]+y[j]+z[j];
        for (int j = 0; j < n; ++j) a[j] = v[j]*(2*v[((n+1)/2)*j%n]-1);
        if (exact(a)) {
            ++passes;
            if (!known.contains(a)) {
                ++novel;
                std::cout << "novel ";
                for (auto d:a) std::cout << d+1;
                std::cout << '\n';
            }
        }
    }
    std::cout << "support decks " << p.size() << ' ' << q.size() << ' ' << r.size()
              << " exact " << passes << " known variants " << known.size()
              << " novel " << novel << '\n';
}
