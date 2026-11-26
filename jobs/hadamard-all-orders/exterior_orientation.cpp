#include <bit>
#include <cstdint>
#include <iostream>
#include <vector>

using Mask = unsigned __int128;

struct Equation {
    Mask positive;
    Mask negative;
};

int count(Mask mask) {
    return std::popcount(static_cast<std::uint64_t>(mask))
        + std::popcount(static_cast<std::uint64_t>(mask >> 64));
}

Mask read_mask() {
    std::uint64_t low, high;
    std::cin >> low >> high;
    return low | (static_cast<Mask>(high) << 64);
}

void enumerate(const std::vector<Equation>& equations, int limit, Mask selected, Mask remaining) {
    // The first equation balances positive and negative flips within this copy.
    const auto [positive, negative] = equations.front();
    while (true) {
        Mask select = 0, reject = 0;
        const int plus = count(positive & selected);
        const int minus = count(negative & selected);
        if (plus > limit || minus > limit) return;
        if (plus == limit) reject |= remaining & positive;
        if (minus == limit) reject |= remaining & negative;

        for (const auto [p, m] : equations) {
            const int target = count(m & selected) - count(p & selected);
            const Mask available_plus = p & remaining;
            const Mask available_minus = m & remaining;
            const int high = count(available_plus);
            const int low = -count(available_minus);
            if (target < low || target > high) return;
            if (target == low) {
                select |= available_minus;
                reject |= available_plus;
            }
            if (target == high) {
                select |= available_plus;
                reject |= available_minus;
            }
        }
        if (select & reject) return;
        if (!(select | reject)) break;
        selected |= select;
        remaining &= ~(select | reject);
    }
    if (!remaining) {
        std::cout << static_cast<std::uint64_t>(selected) << ' '
                  << static_cast<std::uint64_t>(selected >> 64) << '\n';
        return;
    }

    // Either value of this bit is explored. Use the smallest nonempty coefficient class.
    Mask candidates = remaining;
    int best = count(remaining) + 1;
    for (const auto [p, m] : equations) {
        for (Mask group : {p & remaining, m & remaining}) {
            if (group && count(group) < best) {
                candidates = group;
                best = count(group);
            }
        }
    }
    const Mask pivot = candidates & -candidates;
    enumerate(equations, limit, selected, remaining ^ pivot);
    enumerate(equations, limit, selected | pivot, remaining ^ pivot);
}

int main() {
    int width, size, limit;
    if (!(std::cin >> width >> size >> limit) || width <= 0 || width >= 128 || size < 1 || limit < 0)
        return 1;
    std::vector<Equation> equations;
    for (int i = 0; i < size; ++i) equations.push_back({read_mask(), read_mask()});
    if (!std::cin) return 1;
    enumerate(equations, limit, 0, (static_cast<Mask>(1) << width) - 1);
}
