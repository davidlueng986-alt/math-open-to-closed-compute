"""Independently enumerate the full-energy witness's balanced one-trade-per-word neighborhood."""

import itertools
import json
from collections import defaultdict

import numpy as np

from verify import HERE, LENGTH


def trades(word):
    coords = {(i % 9, i % 7, i % 19): i for i in range(LENGTH)}
    flips = {0}
    for k, l in itertools.combinations(range(19), 2):
        charged = defaultdict(list)
        for j in range(7):
            for a, b in itertools.combinations(range(9), 2):
                positions = [coords[i, j, t] for i in (a, b) for t in (k, l)]
                bits = tuple((word >> pos) & 1 for pos in positions)
                if bits not in ((0, 1, 1, 0), (1, 0, 0, 1)):
                    continue
                mask = sum(1 << pos for pos in positions)
                change = [0, 0, 0]
                change[a % 3] += 1 - 2*bits[0]
                change[b % 3] -= 1 - 2*bits[0]
                if not any(change):
                    flips.add(mask)
                    continue
                opposite = tuple(-v for v in change)
                for j2, other in charged[opposite]:
                    if j2 != j:
                        flips.add(mask | other)
                charged[tuple(change)].append((j, mask))
    return sorted(flips)


def original_profiles(word):
    mask = (1 << LENGTH) - 1
    groups = defaultdict(list)
    for flip in trades(word):
        x = word ^ flip
        values = [LENGTH + 1 - 2*(x ^ (((x << s) & mask) | (x >> (LENGTH-s)))).bit_count()
                  for s in range(1, 599)]
        groups[values[398]].append((flip == 0, values))
    return groups


def audit(masks, initial_energy):
    left, right = (original_profiles(int(s, 16)) for s in masks)
    size, ties, minimum = 0, 0, None
    for value, options in left.items():
        if -value not in right:
            continue
        matches = right[-value]
        b = np.array([v for _, v in matches], dtype=np.int32)
        norm_b = np.einsum("ij,ij->i", b, b, dtype=np.int64)
        for start in range(0, len(options), 64):
            group = options[start:start+64]
            a = np.array([v for _, v in group], dtype=np.int32)
            norm_a = np.einsum("ij,ij->i", a, a, dtype=np.int64)
            # 598 * 1198² < 2³¹. Promote before forming the squared norm of the sum.
            cross = np.einsum("ik,jk->ij", a, b, dtype=np.int32).astype(np.int64)
            scores = norm_a[:, None] + norm_b[None, :] + 2*cross
            size += scores.size
            if group[0][0] and matches[0][0]:
                size -= 1
                scores[0, 0] = np.iinfo(np.int64).max
            ties += int(np.count_nonzero(scores == initial_energy))
            best = int(scores.min())
            minimum = best if minimum is None else min(minimum, best)
    return {"neighbors": size, "equal_energy": ties, "minimum_neighbor_energy": minimum}


if __name__ == "__main__":
    certificate = json.loads((HERE / "original-search.json").read_text())["energy"]
    found = audit(certificate["negative_masks"], certificate["raw_energy"])
    if found != certificate["neighborhood"]:
        raise ValueError(f"neighborhood census disagrees: {found}")
    print(json.dumps(found, indent=2))
