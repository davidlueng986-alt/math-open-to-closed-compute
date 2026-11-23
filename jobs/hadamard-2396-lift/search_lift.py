"""Try less symmetric supports for the fourth (trivial) Walsh component."""
import json
import random
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "hadamard-2396-fibres"))
import search as fibre

SEEDS = 4096
MAX_FREE = 18
STRIDE = 2*fibre.P
GRID = sum(fibre.ALL << (STRIDE*f) for f in range(4))


def template(seed):
    rng = random.Random(seed)
    p = fibre.P
    full4 = sum(1 << y for y in rng.sample(range(1,p), 32)) | 1
    # Where no spike row has neighbors, require even combined overlap at the shift.
    # For a symmetric support its overlap parity at s equals its membership at s/2.
    eligible = [s for s in range(1,75) if (full4 & fibre.shift(full4,s)).bit_count() % 2]
    for _ in range(128):
        rng.shuffle(eligible)
        unused = set()
        for s in eligible:
            twice, half = 2*s % p, 75*s % p
            if min(twice,p-twice) not in unused and min(half,p-half) not in unused:
                unused.add(s)
                if len(unused) == 16:
                    break
        if len(unused) == 16:
            break
    else:
        return None
    used = sorted(set(range(1,75))-unused)
    rng.shuffle(used)
    occupied = [sum((1 << y) | (1 << (p-y)) for y in points)
                for points in (used[:18], used[18:36], used[36:])]
    return occupied + [full4 ^ 1]


def correlations(occupied):
    full = sum((u | int(f==3)) << (STRIDE*f) for f,u in enumerate(occupied))
    terms = []
    for s in range(1,75):
        aligned = ((full << s) | (full >> (149-s))) & GRID
        common = full & aligned
        opp = (1 << s) | (1 << (149-s))
        adjacent = sum((occupied[f] & opp) << (STRIDE*f) for f in range(3))
        baseline = 4*common.bit_count() + 2*adjacent.bit_count()
        terms.append((s,common,adjacent,baseline))
    return terms


def score(negative, terms, cutoff):
    packed = sum(u << (STRIDE*f) for f,u in enumerate(negative))
    energy, peak, misses = 0, 0, 0
    for s, common, adjacent, baseline in terms:
        shifted = ((packed << s) | (packed >> (149-s))) & GRID
        value = baseline - 8*((packed ^ shifted) & common).bit_count() - 4*(packed & adjacent).bit_count()
        if value % 16:
            raise AssertionError("affine point failed a shift congruence")
        energy += value*value
        peak = max(peak,abs(value))
        misses += int(value != 0)
        if energy > cutoff:
            return None
    return (energy,peak,misses)


def search_seed(seed, incumbent):
    occupied = template(seed)
    if occupied is None:
        return {"status":"no_template"}
    pivots = fibre.shift_system(occupied)
    if pivots is None:
        return {"status":"inconsistent"}
    forms, dim = fibre.affine_forms(occupied, pivots)
    sizes = tuple(u.bit_count() for u in occupied)
    targets = set(fibre.compatible_norms(forms, fibre.norm_targets(sizes)))
    if not targets:
        return {"status":"norm_rejected","dim":dim}
    # Vary the lowest MAX_FREE affine coordinates and fix any higher coordinates to zero.
    masks = [0]*(dim+1)
    for i, form in forms.items():
        for j in fibre.bits(form):
            masks[j] |= 1 << i
    terms = correlations(occupied)
    samples = 1 << min(dim,MAX_FREE)
    word = masks[0]
    best = None
    norm_hits = exact = 0
    cutoff = incumbent
    for n in range(samples):
        if n:
            word ^= masks[(n & -n).bit_length()]
        neg = [(word >> (149*f)) & fibre.ALL for f in range(4)]
        rows = tuple(o+2*(sz-2*u.bit_count()) for o,sz,u in zip(fibre.ORIGIN,sizes,neg))
        if rows not in targets:
            continue
        norm_hits += 1
        metric = score(neg,terms,cutoff)
        if metric is None:
            continue
        exact += int(metric[0]==0)
        if best is None or metric < tuple(best["score"]):
            best = {"seed":seed,"row_sums":rows,"supports":[hex(x) for x in occupied],
                    "negative":[hex(x) for x in neg],"score":metric}
            cutoff = metric[0]
    return {"status":"capped" if dim>MAX_FREE else "exhausted","dim":dim,"samples":samples,
            "norm_hits":norm_hits,"exact":exact,"best":best}


def run(shard, shards):
    stats, dimensions = Counter(), Counter()
    total = valid = exact = 0
    best = None
    for seed in range(shard, SEEDS, shards):
        res = search_seed(seed, best["score"][0] if best else 10**12)
        stats[res["status"]] += 1
        if "dim" in res:
            dimensions[res["dim"]] += 1
        total += res.get("samples",0)
        valid += res.get("norm_hits",0)
        exact += res.get("exact",0)
        cand = res.get("best")
        if cand and (best is None or (cand["score"],cand["seed"]) < (best["score"],best["seed"])):
            best=cand
    return {"shard":shard,"shards":shards,"seed_count":len(range(shard,SEEDS,shards)),
            "statuses":stats,"consistent_dimensions":dimensions,"signings_evaluated":total,
            "norm_and_mod16":valid,"exact_projection_signings":exact,"best":best}


if __name__ == "__main__":
    shard, shards = map(int,sys.argv[1:3])
    if not 0 <= shard < shards:
        raise ValueError("invalid shard")
    outdir = Path(sys.argv[3])
    outdir.mkdir(parents=True,exist_ok=True)
    (outdir/"result.json").write_text(json.dumps(run(shard,shards))+"\n")
