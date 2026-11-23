"""Try less symmetric supports for the fourth (trivial) Walsh component."""
import json
import random
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "hadamard-2396-fibres"))
import search as fibre

SEEDS = 4096
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
    passes_mod32 = True
    for s, common, adjacent, baseline in terms:
        shifted = ((packed << s) | (packed >> (149-s))) & GRID
        value = baseline - 8*((packed ^ shifted) & common).bit_count() - 4*(packed & adjacent).bit_count()
        if value % 16:
            raise AssertionError("affine point failed a shift congruence")
        if value % 32:
            passes_mod32 = False
        energy += value*value
        peak = max(peak,abs(value))
        misses += int(value != 0)
        # A pruned point can no longer affect either the best score or the mod-32 count.
        if energy > cutoff and not passes_mod32:
            return None, False
    return (energy, peak, misses), passes_mod32


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
    # Gray-code iteration covers every binary solution at this fixed support.
    masks = [0]*(dim+1)
    for i, form in forms.items():
        for j in fibre.bits(form):
            masks[j] |= 1 << i
    terms = correlations(occupied)
    samples = 1 << dim
    word = masks[0]
    best = None
    norm_hits = mod32_hits = exact = 0
    mod32_example = None
    cutoff = incumbent
    for n in range(samples):
        if n:
            word ^= masks[(n & -n).bit_length()]
        neg = [(word >> (149*f)) & fibre.ALL for f in range(4)]
        rows = tuple(o+2*(sz-2*u.bit_count()) for o,sz,u in zip(fibre.ORIGIN,sizes,neg))
        if rows not in targets:
            continue
        norm_hits += 1
        metric, passes_mod32 = score(neg,terms,cutoff)
        mod32_hits += int(passes_mod32)
        if metric is None:
            continue
        exact += int(metric[0]==0)
        improves = metric[0] <= cutoff and (best is None or metric < tuple(best["score"]))
        if improves or (passes_mod32 and mod32_example is None):
            certificate = {"seed":seed,"row_sums":rows,"supports":[hex(x) for x in occupied],
                           "negative":[hex(x) for x in neg],"score":metric}
            if passes_mod32 and mod32_example is None:
                mod32_example = certificate
        if improves:
            best = certificate
            cutoff = metric[0]
    return {"status":"exhausted","dim":dim,"samples":samples,"norm_hits":norm_hits,
            "mod32_hits":mod32_hits,"exact":exact,"best":best,"mod32_example":mod32_example}


def run(shard, shards):
    stats, dimensions = Counter(), Counter()
    total = valid = mod32_hits = exact = 0
    best = None
    mod32_example = None
    enumerated = []
    for seed in range(shard, SEEDS, shards):
        res = search_seed(seed, best["score"][0] if best else 10**12)
        stats[res["status"]] += 1
        if "dim" in res:
            dimensions[res["dim"]] += 1
        total += res.get("samples",0)
        valid += res.get("norm_hits",0)
        mod32_hits += res.get("mod32_hits",0)
        exact += res.get("exact",0)
        if res["status"] == "exhausted":
            enumerated.append({"seed": seed, **{key: res[key] for key in
                               ("dim", "samples", "norm_hits", "mod32_hits", "exact")}})
        if mod32_example is None:
            mod32_example = res.get("mod32_example")
        cand = res.get("best")
        if cand and (best is None or (cand["score"],cand["seed"]) < (best["score"],best["seed"])):
            best=cand
    return {"shard":shard,"shards":shards,"seed_count":len(range(shard,SEEDS,shards)),
            "statuses":stats,"consistent_dimensions":dimensions,"signings_evaluated":total,
            "norm_and_mod16":valid,"norm_and_mod32":mod32_hits,"exact_projection_signings":exact,
            "best":best,"mod32_example":mod32_example,"enumerated":enumerated}


if __name__ == "__main__":
    shard, shards = map(int,sys.argv[1:3])
    if not 0 <= shard < shards:
        raise ValueError("invalid shard")
    outdir = Path(sys.argv[3])
    outdir.mkdir(parents=True,exist_ok=True)
    (outdir/"result.json").write_text(json.dumps(run(shard,shards))+"\n")
