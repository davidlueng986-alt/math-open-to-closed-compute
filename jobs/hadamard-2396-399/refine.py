"""Improve the fixed-fibre, prefix, full and 399-point objectives from the first run."""

import json
from pathlib import Path
import subprocess
import sys
from audit import HERE, LENGTH, QUOTIENT, RESIDUES, TARGET, audit, key, original, representatives, sign_input, unpack

FIRST = json.loads((HERE/"first-search.json").read_text())
GROUP = (1, -1, 106, -106, 463, -463)


def canonical(s):
    return min(s, LENGTH-s)


def closure(shifts):
    return sorted({canonical(u*s % LENGTH) for s in shifts for u in GROUP})


PREFIX = sorted(set(TARGET) | set(closure(range(1, 9))))
ORDER133 = sorted(set(TARGET) | set(representatives((133,))))


def fibres(raw):
    result = {}
    for t in range(1, 200):
        if t%19 == 0 or t%21 == 0 or t != min(t*k % QUOTIENT for k in RESIDUES):
            continue
        values = [raw[canonical(t + 399*j)-1]+2 for j in range(3)]
        if sum(values) == 0:
            result[t] = sum(x*x for x in values)
    return result


def extend(masks, scalar=False):
    stats = audit(masks, scalar)
    raw = original(masks)
    def error(shifts):
        return sum((raw[s-1]+2)**2 for s in shifts)
    consecutive = next((i for i in range(598) if raw[i] != -2), 598)
    complete = sum(all(raw[canonical(t+399*j)-1] == -2 for j in range(3)) for t in range(1,200))
    return {**stats, "prefix_length":consecutive, "prefix8_energy":error(PREFIX),
            "order133_energy":error(ORDER133), "order133_exact_pairs":sum(raw[s-1] == -2 for s in ORDER133),
            "complete_399_fibres":complete}


def ranking(name, r):
    if name == "prefix":
        return (r["target_energy"] != 0, -r["prefix_length"], r["prefix8_energy"], r["raw_energy"])
    if name == "fibres":
        return (r["target_energy"] != 0, -r["complete_399_fibres"], r["raw_energy"])
    if name == "order133":
        return (r["order133_energy"], r["raw_energy"])
    return key(name,r)


def main(binaries, shard, output):
    base = FIRST["witnesses"]
    winners = {}
    def consider(m, provenance):
        r = {"negative_masks":m, **extend(m), "source":provenance}
        for name in ("full","balanced","quotient","extended","prefix","fibres","order133"):
            if name not in winners or ranking(name,r) < ranking(name,winners[name]):
                winners[name] = r
        return r
    for name,r in base.items():
        consider(r["negative_masks"],f"first/{name}")
    alt = consider(FIRST["extended_starts"][shard % 12],f"first/shard-{shard % 12}")
    def run(name, args, source):
        proc = subprocess.run([str(binaries/name), *map(str,args)],input=sign_input(source["negative_masks"]),
                              text=True, capture_output=True, check=True)
        result = json.loads(proc.stdout)
        r = consider(unpack(result), " ".join([name, *map(str,args)]))
        if any(result[k] != r[k] for k in result.keys() & r.keys()):
            raise ValueError("search and scalar quotient / packed original score disagree")
        return r
    for j in range(3):
        seed = 5200 + 3*shard + j
        run("raw",[seed,"free",1250000,0,"paired",12,7],winners["full"])
        run("raw",[seed,"balanced",950000,0,"paired-balanced",10,8],winners["balanced"])
        run("search",[seed,1500000,0],winners["quotient"])
        source = alt if j == 0 else winners["prefix"]
        for end in (2,4,6,8):
            r = run("phases",[seed+end,360000,1,f"--prefix={end}","--nearest"],source)
            if r["target_energy"] == 0:
                source = r
        candidate = alt if j != 1 else winners["extended"]
        labels = fibres(original(candidate["negative_masks"]))
        extras = [k for k in sorted(labels,key=lambda k:labels[k]) if k != 1]
        if extras:
            run("phases",[seed,600000,1,*extras[:1+j],"--nearest"],candidate)
        run("phases",[seed,600000,1,"--order133","--nearest"],candidate)
    output.write_text(json.dumps({"shard":shard,"seed_block":[5200+3*shard,5202+3*shard],
                                 "witnesses":winners},indent=2)+"\n")


if __name__=="__main__":
    main(Path(sys.argv[1]),int(sys.argv[2]),Path(sys.argv[3]))
