"""Seed each admissible seven-entry orientation and refine its best actual sign lifts."""

from itertools import product
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/"hadamard-2396-abelian"))
from audit_group import N, audit, original, words
from scan_groups import better, search
ENDPOINTS = json.loads((HERE.parent/"hadamard-2396-abelian/records.json").read_text())
G = ENDPOINTS["cyclic"]["group"]
ORIENTATIONS = list(product((1,-1),repeat=2))


def unpack(masks):
    rows = words(masks)
    result = []
    for row in rows:
        column = lambda x,k: row[x+63*((k-x)*16%19)]  # 63*16 = 1 mod 19
        a = [column(x,0) for x in range(63)]
        b = [column(x,1) for x in range(63)]
        c = [column(x,2) for x in range(63)]  # 2 is a quadratic nonresidue modulo 19
        result.append((a,[(u+v)//2 for u,v in zip(b,c)],[(u-v)//2 for u,v in zip(b,c)]))
    return result


def check(masks, template, scalar=False):
    stats = audit(masks,"cyclic",G,scalar)
    projected = []
    for (_,m,_),(support,negative,s) in zip(unpack(masks),template):
        expected = [s*(support>>i&1)*(1-2*(negative>>i&1)) for i in range(63)]
        if m!=expected:
            raise ValueError("actual signs violate the claimed signed support")
    for row in words(masks):
        projected.append([sum(row[i::63]) for i in range(63)])
    err0 = sum(x*x for row in projected for x in row)-2358
    energy = 2*stats["quotient_energies"]["63"]-err0**2
    return {**stats,"quotient_energy_all_shifts":energy}


def main(binaries, templates_file, shard, shards, output):
    templates = [tuple(map(int,s.split())) for s in templates_file.read_text().splitlines()]
    flags = (HERE/"orientations.hex").read_text().strip()
    if len(flags)!=len(templates) or sum(int(f,16).bit_count() for f in flags)!=8521:
        raise ValueError("incorrect template/orientation census")
    pools = {"full":[],"quotient":[]}
    direct = []
    attempted = 0
    def offer(r):
        for key,pool in pools.items():
            metric = "raw_energy" if key=="full" else "quotient_energy_all_shifts"
            if len(pool)==6 and pool[-1][metric]<=r[metric]:
                continue
            if any(v["negative_masks"]==r["negative_masks"] for v in pool):
                continue
            pool.append(r)
            pool.sort(key=lambda v:(v[metric],v["raw_energy"],v["source"]))
            del pool[6:]
    def trial(idx,j,seed,schedule,start=None):
        _,a,x,b,y,_ = templates[idx]
        sa,sb = ORIENTATIONS[j]
        pattern = [(a,x,sa),(b,y,sb)]
        lines = [" ".join(map(str,v)) for v in pattern]
        if start:
            for row,_,delta in unpack(start["negative_masks"]):
                lines+=[" ".join(map(str,row))," ".join(map(str,delta))]
        proc = subprocess.run([str(binaries/"squares"),str(seed),"signs" if start else "random",*map(str,schedule)],
                              input="\n".join(lines)+"\n",text=True,capture_output=True,check=True)
        d = json.loads(proc.stdout)
        if len(d["rows"])!=2 or any(len(row)!=N or set(row)-{"0","1"} for row in d["rows"]):
            raise ValueError("invalid original sign masks")
        masks = [hex(int(row[::-1],2)) for row in d["rows"]]
        if d["raw_energy"]!=sum((v+2)**2 for v in original(masks)):
            raise ValueError("Fourier and direct original scores disagree")
        r = {k:d[k] for k in ("raw_energy","quotient_energy_all_shifts")}
        r.update({"negative_masks":masks,"template":pattern,"template_id":idx,"orientation":j,"seed":seed,
                  "source":("warm/" if start else "fresh/")+" ".join(map(str,schedule))})
        offer(r)
        return r
    for idx in range(shard,len(templates),shards):
        for j in range(4):
            if int(flags[idx],16)>>j&1:
                seed = 300000+4*idx+j
                trial(idx,j,seed,[42000,"quotient",14000,12000,68000,"full",34000,38000])
                attempted += 1
    initial = {k:list(v) for k,v in pools.items()}
    for mode,records in initial.items():
        for j,r in enumerate(records):
            stage = [900000,mode,110000,8500 if mode=="quotient" else 18000]
            if mode=="full":
                stage += [600000,"full",150000,9000]
            trial(r["template_id"],r["orientation"],610000+30*shard+j,stage,r)
    for law in ("cyclic","plane"):
        best = ENDPOINTS[law]
        for k in range(6):
            seed = 720000+20*shard+k
            schedule = [700000,(90,140,230)[k%3],80000,-12,2+k%3,160]
            r = search(binaries/"orbits",law,G,seed,schedule,best if k%3 else ENDPOINTS[law])
            best = better(best,r)
        direct.append(best)
    winners = {k:v[0] for k,v in pools.items()}
    for r in winners.values():
        stats = check(r["negative_masks"],r["template"])
        if any(r[k]!=stats[k] for k in ("raw_energy","quotient_energy_all_shifts")):
            raise ValueError("quotient or original score disagrees")
        r.update(stats)
    output.write_text(json.dumps({"shard":shard,"shards":shards,"started_orientations":attempted,
                                 "witnesses":winners,"polished":direct},indent=2)+"\n")


if __name__ == "__main__":
    main(Path(sys.argv[1]).resolve(),Path(sys.argv[2]),int(sys.argv[3]),int(sys.argv[4]),Path(sys.argv[5]))
