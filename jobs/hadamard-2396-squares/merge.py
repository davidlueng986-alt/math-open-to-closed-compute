"""Audit the sparse signs, Fourier decomposition and every published best original pair."""

from pathlib import Path
import json
import sys
from scan import G, HERE, ORIENTATIONS, audit, better, check

def main(root, out):
    winners = {}
    polished = {}
    count = 0
    shards = set()
    flags = (HERE/"orientations.hex").read_text().strip()
    templates = [tuple(map(int,s.split())) for s in (HERE/"templates.txt").read_text().splitlines()]
    for file in sorted(root.glob("shard-*/result.json")):
        data = json.loads(file.read_text())
        n,i = data["shards"],data["shard"]
        if i in shards or file.parent.name!=f"shard-{i}":
            raise ValueError("bad shard identity")
        shards.add(i)
        expected = sum(int(s,16).bit_count() for s in flags[i::n])
        if expected!=data["started_orientations"] or set(data["witnesses"])!={"full","quotient"}:
            raise ValueError("missing searches")
        count += expected
        for key,r in data["witnesses"].items():
            idx,j = r["template_id"],r["orientation"]
            _,a,x,b,y,_ = templates[idx]
            sa,sb = ORIENTATIONS[j]
            if idx%n!=i or not (int(flags[idx],16)>>j&1) or r["template"]!=[[a,x,sa],[b,y,sb]]:
                raise ValueError("wrong template or orientation")
            got = check(r["negative_masks"],r["template"],scalar=True)
            if any(r[k]!=v for k,v in got.items()):
                raise ValueError("incorrect sparse witness")
            metric = "raw_energy" if key=="full" else "quotient_energy_all_shifts"
            if key not in winners or r[metric]<winners[key][metric]:
                winners[key]=r
        if {r["law"] for r in data["polished"]}!={"cyclic","plane"}:
            raise ValueError("missing group-law result")
        for r in data["polished"]:
            law = r["law"]
            got = audit(r["negative_masks"],law,G,scalar=True)
            if r["group"]!=G or any(r[k]!=v for k,v in got.items()):
                raise ValueError("incorrect polished witness")
            polished[law]=better(polished.get(law),r)
    if not shards:
        raise ValueError("no shards")
    result = {"shards":len(shards),"started_orientations":count,"witnesses":winners,"polished":polished}
    (out/"results.json").write_text(json.dumps(result,indent=2)+"\n")
    print(f"{count} sparse orientations, original energy {winners['full']['raw_energy']}, quotient energy {winners['quotient']['quotient_energy_all_shifts']}")


if __name__=="__main__":
    main(Path(sys.argv[1]),Path(sys.argv[2]))
