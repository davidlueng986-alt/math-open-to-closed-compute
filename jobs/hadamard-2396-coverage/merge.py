"""Verify each shard's complete words under the actual abelian group law."""

from pathlib import Path
import json
import sys
from coverage import GROUP, audit, key


def collect(root,out):
    winners={}
    seen=set()
    for file in sorted(root.glob("shard-*/result.json")):
        data=json.loads(file.read_text())
        shard=data["shard"]
        if file.parent.name!=f"shard-{shard}" or shard in seen or data["schedules"]!=24:
            raise ValueError("invalid search count or shard id")
        seen.add(shard)
        if set(data["witnesses"])!={"cyclic","plane"}:
            raise ValueError("missing group")
        for law,records in data["witnesses"].items():
            best=winners.setdefault(law,{})
            if set(records)!={"coverage","energy","at_most_40000"}:
                raise ValueError("missing objective")
            for goal,r in records.items():
                stats=audit(r["negative_masks"],law,GROUP,scalar=True)
                if r["law"]!=law or r["group"]!=GROUP or any(r[k]!=v for k,v in stats.items()):
                    raise ValueError("incorrect original signs or metrics")
                if goal not in best or key(r,goal)<key(best[goal],goal):
                    best[goal]=r
    if not seen:
        raise ValueError("no shards")
    d={"shards":len(seen),"schedules":24*len(seen),"witnesses":winners}
    (out/"results.json").write_text(json.dumps(d,indent=2)+"\n")
    for law,v in winners.items():
        print(law,v["energy"]["raw_energy"],v["coverage"]["raw_exact_pairs"])


if __name__=="__main__":
    collect(Path(sys.argv[1]),Path(sys.argv[2]))
