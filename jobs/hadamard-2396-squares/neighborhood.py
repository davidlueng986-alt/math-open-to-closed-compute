"""Reproduce the exact radius-three singleton exclusion and a planted positive control."""

import json
from math import comb
from pathlib import Path
import subprocess
import sys
from scan import HERE, unpack


def run(binary, args, data):
    return json.loads(subprocess.run([str(binary.resolve()),*map(str,args)],input=data,
                                     text=True,stdout=subprocess.PIPE,check=True).stdout)


def main(binary):
    masks=json.loads((HERE/"lifts.json").read_text())["witnesses"]["quotient"]["negative_masks"]
    split=unpack(masks)
    points=[[s+18*t for s,t in zip(a,m)] for a,m,d in split]
    data="".join(" ".join(map(str,row))+"\n" for row in points)
    local=run(binary,["descent",548,80,3],data)
    if local["quotient_energy_all_shifts"]!=7424 or local["projections"]!=points:
        raise ValueError("paired descent failed to reproduce the endpoint")
    directions=[]
    for a,_,_ in split:
        positive=a.count(1)
        directions.append(sum(comb(positive,k)*comb(63-positive,k) for k in range(4)))
    test=run(binary,["meet",2,"control"],data)
    if not test["exact"] or test["hash_matches"]<test["exact"]:
        raise ValueError("two-exchange planted control missed")
    got=run(binary,["meet",3],data)
    expected={"radius":3,"row_counts":directions,"candidates":directions[0]*directions[1],
              "hash_matches":0,"exact":0}
    if expected!=got:
        raise ValueError(f"unexpected neighborhood {got}")
    print(json.dumps(got))


if __name__=="__main__":
    main(Path(sys.argv[1]))
