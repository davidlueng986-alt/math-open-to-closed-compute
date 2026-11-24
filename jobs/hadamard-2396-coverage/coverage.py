"""Trace full energy and exact-shift count on the same normalized original words."""

import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/"hadamard-2396-abelian"))
from scan_groups import search
from audit_group import audit

LOW = json.loads((HERE.parent/"hadamard-2396-squares/lifts.json").read_text())["polished"]
MATCH = json.loads((HERE/"starts.json").read_text())
GROUP = LOW["cyclic"]["group"]


def key(record, goal):
    exact,energy = record["raw_exact_pairs"],record["raw_energy"]
    if goal=="energy":
        return energy,-exact
    if goal=="at_most_40000":
        return energy>40000, -exact if energy<=40000 else energy, energy
    return -exact,energy


def main(binary, shard, output):
    laws = {}
    for law_index,law in enumerate(("cyclic","plane")):
        best = {}
        def consider(r):
            for goal in ("energy","coverage","at_most_40000"):
                if goal not in best or key(r,goal)<key(best[goal],goal):
                    best[goal]=r
        consider(LOW[law])
        consider(MATCH[law])
        for k in range(9):
            seed = 1100000 + 500*shard + 100*law_index+k
            if k%3==0:
                p = (8,16,28)[k//3]
                base = best["energy"] if k!=3 else MATCH[law]
            elif k%3==1:
                p = (24,65,120)[k//3]
                base = best["at_most_40000"] if k!=4 else best["coverage"]
            else:
                p = (75,240,480)[k//3]
                base = best["coverage"]
            schedule = ["faults",p,0,500000,180+7*p,65000,-7,2+shard%4,128,
                        600000,160+3*p,90000,-9,2+k%3,176]
            found = search(binary,law,GROUP,seed,schedule,base)
            consider(found)
            # Return the coverage-improved lifts to the full 598-equation quadratic objective.
            if k%3==2:
                schedule = [850000,160+20*k,140000,-15,2+shard%4,190]
                consider(search(binary,law,GROUP,seed+30,schedule,found))
        laws[law]=best
    output.write_text(json.dumps({"shard":shard,"schedules":24,"witnesses":laws},indent=2)+"\n")


if __name__=="__main__":
    main(Path(sys.argv[1]).resolve(),int(sys.argv[2]),Path(sys.argv[3]))
