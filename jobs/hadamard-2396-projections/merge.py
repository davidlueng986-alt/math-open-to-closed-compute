"""Verify every shard and retain the best directly checked full-length sign words."""
import json
import sys
from pathlib import Path
from shapes import shapes, orbit
from verify import HERE, LENGTH, check, original, paf, words

def main(source, output):
    paths = list(source.glob("shard-*/result.json"))
    margins = json.loads((HERE/"witness.json").read_text())["projections"]
    normalized = shapes()
    census, logs, witnesses = {}, [], []
    for file in paths:
        result = json.loads(file.read_text())
        shard, shards = result["shard"],result["shards"]
        if shards!=len(paths) or file.parent.name!=f"shard-{shard}":
            raise ValueError("missing or misplaced shard")
        expected = {str(i) for i in range(shard,len(normalized),shards)}
        if expected!=set(result["shapes"]):
            raise ValueError("incomplete invariant-family census")
        for i,r in result["shapes"].items():
            if not r["positive_checksum_control"] or r["hash_matches"]<r["solutions"]:
                raise ValueError("checksum control failed")
            if bool(r["solutions"])!=bool(r["first_witness"]):
                raise ValueError("inconsistent positive count")
            if r["first_witness"]:
                pair = r["first_witness"]
                if not all(len(row)==399 and all(v in (-3,-1,1,3) for v in row) for row in pair):
                    raise ValueError("invalid lift")
                if [[sum(row[j::133]) for j in range(133)] for row in pair] != [
                        [base[3*orbit(t,7)+orbit(t,19)] for t in range(133)] for base in normalized[int(i)]]:
                    raise ValueError("wrong invariant shape")
                if [paf(pair,s) for s in range(399)]!=[2390]+[-6]*398:
                    raise ValueError("invalid lifted correlations")
            census[int(i)]=r
        search=result["lift"]
        for label in ("best","latest"):
            w=search[label]
            if w is None:
                continue
            metrics=check(w["negative_masks"],margins)
            if any(w[k]!=v for k,v in metrics.items()):
                raise ValueError("invalid sign certificate")
            witnesses.append({**w,"shard":shard})
        if search["latest"] is not None:
            w=search["latest"]["negative_masks"]
            shifts=original(w)
            for step in search["rounds"]:
                if step["status"] in ("FEASIBLE","OPTIMAL") and any(shifts[s-1]!=-2 for s in step["shifts"]):
                    raise ValueError("claimed raw shift failed")
            if any(row[i]!=row[i*search["multiplier"]%LENGTH] for row in words(w) for i in range(LENGTH)):
                raise ValueError("invalid multiplier")
        logs.append({"shard":shard,"multiplier":search["multiplier"],"rounds":search["rounds"]})
    if len(census)!=len(normalized):
        raise ValueError("not every shape was tested")
    best=min(witnesses,key=lambda w:(w["raw_energy"],w["negative_masks"]))
    most=max(witnesses,key=lambda w:(w["raw_exact_shift_pairs"],-w["raw_energy"]))
    summary={"shape_count":len(census),"invariant_399_solutions":sum(r["solutions"] for r in census.values()),
             "shape_results":dict(sorted(census.items())),"full_search":sorted(logs,key=lambda x:x["shard"]),
             "best_full_energy":best,"most_exact_shifts":most}
    output.mkdir(parents=True,exist_ok=True)
    (output/"results.json").write_text(json.dumps(summary,indent=2)+"\n")
    print(f"{len(census)} shapes, {summary['invariant_399_solutions']} invariant lifts, "
          f"best original energy {best['raw_energy']}, most exact shift pairs {most['raw_exact_shift_pairs']}/598")

if __name__ == "__main__":
    main(Path(sys.argv[1]),Path(sys.argv[2]))
