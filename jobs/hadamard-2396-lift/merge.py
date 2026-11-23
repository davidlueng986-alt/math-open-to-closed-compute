import json
import sys
from collections import Counter
from pathlib import Path

from search_lift import SEEDS, template


def replay(cert):
    u = [int(x,16) for x in cert["supports"]]
    n = [int(x,16) for x in cert["negative"]]
    if template(cert["seed"]) != u or any(v & ~s for v,s in zip(n,u)):
        raise ValueError("incorrect sign support")
    seq = [[(1 if f<3 else 2) if y==0 else 2*(((u[f]>>y)&1)-2*((n[f]>>y)&1))
            for y in range(149)] for f in range(4)]
    paf = [sum(a[y]*a[(y+s)%149] for a in seq for y in range(149)) for s in range(149)]
    half = paf[1:75]
    metric = [sum(v*v for v in half), max(map(abs,half)), sum(v!=0 for v in half)]
    if metric!=cert["score"] or paf[0]!=599 or sum(paf)!=599 or any(x%16 for x in paf[1:]):
        raise ValueError("incorrect shift certificate")
    if list(map(sum,seq))!=cert["row_sums"]:
        raise ValueError("incorrect row sums")
    return half


def main(src, out):
    paths=list(src.glob("shard-*/result.json"))
    stats, dims = Counter(),Counter()
    tested=valid=exact=0
    winners=[]
    for f in paths:
        r=json.loads(f.read_text())
        if (r["shards"]!=len(paths) or f.parent.name!=f"shard-{r['shard']}"
                or r["seed_count"]!=len(range(r["shard"],SEEDS,len(paths)))
                or sum(r["statuses"].values())!=r["seed_count"]):
            raise ValueError("incomplete seed coverage")
        stats.update(r["statuses"]); dims.update(r["consistent_dimensions"])
        tested+=r["signings_evaluated"]; valid+=r["norm_and_mod16"]; exact+=r["exact_projection_signings"]
        if r["best"]:
            replay(r["best"])
            winners.append(r["best"])
    if sum(stats.values())!=SEEDS:
        raise ValueError("missing seeds")
    best=min(winners,key=lambda c:(c["score"],c["seed"])) if winners else None
    summary={"seed_count":SEEDS,"statuses":stats,"consistent_dimensions":dims,"signings_evaluated":tested,
             "norm_and_mod16":valid,"exact_projection_signings":exact,"best":best}
    if best:
        summary["half_autocorrelations"]=replay(best)
    out.mkdir(parents=True,exist_ok=True)
    (out/"lift.json").write_text(json.dumps(summary,indent=2)+"\n")
    print(f"seeds={SEEDS}, signings={tested}, norm+mod16={valid}, exact={exact}, best={best['score'] if best else None}")


if __name__=="__main__":
    main(Path(sys.argv[1]),Path(sys.argv[2]))
