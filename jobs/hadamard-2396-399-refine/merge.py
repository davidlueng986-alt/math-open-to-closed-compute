"""Verify all first-stage and refinement winners directly on the two sign words."""
import json
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"hadamard-2396-399"))
from refine import extend, ranking


def main(shards, out):
    best = {}
    count = 0
    for file in sorted(shards.glob("shard-*/result.json")):
        result = json.loads(file.read_text())
        shard = result["shard"]
        if result["seed_block"] != [5200+3*shard,5202+3*shard]:
            raise ValueError("incorrect seed block")
        count += 1
        for name,r in result["witnesses"].items():
            stats = extend(r["negative_masks"],True)
            if any(r.get(k) != v for k,v in stats.items()):
                raise ValueError(f"incorrect {name} certificate in {file}")
            if name not in best or ranking(name,r) < ranking(name,best[name]):
                best[name] = r
    if set(best) != {"full","balanced","quotient","extended","prefix","fibres","order133"}:
        raise ValueError("missing one or more objectives")
    (out/"results.json").write_text(json.dumps({"shards":count,"witnesses":best},indent=2)+"\n")
    print(f"{count} shards, full energy {best['full']['raw_energy']}, prefix {best['prefix']['prefix_length']}")


if __name__=="__main__":
    main(Path(sys.argv[1]),Path(sys.argv[2]))
