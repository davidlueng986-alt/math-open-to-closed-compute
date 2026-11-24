"""Independently audit every winning sign pair contributed by every shard."""

import json
from pathlib import Path
import sys

from audit import validate
from shard import key


def main(shards, out):
    winners, total = {}, 0
    for file in sorted(shards.glob("shard-*/result.json")):
        shard = json.loads(file.read_text())
        if [r["seed"] for r in shard["trials"]] != list(range(4200+7*shard["shard"],4207+7*shard["shard"])):
            raise ValueError(f"wrong seed schedule in {file}")
        total += len(shard["trials"])
        for name, r in shard["witnesses"].items():
            validate(r)
            if name not in winners or key(name,r) < key(name,winners[name]):
                winners[name] = r
    if set(winners) != {"balanced", "extended", "quotient", "full"} or winners["extended"]["target_energy"]:
        raise ValueError("missing a search objective or the extended positive control")
    report = {"trials":total, "witnesses":winners}
    (out/"results.json").write_text(json.dumps(report,indent=2)+"\n")
    print(f"{total} seeds, quotient {winners['quotient']['quotient_energy']}, full {winners['full']['raw_energy']}, extended {winners['extended']['raw_energy']}")


if __name__ == "__main__":
    main(Path(sys.argv[1]), Path(sys.argv[2]))
