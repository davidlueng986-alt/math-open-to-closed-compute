"""Verify both original group laws independently before archiving any witness."""

import json
from pathlib import Path
import sys
from audit_group import audit, groups
from scan_groups import START, better


def main(shards, out):
    checked = {}
    attempts = 0
    seen = set()
    for file in sorted(shards.glob("shard-*/result.json")):
        report = json.loads(file.read_text())
        s = report["shard"]
        if file.parent.name != f"shard-{s}" or s in seen:
            raise ValueError("incorrect shard identity")
        seen.add(s)
        expected = [groups(9)[s%18],groups(3)[s%12],tuple(START["group"]),(1,)]
        entries = set()
        for entry in report["entries"]:
            b = entry["batch"]
            r = entry["witness"]
            law, group = r["law"], tuple(r["group"])
            if not 0 <= b < 4 or group != expected[b] or entry["attempts"] != (12,5,3,2)[b]:
                raise ValueError("incorrect group assignment or seed count")
            if (law,b) in entries:
                raise ValueError("repeated batch")
            entries.add((law,b))
            stats = audit(r["negative_masks"],law,group,scalar=True)
            if any(r[k] != v for k,v in stats.items()):
                raise ValueError(f"certificate does not reproduce in {file}")
            attempts += entry["attempts"]
            key = law,group
            checked[key] = better(checked.get(key),r)
        if entries != {(law,b) for law in ("plane","cyclic") for b in range(4)}:
            raise ValueError("incomplete batch")
    if not checked:
        raise ValueError("no shard results")
    best = {}
    for (law,group),r in sorted(checked.items()):
        for name in (law, f"{law}-{len(group)}"):
            best[name] = better(best.get(name),r)
    result = {"shards":len(seen), "attempts":attempts, "witnesses":best,
              "groups":[r for _,r in sorted(checked.items())]}
    (out/"results.json").write_text(json.dumps(result,indent=2)+"\n")
    print(f"{attempts} searches; cyclic energy {best['cyclic']['raw_energy']}, plane energy {best['plane']['raw_energy']}")


if __name__ == "__main__":
    main(Path(sys.argv[1]), Path(sys.argv[2]))
