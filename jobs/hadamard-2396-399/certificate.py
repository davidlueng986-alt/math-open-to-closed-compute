"""Recompute the two cloud reports, formal witness and exact remaining linear dimension."""

from collections import Counter
import json
from pathlib import Path
from audit import HERE, LENGTH, TARGET, validate
from refine import closure, extend, original
from residuals import QUOTIENTS, add_row, representative


def freedom(exact):
    labels = sorted({representative(s) for s in range(1,LENGTH)})
    index = {s:i for i,s in enumerate(labels)}
    basis = {}
    for q in QUOTIENTS:
        for t in range(q):
            add_row(Counter(index[representative(s)] for s in range(t,LENGTH,q) if s),basis)
    for s in sorted(set(exact)):
        add_row({index[representative(s)]:1},basis)
    return [s for i,s in enumerate(labels) if i not in basis]


def main():
    first = json.loads((HERE/"first-search.json").read_text())
    second = json.loads((HERE/"refinement.json").read_text())
    for r in first["witnesses"].values():
        validate(r,scalar=True)
    for r in second["witnesses"].values():
        stats = extend(r["negative_masks"],scalar=True)
        if any(r[k]!=v for k,v in stats.items()):
            raise ValueError("incorrect refinement metadata")
    r = second["witnesses"]["prefix"]
    raw = original(r["negative_masks"])
    prescribed = sorted(set(TARGET)|set(closure([2,3])))
    exact = [s for s in range(1,599) if raw[s-1]==-2]
    if len(prescribed)!=73 or len(exact)!=100 or set(prescribed)-set(exact) or raw[3]!=-50:
        raise ValueError("incorrect prescribed shifts or explicit failure")
    proof = (HERE/"Quotient399.lean").read_text()
    if any(f"def word{c} : Nat := {m}" not in proof for c,m in zip("AB",r["negative_masks"])):
        raise ValueError("Lean certificate uses different words")
    result = {"exact_pairs":len(exact),"specified_pairs":len(prescribed),"paf_at_four":raw[3],
              "free_prescribed":freedom(prescribed), "free_all_exact":freedom(exact)}
    print(json.dumps(result))


if __name__=="__main__":
    main()
