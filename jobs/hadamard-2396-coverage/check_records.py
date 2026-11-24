"""Cross-check the signed cyclic and elementary-3 search records."""

import json
from coverage import GROUP, HERE, audit


def main():
    result=json.loads((HERE/"results.json").read_text())
    if (result["shards"],result["schedules"])!=(12,288):
        raise ValueError("incorrect run size")
    proof=(HERE/"Coverage.lean").read_text()
    for law,records in result["witnesses"].items():
        for goal,r in records.items():
            got=audit(r["negative_masks"],law,GROUP,scalar=True)
            if r["group"]!=GROUP or r["law"]!=law or any(r[k]!=v for k,v in got.items()):
                raise ValueError("incorrect original correlation statistics")
            if law=="cyclic" and any(f"def mask{c} : Nat := {m}" not in proof
                                    for c,m in zip("AB",r["negative_masks"])):
                raise ValueError("Lean certificate has different signs")
            print(law,goal,got["raw_energy"],got["raw_exact_pairs"])


if __name__=="__main__":
    main()
