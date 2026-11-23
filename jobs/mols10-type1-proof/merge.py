import json,sys
from pathlib import Path
from search import cases,points,verify
src,dst=map(Path,sys.argv[1:]);case_map={c[0]:(c[1],c[2]) for c in cases()}
results={}
for f in sorted(src.glob("shard-*/result.json")):
    r=json.loads(f.read_text())
    assert [x["status"] for x in r["controls"]]==["SAT_VERIFIED","UNSAT_CHECKED"]
    for c in r["cases"]:
        label=c["case"];assert label in case_map and label not in results
        if c["status"]=="SAT_VERIFIED":
            assert verify(10,[tuple(p) for p in c["points"]],set(points(10,*case_map[label])))
        if c["proof_retained"]:
            assert (f.parent/f"case-{label}"/"proof.drat.gz").is_file()
        results[label]=c
checked=[k for k,v in results.items() if v["status"]=="UNSAT_CHECKED" and v["proof_retained"]]
sat=[v for v in results.values() if v["status"]=="SAT_VERIFIED"]
summary={"problem":"MOLS10-3","status":"YES_WITNESS" if sat else "OPEN","cases_expected":124,"cases_reported":len(results),"unsat_checked_with_retained_proof":len(checked),"unsat_checked_no_retained_proof":sum(v["status"]=="UNSAT_CHECKED" and not v["proof_retained"] for v in results.values()),"sat_witnesses":sat,"cases":results,"scope":"Restricted Type-1 normalization only; never claims global NO"}
(dst/"type1_summary.json").write_text(json.dumps(summary,indent=2)+"\n")
print(json.dumps({k:v for k,v in summary.items() if k not in ("cases","sat_witnesses")}))
assert len(results)==124,"incomplete case census"
