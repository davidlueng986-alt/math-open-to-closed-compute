#!/usr/bin/env python3
"""Direct SAT attempt on the exact original Erdos-Gyarfas counterexample condition.

n=41 or43; min degree3, max degree4, edges=(3n+1)//2, so exactly one
degree4 vertex and all other vertices degree3. Forbid ordinary C4/8/16/32.
SMS + Glasgow subgraph solver + CaDiCaL. A timeout is UNKNOWN.
Any SAT solution must be decoded, independently checked and then Lean formalized.
The restricted n/degree family is not the universal theorem.
"""
import json,os,sys,time,subprocess,shutil
from pathlib import Path
from pysms.graph_builder import GraphEncodingBuilder

def save_case(out,n,control=False):
    edges=(3*n+1)//2 if not control else 3*n//2
    counter="sequential"
    b=GraphEncodingBuilder(n,directed=False)
    b.minDegree(3,countertype=counter)
    b.maxDegree(4 if not control else 3,countertype=counter)
    b.numEdgesLow(edges,countertype=counter)
    b.numEdgesUpp(edges,countertype=counter)
    cnf=out/("control.cnf" if control else "target.cnf")
    with cnf.open("w") as f:b.print_dimacs(f)
    cycle_lengths=[4,8] if control else [4,8,16,32]
    sub=out/("control.cycles" if control else "target.cycles")
    sub.write_text("".join(
        f"{k} "+" ".join(f"{i} {(i+1)%k}" for i in range(k))+"\n"
        for k in cycle_lengths))
    return cnf,sub,edges,cycle_lengths

def solve(n,out,control=False,budget=18000):
    cnf,cyc,edges,lengths=save_case(out,n,control)
    exe=shutil.which("smsg") or str(Path.home()/".local/bin/smsg")
    cmd=[exe,"--vertices",str(n),"--connected","--cutoff","0",
         "--forbidden-subgraph-file",str(cyc.absolute()),
         "--dimacs",str(cnf.absolute())]
    label="positive_control" if control else "target"
    outf=out/f"{label}.stdout.log";errf=out/f"{label}.stderr.log"
    start=time.monotonic()
    with outf.open("w") as stdout,errf.open("w") as stderr:
        try:
            res=subprocess.run(cmd,stdout=stdout,stderr=stderr,timeout=budget)
            rc=res.returncode
            status={10:"SAT_UNVERIFIED",20:"UNSAT_SOLVER_REPORTED"}.get(rc,"UNKNOWN_RETURN_CODE")
        except subprocess.TimeoutExpired:
            rc=None;status="UNKNOWN_TIMEOUT"
    return {"case":label,"n":n,"edges":edges,"degrees":"3,4" if not control else "3",
            "forbidden_simple_cycle_lengths":lengths,"status":status,
            "solver_exit_code":rc,
            "elapsed_seconds":round(time.monotonic()-start,3),
            "command":cmd,
            "stdout_log":outf.name,"stderr_log":errf.name,
            "caution":"SAT candidate needs independent exact graph proof; UNSAT requires independently checkable certificate; timeouts are not exclusions."}

def main():
    shard,shards,out=int(sys.argv[1]),int(sys.argv[2]),Path(sys.argv[3])
    if shards!=2 or shard not in (0,1):raise ValueError("expected exactly two SAT shards")
    out.mkdir(parents=True,exist_ok=True)
    n=[41,43][shard]
    # Positive calibration: n24 cubic graph lacking C4 and C8 DOES exist.
    ctrl=solve(24,out,control=True,budget=300)
    if ctrl['status']!="SAT_UNVERIFIED":
        raise RuntimeError("positive SAT calibration did not find a known C4/C8-free cubic n24 graph: "+str(ctrl))
    target=solve(n,out,control=False,budget=18000)
    result={"problem":"ERDOS-64","original_status":"OPEN",
            "shard":shard,"shards":shards,"method":"SMS solver with Glasgow forbidden noninduced subgraphs",
            "target":target,"control":ctrl}
    (out/"result.json").write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"n":n,"control":ctrl["status"],"status":target["status"],
                      "seconds":target["elapsed_seconds"]}))

if __name__=="__main__":main()
