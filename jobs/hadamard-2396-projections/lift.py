"""Seek both full sign words, separating violated original equations on exact projected fibres."""
import itertools
import json
import sys
from collections import Counter
from pathlib import Path
from ortools.sat.python import cp_model as cp
from verify import HERE, LENGTH, check, original

def representative(i, multiplier):
    current = i*multiplier % LENGTH
    smallest = i
    while current != i:
        smallest = min(smallest,current)
        current = current*multiplier % LENGTH
    return smallest

class Lift:
    def __init__(self, margins, multiplier):
        self.model = cp.CpModel()
        self.rows = []
        self.free = []
        self.differences = {}
        self.shifts = {399}
        ids = [representative(i,multiplier) for i in range(LENGTH)]
        triples = []
        for f in range(2):
            variables = {k:self.model.new_bool_var("") for k in sorted(set(ids))}
            row = [variables[k] for k in ids]
            self.free.append(variables)
            self.rows.append(row)
            for qtext, pair in margins.items():
                q = int(qtext)
                for j,v in enumerate(pair[f]):
                    self.model.add(sum(row[j::q]) == (LENGTH//q+v)//2)
            for j in range(399):
                group = row[j::399]
                distinct = list({v.index:v for v in group}.values())
                if len(distinct)==1:
                    triples.append(1)
                elif len(distinct)==2:
                    triples.append(1-self.mismatch(*distinct))
                else:
                    equal = self.model.new_bool_var("")
                    self.model.add_allowed_assignments(group+[equal], [
                        (x,y,z,int(x==y==z)) for x,y,z in itertools.product((0,1),repeat=3)])
                    triples.append(equal)
        self.model.add(sum(triples)==199)

    def mismatch(self, a, b):
        key = tuple(sorted((a.index,b.index)))
        if key not in self.differences:
            value = self.model.new_bool_var("")
            self.model.add_bool_xor([a,b,value.Not()])
            self.differences[key] = value
        return self.differences[key]

    def constrain_shift(self, s):
        edges = Counter()
        for row in self.rows:
            for i,a in enumerate(row):
                b = row[(i+s)%LENGTH]
                if a.index != b.index:
                    edges[self.mismatch(a,b).index] += 1
        self.model.add(sum(w*self.model.get_bool_var_from_proto_index(i) for i,w in edges.items()) == LENGTH+1)
        self.shifts.add(s)

    def hints(self, masks):
        self.model.clear_hints()
        for variables, encoded in zip(self.free,masks):
            word = int(encoded,16)
            for k,v in variables.items():
                self.model.add_hint(v,1-((word >> k)&1))

    def solve(self, seconds, seed):
        solver = cp.CpSolver()
        solver.parameters.max_time_in_seconds = seconds
        solver.parameters.num_workers = 3
        solver.parameters.random_seed = seed
        status = solver.solve(self.model)
        if status not in (cp.OPTIMAL,cp.FEASIBLE):
            return solver.status_name(status), None
        return solver.status_name(status), [hex(sum(1 << i for i,v in enumerate(row)
                                                   if solver.value(v)==0)) for row in self.rows]

def target(values, enforced, index):
    missing = [s for s in range(1,(LENGTH+1)//2) if s not in enforced and values[s-1] != -2]
    if index%3 == 0:
        return min(missing,key=lambda s:(-abs(values[s-1]+2),s))
    if index%3 == 1:
        return min(missing,key=lambda s:(abs(values[s-1]+2),s))
    return min(missing,key=lambda s:((s*7919 + index*937)%LENGTH,s))

def run(index, seconds, rounds):
    cert = json.loads((HERE/"witness.json").read_text())
    masks, margins = cert["negative_masks"], cert["projections"]
    # 463 has components (4,1,7) modulo (9,7,19), with order three.
    multiplier = 463 if index%6==5 else 1
    engine = Lift(margins,multiplier)
    best = {"negative_masks":masks,**check(masks,margins)}
    latest = None
    log = []
    found = False
    for step in range(rounds):
        values = original(masks)
        if all(x==-2 for x in values):
            found = True
            break
        if multiplier==1 or step:
            engine.constrain_shift(target(values,engine.shifts,index+step))
            engine.hints(masks)
        status, result = engine.solve(seconds,1237+index*17+step)
        log.append({"shifts":sorted(engine.shifts),"status":status})
        if result is None:
            break
        masks = result
        stats = check(masks,margins)
        values = original(masks)
        if any(values[s-1]!=-2 for s in engine.shifts):
            raise ValueError("solver returned an invalid raw equation")
        if multiplier!=1 and any(row[i]!=row[i*multiplier%LENGTH] for row in
                                 [[(int(m,16)>>i)&1 for i in range(LENGTH)] for m in masks]
                                 for i in range(LENGTH)):
            raise ValueError("solver returned a noninvariant point")
        latest = {"negative_masks":masks,**stats}
        if stats["raw_energy"] < best["raw_energy"]:
            best = latest
        found = stats["raw_energy"]==0
        if found:
            break
    return {"multiplier":multiplier,"rounds":log,"latest":latest,"best":best,"solved":found}

if __name__ == "__main__":
    shard, seconds, rounds = map(int,sys.argv[1:4])
    Path(sys.argv[4]).write_text(json.dumps(run(shard,seconds,rounds))+"\n")
