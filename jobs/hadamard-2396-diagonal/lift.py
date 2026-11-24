"""Construct a symmetric binary lift of the three archived margins with CP-SAT."""

import argparse
from itertools import product
import json

from ortools.sat.python import cp_model
from check import LENGTH, SEED, evaluate, words


def lift(seconds):
    model = cp_model.CpModel()
    representatives = [min(i, 463*i % LENGTH, 463**2*i % LENGTH) for i in range(LENGTH)]
    rows, constants = [], []
    for word, seed in enumerate(words(SEED["negative_masks"])):
        variables = {i: model.new_bool_var("") for i in sorted(set(representatives))}
        row = [variables[i] for i in representatives]
        rows.append(row)
        # Only the singleton column's 63 signs are prescribed from the seed.
        for i in range(0, LENGTH, 19):
            model.add(row[i] == int(seed[i] == 1))
        for q, pair in SEED["projections"].items():
            q = int(q)
            for j, value in enumerate(pair[word]):
                model.add(sum(row[j::q]) == (LENGTH//q + value)//2)
        indicators = {}
        for j in range(399):
            indices = tuple(sorted({v.index for v in row[j::399]}))
            if len(indices) == 1:
                constants.append(1)
                continue
            if indices not in indicators:
                bits = [model.get_bool_var_from_proto_index(k) for k in indices]
                flag = model.new_bool_var("")
                model.add_allowed_assignments(bits + [flag], [
                    (*p, int(len(set(p)) == 1)) for p in product((0, 1), repeat=len(bits))
                ])
                indicators[indices] = flag
            constants.append(indicators[indices])
    model.add(sum(constants) == 199)
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = seconds
    solver.parameters.random_seed = 674
    solver.parameters.num_workers = 2
    status = solver.solve(model)
    if status not in (cp_model.FEASIBLE, cp_model.OPTIMAL):
        raise SystemExit(f"CP-SAT returned {solver.status_name(status)}")
    masks = [hex(sum(1 << i for i, v in enumerate(row) if not solver.value(v))) for row in rows]
    stats = evaluate(masks, "both", scalar=True)
    if sum(stats["constant_triples"]) != 199:
        raise ValueError("invalid singleton lift")
    print(json.dumps({"negative_masks": masks, **stats}, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seconds", type=float, default=30)
    lift(parser.parse_args().seconds)
