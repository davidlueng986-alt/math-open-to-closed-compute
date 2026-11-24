#!/usr/bin/env python3
"""Functional checks for preinstalled computation and proof-checking tools."""
import shutil
import subprocess
import tempfile
from pathlib import Path

import cvc5
import gmpy2
import igraph
import scipy.sparse
import sympy
import z3
from flint import fmpz
from ortools.sat.python import cp_model
from pysat.solvers import Cadical195

assert sympy.factorint(360) == {2: 3, 3: 2, 5: 1}
assert gmpy2.is_prime(101)
assert int(fmpz(2) ** 100) == 2 ** 100
assert scipy.sparse.eye(3).shape == (3, 3)
assert igraph.Graph.Ring(3).ecount() == 3

model = cp_model.CpModel()
x = model.NewIntVar(0, 10, "x")
model.Add(x == 7)
solver = cp_model.CpSolver()
assert solver.Solve(model) in (cp_model.OPTIMAL, cp_model.FEASIBLE)
assert solver.Value(x) == 7

solver = z3.Solver()
y = z3.Int("y")
solver.add(y > 0, y < 0)
assert solver.check() == z3.unsat

solver = cvc5.Solver()
solver.assertFormula(solver.mkFalse())
assert solver.checkSat().isUnsat()

with Cadical195(bootstrap_with=[[1], [-1]]) as solver:
    assert not solver.solve()

with tempfile.TemporaryDirectory() as tmp:
    root = Path(tmp)
    sat = root / "sat.cnf"
    unsat = root / "unsat.cnf"
    proof = root / "proof.drat"
    sat.write_text("p cnf 1 1\n1 0\n")
    unsat.write_text("p cnf 1 2\n1 0\n-1 0\n")
    proof.write_text("0\n")
    for program in ("kissat", "cryptominisat5"):
        for cnf, expected in ((sat, 10), (unsat, 20)):
            result = subprocess.run([program, str(cnf)], capture_output=True, text=True)
            assert result.returncode == expected, (program, result.returncode, result.stderr)
    result = subprocess.run(
        ["drat-trim", str(unsat), str(proof)], capture_output=True, text=True
    )
    assert result.returncode == 0 and "VERIFIED" in result.stdout, result.stdout + result.stderr

result = subprocess.run(["gp", "-fq"], input="print(isprime(101))\n", capture_output=True, text=True)
assert result.returncode == 0 and result.stdout.strip() == "1", result.stderr
assert shutil.which("bliss") and shutil.which("lrat-check")
print("Math toolbox checks passed.")
