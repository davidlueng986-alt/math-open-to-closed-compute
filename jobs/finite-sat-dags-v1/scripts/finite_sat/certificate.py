"""Bounded proof-producing controls and checks bound to exact DIMACS bytes.

No routine in this module changes a research problem's status. Return records
describe precisely the tested instance. The CNF and proof remain in the bundle.
"""
import json
import subprocess
from pathlib import Path
from .core import sha256
from . import mols, moore, plane, ramsey


def read_model(stdout):
    values = []
    for line in stdout.splitlines():
        if line.startswith('v '):
            values.extend(int(x) for x in line[2:].split() if x != '0')
    seen = set(values)
    if any(-v in seen for v in values):
        raise ValueError('contradictory model')
    return values


def original_witness(builder, model, metadata, spec):
    kind = spec['kind']
    if kind == 'ramsey':
        witness = ramsey.decode(model, metadata)
        checked = ramsey.verify(witness, spec['r'], spec['s'], spec['n'])
    elif kind in ('mols', 'plane'):
        squares = mols.decode(model, metadata)
        if kind == 'mols':
            witness = squares
            checked = mols.verify(squares, spec['n'], spec['k'])
        else:
            witness = plane.from_mols(squares)
            checked = plane.validate(witness, spec['n'])
    else:
        witness = moore.decode(builder, model, spec['k'], spec.get('normalize', True))
        checked = {'valid': moore.verify(witness, spec['k']), 'k': spec['k']}
    if not checked['valid']:
        raise ValueError('original mathematical witness failed validation')
    return witness, checked


def replay_unsat(cnf, proof, cnf_sha256, proof_sha256, out_log, seconds=30):
    if sha256(cnf) != cnf_sha256 or sha256(proof) != proof_sha256:
        raise ValueError('CNF or proof hash mismatch')
    run = subprocess.run(['drat-trim', str(cnf), str(proof)],
                         capture_output=True, text=True, timeout=seconds)
    Path(out_log).write_text(run.stdout + run.stderr)
    if run.returncode != 0 or 's VERIFIED' not in run.stdout:
        raise ValueError('independent DRAT replay failed')
    return {'checker': 'drat-trim', 'returncode': run.returncode,
            'cnf_sha256': cnf_sha256, 'proof_sha256': proof_sha256}


def solve_and_check(builder, metadata, spec, out, extra=(), seconds=30):
    out = Path(out)
    out.mkdir(parents=True, exist_ok=True)
    cnf, proof = out / 'instance.cnf', out / 'proof.drat'
    extra = [tuple(x) for x in extra]
    digest = builder.write(cnf, extra)
    record = {'spec': spec, 'cnf_sha256': digest,
              'variables': builder.nvars, 'clauses': builder.nclauses + len(extra),
              'assumptions_as_units': [list(c) for c in extra], 'status': 'OPEN'}
    try:
        run = subprocess.run(['kissat', str(cnf), str(proof)],
                             capture_output=True, text=True, timeout=seconds)
        (out / 'solver.log').write_text(run.stdout + run.stderr)
        record['solver_exit_code'] = run.returncode
        if run.returncode == 10:
            model = read_model(run.stdout)
            if not builder.satisfied(model) or not all(any(x in model for x in c) for c in extra):
                raise ValueError('model fails the exact CNF or cube')
            witness, checked = original_witness(builder, model, metadata, spec)
            (out / 'witness.json').write_text(json.dumps(witness) + '\n')
            (out / 'model.json').write_text(json.dumps(model) + '\n')
            record.update(status='VERIFIED_SAT', original_check=checked,
                          witness_sha256=sha256(out / 'witness.json'))
        elif run.returncode == 20:
            proof_digest = sha256(proof)
            checked = replay_unsat(cnf, proof, digest, proof_digest, out / 'checker.log', seconds)
            record.update(status='VERIFIED_UNSAT', proof_sha256=proof_digest, proof_check=checked)
    except subprocess.TimeoutExpired:
        record['reason'] = 'bounded control timeout; no mathematical conclusion'
    (out / 'result.json').write_text(json.dumps(record, indent=2) + '\n')
    return record
