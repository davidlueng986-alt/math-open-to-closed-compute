"""Exhaustive binary-cube cover and conservative result assembly.

Status strings alone are never proof evidence. A caller must independently
check model/proof artifacts and supply the checked leaf IDs to assemble().
"""
from itertools import product


def leaves(keys):
    keys = [tuple(k) for k in keys]
    if len(set(keys)) != len(keys) or not keys:
        raise ValueError('split keys must be distinct and nonempty')
    return [{'id': ''.join(map(str, bits)),
             'cube': [{'key': list(key), 'value': bool(bit)} for key, bit in zip(keys, bits)]}
            for bits in product((0, 1), repeat=len(keys))]


def validate_cover(keys, records):
    expected = {leaf['id']: leaf['cube'] for leaf in leaves(keys)}
    if len(records) != len(expected):
        raise ValueError('missing or duplicate leaves')
    actual = {}
    for record in records:
        if any(type(item.get('value')) is not bool for item in record['cube']):
            raise ValueError('cube values must be Boolean')
        if record['id'] in actual or record['id'] not in expected:
            raise ValueError('duplicate or foreign leaf')
        if record['cube'] != expected[record['id']]:
            raise ValueError('cube does not match its branch word')
        actual[record['id']] = record['cube']
    if actual != expected:
        raise ValueError('incomplete cover')
    return True


def units(builder, leaf):
    result = []
    for literal in leaf['cube']:
        key = tuple(literal['key'])
        if key not in builder.variables or type(literal['value']) is not bool:
            raise ValueError('cube uses unknown variable or non-Boolean value')
        v = builder.variables[key]
        result.append((v if literal['value'] else -v,))
    return result


def assemble(keys, records, checked_sat=(), checked_unsat=()):
    validate_cover(keys, records)
    valid_ids = {r['id'] for r in records}
    sat, unsat = set(checked_sat), set(checked_unsat)
    if (sat | unsat) - valid_ids:
        raise ValueError('evidence from a foreign leaf')
    if sat & unsat:
        raise ValueError('inconsistent evidence')
    if sat:
        return 'SAT'
    return 'UNSAT' if unsat == valid_ids else 'OPEN'
