"""Conservative exact-Ramsey assembly from independently checked root decisions."""


def exact_value(known_sat_order, known_unsat_order, checked_decisions):
    if known_sat_order >= known_unsat_order:
        raise ValueError('inconsistent endpoint imports')
    lower, upper = known_sat_order + 1, known_unsat_order
    for n, status in checked_decisions.items():
        if type(n) is not int or status not in ('SAT', 'UNSAT'):
            raise ValueError('only checked finite decisions are accepted')
        if status == 'SAT':
            lower = max(lower, n + 1)
        else:
            upper = min(upper, n)
    if lower > upper:
        raise ValueError('contradictory checked Ramsey evidence')
    return {'lower':lower, 'upper':upper, 'exact':lower if lower == upper else None}
