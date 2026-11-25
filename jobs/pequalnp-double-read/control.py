"""Check the 64-gate baseline and a 65-gate double-read construction."""
import json

from synthesis import DIFF, evaluate


def incidence_circuit(double_read):
    gates = []

    def add(is_or, a, b):
        assert a != b and 0 <= min(a, b) and max(a, b) < 26 + len(gates)
        gates.append((is_or, a, b))
        return 25 + len(gates)

    terms = []
    first_term = None
    for line in range(13):
        points = [(line + offset) % 13 for offset in DIFF]
        any_point = points[0]
        for point in points[1:]:
            any_point = add(True, any_point, point)
        if line == 1 and double_read:
            # (line_1 OR A) AND (neighbors_1 OR A) = star_1 OR A.
            assert first_term is not None and 0 not in points
            left = add(True, 13 + line, first_term)
            right = add(True, any_point, first_term)
            terms[-1] = add(False, left, right)
        else:
            term = add(False, 13 + line, any_point)
            terms.append(term)
            if line == 0:
                first_term = term
    output = terms[0]
    for term in terms[1:]:
        output = add(True, output, term)
    assert output == 25 + len(gates)
    return gates


def verify(gates):
    neighborhoods = [sum(1 << ((line + offset) % 13) for offset in DIFF)
                     for line in range(13)]
    for line, neighbors in enumerate(neighborhoods):
        for point in range(13):
            mask = (1 << point) | (1 << (13 + line))
            assert evaluate(26, gates, mask)[0] == bool(neighbors >> point & 1)
    maximal_false_count = 0
    for points in range(1 << 13):
        lines = [line for line, neighbors in enumerate(neighborhoods) if not neighbors & points]
        mask = points | sum(1 << (13 + line) for line in lines)
        assert not evaluate(26, gates, mask)[0]
        blocked = 0
        for line in lines:
            blocked |= neighborhoods[line]
        maximal_false_count += (blocked | points) == (1 << 13) - 1
    return {
        'gates': len(gates), 'incidences': 52, 'false_inputs_tested': 1 << 13,
        'maximal_false_inputs': maximal_false_count,
        'mark_point_zero': evaluate(26, gates, 1 << 13, 0)[1],
        'mark_line_zero': evaluate(26, gates, 1, 13)[1],
    }


if __name__ == '__main__':
    plain = verify(incidence_circuit(False))
    doubled = verify(incidence_circuit(True))
    assert plain['gates'] == 64 and plain['mark_point_zero'] and plain['mark_line_zero']
    assert doubled['gates'] == 65 and not doubled['mark_point_zero'] and not doubled['mark_line_zero']
    print(json.dumps({'baseline': plain, 'double_read_construction': doubled}, indent=2))
