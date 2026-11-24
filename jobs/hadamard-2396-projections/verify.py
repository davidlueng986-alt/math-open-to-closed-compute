"""Replay complete sign words, all projected correlations, and every original shift with integers."""
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
LENGTH = 1197

def words(masks):
    if len(masks) != 2:
        raise ValueError("two sign words required")
    rows = []
    for encoded in masks:
        mask = int(encoded,16)
        if not 0 <= mask < 1 << LENGTH:
            raise ValueError("mask outside the 1197 positions")
        rows.append([1-2*((mask >> i) & 1) for i in range(LENGTH)])
    return rows

def paf(rows, shift):
    return sum(x*row[(i+shift)%len(row)] for row in rows for i,x in enumerate(row))

def original(masks):
    numbers = [int(v,16) for v in masks]
    mask = (1 << LENGTH)-1
    values = []
    for s in range(1,(LENGTH+1)//2):
        differences = sum((word ^ (((word << s) & mask) | (word >> (LENGTH-s)))).bit_count()
                          for word in numbers)
        values.append(2*LENGTH-2*differences)
    return values

def check(masks, margins):
    rows = words(masks)
    if list(map(sum,rows)) != [1,1]:
        raise ValueError("wrong signs or normalization")
    for qtext, expected in margins.items():
        q = int(qtext)
        comp = [[sum(row[j::q]) for j in range(q)] for row in rows]
        if comp != expected or LENGTH % q:
            raise ValueError(f"wrong compression at {q}")
        m = LENGTH//q
        if [paf(comp,s) for s in range(q)] != [2396-2*m]+[-2*m]*(q-1):
            raise ValueError(f"nonzero projection error at {q}")
    true = original(masks)
    triples = [sum(row[j]==row[j+399]==row[j+798] for j in range(399)) for row in rows]
    if 4*sum(triples)-798 != true[398] or true[398] != -2:
        raise ValueError("shift 399 failed")
    return {"raw_energy":sum((x+2)**2 for x in true), "raw_exact_shift_pairs":true.count(-2),
            "raw_peak_error":max(abs(x+2) for x in true), "raw_paf_at_one":true[0],
            "constant_triples":triples}

if __name__ == "__main__":
    cert = json.loads((HERE/"witness.json").read_text())
    print(json.dumps(check(cert["negative_masks"],cert["projections"]), indent=2))
