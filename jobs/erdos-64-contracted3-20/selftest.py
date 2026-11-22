#!/usr/bin/env python3
"""Algebraic and exhaustive small finite-field controls for the triple sieve."""
from itertools import product
from triple_core import contradiction
def possible(forms):
    q=len(forms[0])
    for v in product(range(3),repeat=q):
        if all(sum(a*b for a,b in zip(f,v))%3!=0 for f in forms):
            return True
    return False
controls=[
  [(1,0),(0,1),(1,1),(1,2)],
  [(1,0),(0,1)],
  [(1,0),(0,1),(1,1)],
  [(1,0,0),(0,1,0),(0,0,1)],
  [(1,0,0),(0,1,0),(1,1,0),(1,-1,0)]
]
for forms in controls:
    out=contradiction(forms)[0]
    if out and possible(forms):
        raise AssertionError(f'false triple contradiction: {forms}')
assert contradiction(controls[0])[0]
assert not contradiction(controls[1])[0]
print('GF3 triple UNSAT soundness controls passed')
