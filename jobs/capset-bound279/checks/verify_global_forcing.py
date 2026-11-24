#!/usr/bin/env python3
"""Exact final inequality; relies on separately checked eight profile exclusions."""
def verify():
    m=280;y=(425911502,-25071,94)
    bad={(109,109,62),(109,108,63),(109,107,64),(109,106,65),
         (108,108,64),(108,107,65),(108,106,66),(107,107,66)}
    rows=[(a,b,m-a-b) for a in range(110) for b in range(a+1) if 0<=m-a-b<=b]
    values={p:y[0]+y[1]*sum(x*x for x in p)+y[2]*sum(x**3 for x in p) for p in rows}
    assert len(rows)==208 and {p for p,v in values.items() if v<0}==bad
    target=(1093,364*m*m+729*m,121*m**3+729*m*m+243*m)
    score=sum(a*b for a,b in zip(target,y));assert score==-1508274
    return {'status':'PASS','excluded_size':280,'upper_bound':279,'profiles_checked':208,
            'nonnegative_remaining_profiles':200,'negative_profiles':sorted(bad),
            'polynomial_coefficients':y,'target_moments':target,'target_dot_polynomial':score}
if __name__=='__main__':
    import json
    print(json.dumps(verify(),indent=2))
