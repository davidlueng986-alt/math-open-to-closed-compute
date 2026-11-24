"""Check archived lifts directly and reconstruct every Fourier contribution to the full error."""

import json
from scan import ENDPOINTS, G, HERE, audit, check, unpack


def resolved_energy(masks):
    rows = unpack(masks)
    feature = [(tuple(a[i]+18*m[i] for i in range(63)),tuple(a[i]-m[i] for i in range(63)),d) for a,m,d in rows]
    scaled = 0
    for t in range(63):
        r,u,s = 38-2396*(t==0),-2396*(t==0),0
        for x,f,d in feature:
            for i in range(63):
                j = (i+t)%63
                r += x[i]*x[j]
                u += f[i]*f[j]+19*d[i]*d[j]
                s += f[i]*d[j]-d[i]*f[j]
        scaled += r*r+18*u*u+342*s*s
    energy,rem=divmod(scaled,38)
    if rem:
        raise ValueError("nonintegral original energy")
    return energy


def main():
    report=json.loads((HERE/"lifts.json").read_text())
    if report["started_orientations"]!=8521 or report["shards"]!=16:
        raise ValueError("incorrect search coverage")
    for record in report["witnesses"].values():
        got=check(record["negative_masks"],record["template"],scalar=True)
        if any(record[k]!=v for k,v in got.items()) or resolved_energy(record["negative_masks"])!=got["raw_energy"]:
            raise ValueError("incorrect seven-entry witness")
    for name,records in (("original",ENDPOINTS),("polished",report["polished"])):
        for law,r in records.items():
            got=audit(r["negative_masks"],law,G,scalar=True)
            if any(r[k]!=v for k,v in got.items()):
                raise ValueError("wrong full-energy witness")
            print(name,law,got["raw_energy"],got["raw_exact_pairs"])


if __name__=="__main__":
    main()
