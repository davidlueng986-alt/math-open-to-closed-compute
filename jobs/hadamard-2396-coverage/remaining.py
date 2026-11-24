"""Give sufficient sets of original shifts, conditioning on an explicit record's exact equations."""

from collections import Counter
import json
import sys
from coverage import GROUP, HERE
from audit_group import N, all_paf, minus

sys.path.insert(0,str(HERE.parent/"hadamard-2396-diagonal"))
from residuals import add_row


def reduction(record,law):
    plane=law=="plane"
    # The reduction by congruence mod q uses an additive quotient for both abelian laws.
    # When 9 divides q in the elementary-3 law, its length-q quotient carries that same noncyclic law.
    vals=all_paf(record["negative_masks"],plane,False)
    def label(s):
        return min(min(s*g%N,minus(s*g%N,plane)) for g in GROUP)
    labels=sorted({label(s) for s in vals})
    index={s:i for i,s in enumerate(labels)}
    err={s:v+2 for s,v in vals.items()}
    periods={s:sum(label(k)==s for k in vals) for s in labels}
    exact=[s for s in labels if err[s]==0]
    basis={}
    for s in exact:
        add_row({index[s]:1},basis)
    add_row({index[s]:w for s,w in periods.items()},basis)
    if sum(err[s]*w for s,w in periods.items())!=0:
        raise ValueError("normalized residuals must sum to zero")
    normalized_free=[s for i,s in enumerate(labels) if i not in basis]
    ranks={}
    independent=[]
    for q in (3,7,9,19,21,57,63,133,171,399):
        before=len(basis)
        for t in range(q):
            row=Counter(index[label(s)] for s in range(t,N,q) if s)
            if sum(v*err[labels[i]] for i,v in row.items())==0:
                rank=len(basis)
                add_row(row,basis)
                if len(basis)>rank:
                    independent.append([q,t])
        ranks[str(q)]=len(basis)-before
    free=[s for i,s in enumerate(labels) if i not in basis]
    if len(labels)!=94 or sum(periods.values())!=598 or sum(periods[s] for s in exact)!=record["raw_exact_pairs"]:
        raise ValueError("raw correlations and orbit classes disagree")
    return {"lag_classes":len(labels),"exact_classes":len(exact),
            "exact_class_sizes":dict(sorted(Counter(periods[s] for s in exact).items())),
            "shifts_sufficient_with_known_pairs_and_normalization":normalized_free,
            "additional_quotient_ranks":ranks,"independent_quotient_equations":independent,"shifts_sufficient_with_all_listed_quotient_zeros":free}


if __name__=="__main__":
    data=json.loads((HERE/"results.json").read_text())["witnesses"]
    report={law:{k:reduction(r,law) for k,r in records.items()} for law,records in data.items()}
    best=report["cyclic"]["coverage"]
    if best["exact_classes"]!=38 or len(best["shifts_sufficient_with_all_listed_quotient_zeros"])!=49:
        raise ValueError("the 310-pair sufficiency certificate changed")
    print(json.dumps(report,indent=2))
