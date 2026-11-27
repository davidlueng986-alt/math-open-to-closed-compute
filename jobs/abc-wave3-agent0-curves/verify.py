from sage.all import *
import json, sys, pathlib
from sage.env import SAGE_VERSION
out=pathlib.Path(sys.argv[1]); out.mkdir(parents=True,exist_ok=True)
proof.all(True)
P=PolynomialRing(QQ,"x"); x=P.gen()
g=-6*x**6+25*x**4-36*x**2+18
f=x*x*(3-2*x)
g4=3-2*f(f)
assert g.gcd(g.derivative()) == 1
assert g.discriminant() == 35831808
assert (504*x**4-572*x**2+4)*g+(-84*x**5+212*x**3-145*x)*g.derivative()==72
assert HyperellipticCurve(g).genus()==2
assert HyperellipticCurve(g4).genus()==4
curves=[]
for label, ainvs in [("escape_quotient",[0,-2,0,9,0]),("escape_isogenous",[0,4,0,-32,0])]:
 E=EllipticCurve(QQ,ainvs)
 print("Beginning certified rank calculation",label,flush=True)
 rank=E.rank(use_database=False, only_use_mwrank=True, algorithm="mwrank_lib", proof=True, verbose=True)
 torsion=E.torsion_points()
 rec={"name":label,"ainvs":ainvs,"rank":int(rank),"rank_method":"mwrank_lib, proof=True, use_database=False","torsion":[[str(c) for c in p] for p in torsion],"discriminant":str(E.discriminant()),"conductor":int(E.conductor()),"reduction_counts":{str(p):int(E.change_ring(GF(p)).cardinality()) for p in [5,7,11]}}
 assert rank==0
 curves.append(rec)
 print(json.dumps(rec),flush=True)
E=EllipticCurve(QQ,[0,-2,0,9,0])
assert set(tuple(str(c) for c in p) for p in E.torsion_points())=={("0","1","0"),("0","0","1"),("3","6","1"),("3","-6","1")}
assert 2*E(3,6)==E(0,0)
assert E.change_ring(GF(5)).cardinality()==4
assert E.change_ring(GF(7)).cardinality()==12
mod3=[]
for u in range(3):
 for v in range(3):
  if u==v==0: continue
  vals=[(-u**4+4*u*u*v*v+32*v**4)%3,(2*u**4+4*u*u*v*v-16*v**4)%3]
  assert vals==[2,2]
  mod3.append({"u":u,"v":v,"quartic_residues":vals})
result={"status":"CHECKED","problem_resolution":"unknown","sage_version":SAGE_VERSION,"scope":"Exact genus/discriminant/Bezout identities and certified rank-zero/torsion computations for the fixed escape quotient and its 2-isogenous curve; not a global abc estimate.","genus2_polynomial":str(g),"genus2_discriminant":str(g.discriminant()),"curves":curves,"mod3_exclusions":mod3,"rational_points_consequence":"Using the written degree-two quotient map, the genus2 affine rational points are (x,y)=(+/-1,+/-1). No rational x lies strictly between0 and1."}
(out/"result.json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result,indent=2),flush=True)
