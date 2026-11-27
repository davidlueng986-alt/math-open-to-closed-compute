#!/usr/bin/env python3
import hashlib,json,os,re,sys
from pathlib import Path

source=Path(sys.argv[1]);out=Path(sys.argv[2]);text=source.read_text();log=(out/'kernel.log').read_text()
assert not re.search(r'\b(sorry|admit|native_decide)\b',text)
assert not re.search(r'^\s*(axiom|unsafe)\b',text,re.M)
assert 'sorryAx' not in log
expected=re.findall(r'^#print axioms (ABCWave1\.\w+)',text,re.M)
assert len(expected)==22 and len(set(expected))==22
allowed={'propext','Classical.choice','Quot.sound'}
found={}
for name,body in re.findall(r"'?(ABCWave1\.\w+)'? depends on axioms:\s*\[([^\]]*)\]",log,re.S):
    axioms=[s.strip() for s in body.split(',') if s.strip()]
    assert set(axioms)<=allowed,(name,axioms)
    found[name]=axioms
for name in re.findall(r"'?(ABCWave1\.\w+)'? does not depend on any axioms",log):
    found[name]=[]
assert set(found)==set(expected),{'missing':sorted(set(expected)-set(found)),'extra':sorted(set(found)-set(expected)),'log':log}
assert (out/'Structural.olean').is_file()
result={'agent':6,'status':'LEAN_VERIFIED','problem_resolution':'unknown','lean_version':(out/'lean-version.txt').read_text().strip(),'mathlib_commit':(out/'mathlib-commit.txt').read_text().strip(),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'kernel_log_sha256':hashlib.sha256((out/'kernel.log').read_bytes()).hexdigest(),'theorem_count':len(found),'axioms':found,'github_run_id':os.getenv('GITHUB_RUN_ID'),'github_sha':os.getenv('GITHUB_SHA'),'scope':'22 exact algebraic, arithmetic, inequality and quantifier lemmas only. No proof of conductor/minimality, full abc equivalence, new abc bound, IUT premise or infinite counterexample sequence. The balanced lemma assumes a*b*c<=R^3*U; it does not silently identify arbitrary R with the radical. Reyssat integer quality comparison uses a separately certified radical value.'}
(out/'result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
