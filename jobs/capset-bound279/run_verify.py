#!/usr/bin/env python3
"""Portable exact reproduction of 236 <= r_3(7) <= 279.

Requires Python >=3.10 and g++ with C++17 / signed __int128. No optimizer,
network access, or previous result files are used as evidence. The imported
classification theorems are explicitly listed in README.md and PROOF.md.
"""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time

ROOT=Path(__file__).resolve().parent
CERTS=ROOT/'certificates'
sys.path.insert(0,str(ROOT/'checks'))
from profile_data import PROFILES
from verify_foundations import verify as verify_foundations
from verify_global_forcing import verify as verify_global_forcing
M=280
P=[(109,109,62),(109,108,63),(109,107,64),(109,106,65),
   (108,108,64),(108,107,65),(108,106,66),(107,107,66)]
MODES=['rank0',*[f'rank1_kernel{i}' for i in range(4)],'rank2']
CONTEXTS={108:{tuple(sorted(p)) for p in [P[1],P[4],P[5],P[6]]},
          107:{tuple(sorted(P[7]))}}
HIGH_EXPECTED={(a,k,b,M-a-b) for a in (110,111,112)
 for k in (('ordinary','antipodal') if a==110 else ('single',))
 for b in range((M-a+1)//2,110)}
DOUBLE_EXPECTED={(a,k,b,M-a-b) for a in (110,111,112)
 for k in (('ordinary','antipodal') if a==110 else ('single',))
 for b in range(110,a+1)}
assert len(HIGH_EXPECTED)==101 and len(DOUBLE_EXPECTED)==7


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def load(path):return json.loads(path.read_text())
def m2(n):return 121*n*n+243*n
def m3(n):return 40*n**3+243*n*n+81*n
def ordinary_target(a,b,c):return [364,m2(a),m3(a),m2(b),m3(b),m2(c),m3(c),121*a*b*c]
def ints(ys):
    assert all(type(x) is int and abs(x)<2**63 for x in ys)
    # Every coordinate in a grid or target is below 10^9. This bounds every
    # intermediate dot product for the two small unchecked __int128 checkers.
    assert sum(map(abs,ys))*10**9<2**120
    return ' '.join(map(str,ys))
def run_json(command,stdin=None):
    p=subprocess.run(list(map(str,command)),input=stdin,text=True,capture_output=True)
    if p.returncode:
        raise RuntimeError(f'Checker failed ({p.returncode}): {Path(str(command[0])).name}\n{p.stdout}\n{p.stderr}')
    return json.loads(p.stdout)
def marker(name,**kw):print(json.dumps({'stage':name,**kw}),flush=True)


def checksum_inputs():
    manifest=load(ROOT/'SHA256SUMS.json')
    for name,digest in manifest['files'].items():
        path=ROOT/name
        assert path.is_file() and sha(path)==digest,('sha256 mismatch',name)
    certfiles={str(p.relative_to(ROOT)) for p in CERTS.rglob('*.json')}
    assert len(certfiles)==242 and certfiles=={n for n in manifest['files'] if n.startswith('certificates/')}
    return {'status':'PASS','pinned_files':len(manifest['files']),'manifest_sha256':sha(ROOT/'SHA256SUMS.json')}


def compile_all(work,cxx,workers):
    names=['double','high','completed109','completed_small','generic','centroids','five_holes','cross_section']
    def one(name):
        dest=work/name
        # Never define NDEBUG: assertions are proof acceptance conditions.
        subprocess.run([cxx,'-O3','-std=c++17',str(ROOT/'cpp'/f'{name}.cpp'),'-o',str(dest)],check=True,capture_output=True)
        return name
    with ThreadPoolExecutor(max_workers=workers) as pool:list(pool.map(one,names))
    return names


def auxiliary(work):
    result={'foundations':verify_foundations(ROOT/'inputs')}
    marker('foundations',status='PASS',lower_bound=236,lower_pairs_checked=27730)
    # The inherited standard-library scripts write beside their source file.
    # Run fresh copies with their exact input bytes in an isolated work folder.
    for name,inputfile,outputfile in [
        ('verify_triple_histograms_analytic','deleted_triple_histograms.json','deleted_triple_histograms_analytic.json'),
        ('verify_reflection_completion','cap45.json','reflection_completion_verification.json')]:
        dest=work/name;dest.mkdir()
        shutil.copyfile(ROOT/'checks'/f'{name}.py',dest/f'{name}.py')
        shutil.copyfile(ROOT/'inputs'/inputfile,dest/inputfile)
        run_json([sys.executable,'-I',dest/f'{name}.py'])
        answer=load(dest/outputfile)
        assert answer['status'] in ('PASS','EXACT_PASS')
        if name=='verify_reflection_completion':answer.pop('positive_controls',None)
        result[name]=answer;marker(name,status='PASS')
    holes=run_json([work/'five_holes',ROOT/'inputs/cap45_codes.txt'])
    assert holes['status']=='EXACT_PASS' and holes['cases']==10890 and holes['maximum_independence_number']==5
    assert holes['all_six_subsets_checked']==609840
    result['five_holes']=holes;marker('five_holes',status='PASS',cases=10890)
    cross=run_json([work/'cross_section',ROOT/'inputs/cap18_A2_normalized_codes.txt'])
    assert cross['status']=='EXACT_PASS' and cross['completed_pairs_per_orientation']==26244
    assert cross['horizontal_reflections']==81 and cross['diagonal_reflections']==0
    assert cross['extensions']==cross['partners']==162
    result['cross_section_capacity']=cross;marker('cross_section_capacity',status='PASS',completed_pairs=52488)
    return result


def record(path,d,r):
    assert r['status']=='PASS'
    r['minimum_slack']=int(r['minimum_slack'])
    if 'target_value' in r:r['target_dot_dual']=r.pop('target_value')
    r['target_dot_dual']=int(r['target_dot_dual'])
    assert r['minimum_slack']==d['minimum_slack']>=0
    assert r['target_dot_dual']==d['target_dot_dual']<0
    r['certificate']=str(path.relative_to(ROOT));r['certificate_sha256']=sha(path)
    return r


def verify_structural(path,kind,work,hist):
    d=load(path);assert d['target_total']==M and d['status']=='EXACT_FARKAS_EXCLUSION'
    a,b,c=d['anchor'],d['B'],d['C'];assert a+b+c==M
    center={'none':0,'B':1,'C':2}[d['centered_layer']]
    if kind in ('double','high'):
        k=d['anchor_kind'];key=(a,k,b,c)
        assert key in (DOUBLE_EXPECTED if kind=='double' else HIGH_EXPECTED)
        hs,mult=PROFILES[(a,k)];provided=list(map(tuple,d['hprofiles']))
        assert len(provided)==len(set(provided))==len(hs) and set(provided)==set(hs)
        order=[provided.index(h) for h in hs]
        assert [d['hprofile_multiplicities'][i] for i in order]==mult
        y=[d['integer_dual'][i] for i in order]+d['integer_dual'][len(hs):]
        assert len(y)==len(hs)+5
        payload=f'{M} {a} {b} {c} {center} '+str({'single':0,'ordinary':1,'antipodal':2}[k])+'\n'+ints(y)+'\n'
    else:
        cl=d['histogram_class'];h=hist[cl];key=(cl,b)
        assert a==109 and 86<=b<=109 and c<=b
        assert d['anchor_normalization']=='remaining_cap_centroid_zero'
        assert d['hprofiles']==h['hprofiles'] and d['hprofile_multiplicities']==h['multiplicities']
        assert len(d['integer_dual'])==len(d['hprofiles'])+5
        lines=[f'{M} 109 {b} {c} {center} {len(d["hprofiles"])}']
        lines += [ints(row+[n]) for row,n in zip(d['hprofiles'],d['hprofile_multiplicities'])]
        lines += [ints(d['integer_dual'])];payload='\n'.join(lines)+'\n'
    r=run_json([work/kind],payload)
    for left,right in [('raw_labelled_grids','raw_labelled_grids'),('admissible_grids','valid_labelled_grids'),('distinct_columns','distinct_columns')]:
        assert r[left]==d[right],(path.name,left)
    r=record(path,d,r);r['branch']=list(key)
    return key,r


def verify_small(path,work):
    d=load(path);assert d['target_total']==M and d['status']=='EXACT_FARKAS_EXCLUSION'
    a,b,c=d['A'],d['B'],d['C'];assert a+b+c==M
    k=d['deleted_antipodal_pairs'];zero=int(d['centroid_of_A']=='zero')
    assert (a==108 and 106<=b<=109) or (a==107 and b==107)
    assert (k,zero) in ((0,0),(0,1),(1,0),(2,int(a==108)))
    assert d['conditional_maximum_slice']==109 and d['completion_center_zero'] is True
    assert d['uses_43_43_completion_extension'] is True
    known=d['previously_excluded_global_profiles'];assert known==[list(P[0])]
    delta=112-a;e=112-2*delta+2*k
    target=[56,308,1232-11*delta,12320-110*delta,
            27104+2*delta*delta-475*delta+18*k,
            492800+38*delta*delta-8728*delta+144*k,
            13*a**3+81*a*a+27*a+81*e*(a+1),m2(a),m3(a),m2(b),m3(b),m2(c),m3(c),121*a*b*c,364 if zero else 121]
    assert d['target']==target and len(d['integer_dual'])==15
    lines=[f'{M} {a} {b} {k} {zero} 1 1',ints(P[0]),ints(d['integer_dual'])]
    r=run_json([work/'completed_small'],'\n'.join(lines)+'\n')
    for name in ['A','B','C','raw_labelled_grids','valid_labelled_grids','distinct_columns']:
        assert r[name]==d[name],(path.name,name)
    r=record(path,d,r);key=(a,b,k,zero);r['branch']=list(key)
    return key,r


def verify_generic(path,work,stage,expected_counts):
    d=load(path);assert d['status']=='EXACT_FARKAS_EXCLUSION' and d['target_total']==M
    p=(d['A'],d['B'],d['C']);assert p in P and sum(p)==M
    assert d['conditional_maximum_slice']==109 and d['uses_43_43_completion_extension'] is True
    gs=d['globally_excluded_completed_sizes'];assert gs==[109]
    known=d['previously_excluded_global_profiles']
    expected_known=[] if stage=='P0' else [P[0]] if stage=='P1' else P[:2] if stage=='P2P3P4' else P[:5]
    assert list(map(tuple,known))==expected_known
    contexts={int(n):{tuple(sorted(p)) for p in ps} for n,ps in d['completed_slice_contexts'].items()}
    assert contexts==({} if stage=='P0' else CONTEXTS)
    ns=list(p);centered=[]
    for i,n in enumerate(ns):
        if n%3 and len(centered)<2:centered.append(i)
    assert d['centered_rows']==['ABC'[i] for i in centered]
    relation=d.get('centroid_relation','unsplit')
    target=ordinary_target(*p)
    if relation=='unsplit':kind='generic';mode=None
    else:
        assert relation in MODES and len(centered)==1
        kind='centroids';mode=MODES.index(relation)
        target += [364 if mode==0 or 1<=mode<=4 and j==mode-1 else 121 for j in range(4)]
    assert d['target']==target and len(d['integer_dual'])==len(target)
    cs=[(n,pr) for n,ps in sorted(contexts.items()) for pr in sorted(ps)]
    lines=[f'{M} '+ints(p)+f' 1 {len(gs)} {len(known)} {len(cs)}',ints(gs)]
    lines += [ints(pr) for pr in known]
    lines += [ints([n,*pr]) for n,pr in cs]
    if mode is not None:lines += [f'{len(target)} {mode}']
    lines += [ints(d['integer_dual'])]
    r=run_json([work/kind],'\n'.join(lines)+'\n');r=record(path,d,r)
    assert r['profile']==list(p)
    for name,value in expected_counts[path.name].items():assert int(r[name])==value,(path.name,name)
    key=(p,relation);r['branch']=[list(p),relation]
    return key,r


def group(name,paths,expected,fn,workers):
    assert len(paths)==len(expected),(name,len(paths),len(expected))
    records=[];found=set()
    with ThreadPoolExecutor(max_workers=workers) as pool:
        for key,r in pool.map(fn,paths):
            assert key not in found;found.add(key);records.append(r)
    assert found==expected,(name,'incomplete coverage')
    raw=sum(r.get('raw_labelled_grids',r.get('raw_fully_labelled',0)) for r in records)
    valid=sum(r.get('admissible_grids',r.get('valid_labelled_grids',r.get('valid_fully_labelled',0))) for r in records)
    marker(name,status='PASS',branches=len(records),raw_grids=raw,admissible_grids=valid)
    return {'status':'PASS','branches':len(records),'raw_grids':raw,'admissible_grids':valid,'cases':records}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--workers',type=int,choices=(1,2),default=2)
    ap.add_argument('--cxx',default=os.environ.get('CXX','g++'))
    ap.add_argument('--output',type=Path,default=ROOT/'VERIFICATION_RESULT.json')
    args=ap.parse_args();assert sys.version_info>=(3,10) and __debug__,'Use Python >=3.10 without -O'
    start=time.monotonic();checks=checksum_inputs();marker('checksums',**checks)
    hist=load(ROOT/'inputs/deleted_triple_histograms.json')['remaining_cap_centroid_zero']['histogram_classes']
    expected_counts=load(ROOT/'inputs/generic_expected_counts.json')
    groups={}
    with tempfile.TemporaryDirectory(prefix='cap066-replay-') as tmp:
        work=Path(tmp);compile_all(work,args.cxx,args.workers);marker('compilation',status='PASS',checkers=8)
        aux=auxiliary(work)
        for kind,expected in [('double',DOUBLE_EXPECTED),('high',HIGH_EXPECTED),('completed109',{(cl,b) for cl in range(4) for b in range(86,110)})]:
            paths=sorted((CERTS/kind).glob('*.json'))
            groups[kind]=group(kind,paths,expected,lambda p:verify_structural(p,kind,work,hist),args.workers)
        groups['P0']=group('P0',[CERTS/'generic/generic_pending43_A109_B109.json'],{(P[0],'unsplit')},lambda p:verify_generic(p,work,'P0',expected_counts),args.workers)
        small_expected={(a,b,k,z) for a in (107,108) for b in ([107] if a==107 else range(106,110))
                        for k,z in [(0,0),(0,1),(1,0),(2,int(a==108))]}
        groups['completed_small']=group('completed_small',sorted((CERTS/'completed_small').glob('*.json')),small_expected,lambda p:verify_small(p,work),args.workers)
        gens=CERTS/'generic'
        paths=[gens/f'centroid_fullrank_A109_B108_{mode}.json' for mode in MODES]
        groups['P1']=group('P1',paths,{(P[1],m) for m in MODES},lambda p:verify_generic(p,work,'P1',expected_counts),args.workers)
        paths=[gens/f'centroid_afterP1_A108_B108_{mode}.json' for mode in MODES]+[gens/'centroid_afterP1_A109_B107_unsplit.json',gens/'centroid_afterP1_A109_B106_unsplit.json']
        expected={(P[4],m) for m in MODES}|{(P[i],'unsplit') for i in (2,3)}
        groups['P2P3P4']=group('P2P3P4',paths,expected,lambda p:verify_generic(p,work,'P2P3P4',expected_counts),args.workers)
        paths=[gens/f'centroid_afterP4_A{a}_B{b}_unsplit.json' for a,b in [(108,107),(108,106),(107,107)]]
        groups['P5P6P7']=group('P5P6P7',paths,{(P[i],'unsplit') for i in (5,6,7)},lambda p:verify_generic(p,work,'P5P6P7',expected_counts),args.workers)
    forcing=verify_global_forcing()
    totals={k:sum(g[k] for g in groups.values()) for k in ('branches','raw_grids','admissible_grids')}
    assert totals=={'branches':242,'raw_grids':1974032142,'admissible_grids':273592522}
    out={'status':'PASS','lower_bound':236,'upper_bound':279,'excluded_size':280,
         'classification_theorems_imported':True,'end_to_end_lean':False,
         'arithmetic':'Python integers and signed C++ __int128; no numerical solver',
         'seconds':time.monotonic()-start,'workers':args.workers,'checksums':checks,
         'totals':totals,'auxiliary_checks':aux,'groups':groups,'global_forcing':forcing}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    marker('COMPLETE',status='PASS',lower_bound=236,upper_bound=279,**totals,seconds=out['seconds'])

if __name__=='__main__':main()
