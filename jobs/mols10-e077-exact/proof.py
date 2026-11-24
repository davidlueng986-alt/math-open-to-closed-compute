#!/usr/bin/env python3
"""External DRAT -> LRAT verification, with exact files and exit statuses."""
from __future__ import annotations
import hashlib,json,pathlib,re,subprocess,time
from encode import sha256_file

DRAT_SOURCE='https://github.com/marijnheule/drat-trim/tree/2e3b2dc0ecf938addbd779d42877b6ed69d9a985'

def logged(command,output,seconds):
    start=time.monotonic();timed_out=False
    with open(output,'wb') as f:
        try:
            p=subprocess.run(command,stdout=f,stderr=subprocess.STDOUT,timeout=max(1,seconds),check=False)
            code=p.returncode
        except subprocess.TimeoutExpired:
            code=None;timed_out=True
    return {'command':list(map(str,command)),'returncode':code,'timed_out':timed_out,
            'seconds':time.monotonic()-start,'log':pathlib.Path(output).name}

def verified_line(path,pattern):
    return any(re.fullmatch(pattern,line.strip()) for line in pathlib.Path(path).read_text(errors='replace').replace('\r','\n').splitlines())

def verify_unsat(cnf,drat,drat_trim,lrat_check,seconds=900):
    cnf=pathlib.Path(cnf);drat=pathlib.Path(drat)
    prefix=drat.with_suffix('');lrat=prefix.with_suffix('.lrat')
    trim_log=prefix.with_suffix('.drat-check.log');lrat_log=prefix.with_suffix('.lrat-check.log')
    result={'status':'UNSAT_UNVERIFIED','cnf':cnf.name,'cnf_sha256':sha256_file(cnf),
            'drat':drat.name,'drat_sha256':sha256_file(drat),'checker_source':DRAT_SOURCE}
    first=logged([str(drat_trim),str(cnf),str(drat),'-L',str(lrat),'-t',str(max(1,int(seconds)))],trim_log,seconds+5)
    result['drat_check']=first
    if first['returncode']!=0 or not verified_line(trim_log,r's VERIFIED') or not lrat.exists():return result
    result['lrat']=lrat.name;result['lrat_sha256']=sha256_file(lrat)
    second=logged([str(lrat_check),str(cnf),str(lrat)],lrat_log,seconds)
    result['lrat_check']=second
    if second['returncode']==0 and verified_line(lrat_log,r'c VERIFIED'):
        result['status']='UNSAT_VERIFIED'
    return result

def replay_lrat(cnf,lrat,lrat_check,log,seconds=900):
    result=logged([str(lrat_check),str(cnf),str(lrat)],log,seconds)
    result['verified']=result['returncode']==0 and verified_line(log,r'c VERIFIED')
    return result
