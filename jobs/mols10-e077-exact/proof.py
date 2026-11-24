#!/usr/bin/env python3
"""External DRAT -> LRAT verification, with exact files and exit statuses."""
from __future__ import annotations
import hashlib,json,os,pathlib,re,shutil,signal,subprocess,time
from encode import sha256_file

DRAT_SOURCE='https://github.com/marijnheule/drat-trim/tree/2e3b2dc0ecf938addbd779d42877b6ed69d9a985'

def detect_drat_format(path):
    path=pathlib.Path(path)
    if not path.exists():return 'absent'
    with path.open('rb') as source:prefix=source.read(65536)
    if not prefix:return 'empty'
    if prefix[:1]==b'a' or (prefix[:1]==b'd' and b'\0' in prefix):return 'binary_drat'
    if all(value in b'0123456789-+dc \r\n\t' for value in prefix):return 'ascii_drat'
    return 'unclassified'

def logged(command,output,seconds,disk_reserve_bytes=0):
    start=time.monotonic();timed_out=False;reason=None
    with open(output,'wb') as f:
        if disk_reserve_bytes and shutil.disk_usage(pathlib.Path(output).parent).free<disk_reserve_bytes:
            code=None;reason='DISK_RESERVE_LIMIT'
        else:
            p=subprocess.Popen(command,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
            try:
                while p.poll() is None:
                    if time.monotonic()-start>max(1,seconds):
                        timed_out=True;reason='CHECK_TIME_LIMIT';break
                    if disk_reserve_bytes and shutil.disk_usage(pathlib.Path(output).parent).free<disk_reserve_bytes:
                        reason='DISK_RESERVE_LIMIT';break
                    time.sleep(0.25)
            finally:
                if p.poll() is None:
                    try:os.killpg(p.pid,signal.SIGTERM)
                    except ProcessLookupError:pass
                    try:p.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        try:os.killpg(p.pid,signal.SIGKILL)
                        except ProcessLookupError:pass
                        p.wait()
            code=p.returncode
    return {'command':list(map(str,command)),'returncode':code,'timed_out':timed_out,
            'stop_reason':reason,'disk_reserve_bytes':disk_reserve_bytes,
            'seconds':time.monotonic()-start,'log':pathlib.Path(output).name}

def verified_line(path,pattern):
    return any(re.fullmatch(pattern,line.strip()) for line in pathlib.Path(path).read_text(errors='replace').replace('\r','\n').splitlines())

def verify_unsat(cnf,drat,drat_trim,lrat_check,seconds=900,disk_reserve_bytes=0):
    cnf=pathlib.Path(cnf);drat=pathlib.Path(drat)
    prefix=drat.with_suffix('');lrat=prefix.with_suffix('.lrat')
    trim_log=prefix.with_suffix('.drat-check.log');lrat_log=prefix.with_suffix('.lrat-check.log')
    result={'status':'UNSAT_UNVERIFIED','cnf':cnf.name,'cnf_sha256':sha256_file(cnf),
            'drat':drat.name,'drat_sha256':sha256_file(drat),'drat_format_observed':detect_drat_format(drat),
            'checker_source':DRAT_SOURCE}
    first=logged([str(drat_trim),str(cnf),str(drat),'-L',str(lrat),'-t',str(max(1,int(seconds)))],trim_log,seconds+5,disk_reserve_bytes)
    result['drat_check']=first
    if first['stop_reason']:
        result.update(status='UNSAT_AWAITING_VERIFICATION',verification_deferred=first['stop_reason'])
        return result
    if first['returncode']!=0 or not verified_line(trim_log,r's VERIFIED') or not lrat.exists():return result
    result['lrat']=lrat.name;result['lrat_sha256']=sha256_file(lrat)
    second=logged([str(lrat_check),str(cnf),str(lrat)],lrat_log,seconds,disk_reserve_bytes)
    result['lrat_check']=second
    if second['stop_reason']:
        result.update(status='UNSAT_AWAITING_VERIFICATION',verification_deferred=second['stop_reason'])
        return result
    if second['returncode']==0 and verified_line(lrat_log,r'c VERIFIED'):
        result['status']='UNSAT_VERIFIED'
    return result

def replay_lrat(cnf,lrat,lrat_check,log,seconds=900):
    result=logged([str(lrat_check),str(cnf),str(lrat)],log,seconds)
    result['verified']=result['returncode']==0 and verified_line(log,r'c VERIFIED')
    return result
