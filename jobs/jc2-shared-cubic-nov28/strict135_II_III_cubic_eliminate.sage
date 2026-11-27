#!/usr/bin/env sage
"""Exact characteristic-zero two-stage strict-III elimination.

sage strict135_III_eliminate.sage OUTPUT_DIRECTORY
Eleven variables; arbitrary monic cubic common divisor covers all derivative-gcd degrees at least three. Includes three independently checked common-fibre phase equations.
First try D|W,D|H, then if nonunit or timed out add D|p',D|q'. Total internal budget20 minutes;
recommended Actions timeout30 minutes, always below the six-hour limit.
Only a characteristic-zero lift certificate, checked and replayed in a fresh
Singular process, is accepted. Timeout and nonunit outcomes are inconclusive.
"""
import json, pathlib, signal, subprocess, sys, time
from sage.all import QQ, PolynomialRing, save

started=time.monotonic()
TOTAL_SECONDS=int(1200)
out=pathlib.Path(sys.argv[1] if len(sys.argv)>1 else 'strict135_II_III_cubic_elimination_output')
out.mkdir(parents=True,exist_ok=True)

def alarm_handler(signum,frame):
    raise TimeoutError('Overall exact-elimination budget exhausted')
signal.signal(signal.SIGALRM,alarm_handler)
signal.alarm(TOTAL_SECONDS)

def dump_status(value):
    (out/'status.json').write_text(json.dumps(value,indent=2))
    print(json.dumps(value),flush=True)

def remaining():
    return max(1,int(TOTAL_SECONDS-(time.monotonic()-started)-15))

def sing(f):
    return str(f).replace('**','^')

try:
    vars=['r4','r3','s4','s3','s2','s1','s0','d2','d1','d0','z']
    C=PolynomialRing(QQ,names=vars,order='degrevlex')
    g=C.gens_dict()
    A=PolynomialRing(C,'t');t=A.gen()
    r4,r3,s4,s3,s2,s1,s0=[g[v] for v in vars[:7]]
    d2,d1,d0,z=[g[v] for v in vars[7:]]
    r2=(3*s1+6*s4*s2+3*s3**2+3*s3*s4**2+3*r4**2-6*r3*s4-6*r4*s3-6*r4*s4**2)/2
    S=t**5+s4*t**4+s3*t**3+s2*t**2+s1*t+s0
    Rbase=t**6+r4*t**4+r3*t**3+r2*t**2
    U,Vbase=(S**2).quo_rem(Rbase)
    r1=Vbase[5]
    r0=Vbase[4]-r1*U[3]
    R=Rbase+r1*t+r0
    V=S**2-R*U
    assert V.degree()<=3
    P=R**2+S
    Q=R**3+QQ(3)/2*R*S+QQ(3)/8*U
    E=QQ(1)/8*(S**3-6*V*R**2)-QQ(9)/8*V*S+QQ(9)/64*U**2
    assert E==Q**2-P**3
    W=2*P*Q.derivative()-3*Q*P.derivative()
    assert W.degree()<=10
    lam=E[12]
    base=[]
    for i in range(6,11): base.append((f'W_coeff_{i}_zero',C(W[i])))
    base.append(('weierstrass_remainder_coeff_11_zero',C(E[11])))
    base.append(('W_leading_coefficient',C(W[5]+24*lam)))
    TT=E-lam*P
    base.append(('exact_remainder_degree10_rabinowitsch',C(z*TT[10]-1)))
    base.append(('common_fibre_canonical_T9',C(TT[9])))
    base.append(('common_fibre_canonical_T7_times12',C(12*TT[7]-9*TT[9]*P[10]-10*TT[10]*P[9])))
    base.append(('common_fibre_canonical_T5_times288',C(288*TT[5]-168*TT[7]*P[10]-192*TT[8]*P[9]-216*TT[9]*P[8]+153*TT[9]*P[10]**2-240*TT[10]*P[7]+340*TT[10]*P[10]*P[9])))
    D=t**3+d2*t**2+d1*t+d0
    H=U*U.derivative()-4*S*V.derivative()
    assert H.degree()<=7 and H[7]==4-12*V[3]
    assert 3*H==(U+4*S*R)*(8*Q).derivative()-3*(4*R*(U+4*S*R)+8*S**2)*P.derivative()
    meta={'field':'QQ','variables':vars,'order':'degrevlex','internal_total_seconds':TOTAL_SECONDS,
          'normalizations':['R monic sextic','R5=0','S monic quintic'],
          'triangular_eliminations':['r1 from V5=0','r0 from V4=0','r2 from E11 after E15,E14,E13'],
          'saturation':['z*T10=1'],'stages':['cubic D divides W and H','cubic D divides Pprime and Qprime'],
          'scope':'Complete common-cubic-divisor target for shared II/III phase family; lambda may be zero. A unit certificate proves derivative gcd degree at most two.'}
    (out/'system_metadata.json').write_text(json.dumps(meta,indent=2))
    save({'ring':C,'R':R,'S':S,'U':U,'V':V,'P':P,'Q':Q,'E':E,'W':W,'D':D,'H':H,
          'lambda':lam,'base_equations':base},str(out/'construction.sobj'))
    print('BOUNDARY_SYSTEM_READY '+json.dumps(meta),flush=True)

    def monic_remainder(f,label):
        rem=f
        for k in range(int(f.degree()),2,-1):
            rem=rem-rem[k]*t**(k-3)*D
            print(label+' REMAINDER_STEP '+str(k)+' TERMS '+str(sum(len(C(rem[i]).monomials()) for i in range(k))),flush=True)
        assert rem.degree()<=2
        return [(label+f'_remainder_{i}',C(rem[i])) for i in range(3)]

    def run_stage(name,named,seconds):
        stage=out/name;stage.mkdir(parents=True,exist_ok=True)
        cleared=[]
        for label,f in named:
            if f: cleared.append((label,C(f.denominator()*f)))
        I=C.ideal([f for _,f in cleared])
        save({'ring':C,'ideal':I,'equations':cleared},str(stage/'system.sobj'))
        (stage/'equations.txt').write_text('\n\n'.join(label+' := '+str(f) for label,f in cleared)+'\n')
        prefix=['ring r=0,('+','.join(vars)+'),dp;',
                'ideal I='+',\n'.join(sing(f) for _,f in cleared)+';']
        lines=prefix+['option(redSB);','ideal G=std(I);',
            'print("GROEBNER_FINISHED"); print("BASIS_SIZE"); print(size(G));',
            'write("groebner.txt",G);','if (reduce(1,G)==0) {',
            ' print("UNIT_IDEAL_OVER_QQ");',' matrix M=lift(I,ideal(1));',
            ' matrix One[1][1]=1;',' matrix Check=matrix(I)*M-One;',
            ' print("CERTIFICATE_REMAINDER"); print(Check);',
            ' if (size(ideal(Check))==0) {',
            '  print("CERTIFICATE_EXACTLY_VERIFIED");',
            '  write("certificate_matrix.txt",M);',
            '  write("certificate.sing","matrix M["+string(size(I))+"][1]="+string(M)+";");',
            ' } else { print("CERTIFICATE_CHECK_FAILED"); }',
            '} else { print("NONUNIT_OR_UNRESOLVED"); }','quit;']
        (stage/'system.sing').write_text('\n'.join(lines)+'\n')
        sec=min(seconds,remaining())
        print('STAGE_BEGIN '+name+' seconds='+str(sec)+' equations='+str(len(cleared)),flush=True)
        begin=time.monotonic()
        try:
            result=subprocess.run(['Singular','-q','system.sing'],cwd=str(stage),text=True,
                    stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=sec)
            raw=result.stdout
            (stage/'singular.log').write_text(raw)
            candidate=('CERTIFICATE_EXACTLY_VERIFIED' in raw and
                'CERTIFICATE_CHECK_FAILED' not in raw and result.returncode==0 and
                (stage/'certificate.sing').is_file())
            replayed=False
            if candidate:
                replay=prefix+['execute(read("certificate.sing"));','matrix One[1][1]=1;',
                    'matrix Check=matrix(I)*M-One;',
                    'if (size(ideal(Check))==0) { print("FRESH_REPLAY_EXACT_ZERO"); }',
                    'else { print("FRESH_REPLAY_FAILED"); print(Check); }','quit;']
                (stage/'replay.sing').write_text('\n'.join(replay)+'\n')
                checked=subprocess.run(['Singular','-q','replay.sing'],cwd=str(stage),text=True,
                    stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=min(120,remaining()))
                (stage/'replay.log').write_text(checked.stdout)
                replayed=('FRESH_REPLAY_EXACT_ZERO' in checked.stdout and
                    'FRESH_REPLAY_FAILED' not in checked.stdout and checked.returncode==0)
            status={'stage':name,'seconds':time.monotonic()-begin,'exit_code':result.returncode,
                'verified_unit_certificate':bool(candidate and replayed),
                'result':'EXACT_QQ_UNIT_CERTIFICATE_REPLAYED' if candidate and replayed else 'INCONCLUSIVE_OR_NONUNIT'}
            print(raw[-5000:],flush=True)
        except subprocess.TimeoutExpired as err:
            raw=err.stdout or ''
            if isinstance(raw,bytes): raw=raw.decode('utf-8',errors='replace')
            (stage/'singular.log').write_text(raw)
            status={'stage':name,'seconds':time.monotonic()-begin,'result':'TIMEOUT_INCONCLUSIVE','verified_unit_certificate':False}
        (stage/'status.json').write_text(json.dumps(status,indent=2))
        print(json.dumps(status),flush=True)
        return status

    Wsmall=sum(W[i]*t**i for i in range(6))
    low=monic_remainder(Wsmall,'W')+monic_remainder(H,'H')
    first=run_stage('low_degree',base+low,min(120,remaining()))
    if first['verified_unit_certificate']:
        dump_status({'result':'SHARED_PHASE_FAMILY_DERIVATIVE_GCD_AT_MOST_TWO','stage':'low_degree',
            'verified_unit_certificate':True,'seconds':time.monotonic()-started,
            'limitation':'Requires separately audited geometric profile and cusp-budget premises; Lean replay still required.'})
    elif remaining()>90:
        full=monic_remainder(P.derivative(),'Pprime')+monic_remainder(Q.derivative(),'Qprime')
        second=run_stage('full_degree',base+low+full,remaining())
        dump_status({'result':'SHARED_PHASE_FAMILY_DERIVATIVE_GCD_AT_MOST_TWO' if second['verified_unit_certificate'] else 'INCONCLUSIVE',
            'verified_unit_certificate':second['verified_unit_certificate'],'stage':'full_degree',
            'seconds':time.monotonic()-started,
            'limitation':'Timeout/nonunit is not evidence of existence or nonexistence; every terminal closure needs audited geometry and Lean replay.'})
    else:
        dump_status({'result':'TIME_BUDGET_INCONCLUSIVE','verified_unit_certificate':False,'seconds':time.monotonic()-started})
except TimeoutError as err:
    dump_status({'result':'OVERALL_TIMEOUT_INCONCLUSIVE','verified_unit_certificate':False,
        'seconds':time.monotonic()-started,'message':str(err)})
except Exception as err:
    dump_status({'result':'ERROR_INCONCLUSIVE','verified_unit_certificate':False,
        'seconds':time.monotonic()-started,'error_type':type(err).__name__,'message':str(err)})
    raise
finally:
    signal.alarm(0)
