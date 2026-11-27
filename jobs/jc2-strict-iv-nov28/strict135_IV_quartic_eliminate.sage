#!/usr/bin/env sage
"""Exact QQ strict-IV quartic-common-divisor obstruction,21 variables.

sage strict135_IV_quartic_eliminate.sage OUTPUT_DIRECTORY
Independent divisor coefficients and compact W avoid the previous large
substituted inverse-W expansion. Three stages add necessary divisibility
conditions, each exact. Total internal budget20 minutes; recommend30-minute
Actions timeout. A term cap is purely computational and yields no theorem.
Only an exported lift certificate replayed in a fresh process counts.
"""
import json, pathlib, re, signal, subprocess, sys, time
from sage.all import QQ, PolynomialRing, save

started=time.monotonic()
TOTAL_SECONDS=int(1200)
out=pathlib.Path(sys.argv[1] if len(sys.argv)>1 else 'strict135_IV_quartic_elimination_output')
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

def singular_has_error(raw):
    # Singular may return exit code zero after an interpreter error. Such a
    # run is never accepted, even if a later statement prints a success marker.
    return any(re.match(r'^\s*\?', line) for line in raw.splitlines())

try:
    vars=[f'r{i}' for i in range(7,-1,-1)]+[f's{i}' for i in range(7,-1,-1)]+['d3','d2','d1','d0','z']
    C=PolynomialRing(QQ,names=vars,order='degrevlex')
    g=C.gens_dict()
    A=PolynomialRing(C,'t');t=A.gen()
    R=t**9+sum(g[f'r{i}']*t**i for i in range(8))
    S=t**8+sum(g[f's{i}']*t**i for i in range(8))
    U,V=(S**2).quo_rem(R)
    assert U.degree()==7 and U[7]==1 and V.degree()<=8
    P=R**2+S
    Pprime=2*R*R.derivative()+S.derivative()
    # These compact identities are proved from S^2=RU+V. Do not expand Q^2.
    E=QQ(1)/8*(S**3-6*V*R**2)-QQ(9)/8*V*S+QQ(9)/64*U**2
    W=(24*V*R.derivative()-6*R*V.derivative()+6*S*U.derivative()-9*U*S.derivative())/8
    H=U*U.derivative()-4*S*V.derivative()
    assert W.degree()<=16 and H.degree()<=15
    lam=E[18]
    TT=E-lam*P
    base=[]
    for i in range(9,17): base.append((f'W_coeff_{i}_zero',C(W[i])))
    base.append(('T_degree17_zero',C(TT[17])))
    base.append(('T_degree16_zero',C(TT[16])))
    base.append(('W_leading_coefficient',C(W[8]+36*lam)))
    base.append(('V_degree8_zero',C(V[8])))
    base.append(('V_degree7_zero',C(V[7])))
    base.append(('exact_remainder_degree15_rabinowitsch',C(g['z']*TT[15]-1)))
    base.append(('common_fibre_canonical_T14',C(TT[14])))
    base.append(('common_fibre_canonical_T13_times6',C(6*TT[13]-5*TT[15]*P[16])))
    base.append(('common_fibre_canonical_T11_times216',C(216*TT[11]-156*TT[13]*P[16]-168*TT[14]*P[15]-180*TT[15]*P[14]+145*TT[15]*P[16]**2)))
    base.append(('common_fibre_canonical_T10_times162',C(162*TT[10]-108*TT[12]*P[16]-117*TT[13]*P[15]-126*TT[14]*P[14]+98*TT[14]*P[16]**2-135*TT[15]*P[13]+210*TT[15]*P[16]*P[15])))
    D=t**4+g['d3']*t**3+g['d2']*t**2+g['d1']*t+g['d0']
    meta={'field':'QQ','variables':vars,'order':'degrevlex','internal_total_seconds':TOTAL_SECONDS,
          'normalizations':['R monic degree9','R8=0','S monic degree8','independent monic quartic D'],
          'triangular_eliminations':'Retained as equations to avoid dense substitutions',
          'saturation':['z*T15=1'],'lambda_zero_case':'included',
          'stages':['D divides W,H','add D divides Pprime','add D divides Qprime'],
          'certificate_acceptance':['No Singular interpreter errors','Correct lift dimensions',
              'Independent exact QQ Sage polynomial identity','Fresh Singular replay'],
          'term_budget_per_remainder':350000,
          'scope':'Complete necessary strictIV target: a quartic divisor exists whenever derivative gcd degree is4 or6.'}
    (out/'system_metadata.json').write_text(json.dumps(meta,indent=2))
    save({'ring':C,'R':R,'S':S,'U':U,'V':V,'P':P,'E':E,'W':W,'D':D,'H':H,
          'lambda':lam,'base_equations':base},str(out/'construction.sobj'))
    print('BOUNDARY_SYSTEM_READY '+json.dumps(meta),flush=True)

    def monic_remainder(f,label):
        rem=f
        for k in range(int(f.degree()),3,-1):
            rem=rem-rem[k]*t**(k-4)*D
            terms=sum(len(C(rem[i]).monomials()) for i in range(k))
            print(label+' REMAINDER_STEP '+str(k)+' TERMS '+str(terms),flush=True)
            if terms>350000: raise RuntimeError('TERM_BUDGET_INCONCLUSIVE: expanded remainder exceeds350000 terms')
        assert rem.degree()<=3
        return [(label+f'_remainder_{i}',C(rem[i])) for i in range(4)]

    def run_stage(name,named,seconds):
        stage=out/name;stage.mkdir(parents=True,exist_ok=True)
        # A rerun must not reuse certificate files from an earlier process.
        for previous in stage.glob('certificate*'):
            if previous.is_file(): previous.unlink()
        cleared=[]
        for label,f in named:
            if f: cleared.append((label,C(f.denominator()*f)))
        I=C.ideal([f for _,f in cleared])
        save({'ring':C,'ideal':I,'equations':cleared},str(stage/'system.sobj'))
        (stage/'equations.txt').write_text('\n\n'.join(label+' := '+str(f) for label,f in cleared)+'\n')
        prefix=['ring r=0,('+','.join(vars)+'),dp;', 'short=0;',
                'ideal I='+',\n'.join(sing(f) for _,f in cleared)+';']
        lines=prefix+['option(redSB);','ideal G=std(I);',
            'print("GROEBNER_FINISHED"); print("BASIS_SIZE"); print(size(G));',
            'write("groebner.txt",G);','if (reduce(1,G)==0) {',
            ' print("UNIT_IDEAL_OVER_QQ");',' matrix M=lift(I,ideal(1));',
            ' if ((nrows(M)==size(I)) && (ncols(M)==1)) {',
            '  print("CERTIFICATE_DIMENSIONS_VERIFIED");',
            '  matrix One[1][1]=1;','  matrix Check=matrix(I)*M-One;',
            '  print("CERTIFICATE_REMAINDER"); print(Check);',
            '  if (Check[1,1]==0) {',
            '   print("CERTIFICATE_EXACTLY_VERIFIED");',
            '   int j;',
            '   for (j=1;j<=size(I);j++) {',
            '    write("certificate_coeff_"+string(j)+".txt",string(M[j,1]));',
            '   }',
            '  } else { print("CERTIFICATE_CHECK_FAILED"); }',
            ' } else { print("CERTIFICATE_DIMENSIONS_FAILED"); }',
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
                'CERTIFICATE_DIMENSIONS_VERIFIED' in raw and
                'CERTIFICATE_CHECK_FAILED' not in raw and
                'CERTIFICATE_DIMENSIONS_FAILED' not in raw and
                not singular_has_error(raw) and result.returncode==0)
            sage_verified=False
            replayed=False
            if candidate:
                # Independent exact QQ reconstruction: the asserted Singular
                # shape and printed markers are insufficient evidence by
                # themselves. Parse each coefficient into the original Sage
                # ring and check the polynomial identity against the original
                # cleared generators, without any ideal-membership oracle.
                expected=[stage/('certificate_coeff_'+str(j)+'.txt')
                          for j in range(1,len(cleared)+1)]
                exported=list(stage.glob('certificate_coeff_*.txt'))
                if set(exported)!=set(expected):
                    raise RuntimeError('CERTIFICATE_EXPORT_COUNT_MISMATCH')
                coeffs=[C(path.read_text().strip()) for path in expected]
                residual=sum((f*h for (_,f),h in zip(cleared,coeffs)),C.zero())-1
                sage_verified=bool(residual==0)
                (stage/'certificate_sage_check.json').write_text(json.dumps({
                    'field':'QQ','generator_count':len(cleared),
                    'coefficient_count':len(coeffs),
                    'residual_is_exact_zero':sage_verified,
                    'method':'Exact polynomial arithmetic; no Groebner basis used in this check.'},indent=2))
                save({'ring':C,'generators':[f for _,f in cleared],
                      'coefficients':coeffs,'residual':residual},str(stage/'certificate.sobj'))
                if not sage_verified:
                    raise RuntimeError('INDEPENDENT_SAGE_CERTIFICATE_IDENTITY_FAILED')
                print('INDEPENDENT_SAGE_EXACT_QQ_IDENTITY_VERIFIED',flush=True)
                # Re-serialize the Sage-parsed coefficients rather than
                # executing an unparsed Singular-generated matrix string.
                certificate='matrix M['+str(len(cleared))+'][1]='+','.join(sing(h) for h in coeffs)+';'
                (stage/'certificate.sing').write_text(certificate+'\n')
                replay=prefix+[certificate,
                    'if ((nrows(M)==size(I)) && (ncols(M)==1)) {',
                    ' print("FRESH_REPLAY_DIMENSIONS_VERIFIED");',
                    ' matrix One[1][1]=1;',' matrix Check=matrix(I)*M-One;',
                    ' if (Check[1,1]==0) { print("FRESH_REPLAY_EXACT_ZERO"); }',
                    ' else { print("FRESH_REPLAY_FAILED"); print(Check); }',
                    '} else { print("FRESH_REPLAY_DIMENSIONS_FAILED"); }','quit;']
                (stage/'replay.sing').write_text('\n'.join(replay)+'\n')
                checked=subprocess.run(['Singular','-q','replay.sing'],cwd=str(stage),text=True,
                    stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=min(120,remaining()))
                (stage/'replay.log').write_text(checked.stdout)
                replayed=('FRESH_REPLAY_EXACT_ZERO' in checked.stdout and
                    'FRESH_REPLAY_DIMENSIONS_VERIFIED' in checked.stdout and
                    'FRESH_REPLAY_FAILED' not in checked.stdout and
                    'FRESH_REPLAY_DIMENSIONS_FAILED' not in checked.stdout and
                    not singular_has_error(checked.stdout) and checked.returncode==0)
            accepted=bool(candidate and sage_verified and replayed)
            status={'stage':name,'seconds':time.monotonic()-begin,'exit_code':result.returncode,
                'singular_interpreter_error':singular_has_error(raw),
                'independent_sage_identity_verified':sage_verified,
                'fresh_singular_replay_verified':replayed,
                'verified_unit_certificate':accepted,
                'result':'EXACT_QQ_UNIT_CERTIFICATE_REPLAYED' if accepted else 'INCONCLUSIVE_OR_NONUNIT'}
            print(raw[-5000:],flush=True)
        except subprocess.TimeoutExpired as err:
            raw=err.stdout or ''
            if isinstance(raw,bytes): raw=raw.decode('utf-8',errors='replace')
            (stage/'singular.log').write_text(raw)
            status={'stage':name,'seconds':time.monotonic()-begin,'result':'TIMEOUT_INCONCLUSIVE','verified_unit_certificate':False}
        (stage/'status.json').write_text(json.dumps(status,indent=2))
        print(json.dumps(status),flush=True)
        return status

    # Exercise export, dimensions, exact independent parsing, and fresh replay
    # on a known unit ideal before using the same path for the research ideal.
    # This self-test is never used as evidence about strict profile IV.
    smoke=run_stage('certificate_self_test',
        [('test_x',g['r7']),('test_one_minus_x',1-g['r7'])],min(30,remaining()))
    if not smoke['verified_unit_certificate']:
        raise RuntimeError('CERTIFICATE_PIPELINE_SELF_TEST_FAILED')
    print('CERTIFICATE_PIPELINE_SELF_TEST_PASSED_NO_RESEARCH_CONCLUSION',flush=True)

    Wsmall=sum(W[i]*t**i for i in range(9))
    Hsmall=sum(H[i]*t**i for i in range(14))
    low=monic_remainder(Wsmall,'W')+monic_remainder(Hsmall,'H')
    first=run_stage('low_degree',base+low,min(90,remaining()))
    final=first
    if not final['verified_unit_certificate'] and remaining()>90:
        middle=monic_remainder(Pprime,'Pprime')
        second=run_stage('Pprime_stage',base+low+middle,min(180,remaining()))
        final=second
        if not final['verified_unit_certificate'] and remaining()>90:
            Qprime=QQ(3)/2*R*Pprime+QQ(3)/2*S*R.derivative()+QQ(3)/8*U.derivative()
            high=monic_remainder(Qprime,'Qprime')
            final=run_stage('full_common_divisor',base+low+middle+high,remaining())
    dump_status({'result':'STRICT_IV_ALGEBRA_EXCLUDED' if final['verified_unit_certificate'] else 'INCONCLUSIVE',
        'verified_unit_certificate':final['verified_unit_certificate'],'stage':final['stage'],
        'seconds':time.monotonic()-started,
        'limitation':'Exact algebra certificate still needs audited geometry and requested Lean replay; nonunit/timeout/term cap is inconclusive.'})
except TimeoutError as err:
    dump_status({'result':'OVERALL_TIMEOUT_INCONCLUSIVE','verified_unit_certificate':False,
        'seconds':time.monotonic()-started,'message':str(err)})
except Exception as err:
    dump_status({'result':'ERROR_INCONCLUSIVE','verified_unit_certificate':False,
        'seconds':time.monotonic()-started,'error_type':type(err).__name__,'message':str(err)})
    raise
finally:
    signal.alarm(0)
