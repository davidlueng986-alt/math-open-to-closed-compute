#!/usr/bin/env sage
"""
Exact QQ and modular Singular 4.4.1 elimination for the coupled
SECANT-HEIGHT-FOUR-REALIZATION ODE (OPPOSITE-EDGE.md Eqs. 79-83):

  16*X*(2*V*X' - 3*X + (3/2)*a1^2 - (3/2)*mu3*a1 + mu2*V)
    = 3*(a1^4 - 2*mu3*a1^3 + 4*mu2*V*a1^2 - 8*mu1*V^2*a1 + 16*mu0*V^3)

With exact Opposite-Edge boundary coupling:
  mu0 = alpha != 0, mu1 = alpha*dlt, mu2 = 1, mu3 = -dlt
  a1(V) = -dlt + a2*V^2 + ... + a_{d-1}*V^{d-1} + V^d   (scaled a_d = 1)
  X(V)  = -dlt^2/4 + V + 3*alpha*V^2 + x3*V^3 + ... + x_{2d}*V^{2d}
  w*alpha - 1 = 0  (enforcing mu0 = alpha != 0)
"""
import json, pathlib, re, subprocess, sys, time
from sage.all import QQ, PolynomialRing

out = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else 'out_height4')
out.mkdir(parents=True, exist_ok=True)

def sing_str(f):
    return str(f).replace('**', '^')

def build_equations(d, delta_zero=False):
    a_names = [f'a{k}' for k in range(2, d)]
    x_names = [f'x{k}' for k in range(3, 2*d + 1)]
    if delta_zero:
        vnames = x_names + a_names + ['alpha', 'w']
    else:
        vnames = x_names + a_names + ['dlt', 'alpha', 'w']
    R = PolynomialRing(QQ, names=vnames, order='degrevlex')
    g = R.gens_dict()
    PR = PolynomialRing(R, 'V')
    V = PR.gen()

    dlt = R(0) if delta_zero else g['dlt']
    alpha = g['alpha']
    mu0, mu1, mu2, mu3 = alpha, alpha * dlt, R(1), -dlt

    a1 = -dlt + sum(g[f'a{k}'] * V**k for k in range(2, d)) + V**d
    X = -dlt**2 / 4 + V + 3 * alpha * V**2 + sum(g[f'x{k}'] * V**k for k in range(3, 2*d + 1))

    lhs = 16 * X * (2 * V * X.derivative() - 3 * X + QQ(3)/2 * a1**2 - QQ(3)/2 * mu3 * a1 + mu2 * V)
    rhs = 3 * (a1**4 - 2 * mu3 * a1**3 + 4 * mu2 * V * a1**2 - 8 * mu1 * V**2 * a1 + 16 * mu0 * V**3)
    diff = lhs - rhs

    # Verify V^0..V^3 vanish identically
    for k in range(4):
        assert diff[k] == 0, f"Unexpected nonzero V^{k}: {diff[k]}"

    eqs = []
    for k in range(4, diff.degree() + 1):
        c = R(diff[k])
        if c != 0:
            eqs.append(R(c.denominator() * c))
    eqs.append(g['w'] * alpha - 1)
    return R, vnames, eqs

def run_singular(tag, vnames, eqs, char=0, algo='slimgb', timeout_sec=180, verify_lift=False):
    stage = out / tag
    stage.mkdir(parents=True, exist_ok=True)
    ring_decl = f"ring r={char},({','.join(vnames)}),dp;"
    ideal_decl = "ideal I=" + ",\n".join(sing_str(f) for f in eqs) + ";"
    lines = [
        ring_decl,
        "short=0;",
        ideal_decl,
        "option(redSB);",
        f"ideal G={algo}(I);",
        'print("GB_DONE");',
        'print("GB_SIZE=" + string(size(G)));',
        'if (reduce(1, G) == 0) {',
        '  print("UNIT_IDEAL");',
    ]
    if verify_lift and char == 0:
        lines += [
            '  matrix M = lift(I, ideal(1));',
            '  matrix One[1][1] = 1;',
            '  matrix Chk = matrix(I) * M - One;',
            '  if ((nrows(M) == size(I)) && (ncols(M) == 1) && (Chk[1,1] == 0)) {',
            '    print("LIFT_VERIFIED_EXACT");',
            '  } else {',
            '    print("LIFT_FAILED");',
            '  }',
        ]
    lines += [
        '} else {',
        '  print("NONUNIT_IDEAL");',
        '  print("DIM=" + string(dim(G)));',
        '  print("DEG=" + string(deg(G)));',
        '}',
        'quit;'
    ]
    (stage / 'run.sing').write_text('\n'.join(lines) + '\n')
    t0 = time.monotonic()
    try:
        res = subprocess.run(['Singular', '-q', 'run.sing'], cwd=str(stage),
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                             text=True, timeout=timeout_sec)
        elapsed = time.monotonic() - t0
        raw = res.stdout
        (stage / 'singular.log').write_text(raw)
        has_err = any(re.match(r'^\s*\?', ln) for ln in raw.splitlines())
        status = 'ERROR' if has_err or res.returncode != 0 else (
            'UNIT_LIFT_VERIFIED' if 'LIFT_VERIFIED_EXACT' in raw else (
            'UNIT_IDEAL' if 'UNIT_IDEAL' in raw else 'NONUNIT_IDEAL'))
        print(f"[{tag}] char={char} algo={algo} status={status} time={elapsed:.2f}s vars={len(vnames)} eqs={len(eqs)}", flush=True)
        if status != 'UNIT_LIFT_VERIFIED' and status != 'UNIT_IDEAL':
            print(raw[-1500:], flush=True)
        return status, elapsed
    except subprocess.TimeoutExpired:
        elapsed = time.monotonic() - t0
        print(f"[{tag}] char={char} algo={algo} status=TIMEOUT ({elapsed:.1f}s)", flush=True)
        return 'TIMEOUT', elapsed

results = {}

# 1. Exact QQ with lift verification for d=2, 3, 4 (general delta)
for d, tlim in [(2, 30), (3, 60), (4, 180)]:
    R, vnames, eqs = build_equations(d, delta_zero=False)
    st, el = run_singular(f'd{d}_gen_QQ', vnames, eqs, char=0, algo='slimgb', timeout_sec=tlim, verify_lift=True)
    results[f'd{d}_gen_QQ'] = {'status': st, 'seconds': round(el, 2)}

# 2. Delta = 0 for d=4, 5, 6 (first mod 32003, then exact QQ!)
for d, tlim in [(4, 60), (5, 180), (6, 240)]:
    R, vnames, eqs = build_equations(d, delta_zero=True)
    st_m, el_m = run_singular(f'd{d}_dlt0_mod32003', vnames, eqs, char=32003, algo='slimgb', timeout_sec=60)
    results[f'd{d}_dlt0_mod32003'] = {'status': st_m, 'seconds': round(el_m, 2)}
    if st_m == 'UNIT_IDEAL':
        st_q, el_q = run_singular(f'd{d}_dlt0_QQ', vnames, eqs, char=0, algo='slimgb', timeout_sec=tlim, verify_lift=True)
        results[f'd{d}_dlt0_QQ'] = {'status': st_q, 'seconds': round(el_q, 2)}

# 3. GENERAL delta for d=5 (j=4, Wave 1 minimal survivor!)
R, vnames, eqs = build_equations(5, delta_zero=False)
st_m5, el_m5 = run_singular('d5_gen_mod32003', vnames, eqs, char=32003, algo='slimgb', timeout_sec=180)
results['d5_gen_mod32003'] = {'status': st_m5, 'seconds': round(el_m5, 2)}
if st_m5 == 'UNIT_IDEAL':
    st_q5, el_q5 = run_singular('d5_gen_QQ', vnames, eqs, char=0, algo='slimgb', timeout_sec=360, verify_lift=True)
    results['d5_gen_QQ'] = {'status': st_q5, 'seconds': round(el_q5, 2)}

(out / 'summary.json').write_text(json.dumps(results, indent=2))
print("FINAL_SUMMARY:", json.dumps(results, indent=2), flush=True)
