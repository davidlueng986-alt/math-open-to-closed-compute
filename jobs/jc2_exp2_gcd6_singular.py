#!/usr/bin/env python3
"""
Exact Q-algebraic exclusion test for DEGREE-135-IV-GCD-SIX using SymPy + Singular.
Generates the exact weighted-homogeneous subsystem (l = 1 WLOG since l != 0):
  - 2*M*T' - M'*T - 18*A*(A'*r - A*r') = 0  (degrees 23..0; t20..t3 solved exactly)
  - coeff_d(T^2 - 9*p_L*A^2) = 0            (degrees 26..23, and optionally 22..18)
  - w * b2 - 1 = 0                          (Rabinowitsch saturation for b2 != 0)
and computes exact Groebner bases over Q in Singular.
"""
import subprocess
import time
import sympy as sp

def main():
    t0_start = time.time()
    u = sp.Symbol('u')
    r1, r0, v6, a2, a1, a0, t2, t1, t0, p0 = sp.symbols('r1 r0 v6 a2 a1 a0 t2 t1 t0 p0')
    l = sp.Integer(1)

    r = u**2 + r1*u + r0
    b9 = sp.Rational(9, 2)
    v9 = sp.Integer(1)
    b6 = sp.Rational(9, 8)*(4*v6 - 13*l)
    v3 = sp.Rational(3, 500)*l*(500*v6 - 1001*l)
    b3 = sp.Rational(27, 500)*l*(377*l - 125*v6)

    # 1. Exact B(u) and g(u)
    Q_B = sp.expand(b9 * r**6 / u**3 + b6 * r**4 / u**2 + b3 * r**2 / u)
    num_B = sp.Poly(sp.expand(Q_B * u**3), u)
    poly_B = sum(num_B.nth(k) * u**(k - 3) for k in range(3, num_B.degree() + 1))

    c2, c1 = sp.symbols('c2 c1')
    B_tmp = sp.expand(poly_B + c2*u**2 + c1*u)
    _, rem_B = sp.div(sp.Poly(sp.diff(B_tmp, u), u), sp.Poly(r, u))
    sol_c = sp.solve([rem_B.nth(1), rem_B.nth(0)], [c2, c1])
    c2_val = sp.expand(sol_c[c2])
    c1_val = sp.expand(sol_c[c1])
    B = sp.expand(poly_B + c2_val*u**2 + c1_val*u)
    g = sp.div(sp.Poly(sp.diff(B, u), u), sp.Poly(r, u))[0].as_expr()

    b2_val = c2_val
    b1_val = sp.expand(c1_val - sp.Rational(4, 3)*r1*b2_val)
    v2_val = sp.expand(sp.Rational(2, 9) * b2_val)
    v1_val = sp.expand(sp.Rational(2, 9) * b1_val)

    # 2. Exact A(u)
    Q_A = sp.expand(v9 * r**7 / u**3 + v6 * r**5 / u**2 + v3 * r**3 / u)
    num_A = sp.Poly(sp.expand(Q_A * u**3), u)
    poly_A_hi = sum(num_A.nth(k) * u**(k - 3) for k in range(6, num_A.degree() + 1))
    extra_A = sp.Poly(sp.expand(r * (v2_val*(u**2 + sp.Rational(4,3)*r1*u) + v1_val*u)), u)
    extra_A_hi = sum(extra_A.nth(k) * u**k for k in range(3, extra_A.degree() + 1))
    A = sp.expand(poly_A_hi + extra_A_hi + a2*u**2 + a1*u + a0)

    # 3. Exact ODE 2*M*T' - M'*T = 18*A*(A'*r - A*r')
    M = sp.Poly(sp.expand(r**2 + l*u), u)
    RHS = sp.Poly(sp.expand(18 * A * (sp.diff(A, u)*r - A*sp.diff(r, u))), u)

    t = [sp.Integer(0)] * 21
    for k in range(20, 2, -1):
        d = k + 3
        lhs_rest = sp.Integer(0)
        for j in range(0, 4):
            i = d + 1 - j
            if 3 <= i <= 20:
                lhs_rest += t[i] * (2*i - j) * M.nth(j)
        t[k] = sp.expand((RHS.nth(d) - lhs_rest) / (2*k - 4))
    t[2], t[1], t[0] = t2, t1, t0

    # Remaining ODE equations at degrees 5, 4, 3, 2, 1, 0:
    ode_eqs = {}
    for d in [5, 4, 3, 2, 1, 0]:
        lhs_d = sp.Integer(0)
        for j in range(0, 5):
            i = d + 1 - j
            if 0 <= i <= 20:
                lhs_d += t[i] * (2*i - j) * M.nth(j)
        ode_eqs[d] = sp.expand(RHS.nth(d) - lhs_d)

    # 4. Exact T^2 - 9*pL*A^2 at degrees 26..18:
    pL = sp.integrate(sp.expand(g * A), u) + p0
    T_full = sum(t[k]*u**k for k in range(0, 21))
    P_T = sp.Poly(T_full, u)
    P_pL = sp.Poly(pL, u)
    P_A2 = sp.Poly(sp.expand(A**2), u)

    def coeff_prod(P1, P2, deg):
        res = sp.Integer(0)
        for i in range(max(0, deg - P2.degree()), min(P1.degree(), deg) + 1):
            res += P1.nth(i) * P2.nth(deg - i)
        return sp.expand(res)

    sq_eqs = {}
    for d in [26, 25, 24, 23, 22, 21, 20, 19, 18]:
        sq_eqs[d] = sp.expand(coeff_prod(P_T, P_T, d) - 9 * coeff_prod(P_pL, P_A2, d))

    print(f"Generated exact polynomials in {time.time() - t0_start:.2f}s.", flush=True)

    def clear_denom(expr):
        # Clear rational denominators to get primitive integer polynomial
        expr = sp.expand(expr)
        if expr == 0:
            return sp.Integer(0)
        p_obj = sp.Poly(expr, r1, r0, v6, a2, a1, a0, t2, t1, t0, p0, domain='QQ')
        _, prim = p_obj.clear_denoms()
        return prim.as_expr()

    def to_sing(expr):
        return str(clear_denom(expr)).replace('**', '^')

    # Write Singular script 1: ODE + sq_eqs[26..23] + w*b2 - 1 (NO p0!)
    sing_lines = [
        'option(redSB);',
        'ring R = 0, (t2, t1, t0, a2, a1, a0, w, v6, r0, r1), dp;',
    ]
    polys_1 = [
        ('eq26', sq_eqs[26]),
        ('eq25', sq_eqs[25]),
        ('eq24', sq_eqs[24]),
        ('eq23', sq_eqs[23]),
        ('ode5', ode_eqs[5]),
        ('ode4', ode_eqs[4]),
        ('ode3', ode_eqs[3]),
        ('ode2', ode_eqs[2]),
        ('ode1', ode_eqs[1]),
        ('ode0', ode_eqs[0]),
    ]
    for name, expr in polys_1:
        sing_lines.append(f'poly {name} = {to_sing(expr)};')
    sing_lines.append(f'poly b2p = {to_sing(b2_val)};')
    sing_lines.append('poly sat = w * b2p - 1;')
    sing_lines.append('ideal I1 = eq26, eq25, eq24, eq23, ode5, ode4, ode3, ode2, ode1, ode0, sat;')
    sing_lines.append('printf("=== Running groebner(I1) over Q (without p0) ===");')
    sing_lines.append('ideal G1 = groebner(I1);')
    sing_lines.append('printf("G1 size = %s", size(G1));')
    sing_lines.append('G1;')
    sing_lines.append('if (size(G1) == 1 && G1[1] == 1) { printf("RESULT_I1: UNIT_IDEAL_PROVED_OVER_Q"); }')
    sing_lines.append('quit;')

    with open('test_gcd6_I1.sing', 'w') as f:
        f.write('\n'.join(sing_lines) + '\n')

    # Also write Singular script 2: with sq_eqs[22..18] and p0 included!
    sing_lines2 = [
        'option(redSB);',
        'ring R = 0, (p0, t2, t1, t0, a2, a1, a0, w, v6, r0, r1), dp;',
    ]
    polys_2 = polys_1 + [
        ('eq22', sq_eqs[22]),
        ('eq21', sq_eqs[21]),
        ('eq20', sq_eqs[20]),
        ('eq19', sq_eqs[19]),
        ('eq18', sq_eqs[18]),
    ]
    for name, expr in polys_2:
        sing_lines2.append(f'poly {name} = {to_sing(expr)};')
    sing_lines2.append(f'poly b2p = {to_sing(b2_val)};')
    sing_lines2.append('poly sat = w * b2p - 1;')
    sing_lines2.append('ideal I2 = eq26, eq25, eq24, eq23, eq22, eq21, eq20, eq19, eq18, ode5, ode4, ode3, ode2, ode1, ode0, sat;')
    sing_lines2.append('printf("=== Running groebner(I2) over Q (with p0 and eq22..18) ===");')
    sing_lines2.append('ideal G2 = groebner(I2);')
    sing_lines2.append('printf("G2 size = %s", size(G2));')
    sing_lines2.append('G2;')
    sing_lines2.append('if (size(G2) == 1 && G2[1] == 1) { printf("RESULT_I2: UNIT_IDEAL_PROVED_OVER_Q"); }')
    sing_lines2.append('quit;')

    with open('test_gcd6_I2.sing', 'w') as f:
        f.write('\n'.join(sing_lines2) + '\n')

    # First run I1 with Singular!
    print("Running Singular on I1...", flush=True)
    t1_start = time.time()
    proc1 = subprocess.run(['Singular', '-q', 'test_gcd6_I1.sing'], capture_output=True, text=True)
    print(f"Singular I1 finished in {time.time() - t1_start:.2f}s, rc={proc1.returncode}", flush=True)
    print(proc1.stdout)
    if proc1.stderr:
        print("STDERR:", proc1.stderr)

    if 'UNIT_IDEAL_PROVED_OVER_Q' not in proc1.stdout:
        print("Running Singular on I2...", flush=True)
        t2_start = time.time()
        proc2 = subprocess.run(['Singular', '-q', 'test_gcd6_I2.sing'], capture_output=True, text=True)
        print(f"Singular I2 finished in {time.time() - t2_start:.2f}s, rc={proc2.returncode}", flush=True)
        print(proc2.stdout)
        if proc2.stderr:
            print("STDERR:", proc2.stderr)

if __name__ == '__main__':
    main()
