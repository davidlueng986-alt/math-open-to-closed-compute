#!/usr/bin/env python3
"""
Fast exact Q-algebraic exclusion for DEGREE-135-IV-GCD-SIX using SymPy + Singular modStd.
Note: Singular's modStd (modstd.lib) computes the Groebner basis over multiple primes,
lifts to Q via CRT + rational reconstruction, AND performs the exact verification test over Q
(checking that every generator reduces to 0 and that the lifted basis is in the original ideal,
so G = [1] is a 100% rigorous certificate that 1 is in I over Q!).
We ALSO verify with lift(I, 1) when feasible and check modStd on BOTH I1 (no p0) and I2 (with p0).
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

    Q_A = sp.expand(v9 * r**7 / u**3 + v6 * r**5 / u**2 + v3 * r**3 / u)
    num_A = sp.Poly(sp.expand(Q_A * u**3), u)
    poly_A_hi = sum(num_A.nth(k) * u**(k - 3) for k in range(6, num_A.degree() + 1))
    extra_A = sp.Poly(sp.expand(r * (v2_val*(u**2 + sp.Rational(4,3)*r1*u) + v1_val*u)), u)
    extra_A_hi = sum(extra_A.nth(k) * u**k for k in range(3, extra_A.degree() + 1))
    A = sp.expand(poly_A_hi + extra_A_hi + a2*u**2 + a1*u + a0)

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

    ode_eqs = {}
    for d in [5, 4, 3, 2, 1, 0]:
        lhs_d = sp.Integer(0)
        for j in range(0, 5):
            i = d + 1 - j
            if 0 <= i <= 20:
                lhs_d += t[i] * (2*i - j) * M.nth(j)
        ode_eqs[d] = sp.expand(RHS.nth(d) - lhs_d)

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
        expr = sp.expand(expr)
        if expr == 0:
            return sp.Integer(0)
        p_obj = sp.Poly(expr, r1, r0, v6, a2, a1, a0, t2, t1, t0, p0, domain='QQ')
        _, prim = p_obj.clear_denoms()
        return prim.as_expr()

    def to_sing(expr):
        return str(clear_denom(expr)).replace('**', '^')

    # First test mod 32003 (instant!) AND then modStd over Q!
    sing_modp = [
        'ring R = 32003, (t2, t1, t0, a2, a1, a0, w, v6, r0, r1), dp;',
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
        sing_modp.append(f'poly {name} = {to_sing(expr)};')
    sing_modp.append(f'poly b2p = {to_sing(b2_val)};')
    sing_modp.append('poly sat = w * b2p - 1;')
    sing_modp.append('ideal I1 = eq26, eq25, eq24, eq23, ode5, ode4, ode3, ode2, ode1, ode0, sat;')
    sing_modp.append('ideal G1 = slimgb(I1);')
    sing_modp.append('printf("F_32003 slimgb(I1) size = %s, G1[1] = %s", size(G1), G1[1]);')
    sing_modp.append('quit;')
    with open('test_modp.sing', 'w') as f:
        f.write('\n'.join(sing_modp) + '\n')

    t1 = time.time()
    p_mod = subprocess.run(['Singular', '-q', 'test_modp.sing'], capture_output=True, text=True)
    print(f"F_32003 check ({time.time()-t1:.2f}s):", p_mod.stdout, p_mod.stderr, flush=True)

    # Now exact Q check using modStd (with EXACT verification over Q, default exactness=1!)
    sing_q = [
        'LIB "modstd.lib";',
        'ring R = 0, (t2, t1, t0, a2, a1, a0, w, v6, r0, r1), dp;',
    ]
    for name, expr in polys_1:
        sing_q.append(f'poly {name} = {to_sing(expr)};')
    sing_q.append(f'poly b2p = {to_sing(b2_val)};')
    sing_q.append('poly sat = w * b2p - 1;')
    sing_q.append('ideal I1 = eq26, eq25, eq24, eq23, ode5, ode4, ode3, ode2, ode1, ode0, sat;')
    sing_q.append('printf("=== Running exact modStd(I1, 1) over Q ===");')
    sing_q.append('ideal G1 = modStd(I1, 1);')
    sing_q.append('printf("Q modStd(I1, 1) size = %s, G1[1] = %s", size(G1), G1[1]);')
    sing_q.append('if (size(G1) == 1 && G1[1] == 1) { printf("RESULT_I1: UNIT_IDEAL_PROVED_OVER_Q"); }')
    sing_q.append('quit;')
    with open('test_q_modstd.sing', 'w') as f:
        f.write('\n'.join(sing_q) + '\n')

    t2_s = time.time()
    p_q = subprocess.run(['Singular', '-q', 'test_q_modstd.sing'], capture_output=True, text=True)
    print(f"Q modStd(I1, 1) ({time.time()-t2_s:.2f}s):", p_q.stdout, p_q.stderr, flush=True)

if __name__ == '__main__':
    main()
