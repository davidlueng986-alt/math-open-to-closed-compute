#!/usr/bin/env python3
"""
3-variable exact Q-proof for DEGREE-135-IV-GCD-SIX using SymPy + Singular.
Eliminates t1, t0 (integer denoms 2, 4) and t2 (all three 2x2 minors of ode2, ode1, ode0),
and splits cleanly into:
  Branch A (denom_a != 0): 3-variable ideal (m0123, m0124, num_det21, num_det20, num_det10)
                           saturated by denom_a * b2 != 0.
  Branch B (denom_a == 0): 3-variable ideal (denom_a, m0123, m0124, m0134, m0234, m1234)
                           saturated by b2 != 0.
Both branches cover 100% of solutions in C^3 with l=1 (WLOG) and b2 != 0!
"""
import subprocess
import time
import sympy as sp

def main():
    t0_s = time.time()
    u = sp.Symbol('u')
    r1, r0, v6, a2, a1, a0, t2, t1, t0 = sp.symbols('r1 r0 v6 a2 a1 a0 t2 t1 t0')
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

    # Eliminate t1 from ode4 (coeff of t1 is +2), t0 from ode3 (coeff of t0 is +4)
    sol_t1 = sp.solve(ode_eqs[4], t1)[0]
    sol_t0 = sp.solve(ode_eqs[3].subs(t1, sol_t1), t0)[0]
    ode2 = sp.expand(ode_eqs[2].subs({t1: sol_t1, t0: sol_t0}))
    ode1 = sp.expand(ode_eqs[1].subs({t1: sol_t1, t0: sol_t0}))
    ode0 = sp.expand(ode_eqs[0].subs({t1: sol_t1, t0: sol_t0}))

    # Extract linear coefficients in t2 for ode2, ode1, ode0:
    def lin_t2(e):
        return sp.expand(e.coeff(t2, 1)), sp.expand(e.subs(t2, 0))
    c2_t2, c2_0 = lin_t2(ode2)
    c1_t2, c1_0 = lin_t2(ode1)
    c0_t2, c0_0 = lin_t2(ode0)
    # 3x2 matrix [[c2_t2, c2_0], [c1_t2, c1_0], [c0_t2, c0_0]] must have rank <= 1!
    # Wait: c2_t2, c1_t2, c0_t2 depend ONLY on (r1, r0), NOT on (a2, a1, a0)!!
    print("c2_t2 =", sp.factor(c2_t2))
    print("c1_t2 =", sp.factor(c1_t2))
    print("c0_t2 =", sp.factor(c0_t2))

    # Build 5x4 augmented matrix M_aug for [eq26, eq25, eq24, eq23, ode5]:
    pL = sp.integrate(sp.expand(g * A), u)
    T_hi = sum(t[k]*u**k for k in range(3, 21))
    P_T = sp.Poly(T_hi, u)
    P_pL = sp.Poly(pL, u)
    P_A2 = sp.Poly(sp.expand(A**2), u)

    def coeff_prod(P1, P2, deg):
        res = sp.Integer(0)
        for i in range(max(0, deg - P2.degree()), min(P1.degree(), deg) + 1):
            res += P1.nth(i) * P2.nth(deg - i)
        return sp.expand(res)

    lin5 = [sp.expand(coeff_prod(P_T, P_T, d) - 9 * coeff_prod(P_pL, P_A2, d)) for d in [26, 25, 24, 23]]
    lin5.append(ode_eqs[5])

    M_aug = sp.Matrix([[sp.expand(e.coeff(v, 1)) for v in [a2, a1, a0]] + [sp.expand(e.subs({a2:0, a1:0, a0:0}))] for e in lin5])
    print(f"Built M_aug in {time.time()-t0_s:.2f}s. Computing 3x3 and 4x4 minors...", flush=True)

    # 3x3 determinant of rows 0,1,2:
    denom_a = sp.expand(M_aug[[0,1,2], [0,1,2]].det())
    # Cramer numerators for a2, a1, a0 (so a_k = num_ak / denom_a):
    # Note M_aug * [a2, a1, a0, 1]^T = 0 => A3 * [a2, a1, a0]^T = -col3
    A3 = M_aug[[0,1,2], [0,1,2]]
    rhs3 = -M_aug[[0,1,2], [3]]
    num_a = []
    for col in range(3):
        Mc = A3.copy()
        Mc[:, col] = rhs3
        num_a.append(sp.expand(Mc.det()))

    # 4x4 minors of M_aug (all 5):
    m0123 = sp.expand(M_aug[[0,1,2,3], :].det())
    m0124 = sp.expand(M_aug[[0,1,2,4], :].det())
    m0134 = sp.expand(M_aug[[0,1,3,4], :].det())
    m0234 = sp.expand(M_aug[[0,2,3,4], :].det())
    m1234 = sp.expand(M_aug[[1,2,3,4], :].det())
    print(f"Computed 4x4 minors in {time.time()-t0_s:.2f}s.", flush=True)

    # Substitute a_k = num_a[k] / denom_a into the three 2x2 determinants of (ode2, ode1, ode0):
    # Since c*_0 is degree <= 2 in (a2, a1, a0), multiplying by denom_a^2 clears denominators!
    def sub_cramer_hom(expr):
        P = sp.Poly(expr, a2, a1, a0)
        res = sp.Integer(0)
        for (e2, e1, e0), coeff in zip(P.monoms(), P.coeffs()):
            d_tot = e2 + e1 + e0
            res += coeff * (num_a[0]**e2) * (num_a[1]**e1) * (num_a[2]**e0) * (denom_a**(2 - d_tot))
        return sp.expand(res)

    det21 = sp.expand(c2_t2 * c1_0 - c1_t2 * c2_0)
    det20 = sp.expand(c2_t2 * c0_0 - c0_t2 * c2_0)
    det10 = sp.expand(c1_t2 * c0_0 - c0_t2 * c1_0)

    print("Clearing denominators into 3-var polys (det21, det20, det10)...", flush=True)
    H21 = sub_cramer_hom(det21)
    H20 = sub_cramer_hom(det20)
    H10 = sub_cramer_hom(det10)
    print(f"All 3-var polynomials built in {time.time()-t0_s:.2f}s!", flush=True)

    def to_sing3(expr):
        P = sp.Poly(sp.expand(expr), v6, r0, r1, domain='QQ')
        _, prim = P.clear_denoms()
        return str(prim.as_expr()).replace('**', '^')

    # --- Singular Script for Branch B (denom_a == 0) ---
    sing_B = [
        'LIB "modstd.lib";',
        'ring R = 0, (w, v6, r0, r1), dp;',
        f'poly da = {to_sing3(denom_a)};',
        f'poly m1 = {to_sing3(m0123)};',
        f'poly m2 = {to_sing3(m0124)};',
        f'poly m3 = {to_sing3(m0134)};',
        f'poly m4 = {to_sing3(m0234)};',
        f'poly m5 = {to_sing3(m1234)};',
        f'poly b2p = {to_sing3(b2_val)};',
        'ideal IB = da, m1, m2, m3, m4, m5, w*b2p - 1;',
        'ideal GB = modStd(IB, 1);',
        'printf("BRANCH_B (denom_a=0) exact Q modStd size=%s, GB[1]=%s", size(GB), GB[1]);',
        'if (size(GB) == 1 && GB[1] == 1) { printf("BRANCH_B_PROVED_EMPTY_OVER_Q"); }',
        'quit;'
    ]
    with open('branch_B.sing', 'w') as f:
        f.write('\n'.join(sing_B) + '\n')

    tB = time.time()
    pB = subprocess.run(['Singular', '-q', 'branch_B.sing'], capture_output=True, text=True)
    print(f"Branch B finished in {time.time()-tB:.2f}s:", pB.stdout, pB.stderr, flush=True)

    # --- Singular Script for Branch A (denom_a != 0) ---
    # First check over F_32003, then exact Q modStd!
    sing_A = [
        'LIB "modstd.lib";',
        'LIB "elim.lib";',
        'ring R = 0, (v6, r0, r1), dp;',
        f'poly da = {to_sing3(denom_a)};',
        f'poly m1 = {to_sing3(m0123)};',
        f'poly m2 = {to_sing3(m0124)};',
        f'poly h21 = {to_sing3(H21)};',
        f'poly h20 = {to_sing3(H20)};',
        f'poly h10 = {to_sing3(H10)};',
        f'poly b2p = {to_sing3(b2_val)};',
        'ideal IA = m1, m2, h21, h20, h10;',
        'printf("=== Computing modStd(IA, 1) in 3 vars over Q ===");',
        'ideal GA = modStd(IA, 1);',
        'printf("dim(GA) = %s, size(GA) = %s", dim(GA), size(GA));',
        'printf("=== Saturating GA by da and b2p ===");',
        'ring R4 = 0, (w, v6, r0, r1), dp;',
        'ideal GA4 = imap(R, GA);',
        'poly da4 = imap(R, da);',
        'poly b2p4 = imap(R, b2p);',
        'ideal IA_sat = GA4, w * da4 * b2p4 - 1;',
        'ideal GA_sat = modStd(IA_sat, 1);',
        'printf("BRANCH_A (denom_a!=0) exact Q modStd size=%s, GA_sat[1]=%s", size(GA_sat), GA_sat[1]);',
        'if (size(GA_sat) == 1 && GA_sat[1] == 1) { printf("BRANCH_A_PROVED_EMPTY_OVER_Q"); }',
        'quit;'
    ]
    with open('branch_A.sing', 'w') as f:
        f.write('\n'.join(sing_A) + '\n')

    tA = time.time()
    pA = subprocess.run(['Singular', '-q', 'branch_A.sing'], capture_output=True, text=True)
    print(f"Branch A finished in {time.time()-tA:.2f}s:", pA.stdout, pA.stderr, flush=True)

if __name__ == '__main__':
    main()
