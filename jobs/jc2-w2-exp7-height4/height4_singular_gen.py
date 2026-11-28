#!/usr/bin/env python3
"""
Wave 2 Explorer 7: Exact top-down polynomial elimination and Singular 4.4.1
certificate generator for SECANT-HEIGHT-FOUR-REALIZATION (OPPOSITE-EDGE.md Eq. (83)).

Given d >= 4 (corresponding to j = d - 1 >= 3, deg(P,Q) = (16*(2j+1), 16*(3j+1))
before shear or (4a, 4b) opposite-edge rectangle), we normalize WLOG over C:
  c_d = 1, mu_2 = 1, mu_3 = -delta, mu_1 = m0 * delta, mu_0 = m0 (m0 != 0).
(Valid because the 2-parameter scaling (V, a1, X) -> (s*V, t*a1, t^2*X) has
exponent determinant -2d + 1 != 0 for all d >= 1.)

Polynomiality of b1 = (X + a1*b2 - (3/4)*a1^2)/V and [xi^2]|_{V=0} forces:
  x_0 = -delta^2 / 4,   x_1 = 1,   x_2 = 3*m0   (and x_3 = -3*m0^2 if delta = 0).

Top-down elimination from [V^{4d}] down to [V^{2d}] has strictly nonzero linear
pivots for ALL d >= 4 and ALL 0 <= k <= 2d-1, and x_0..x_{2d} are completely
independent of m0 (since 2d > d + 2 for all d >= 3). Thus m0 = x_2 / 3 is
eliminated with zero denominators, leaving a pure polynomial ideal in
(c_{d-1}, ..., c_2, delta) over Q(sqrt(3d)).
"""
import argparse
import math
import sys
import time
import sympy as sp


def squarefree_part(n: int):
    """Return (r, s) with n = r^2 * s and s squarefree."""
    r = 1
    s = n
    p = 2
    while p * p <= s:
        while s % (p * p) == 0:
            s //= (p * p)
            r *= p
        p += 1
    return r, s


def verify_decoupling_identity():
    """Verify from first principles that [PH, QL] = M(xi) implies the X-ODE."""
    V, xi, m0, m1, m2, m3 = sp.symbols('V xi m0 m1 m2 m3')
    a1 = sp.Function('a1')(V)
    a0 = sp.Function('a0')(V)
    b2 = sp.Function('b2')(V)
    b1 = sp.Function('b1')(V)
    b0 = sp.Function('b0')(V)

    PH = xi**3 * V + xi**2 * b2 + xi * b1 + b0
    QL = xi**2 * V + xi * a1 + a0
    PB = sp.expand(sp.diff(PH, xi) * sp.diff(QL, V) - sp.diff(PH, V) * sp.diff(QL, xi))
    M = xi**4 * V + m3 * xi**3 + m2 * xi**2 + m1 * xi + m0
    Pdiff = sp.Poly(PB - M, xi)

    # E3: 3*V*a1' - 2*V*b2' - m3 - a1 + 2*b2 = 0
    # E2: 3*V*a0' - 2*V*b1' - m2 - a1*b2' + b1 + 2*b2*a1' = 0
    b2p_expr = (3 * V * sp.diff(a1, V) - a1 + 2 * b2 - m3) / (2 * V)
    b1p_expr = (3 * V * sp.diff(a0, V) + b1 + 2 * b2 * sp.diff(a1, V) - a1 * b2p_expr - m2) / (2 * V)
    assert sp.simplify(Pdiff.nth(3).subs(sp.diff(b2, V), b2p_expr)) == 0
    assert sp.simplify(Pdiff.nth(2).subs({sp.diff(b2, V): b2p_expr, sp.diff(b1, V): b1p_expr})) == 0

    X = V * b1 - a1 * b2 + sp.Rational(3, 4) * a1**2
    lhs_factor = sp.simplify(
        (2 * V * sp.diff(X, V) - 3 * X + sp.Rational(3, 2) * a1**2 - sp.Rational(3, 2) * m3 * a1 + m2 * V)
        .subs({sp.diff(b2, V): b2p_expr, sp.diff(b1, V): b1p_expr})
    )
    dQL_dV_crit = sp.simplify(sp.diff(QL, V).subs(xi, -a1 / (2 * V)))
    dPH_dxi_crit = sp.simplify(sp.diff(PH, xi).subs(xi, -a1 / (2 * V)))
    assert sp.simplify(X - V * dPH_dxi_crit) == 0
    assert sp.simplify(lhs_factor - 3 * V**2 * dQL_dV_crit) == 0
    rhs_val = sp.expand(16 * V**3 * M.subs(xi, -a1 / (2 * V)))
    ode_rhs = sp.expand(a1**4 - 2 * m3 * a1**3 + 4 * m2 * V * a1**2 - 8 * m1 * V**2 * a1 + 16 * m0 * V**3)
    assert sp.simplify(rhs_val - ode_rhs) == 0
    print("[OK] Verified exact symplectic decoupling identity from [PH, QL] = M(xi).")


def build_system(d: int, set_delta0: bool):
    t0 = time.time()
    assert d >= 4, "Top-down pivot non-vanishing holds for all d >= 4."
    r_rad, s_rad = squarefree_part(3 * d)  # sqrt(3d) = r_rad * w, w^2 = s_rad
    V, delta, m0, w = sp.symbols('V delta m0 w')
    cs = [sp.Symbol(f'c{k}') for k in range(2, d)]  # c2, ..., c_{d-1}
    xs = [sp.Symbol(f'x{k}') for k in range(2 * d + 1)]

    d_val = sp.Integer(0) if set_delta0 else delta
    a1 = -d_val + sum(cs[k - 2] * V**k for k in range(2, d)) + V**d
    X = sum(xs[k] * V**k for k in range(2 * d + 1))

    ode = sp.Poly(
        16 * X * (2 * V * sp.diff(X, V) - 3 * X + sp.Rational(3, 2) * a1**2 + sp.Rational(3, 2) * d_val * a1 + V)
        - 3 * (a1**4 + 2 * d_val * a1**3 + 4 * V * a1**2 - 8 * m0 * d_val * V**2 * a1 + 16 * m0 * V**3),
        V,
    )

    def reduce_w(expr):
        p = sp.Poly(sp.expand(expr), w)
        res = sp.Integer(0)
        for (deg_w,), coeff in p.terms():
            q, rem = divmod(deg_w, 2)
            res += coeff * (s_rad**q) * (w**rem)
        return sp.expand(res)

    subs = {xs[2 * d]: (-3 + 2 * r_rad * w) / (4 * (4 * d - 3))}
    assert reduce_w(ode.nth(4 * d).subs(subs)) == 0

    for k in range(2 * d - 1, -1, -1):
        eq = reduce_w(ode.nth(2 * d + k).subs(subs))
        piv = sp.Poly(eq.coeff(xs[k]), w)
        A, B = piv.nth(0), piv.nth(1)
        den = sp.expand(A**2 - s_rad * B**2)
        assert den != 0, f"Zero pivot at d={d}, k={k}"
        rhs = reduce_w(-eq.subs(xs[k], 0))
        subs[xs[k]] = reduce_w(rhs * (A - B * w)) / den

    for k in range(2 * d + 1):
        assert not subs[xs[k]].has(m0), f"x_{k} depends on m0!"

    m0_expr = sp.expand(subs[xs[2]] / 3)
    raw_eqs = [
        ("x0_init", reduce_w(subs[xs[0]] + d_val**2 / 4)),
        ("x1_init", reduce_w(subs[xs[1]] - 1)),
    ]
    if set_delta0:
        raw_eqs.append(("x3_init", reduce_w(subs[xs[3]] + 3 * m0_expr**2)))
    for k in range(4, 2 * d):
        raw_eqs.append((f"V{k}", reduce_w(ode.nth(k).subs(subs).subs(m0, m0_expr))))

    # Order variables by increasing quasi-homogeneous weight: c_{d-1} (wt 1), ..., c2 (wt d-2), delta (wt d)
    vars_ordered = list(reversed(cs)) + ([] if set_delta0 else [delta])
    weights = [d - k for k in range(d - 1, 1, -1)] + ([] if set_delta0 else [d])

    polys = []
    for name, expr in raw_eqs:
        num, _ = sp.fraction(sp.together(expr))
        num = sp.expand(num)
        if num != 0:
            P = sp.Poly(num, *(vars_ordered + [w]), domain='ZZ')
            _, prim = P.primitive()
            polys.append((name, prim.as_expr()))

    print(
        f"[OK] Built d={d} (delta={'0' if set_delta0 else 'free'}, w^2={s_rad}): "
        f"{len(vars_ordered)} vars {vars_ordered}, weights={weights}, "
        f"{len(polys)} eqs in {time.time() - t0:.2f}s"
    )
    return vars_ordered, weights, s_rad, polys


def write_singular_file(path: str, d: int, set_delta0: bool, vars_ordered, weights, s_rad: int, polys, mode: str):
    """
    mode == 'field_wp': ring R = (0, w), (vars...), wp(weights...); minpoly = w^2 - s_rad;
    mode == 'poly_dp':  ring R = 0, (vars..., w), dp; (with w^2 - s_rad in ideal)
    mode == 'modp':     ring R = 32003, (vars..., w), wp(weights..., 1); (fast prime check)
    """
    var_str = ", ".join(str(v) for v in vars_ordered)
    wt_str = ", ".join(str(wt) for wt in weights)

    lines = [
        f"// Auto-generated by height4_singular_gen.py for d={d}, delta={'0' if set_delta0 else 'free'}, mode={mode}",
        "option(prot);",
        "int t0 = timer;",
    ]
    if mode == 'field_wp':
        lines.append(f"ring R = (0, w), ({var_str}), wp({wt_str});")
        lines.append(f"minpoly = w^2 - {s_rad};")
    elif mode == 'poly_dp':
        lines.append(f"ring R = 0, ({var_str}, w), dp;")
    elif mode == 'modp':
        lines.append(f"ring R = 32003, ({var_str}, w), wp({wt_str}, 1);")
    else:
        raise ValueError(mode)

    lines.append("ideal I =")
    poly_strs = []
    for name, expr in polys:
        poly_strs.append(f"  // {name}\n  {sp.sstr(expr).replace('**', '^')}")
    if mode in ('poly_dp', 'modp'):
        poly_strs.append(f"  // minpoly\n  w^2 - {s_rad}")
    lines.append(",\n".join(poly_strs) + ";")

    if mode == 'field_wp':
        lines.append("ideal G = slimgb(I);")
    else:
        lines.append("ideal G = slimgb(I);")

    lines.extend([
        'printf("RESULT d=%s delta=%s mode=%s elapsed=%ss size=%s G[1]=%s", '
        + f'{d}, "{"0" if set_delta0 else "free"}", "{mode}", timer - t0, size(G), G[1]);',
        "if (size(G) == 1 && G[1] == 1) {",
        '  print("STATUS: UNIT_IDEAL_PROVED");',
        "} else {",
        '  print("STATUS: NOT_UNIT_IDEAL");',
        "  print(G);",
        "  quit;",
        "}",
        "quit;",
    ])
    with open(path, "w") as f:
        f.write("\n".join(lines) + "\n")
    print(f"[OK] Wrote {path} ({len(lines)} lines)")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--d", type=int, required=True)
    ap.add_argument("--delta0", action="store_true")
    ap.add_argument("--mode", choices=["field_wp", "poly_dp", "modp"], default="field_wp")
    ap.add_argument("--out", required=True)
    ap.add_argument("--verify-identity", action="store_true")
    args = ap.parse_args()

    if args.verify_identity:
        verify_decoupling_identity()
    vars_ordered, weights, s_rad, polys = build_system(args.d, args.delta0)
    write_singular_file(args.out, args.d, args.delta0, vars_ordered, weights, s_rad, polys, args.mode)


if __name__ == "__main__":
    main()
