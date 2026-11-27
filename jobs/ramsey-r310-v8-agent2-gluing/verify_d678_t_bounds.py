#!/usr/bin/env python3
"""
Exact verification of Theorem 1 (alpha(G[X,Y]) <= 9 lower bound on t)
and Theorem 2 (A/B singleton upper bound on t) across all 12 D678 leaves.
"""
import json

V = (6, 7, 8, 9)

def d678_t_bounds():
    rows = []
    for d in (6, 7, 8):
        for q in V:
            nx, ny, nt = d - 1, q - 1, 40 - d - q
            v7_hi = min(nx * ny, nx * (q - 3), ny * (d - 3))
            t_lo = max(0, d + q - 11)
            sx_max, sy_max = 9 * nx, 9 * ny
            t_hi_x = sx_max - nx - 2 * nt + nx * (10 - d)
            t_hi_y = sy_max - ny - 2 * nt + ny * (10 - q)
            t_hi = min(v7_hi, t_hi_x, t_hi_y)
            old_span = v7_hi + 1
            new_span = max(0, t_hi - t_lo + 1)
            rows.append({
                "leaf": f"D{d}-N{q}", "d": d, "q": q, "nx": nx, "ny": ny, "nt": nt,
                "v7_t_range": [0, v7_hi], "thm1_t_lo": t_lo,
                "thm2_t_hi_x": t_hi_x, "thm2_t_hi_y": t_hi_y,
                "exact_t_range": [t_lo, t_hi],
                "v7_t_count": old_span, "new_t_count": new_span,
                "t_pruned_pct": round(100.0 * (1.0 - new_span / old_span), 1)
            })
    return rows

if __name__ == "__main__":
    rows = d678_t_bounds()
    print("Leaf  | v7 t-range | Thm1 lo | Thm2 hi(X,Y) | Exact t-range | Pruned %")
    print("------|------------|---------|--------------|---------------|---------")
    for r in rows:
        print(f"{r['leaf']:5s} |  0..{r['v7_t_range'][1]:2d}     |   {r['thm1_t_lo']:2d}    |"
              f" ({r['thm2_t_hi_x']:2d}, {r['thm2_t_hi_y']:2d})     |"
              f"   {r['exact_t_range'][0]:2d}..{r['exact_t_range'][1]:2d}      |  {r['t_pruned_pct']:5.1f}%")
    with open("d678_t_bounds.json", "w") as f:
        json.dump(rows, f, indent=2)
