#!/usr/bin/env python3
"""
Compute the order-7 (R₇) BCH residual for Suzuki S₄, producing data for the
uniform Trotter-error bound

    ‖S₄(t) − e^{tH}‖ ≤ t⁵ · Σ γᵢ ‖Cᵢ‖ + t⁷ · K · max(‖A‖,‖B‖)^7

where γᵢ are the order-5 BCH prefactors (from compute_bch_prefactors.py) and
K is a uniform bound on ‖R₇‖ / max(‖A‖,‖B‖)^7.

Method: extend the NC-free-algebra BCH expansion from max_degree=5 to
max_degree=7, verify order-6 vanishes (palindromic), extract R₇ as a
polynomial in 7-letter words, and compute

    K = Σ (7-letter words w) |coef(w)|

which is a rigorous (if crude) uniform bound on ‖R₇‖ via the triangle
inequality ‖R₇‖ ≤ K · max(‖A‖,‖B‖)^7.

This is a SUFFICIENT bound for the uniform-bound theorem in Lean: once
K is an explicit rational number, the bound is fully rigorous.

Usage:       python3 compute_bch_r7.py
Dependencies: sympy
"""

import sympy as sp
from collections import defaultdict
from typing import Dict, Tuple


# ---------- Free non-commutative algebra over ℚ[p] (same as compute_bch_prefactors.py) ----------

NCPoly = Dict[Tuple[int, ...], sp.Expr]


def ncpoly_zero() -> NCPoly:
    return defaultdict(lambda: sp.Integer(0))


def ncpoly_from_scalar(c) -> NCPoly:
    r = ncpoly_zero()
    c = sp.sympify(c)
    if c != 0:
        r[()] = c
    return r


def ncpoly_a() -> NCPoly:
    r = ncpoly_zero()
    r[(0,)] = sp.Integer(1)
    return r


def ncpoly_b() -> NCPoly:
    r = ncpoly_zero()
    r[(1,)] = sp.Integer(1)
    return r


def ncpoly_add(p: NCPoly, q: NCPoly) -> NCPoly:
    r = ncpoly_zero()
    for w, c in p.items():
        r[w] = r[w] + c
    for w, c in q.items():
        r[w] = r[w] + c
    return defaultdict(lambda: sp.Integer(0),
                       {w: sp.expand(c) for w, c in r.items() if c != 0})


def ncpoly_scale(p: NCPoly, c) -> NCPoly:
    c = sp.sympify(c)
    if c == 0:
        return ncpoly_zero()
    return defaultdict(lambda: sp.Integer(0),
                       {w: sp.expand(c * v) for w, v in p.items()})


def ncpoly_neg(p: NCPoly) -> NCPoly:
    return ncpoly_scale(p, -1)


def ncpoly_sub(p: NCPoly, q: NCPoly) -> NCPoly:
    return ncpoly_add(p, ncpoly_neg(q))


def ncpoly_mul(p: NCPoly, q: NCPoly) -> NCPoly:
    r = ncpoly_zero()
    for w1, c1 in p.items():
        for w2, c2 in q.items():
            w = w1 + w2
            r[w] = r[w] + c1 * c2
    return defaultdict(lambda: sp.Integer(0),
                       {w: sp.expand(c) for w, c in r.items() if c != 0})


def ncpoly_truncate(p: NCPoly, max_degree: int) -> NCPoly:
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in p.items() if len(w) <= max_degree})


def ncpoly_exp(x: NCPoly, max_degree: int) -> NCPoly:
    result = ncpoly_from_scalar(1)
    x_power = ncpoly_from_scalar(1)
    for k in range(1, max_degree + 1):
        x_power = ncpoly_truncate(ncpoly_mul(x_power, x), max_degree)
        result = ncpoly_add(result, ncpoly_scale(x_power, sp.Rational(1, sp.factorial(k))))
    return result


def ncpoly_log_one_plus(x: NCPoly, max_degree: int) -> NCPoly:
    result = ncpoly_zero()
    x_power = ncpoly_from_scalar(1)
    for k in range(1, max_degree + 1):
        x_power = ncpoly_truncate(ncpoly_mul(x_power, x), max_degree)
        sign = sp.Integer(1) if k % 2 == 1 else sp.Integer(-1)
        result = ncpoly_add(result, ncpoly_scale(x_power, sign / sp.Integer(k)))
    return result


# ---------- Build S₂ and S₄ ----------

def strang_block_series(c, max_degree: int) -> NCPoly:
    half_c = c / sp.Integer(2)
    halfA = ncpoly_scale(ncpoly_a(), half_c)
    cB = ncpoly_scale(ncpoly_b(), c)
    exp_halfA = ncpoly_exp(halfA, max_degree)
    exp_cB = ncpoly_exp(cB, max_degree)
    result = exp_halfA
    result = ncpoly_truncate(ncpoly_mul(result, exp_cB), max_degree)
    result = ncpoly_truncate(ncpoly_mul(result, exp_halfA), max_degree)
    return result


def suzuki4_series(p, max_degree: int) -> NCPoly:
    q = sp.Integer(1) - 4 * p
    s_p = strang_block_series(p, max_degree)
    s_q = strang_block_series(q, max_degree)
    result = s_p
    for block in [s_p, s_q, s_p, s_p]:
        result = ncpoly_truncate(ncpoly_mul(result, block), max_degree)
    return result


def log_s4_residual(p, max_degree: int = 7) -> NCPoly:
    s4 = suzuki4_series(p, max_degree)
    y = defaultdict(lambda: sp.Integer(0), {w: c for w, c in s4.items() if w != ()})
    ls4 = ncpoly_log_one_plus(y, max_degree)
    target = ncpoly_zero()
    target[(0,)] = sp.Integer(1)
    target[(1,)] = sp.Integer(1)
    return ncpoly_sub(ls4, target)


def extract_degree(p: NCPoly, k: int) -> NCPoly:
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in p.items() if len(w) == k})


def simplify_under_suzuki(expr, p) -> sp.Expr:
    """Reduce p^n (n ≥ 3) using p^3 = (48p² − 12p + 1)/60 (Suzuki cubic)."""
    expr = sp.expand(expr)
    suzuki_reduction = (48 * p**2 - 12 * p + 1) / 60
    for n in range(10, 2, -1):
        while expr.has(p**n):
            expr = expr.subs(p**n, p**(n-3) * suzuki_reduction)
            expr = sp.expand(expr)
    return sp.simplify(expr)


# ---------- Main ----------

def main():
    p = sp.Symbol('p')
    suzuki_p_val = 1 / (4 - sp.Rational(4, 1)**sp.Rational(1, 3))
    suzuki_p_val_num = float(suzuki_p_val)

    print("=" * 70)
    print("R₇ computation for Suzuki S₄ (order 7 BCH residual)")
    print("=" * 70)
    print(f"Suzuki p ≈ {suzuki_p_val_num:.6f}")
    print("\nComputing log(S₄(τ)) - τ·(A+B) up to degree 7 (this may take 1-5 minutes) ...")

    residual = log_s4_residual(p, max_degree=7)

    print("\nVerifying palindromic cancellations:")
    for k in [2, 3, 4, 6]:
        part = extract_degree(residual, k)
        part_reduced = defaultdict(lambda: sp.Integer(0))
        for w, c in part.items():
            c_red = simplify_under_suzuki(c, p)
            if c_red != 0:
                part_reduced[w] = c_red
        nz = sum(1 for c in part_reduced.values() if c != 0)
        status = "vanishes ✓" if nz == 0 else f"has {nz} non-zero terms"
        print(f"  Degree {k}: {status}")

    print("\nExtracting R₇ (degree-7 residual) ...")
    r7 = extract_degree(residual, 7)
    r7_reduced = defaultdict(lambda: sp.Integer(0))
    for w, c in r7.items():
        c_red = simplify_under_suzuki(c, p)
        if c_red != 0:
            r7_reduced[w] = c_red
    nz7 = sum(1 for c in r7_reduced.values() if c != 0)
    print(f"  R₇ has {nz7} non-zero 7-letter words.")

    print("\n" + "=" * 70)
    print("Uniform bound: K = Σ_w |coef(w)| (at Suzuki p)")
    print("=" * 70)
    K_sum = sp.Integer(0)
    for w, c in r7_reduced.items():
        c_num = c.subs(p, suzuki_p_val_num)
        K_sum += sp.Abs(c_num)
    K_num = float(K_sum)
    print(f"  K ≈ {K_num:.6f}")
    print(f"  ‖R₇‖ ≤ K · max(‖A‖,‖B‖)^7 ≤ {K_num:.6f} · max(‖A‖,‖B‖)^7")

    # Also compute bound via A/B degree split:
    # Each word of length 7 has k A's and 7-k B's. Group by AB-signature.
    print("\n" + "=" * 70)
    print("Refined bound: ‖R₇‖ ≤ Σ_{k=0..7} Kₖ · ‖A‖^k · ‖B‖^(7-k)")
    print("=" * 70)
    K_k = [sp.Integer(0)] * 8
    for w, c in r7_reduced.items():
        n_a = sum(1 for x in w if x == 0)
        n_b = 7 - n_a
        c_num = c.subs(p, suzuki_p_val_num)
        K_k[n_a] += sp.Abs(c_num)
    for k in range(8):
        kk = float(K_k[k])
        if kk > 0:
            print(f"  K_{k} (‖A‖^{k}·‖B‖^{7-k}): {kk:.6f}")
    total_refined = sum(float(kk) for kk in K_k)
    print(f"  Total (should match crude K): {total_refined:.6f}")

    # Display top 10 largest word coefficients (for interest)
    print("\nLargest R₇ word coefficients (top 10 by absolute value):")
    items = sorted([(w, float(c.subs(p, suzuki_p_val_num))) for w, c in r7_reduced.items()],
                   key=lambda x: abs(x[1]), reverse=True)
    for w, v in items[:10]:
        word = ''.join('A' if x == 0 else 'B' for x in w)
        print(f"  {word}: {v:+.8f}")

    print("\n" + "=" * 70)
    print("Lean-ready snippet for Suzuki4ViaBCH.lean")
    print("=" * 70)
    # Round K up to a nice rational
    K_rational_num = int(K_num * 1000000 + 1) / 1000000  # round up
    print(f"def bchR7UniformCoefficient : ℝ := {K_rational_num}  -- upper bound on K from CAS")
    print(f"-- Precise value from CAS: K ≈ {K_num}")
    print(f"-- Per A/B-degree: {[float(kk) for kk in K_k]}")


if __name__ == "__main__":
    main()
