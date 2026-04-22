#!/usr/bin/env python3
"""
Compute the exact BCH prefactors for the Suzuki S₄ 4th-order Trotter error.

Approach: symbolic non-commutative algebra over Q[p], then specialize to
Suzuki p at the end.

Goal
----
Compute the τ⁵ coefficient of log(S₄(τ)) − τ·(A+B) for the palindromic
Suzuki S₄:

    S₄(τ) = S₂(pτ)·S₂(pτ)·S₂((1-4p)τ)·S₂(pτ)·S₂(pτ)

where S₂(s) = exp((s/2)A)·exp(sB)·exp((s/2)A) and p satisfies
`4p³ + (1-4p)³ = 0` (Suzuki cubic).

Verifies:
- Degree-2 terms vanish identically (palindromic).
- Degree-3 terms are proportional to `4p³+(1-4p)³`, hence vanish under Suzuki.
- Degree-4 terms vanish identically (palindromic).
- Degree-5 terms give R₅, a polynomial in p with 4-fold commutator content.

Outputs rational coefficients of R₅ in the Childs 8-commutator basis
(evaluated at exact Suzuki p).

Dependencies: sympy
Usage:       python3 compute_bch_prefactors.py
"""

import sympy as sp
from collections import defaultdict
from typing import Dict, Tuple


# ---------- Free non-commutative algebra over sympy Expr (Q[p]) ----------

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
        r[w] = sp.simplify(r[w] + c)
    for w, c in q.items():
        r[w] = sp.simplify(r[w] + c)
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in r.items() if c != 0})


def ncpoly_scale(p: NCPoly, c) -> NCPoly:
    c = sp.sympify(c)
    if c == 0:
        return ncpoly_zero()
    return defaultdict(lambda: sp.Integer(0),
                       {w: sp.simplify(c * v) for w, v in p.items()})


def ncpoly_neg(p: NCPoly) -> NCPoly:
    return ncpoly_scale(p, -1)


def ncpoly_sub(p: NCPoly, q: NCPoly) -> NCPoly:
    return ncpoly_add(p, ncpoly_neg(q))


def ncpoly_mul(p: NCPoly, q: NCPoly) -> NCPoly:
    r = ncpoly_zero()
    for w1, c1 in p.items():
        for w2, c2 in q.items():
            w = w1 + w2
            r[w] = sp.simplify(r[w] + c1 * c2)
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in r.items() if c != 0})


def ncpoly_truncate(p: NCPoly, max_degree: int) -> NCPoly:
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in p.items() if len(w) <= max_degree})


# ---------- Exp and Log truncated power series ----------

def ncpoly_exp(x: NCPoly, max_degree: int) -> NCPoly:
    """exp(x) truncated at max_degree. Assumes x has no constant term."""
    result = ncpoly_from_scalar(1)
    x_power = ncpoly_from_scalar(1)
    for k in range(1, max_degree + 1):
        x_power = ncpoly_truncate(ncpoly_mul(x_power, x), max_degree)
        result = ncpoly_add(result, ncpoly_scale(x_power, sp.Rational(1, sp.factorial(k))))
    return result


def ncpoly_log_one_plus(x: NCPoly, max_degree: int) -> NCPoly:
    """log(1+x) truncated at max_degree. Assumes x has no constant term."""
    result = ncpoly_zero()
    x_power = ncpoly_from_scalar(1)
    for k in range(1, max_degree + 1):
        x_power = ncpoly_truncate(ncpoly_mul(x_power, x), max_degree)
        sign = sp.Integer(1) if k % 2 == 1 else sp.Integer(-1)
        result = ncpoly_add(result, ncpoly_scale(x_power, sign / sp.Integer(k)))
    return result


# ---------- Commutators and Childs basis ----------

def commutator(p: NCPoly, q: NCPoly) -> NCPoly:
    return ncpoly_sub(ncpoly_mul(p, q), ncpoly_mul(q, p))


def childs_commutators() -> Dict[str, NCPoly]:
    A = ncpoly_a()
    B = ncpoly_b()
    BA = commutator(B, A)
    ABA = commutator(A, BA)
    BBA = commutator(B, BA)
    return {
        'C1': commutator(A, commutator(A, ABA)),
        'C2': commutator(A, commutator(A, BBA)),
        'C3': commutator(A, commutator(B, ABA)),
        'C4': commutator(A, commutator(B, BBA)),
        'C5': commutator(B, commutator(A, ABA)),
        'C6': commutator(B, commutator(A, BBA)),
        'C7': commutator(B, commutator(B, ABA)),
        'C8': commutator(B, commutator(B, BBA)),
    }


# ---------- Build S₂ and S₄ ----------

def strang_block_series(c, max_degree: int) -> NCPoly:
    """S₂(c·τ) = exp((c/2)A)·exp(c·B)·exp((c/2)A) with c symbolic scalar.
    Coefficients of words of length k give τ^k coefficient."""
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
    """S₄(τ) = S₂(pτ)·S₂(pτ)·S₂((1-4p)τ)·S₂(pτ)·S₂(pτ)."""
    q = sp.Integer(1) - 4 * p
    s_p = strang_block_series(p, max_degree)
    s_q = strang_block_series(q, max_degree)
    result = s_p
    for block in [s_p, s_q, s_p, s_p]:
        result = ncpoly_truncate(ncpoly_mul(result, block), max_degree)
    return result


def log_s4_residual(p, max_degree: int = 5) -> NCPoly:
    """log(S₄(τ)) - τ·(A+B), truncated at degree max_degree."""
    s4 = suzuki4_series(p, max_degree)
    y = defaultdict(lambda: sp.Integer(0), {w: c for w, c in s4.items() if w != ()})
    log_s4 = ncpoly_log_one_plus(y, max_degree)
    target = ncpoly_zero()
    target[(0,)] = sp.Integer(1)
    target[(1,)] = sp.Integer(1)
    return ncpoly_sub(log_s4, target)


def extract_degree(p: NCPoly, k: int) -> NCPoly:
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in p.items() if len(w) == k})


# ---------- Display and Suzuki substitution ----------

def simplify_under_suzuki(expr, p) -> sp.Expr:
    """Simplify an expression in p using Suzuki condition 4p³+(1-4p)³=0.

    Expanding: 4p³+(1-4p)³ = 4p³ + 1 - 12p + 48p² - 64p³ = -60p³ + 48p² - 12p + 1.
    Suzuki: -60p³ + 48p² - 12p + 1 = 0, i.e., 60p³ = 48p² - 12p + 1.

    So p³ = (48p² - 12p + 1)/60. We reduce mod this relation.
    """
    expr = sp.expand(expr)
    # Suzuki cubic: 60p³ - 48p² + 12p - 1 = 0, so p³ = (48p² - 12p + 1)/60.
    suzuki_reduction = (48 * p**2 - 12 * p + 1) / 60
    # Replace p^3, p^4, p^5 etc. iteratively
    for n in [5, 4, 3]:
        while expr.has(p**n):
            # p^n = p^(n-3) * p^3 = p^(n-3) * (48p²-12p+1)/60
            expr = expr.subs(p**n, p**(n-3) * suzuki_reduction)
            expr = sp.expand(expr)
    return sp.simplify(expr)


def display_ncpoly(p: NCPoly, suzuki_p_sym=None, suzuki_p_val=None, limit: int = 30):
    items = sorted([(w, c) for w, c in p.items() if c != 0],
                   key=lambda x: (len(x[0]), x[0]))
    if not items:
        print("  (zero)")
        return
    for w, c in items[:limit]:
        word_str = ''.join('A' if l == 0 else 'B' for l in w)
        c_display = c
        if suzuki_p_sym is not None:
            c_display = simplify_under_suzuki(c, suzuki_p_sym)
        if suzuki_p_val is not None:
            c_num = float(c_display.subs(suzuki_p_sym, suzuki_p_val))
            print(f"  [{c_display}]  ·  {word_str}   (≈ {c_num:.6f})")
        else:
            print(f"  {c_display} · {word_str}")
    if len(items) > limit:
        print(f"  ... ({len(items) - limit} more terms)")


# ---------- Main driver ----------

def main():
    p = sp.Symbol('p')
    # Suzuki p satisfies 4p³+(1-4p)³=0, i.e., 60p³-48p²+12p-1=0.
    # Numerically p = 1/(4 - 4^(1/3)) ≈ 0.414491.
    suzuki_p_val = 1 / (4 - sp.Rational(4, 1)**sp.Rational(1, 3))
    suzuki_p_val_num = float(suzuki_p_val)

    print("=" * 70)
    print("BCH prefactor computation for Suzuki S₄ (symbolic p)")
    print("=" * 70)
    print(f"Suzuki p = 1/(4 - 4^(1/3)) ≈ {suzuki_p_val_num:.6f}")
    print("(Carried symbolically; Suzuki cubic 4p³+(1-4p)³=0 applied at end.)")

    print("\nComputing log(S₄(τ)) - τ·(A+B) up to degree 5 ...")
    residual = log_s4_residual(p, max_degree=5)

    print("\n" + "=" * 70)
    print("Verification: orders 2, 3, 4 vanish under Suzuki condition")
    print("=" * 70)
    for k in range(2, 5):
        part = extract_degree(residual, k)
        part_reduced = defaultdict(lambda: sp.Integer(0))
        for w, c in part.items():
            c_red = simplify_under_suzuki(c, p)
            if c_red != 0:
                part_reduced[w] = c_red
        nz = sum(1 for c in part_reduced.values() if c != 0)
        status = "vanishes ✓" if nz == 0 else f"has {nz} terms ✗"
        print(f"  Degree {k}: {status}")
        if nz > 0:
            display_ncpoly(part_reduced, limit=3)

    print("\n" + "=" * 70)
    print("Degree-5 residual R₅ (the BCH quintic contribution)")
    print("=" * 70)
    r5 = extract_degree(residual, 5)
    r5_reduced = defaultdict(lambda: sp.Integer(0))
    for w, c in r5.items():
        c_red = simplify_under_suzuki(c, p)
        if c_red != 0:
            r5_reduced[w] = c_red
    print(f"  Non-zero 5-letter words: {sum(1 for c in r5_reduced.values() if c != 0)}")
    print("  First few terms (word, coefficient in p):")
    display_ncpoly(r5_reduced, suzuki_p_sym=p, suzuki_p_val=suzuki_p_val_num, limit=12)

    print("\n" + "=" * 70)
    print("Projection onto Childs 8-commutator basis")
    print("=" * 70)
    # Build linear system: Σ γᵢ · Cᵢ = R₅ (treating each word as a coordinate).
    childs = childs_commutators()
    childs_list = list(childs.items())

    all_words = sorted(set(r5_reduced.keys()) |
                       {w for _, poly in childs_list for w in poly.keys() if len(w) == 5})
    print(f"  Linear system: {len(all_words)} equations × {len(childs_list)} unknowns")

    gammas = sp.symbols('g1:9')
    # Build system
    M_rows = []
    b_entries = []
    for w in all_words:
        row = []
        for name, poly in childs_list:
            c = poly.get(w, sp.Integer(0))
            row.append(c)
        M_rows.append(row)
        b_entries.append(r5_reduced.get(w, sp.Integer(0)))

    M = sp.Matrix(M_rows)
    b = sp.Matrix(b_entries)

    # Solve with Gauss-Jordan (handles under-/over-determined systems symbolically)
    results = {}
    try:
        # gauss_jordan_solve returns (solution, free_symbols) for consistent systems
        sol, free_params = M.gauss_jordan_solve(b)
        print("\n  Projection via gauss_jordan_solve:")
        print(f"  Free parameters (basis over-completeness): {len(free_params)}")
        # Set free parameters to zero for a specific projection
        subst = {fp: 0 for fp in free_params}
        for i, (name, _) in enumerate(childs_list):
            g_raw = sol[i].subs(subst)
            g_red = simplify_under_suzuki(g_raw, p)
            g_simp = sp.simplify(g_red)
            results[name] = g_simp
        # Numerical values at Suzuki p
        for i, (name, _) in enumerate(childs_list):
            g = results[name]
            try:
                g_num = float(g.subs(p, suzuki_p_val_num))
                print(f"    {name}:  γ = {g}  (≈ {g_num:.6f})")
            except (TypeError, ValueError):
                print(f"    {name}:  γ = {g}")
    except Exception as e:
        print(f"  Gauss-Jordan solve failed: {e}")
        print("  Falling back: display R₅ word coefficients for manual projection.")

    # Comparison with Childs
    print("\n" + "=" * 70)
    print("Comparison with Childs (2021) heuristic coefficients")
    print("=" * 70)
    childs_vals = {
        'C1': 0.0047, 'C2': 0.0057, 'C3': 0.0046, 'C4': 0.0074,
        'C5': 0.0097, 'C6': 0.0097, 'C7': 0.0173, 'C8': 0.0284,
    }
    if results:
        for name in sorted(results.keys()):
            g = results[name]
            try:
                g_num = abs(float(g.subs(p, suzuki_p_val_num)))
                ch = childs_vals[name]
                marker = "tighter ✓" if g_num < ch else "~=" if abs(g_num - ch) < 1e-5 else "looser ✗"
                print(f"  {name}:  |γ| ≈ {g_num:.6f},  childs = {ch:.5f}  [{marker}]")
            except Exception:
                print(f"  {name}:  γ = {g}")

    # Emit Lean snippet
    if results:
        print("\n" + "=" * 70)
        print("Lean snippet (paste into Suzuki4ViaBCH.lean, replacing bchTightPrefactors)")
        print("=" * 70)
        print("def bchTightPrefactors : BCHPrefactors where")
        for i, name in enumerate(sorted(results.keys()), start=1):
            g = results[name]
            try:
                g_val = float(g.subs(p, suzuki_p_val_num))
                g_abs = abs(g_val)
                print(f"  γ{i} := {g_abs:.6f}  -- BCH-derived value at Suzuki p")
            except Exception:
                print(f"  γ{i} := /-unknown, symbolic expr:-/ sorry")
        for i in range(1, 9):
            print(f"  nonneg{i} := by norm_num")


if __name__ == "__main__":
    main()
