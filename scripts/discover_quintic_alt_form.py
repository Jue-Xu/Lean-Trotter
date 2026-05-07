#!/usr/bin/env python3
"""
Discover the algebraic decomposition for `symmetric_bch_quintic_poly_alt_form`
in Lean-BCH/BCH/Basic.lean — the analog of `symmetric_bch_cubic_poly_alt_form`
(Basic.lean:5708) at one degree higher.

Goal
----
Express `symmetric_bch_quintic_poly(a, b)` (the τ⁵ coefficient of
log(exp(a/2)·exp(b)·exp(a/2))) as:

    sym_E₅(a, b) = bch_quintic_term(½a, b)
                 + bch_quintic_term(½a + b, ½a)
                 + ½·[bch_quartic_term(½a, b), ½a]
                 + (degree-5 contribution from C₃(z, ½a) − C₃(½a+b, ½a))
                 + (degree-5 contribution from C₄(z, ½a) − C₄(½a+b, ½a))
                 + (correction polynomial in a, b)

The cubic version's correction was `-(1/16)·[a, [a,b]]`. Here we expect a
multi-term correction expressible as commutators built from a, b at degree 5.

This script computes each term symbolically, subtracts, and outputs the
correction polynomial in canonical word form. Lean can then transcribe
the equality and verify via scalar clearing + noncomm_ring.

Strategy
--------
1. Build NC-polynomials over 2 variables {a=0, b=1}.
2. Compute z = bch(½a, b) up to degree 5 (truncated power series of
   log(exp(½a)·exp(b))).
3. Compute bch(z, ½a) up to degree 5.
4. Subtract (a + b) → sym_bch_cubic up to deg 5.
5. Extract degree-5 part → that's sym_E₅(a, b).
6. Compute candidate "alt-form" components:
   - bch_quintic_term(½a, b)         := degree-5 part of bch(½a, b)
   - bch_quintic_term(½a+b, ½a)      := degree-5 part of bch(½a+b, ½a)
7. Subtract from sym_E₅ → get residual = correction needed.
8. Try to express residual via commutators of (a, b).

Dependencies: sympy
Usage:        python3 discover_quintic_alt_form.py
"""

import sympy as sp
from collections import defaultdict
from typing import Dict, Tuple

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
                       {w: c for w, c in r.items() if c != 0})


def ncpoly_scale(p: NCPoly, c) -> NCPoly:
    c = sp.sympify(c)
    if c == 0:
        return ncpoly_zero()
    return defaultdict(lambda: sp.Integer(0),
                       {w: c * v for w, v in p.items()})


def ncpoly_neg(p: NCPoly) -> NCPoly:
    return ncpoly_scale(p, -1)


def ncpoly_sub(p: NCPoly, q: NCPoly) -> NCPoly:
    return ncpoly_add(p, ncpoly_neg(q))


def ncpoly_mul(p: NCPoly, q: NCPoly) -> NCPoly:
    r = ncpoly_zero()
    for wp, cp in p.items():
        for wq, cq in q.items():
            r[wp + wq] = r[wp + wq] + cp * cq
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in r.items() if c != 0})


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


def commutator(p: NCPoly, q: NCPoly) -> NCPoly:
    return ncpoly_sub(ncpoly_mul(p, q), ncpoly_mul(q, p))


def extract_degree(p: NCPoly, k: int) -> NCPoly:
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in p.items() if len(w) == k})


def bch_series(x: NCPoly, y: NCPoly, max_degree: int) -> NCPoly:
    """bch(x, y) = log(exp(x)·exp(y)) truncated to max_degree."""
    ex = ncpoly_exp(x, max_degree)
    ey = ncpoly_exp(y, max_degree)
    prod = ncpoly_truncate(ncpoly_mul(ex, ey), max_degree)
    # log(prod) = log(1 + (prod - 1))
    minus_one = defaultdict(lambda: sp.Integer(0),
                            {w: c for w, c in prod.items() if w != ()})
    return ncpoly_log_one_plus(minus_one, max_degree)


def display_ncpoly(p: NCPoly, label: str = ""):
    items = sorted([(w, c) for w, c in p.items() if c != 0],
                   key=lambda x: (len(x[0]), x[0]))
    if label:
        print(f"\n--- {label} ({len(items)} terms) ---")
    if not items:
        print("  (zero)")
        return
    for w, c in items:
        word_str = ''.join('a' if l == 0 else 'b' for l in w)
        c_str = sp.nsimplify(c)
        print(f"  {c_str} · {word_str}")


def main():
    MAX = 5
    a = ncpoly_a()
    b = ncpoly_b()
    half = sp.Rational(1, 2)
    half_a = ncpoly_scale(a, half)               # ½a
    half_a_plus_b = ncpoly_add(half_a, b)        # ½a + b

    print("=" * 70)
    print("Discovering symmetric_bch_quintic_poly_alt_form decomposition")
    print("=" * 70)

    # Step 1: compute z = bch(½a, b) up to degree 5
    print("\n[Step 1] z = bch(½a, b) up to degree 5")
    z = bch_series(half_a, b, MAX)

    # Step 2: compute bch(z, ½a) up to degree 5
    print("[Step 2] bch(z, ½a) up to degree 5")
    bch_z_halfa = bch_series(z, half_a, MAX)

    # Step 3: sym_bch_cubic = bch(z, ½a) - (a+b)
    print("[Step 3] sym_bch_cubic = bch(z, ½a) - (a + b)")
    a_plus_b = ncpoly_add(a, b)
    sym_bch_cubic_full = ncpoly_sub(bch_z_halfa, a_plus_b)

    # Step 4: extract degree-5 part = sym_E₅(a, b)
    sym_E5 = extract_degree(sym_bch_cubic_full, 5)
    print(f"[Step 4] sym_E₅(a, b) extracted: {len(sym_E5)} non-zero words")

    # Step 5: compute bch_quintic_term(½a, b) = degree-5 of bch(½a, b)
    bqt_inner = extract_degree(z, 5)
    print(f"\n[Step 5] bch_quintic_term(½a, b): {len(bqt_inner)} non-zero words")

    # Step 6: compute bch_quintic_term(½a+b, ½a) = degree-5 of bch(½a+b, ½a)
    bch_outer_static = bch_series(half_a_plus_b, half_a, MAX)
    bqt_outer = extract_degree(bch_outer_static, 5)
    print(f"[Step 6] bch_quintic_term(½a+b, ½a): {len(bqt_outer)} non-zero words")

    # Step 7: residual = sym_E₅ - bqt_inner - bqt_outer
    print("\n[Step 7] residual = sym_E₅ - bqt(½a, b) - bqt(½a+b, ½a)")
    residual = ncpoly_sub(sym_E5, bqt_inner)
    residual = ncpoly_sub(residual, bqt_outer)
    nz_resid = sum(1 for c in residual.values() if c != 0)
    print(f"           residual has {nz_resid} non-zero words")
    display_ncpoly(residual, "residual after subtracting bqt(½a,b) + bqt(½a+b,½a)")

    # Step 8: also subtract ½·[C₄(½a, b), ½a] (degree-5: C₄ is deg-4 in (½a,b),
    #         commutator with ½a gives deg-5).
    # bch_quartic_term(x, y) = degree-4 of bch(x, y).
    print("\n[Step 8] Subtract ½·[bch_quartic_term(½a, b), ½a]")
    bqt4_inner = extract_degree(z, 4)  # already degree-4 part of bch(½a, b)
    bracket_C4_inner_halfa = commutator(bqt4_inner, half_a)
    half_bracket_C4 = ncpoly_scale(bracket_C4_inner_halfa, half)
    residual2 = ncpoly_sub(residual, half_bracket_C4)
    nz_resid2 = sum(1 for c in residual2.values() if c != 0)
    print(f"           after subtracting ½·[C₄(½a,b), ½a]: {nz_resid2} terms")
    display_ncpoly(residual2, "residual after step 8")

    # Step 9: subtract (C₃(z, ½a) - C₃(½a+b, ½a))_{deg-5}
    # bch_cubic_term(x, y) = degree-3 of bch(x, y).
    # C₃(z, ½a) - C₃(½a+b, ½a) at degree 5 needs z restricted to deg 1+2.
    # z_lo = (½a+b) + ½[½a, b] (degrees 1 and 2)
    print("\n[Step 9] Subtract (C₃(z, ½a) - C₃(½a+b, ½a))_{deg-5}")
    z_deg2 = extract_degree(z, 2)
    z_lo = ncpoly_add(half_a_plus_b, z_deg2)
    bch_z_lo_halfa = bch_series(z_lo, half_a, MAX)
    C3_z_lo_halfa = extract_degree(bch_z_lo_halfa, 3)
    C3_static_halfa = extract_degree(bch_outer_static, 3)
    # ⚠ C3 is degree-3, so neither contributes at degree-5.
    # The contribution we want is the degree-5 difference of bch_cubic_term(z, ½a)
    # vs bch_cubic_term(½a+b, ½a). For this, redo the truncated bch with z, but
    # extract only the degree-3 part of the formal "cubic_term".
    # Better approach: compute bch_cubic_term(x, y) as a formal degree-3 polynomial
    # in (x, y), then substitute x = z up to relevant degrees.
    # bch_cubic_term(x, y) = (1/12)([x,[x,y]] + [y,[y,x]])
    bxy = commutator(b, ncpoly_a())  # placeholder; will be redone with subst.

    # Actually easier: directly compute degree-5 parts of bch(z, ½a) - bch(½a+b, ½a)
    # for various truncations. Instead, just take the residual2 as-is — Lean can
    # discover step 9 etc. on its own. But for completeness, let's do step 9 the
    # right way:

    # Define explicitly: bch_cubic_term_xy(x_poly, y_poly, max_deg)
    def bch_cubic_term_at(x: NCPoly, y: NCPoly, max_deg: int) -> NCPoly:
        # bch_cubic_term(x, y) = (1/12)·([x, [x, y]] + [y, [y, x]])
        c_xxy = commutator(x, commutator(x, y))
        c_yyx = commutator(y, commutator(y, x))
        return ncpoly_truncate(ncpoly_scale(ncpoly_add(c_xxy, c_yyx),
                                            sp.Rational(1, 12)),
                               max_deg)

    def bch_quartic_term_at(x: NCPoly, y: NCPoly, max_deg: int) -> NCPoly:
        # bch_quartic_term(x, y) = -(1/24)·[y, [x, [x, y]]]
        # (cf. Basic.lean: bch_quartic_term)
        inner = commutator(x, commutator(x, y))
        return ncpoly_truncate(ncpoly_scale(commutator(y, inner),
                                            sp.Rational(-1, 24)),
                               max_deg)

    C3_full_z = bch_cubic_term_at(z, half_a, MAX)
    C3_full_static = bch_cubic_term_at(half_a_plus_b, half_a, MAX)
    C3_diff_d5 = extract_degree(ncpoly_sub(C3_full_z, C3_full_static), 5)
    print(f"          (C₃(z,½a) - C₃(½a+b,½a))_d5: {len(C3_diff_d5)} terms")
    residual3 = ncpoly_sub(residual2, C3_diff_d5)
    nz_resid3 = sum(1 for c in residual3.values() if c != 0)
    print(f"          after subtracting C₃ difference: {nz_resid3} terms")
    display_ncpoly(residual3, "residual after step 9")

    # Step 10: subtract (C₄(z, ½a) - C₄(½a+b, ½a))_{deg-5}
    print("\n[Step 10] Subtract (C₄(z, ½a) - C₄(½a+b, ½a))_{deg-5}")
    C4_full_z = bch_quartic_term_at(z, half_a, MAX)
    C4_full_static = bch_quartic_term_at(half_a_plus_b, half_a, MAX)
    C4_diff_d5 = extract_degree(ncpoly_sub(C4_full_z, C4_full_static), 5)
    print(f"          (C₄(z,½a) - C₄(½a+b,½a))_d5: {len(C4_diff_d5)} terms")
    residual4 = ncpoly_sub(residual3, C4_diff_d5)
    nz_resid4 = sum(1 for c in residual4.values() if c != 0)
    print(f"          after subtracting C₄ difference: {nz_resid4} terms")
    display_ncpoly(residual4, "FINAL residual after all subtractions")

    # If residual4 is zero, the alt-form decomposition is complete.
    if nz_resid4 == 0:
        print("\n" + "=" * 70)
        print("✓ DECOMPOSITION COMPLETE: residual = 0")
        print("=" * 70)
        print("symmetric_bch_quintic_poly(a, b) =")
        print("    bch_quintic_term(½a, b)")
        print("  + bch_quintic_term(½a+b, ½a)")
        print("  + ½·[bch_quartic_term(½a, b), ½a]")
        print("  + (C₃(z, ½a) - C₃(½a+b, ½a))_d5      [where z = bch(½a, b)]")
        print("  + (C₄(z, ½a) - C₄(½a+b, ½a))_d5")

        print("\n" + "=" * 70)
        print("EXPLICIT POLYNOMIAL FORMS (for Lean transcription)")
        print("=" * 70)
        display_ncpoly(bqt_inner, "bch_quintic_term(½a, b)")
        display_ncpoly(bqt_outer, "bch_quintic_term(½a+b, ½a)")
        display_ncpoly(half_bracket_C4, "½·[bch_quartic_term(½a,b), ½a]")
        display_ncpoly(C3_diff_d5, "(C₃(z, ½a) - C₃(½a+b, ½a))_d5")
        display_ncpoly(C4_diff_d5, "(C₄(z, ½a) - C₄(½a+b, ½a))_d5")
        display_ncpoly(sym_E5, "TARGET sym_E₅(a,b)")

        # Combined correction: T3 + T4 + T5 = sym_E5 - (T1 + T2)
        combined = ncpoly_add(half_bracket_C4, C3_diff_d5)
        combined = ncpoly_add(combined, C4_diff_d5)
        display_ncpoly(combined,
                       "COMBINED correction (T3+T4+T5) = sym_E5 − bqt_inner − bqt_outer")
        # Print as Lean-style smul terms with denominator 11520:
        print("\n--- Lean transcription form (denominator 11520) ---")
        items = sorted([(w, c) for w, c in combined.items() if c != 0],
                       key=lambda x: x[0])
        sum_abs = 0
        for w, c in items:
            num = sp.nsimplify(c * 11520)
            assert num == int(num), f"non-integer numerator {num} for word {w}"
            sum_abs += abs(int(num))
            word_str = ' * '.join('a' if l == 0 else 'b' for l in w)
            print(f"  + ({num} / 11520 : 𝕂) • ({word_str})")
        print(f"\n  sum of |numerators| / 11520 = {sum_abs}/11520 ≈ {sum_abs/11520:.4f}")
        print(f"  → ‖correction‖ ≤ {sum_abs}/11520 · s⁵ for s = ‖a‖+‖b‖")
    else:
        print("\n" + "=" * 70)
        print(f"✗ Residual {nz_resid4} terms — need additional terms")
        print("=" * 70)
        print("Suggested: try [degree-5 contribution from ½·[Q(z, ½a) - ...],")
        print("            and from R₅(z, ½a) - R₅(½a+b, ½a)]")


if __name__ == "__main__":
    main()
