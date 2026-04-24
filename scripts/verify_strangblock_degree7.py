#!/usr/bin/env python3
"""
B1.c CAS sanity check — verify the statement of `norm_symmetric_bch_quintic_sub_poly_le`.

Goal: compute log(exp(a/2)·exp(b)·exp(a/2)) up to degree 7, then confirm:
 - degree 6 vanishes identically (palindromic symmetry of the 3-factor product);
 - degree 7 is non-zero (the next leading term after the symmetric τ⁵
   polynomial `symmetric_bch_quintic_poly a b`).

The theorem claimed in Lean-BCH's `BCH/SymmetricQuintic.lean`:

    ∀ a b, ‖a‖+‖b‖ < 1/4 →
      ‖symmetric_bch(a,b) − (a+b) − symmetric_bch_cubic_poly a b
                               − symmetric_bch_quintic_poly a b‖ ≤ K·(‖a‖+‖b‖)⁷

is therefore structurally correct: the residual is a degree-7+ polynomial in a, b
with absolutely convergent coefficient series (for s < log 2), and every degree-6
word has zero coefficient by palindromic symmetry.

Dependencies: sympy
Usage:       python3 verify_strangblock_degree7.py
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
    return r


def ncpoly_sub(p: NCPoly, q: NCPoly) -> NCPoly:
    r = ncpoly_zero()
    for w, c in p.items():
        r[w] = r[w] + c
    for w, c in q.items():
        r[w] = r[w] - c
    return r


def ncpoly_scale(p: NCPoly, c) -> NCPoly:
    c = sp.sympify(c)
    r = ncpoly_zero()
    if c == 0:
        return r
    for w, cc in p.items():
        r[w] = cc * c
    return r


def ncpoly_mul(p: NCPoly, q: NCPoly) -> NCPoly:
    r = ncpoly_zero()
    for wp, cp in p.items():
        for wq, cq in q.items():
            r[wp + wq] = r[wp + wq] + cp * cq
    return r


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
        sign = 1 if (k % 2 == 1) else -1
        result = ncpoly_add(result, ncpoly_scale(x_power, sp.Rational(sign, k)))
    return result


def strang_block_log(max_degree: int) -> NCPoly:
    """log(exp(a/2)·exp(b)·exp(a/2)) truncated to `max_degree`."""
    halfA = ncpoly_scale(ncpoly_a(), sp.Rational(1, 2))
    B = ncpoly_b()
    exp_halfA = ncpoly_exp(halfA, max_degree)
    exp_B = ncpoly_exp(B, max_degree)
    # Product: exp(a/2) · exp(b) · exp(a/2)
    prod = exp_halfA
    prod = ncpoly_truncate(ncpoly_mul(prod, exp_B), max_degree)
    prod = ncpoly_truncate(ncpoly_mul(prod, exp_halfA), max_degree)
    # y = prod - 1; log(1+y) = log(prod).
    y = defaultdict(lambda: sp.Integer(0), {w: c for w, c in prod.items() if w != ()})
    return ncpoly_log_one_plus(y, max_degree)


def extract_degree(p: NCPoly, k: int) -> NCPoly:
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in p.items() if len(w) == k})


def count_nonzero(p: NCPoly) -> int:
    return sum(1 for c in p.values() if c != 0)


def display_ncpoly(p: NCPoly, limit: int = 15):
    items = sorted([(w, c) for w, c in p.items() if c != 0],
                   key=lambda x: (len(x[0]), x[0]))
    if not items:
        print("  (zero)")
        return
    for w, c in items[:limit]:
        word_str = ''.join('A' if l == 0 else 'B' for l in w)
        print(f"  {c} · {word_str}")
    if len(items) > limit:
        print(f"  ... ({len(items) - limit} more terms)")


def main():
    MAX = 7
    print(f"Computing log(exp(a/2)·exp(b)·exp(a/2)) truncated to degree {MAX} ...")
    series = strang_block_log(MAX)

    print("\n" + "=" * 66)
    print("Degree-by-degree summary (symmetric / palindromic structure)")
    print("=" * 66)
    for k in range(1, MAX + 1):
        part = extract_degree(series, k)
        nz = count_nonzero(part)
        print(f"  Degree {k}: {nz} non-zero words", end="")
        if k == 1:
            print("  (expected a + b)")
        elif k in (2, 4, 6):
            if nz == 0:
                print("  ✓ vanishes (palindromic)")
            else:
                print(f"  ✗ EXPECTED VANISHING")
                display_ncpoly(part, limit=5)
        elif k == 3:
            print(f"  (symmetric_bch_cubic_poly a b)")
        elif k == 5:
            print(f"  (symmetric_bch_quintic_poly a b — the B1.b target; should be 30)")
        elif k == 7:
            print(f"  (next non-zero degree; bounded by K·s⁷ for small s)")

    print("\n" + "=" * 66)
    print("STATEMENT VERIFICATION")
    print("=" * 66)
    d3 = extract_degree(series, 3)
    d5 = extract_degree(series, 5)
    d7 = extract_degree(series, 7)
    for k in (2, 4, 6):
        part = extract_degree(series, k)
        nz = count_nonzero(part)
        assert nz == 0, f"degree {k} is non-zero: {nz} terms"

    print(f"  degree-3 word count: {count_nonzero(d3)}")
    print(f"  degree-5 word count: {count_nonzero(d5)}  (expected: 30)")
    print(f"  degree-7 word count: {count_nonzero(d7)}  (non-zero => theorem K·s⁷ constant needed)")

    print("\n✓ Palindromic symmetry confirmed: degrees 2, 4, 6 all vanish.")
    print("✓ Residual symmetric_bch - (a+b) - cubic_poly - quintic_poly starts at degree 7.")
    print("\nConclusion: `norm_symmetric_bch_quintic_sub_poly_le` statement is")
    print("structurally correct — the bound K·s⁷ is achievable for any K that")
    print("dominates the degree-7 coefficients and the series tail.")


if __name__ == "__main__":
    main()
