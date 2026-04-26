#!/usr/bin/env python3
"""
Extract the symbolic τ⁵ coefficient (Z₅) of the BCH expansion
    bch(a, b) = log(exp(a) * exp(b))
              = a + b + ½[a,b] + Z₃(a,b) + Z₄(a,b) + Z₅(a,b) + O(·^6)

as a sum of 5-letter words in {a, b} with rational coefficients.

Strategy:
1. Use the existing NCPoly infrastructure from compute_bch_prefactors.py.
2. Treat a, b as length-1 NC monomials; build exp(a) * exp(b) - 1 to degree 5.
3. Apply log(1+·) to get the BCH expansion to degree 5.
4. Extract the degree-5 part. Print all non-zero 5-letter words.

This output will be lifted to Lean as the body of `bch_quintic_term` in
BCH/Basic.lean.

Usage:
    python3 extract_bch_z5.py
"""

import sympy as sp
from collections import defaultdict
from typing import Dict, Tuple

# Re-use NCPoly machinery from compute_bch_prefactors.py
from compute_bch_prefactors import (
    NCPoly,
    ncpoly_zero,
    ncpoly_from_scalar,
    ncpoly_a,
    ncpoly_b,
    ncpoly_add,
    ncpoly_scale,
    ncpoly_neg,
    ncpoly_sub,
    ncpoly_mul,
    ncpoly_truncate,
    ncpoly_exp,
    ncpoly_log_one_plus,
)


def word_to_str(w: Tuple[int, ...]) -> str:
    """Convert a word (0-tuple = a, 1-tuple = b) to a string like 'aabba'."""
    return ''.join('a' if l == 0 else 'b' for l in w)


def word_to_lean(w: Tuple[int, ...]) -> str:
    """Convert a word to a Lean monomial expression like 'a * a * b * b * a'."""
    parts = ['a' if l == 0 else 'b' for l in w]
    return ' * '.join(parts)


def main():
    # Build exp(a) * exp(b) - 1 to degree 5
    a = ncpoly_a()
    b = ncpoly_b()
    exp_a = ncpoly_exp(a, max_degree=5)
    exp_b = ncpoly_exp(b, max_degree=5)
    prod = ncpoly_truncate(ncpoly_mul(exp_a, exp_b), max_degree=5)
    # y = exp(a) * exp(b) - 1 (drop constant term)
    y = defaultdict(lambda: sp.Integer(0),
                    {w: c for w, c in prod.items() if w != ()})
    # bch(a, b) = log(1 + y)
    bch_full = ncpoly_log_one_plus(y, max_degree=5)

    # Verify low-degree pieces match the expected formula
    # Degree 1: a + b
    deg1 = {w: c for w, c in bch_full.items() if len(w) == 1}
    assert deg1.get((0,)) == 1 and deg1.get((1,)) == 1, f"deg1 mismatch: {dict(deg1)}"
    # Degree 2: ½(ab - ba) = ½[a,b]
    deg2 = {w: c for w, c in bch_full.items() if len(w) == 2}
    expected_deg2 = {(0, 1): sp.Rational(1, 2), (1, 0): sp.Rational(-1, 2)}
    assert dict(deg2) == expected_deg2, f"deg2 mismatch: {dict(deg2)} vs {expected_deg2}"

    # Extract Z₅ = degree-5 part
    z5 = {w: c for w, c in bch_full.items() if len(w) == 5}
    z5_sorted = sorted(z5.items(), key=lambda x: x[0])

    print("=" * 70)
    print("Z₅ : τ⁵ coefficient of bch(a, b) = log(exp(a) * exp(b))")
    print(f"Number of non-zero 5-letter words: {len(z5_sorted)}")
    print("=" * 70)
    print()
    print("As a sum of monomials (NC-polynomial form):")
    print()
    for w, c in z5_sorted:
        word_str = word_to_str(w)
        # Print the rational coefficient as p/q
        if c.is_Rational:
            num, den = c.p, c.q
            sign = '+' if num > 0 else '-'
            print(f"  {sign} {abs(num)}/{den}  ·  {word_str}")
        else:
            print(f"    {c}  ·  {word_str}")
    print()

    # Print as a Lean expression (each word as a noncomm product)
    print("=" * 70)
    print("Lean expression form (for inserting into BCH/Basic.lean):")
    print("  bch_quintic_term 𝕂 a b :=")
    print("=" * 70)
    print()
    # Group by denominator for cleaner Lean code
    by_denom: Dict[int, list] = defaultdict(list)
    for w, c in z5_sorted:
        if c.is_Rational:
            by_denom[c.q].append((w, c))

    # Print in (denom)⁻¹ • (sum of integer-coef monomials) form
    pieces = []
    for denom in sorted(by_denom.keys()):
        terms = by_denom[denom]
        # Build sum of (numerator_i * monomial_i)
        first = True
        line_parts = [f"  ({denom} : 𝕂)⁻¹ • ("]
        for w, c in terms:
            num = c.p
            mono = word_to_lean(w)
            if first:
                if num == 1:
                    line_parts.append(f"{mono}")
                elif num == -1:
                    line_parts.append(f"-({mono})")
                else:
                    line_parts.append(f"{num} * ({mono})")
                first = False
            else:
                if num > 0:
                    if num == 1:
                        line_parts.append(f" + {mono}")
                    else:
                        line_parts.append(f" + {num} * ({mono})")
                else:
                    if num == -1:
                        line_parts.append(f" - {mono}")
                    else:
                        line_parts.append(f" - {abs(num)} * ({mono})")
        line_parts.append(")")
        pieces.append(''.join(line_parts))

    for i, piece in enumerate(pieces):
        if i == 0:
            print(piece)
        else:
            print(f"  +\n{piece}")
    print()

    # Common-denominator form: factor out the LCM
    from math import gcd
    from functools import reduce

    def lcm(a, b):
        return a * b // gcd(a, b)

    if z5_sorted:
        all_denoms = [c.q for w, c in z5_sorted if c.is_Rational]
        L = reduce(lcm, all_denoms)
        print("=" * 70)
        print(f"Common-denominator form (LCM = {L}):")
        print(f"  Z₅ = (1/{L}) · Σ (integer_coefficient_i) · monomial_i")
        print("=" * 70)
        print()
        print(f"  ({L} : 𝕂)⁻¹ • (")
        first = True
        for w, c in z5_sorted:
            if c.is_Rational:
                k = c.p * (L // c.q)
                mono = word_to_lean(w)
                if first:
                    if k == 1:
                        print(f"    {mono}")
                    elif k == -1:
                        print(f"    -({mono})")
                    else:
                        print(f"    {k} * ({mono})")
                    first = False
                else:
                    if k > 0:
                        if k == 1:
                            print(f"    + {mono}")
                        else:
                            print(f"    + {k} * ({mono})")
                    else:
                        if k == -1:
                            print(f"    - {mono}")
                        else:
                            print(f"    - {abs(k)} * ({mono})")
        print(f"  )")

    # Sanity check: sum of all coefficients vanishes (Lie polynomial property?)
    # Actually that's not generally true. Let's just verify Z₅ has the right
    # number of monomials: free associative algebra on {a,b} has 2^5 = 32
    # words at degree 5, but Z₅ as a Lie polynomial has at most ~6 free Lie
    # algebra dimensions. The associative form has more monomials but they
    # collapse via Jacobi. Print the count for sanity.
    print()
    print(f"Sanity: total non-zero monomials = {len(z5_sorted)}")
    print(f"Total possible 5-letter words on {{a,b}} = {2**5}")


if __name__ == "__main__":
    main()
