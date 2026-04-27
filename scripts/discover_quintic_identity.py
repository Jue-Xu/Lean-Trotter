#!/usr/bin/env python3
"""
Discover the algebraic decomposition for `quintic_identity` in
Lean-BCH/BCH/Basic.lean — the analog of `quartic_identity` (Basic.lean:1898)
at one degree higher.

Strategy:
1. Build NC-polynomials over 4 variables {a, b, ea, eb} (no relation
   imposed between ea/eb and a/b — they're treated as opaque).
2. Build all the auxiliary quantities (D₁, D₂, E₁, E₂, F₁, F₂, G₁, G₂,
   P, Q, z, y, C₃, C₄) as NC-polynomials.
3. Verify quartic_identity holds (sanity check): LHS_q − RHS_q == 0.
4. Compute LHS_quintic = ½W_H1 + ⅓z³ − ¼y⁴ − C₃ − C₄ as NC-polynomial.
5. Try various candidate RHS shapes and check which one (if any) satisfies
   LHS_quintic = RHS_quintic.

Variable encoding: tuples of integers 0=a, 1=b, 2=ea, 3=eb. Each tuple
represents a left-associated NC monomial.

Usage:    python3 discover_quintic_identity.py
"""

import sympy as sp
from collections import defaultdict
from typing import Dict, Tuple

# Re-implement minimal NCPoly machinery over 4 variables {a=0, b=1, ea=2, eb=3}.

NCPoly = Dict[Tuple[int, ...], sp.Expr]


def npz() -> NCPoly:
    return defaultdict(lambda: sp.Integer(0))


def npc(c) -> NCPoly:
    """Constant scalar."""
    r = npz()
    c = sp.sympify(c)
    if c != 0:
        r[()] = c
    return r


def npv(i: int) -> NCPoly:
    """Variable v_i."""
    r = npz()
    r[(i,)] = sp.Integer(1)
    return r


def add(p: NCPoly, q: NCPoly) -> NCPoly:
    r = npz()
    for w, c in p.items():
        r[w] = r[w] + c
    for w, c in q.items():
        r[w] = r[w] + c
    return defaultdict(lambda: sp.Integer(0),
                       {w: sp.simplify(c) for w, c in r.items() if sp.simplify(c) != 0})


def scale(p: NCPoly, c) -> NCPoly:
    c = sp.sympify(c)
    if c == 0:
        return npz()
    return defaultdict(lambda: sp.Integer(0),
                       {w: sp.simplify(c * v) for w, v in p.items()})


def neg(p: NCPoly) -> NCPoly:
    return scale(p, -1)


def sub(p: NCPoly, q: NCPoly) -> NCPoly:
    return add(p, neg(q))


def mul(p: NCPoly, q: NCPoly) -> NCPoly:
    r = npz()
    for w1, c1 in p.items():
        for w2, c2 in q.items():
            w = w1 + w2
            r[w] = r[w] + c1 * c2
    return defaultdict(lambda: sp.Integer(0),
                       {w: sp.simplify(c) for w, c in r.items() if sp.simplify(c) != 0})


def is_zero(p: NCPoly) -> bool:
    return all(sp.simplify(c) == 0 for c in p.values())


def num_terms(p: NCPoly) -> int:
    return len({w for w, c in p.items() if sp.simplify(c) != 0})


def fmt_word(w: Tuple[int, ...]) -> str:
    return ''.join('aabe' if False else ['a', 'b', 'A', 'B'][i] for i in w)
    # 'A' = ea, 'B' = eb (capital for the exp's)


def print_poly(p: NCPoly, name: str, limit: int = 30):
    items = sorted(p.items(), key=lambda x: (len(x[0]), x[0]))
    items = [(w, c) for w, c in items if sp.simplify(c) != 0]
    print(f"  {name}: {len(items)} non-zero terms.")
    if len(items) <= limit:
        for w, c in items:
            print(f"    {sp.simplify(c)}  ·  {fmt_word(w)}")
    else:
        for w, c in items[:limit]:
            print(f"    {sp.simplify(c)}  ·  {fmt_word(w)}")
        print(f"    ... ({len(items) - limit} more)")


# -------------------------------------------------------------------------
# Build the auxiliary quantities
# -------------------------------------------------------------------------

a = npv(0)
b = npv(1)
ea = npv(2)
eb = npv(3)
one = npc(1)

a2 = mul(a, a); a3 = mul(a, a2); a4 = mul(a, a3); a5 = mul(a, a4)
b2 = mul(b, b); b3 = mul(b, b2); b4 = mul(b, b3); b5 = mul(b, b4)

# D₁ = ea - 1 - a, D₂ = eb - 1 - b
D1 = sub(sub(ea, one), a)
D2 = sub(sub(eb, one), b)

# z = a + b
z = add(a, b)

# y = ea·eb - 1
y = sub(mul(ea, eb), one)

# P = y - z
P = sub(y, z)

# E₁ = D₁ - ½a², E₂ = D₂ - ½b²
E1 = sub(D1, scale(a2, sp.Rational(1, 2)))
E2 = sub(D2, scale(b2, sp.Rational(1, 2)))

# Q = a·D₂ + D₁·b + D₁·D₂
Q = add(add(mul(a, D2), mul(D1, b)), mul(D1, D2))

# F₁ = E₁ - ⅙a³, F₂ = E₂ - ⅙b³
F1 = sub(E1, scale(a3, sp.Rational(1, 6)))
F2 = sub(E2, scale(b3, sp.Rational(1, 6)))

# G₁ = F₁ - (1/24)a⁴, G₂ = F₂ - (1/24)b⁴
G1 = sub(F1, scale(a4, sp.Rational(1, 24)))
G2 = sub(F2, scale(b4, sp.Rational(1, 24)))

# H₁ = G₁ - (1/120)a⁵, H₂ = G₂ - (1/120)b⁵  (sextic exp remainders)
H1 = sub(G1, scale(a5, sp.Rational(1, 120)))
H2 = sub(G2, scale(b5, sp.Rational(1, 120)))

# C₃ = bch_cubic_term = (1/12)([a,[a,b]] + [b,[b,a]])
ab = mul(a, b); ba = mul(b, a)
ab_ba = sub(ab, ba)        # [a, b] = ab - ba
ba_ab = sub(ba, ab)        # [b, a] = ba - ab
a_ab_ba = sub(mul(a, ab_ba), mul(ab_ba, a))   # [a, [a, b]]
b_ba_ab = sub(mul(b, ba_ab), mul(ba_ab, b))   # [b, [b, a]]
C3 = scale(add(a_ab_ba, b_ba_ab), sp.Rational(1, 12))

# C₄ = bch_quartic_term = -(1/24)[b, [a, [a, b]]]
b_a_ab_ba = sub(mul(b, a_ab_ba), mul(a_ab_ba, b))   # [b, [a, [a, b]]]
C4 = scale(b_a_ab_ba, sp.Rational(-1, 24))

# W_H1 = 2·(E₁ + E₂ + a·D₂ + D₁·b + D₁·D₂) - z·P - P·z - P²
inner_W = add(add(add(add(E1, E2), mul(a, D2)), mul(D1, b)), mul(D1, D2))
W = sub(sub(sub(scale(inner_W, 2), mul(z, P)), mul(P, z)), mul(P, P))

# y² = (ea·eb - 1)²
y2 = mul(y, y)
# y³, y⁴, y⁵
y3 = mul(y, y2)
y4 = mul(y, y3)
y5 = mul(y, y4)

# z³ = (a+b)³
z2 = mul(z, z)
z3 = mul(z, z2)


def main():
    print("=" * 70)
    print("Step 1: Verify quartic_identity (sanity check)")
    print("=" * 70)

    # quartic LHS = ½W + ⅓z³ - C₃
    LHS_q = sub(add(scale(W, sp.Rational(1, 2)),
                     scale(z3, sp.Rational(1, 3))), C3)

    # quartic RHS = F₁ + F₂ + a·E₂ + E₁·b + D₁·D₂
    #             - ½(z·(E₁+E₂+Q) + (E₁+E₂+Q)·z) - ½P²
    E12pQ = add(add(E1, E2), Q)
    RHS_q = sub(
        sub(
            add(add(add(add(F1, F2), mul(a, E2)), mul(E1, b)), mul(D1, D2)),
            scale(add(mul(z, E12pQ), mul(E12pQ, z)), sp.Rational(1, 2))
        ),
        scale(mul(P, P), sp.Rational(1, 2))
    )

    diff_q = sub(LHS_q, RHS_q)
    if is_zero(diff_q):
        print("✓ quartic_identity verified: LHS_q − RHS_q = 0.")
    else:
        print(f"✗ quartic_identity FAILS: {num_terms(diff_q)} residual terms:")
        print_poly(diff_q, "diff_q")
        return

    print("\n" + "=" * 70)
    print("Step 2: Compute LHS_quintic = ½W + ⅓z³ - ¼y⁴ - C₃ - C₄")
    print("=" * 70)

    step1 = add(scale(W, sp.Rational(1, 2)), scale(z3, sp.Rational(1, 3)))
    step2 = sub(step1, scale(y4, sp.Rational(1, 4)))
    step3 = sub(step2, C3)
    LHS = sub(step3, C4)

    print(f"  LHS_quintic: {num_terms(LHS)} non-zero terms.")

    print("\n" + "=" * 70)
    print("Step 3: Try candidate RHS shapes")
    print("=" * 70)

    # Candidate 1: naive extension by adding "next-order" terms.
    # Quartic was: F₁ + F₂ + a·E₂ + E₁·b + D₁·D₂ - ½(z·X + X·z) - ½P²
    # where X = E₁ + E₂ + Q.
    #
    # For quintic, an obvious extension:
    # - Promote each F to G (one degree higher remainder).
    # - Promote each E to F where it appears as "outer".
    # - Add new cross terms: a·E₂·b, E₁·a·b, etc.
    # - Promote z·X·z to z·Y·z where Y is one degree higher.
    # - Add - ½(P·X + X·P) for new P-mixed terms.
    # - Add - ⅓P³.
    #
    # Trial 1: bare analog
    F12pQ_quartic = add(add(F1, F2), Q)  # quartic-order pieces
    # We'll need new quartic-order Q-analog: Q' = a·E₂ + E₁·b + D₁·E₂ + E₁·D₂ + D₁·D₂·... hmm
    # Actually let me think: in quartic, X = E₁ + E₂ + Q where Q = aD₂ + D₁b + D₁D₂.
    # The "Q" part captures the D₁D₂-style cross terms at degree-3 minimum.
    # For quintic, we'd want Y = F₁ + F₂ + (next-order Q).

    # Let me first just print LHS to see what it looks like.
    print("\nLHS_quintic structure (top 50 terms by length):")
    print_poly(LHS, "LHS_quintic", limit=50)

    # Try Trial 1: same as quartic RHS but promoted (F → G, E → F):
    F12pQ_naive = add(add(F1, F2), Q)
    # No, that doesn't match. Let me think more carefully.
    # The natural "promotion" of quartic_identity:
    # ½W + ⅓z³ - ¼y⁴ - C₃ - C₄ = LHS_q + (-¼y⁴ - C₄)
    # If we expand: LHS_q = RHS_q (quartic_identity).
    # So LHS_quintic = RHS_q + (-¼y⁴ - C₄).
    # Therefore: LHS_quintic - RHS_q = -¼y⁴ - C₄.
    print("\nDoes LHS_quintic = RHS_q - ¼y⁴ - C₄?")
    expected = sub(sub(RHS_q, scale(y4, sp.Rational(1, 4))), C4)
    diff_check = sub(LHS, expected)
    if is_zero(diff_check):
        print("✓ Yes — by construction, LHS_quintic = RHS_q - ¼y⁴ - C₄.")
    else:
        print(f"✗ No — {num_terms(diff_check)} residual terms (BUG IN SCRIPT).")
        return

    # That's a tautology. The interesting question: can we re-express
    # the RHS in a way where each summand is structurally degree-5+ when
    # ea = exp(a), eb = exp(b)?
    #
    # The "degree-5+" shape we want: G₁, G₂, a·F₂, F₁·b, double-remainders
    # like D₁·F₂, F₁·D₂, E₁·E₂, etc. The point is that with ea = exp a,
    # G_i = O(α^5), F_i = O(α^4), E_i = O(α^3), D_i = O(α^2) (where α = ‖a‖).
    # So a·F₂ = O(αβ^4) = O(s^5), D₁·E₂ = O(α²β³) = O(s^5), E₁·D₂ = O(α³β²) = O(s^5).
    # And cross combinations like D₁·D₂·D₁ = O(α²β²α²) = O(s^6) — sixth-order.
    #
    # The challenge: re-express RHS_q - ¼y⁴ - C₄ in this canonical form.

    # One approach: try a parametric ansatz with ALL plausible degree-5+ basis
    # elements, and solve for coefficients via linear algebra.
    # That's the right approach but is complex. Let me first do a structural
    # check: just print -¼y⁴ - C₄ to see what it contains.

    print("\nThe 'extra' term -¼y⁴ - C₄ from quintic vs quartic LHS:")
    extra = sub(neg(scale(y4, sp.Rational(1, 4))), C4)
    print_poly(extra, "extra", limit=30)

    # ----------------------------------------------------------------
    # Candidate RHS attempts for quintic_identity
    # ----------------------------------------------------------------

    print("\n" + "=" * 70)
    print("Step 4: Try candidate RHS shapes for quintic_identity")
    print("=" * 70)

    X = add(add(E1, E2), Q)  # quartic-level "X"
    Q5 = add(add(mul(a, E2), mul(E1, b)), mul(D1, D2))  # next-order "Q"
    Y = add(add(F1, F2), Q5)  # quintic-level "Y" (one degree higher)

    # Trial 1: naive promotion F→G, E→F, plus new -⅓P³ and -½(P·X + X·P).
    print("\n--- Trial 1: G's + a·F₂ + F₁·b + D₁·E₂ + E₁·D₂ "
          "- ½(z·Y + Y·z) - ½(P·X + X·P) - ⅓P³ ---")
    P3 = mul(P, mul(P, P))
    cand1 = sub(sub(sub(
        add(add(add(add(add(G1, G2), mul(a, F2)), mul(F1, b)),
                mul(D1, E2)), mul(E1, D2)),
        scale(add(mul(z, Y), mul(z, Y)), sp.Rational(1, 2))),  # using mul(z, Y) twice = wrong, but for trial
        scale(add(mul(P, X), mul(X, P)), sp.Rational(1, 2))),
        scale(P3, sp.Rational(1, 3)))
    diff1 = sub(LHS, cand1)
    print(f"  LHS - cand1: {num_terms(diff1)} residual terms.")
    if num_terms(diff1) <= 30:
        print_poly(diff1, "diff1", limit=30)

    # Trial 2: same but fix the z·Y + Y·z (was wrong above).
    print("\n--- Trial 2: G's + a·F₂ + F₁·b + D₁·E₂ + E₁·D₂ "
          "- ½(z·Y + Y·z) - ½(P·X + X·P) - ⅓P³ (fixed) ---")
    cand2 = sub(sub(sub(
        add(add(add(add(add(G1, G2), mul(a, F2)), mul(F1, b)),
                mul(D1, E2)), mul(E1, D2)),
        scale(add(mul(z, Y), mul(Y, z)), sp.Rational(1, 2))),
        scale(add(mul(P, X), mul(X, P)), sp.Rational(1, 2))),
        scale(P3, sp.Rational(1, 3)))
    diff2 = sub(LHS, cand2)
    print(f"  LHS - cand2: {num_terms(diff2)} residual terms.")
    if num_terms(diff2) <= 30:
        print_poly(diff2, "diff2", limit=30)

    # Print the structure of LHS and various "natural" pieces to help discover.
    print("\n" + "=" * 70)
    print("Step 5: Print all candidate building block polynomials")
    print("=" * 70)
    print_poly(G1, "G₁ = ea - 1 - a - ½a² - ⅙a³ - (1/24)a⁴", limit=10)
    print_poly(G2, "G₂", limit=10)
    print_poly(mul(a, F2), "a·F₂", limit=10)
    print_poly(mul(F1, b), "F₁·b", limit=10)
    print_poly(mul(D1, E2), "D₁·E₂", limit=10)
    print_poly(mul(E1, D2), "E₁·D₂", limit=10)
    print_poly(mul(P, P), "P²", limit=10)
    print_poly(P3, "P³", limit=10)
    print_poly(mul(P, X), "P·X", limit=15)
    print_poly(mul(X, P), "X·P", limit=15)
    print_poly(mul(z, Y), "z·Y", limit=15)
    print_poly(mul(Y, z), "Y·z", limit=15)

    # ----------------------------------------------------------------
    # Step 6: Substitute ea = exp_truncated(a), eb = exp_truncated(b)
    # to verify the BCH identity at degree-5+
    # ----------------------------------------------------------------
    print("\n" + "=" * 70)
    print("Step 6: Substitute ea → 1+a+½a²+⅙a³+(1/24)a⁴+(1/120)a⁵ (degree 5)")
    print("        and check that LHS_full = ½W + ⅓y³ - ¼y⁴ + ⅕y⁵ - C₃ - C₄ - C₅")
    print("        is O(s^6) — i.e., all degree-≤5 terms in a, b vanish.")
    print("=" * 70)

    # Build C₅ = bch_quintic_term (from extract_bch_z5.py output, LCM 720)
    # Encoded as a sum over the 30 non-zero 5-letter words.
    # Using the same coefficient table as the Lean def.
    from extract_bch_z5 import main as _extract_z5_main  # not used, just imports
    # Build C5 explicitly:
    def word(letters):
        """Build a polynomial monomial from a string like 'aabba'."""
        result = npc(1)
        for ch in letters:
            i = {'a': 0, 'b': 1}[ch]
            result = mul(result, npv(i))
        return result

    coeffs_z5 = [
        ('aaaab', sp.Rational(-1, 720)),
        ('aaaba', sp.Rational(4, 720)),
        ('aaabb', sp.Rational(4, 720)),
        ('aabaa', sp.Rational(-6, 720)),
        ('aabab', sp.Rational(-6, 720)),
        ('aabba', sp.Rational(-6, 720)),
        ('aabbb', sp.Rational(4, 720)),
        ('abaaa', sp.Rational(4, 720)),
        ('abaab', sp.Rational(-6, 720)),
        ('ababa', sp.Rational(24, 720)),
        ('ababb', sp.Rational(-6, 720)),
        ('abbaa', sp.Rational(-6, 720)),
        ('abbab', sp.Rational(-6, 720)),
        ('abbba', sp.Rational(4, 720)),
        ('abbbb', sp.Rational(-1, 720)),
        ('baaaa', sp.Rational(-1, 720)),
        ('baaab', sp.Rational(4, 720)),
        ('baaba', sp.Rational(-6, 720)),
        ('baabb', sp.Rational(-6, 720)),
        ('babaa', sp.Rational(-6, 720)),
        ('babab', sp.Rational(24, 720)),
        ('babba', sp.Rational(-6, 720)),
        ('babbb', sp.Rational(4, 720)),
        ('bbaaa', sp.Rational(4, 720)),
        ('bbaab', sp.Rational(-6, 720)),
        ('bbaba', sp.Rational(-6, 720)),
        ('bbabb', sp.Rational(-6, 720)),
        ('bbbaa', sp.Rational(4, 720)),
        ('bbbab', sp.Rational(4, 720)),
        ('bbbba', sp.Rational(-1, 720)),
    ]

    C5 = npz()
    for w_str, c in coeffs_z5:
        C5 = add(C5, scale(word(w_str), c))

    print(f"\n  C₅ has {num_terms(C5)} non-zero terms (expected: 30).")

    # Define LHS_full = ½W + ⅓y³ - ¼y⁴ + ⅕y⁵ - C₃ - C₄ - C₅
    LHS_full = sub(sub(sub(sub(sub(sub(
        scale(W, sp.Rational(1, 2)),
        scale(y3, sp.Rational(-1, 3))),  # +⅓y³ via -(-⅓y³)
        scale(y4, sp.Rational(1, 4))),   # -¼y⁴
        scale(y5, sp.Rational(-1, 5))),  # +⅕y⁵
        C3),
        C4),
        C5)
    print(f"\n  LHS_full has {num_terms(LHS_full)} non-zero terms in {{a, b, ea, eb}}.")

    # Substitute ea → series, eb → series at degree 6+, see if LHS_full degree-≤5 vanishes
    # in {a, b}.
    # exp(a) truncated to degree 6: 1 + a + ½a² + ⅙a³ + (1/24)a⁴ + (1/120)a⁵ + (1/720)a⁶
    a6 = mul(a, a5)
    b6 = mul(b, b5)
    exp_a_trunc6 = add(add(add(add(add(add(add(
        npc(1), a),
        scale(a2, sp.Rational(1, 2))),
        scale(a3, sp.Rational(1, 6))),
        scale(a4, sp.Rational(1, 24))),
        scale(a5, sp.Rational(1, 120))),
        scale(a6, sp.Rational(1, 720))),
        npz())  # padding

    exp_b_trunc6 = add(add(add(add(add(add(add(
        npc(1), b),
        scale(b2, sp.Rational(1, 2))),
        scale(b3, sp.Rational(1, 6))),
        scale(b4, sp.Rational(1, 24))),
        scale(b5, sp.Rational(1, 120))),
        scale(b6, sp.Rational(1, 720))),
        npz())

    # Substitute ea → exp_a_trunc6 in LHS_full
    def substitute(p: NCPoly, var_idx: int, replacement: NCPoly,
                   max_degree_keep: int = 6) -> NCPoly:
        """In each monomial of p, replace each occurrence of variable var_idx
        with replacement, then expand the result. Truncate to max_degree_keep."""
        result = npz()
        for w, c in p.items():
            # Build the monomial m by multiplying letters, replacing var_idx
            m = npc(1)
            for letter in w:
                if letter == var_idx:
                    m = mul(m, replacement)
                else:
                    m = mul(m, npv(letter))
            # Truncate to max_degree_keep AFTER multiplication
            m = defaultdict(lambda: sp.Integer(0),
                            {ww: cc for ww, cc in m.items() if len(ww) <= max_degree_keep})
            result = add(result, scale(m, c))
        return result

    def mul_trunc(p: NCPoly, q: NCPoly, max_degree_keep: int) -> NCPoly:
        """Multiply p · q and truncate to max_degree_keep. Safe to call iteratively
        since high-degree terms can only become higher under multiplication."""
        r = npz()
        for w1, c1 in p.items():
            for w2, c2 in q.items():
                w = w1 + w2
                if len(w) <= max_degree_keep:
                    r[w] = r[w] + c1 * c2
        return defaultdict(lambda: sp.Integer(0),
                           {w: sp.simplify(c) for w, c in r.items() if sp.simplify(c) != 0})

    def substitute_both(p: NCPoly, replacement_a: NCPoly, replacement_b: NCPoly,
                        max_degree_keep: int = 6) -> NCPoly:
        """In each monomial of p, replace ea (var_idx=2) with replacement_a and
        eb (var_idx=3) with replacement_b SIMULTANEOUSLY, with incremental
        truncation to keep intermediate sizes manageable."""
        result = npz()
        for w, c in p.items():
            m = npc(1)
            for letter in w:
                if letter == 2:
                    m = mul_trunc(m, replacement_a, max_degree_keep)
                elif letter == 3:
                    m = mul_trunc(m, replacement_b, max_degree_keep)
                else:
                    m = mul_trunc(m, npv(letter), max_degree_keep)
            result = add(result, scale(m, c))
        return result

    # Debug: substitute y first and verify
    y_subst = substitute(y, 2, exp_a_trunc6, max_degree_keep=6)
    y_subst = substitute(y_subst, 3, exp_b_trunc6, max_degree_keep=6)
    print(f"\n  DEBUG: y_subst = ea·eb - 1 has {num_terms(y_subst)} non-zero terms.")
    by_deg_y = defaultdict(list)
    for w, c in y_subst.items():
        if sp.simplify(c) != 0:
            by_deg_y[len(w)].append((w, c))
    for deg in sorted(by_deg_y.keys())[:4]:
        terms = by_deg_y[deg]
        print(f"    Degree {deg}: {len(terms)} terms.")
        if deg <= 3:
            for w, c in sorted(terms):
                ws = ''.join('a' if l == 0 else 'b' for l in w)
                print(f"      {sp.simplify(c)}  ·  {ws}")

    # Debug: substitute ½W and check H1
    W_subst = substitute(scale(W, sp.Rational(1, 2)), 2, exp_a_trunc6, max_degree_keep=6)
    W_subst = substitute(W_subst, 3, exp_b_trunc6, max_degree_keep=6)
    print(f"\n  DEBUG: ½W_subst has {num_terms(W_subst)} non-zero terms (expected: degree 3+).")
    by_deg_W = defaultdict(list)
    for w, c in W_subst.items():
        if sp.simplify(c) != 0:
            by_deg_W[len(w)].append((w, c))
    for deg in sorted(by_deg_W.keys())[:5]:
        terms = by_deg_W[deg]
        print(f"    Degree {deg}: {len(terms)} terms.")
        if deg <= 3 and len(terms) <= 6:
            for w, c in sorted(terms):
                ws = ''.join('a' if l == 0 else 'b' for l in w)
                print(f"      {sp.simplify(c)}  ·  {ws}")

    # Debug: print y5 unsubstituted, then substituted
    print(f"\n  DEBUG: y5 unsubstituted: {num_terms(y5)} terms")
    print_poly(y5, "y5", limit=20)

    # Substitute with larger truncation to see if it changes
    print("\n  Substitute y5 with max_degree_keep=6:")
    y5_subst_6 = substitute(y5, 2, exp_a_trunc6, max_degree_keep=6)
    y5_subst_6 = substitute(y5_subst_6, 3, exp_b_trunc6, max_degree_keep=6)
    print_poly(y5_subst_6, "y5_subst_6", limit=8)

    # Build degree-10 truncated exp's
    exp_a_trunc10 = npc(1)
    a_pow = npc(1)
    for k in range(1, 11):
        a_pow = mul(a_pow, npv(0))
        exp_a_trunc10 = add(exp_a_trunc10, scale(a_pow, sp.Rational(1, sp.factorial(k))))
    exp_b_trunc10 = npc(1)
    b_pow = npc(1)
    for k in range(1, 11):
        b_pow = mul(b_pow, npv(1))
        exp_b_trunc10 = add(exp_b_trunc10, scale(b_pow, sp.Rational(1, sp.factorial(k))))
    print("\n  Substitute y5 with max_degree_keep=10 (using deg-10 exp truncation):")
    y5_subst_10 = substitute(y5, 2, exp_a_trunc10, max_degree_keep=10)
    y5_subst_10 = substitute(y5_subst_10, 3, exp_b_trunc10, max_degree_keep=10)
    print_poly(y5_subst_10, "y5_subst_10", limit=8)

    # Use original substitute (degree-6 in input, degree-6 in output)
    y5_subst = y5_subst_6

    # Cross-check: build LHS_full step by step, substituting at each step
    print(f"\n  Cross-check: building LHS step by step (substituted to {{a, b}}):")
    def subst_full(p):
        return substitute_both(p, exp_a_trunc6, exp_b_trunc6, max_degree_keep=6)

    def lowest_deg(p):
        deg_terms = sorted([(len(w), w, sp.simplify(c)) for w, c in p.items() if sp.simplify(c) != 0])
        if deg_terms:
            return deg_terms[0][0]
        return -1

    s = scale(W, sp.Rational(1, 2))
    s_subst = subst_full(s)
    print(f"    ½W substituted: {num_terms(s_subst)} terms, lowest deg = {lowest_deg(s_subst)}")
    s = sub(s, scale(y3, sp.Rational(-1, 3)))
    s_subst = subst_full(s)
    print(f"    ½W + ⅓y³ substituted: {num_terms(s_subst)} terms, lowest deg = {lowest_deg(s_subst)}")
    s = sub(s, scale(y4, sp.Rational(1, 4)))
    s_subst = subst_full(s)
    print(f"    ½W + ⅓y³ - ¼y⁴ substituted: {num_terms(s_subst)} terms, lowest deg = {lowest_deg(s_subst)}")
    s = sub(s, scale(y5, sp.Rational(-1, 5)))
    s_subst = subst_full(s)
    print(f"    ½W + ⅓y³ - ¼y⁴ + ⅕y⁵ substituted: {num_terms(s_subst)} terms, lowest deg = {lowest_deg(s_subst)}")
    s = sub(s, C3)
    s_subst = subst_full(s)
    print(f"    ... - C₃ substituted: {num_terms(s_subst)} terms, lowest deg = {lowest_deg(s_subst)}")
    s = sub(s, C4)
    s_subst = subst_full(s)
    print(f"    ... - C₄ substituted: {num_terms(s_subst)} terms, lowest deg = {lowest_deg(s_subst)}")
    s = sub(s, C5)
    s_subst = subst_full(s)
    print(f"    ... - C₅ substituted: {num_terms(s_subst)} terms, lowest deg = {lowest_deg(s_subst)}")

    LHS_substituted = substitute_both(LHS_full, exp_a_trunc6, exp_b_trunc6,
                                      max_degree_keep=6)
    print(f"\n  After substitution ea→exp(a)_6, eb→exp(b)_6 (single pass):")
    print(f"  LHS_substituted has {num_terms(LHS_substituted)} non-zero terms in {{a, b}}.")

    # Filter by degree
    by_degree = defaultdict(list)
    for w, c in LHS_substituted.items():
        if sp.simplify(c) != 0:
            by_degree[len(w)].append((w, c))
    for deg in sorted(by_degree.keys()):
        terms = by_degree[deg]
        print(f"    Degree {deg}: {len(terms)} non-zero terms.")
        if len(terms) <= 6:
            for w, c in sorted(terms):
                ws = ''.join('a' if l == 0 else 'b' for l in w)
                print(f"      {sp.simplify(c)}  ·  {ws}")

    # Expected: degrees 0-5 should ALL be zero (BCH identity holds).
    # Only degree-6+ terms should remain. Those are the "BCH residual at order 6+".
    deg_lt_6 = [d for d in by_degree.keys() if d < 6]
    if not deg_lt_6:
        print("\n  ✓ All degrees < 6 vanish — BCH identity verified at degree 5.")
        print("    This confirms C₅ from extract_bch_z5.py is correct.")
    else:
        print(f"\n  ✗ Non-zero terms at degrees {deg_lt_6} — BCH identity FAILS!")

    # ----------------------------------------------------------------
    # Step 6.5: Extract deg-4 + deg-5 substituted contributions for the
    # sextic_pure_identity discovery. The identity is:
    #
    #   ½·W_subst[4] + ⅓·y³_subst[4] - C₃_subst[4] - ¼·z⁴_subst[4] - C₄ = 0
    #     (deg-4 cancellation, this IS quintic_pure_identity in Lean)
    #
    #   ½·W_subst[5] + ⅓·y³_subst[5] - ¼·y⁴_subst[5] + ⅕·y⁵_subst[5]
    #     - C₃_subst[5] - C₄_subst[5] - C₅ = 0
    #     (deg-5 cancellation, this is the NEW sextic_pure_identity)
    #
    # These are pure {a, b} polynomial identities at fixed degree, which
    # noncomm_ring CAN handle in Lean (after scalar clearing).
    # ----------------------------------------------------------------
    print("\n" + "=" * 70)
    print("Step 6.5: Extract deg-4 and deg-5 contributions for sextic_pure_identity")
    print("=" * 70)

    def deg_part(p, deg):
        """Extract the degree-d part of polynomial p (in {a, b})."""
        return defaultdict(lambda: sp.Integer(0),
                           {w: sp.simplify(c) for w, c in p.items()
                            if len(w) == deg and sp.simplify(c) != 0})

    def fmt_pure_poly(p, name, max_print=12):
        items = sorted(p.items(), key=lambda x: x[0])
        items = [(w, c) for w, c in items if sp.simplify(c) != 0]
        print(f"  {name}: {len(items)} non-zero pure {{a,b}} terms.")
        for i, (w, c) in enumerate(items):
            if i >= max_print:
                print(f"    ... ({len(items) - max_print} more)")
                break
            ws = ''.join('a' if l == 0 else 'b' for l in w)
            print(f"    {sp.simplify(c)}  ·  {ws}")

    # Compute substituted W, y3, y4, y5
    W_subst_full = subst_full(W)
    y3_subst_full = subst_full(y3)
    y4_subst_full = subst_full(y4)
    y5_subst_full = subst_full(y5)

    # Degree-4 contributions
    print("\n--- DEGREE 4 contributions (for quintic_pure_identity) ---")
    W4 = deg_part(W_subst_full, 4)
    y3_4 = deg_part(y3_subst_full, 4)
    fmt_pure_poly(W4, "½·W_subst[4]·2 (= W_subst[4])")
    fmt_pure_poly(y3_4, "y³_subst[4]")
    print(f"  C₃_subst[4]: {num_terms(deg_part(C3, 4))} terms (should be 0, C₃ is deg 3).")
    print(f"  C₄ pure deg 4: {num_terms(C4)} terms.")

    # The quintic_pure_identity says:
    #   ½·W_subst[4] + ⅓·y³_subst[4] - ¼·z⁴ - C₄ = 0
    z4 = mul(z, z3)
    test_d4 = sub(sub(sub(add(scale(W4, sp.Rational(1, 2)),
                              scale(y3_4, sp.Rational(1, 3))),
                          scale(z4, sp.Rational(1, 4))),
                      C3),
                  C4)  # Should this be 0? Note C3 deg 4 = 0, so adding/subtracting C3 doesn't matter at deg 4.
    test_d4 = deg_part(test_d4, 4)
    print(f"\n  Verify: ½·W_subst[4] + ⅓·y³_subst[4] - ¼·z⁴ - C₄ at deg 4:")
    print(f"    {num_terms(test_d4)} non-zero terms (should be 0).")
    if num_terms(test_d4) > 0:
        fmt_pure_poly(test_d4, "RESIDUAL", max_print=20)

    # Degree-5 contributions
    print("\n--- DEGREE 5 contributions (for sextic_pure_identity) ---")
    W5 = deg_part(W_subst_full, 5)
    y3_5 = deg_part(y3_subst_full, 5)
    y4_5 = deg_part(y4_subst_full, 5)
    y5_5 = deg_part(y5_subst_full, 5)
    fmt_pure_poly(W5, "W_subst[5]")
    fmt_pure_poly(y3_5, "y³_subst[5]")
    fmt_pure_poly(y4_5, "y⁴_subst[5]")
    fmt_pure_poly(y5_5, "y⁵_subst[5]")
    print(f"  C₅ pure deg 5: {num_terms(C5)} terms.")

    # The sextic_pure_identity says:
    #   ½·W_subst[5] + ⅓·y³_subst[5] - ¼·y⁴_subst[5] + ⅕·y⁵_subst[5] - C₅ = 0
    test_d5 = sub(add(add(sub(add(scale(W5, sp.Rational(1, 2)),
                                  scale(y3_5, sp.Rational(1, 3))),
                              scale(y4_5, sp.Rational(1, 4))),
                          scale(y5_5, sp.Rational(1, 5))),
                      npz()),  # placeholder
                  C5)
    test_d5 = deg_part(test_d5, 5)
    print(f"\n  Verify sextic_pure_identity at deg 5:")
    print(f"    ½·W_subst[5] + ⅓·y³_subst[5] - ¼·y⁴_subst[5] + ⅕·y⁵_subst[5] - C₅")
    print(f"    = {num_terms(test_d5)} non-zero terms (should be 0).")
    if num_terms(test_d5) > 0:
        fmt_pure_poly(test_d5, "RESIDUAL", max_print=20)
    else:
        print("    ✓ sextic_pure_identity HOLDS at deg 5! Suitable for noncomm_ring.")

    # ----------------------------------------------------------------
    # Step 7: Parametric RHS solver
    # ----------------------------------------------------------------
    print("\n" + "=" * 70)
    print("Step 7: Parametric RHS solver — find c₁, c₂, ... such that")
    print("        LHS_full = c₁·basis_1 + c₂·basis_2 + ...")
    print("=" * 70)

    # Candidate basis: all "natural" degree-5+ building blocks.
    # Each is a polynomial in {a, b, ea, eb}; we'll solve for rational coefficients.
    H1 = sub(G1, scale(a5, sp.Rational(1, 120)))  # H₁ = G₁ - (1/120)a⁵
    H2 = sub(G2, scale(b5, sp.Rational(1, 120)))

    # Build the basis dict: name → NCPoly
    # Include all natural "degree-5+" building blocks in {a, b, ea, eb}.
    basis = {
        # Degree-5+ singles
        'G1': G1, 'G2': G2,
        # Cross-quartic
        'aF2': mul(a, F2), 'F1b': mul(F1, b),
        'F2a': mul(F2, a), 'bF1': mul(b, F1),
        # Cross-mixed-cubic
        'D1E2': mul(D1, E2), 'E1D2': mul(E1, D2),
        'E2D1': mul(E2, D1), 'D2E1': mul(D2, E1),
        # P-related (P starts at deg 2)
        'PX': mul(P, X), 'XP': mul(X, P),
        'P_sq_a': mul(mul(P, P), a), 'aP_sq': mul(a, mul(P, P)),
        'bP_sq': mul(b, mul(P, P)), 'P_sq_b': mul(mul(P, P), b),
        'P3': mul(P, mul(P, P)),
        # z·Y + Y·z (Y = F1+F2+Q5)
        'zY': mul(z, Y), 'Yz': mul(Y, z),
        # D-D-D triples (deg 6)
        'D1D2D1': mul(D1, mul(D2, D1)), 'D2D1D2': mul(D2, mul(D1, D2)),
        # Sandwiches with a, b in middle/edges
        'aD2a': mul(mul(a, D2), a), 'bD1b': mul(mul(b, D1), b),
        'aD2b': mul(mul(a, D2), b), 'bD1a': mul(mul(b, D1), a),
        'D1bD2': mul(mul(D1, b), D2), 'D2aD1': mul(mul(D2, a), D1),
        'D1aD2': mul(mul(D1, a), D2), 'D2bD1': mul(mul(D2, b), D1),
        # E with single var (degree 4 each, but combined deg 5+)
        'aE2a': mul(mul(a, E2), a), 'bE1b': mul(mul(b, E1), b),
        'aE2b': mul(mul(a, E2), b), 'bE1a': mul(mul(b, E1), a),
        'aaE2': mul(mul(a, a), E2), 'E1bb': mul(E1, mul(b, b)),
        'E2aa': mul(E2, mul(a, a)), 'bbE1': mul(mul(b, b), E1),
        # D with squares (deg 4)
        'aaD2': mul(mul(a, a), D2), 'D1bb': mul(D1, mul(b, b)),
        'bbD1': mul(mul(b, b), D1), 'D2aa': mul(D2, mul(a, a)),
        # D-cross with ab/ba
        'D1ab': mul(D1, mul(a, b)), 'abD2': mul(mul(a, b), D2),
        'D1ba': mul(D1, mul(b, a)), 'baD2': mul(mul(b, a), D2),
        'abD1': mul(mul(a, b), D1), 'D2ab': mul(D2, mul(a, b)),
        'baD1': mul(mul(b, a), D1), 'D2ba': mul(D2, mul(b, a)),
        # Triple cross D-D-D with vars
        'D1D2a': mul(mul(D1, D2), a), 'aD1D2': mul(a, mul(D1, D2)),
        'bD1D2': mul(b, mul(D1, D2)), 'D1D2b': mul(mul(D1, D2), b),
        # z² · D, D · z² etc.
        'zzD1': mul(mul(z, z), D1), 'D1zz': mul(D1, mul(z, z)),
        'zzD2': mul(mul(z, z), D2), 'D2zz': mul(D2, mul(z, z)),
        'zD1z': mul(mul(z, D1), z), 'zD2z': mul(mul(z, D2), z),
        'zE1z': mul(mul(z, E1), z), 'zE2z': mul(mul(z, E2), z),
        # E·F, F·E products (produce pure {a, b} deg-5 cross monomials)
        'E1F2': mul(E1, F2), 'F1E2': mul(F1, E2),
        'F2E1': mul(F2, E1), 'E2F1': mul(E2, F1),
        # D·G, G·D products (deg 5+ pure)
        'D1G2': mul(D1, G2), 'G1D2': mul(G1, D2),
        'G2D1': mul(G2, D1), 'D2G1': mul(D2, G1),
        # F·F products (deg 6 pure max, with deg-5 contributions)
        'F1F2': mul(F1, F2), 'F2F1': mul(F2, F1),
        # E·E with single var sandwich (deg 5)
        'E1aE2': mul(mul(E1, a), E2), 'E1bE2': mul(mul(E1, b), E2),
        'E2aE1': mul(mul(E2, a), E1), 'E2bE1': mul(mul(E2, b), E1),
        'aE1E2': mul(a, mul(E1, E2)), 'E1E2a': mul(E1, mul(E2, a)),
        'bE1E2': mul(b, mul(E1, E2)), 'E1E2b': mul(E1, mul(E2, b)),
        'aE2E1': mul(a, mul(E2, E1)), 'E2E1a': mul(E2, mul(E1, a)),
        'bE2E1': mul(b, mul(E2, E1)), 'E2E1b': mul(E2, mul(E1, b)),
        # P^4 (pure ABABABAB-type contributions)
        'P4': mul(mul(P, P), mul(P, P)),
        # y^k powers directly (need y² and y³ for log series structure)
        'y2': mul(y, y),
        'y3': mul(y, mul(y, y)),
        'y4': mul(mul(y, y), mul(y, y)),
        'y5': mul(y, mul(mul(y, y), mul(y, y))),
        # SANDWICH BASIS: a^k·D_m·a^l, structurally O(s^{k+l+1}) with deg-5 pure
        # contributions covering interleaved {a,b} 5-letter words.
        # Each "a^k D b^l a^m" gives a specific pure {a,b} deg-5 term.
        # Naming: 'aaD2aa' = a²·D₂·a², deg 5 pure = -aabaa.
        # i = 0 (D₁ middle): D₁ between b's → covers b^k·a·b^l type
        'D1bbbb': mul(D1, mul(mul(b, b), mul(b, b))),
        'bD1bbb': mul(b, mul(D1, mul(b, mul(b, b)))),
        'bbD1bb': mul(mul(b, b), mul(D1, mul(b, b))),
        'bbbD1b': mul(mul(b, b), mul(b, mul(D1, b))),
        'bbbbD1': mul(mul(b, b), mul(b, mul(b, D1))),
        # i = 1 (D₂ middle): covers a^k·b·a^l type
        'D2aaaa': mul(D2, mul(mul(a, a), mul(a, a))),
        'aD2aaa': mul(a, mul(D2, mul(a, mul(a, a)))),
        'aaD2aa': mul(mul(a, a), mul(D2, mul(a, a))),
        'aaaD2a': mul(mul(a, a), mul(a, mul(D2, a))),
        'aaaaD2': mul(mul(a, a), mul(a, mul(a, D2))),
        # Two-D sandwiches (e.g., a·D₂·a·D₂·a → ababa)
        'aD2aD2a': mul(a, mul(D2, mul(a, mul(D2, a)))),
        'D2aD2aD2': mul(D2, mul(a, mul(D2, mul(a, D2)))),
        'bD1bD1b': mul(b, mul(D1, mul(b, mul(D1, b)))),
        'D1bD1bD1': mul(D1, mul(b, mul(D1, mul(b, D1)))),
        # Mixed alternations: a·D₂·a·D₂·b → ababb, etc.
        'aD2aD2b': mul(a, mul(D2, mul(a, mul(D2, b)))),
        'aD2bD1b': mul(a, mul(D2, mul(b, mul(D1, b)))),
        'aD2bD2b': mul(a, mul(D2, mul(b, mul(D2, b)))),
        'D2bD2aD2': mul(D2, mul(b, mul(D2, mul(a, D2)))),
        # Asymmetric three-letter middle: aab, abb, baa, bba kind
        'aaD2ab': mul(mul(a, a), mul(D2, mul(a, b))),
        'aD2aab': mul(a, mul(D2, mul(a, mul(a, b)))),
        'abD2aa': mul(mul(a, b), mul(D2, mul(a, a))),
        'baaD2b': mul(b, mul(mul(a, a), mul(D2, b))),
        'bD2aab': mul(b, mul(D2, mul(a, mul(a, b)))),
        'baD2ab': mul(b, mul(a, mul(D2, mul(a, b)))),
        'baD2ba': mul(b, mul(a, mul(D2, mul(b, a)))),
        # Asymmetric with D in middle and longer arms
        'D2abba': mul(D2, mul(a, mul(b, mul(b, a)))),
        'abbaD2': mul(mul(a, b), mul(b, mul(a, D2))),
        'D2baab': mul(D2, mul(b, mul(a, mul(a, b)))),
        'baabD2': mul(b, mul(a, mul(a, mul(b, D2)))),
        # F-sandwich elements (cover a·b³·a and b·a³·b type via -1/6·a³ in F)
        'aF2a': mul(a, mul(F2, a)),  # deg 5 pure: -⅙·abbba (covers abbba)
        'bF1b': mul(b, mul(F1, b)),  # deg 5 pure: -⅙·baaab (covers baaab)
        'aF2b': mul(a, mul(F2, b)),  # mixed
        'bF1a': mul(b, mul(F1, a)),
        # Sandwiches for 3-switch words (baaba, babaa, bbaba)
        'baD2aa': mul(b, mul(a, mul(D2, mul(a, a)))),  # deg 5: -baaaa - babaa
        'aaD2ba': mul(mul(a, a), mul(D2, mul(b, a))),
        'bF1ba': mul(b, mul(F1, mul(b, a))),  # deg 5: includes -½·baaba
        'abF1b': mul(mul(a, b), mul(F1, b)),
        'bbD1ba': mul(mul(b, b), mul(D1, mul(b, a))),  # deg 5: -bbaba
        'abD1ba': mul(mul(a, b), mul(D1, mul(b, a))),
        'baD1ba': mul(mul(b, a), mul(D1, mul(b, a))),
        'baF1b': mul(mul(b, a), mul(F1, b)),  # mixed
        'abD2bb': mul(mul(a, b), mul(D2, mul(b, b))),
        'bD1aab': mul(b, mul(D1, mul(a, mul(a, b)))),
        'abD1aa': mul(mul(a, b), mul(D1, mul(a, a))),
        'bD2aba': mul(b, mul(D2, mul(a, mul(b, a)))),
    }

    print(f"\n  Basis size: {len(basis)} candidate terms.")
    print(f"  LHS_full target: {num_terms(LHS_full)} non-zero monomials.")

    # Build a linear system: for each monomial m in {a, b, ea, eb}, the equation
    #   LHS_full[m] = sum_k c_k · basis[k][m]
    # over all c_k. Each monomial → one equation.

    # Collect all monomials that appear in LHS_full or any basis element
    all_monomials = set(LHS_full.keys())
    for poly in basis.values():
        all_monomials.update(poly.keys())
    all_monomials = sorted(all_monomials)

    # Build matrix M (rows = monomials, cols = basis elements + LHS column)
    # Equation: sum_k c_k · basis[k][m] = LHS_full[m]
    coeff_names = list(basis.keys())
    n_vars = len(coeff_names)
    n_eqs = len(all_monomials)

    print(f"  Linear system: {n_eqs} equations, {n_vars} unknowns.")

    # Build augmented matrix A | b where A[i][j] = basis_j[m_i], b[i] = LHS[m_i]
    # Use sympy.Matrix
    rows = []
    rhs_col = []
    for m in all_monomials:
        row = []
        for name in coeff_names:
            row.append(basis[name].get(m, sp.Integer(0)))
        rows.append(row)
        rhs_col.append(LHS_full.get(m, sp.Integer(0)))

    A = sp.Matrix(rows)
    b_vec = sp.Matrix(rhs_col)

    print(f"  Matrix shape: {A.shape}")
    print(f"  Solving Ax = b...")
    aug = A.row_join(b_vec)
    rref, pivots = aug.rref()
    print(f"  RREF computed. Pivots: {pivots}")

    # Check if system is consistent: any row with all-zero LHS but non-zero RHS = inconsistent
    is_consistent = True
    for i in range(rref.rows):
        if all(rref[i, j] == 0 for j in range(n_vars)) and rref[i, n_vars] != 0:
            is_consistent = False
            break
    if is_consistent:
        print(f"  ✓ System is consistent. Computing solution...")
        # Extract solution: free variables → 0; pivot variables determined.
        coeffs = [sp.Integer(0)] * n_vars
        for piv_idx, col in enumerate(pivots):
            if col < n_vars:  # Skip pivot in RHS column (would mean inconsistent)
                coeffs[col] = rref[piv_idx, n_vars]

        print("\n  Solution (RHS = sum of c_i · basis_i):")
        for name, c in zip(coeff_names, coeffs):
            if c != 0:
                print(f"    {c}  ·  {name}")

        # Verify
        rhs_built = npz()
        for name, c in zip(coeff_names, coeffs):
            rhs_built = add(rhs_built, scale(basis[name], c))
        diff = sub(LHS_full, rhs_built)
        if is_zero(diff):
            print("\n  ✓ VERIFIED: LHS_full = sum of c_i · basis_i (exact ring identity).")
        else:
            print(f"\n  ✗ Mismatch — {num_terms(diff)} residual terms (non-pivot vars matter):")
            print_poly(diff, "diff", limit=15)
    else:
        print("  ✗ System is INCONSISTENT — basis is insufficient.")
        print("    Need more candidate building blocks.")

        # Diff-driven analysis: extract the inconsistency residual.
        # In RREF, rows with all-zero LHS but non-zero RHS represent
        # equations that LHS_full has a non-zero value at some monomial-direction
        # that the basis can't reach.
        print("\n  Inconsistency rows (these monomial-directions are unreachable):")
        # Track which combinations of monomials are inconsistent.
        # For each row in RREF that's inconsistent, the corresponding original
        # equation row indices reveal which monomials it constrains.
        # Compute via the row-reduction transformation: aug_after = T · aug_before
        # We can find T by augmenting with identity and reducing.
        I_aug = sp.eye(n_eqs)
        big_aug = aug.row_join(I_aug)
        big_rref, big_pivots = big_aug.rref()
        n_inconsistent = 0
        for i in range(big_rref.rows):
            # Inconsistent row: all coefficient cols = 0, b col ≠ 0.
            row_zero_in_A = all(big_rref[i, j] == 0 for j in range(n_vars))
            if row_zero_in_A and big_rref[i, n_vars] != 0:
                n_inconsistent += 1
                if n_inconsistent <= 5:  # Print first 5 inconsistencies
                    # Recover the linear combination of monomials
                    print(f"    Inconsistency row {n_inconsistent}: ", end='')
                    rhs_val = big_rref[i, n_vars]
                    print(f"sum = {rhs_val}, contributing equations:")
                    contribs = []
                    for k in range(n_eqs):
                        coef = big_rref[i, n_vars + 1 + k]
                        if coef != 0:
                            ms = ''.join(['a','b','A','B'][ll] for ll in all_monomials[k])
                            contribs.append(f"{coef}·[{ms}]")
                    if len(contribs) <= 8:
                        print(f"      {' + '.join(contribs)}")
                    else:
                        print(f"      ({len(contribs)} monomials in linear combo)")
                        for c in contribs[:5]:
                            print(f"        {c}")
                        print(f"        ... ({len(contribs)-5} more)")
        print(f"  Total inconsistent rows: {n_inconsistent}")

        # Compute the residual: the projection of LHS_full onto the orthogonal
        # complement of the column space of A. We can do this by:
        # - find a "best fit" coefficient set (pseudo-inverse or partial soln)
        # - residual = LHS_full - sum c_i basis_i

        # For a quick analysis, just find which monomials in LHS_full are NOT
        # covered by the union of basis monomials.
        basis_monomials = set()
        for poly in basis.values():
            basis_monomials.update(poly.keys())
        lhs_monomials = set(LHS_full.keys())
        uncovered = lhs_monomials - basis_monomials
        print(f"\n  Monomials in LHS_full NOT covered by ANY basis element: {len(uncovered)}")
        if uncovered:
            for m in sorted(uncovered):
                ms = ''.join(['a','b','A','B'][i] for i in m)
                print(f"    {LHS_full[m]}  ·  {ms}")

        # Alternative: solve the least-squares problem via QR or pseudo-inverse.
        # But sympy's RREF gives us enough info. Let me extract a "best partial
        # fit" by setting non-pivot variables to 0 and seeing what residual remains.
        partial_coeffs = [sp.Integer(0)] * n_vars
        for piv_idx, col in enumerate(pivots):
            if col < n_vars:
                partial_coeffs[col] = rref[piv_idx, n_vars]
        partial_rhs = npz()
        for name, c in zip(coeff_names, partial_coeffs):
            partial_rhs = add(partial_rhs, scale(basis[name], c))
        residual = sub(LHS_full, partial_rhs)
        print(f"\n  Residual (LHS_full - partial_fit): {num_terms(residual)} non-zero terms.")
        if num_terms(residual) <= 30:
            print_poly(residual, "residual", limit=30)


if __name__ == "__main__":
    main()
