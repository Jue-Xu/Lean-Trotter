"""Compute the factored form of sumQuadCorr(s4DList A B p) for axiom 1 closure.

Symbolically computes:
    sumQuadCorr(s4DList A B p) = (4p^3 + (1-4p)^3) * Q(A, B)

where Q is an explicit quartic combination of A, B. Output can be pasted into
LieTrotter/Suzuki4MultinomialExpand.lean as a factored-form lemma.

Uses sympy's non-commutative symbols. Expands sumQuadCorr via its cons
recurrence on s4DList = [(A, p/2), (B, p), (A, p), (B, p),
                         (A, (1-3p)/2), (B, 1-4p), (A, (1-3p)/2),
                         (B, p), (A, p), (B, p), (A, p/2)].
"""

from sympy import symbols, Symbol, Rational, expand, simplify, factor, collect
from sympy.abc import p

# Non-commutative symbols for operators
A = Symbol('A', commutative=False)
B = Symbol('B', commutative=False)

# s4DList
s4DList = [
    (A, p / 2),
    (B, p),
    (A, p),
    (B, p),
    (A, (1 - 3*p) / 2),
    (B, 1 - 4*p),
    (A, (1 - 3*p) / 2),
    (B, p),
    (A, p),
    (B, p),
    (A, p / 2),
]

def sumDList(L):
    """Sum of c*X over L."""
    result = 0
    for (X, c) in L:
        result += c * X
    return result

def sumCommList(L):
    """Sum of commutators [d_i, d_j] for i<j in L, accumulated via cons recurrence."""
    if not L:
        return 0
    (X, c) = L[0]
    tail = L[1:]
    d = c * X
    return sumCommList(tail) + (d * sumDList(tail) - sumDList(tail) * d)

def sumTripleCorr(L):
    """Cubic correction sum."""
    if not L:
        return 0
    (X, c) = L[0]
    tail = L[1:]
    d = c * X
    commSingle = d * sumDList(tail) - sumDList(tail) * d
    return (sumTripleCorr(tail)
            + 3 * (d * sumCommList(tail))
            + (2 * (d * commSingle) + commSingle * d)
            + (2 * (commSingle * sumDList(tail)) + sumDList(tail) * commSingle))

def sumQuadCorr(L):
    """Quartic correction sum."""
    if not L:
        return 0
    (X, c) = L[0]
    tail = L[1:]
    d = c * X
    s = sumDList(tail)
    return (sumQuadCorr(tail)
            + 4 * d * sumTripleCorr(tail)
            + 6 * d**2 * sumCommList(tail)
            + (s**4 + 4 * d * s**3 + 6 * d**2 * s**2 + 4 * d**3 * s + d**4
               - (d + s)**4))

print("Computing sumQuadCorr(s4DList)...")
sqc = sumQuadCorr(s4DList)
print("Expanding...")
sqc_expanded = expand(sqc)

# Expected: sqc_expanded = (4p^3 + (1-4p)^3) * Q
scalar = 4*p**3 + (1 - 4*p)**3
scalar_expanded = expand(scalar)
print(f"Scalar: 4p^3 + (1-4p)^3 = {scalar_expanded}")

# Divide sqc by scalar — but this is a non-commutative expression with polynomial-in-p coefficients.
# We need to collect monomials and extract coefficients in p for each monomial.

print("\nCollecting monomial-wise...")
# Use Poly with the non-commutative variables
# sympy can't directly factor non-commutative expressions by scalar,
# so we have to do it manually per monomial.

from collections import defaultdict

# Extract monomials and their p-coefficients
def extract_monomials(expr):
    """Return dict: monomial (as string) -> polynomial in p."""
    expr = expand(expr)
    monos = defaultdict(lambda: 0)
    if expr.is_Add:
        terms = expr.args
    else:
        terms = (expr,)
    for term in terms:
        # Separate scalar from non-commutative part
        scalar_part = 1
        nc_part = 1
        if term.is_Mul:
            for f in term.args:
                if f.is_commutative:
                    scalar_part *= f
                else:
                    nc_part *= f
        elif term.is_commutative:
            scalar_part = term
            nc_part = 1
        else:
            nc_part = term
        monos[nc_part] += scalar_part
    return monos

monos_lhs = extract_monomials(sqc_expanded)

# Check each monomial's coefficient is divisible by (4p^3 + (1-4p)^3)
print(f"\nFound {len(monos_lhs)} distinct quartic monomials in sumQuadCorr(s4DList).")
print("\nChecking factorization...")

Q_coeffs = {}  # monomial -> Q-coefficient (scalar, independent of p)
all_divisible = True
for mono, coef in monos_lhs.items():
    coef_simp = expand(coef)
    if coef_simp == 0:
        continue
    # Divide by scalar_expanded
    from sympy import div
    q, r = div(coef_simp, scalar_expanded, p)
    if r == 0:
        Q_coeffs[mono] = q
    else:
        all_divisible = False
        print(f"  Non-divisible: {mono} -> coef {coef_simp}, remainder {r}")

if all_divisible:
    print("\n✓ All monomial coefficients are divisible by (4p^3 + (1-4p)^3).")
    print(f"Q has {len(Q_coeffs)} non-zero quartic monomials:\n")
    for mono, q in sorted(Q_coeffs.items(), key=lambda x: str(x[0])):
        print(f"  {mono} : {q}")
else:
    print("\n✗ Factorization FAILS — sumQuadCorr is not divisible by (4p^3 + (1-4p)^3).")
    print("This means the identity sumQuadCorr = <scalar> * Q_quartic does not hold.")
