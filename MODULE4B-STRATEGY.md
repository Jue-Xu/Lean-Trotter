# Module 4b Attack Strategy: S₄ O(t⁵) Residual Bound

## Goal

Discharge the **two remaining sorries** in the Lean-Trotter project:

1. `norm_suzuki4_fifth_order` in `Suzuki4OrderFive.lean:423`
2. `norm_suzuki4_childs_form` in `Suzuki4ChildsForm.lean:187`

Both reduce to the **same core task**: prove the pointwise residual bound

```
‖w4Deriv A B p τ‖ ≤ C · τ⁴    for all τ ∈ [0, t]
```

where `C` involves 4-fold nested commutator norms. Everything upstream
(Modules 1–3, Module 4a, Module 4b-A1/A2/A3/B1) is sorry-free.

---

## What's Already Proved

| Lemma | File | What it does |
|-------|------|-------------|
| `hasDerivAt_w4Explicit` | `Suzuki4DerivExplicit.lean` | HasDerivAt for all 12 factors (product rule chain) |
| `w4Deriv_eq_w4DerivExplicit` | same | Extracted derivative = explicit 12-term form |
| `w4DerivExplicit_eq_exp_mul_residual` | same | `w4DerivExplicit = exp(-τH) · w4Residual` |
| `norm_w4DerivExplicit_eq_norm_residual` | same | `‖w4DerivExplicit τ‖ = ‖w4Residual τ‖` (anti-Hermitian isometry) |
| `w4DerivExplicit_at_zero` | same | Order-0: `w4DerivExplicit 0 = 0` (via `suzuki4_free_term`) |
| `w4Deriv_at_zero` | same | Corollary: `w4Deriv 0 = 0` |
| `w4Residual_at_zero` | same | `w4Residual 0 = 0` |
| `w4Residual_eq_s4Deriv_sub_H_s4` | same | Cleaner form: `w4Residual = s4' - H·S₄` |
| `suzuki4_free_term` | `Suzuki4CommutatorScaling.lean` | `Σⱼ dⱼ = A + B` (order-0 coefficient identity) |
| `suzuki4_cubic_cancel` | same or imported | `4p³ + q³ = 0` (order-3 coefficient identity) |
| `continuous_w4Deriv` | `Suzuki4Module4.lean` | Continuity of `w4Deriv` (for FTC-2) |
| `norm_w4_sub_one_le_t5_via_residual` | `Suzuki4Module3.lean` | FTC-2: τ⁴ pointwise bound → t⁵ integrated bound |
| `norm_suzuki4_order5_via_module3` | same | Conditional S₄ O(t⁵) (needs pointwise bound as hypothesis) |
| `norm_suzuki4_childs_via_residual` | `Suzuki4ChildsForm.lean` | Conditional Childs-form bound (needs residual bound as hypothesis) |

## The Residual Structure

### The 12-term derivative

`w4DerivExplicit A B p τ` is defined in `Suzuki4DerivExplicit.lean:78–118`.
It's the product-rule expansion of `d/dτ [exp(-τH) · S₄(τ)]`:

```
w4DerivExplicit = Σⱼ₌₀¹¹ (e₀·...·eⱼ₋₁) · (dⱼ · eⱼ) · (eⱼ₊₁·...·e₁₁)
```

where the 12 factors and their derivative insertions are:

| j | Factor eⱼ | Insertion dⱼ | Coefficient |
|---|-----------|-------------|-------------|
| 0 | `exp((-τ)•H)` | `-H = -(A+B)` | -1 |
| 1 | `exp((p/2·τ)•A)` | `(p/2)•A` | p/2 |
| 2 | `exp((p·τ)•B)` | `p•B` | p |
| 3 | `exp((p·τ)•A)` | `p•A` | p |
| 4 | `exp((p·τ)•B)` | `p•B` | p |
| 5 | `exp(((1-3p)/2·τ)•A)` | `((1-3p)/2)•A` | (1-3p)/2 |
| 6 | `exp(((1-4p)·τ)•B)` | `(1-4p)•B` | 1-4p |
| 7 | `exp(((1-3p)/2·τ)•A)` | `((1-3p)/2)•A` | (1-3p)/2 |
| 8 | `exp((p·τ)•B)` | `p•B` | p |
| 9 | `exp((p·τ)•A)` | `p•A` | p |
| 10 | `exp((p·τ)•B)` | `p•B` | p |
| 11 | `exp((p/2·τ)•A)` | `(p/2)•A` | p/2 |

### The residual (conjugated form)

```
w4Residual(τ) = exp(τ·H) · w4DerivExplicit(τ)
```

Equivalently (`w4Residual_eq_s4Deriv_sub_H_s4`):

```
w4Residual(τ) = s4DerivExplicit(τ) - H · S₄(τ)
```

By anti-Hermitian isometry: `‖w4DerivExplicit τ‖ = ‖w4Residual τ‖`, so
bounding one bounds the other.

### Order conditions (what makes the residual O(τ⁴))

The residual `w4Residual(τ)` vanishes to order 3 at τ=0 because of
four algebraic cancellations (the "Suzuki order conditions"):

| Order | Identity | Status | What it means |
|-------|----------|--------|---------------|
| 0 | `Σⱼ dⱼ = 0` (i.e., `-H + (A+B) = 0`) | ✅ `w4DerivExplicit_at_zero` | Free-term cancellation |
| 1 | `Σⱼ cⱼ·Xⱼ = H` (coefficient sum = identity) | 🔴 Not yet formalized | Linear-term cancellation |
| 2 | Palindromic quadratic cancellation | 🔴 Not yet formalized | From S₂ symmetric structure |
| 3 | `4p³ + q³ = 0` (cubic coefficient vanishes) | ✅ `suzuki4_cubic_cancel` (scalar), 🔴 not connected to integrand | Cubic-term cancellation |

---

## Attack Plan

### Strategy: Iterated FTC Extraction (not Taylor expansion)

**Do NOT** try to Taylor-expand the residual and check coefficient-by-coefficient.
That approach requires computing 12×(order) terms and is intractable in Lean.

**Instead**, use the same technique that worked for Strang (Tasks I, K):
iterated FTC (Fundamental Theorem of Calculus) on conjugation differences.

The key identity (already proved as `exp_conj_sub_eq_integral` in
`CommutatorScaling.lean`) is:

```
exp(τ·X) · Y · exp(-τ·X) - Y = ∫₀ᵗ exp(s·X) · [X,Y] · exp(-s·X) ds
```

Each application extracts one commutator and one power of τ:
- 1st FTC: `O(1) → [X,Y] · O(τ)`
- 2nd FTC: `[X,Y] · O(τ) → [X,[X,Y]] · O(τ²)`
- etc.

For S₄, we need 4 levels of FTC extraction (orders 0–3 must cancel,
leaving order 4 as the residual), yielding an `O(τ⁴)` bound involving
4-fold nested commutators.

### Phase 1: Rewrite residual as sum of conjugation differences

**Goal**: Express `w4Residual(τ)` as a sum of 11 terms, each of the form:

```
(prefix) · [exp(cⱼτ·Xⱼ) · dⱼ · exp(-cⱼτ·Xⱼ) - dⱼ] · (suffix)
```

plus correction terms from non-commuting prefixes.

**How**: Factor out `exp(τH)` from the left of each term in
`w4DerivExplicit`, use `exp(τH) · exp(-τH) = 1` to absorb the prefactor,
then group. The cleaner residual form `w4Residual = s4' - H·S₄` is the
starting point.

**Key technique**: The same approach as `hasDerivAt_conj_strang` in
`StrangCommutatorScaling.lean` (design decision #9 in CLAUDE.md):
set each exponential factor as an opaque variable, factor algebraically
via `noncomm_ring`, then handle commutativity rewrites separately.

**Estimated effort**: ~150 lines.

### Phase 2: Apply FTC to each conjugation difference (orders 0–1)

**Goal**: For each conjugation difference
`exp(cⱼτ·Xⱼ)·dⱼ·exp(-cⱼτ·Xⱼ) - dⱼ`, apply `exp_conj_sub_eq_integral`
to extract `[Xⱼ, dⱼ]` and a factor of τ:

```
exp(cτ·X)·Y·exp(-cτ·X) - Y = ∫₀^{cτ} exp(s·X)·[X,Y]·exp(-s·X) ds
```

The residual at this stage has the form `Σ cⱼ·τ · fⱼ(τ)` where each `fⱼ`
involves a conjugated commutator.

**Order-0 cancellation** (already proved): At τ=0, the sum of insertions
`d₀ + d₁ + ... + d₁₁ = 0` by `suzuki4_free_term`. This is why the
integral representation starts at O(τ), not O(1).

**Order-1 cancellation**: The coefficient of τ in the expansion is
`Σⱼ cⱼ·[Xⱼ, dⱼ] = Σⱼ cⱼ²·[Xⱼ, Xⱼ] = 0` (each term is a
self-commutator). This cancellation is trivial in the non-commutative
algebra.

Actually, more precisely: after the first FTC extraction, the τ-linear
coefficient involves `Σⱼ cⱼ · Xⱼ - H = 0` (the order-1 Suzuki condition,
which says the sum of weighted operators equals H). This is the same
identity as the free-term but one order up.

**Certificate approach**: The scalar part `Σⱼ cⱼ = 1` (where cⱼ acts on A
or B) is a polynomial identity in p. Specifically:

```
For A-coefficients: p/2 + p + (1-3p)/2 + (1-3p)/2 + p + p/2 = 1
For B-coefficients: p + p + (1-4p) + p + p = 1
```

Both are trivially `ring`-provable. No external CAS needed here.

**Estimated effort**: ~100 lines.

### Phase 3: Second FTC extraction (order 2)

**Goal**: Apply `exp_conj_sub_comm_eq_double_integral` (from
`StrangCommutatorScaling.lean`) to extract second-order commutators.

**Order-2 cancellation**: The quadratic coefficient involves sums of
products `cⱼ² · [Xⱼ, [Xⱼ, dⱼ]] / 2`. By the palindromic structure of S₄,
these terms cancel pairwise: S₄ = S₂(p)·S₂(p)·S₂(q)·S₂(p)·S₂(p) has a
mirror symmetry, and the second-order terms from the left half cancel those
from the right half.

**Certificate approach**: The cancellation reduces to the polynomial
identity:

```
4·(p/2)² + 4·p² + 2·((1-3p)/2)² + (1-4p)² = 1
```

(i.e., the sum of squared coefficients, weighted by multiplicity). This
is again a single-variable polynomial in p, checkable by `ring` or
`norm_num`.

**If `ring` struggles** (e.g., because the goal has non-commutative
structure mixed with scalar coefficients), use the **two-phase approach**:

1. Factor the non-commutative expression into scalar coefficients times
   fixed commutator monomials using `Algebra.smul_mul_assoc`,
   `Algebra.mul_smul_comm`, and `smul_smul` (same as design decision #12
   in CLAUDE.md).
2. Show each scalar coefficient vanishes using `ring` on the scalar part.

If the scalar identity is complex enough to need external verification,
use the **Gröbner-certificate pattern**:

```python
# In SageMath:
R.<p> = QQ[]
q = 1 - 4*p
# Check that the order-2 coefficient is zero mod (q - (1-4*p)):
f = 4*(p/2)^2 + 4*p^2 + 2*((1-3*p)/2)^2 + (1-4*p)^2 - 1
print(f.reduce([q - 1 + 4*p]))  # Should be 0
```

Then in Lean, the certificate is: `have : f(p) = g(p) · (q - (1-4*p))` by `ring`.

**Estimated effort**: ~200 lines (the palindromic argument is the hardest
part of the order-condition analysis).

### Phase 4: Third FTC extraction (order 3) — the critical step

**Goal**: Apply the triple FTC (`exp_conj_sub_comm2_eq_triple_integral`
from `HigherCommutator.lean`) to extract third-order commutators.

**Order-3 cancellation**: The cubic coefficient is proportional to
`4p³ + q³` (already proved to equal 0 by `suzuki4_cubic_cancel`).

**Key subtlety**: The scalar identity `4p³ + q³ = 0` must be applied
**at the integrand level**, before taking norms. If you take absolute
values first, you get `4p³ + |q|³ = 4p³ + (4p-1)³ ≠ 0` (since q < 0
for the Suzuki parameter). This is exactly why the telescoping approach
in `Suzuki4FullDuhamel.lean` gives O(t³) instead of O(t⁵) — the triangle
inequality destroys the signed cancellation.

**Certificate approach**: The non-commutative cubic coefficient factors as:

```
Σⱼ cⱼ³ · [Xⱼ, [Xⱼ, [Xⱼ, ·]]] / 6
```

By the palindromic structure, the A-type and B-type terms separate.
The A-type scalar sum is `4·(p/2)³ + 2·((1-3p)/2)³ + ... = (4p³+q³)·(something)/6`
and similarly for B-type. Since `4p³ + q³ = 0` (proved), both vanish.

The exact polynomial identity to verify is:

```python
# In SageMath:
R.<p> = QQ[]
q = 1 - 4*p
cubic_identity = 4*p^3 + q^3
print(cubic_identity)  # Should simplify to 0 given q = 1-4p
# Actually: 4p³ + (1-4p)³ = 4p³ + 1 - 12p + 48p² - 64p³ = 1 - 12p + 48p² - 60p³
# This is NOT zero in general! The cancellation only works at the specific
# Suzuki value p = 1/(4 - 4^{1/3}).
#
# More precisely: q³ = (1-4p)³, and the identity 4p³ + q³ = 0 determines p.
# So the certificate uses the polynomial relation 4p³ + (1-4p)³ = 0 directly.
```

**Important**: `suzuki4_cubic_cancel` proves `4p³ + q³ = 0` as a
*hypothesis* on p (specifically, `p = 1/(4-r)` where `r³ = 4`). This is
NOT a polynomial identity in p — it's an algebraic relation that holds at
the specific Suzuki parameter value. The Lean proof uses `r³ = 4` and
`q = 1-4p` to derive it.

**Connection to integrand**: Need to show that the non-commutative
cubic-order term in `w4Residual(τ)` has the form `(4p³ + q³) · M(A,B) · τ³`
for some monomial `M`. Then `suzuki4_cubic_cancel` kills it.

**Estimated effort**: ~150 lines (most work is connecting the scalar
identity to the non-commutative integrand).

### Phase 5: Fourth-order residual bound

**Goal**: After orders 0–3 cancel, the remaining integrand is O(τ⁴).
Bound it using 4-fold commutator norms.

**Approach**: Use `norm_exp_conj_sub_comm2_le_of_skewAdjoint` (from
`HigherCommutator.lean`) or its extension to 4th order, plus triangle
inequality and `norm_integral_le_of_norm_le` to get:

```
‖w4Residual(τ)‖ ≤ C · τ⁴
```

where C involves `‖[X₄,[X₃,[X₂,[X₁,·]]]]‖` for various Xᵢ ∈ {A,B}.

**For the Childs form**: C decomposes into the 8 specific commutators
`childsComm₁` through `childsComm₈` (defined in `Suzuki4ChildsForm.lean`)
with explicit rational coefficients. These coefficients (0.0047–0.0284 in
Childs et al.) are exact rational functions of p, verifiable by `norm_num`.

**Estimated effort**: ~100 lines.

### Phase 6: Assembly

**Goal**: Feed `‖w4Deriv τ‖ ≤ C · τ⁴` into the existing conditional theorems.

- `norm_suzuki4_order5_via_module3` (in `Suzuki4Module3.lean`) gives the
  generic O(t⁵) bound.
- `norm_suzuki4_childs_via_residual` (in `Suzuki4ChildsForm.lean`) gives
  the Childs-form bound with specific commutator coefficients.

**Estimated effort**: ~30 lines (just instantiate the conditionals).

---

## Certificate-Based Polynomial Tactics (Optional Acceleration)

### The Idea

From Shen, Guo, Liu, Zhi, "Automated Tactics for Polynomial Reasoning
in Lean 4" (arXiv:2604.13514, April 2026):

> "Computing Gröbner bases directly inside Lean is impractical...
> we propose a certificate-based approach that combines external CAS
> (SageMath/SymPy) with formal verification in Lean 4."

### How It Applies Here

**Step 1**: In SageMath, compute the exact polynomial identities:

```python
R.<p, q> = QQ[]
I = R.ideal(q - 1 + 4*p)  # Constraint: q = 1-4p

# Order-1 coefficient (A-terms):
f1_A = p/2 + p + (1-3*p)/2 + (1-3*p)/2 + p + p/2 - 1
print(f1_A in I)  # True

# Order-2 coefficient:
f2 = ...  # (the quadratic sum)
print(f2 in I)  # True

# Order-3 coefficient:
f3 = 4*p^3 + q^3
print(f3 in I)  # True
```

**Step 2**: Export certificates (polynomial multipliers gᵢ such that
`fₖ = Σᵢ gᵢ · hᵢ` where hᵢ are the ideal generators).

**Step 3**: In Lean, verify each certificate with `ring` or `linear_combination`.

### When to Use

- **Orders 1–2**: Probably simple enough for `ring` / `linear_combination` directly.
- **Order 3**: `suzuki4_cubic_cancel` already handles the scalar part.
  The polynomial tactic adds value for connecting it to the integrand.
- **Order 4 (Childs coefficients)**: The 8 rational coefficients
  (0.0047, 0.0057, ..., 0.0284) are exact rationals in p. Verifying these
  as Gröbner-certificate ideal memberships would automate the most tedious
  part of Phase 5.

### Practical Recommendation

For the Lean-Trotter project, **do NOT import the full tactic framework**
from arXiv:2604.13514. Instead, use the *idea* of certificates:

1. Compute each polynomial identity in SageMath offline.
2. Express it as `f(p,q) = g(p,q) · (q - 1 + 4·p)` for some explicit `g`.
3. Prove in Lean via `have : f = g * (q - 1 + 4*p) := by ring`.
4. Substitute `q = 1 - 4*p` to conclude `f = 0`.

This gives the benefits of external CAS without the dependency.

---

## Estimated Total Effort

| Phase | Lines | Risk |
|-------|-------|------|
| 1. Conjugation-difference rewrite | ~150 | Medium (12-term bookkeeping) |
| 2. First FTC + order 0-1 cancel | ~100 | Low (follows existing pattern) |
| 3. Second FTC + order 2 cancel | ~200 | Medium (palindromic argument) |
| 4. Third FTC + order 3 cancel | ~150 | Medium (connecting scalar identity to integrand) |
| 5. Fourth-order residual bound | ~100 | Low (norm triangle inequality) |
| 6. Assembly | ~30 | Trivial |
| **Total** | **~730** | |

Compare: `StrangCommutatorScaling.lean` is ~480 lines for the analogous
2nd-order analysis (4 factors, 2 FTC levels). S₄ has 12 factors and 4 FTC
levels, so ~730 lines is reasonable.

---

## Key Files to Read Before Starting

1. `LieTrotter/StrangCommutatorScaling.lean` — the template proof (4 factors, O(t³))
2. `LieTrotter/HigherCommutator.lean` — triple FTC extraction (building block)
3. `LieTrotter/Suzuki4DerivExplicit.lean` — the 12-term derivative (starting point)
4. `LieTrotter/Suzuki4Module3.lean` — the conditional O(t⁵) (endpoint)
5. `LieTrotter/Suzuki4ChildsForm.lean` — the Childs-form conditional (alternative endpoint)

## Key Lemmas to Import

- `exp_conj_sub_eq_integral` (from `CommutatorScaling.lean`) — 1st FTC
- `exp_conj_sub_comm_eq_double_integral` (from `StrangCommutatorScaling.lean`) — 2nd FTC
- `exp_conj_sub_comm2_eq_triple_integral` (from `HigherCommutator.lean`) — 3rd FTC
- `norm_exp_conj_sub_comm2_le_of_skewAdjoint` (from `HigherCommutator.lean`) — 3rd-order bound
- `suzuki4_free_term` — order-0 identity
- `suzuki4_cubic_cancel` — order-3 identity
- `norm_exp_smul_of_skewAdjoint` — anti-Hermitian isometry `‖exp(tX)‖ = 1`

## Critical Design Decisions to Follow

- Work over `NormedAlgebra ℝ 𝔸` (not general 𝕂) — design decision #7
- Use `noncomm_ring` for free-ring factoring, then `abel` for the final step — decision #9
- Factor scalars through products via `Algebra.smul_mul_assoc` / `mul_smul_comm` — decision #12
- Use `module` tactic for smul algebra when `abel` fails on negated scalars — decision #14
- "Subtract-constant-at-τ" trick to avoid Fubini — decision #10
- Bound norms via `norm_integral_le_of_norm_le` (non-constant) + FTC on polynomials — decision from CommutatorScaling
