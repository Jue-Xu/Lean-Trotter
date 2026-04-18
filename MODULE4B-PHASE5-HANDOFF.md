# Module 4b Phase 5 Handoff

## Status as of last commit (`6c89f6f`)

**Sorry count: 2** (`norm_suzuki4_fifth_order`, `norm_suzuki4_childs_form` — both endpoint research targets, untouched).

**`Suzuki4DerivExplicit.lean`: 979 lines, 0 sorry, all build-clean.**

The chain to close the remaining sorries is now **end-to-end packaged**:

```
Phase 5 (the only remaining work):
  ‖w4Residual(τ)‖ ≤ C·τ⁴   ← TARGET
       ↓ (norm_suzuki4_order5_from_residual_bound — PROVED)
  ‖S₄(t) - exp(tH)‖ ≤ C/5·t⁵
       ↓ (Module 3 + Childs Form conditionals — PROVED)
  Closes norm_suzuki4_fifth_order ∧ norm_suzuki4_childs_form
```

## What's already proved (15+ commits)

| Component | Lemma | Status |
|---|---|---|
| Module 3 FTC reduction | `norm_suzuki4_order5_via_module3` | ✅ |
| Module 4a continuity | `continuous_w4Deriv` | ✅ |
| 4b-A1 explicit derivative | `hasDerivAt_w4Explicit` | ✅ |
| 4b-A2 uniqueness | `w4Deriv_eq_w4DerivExplicit` | ✅ |
| 4b-A3 exp-factorization | `w4DerivExplicit_eq_exp_mul_residual` | ✅ |
| 4b-A3' cleaner form | `w4Residual_eq_s4Deriv_sub_H_s4` | ✅ |
| 4b-B1 order-0 vanish | `w4Deriv_at_zero` | ✅ |
| Phase 1 commutator form | `w4Residual_eq_comm_sum` | ✅ |
| Phase 2 order-1 palindromic | `s4_pairwise_commutator_sum_zero` | ✅ |
| Phase 3 order-3 polynomials | `suzuki4_phase3_{aba,a2b,bab}` | ✅ |
| Smoothness | `contDiff_w4Residual` | ✅ |
| Bridge norm equality | `norm_w4Deriv_eq_norm_residual` | ✅ |
| Final assembly | `norm_suzuki4_order5_from_residual_bound` | ✅ |

## Phase 5 plan (estimated ~600 lines, multi-session)

### Step 1: Compute s4DerivExplicit'(0) explicitly (~200 lines)

**Goal**: Prove `s4DerivExplicit'(0) = Σⱼ dⱼ² + 2·Σ_{i<j} dᵢdⱼ`.

**Approach**: Each of the 11 terms `Tⱼ = Lⱼ·dⱼ·Rⱼ` of `s4DerivExplicit`
is a product of 12 factors (1 constant `dⱼ` + 11 exp factors). Differentiate
via product rule (only the 11 exp factors contribute non-zero derivatives).
At τ=0, each exp evaluates to 1 and each derivative gives the corresponding
`dₖ`.

For each j, `Tⱼ'(0) = Σ_{k<j} dₖ·dⱼ + dⱼ² + Σ_{k>j} dⱼ·dₖ`.

Summing: `s4DerivExplicit'(0) = Σⱼ dⱼ² + 2·Σ_{i<j} dᵢ·dⱼ`.

For Lean implementation, use `HasDerivAt.mul` chain on the 11-factor products,
similar to `hasDerivAt_w4Explicit` but applied to s4DerivExplicit. The result
is a HasDerivAt with explicit derivative form, which evaluated at τ=0 gives
the desired expression.

**Caveat**: Each term `Tⱼ` has different position for the `dⱼ` insertion, so
11 separate HasDerivAt proofs are needed. Each ~15-20 lines.

### Step 2: Show s4DerivExplicit'(0) = H², hence w4Residual'(0) = 0 (~50 lines)

**Goal**: Conclude `w4Residual'(0) = 0` (= order-2 of w4Func, automatic
from palindromic).

**Approach**:
- `H² = (A+B)² = (Σⱼ dⱼ)²` by `suzuki4_free_term`
- Expand `(Σⱼ dⱼ)² = Σⱼ dⱼ² + Σ_{i<j}(dᵢdⱼ + dⱼdᵢ)` (non-commutative)
- Then `s4DerivExplicit'(0) - H² = Σ_{i<j} (dᵢdⱼ - dⱼdᵢ) = Σ_{i<j} [dᵢ, dⱼ]`
- Apply `s4_pairwise_commutator_sum_zero` (Phase 2) to conclude this = 0
- So `w4Residual'(0) = s4DerivExplicit'(0) - H² = 0`

### Step 3: Compute s4DerivExplicit''(0) explicitly (~250 lines)

**Goal**: Compute the third derivative of s4Func at 0 and show it equals H³
modulo `4p³+q³ = 0`.

**Approach**: Differentiate s4DerivExplicit (sum of 11 terms) once more.
Each term gives 11×(11-1) = 110 sub-terms (or 121 counting position-pairs).
At τ=0, each sub-term is a product of 3 d's.

Result: `s4'''(0) = Σⱼ dⱼ³ + 3·Σ_{i<j}(dᵢ²dⱼ + dᵢdⱼ²) + 6·Σ_{i<j<k} dᵢdⱼdₖ`
(this is the standard 3rd-derivative formula for products of unit-valued
exp factors).

By similar expansion of H³ = (Σⱼ dⱼ)³, the difference s4'''(0) - H³ has
each operator-monomial coefficient (ABA, AB², A²B, BAB, BA², B²A) equal
to a scalar multiple of `4p³+q³`. Apply Phase 3 polynomial identities
(`suzuki4_phase3_{aba,a2b,bab}`) plus `suzuki4_cubic_cancel` to vanish
each coefficient.

### Step 4: τ⁴ pointwise bound (~100 lines)

**Goal**: `‖w4Residual(τ)‖ ≤ C·τ⁴` for some C involving 4-fold commutator
norms.

**Approach**: With `w4Residual^(k)(0) = 0` for k=0,1,2,3 (from Steps 1-3
plus order-0 from B1), apply Taylor's theorem with integral remainder:

```
w4Residual(τ) = ∫₀^τ (τ-s)³/3! · w4Residual^(4)(s) ds
```

Bound:
```
‖w4Residual(τ)‖ ≤ τ⁴/24 · sup_{s∈[0,τ]} ‖w4Residual^(4)(s)‖
```

The 4th derivative is ContDiff (from `contDiff_w4Residual ⊤`), so bounded
on `[0, t]`. The bound constant involves 4-fold commutator-norm products.

Mathlib lemmas to use:
- `intervalIntegral.norm_integral_le_of_norm_le`
- `iteratedDeriv` and Taylor remainder theorems (e.g., from `Mathlib.Analysis.Calculus.Taylor`)

### Step 5: Close the sorries (~30 lines)

Apply `norm_suzuki4_order5_from_residual_bound` with the C from Step 4
to close `norm_suzuki4_fifth_order`. Similarly for `norm_suzuki4_childs_form`
(potentially requiring additional work to match Childs's specific 8-term
coefficient structure — Phase D1, optional).

## Key files and lemmas to import

```lean
import LieTrotter.Suzuki4DerivExplicit  -- All Phase 1-3 + bridge lemmas
import LieTrotter.Suzuki4Module3         -- Module 3 conditional
import LieTrotter.Suzuki4ChildsForm      -- Childs-form conditional
import Mathlib.Analysis.Calculus.Taylor  -- Taylor's theorem with remainder
```

Key lemmas already proved:
- `s4_pairwise_commutator_sum_zero` — order-1 palindromic
- `suzuki4_phase3_aba`, `suzuki4_phase3_a2b`, `suzuki4_phase3_bab` — order-3 ∝ cubic
- `suzuki4_cubic_cancel` — `4p³+q³=0`
- `contDiff_w4Residual` — smoothness for Taylor
- `norm_suzuki4_order5_from_residual_bound` — final assembly

## Pitfalls to avoid

1. **`fun_prop` on s4DerivExplicit**: doesn't work for ContDiff on the 11-term
   sum directly. Use explicit `ContDiff.add` chain (see `contDiff_s4DerivExplicit`
   for the pattern).

2. **`linarith` doesn't work on 𝔸-valued equations**. Use
   `linear_combination (norm := module)` for ℝ-module identities, or
   `noncomm_ring` for non-commutative ring identities.

3. **Pi.mul vs lambda functions in HasDerivAt.mul**: the chain produces
   `Pi.mul` form which doesn't directly unify with explicit lambdas. Use
   `funext + show + rfl` to bridge (see `hasDerivAt_s4Explicit` for the
   pattern in `Suzuki4DerivExplicit.lean`).

4. **MODULE4B-STRATEGY.md's claimed order-2 polynomial identity is wrong** —
   it stated `4·(p/2)² + 4·p² + 2·((1-3p)/2)² + (1-4p)² = 1`, which evaluates
   to 1.32 (not 1) for Suzuki p. The actual order-2 condition is automatic
   from palindromic structure (no separate p-identity beyond Phase 2's
   `s4_pairwise_commutator_sum_zero`).

## Estimated effort

| Step | Lines | Difficulty |
|---|---|---|
| 1. s4DerivExplicit'(0) explicit | ~200 | Medium (mechanical product rules) |
| 2. = H² via suzuki4_free_term + Phase 2 | ~50 | Easy |
| 3. s4DerivExplicit''(0) and = H³ | ~250 | Hard (combinatorial expansion) |
| 4. τ⁴ Taylor bound | ~100 | Medium (Mathlib Taylor API) |
| 5. Close sorries via assembly | ~30 | Trivial |
| **Total** | **~630** | |

## What's been validated by external CAS (sympy)

- `s4''(0) - H² = 0` holds as an algebraic identity (no p-dependence)
- `s4'''(0) - H³` decomposes into 6 monomial-coefficients, each a scalar
  multiple of `60p³ - 48p² + 12p - 1 = -(4p³+q³)` — verified by direct
  symbolic expansion.

These CAS results give us confidence the polynomial identities (Phase 2/3)
are the COMPLETE list of conditions. No additional polynomial cancellations
beyond palindromic + cubic are needed.
