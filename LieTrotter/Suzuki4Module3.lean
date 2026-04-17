/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Module 3: FTC-2 Reduction of S₄ O(t⁵) to a Pointwise Residual Bound

This module reduces the O(t⁵) S₄ bound to a pointwise τ⁴ bound on the
Duhamel residual `w₄'(τ) = w4Deriv A B p τ`. The reduction uses:

1. **Module 2** relation: `‖S₄(t) - exp(tH)‖ = ‖w₄(t) - 1‖` (anti-Hermitian)
2. **FTC-2**: `w₄(t) - w₄(0) = ∫₀ᵗ w₄'(τ) dτ`, with `w₄(0) = 1`
3. **Integral comparison**: `‖∫ f‖ ≤ ∫ ‖f‖ ≤ ∫ C·τ⁴ = C·t⁵/5`

The result is a CONDITIONAL theorem: given continuity of `w4Deriv` and a
pointwise τ⁴ bound, the O(t⁵) S₄ bound follows. The remaining work
(Module 4) is to PRODUCE the pointwise residual bound from the Suzuki
order conditions (palindromic symmetry + 4p³+q³=0).

## Why this is the right reduction

Without the order conditions, the small-τ behavior of `w₄(τ) - 1` is
generically O(τ¹) (one derivative non-zero at 0). To get O(τ⁵) we MUST
have the order-condition cancellation at the integrand level. Module 4
provides the integrand-level analysis; this module provides the clean
"FTC-2 + integration" wrapper.

## What this module provides

- `norm_w4_sub_one_le_t5_via_residual` (PROVED) — the conditional FTC-2 reduction
- `norm_suzuki4_order5_via_module3` (PROVED conditionally) — the S₄ O(t⁵) bound
-/

import LieTrotter.Suzuki4Module2
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section

open NormedSpace MeasureTheory intervalIntegral
open scoped BigOperators

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-!
## FTC-2 reduction (proved unconditionally)

Given continuity of `w4Deriv` and a pointwise τ⁴ bound on its norm,
the integrated bound `‖w₄(t) - 1‖ ≤ C/5 · t⁵` follows by FTC-2 +
`integral_pow`.
-/

/-- **Module 3 core (proved)**: FTC-2 reduction.

  If `w4Deriv` is continuous and pointwise bounded by `C·τ⁴` on `[0, t]`,
  then `‖w₄(t) - 1‖ ≤ C/5 · t⁵`.

  This is the integration step. Module 4 will produce the pointwise bound
  from the Suzuki order conditions. -/
lemma norm_w4_sub_one_le_t5_via_residual (A B : 𝔸) (p : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hCont : Continuous (w4Deriv A B p))
    {C : ℝ}
    (hBound : ∀ τ ∈ Set.Icc (0 : ℝ) t, ‖w4Deriv A B p τ‖ ≤ C * τ ^ 4) :
    ‖w4Func A B p t - 1‖ ≤ C / 5 * t ^ 5 := by
  -- Step 1: FTC-2 to get w₄(t) - 1 = ∫₀ᵗ w₄'(τ) dτ
  have hFTC : (∫ τ in (0)..t, w4Deriv A B p τ) = w4Func A B p t - w4Func A B p 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro τ _
      exact hasDerivAt_w4_explicit A B p τ
    · exact hCont.intervalIntegrable 0 t
  rw [w4Func_zero] at hFTC
  -- So w4Func t - 1 = ∫₀ᵗ w4Deriv τ dτ
  rw [← hFTC]
  -- Step 2: bound the integral using norm_integral_le_of_norm_le
  -- We need: ∀ᵐ τ ∂volume, τ ∈ Set.Ioc 0 t → ‖w4Deriv A B p τ‖ ≤ C * τ ^ 4
  have hbound_int : IntervalIntegrable (fun τ => C * τ ^ 4) MeasureTheory.volume 0 t :=
    (continuous_const.mul (continuous_id.pow 4)).intervalIntegrable 0 t
  have hae : ∀ᵐ τ ∂MeasureTheory.volume, τ ∈ Set.Ioc (0 : ℝ) t →
      ‖w4Deriv A B p τ‖ ≤ C * τ ^ 4 := by
    refine Filter.Eventually.of_forall ?_
    intro τ hτ
    exact hBound τ ⟨le_of_lt hτ.1, hτ.2⟩
  have hint_le : ‖∫ τ in (0:ℝ)..t, w4Deriv A B p τ‖ ≤
      ∫ τ in (0:ℝ)..t, C * τ ^ 4 :=
    intervalIntegral.norm_integral_le_of_norm_le ht hae hbound_int
  -- Step 3: compute ∫₀ᵗ C·τ⁴ dτ = C·t⁵/5
  have hint_eq : (∫ τ in (0:ℝ)..t, C * τ ^ 4) = C * t ^ 5 / 5 := by
    rw [intervalIntegral.integral_const_mul]
    rw [integral_pow]
    push_cast
    ring
  -- Combine: ‖w4Func t - 1‖ ≤ C·t⁵/5 = (C/5)·t⁵
  calc ‖∫ τ in (0:ℝ)..t, w4Deriv A B p τ‖
      ≤ ∫ τ in (0:ℝ)..t, C * τ ^ 4 := hint_le
    _ = C * t ^ 5 / 5 := hint_eq
    _ = C / 5 * t ^ 5 := by ring

section AntiHermitian

variable [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]

/-!
## S₄ O(t⁵) bound: conditional on the residual hypothesis

Combining Module 2's `norm_suzuki4_diff_eq_norm_relative` with the FTC-2
reduction above gives the desired S₄ bound, conditional on the
pointwise residual estimate.
-/

/-- **S₄ O(t⁵) bound** via Module 3's FTC-2 reduction.

  If the Duhamel residual `w4Deriv` is continuous and satisfies a pointwise
  τ⁴ bound on `[0, t]`, then `‖S₄(t) - exp(tH)‖ ≤ C/5 · t⁵`.

  The hypothesis bundles together two pieces that Module 4 will provide:
  (i) continuity of the extracted derivative, and
  (ii) the genuine order-condition cancellation. -/
theorem norm_suzuki4_order5_via_module3 (A B : 𝔸)
    (hA : star A = -A) (hB : star B = -B) (p : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hCont : Continuous (w4Deriv A B p))
    {C : ℝ} (hC : 0 ≤ C)
    (hBound : ∀ τ ∈ Set.Icc (0 : ℝ) t, ‖w4Deriv A B p τ‖ ≤ C * τ ^ 4) :
    ‖suzuki4Exp A B p t - exp (t • (A + B))‖ ≤ C / 5 * t ^ 5 := by
  -- Module 2: ‖S₄ - exp(tH)‖ = ‖w₄(t) - 1‖
  rw [norm_suzuki4_diff_eq_norm_relative A B hA hB p t]
  -- Apply Module 3's FTC-2 reduction
  let _ := hC  -- documentary: C ≥ 0 is part of the intended residual hypothesis
  exact norm_w4_sub_one_le_t5_via_residual A B p ht hCont hBound

/-- **Existential S₄ O(t⁵) bound** (the headline statement, conditional on Module 4).

  Packaged as `∃ C₅, ‖S₄(t) - exp(tH)‖ ≤ C₅ · t⁵` for symmetry with the
  other Trotter bounds in the project. -/
theorem norm_suzuki4_order5_exists_via_module3 (A B : 𝔸)
    (hA : star A = -A) (hB : star B = -B) (p : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hCont : Continuous (w4Deriv A B p))
    {C : ℝ} (hC : 0 ≤ C)
    (hBound : ∀ τ ∈ Set.Icc (0 : ℝ) t, ‖w4Deriv A B p τ‖ ≤ C * τ ^ 4) :
    ∃ C₅ : ℝ, 0 ≤ C₅ ∧ ‖suzuki4Exp A B p t - exp (t • (A + B))‖ ≤ C₅ * t ^ 5 :=
  ⟨C / 5, by positivity,
    norm_suzuki4_order5_via_module3 A B hA hB p ht hCont hC hBound⟩

end AntiHermitian

/-!
## Status of Module 3

**Provided (PROVED, no sorry):**
- `norm_w4_sub_one_le_t5_via_residual`: FTC-2 reduction
- `norm_suzuki4_order5_via_module3`: S₄ O(t⁵) bound (conditional)
- `norm_suzuki4_order5_exists_via_module3`: existential variant

**Architecture insight:**

Modules 1-3 are now sorry-free. The architecture is clean:

  Module 1 (HasDerivAt)
       ↓
  Module 2 (FTC-2 bridge: ‖S₄-exp‖=‖w₄-1‖)
       ↓
  Module 3 (FTC-2 reduction: ∫ ≤ C·t⁵/5)
       ↓
  norm_suzuki4_order5_via_module3 (conditional on residual bound)

The remaining work is **Module 4**: produce the pointwise residual bound
`‖w4Deriv A B p τ‖ ≤ C·τ⁴` from the Suzuki order conditions. This requires:

1. **Explicit form for `w4Deriv`** (replacing the `Classical.choose` from Module 2):
   compute the 12-term product-rule expansion and simplify to
   `exp(-τH) · 𝒯₄(τ) · S₄(τ)` where 𝒯₄ is a sum of 11 conjugation differences.

2. **Continuity of `w4Deriv`** follows from the explicit form (continuous functions composed).

3. **Order-condition cancellation**: expand each conjugation difference to order 3
   via single/double/triple FTC, and verify orders 0-3 vanish:
   - Order 0: `suzuki4_free_term` (already proved)
   - Order 1: palindromic symmetry of S₄
   - Order 2: another polynomial identity
   - Order 3: `suzuki4_cubic_cancel` (4p³+q³=0, already proved)

4. **Order-4 residual bound** via 4-fold commutator FTC iteration.

These four steps are the genuine algebraic core of the O(t⁵) result.
-/

end
