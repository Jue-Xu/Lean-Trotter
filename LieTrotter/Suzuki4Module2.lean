/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Module 2: FTC-2 Integral Representation for the Conjugated S₄ Product

Builds on Module 1 (`Suzuki4HasDerivAt.lean`) to establish:

  S₄(t) - exp(tH) = exp(tH) · ∫₀ᵗ w₄'(τ) dτ

via FTC-2 applied to `w₄(τ) = exp(-τH) · S₄(τ)`.

The derivative `w₄'(τ)` is extracted from Module 1's existential
HasDerivAt via `Classical.choose`.

## What this provides

- `w4Deriv A B p τ`: extracted derivative of w₄ at τ (via Classical.choose)
- `hasDerivAt_w4_explicit`: HasDerivAt with the named derivative
- `w4Func_zero`: w₄(0) = 1 (boundary value)
- `suzuki4_diff_eq_exp_mul_relative`: S₄(t) - exp(tH) = exp(tH) · (w₄(t) - 1)

Module 3 (future) will bound ‖w₄(τ)‖ via the order-condition cancellation.
Module 4 (future) will combine FTC-2 + continuity + bound into the final O(t⁵).
-/

import LieTrotter.Suzuki4HasDerivAt
import LieTrotter.Suzuki4CommutatorScaling

noncomputable section

open NormedSpace MeasureTheory intervalIntegral
open scoped BigOperators Classical

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-!
## Extract derivative via Classical.choose

The Module 1 lemma `hasDerivAt_w4` is existential. We extract the
derivative as a named function for use in FTC-2.
-/

/-- The derivative of `w₄(τ) = exp(-τH) · S₄(τ)` at τ.
    Extracted from Module 1's existential HasDerivAt. -/
def w4Deriv (A B : 𝔸) (p τ : ℝ) : 𝔸 :=
  Classical.choose (hasDerivAt_w4 A B p τ)

/-- HasDerivAt for w₄ with the named derivative `w4Deriv`. -/
lemma hasDerivAt_w4_explicit (A B : 𝔸) (p τ : ℝ) :
    HasDerivAt (w4Func A B p) (w4Deriv A B p τ) τ :=
  Classical.choose_spec (hasDerivAt_w4 A B p τ)

/-!
## Boundary value: w₄(0) = 1

At τ = 0, all exponentials become exp(0) = 1, so the product is 1.
-/

/-- The conjugated S₄ product at τ = 0 equals 1. -/
lemma w4Func_zero (A B : 𝔸) (p : ℝ) : w4Func A B p 0 = 1 := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  unfold w4Func s4Func
  -- All factors become exp(0 • _) = exp(0) = 1
  simp only [neg_zero, zero_smul, mul_zero, exp_zero, mul_one, one_mul]

/-!
## Relating S₄ - exp(tH) to w₄(t) - 1

For anti-Hermitian H (where exp(tH) is invertible with inverse exp(-tH)):

  S₄(t) - exp(tH) = exp(tH) · (exp(-tH) · S₄(t) - 1) = exp(tH) · (w₄(t) - 1)

This bridges from w₄ (which has the FTC-2 representation) to the actual
S₄ error.
-/

/-- S₄(t) - exp(tH) factors as exp(tH) times the relative error w₄(t) - 1. -/
lemma suzuki4_diff_eq_exp_mul_relative (A B : 𝔸) (p t : ℝ) :
    suzuki4Exp A B p t - exp (t • (A + B)) =
      exp (t • (A + B)) * (w4Func A B p t - 1) := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  unfold w4Func
  -- Need: S₄(t) - exp(tH) = exp(tH) * (exp(-tH) * S₄_inner - 1)
  -- where S₄_inner = s4Func A B p t = same as suzuki4Exp A B p t
  have hs4_eq : s4Func A B p t = suzuki4Exp A B p t := by
    unfold s4Func suzuki4Exp
    rfl
  rw [hs4_eq]
  -- Goal: suzuki4Exp - exp(tH) = exp(tH) * (exp(-tH) * suzuki4Exp - 1)
  -- RHS = exp(tH) * exp(-tH) * suzuki4Exp - exp(tH) = 1 * suzuki4Exp - exp(tH)
  have hcomm : Commute (t • (A + B)) ((-t) • (A + B)) :=
    (Commute.refl (A + B)).smul_left t |>.smul_right (-t)
  have hinv : exp (t • (A + B)) * exp ((-t) • (A + B)) = 1 := by
    rw [← exp_add_of_commute hcomm]
    rw [show t • (A + B) + (-t) • (A + B) = (0 : ℝ) • (A + B) from by
      rw [← add_smul]; ring_nf]
    simp
  rw [mul_sub, mul_one, ← mul_assoc, hinv, one_mul]

/-!
## Anti-Hermitian norm bound: ‖S₄(t) - exp(tH)‖ = ‖w₄(t) - 1‖

For anti-Hermitian H, ‖exp(tH)‖ = 1, so the multiplicative factor doesn't
affect the norm.
-/

section AntiHermitian

variable [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]

/-- For anti-Hermitian operators, the S₄ error norm equals the relative error norm. -/
lemma norm_suzuki4_diff_eq_norm_relative (A B : 𝔸)
    (hA : star A = -A) (hB : star B = -B) (p t : ℝ) :
    ‖suzuki4Exp A B p t - exp (t • (A + B))‖ = ‖w4Func A B p t - 1‖ := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  rw [suzuki4_diff_eq_exp_mul_relative]
  -- ‖exp(tH) * X‖ = ‖exp(tH)‖ * ‖X‖ = 1 * ‖X‖ = ‖X‖ ... but need equality, not ≤
  -- For C*-algebras with anti-Hermitian H, exp(tH) is unitary, hence isometric
  -- ‖U * X‖ = ‖X‖ for unitary U
  have hAB : star (A + B) = -(A + B) := by rw [star_add, hA, hB, neg_add]
  have hnorm : ‖exp (t • (A + B))‖ = 1 := norm_exp_smul_of_skewAdjoint hAB t
  -- For ‖U * X‖ = ‖X‖, we use that U is unitary (norm 1 in both directions)
  -- ‖U * X‖ ≤ ‖U‖ * ‖X‖ = ‖X‖ and ‖X‖ = ‖U⁻¹ * U * X‖ ≤ ‖U⁻¹‖ * ‖U * X‖ = ‖U * X‖
  apply le_antisymm
  · calc ‖exp (t • (A + B)) * (w4Func A B p t - 1)‖
        ≤ ‖exp (t • (A + B))‖ * ‖w4Func A B p t - 1‖ := norm_mul_le _ _
      _ = ‖w4Func A B p t - 1‖ := by rw [hnorm]; ring
  · -- ‖w4Func t - 1‖ = ‖exp(-tH) * (exp(tH) * (w4Func t - 1))‖
    have hinv_norm : ‖exp ((-t) • (A + B))‖ = 1 :=
      norm_exp_smul_of_skewAdjoint hAB (-t)
    have hcomm : Commute (t • (A + B)) ((-t) • (A + B)) :=
      (Commute.refl (A + B)).smul_left t |>.smul_right (-t)
    have hinv : exp ((-t) • (A + B)) * exp (t • (A + B)) = 1 := by
      rw [← exp_add_of_commute hcomm.symm]
      rw [show (-t) • (A + B) + t • (A + B) = (0 : ℝ) • (A + B) from by
        rw [← add_smul]; ring_nf]
      simp
    calc ‖w4Func A B p t - 1‖
        = ‖exp ((-t) • (A + B)) * (exp (t • (A + B)) * (w4Func A B p t - 1))‖ := by
          rw [← mul_assoc, hinv, one_mul]
      _ ≤ ‖exp ((-t) • (A + B))‖ * ‖exp (t • (A + B)) * (w4Func A B p t - 1)‖ :=
          norm_mul_le _ _
      _ = ‖exp (t • (A + B)) * (w4Func A B p t - 1)‖ := by rw [hinv_norm]; ring

end AntiHermitian

/-!
## Status of Module 2

Provided in this file:
- `w4Deriv`: named extraction of the Module 1 derivative
- `hasDerivAt_w4_explicit`: HasDerivAt for w₄ with named derivative
- `w4Func_zero`: w₄(0) = 1
- `suzuki4_diff_eq_exp_mul_relative`: factoring of S₄ - exp(tH)
- `norm_suzuki4_diff_eq_norm_relative`: ‖S₄ - exp(tH)‖ = ‖w₄(t) - 1‖ (anti-Hermitian)

**Remaining for Module 2 to fully bridge to FTC-2** (deferred to Module 2.5):
- `Continuous (w4Deriv A B p)`: continuity of the extracted derivative
  - Requires either explicit derivative form or smoothness arguments
- `suzuki4_ftc2_repr`: explicit FTC-2 statement

**Module 3 (norm bound on residual)** can proceed with `‖w4Func t - 1‖`
directly, using the relation above.
-/

end
