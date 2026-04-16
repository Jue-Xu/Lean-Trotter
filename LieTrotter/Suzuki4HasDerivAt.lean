/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# HasDerivAt for the 12-Factor Conjugated S₄ Product

Computes `HasDerivAt` for `w₄(τ) = exp(-τH) · S₄(τ)` where S₄ has 11
exponential factors. This is **Module 1** of the O(t⁵) S₄ proof —
mechanical product-rule scaffolding with no algebraic simplification.

Modules 2-4 (algebraic collapse, order-condition cancellation, FTC-2
+ integration) consume this lemma but are NOT in this file.

## Strategy

Use `hasDerivAt_exp_smul_mul` for each S₄ factor, plus
`hasDerivAt_exp_smul_const'` (with `(-u)•(A+B) = u•(-(A+B))` normalization)
for the `exp(-uH)` prefactor. Combine via 11 right/left-associated
applications of `HasDerivAt.mul`.

We expose the derivative existentially (∃ D, HasDerivAt _ D _) since the
explicit form is a 12-term sum that Module 2 will simplify.
-/

import LieTrotter.Suzuki4Deriv

noncomputable section

open NormedSpace
open scoped BigOperators

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-- The 11-factor S₄ product as a function of τ. -/
def s4Func (A B : 𝔸) (p : ℝ) (τ : ℝ) : 𝔸 :=
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  exp ((p/2 * τ) • A) * exp ((p * τ) • B) *
  exp ((p * τ) • A) * exp ((p * τ) • B) *
  exp (((1-3*p)/2 * τ) • A) * exp (((1-4*p) * τ) • B) *
  exp (((1-3*p)/2 * τ) • A) * exp ((p * τ) • B) *
  exp ((p * τ) • A) * exp ((p * τ) • B) *
  exp ((p/2 * τ) • A)

/-- The conjugated S₄ product `w₄(τ) = exp(-τH) · S₄(τ)`. -/
def w4Func (A B : 𝔸) (p : ℝ) (τ : ℝ) : 𝔸 :=
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  exp ((-τ) • (A + B)) * s4Func A B p τ

/-!
## HasDerivAt for the 12-factor product

The derivative is exposed existentially. Module 2 (future) will compute
the explicit form by simplifying the raw 12-term sum from `HasDerivAt.mul`.
-/

/-- HasDerivAt for the 11-factor S₄ product `s4Func`.
    The derivative is the raw output of 11 `HasDerivAt.mul` applications. -/
lemma hasDerivAt_s4Func (A B : 𝔸) (p τ : ℝ) :
    ∃ D : 𝔸, HasDerivAt (s4Func A B p) D τ := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  -- 11 individual derivatives via hasDerivAt_exp_smul_mul
  have h1  := hasDerivAt_exp_smul_mul A (p/2) τ
  have h2  := hasDerivAt_exp_smul_mul B p τ
  have h3  := hasDerivAt_exp_smul_mul A p τ
  have h4  := hasDerivAt_exp_smul_mul B p τ
  have h5  := hasDerivAt_exp_smul_mul A ((1-3*p)/2) τ
  have h6  := hasDerivAt_exp_smul_mul B (1-4*p) τ
  have h7  := hasDerivAt_exp_smul_mul A ((1-3*p)/2) τ
  have h8  := hasDerivAt_exp_smul_mul B p τ
  have h9  := hasDerivAt_exp_smul_mul A p τ
  have h10 := hasDerivAt_exp_smul_mul B p τ
  have h11 := hasDerivAt_exp_smul_mul A (p/2) τ
  -- Chain via HasDerivAt.mul, left-associated to match s4Func definition
  have h12 := h1.mul h2
  have h123 := h12.mul h3
  have h1234 := h123.mul h4
  have h12345 := h1234.mul h5
  have h123456 := h12345.mul h6
  have h1234567 := h123456.mul h7
  have h12345678 := h1234567.mul h8
  have h123456789 := h12345678.mul h9
  have h12345678910 := h123456789.mul h10
  have hAll := h12345678910.mul h11
  exact ⟨_, hAll⟩

/-- HasDerivAt for the conjugated S₄ product `w₄(τ) = exp(-τH) · S₄(τ)`.
    The derivative is the raw 12-term product-rule expansion (11 from S₄
    factors + 1 from the exp(-τH) prefactor). -/
lemma hasDerivAt_w4 (A B : 𝔸) (p τ : ℝ) :
    ∃ D : 𝔸, HasDerivAt (w4Func A B p) D τ := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  -- Prefactor derivative: d/dτ exp((-τ)•(A+B))
  -- Normalize (-u) • (A+B) to u • (-(A+B)) so hasDerivAt_exp_smul_const' applies
  have hpre : HasDerivAt (fun u : ℝ => exp ((-u) • (A + B)))
      ((-(A + B)) * exp ((-τ) • (A + B))) τ := by
    simp_rw [show ∀ u : ℝ, (-u) • (A + B) = u • (-(A + B)) from
      fun u => by rw [neg_smul, smul_neg]]
    exact hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-(A + B)) τ
  -- S₄ product derivative
  obtain ⟨_Ds4, hs4⟩ := hasDerivAt_s4Func A B p τ
  -- w₄ = (exp(-τH)) · (S₄), so w₄' = (exp(-τH))' · S₄ + exp(-τH) · S₄'
  exact ⟨_, hpre.mul hs4⟩

/-!
## Continuity helpers (for future Module 4: FTC-2 + integration)
-/

/-- Continuity of the S₄ product (each factor is continuous). -/
private lemma continuous_s4Func (A B : 𝔸) (p : ℝ) : Continuous (s4Func A B p) := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  unfold s4Func
  -- Each factor is exp(c·u·X), continuous
  have hexp : ∀ (c : ℝ) (X : 𝔸),
      Continuous (fun u : ℝ => exp ((c * u) • X)) := fun c X =>
    exp_continuous.comp ((continuous_const.mul continuous_id).smul continuous_const)
  have c1 := hexp (p/2) A
  have c2 := hexp p B
  have c3 := hexp p A
  have c4 := hexp p B
  have c5 := hexp ((1-3*p)/2) A
  have c6 := hexp (1-4*p) B
  have c7 := hexp ((1-3*p)/2) A
  have c8 := hexp p B
  have c9 := hexp p A
  have c10 := hexp p B
  have c11 := hexp (p/2) A
  exact ((((((((((c1.mul c2).mul c3).mul c4).mul c5).mul c6).mul c7).mul c8).mul c9).mul c10).mul c11)

/-- Continuity of the conjugated S₄ product `w₄`. -/
lemma continuous_w4 (A B : 𝔸) (p : ℝ) : Continuous (w4Func A B p) := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  unfold w4Func
  exact (exp_continuous.comp (continuous_neg.smul continuous_const)).mul
    (continuous_s4Func A B p)

end
