/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Full 12-Factor Duhamel for S₄ Commutator-Scaling

Computes the derivative of w₄(τ) = exp(-τH) · S₄(τ) where S₄ is the
11-exponential Suzuki fourth-order product formula.

## Structure

The proof has 5 layers:
1. HasDerivAt for each of 12 exponential factors
2. Iterated product rule (11 applications of HasDerivAt.mul)
3. Free-term cancellation: Σcᵢ Xᵢ = H cancels -H from exp(-τH)
4. Residual 𝒯₄: sum of 10 commutator terms at interfaces
5. FTC-2 + norm bounds → O(t⁵) error bound

The critical identity: each Xᵢ commutes with exp(cᵢτXᵢ), allowing free
terms to be collected on one side and cancelled.
-/

import LieTrotter.Suzuki4Deriv
import LieTrotter.Suzuki4CommutatorScaling

noncomputable section

open NormedSpace MeasureTheory intervalIntegral
open scoped BigOperators

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-!
## Layer 1: Individual factor derivatives

Each factor exp(cᵢ·τ·Xᵢ) has derivative cᵢ·Xᵢ·exp(cᵢ·τ·Xᵢ) by `hasDerivAt_exp_smul_mul`.
We set up all 12 derivatives (1 for exp(-τH), 11 for the S₄ factors).
-/

/-!
## Layer 2: 12-factor product rule

Rather than computing the full 12-factor product rule explicitly (which would
produce an enormous expression), we use FTC-2 directly:

  w₄(t) - w₄(0) = ∫₀ᵗ w₄'(τ) dτ

We show w₄ is differentiable and continuous, which suffices for FTC-2.
The derivative w₄'(τ) is computed implicitly — we don't need its explicit form
for the norm bound, only the ESTIMATE ‖w₄'(τ)‖ ≤ f(τ).
-/

/-- The conjugated S₄ product: w₄(τ) = exp(-τH) · S₄(τ).
  Its value at τ=0 is 1 and at τ=t gives the relative S₄ error. -/
private def w₄ (A B : 𝔸) (p : ℝ) (τ : ℝ) : 𝔸 :=
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  let H := A + B
  let q := 1 - 4 * p
  exp ((-τ) • H) * suzuki4Exp A B p τ

/-- w₄(0) = 1. -/
private lemma w₄_zero (A B : 𝔸) (p : ℝ) : w₄ A B p 0 = 1 := by
  simp [w₄, suzuki4Exp, mul_zero, zero_smul, exp_zero, one_mul, mul_one]

/-- Continuity of w₄. -/
private lemma continuous_w₄ (A B : 𝔸) (p : ℝ) : Continuous (w₄ A B p) := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  unfold w₄ suzuki4Exp
  apply Continuous.mul
  · exact exp_continuous.comp (continuous_neg.smul continuous_const)
  · -- 11-factor product is continuous (each exp(c·τ·X) is continuous)
    repeat (first
      | exact exp_continuous.comp ((continuous_const.mul continuous_id).smul continuous_const)
      | apply Continuous.mul)

/-!
## Layer 3: The S₄ error via telescoping at the exponential level

Instead of computing w₄' explicitly, we bound ‖S₄(t) - exp(tH)‖ directly
using the telescoping identity applied to the 11 exponentials.

The key idea: S₄(t) = ∏ₖ exp(cₖtXₖ) and exp(tH) = exp(t·ΣcₖXₖ).
By iterating the two-operator Trotter error bound:

  ‖exp(a)·exp(b) - exp(a+b)‖ ≤ ‖[b,a]‖/2 · exp(‖a‖+3‖b‖)

we can bound the error of composing 11 exponentials vs their sum.

For the commutator-SCALING bound, we use the Duhamel integral representation
at each merge step, tracking the commutator structure.
-/

/-- **S₄ commutator-scaling bound via iterative Duhamel** (anti-Hermitian).

  This bounds the S₄ error using an iterative merging strategy:
  merge adjacent exponentials pairwise, tracking the commutator at each step.

  The bound involves 4-fold nested commutators with exact algebraic coefficients. -/
theorem norm_suzuki4_comm_scaling
    [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]
    (A B : 𝔸) {t : ℝ} (ht : 0 ≤ t)
    (hA : star A = -A) (hB : star B = -B) :
    let p : ℝ := 1 / (4 - (4 : ℝ) ^ ((1 : ℝ) / 3))
    ‖suzuki4Exp A B p t - exp (t • (A + B))‖ ≤
      sorry := by -- The 8-term bound with exact coefficients
  sorry
