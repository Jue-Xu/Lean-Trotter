/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Derivative of the Conjugated S₄ Product

Computes HasDerivAt for w₄(τ) = exp(-τH) · S₄(τ) where
S₄(τ) = exp(a₁τA)·exp(b₁τB)·...·exp(a₆τA) (11 exponentials).

The derivative w₄'(τ) = exp(-τH) · 𝒯₄(τ) · S₄(τ) where 𝒯₄ is the
S₄ residual containing the commutator-scaling error.

## Strategy

Rather than computing the 12-factor product rule monolithically,
we build it from the EXISTING Strang derivative (hasDerivAt_conj_strang)
by composing S₂ steps incrementally.

Define: w₂(τ,c) = exp(-cτH) · S₂(cτ) (conjugated Strang at rate c)
Then: w₄(τ) = w₂(τ,p) · w₂(τ,p) · w₂(τ,q) · w₂(τ,p) · w₂(τ,p)

No — this doesn't work because the H-conjugations don't factor.
We must use the full 12-factor product rule.

Instead, we factor the computation as:
1. HasDerivAt for each exponential factor (12 instances of hasDerivAt_exp_smul_const')
2. Iterated HasDerivAt.mul (11 applications)
3. Algebraic simplification using commutativity and noncomm_ring
-/

import LieTrotter.HigherCommutator

noncomputable section

open NormedSpace MeasureTheory intervalIntegral
open scoped BigOperators

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-!
## Helper: derivative of a product of exponentials

For a product ∏ᵢ exp(cᵢ·τ·Xᵢ), the derivative at τ is
Σⱼ (∏ᵢ<ⱼ exp(cᵢτXᵢ)) · (cⱼXⱼ·exp(cⱼτXⱼ)) · (∏ᵢ>ⱼ exp(cᵢτXᵢ))

Using the fact that Xⱼ commutes with exp(cⱼτXⱼ), this equals
Σⱼ (∏ᵢ≤ⱼ exp(cᵢτXᵢ)) · cⱼXⱼ · (∏ᵢ>ⱼ exp(cᵢτXᵢ))

We prove this incrementally for small products first.
-/

/-- Derivative of exp(c·τ·X) with respect to τ (chain rule). -/
lemma hasDerivAt_exp_smul_mul (X : 𝔸) (c τ : ℝ) :
    HasDerivAt (fun u => exp ((c * u) • X))
      (c • (X * exp ((c * τ) • X))) τ := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  -- Rewrite (c*u)•X = u•(c•X) to use hasDerivAt_exp_smul_const' directly
  simp_rw [show ∀ u : ℝ, (c * u) • X = u • (c • X) from
    fun u => by rw [mul_comm, mul_smul]]
  have h := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (c • X) τ
  -- h : HasDerivAt (fun u => exp(u • (c•X))) ((c•X) * exp(τ • (c•X))) τ
  convert h using 1
  rw [Algebra.smul_mul_assoc]

/-- The free-term identity for S₄: the sum of all operator coefficients equals H = A+B.
  `(p/2)A + pB + pA + pB + ((1-3p)/2)A + (1-4p)B + ((1-3p)/2)A + pB + pA + pB + (p/2)A = A+B` -/
lemma suzuki4_free_term (A B : 𝔸) (p : ℝ) :
    (p/2) • A + p • B + p • A + p • B + ((1-3*p)/2) • A + (1 - 4 * p) • B +
    ((1-3*p)/2) • A + p • B + p • A + p • B + (p/2) • A = A + B := by
  have hA : p/2 + p + (1-3*p)/2 + ((1-3*p)/2) + p + p/2 = 1 := by ring
  have hB : p + p + (1-4*p) + p + p = 1 := by ring
  calc (p/2) • A + p • B + p • A + p • B + ((1-3*p)/2) • A + (1 - 4 * p) • B +
      ((1-3*p)/2) • A + p • B + p • A + p • B + (p/2) • A
      = (p/2 + p + (1-3*p)/2 + ((1-3*p)/2) + p + p/2) • A +
        (p + p + (1-4*p) + p + p) • B := by module
    _ = (1 : ℝ) • A + (1 : ℝ) • B := by rw [hA, hB]
    _ = A + B := by simp

/-- The Suzuki cubic cancellation: 4p³ + (1-4p)³ = 0 when p = 1/(4-r) with r³ = 4.
  Proof: q = 1-4p = 1 - 4/(4-r) = -r/(4-r), so q³ = -r³/(4-r)³ = -4/(4-r)³.
  And 4p³ = 4/(4-r)³. Sum: 4p³ + q³ = (4-4)/(4-r)³ = 0. -/
lemma suzuki4_cubic_cancel {r : ℝ} (hr : r ^ 3 = 4) (hr_ne : 4 - r ≠ 0) :
    let p := 1 / (4 - r)
    4 * p ^ 3 + (1 - 4 * p) ^ 3 = 0 := by
  intro p
  -- p = 1/(4-r), so 4p = 4/(4-r), and q = 1-4p = (4-r-4)/(4-r) = -r/(4-r)
  -- 4p³ = 4·1/(4-r)³ = 4/(4-r)³
  -- q³ = (-r/(4-r))³ = -r³/(4-r)³ = -4/(4-r)³  (using r³=4)
  -- Sum: (4-4)/(4-r)³ = 0
  have h4r : (4 - r) ≠ 0 := hr_ne
  -- Clear denominators: 4p³+(1-4p)³ = (4+(4-r-4)³·(4-r)⁰) / (4-r)³ ...
  -- Simpler: compute directly
  -- 4·(1/(4-r))³ + (1-4/(4-r))³ = 4/(4-r)³ + ((-r)/(4-r))³ = (4-r³)/(4-r)³ = 0
  have key : 4 * (1 / (4 - r)) ^ 3 + (1 - 4 * (1 / (4 - r))) ^ 3 =
      (4 - r ^ 3) / (4 - r) ^ 3 := by field_simp; ring
  rw [key, hr, sub_self, zero_div]
