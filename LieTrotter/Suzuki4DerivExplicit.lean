/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Module 4b-A1: Explicit Form of `w4Deriv`

This module defines `w4DerivExplicit A B p τ` as the explicit 12-term
product-rule sum and proves `HasDerivAt (w4Func A B p) (w4DerivExplicit A B p τ) τ`.

This unwraps Module 1's existential `hasDerivAt_w4` (which uses
`Classical.choose`) into a concrete handle on the derivative, suitable
for the order-condition cancellation analysis in subsequent Module 4b
sub-tasks.

## The 12-term explicit form

`w4Func A B p τ = exp((-τ)•H) · e₁(τ) · e₂(τ) · ... · e₁₁(τ)` where the
11 exponentials follow the Suzuki S₄ structure. The product-rule
expansion of `d/dτ w4Func` yields:

  w4DerivExplicit(τ) = -H · w4Func(τ) +
    Σⱼ₌₁^¹¹ cⱼ · (∏_{i<j} eᵢ(τ)) · Xⱼ · (∏_{i≥j} eᵢ(τ))

where (cⱼ, Xⱼ) are the (coefficient, operator) pairs for each S₄ factor.
-/

import LieTrotter.Suzuki4HasDerivAt
import LieTrotter.Suzuki4CommutatorScaling
import LieTrotter.Suzuki4Module2

noncomputable section

open NormedSpace

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-!
## Single-factor derivative helper (cleaner form)

The Suzuki4Deriv lemma `hasDerivAt_exp_smul_mul` gives the derivative as
`c • (X * exp(...))`. For chaining, the multiplicative form
`(c • X) * exp(...)` is more convenient.
-/

/-- Cleaner form of `hasDerivAt_exp_smul_mul`: the derivative of
  `exp((c·τ)•X)` is `(c•X) * exp((c·τ)•X)` (multiplicative). -/
private lemma hasDerivAt_exp_smul_mul' (X : 𝔸) (c τ : ℝ) :
    HasDerivAt (fun u : ℝ => exp ((c * u) • X))
      ((c • X) * exp ((c * τ) • X)) τ := by
  have h := hasDerivAt_exp_smul_mul X c τ
  rwa [← Algebra.smul_mul_assoc] at h

/-- Derivative of the prefactor `exp((-τ)•H)` is `(-H) * exp((-τ)•H)`. -/
private lemma hasDerivAt_exp_neg_smul' (H : 𝔸) (τ : ℝ) :
    HasDerivAt (fun u : ℝ => exp ((-u) • H)) ((-H) * exp ((-τ) • H)) τ := by
  -- Normalize (-u) • H to u • (-H), apply hasDerivAt_exp_smul_const'
  have heq : (fun u : ℝ => exp ((-u) • H)) = (fun u : ℝ => exp (u • (-H))) := by
    funext u; rw [neg_smul, smul_neg]
  rw [heq]
  have h := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-H) τ
  -- h : HasDerivAt _ ((-H) * exp (τ • (-H))) τ
  -- Need: ((-H) * exp ((-τ) • H))
  convert h using 1
  rw [neg_smul, smul_neg]

/-!
## The explicit derivative

We define `w4DerivExplicit` as the 12-term product-rule sum.
-/

/-- The explicit 12-term derivative of `w4Func A B p` at `τ`.

  Each term corresponds to differentiating one of the 12 factors:
  the prefactor `exp(-τH)` (giving `-H · w4Func`) plus 11 terms from
  differentiating each S₄ exponential `exp((cⱼτ)Xⱼ)` (giving
  `(prefix) · (cⱼ•Xⱼ) · eⱼ · (suffix)`). -/
def w4DerivExplicit (A B : 𝔸) (p : ℝ) (τ : ℝ) : 𝔸 :=
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  let H : 𝔸 := A + B
  let e0  : 𝔸 := exp ((-τ) • H)
  let e1  : 𝔸 := exp ((p/2 * τ) • A)
  let e2  : 𝔸 := exp ((p * τ) • B)
  let e3  : 𝔸 := exp ((p * τ) • A)
  let e4  : 𝔸 := exp ((p * τ) • B)
  let e5  : 𝔸 := exp (((1-3*p)/2 * τ) • A)
  let e6  : 𝔸 := exp (((1-4*p) * τ) • B)
  let e7  : 𝔸 := exp (((1-3*p)/2 * τ) • A)
  let e8  : 𝔸 := exp ((p * τ) • B)
  let e9  : 𝔸 := exp ((p * τ) • A)
  let e10 : 𝔸 := exp ((p * τ) • B)
  let e11 : 𝔸 := exp ((p/2 * τ) • A)
  -- Insertion operators (the cⱼ•Xⱼ at position j)
  let d0  : 𝔸 := -H
  let d1  : 𝔸 := (p/2 : ℝ) • A
  let d2  : 𝔸 := (p : ℝ) • B
  let d3  : 𝔸 := (p : ℝ) • A
  let d4  : 𝔸 := (p : ℝ) • B
  let d5  : 𝔸 := ((1-3*p)/2 : ℝ) • A
  let d6  : 𝔸 := ((1-4*p) : ℝ) • B
  let d7  : 𝔸 := ((1-3*p)/2 : ℝ) • A
  let d8  : 𝔸 := (p : ℝ) • B
  let d9  : 𝔸 := (p : ℝ) • A
  let d10 : 𝔸 := (p : ℝ) • B
  let d11 : 𝔸 := (p/2 : ℝ) • A
  -- 12-term product-rule sum: term j inserts dⱼ between (prefix) and eⱼ·(suffix)
  (d0 * e0) * e1 * e2 * e3 * e4 * e5 * e6 * e7 * e8 * e9 * e10 * e11
  + e0 * (d1 * e1) * e2 * e3 * e4 * e5 * e6 * e7 * e8 * e9 * e10 * e11
  + e0 * e1 * (d2 * e2) * e3 * e4 * e5 * e6 * e7 * e8 * e9 * e10 * e11
  + e0 * e1 * e2 * (d3 * e3) * e4 * e5 * e6 * e7 * e8 * e9 * e10 * e11
  + e0 * e1 * e2 * e3 * (d4 * e4) * e5 * e6 * e7 * e8 * e9 * e10 * e11
  + e0 * e1 * e2 * e3 * e4 * (d5 * e5) * e6 * e7 * e8 * e9 * e10 * e11
  + e0 * e1 * e2 * e3 * e4 * e5 * (d6 * e6) * e7 * e8 * e9 * e10 * e11
  + e0 * e1 * e2 * e3 * e4 * e5 * e6 * (d7 * e7) * e8 * e9 * e10 * e11
  + e0 * e1 * e2 * e3 * e4 * e5 * e6 * e7 * (d8 * e8) * e9 * e10 * e11
  + e0 * e1 * e2 * e3 * e4 * e5 * e6 * e7 * e8 * (d9 * e9) * e10 * e11
  + e0 * e1 * e2 * e3 * e4 * e5 * e6 * e7 * e8 * e9 * (d10 * e10) * e11
  + e0 * e1 * e2 * e3 * e4 * e5 * e6 * e7 * e8 * e9 * e10 * (d11 * e11)

/-!
## HasDerivAt for the explicit form

Building the chain via `HasDerivAt.mul` and showing the chained
derivative equals our explicit 12-term sum.
-/

/-- **Module 4b-A1**: `HasDerivAt (w4Func A B p) (w4DerivExplicit A B p τ) τ`.

  The 12-factor product rule, with explicit derivative form. -/
lemma hasDerivAt_w4Explicit (A B : 𝔸) (p τ : ℝ) :
    HasDerivAt (w4Func A B p) (w4DerivExplicit A B p τ) τ := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  -- Per-factor derivatives at τ
  have hpre := hasDerivAt_exp_neg_smul' (A + B) τ
  have h1  := hasDerivAt_exp_smul_mul' A (p/2) τ
  have h2  := hasDerivAt_exp_smul_mul' B p τ
  have h3  := hasDerivAt_exp_smul_mul' A p τ
  have h4  := hasDerivAt_exp_smul_mul' B p τ
  have h5  := hasDerivAt_exp_smul_mul' A ((1-3*p)/2) τ
  have h6  := hasDerivAt_exp_smul_mul' B (1-4*p) τ
  have h7  := hasDerivAt_exp_smul_mul' A ((1-3*p)/2) τ
  have h8  := hasDerivAt_exp_smul_mul' B p τ
  have h9  := hasDerivAt_exp_smul_mul' A p τ
  have h10 := hasDerivAt_exp_smul_mul' B p τ
  have h11 := hasDerivAt_exp_smul_mul' A (p/2) τ
  -- Build LEFT-associated chain matching s4Func structure
  have hs2  := h1.mul h2
  have hs3  := hs2.mul h3
  have hs4  := hs3.mul h4
  have hs5  := hs4.mul h5
  have hs6  := hs5.mul h6
  have hs7  := hs6.mul h7
  have hs8  := hs7.mul h8
  have hs9  := hs8.mul h9
  have hs10 := hs9.mul h10
  have hs11 := hs10.mul h11
  -- Now hs11 : HasDerivAt (s4-product) (chained-s4-deriv) τ
  -- Combine with prefactor
  have hw4 := hpre.mul hs11
  -- hw4 : HasDerivAt (e0 * s4-product) (chained-w4-deriv) τ
  -- The function (e0 * s4-product) is definitionally equal to w4Func A B p
  -- The chained derivative equals w4DerivExplicit A B p τ after distributing
  convert hw4 using 1
  -- Goal: w4DerivExplicit A B p τ = chained-w4-deriv
  -- Unfold w4DerivExplicit and use noncomm_ring
  show w4DerivExplicit A B p τ = _
  unfold w4DerivExplicit
  -- The chained derivative has Pi.mul function applications; reduce them
  simp only [Pi.mul_apply]
  noncomm_ring

/-!
## Module 4b-A2: `w4Deriv = w4DerivExplicit` via uniqueness

By HasDerivAt uniqueness, the extracted `w4Deriv A B p τ` (from
Module 2's `Classical.choose`) equals our explicit form.
-/

/-- **Module 4b-A2**: `w4Deriv` (extracted via Module 2's `Classical.choose`)
  equals the explicit 12-term sum pointwise. -/
lemma w4Deriv_eq_w4DerivExplicit (A B : 𝔸) (p τ : ℝ) :
    w4Deriv A B p τ = w4DerivExplicit A B p τ := by
  -- HasDerivAt uniqueness: two HasDerivAt's of the same function give equal derivatives
  exact (hasDerivAt_w4_explicit A B p τ).unique (hasDerivAt_w4Explicit A B p τ)

/-- **Functional version of 4b-A2**: `w4Deriv = w4DerivExplicit` as functions. -/
lemma w4Deriv_funext (A B : 𝔸) (p : ℝ) :
    w4Deriv A B p = w4DerivExplicit A B p := by
  funext τ
  exact w4Deriv_eq_w4DerivExplicit A B p τ

/-!
## Module 4b-B1: Order-0 cancellation `w4Deriv A B p 0 = 0`

At τ=0, every exponential factor reduces to `exp(0) = 1`. Each of the
12 terms in `w4DerivExplicit` collapses to a single `dⱼ` (with
d₀ = -(A+B)). The sum equals `-(A+B) + Σⱼ₌₁^¹¹ dⱼ = 0` by
`suzuki4_free_term`.
-/

/-- **Module 4b-B1**: the derivative `w4Deriv A B p 0` vanishes at τ=0. -/
lemma w4DerivExplicit_at_zero (A B : 𝔸) (p : ℝ) :
    w4DerivExplicit A B p 0 = 0 := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  unfold w4DerivExplicit
  -- All `(c * 0) • X = 0 • X = 0`, `exp 0 = 1`
  simp only [mul_zero, zero_smul, exp_zero, mul_one, one_mul, neg_zero]
  -- Remaining goal is an algebraic identity: the 12 dⱼ terms sum to 0
  -- d₀ = -(A+B), d₁ = p/2•A, d₂ = p•B, ..., d₁₁ = p/2•A
  -- Sum: -(A+B) + (A+B) = 0 via suzuki4_free_term
  have hfree := suzuki4_free_term A B p
  -- hfree : (p/2)•A + p•B + p•A + p•B + ((1-3p)/2)•A + (1-4p)•B +
  --         ((1-3p)/2)•A + p•B + p•A + p•B + (p/2)•A = A + B
  linear_combination (norm := module) hfree

/-- Corollary: `w4Deriv A B p 0 = 0`. -/
lemma w4Deriv_at_zero (A B : 𝔸) (p : ℝ) : w4Deriv A B p 0 = 0 := by
  rw [w4Deriv_eq_w4DerivExplicit, w4DerivExplicit_at_zero]

end
