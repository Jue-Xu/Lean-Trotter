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
import LieTrotter.Suzuki4Module3
import LieTrotter.Suzuki4Module4

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

/-!
## Module 4b-A3: Factorization `w4DerivExplicit = exp(-τH) · w4Residual`

For anti-Hermitian operators, `exp((-τ)•(A+B))` is an isometry, so
bounding `w4DerivExplicit` reduces to bounding `w4Residual` defined as
the "conjugated" form `exp(τ•(A+B)) · w4DerivExplicit`.

This is the simplest factorization (via `exp(τH) · exp(-τH) = 1`). The
"commutator form" `w4Residual = Σⱼ [Lⱼ(τ), dⱼ] · Rⱼ(τ)` is a separate
equivalence proved later when needed for the order-condition analysis.
-/

/-- The "residual" function: conjugate `w4DerivExplicit` by `exp(τH)`. -/
def w4Residual (A B : 𝔸) (p : ℝ) (τ : ℝ) : 𝔸 :=
  exp ((τ : ℝ) • (A + B)) * w4DerivExplicit A B p τ

/-- **Module 4b-A3**: `w4DerivExplicit = exp(-τ•H) · w4Residual`. -/
lemma w4DerivExplicit_eq_exp_mul_residual (A B : 𝔸) (p τ : ℝ) :
    w4DerivExplicit A B p τ = exp ((-τ) • (A + B)) * w4Residual A B p τ := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  unfold w4Residual
  -- Goal: w4Deriv = exp(-τH) * (exp(τH) * w4Deriv)
  -- Reassociate and use exp(-τH) * exp(τH) = 1
  rw [← mul_assoc]
  have hcomm : Commute ((-τ) • (A + B)) ((τ : ℝ) • (A + B)) :=
    (Commute.refl (A + B)).smul_left _ |>.smul_right _
  have hinv : exp ((-τ) • (A + B)) * exp ((τ : ℝ) • (A + B)) = 1 := by
    rw [← exp_add_of_commute hcomm]
    rw [show (-τ) • (A + B) + (τ : ℝ) • (A + B) = (0 : ℝ) • (A + B) from by
      rw [← add_smul]; ring_nf]
    simp
  rw [hinv, one_mul]

/-- At τ=0, `w4Residual` also vanishes (via `w4DerivExplicit_at_zero`). -/
lemma w4Residual_at_zero (A B : 𝔸) (p : ℝ) : w4Residual A B p 0 = 0 := by
  unfold w4Residual
  rw [w4DerivExplicit_at_zero, mul_zero]

/-!
### Anti-Hermitian isometry: `‖w4DerivExplicit τ‖ = ‖w4Residual τ‖`
-/

section AntiHermitianBound
variable [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]

/-- For anti-Hermitian A, B, bounds on `w4Residual` transfer to bounds on
  `w4DerivExplicit` with the same norm (since `exp((-τ)•H)` is unitary). -/
lemma norm_w4DerivExplicit_eq_norm_residual (A B : 𝔸)
    (hA : star A = -A) (hB : star B = -B) (p τ : ℝ) :
    ‖w4DerivExplicit A B p τ‖ = ‖w4Residual A B p τ‖ := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  have hAB : star (A + B) = -(A + B) := by rw [star_add, hA, hB, neg_add]
  rw [w4DerivExplicit_eq_exp_mul_residual]
  -- ‖exp((-τ)•H) * w4Residual‖ = ‖w4Residual‖ since ‖exp((-τ)•H)‖ = 1 is an isometry
  apply le_antisymm
  · calc ‖exp ((-τ) • (A + B)) * w4Residual A B p τ‖
        ≤ ‖exp ((-τ) • (A + B))‖ * ‖w4Residual A B p τ‖ := norm_mul_le _ _
      _ = ‖w4Residual A B p τ‖ := by
          rw [norm_exp_smul_of_skewAdjoint hAB]; ring
  · -- Reverse: ‖w4Residual‖ = ‖exp(τH) * exp(-τH) * w4Residual‖ ≤ 1 * ‖exp(-τH) * w4Residual‖
    have hcomm : Commute ((τ : ℝ) • (A + B)) ((-τ) • (A + B)) :=
      (Commute.refl (A + B)).smul_left _ |>.smul_right _
    have hinv : exp ((τ : ℝ) • (A + B)) * exp ((-τ) • (A + B)) = 1 := by
      rw [← exp_add_of_commute hcomm]
      rw [show (τ : ℝ) • (A + B) + (-τ) • (A + B) = (0 : ℝ) • (A + B) from by
        rw [← add_smul]; ring_nf]
      simp
    calc ‖w4Residual A B p τ‖
        = ‖exp ((τ : ℝ) • (A + B)) * (exp ((-τ) • (A + B)) * w4Residual A B p τ)‖ := by
          rw [← mul_assoc, hinv, one_mul]
      _ ≤ ‖exp ((τ : ℝ) • (A + B))‖ *
          ‖exp ((-τ) • (A + B)) * w4Residual A B p τ‖ := norm_mul_le _ _
      _ = ‖exp ((-τ) • (A + B)) * w4Residual A B p τ‖ := by
          rw [norm_exp_smul_of_skewAdjoint hAB]; ring

end AntiHermitianBound

/-!
## Module 4b-A3': Cleaner residual form `w4Residual = s4' - H·s4`

The exp-factorization form `w4Residual = exp(τH) · w4DerivExplicit` has
an equivalent, more tractable expression: `w4Residual = s4DerivExplicit - H · s4Func`.

This follows from the product rule for `w4Func = exp(-τH) · s4Func`:
  `w4DerivExplicit = -H · exp(-τH) · s4Func + exp(-τH) · s4DerivExplicit`
                   `= exp(-τH) · (s4DerivExplicit - H · s4Func)`  (using [H, exp(-τH)]=0)

Hence `w4Residual = exp(τH) · w4DerivExplicit = s4DerivExplicit - H · s4Func`.

This form has the advantage that s4DerivExplicit and s4Func are both
continuously differentiable (no `Classical.choose`), making subsequent
Taylor / FTC expansions direct.
-/

/-- Explicit 11-term derivative of `s4Func`. -/
def s4DerivExplicit (A B : 𝔸) (p : ℝ) (τ : ℝ) : 𝔸 :=
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
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
  -- 11 product-rule terms
  (d1 * e1) * e2 * e3 * e4 * e5 * e6 * e7 * e8 * e9 * e10 * e11
  + e1 * (d2 * e2) * e3 * e4 * e5 * e6 * e7 * e8 * e9 * e10 * e11
  + e1 * e2 * (d3 * e3) * e4 * e5 * e6 * e7 * e8 * e9 * e10 * e11
  + e1 * e2 * e3 * (d4 * e4) * e5 * e6 * e7 * e8 * e9 * e10 * e11
  + e1 * e2 * e3 * e4 * (d5 * e5) * e6 * e7 * e8 * e9 * e10 * e11
  + e1 * e2 * e3 * e4 * e5 * (d6 * e6) * e7 * e8 * e9 * e10 * e11
  + e1 * e2 * e3 * e4 * e5 * e6 * (d7 * e7) * e8 * e9 * e10 * e11
  + e1 * e2 * e3 * e4 * e5 * e6 * e7 * (d8 * e8) * e9 * e10 * e11
  + e1 * e2 * e3 * e4 * e5 * e6 * e7 * e8 * (d9 * e9) * e10 * e11
  + e1 * e2 * e3 * e4 * e5 * e6 * e7 * e8 * e9 * (d10 * e10) * e11
  + e1 * e2 * e3 * e4 * e5 * e6 * e7 * e8 * e9 * e10 * (d11 * e11)

/-- `HasDerivAt (s4Func A B p) (s4DerivExplicit A B p τ) τ`. -/
lemma hasDerivAt_s4Explicit (A B : 𝔸) (p τ : ℝ) :
    HasDerivAt (s4Func A B p) (s4DerivExplicit A B p τ) τ := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  -- Per-factor derivatives at τ (same as in hasDerivAt_w4Explicit)
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
  convert hs11 using 1
  show s4DerivExplicit A B p τ = _
  unfold s4DerivExplicit
  simp only [Pi.mul_apply]
  noncomm_ring

/-- **Module 4b-A3'**: `w4Residual = s4DerivExplicit - (A+B)·s4Func`.

  This is the cleaner residual form, avoiding the `Classical.choose` inside. -/
lemma w4Residual_eq_s4Deriv_sub_H_s4 (A B : 𝔸) (p τ : ℝ) :
    w4Residual A B p τ = s4DerivExplicit A B p τ - (A + B) * s4Func A B p τ := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  -- Strategy: use HasDerivAt uniqueness to relate w4DerivExplicit and s4DerivExplicit
  -- via the product rule for w4Func = exp(-τH) * s4Func.
  -- w4DerivExplicit = d/dτ w4Func = (d/dτ exp(-τH)) * s4Func + exp(-τH) * s4DerivExplicit
  --                = -H * exp(-τH) * s4Func + exp(-τH) * s4DerivExplicit
  --                = exp(-τH) * (s4DerivExplicit - H * s4Func)   (since [H, e0] = 0)
  -- w4Residual = exp(τH) * w4DerivExplicit = 1 * (s4DerivExplicit - H * s4Func)
  --            = s4DerivExplicit - H * s4Func
  -- Build HasDerivAt for exp(-τH) · s4Func, then equate with hasDerivAt_w4Explicit
  have hpre := hasDerivAt_exp_neg_smul' (A + B) τ
  have hs4 := hasDerivAt_s4Explicit A B p τ
  have hw4_prod := hpre.mul hs4
  -- hw4_prod : HasDerivAt ((fun u => exp((-u)•(A+B))) * s4Func A B p) (prod_deriv) τ
  -- The Pi.mul form equals w4Func A B p
  have hfun : (fun u : ℝ => exp ((-u) • (A + B))) * s4Func A B p = w4Func A B p := by
    funext u
    show exp ((-u) • (A + B)) * s4Func A B p u = w4Func A B p u
    rfl
  rw [hfun] at hw4_prod
  -- hw4_prod : HasDerivAt (w4Func A B p) (prod_deriv) τ
  -- And we have hasDerivAt_w4Explicit : HasDerivAt (w4Func A B p) (w4DerivExplicit ...) τ
  have heq := (hasDerivAt_w4Explicit A B p τ).unique hw4_prod
  -- heq : w4DerivExplicit A B p τ = prod_deriv
  -- prod_deriv is the product-rule output:
  -- (-H * exp(-τH)) * s4Func τ + exp(-τH) * s4DerivExplicit τ
  -- which equals exp(-τH) * (s4DerivExplicit τ - H * s4Func τ) using [H, e0] = 0
  unfold w4Residual
  -- Goal: exp(τH) * w4DerivExplicit = s4DerivExplicit - H*s4Func
  rw [heq]
  -- Goal: exp(τH) * (prod_deriv) = s4DerivExplicit - H*s4Func
  -- prod_deriv = -H·exp(-τH)·s4 + exp(-τH)·s4Deriv
  -- Use Commute of H with exp(-τH) to refactor
  have hcomm_H : (-(A + B)) * exp ((-τ) • (A + B)) = exp ((-τ) • (A + B)) * (-(A + B)) := by
    have h1 : Commute (A + B) (((-τ) : ℝ) • (A + B)) :=
      (Commute.refl (A + B)).smul_right _
    have h2 : Commute (A + B) (exp ((-τ) • (A + B))) := h1.exp_right
    -- h2 : (A+B) * exp(-τH) = exp(-τH) * (A+B)
    rw [neg_mul, h2.eq, mul_neg]
  -- Also need Commute((τ)•(A+B)) ((-τ)•(A+B)) for combining exp(τH) * exp(-τH)
  have hinv_comm : Commute ((τ : ℝ) • (A + B)) ((-τ) • (A + B)) :=
    (Commute.refl (A + B)).smul_left _ |>.smul_right _
  have hinv : exp ((τ : ℝ) • (A + B)) * exp ((-τ) • (A + B)) = 1 := by
    rw [← exp_add_of_commute hinv_comm]
    rw [show (τ : ℝ) • (A + B) + (-τ) • (A + B) = (0 : ℝ) • (A + B) from by
      rw [← add_smul]; ring_nf]
    simp
  -- Rewrite the prod_deriv:
  -- prod_deriv = -(A+B) * exp(-τH) * s4Func τ + exp(-τH) * s4DerivExplicit τ
  -- Factor exp(-τH): prod_deriv = exp(-τH) * (-(A+B) * s4Func τ + s4DerivExplicit τ)
  -- using hcomm_H: -(A+B) * exp(-τH) = exp(-τH) * -(A+B)
  show exp ((τ : ℝ) • (A + B)) * ((-(A + B)) * exp ((-τ) • (A + B)) * s4Func A B p τ +
    exp ((-τ) • (A + B)) * s4DerivExplicit A B p τ) =
    s4DerivExplicit A B p τ - (A + B) * s4Func A B p τ
  rw [hcomm_H]
  -- After rewrite: exp(τH) * (exp(-τH) * -(A+B) * s4Func + exp(-τH) * s4Deriv)
  -- Distribute mul over add, then pull exp(τH) · exp(-τH) = 1
  rw [mul_add]
  rw [show exp ((τ : ℝ) • (A + B)) * (exp ((-τ) • (A + B)) * (-(A + B)) * s4Func A B p τ) =
      (exp ((τ : ℝ) • (A + B)) * exp ((-τ) • (A + B))) * ((-(A + B)) * s4Func A B p τ) from by
    noncomm_ring]
  rw [show exp ((τ : ℝ) • (A + B)) * (exp ((-τ) • (A + B)) * s4DerivExplicit A B p τ) =
      (exp ((τ : ℝ) • (A + B)) * exp ((-τ) • (A + B))) * s4DerivExplicit A B p τ from by
    noncomm_ring]
  rw [hinv, one_mul, one_mul]
  -- Goal: -(A+B) * s4Func τ + s4DerivExplicit τ = s4DerivExplicit τ - (A+B) * s4Func τ
  noncomm_ring

/-!
## Smoothness consequences of the cleaner form

Since `s4Func` is smooth (Module 4a pattern) and `s4DerivExplicit` is
its derivative function, both are C^∞. Hence `w4Residual` (defined as
`s4' - H·s4`) is also C^∞.

This enables Taylor expansion / iterated FTC arguments for subsequent
order-condition analysis.
-/

/-- `s4DerivExplicit` is continuous (composition/products of continuous functions). -/
lemma continuous_s4DerivExplicit (A B : 𝔸) (p : ℝ) :
    Continuous (s4DerivExplicit A B p) := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  unfold s4DerivExplicit
  -- Each exp((c*τ)•X) is continuous; products / sums of continuous are continuous
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
  -- Sum of 11 products, each is continuous
  fun_prop

/-- `s4Func` is continuous. -/
lemma continuous_s4Func (A B : 𝔸) (p : ℝ) : Continuous (s4Func A B p) := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  unfold s4Func
  have hexp : ∀ (c : ℝ) (X : 𝔸),
      Continuous (fun u : ℝ => exp ((c * u) • X)) := fun c X =>
    exp_continuous.comp ((continuous_const.mul continuous_id).smul continuous_const)
  fun_prop

/-- `w4Residual` is continuous. -/
lemma continuous_w4Residual (A B : 𝔸) (p : ℝ) :
    Continuous (w4Residual A B p) := by
  -- w4Residual τ = s4DerivExplicit τ - (A+B) * s4Func τ
  have h : w4Residual A B p = (fun τ => s4DerivExplicit A B p τ - (A + B) * s4Func A B p τ) := by
    funext τ; exact w4Residual_eq_s4Deriv_sub_H_s4 A B p τ
  rw [h]
  exact (continuous_s4DerivExplicit A B p).sub (continuous_const.mul (continuous_s4Func A B p))

/-!
### Smoothness of s4DerivExplicit and w4Residual

For Taylor-remainder bounds in the Phase 5 residual analysis, we need
`ContDiff ℝ ⊤ (w4Residual A B p)`. This follows from:
- `s4Func` is `ContDiff ℝ ⊤` (from Module 4a pattern: analytic exp composed
  with smooth linear maps, products of smooth are smooth)
- `s4DerivExplicit` is `ContDiff ℝ ⊤` (same reasoning; also the derivative
  of s4Func which inherits smoothness)
- `w4Residual = s4DerivExplicit - H·s4Func` is `ContDiff ℝ ⊤` (sum/product
  of smooth functions with constants)
-/

/-- Each exp factor `τ ↦ exp((c·τ)•X)` is smooth (copied from Module 4a). -/
private lemma contDiff_exp_smul_factor_local (X : 𝔸) (c : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun τ : ℝ => exp ((c * τ) • X)) := by
  have heq : (fun τ : ℝ => (c * τ) • X) = (fun τ : ℝ => τ • (c • X)) := by
    funext τ; rw [mul_comm, mul_smul]
  have h_lin : ContDiff ℝ n (fun τ : ℝ => (c * τ) • X) := by
    rw [heq]; exact (contDiff_id (𝕜 := ℝ)).smul contDiff_const
  have h_exp_cd : ContDiff ℝ n (exp : 𝔸 → 𝔸) := contDiff_iff_contDiffAt.mpr fun y =>
    (NormedSpace.exp_analytic (𝕂 := ℝ) y).contDiffAt
  exact h_exp_cd.comp h_lin

/-- `s4Func` is `ContDiff ℝ n` for any `n`. -/
lemma contDiff_s4Func (A B : 𝔸) (p : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (s4Func A B p) := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  unfold s4Func
  have c1  := contDiff_exp_smul_factor_local A (p/2) (n := n)
  have c2  := contDiff_exp_smul_factor_local B p (n := n)
  have c3  := contDiff_exp_smul_factor_local A p (n := n)
  have c4  := contDiff_exp_smul_factor_local B p (n := n)
  have c5  := contDiff_exp_smul_factor_local A ((1-3*p)/2) (n := n)
  have c6  := contDiff_exp_smul_factor_local B (1-4*p) (n := n)
  have c7  := contDiff_exp_smul_factor_local A ((1-3*p)/2) (n := n)
  have c8  := contDiff_exp_smul_factor_local B p (n := n)
  have c9  := contDiff_exp_smul_factor_local A p (n := n)
  have c10 := contDiff_exp_smul_factor_local B p (n := n)
  have c11 := contDiff_exp_smul_factor_local A (p/2) (n := n)
  exact ((((((((((c1.mul c2).mul c3).mul c4).mul c5).mul c6).mul c7).mul c8).mul c9).mul c10).mul c11)

/-- `s4DerivExplicit` is `ContDiff ℝ n` (as a sum of products of smooth exps
  and constant insertions). -/
lemma contDiff_s4DerivExplicit (A B : 𝔸) (p : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (s4DerivExplicit A B p) := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  unfold s4DerivExplicit
  -- Each of the 11 terms is a product of 12 ContDiff functions (1 dⱼ constant + 11 exp factors)
  have c1  := contDiff_exp_smul_factor_local A (p/2) (n := n)
  have c2  := contDiff_exp_smul_factor_local B p (n := n)
  have c3  := contDiff_exp_smul_factor_local A p (n := n)
  have c4  := contDiff_exp_smul_factor_local B p (n := n)
  have c5  := contDiff_exp_smul_factor_local A ((1-3*p)/2) (n := n)
  have c6  := contDiff_exp_smul_factor_local B (1-4*p) (n := n)
  have c7  := contDiff_exp_smul_factor_local A ((1-3*p)/2) (n := n)
  have c8  := contDiff_exp_smul_factor_local B p (n := n)
  have c9  := contDiff_exp_smul_factor_local A p (n := n)
  have c10 := contDiff_exp_smul_factor_local B p (n := n)
  have c11 := contDiff_exp_smul_factor_local A (p/2) (n := n)
  -- dⱼ are constants, hence ContDiff
  have hd1  : ContDiff ℝ n (fun _ : ℝ => ((p/2 : ℝ) • A : 𝔸)) := contDiff_const
  have hd2  : ContDiff ℝ n (fun _ : ℝ => ((p : ℝ) • B : 𝔸)) := contDiff_const
  have hd3  : ContDiff ℝ n (fun _ : ℝ => ((p : ℝ) • A : 𝔸)) := contDiff_const
  have hd4  : ContDiff ℝ n (fun _ : ℝ => ((p : ℝ) • B : 𝔸)) := contDiff_const
  have hd5  : ContDiff ℝ n (fun _ : ℝ => (((1-3*p)/2 : ℝ) • A : 𝔸)) := contDiff_const
  have hd6  : ContDiff ℝ n (fun _ : ℝ => (((1-4*p) : ℝ) • B : 𝔸)) := contDiff_const
  have hd7  : ContDiff ℝ n (fun _ : ℝ => (((1-3*p)/2 : ℝ) • A : 𝔸)) := contDiff_const
  have hd8  : ContDiff ℝ n (fun _ : ℝ => ((p : ℝ) • B : 𝔸)) := contDiff_const
  have hd9  : ContDiff ℝ n (fun _ : ℝ => ((p : ℝ) • A : 𝔸)) := contDiff_const
  have hd10 : ContDiff ℝ n (fun _ : ℝ => ((p : ℝ) • B : 𝔸)) := contDiff_const
  have hd11 : ContDiff ℝ n (fun _ : ℝ => ((p/2 : ℝ) • A : 𝔸)) := contDiff_const
  -- Build each term, then sum
  -- Term 1: (d1 * e1) * e2 * ... * e11
  refine ContDiff.add ?_ ?_
  · refine ContDiff.add ?_ ?_
    refine ContDiff.add ?_ ?_
    refine ContDiff.add ?_ ?_
    refine ContDiff.add ?_ ?_
    refine ContDiff.add ?_ ?_
    refine ContDiff.add ?_ ?_
    refine ContDiff.add ?_ ?_
    refine ContDiff.add ?_ ?_
    refine ContDiff.add ?_ ?_
    · exact ((((((((((hd1.mul c1).mul c2).mul c3).mul c4).mul c5).mul c6).mul c7).mul c8).mul c9).mul c10).mul c11
    · exact ((((((((((c1.mul (hd2.mul c2)).mul c3).mul c4).mul c5).mul c6).mul c7).mul c8).mul c9).mul c10).mul c11)
    · exact ((((((((((c1.mul c2).mul (hd3.mul c3)).mul c4).mul c5).mul c6).mul c7).mul c8).mul c9).mul c10).mul c11)
    · exact ((((((((((c1.mul c2).mul c3).mul (hd4.mul c4)).mul c5).mul c6).mul c7).mul c8).mul c9).mul c10).mul c11)
    · exact ((((((((((c1.mul c2).mul c3).mul c4).mul (hd5.mul c5)).mul c6).mul c7).mul c8).mul c9).mul c10).mul c11)
    · exact ((((((((((c1.mul c2).mul c3).mul c4).mul c5).mul (hd6.mul c6)).mul c7).mul c8).mul c9).mul c10).mul c11)
    · exact ((((((((((c1.mul c2).mul c3).mul c4).mul c5).mul c6).mul (hd7.mul c7)).mul c8).mul c9).mul c10).mul c11)
    · exact ((((((((((c1.mul c2).mul c3).mul c4).mul c5).mul c6).mul c7).mul (hd8.mul c8)).mul c9).mul c10).mul c11)
    · exact ((((((((((c1.mul c2).mul c3).mul c4).mul c5).mul c6).mul c7).mul c8).mul (hd9.mul c9)).mul c10).mul c11)
    · exact ((((((((((c1.mul c2).mul c3).mul c4).mul c5).mul c6).mul c7).mul c8).mul c9).mul (hd10.mul c10)).mul c11)
  · exact ((((((((((c1.mul c2).mul c3).mul c4).mul c5).mul c6).mul c7).mul c8).mul c9).mul c10).mul (hd11.mul c11))

/-- `w4Residual` is `ContDiff ℝ n` for any `n`. -/
lemma contDiff_w4Residual (A B : 𝔸) (p : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (w4Residual A B p) := by
  have heq : w4Residual A B p =
      (fun τ => s4DerivExplicit A B p τ - (A + B) * s4Func A B p τ) := by
    funext τ; exact w4Residual_eq_s4Deriv_sub_H_s4 A B p τ
  rw [heq]
  exact (contDiff_s4DerivExplicit A B p).sub (contDiff_const.mul (contDiff_s4Func A B p))

/-!
## Phase 1 (per MODULE4B-STRATEGY.md): Commutator form

Express `w4Residual` as a sum of 11 commutator terms:

  `w4Residual(τ) = Σⱼ ([Lⱼ(τ), dⱼ] · Rⱼ(τ))`

where Lⱼ = ∏_{i<j} eᵢ, Rⱼ = ∏_{i≥j} eᵢ, and `[Lⱼ, dⱼ] = Lⱼ·dⱼ - dⱼ·Lⱼ`.

Proof outline:
- `w4Residual = s4DerivExplicit - (A+B)·s4Func` (from A3')
- `s4DerivExplicit = Σⱼ Lⱼ·dⱼ·Rⱼ` (definitional unfolding)
- `(A+B)·s4Func = (Σⱼ dⱼ)·s4Func = Σⱼ dⱼ·Lⱼ·Rⱼ` (using `suzuki4_free_term` + `s4Func = Lⱼ·Rⱼ`)
- Subtracting term-by-term: `Σⱼ (Lⱼ·dⱼ - dⱼ·Lⱼ)·Rⱼ = Σⱼ [Lⱼ, dⱼ]·Rⱼ`

The proof reduces to a `noncomm_ring` algebraic identity AFTER substituting
`A+B = Σⱼ dⱼ` (which is `suzuki4_free_term`).
-/

/-!
### Polynomial identities for order-condition cancellations

The operator-level cancellations in Phases 2-4 reduce to scalar
polynomial identities in the Suzuki parameter `p`. We isolate these
identities here so that the operator-level proofs can simply rewrite
using them.
-/

/-- Sum of `cᵢ · cⱼ` over (i, j) pairs with i < j, position i is A, position j is B.
  The 15 AB-pairs are: (1,2), (1,4), (1,6), (1,8), (1,10), (3,4), (3,6),
  (3,8), (3,10), (5,6), (5,8), (5,10), (7,8), (7,10), (9,10). -/
def s4_sumAB (p : ℝ) : ℝ :=
  -- i=1 (A, c=p/2)
  (p/2)*p + (p/2)*p + (p/2)*(1-4*p) + (p/2)*p + (p/2)*p +
  -- i=3 (A, c=p)
  p*p + p*(1-4*p) + p*p + p*p +
  -- i=5 (A, c=(1-3p)/2)
  ((1-3*p)/2)*(1-4*p) + ((1-3*p)/2)*p + ((1-3*p)/2)*p +
  -- i=7 (A, c=(1-3p)/2)
  ((1-3*p)/2)*p + ((1-3*p)/2)*p +
  -- i=9 (A, c=p)
  p*p

/-- Sum of `cᵢ · cⱼ` over (i, j) pairs with i < j, position i is B, position j is A.
  The 15 BA-pairs are: (2,3), (2,5), (2,7), (2,9), (2,11), (4,5), (4,7),
  (4,9), (4,11), (6,7), (6,9), (6,11), (8,9), (8,11), (10,11). -/
def s4_sumBA (p : ℝ) : ℝ :=
  -- i=2 (B, c=p)
  p*p + p*((1-3*p)/2) + p*((1-3*p)/2) + p*p + p*(p/2) +
  -- i=4 (B, c=p)
  p*((1-3*p)/2) + p*((1-3*p)/2) + p*p + p*(p/2) +
  -- i=6 (B, c=1-4p)
  (1-4*p)*((1-3*p)/2) + (1-4*p)*p + (1-4*p)*(p/2) +
  -- i=8 (B, c=p)
  p*p + p*(p/2) +
  -- i=10 (B, c=p)
  p*(p/2)

/-- **Phase 2 polynomial identity (palindromic order-1 cancellation)**:
  `s4_sumAB = s4_sumBA` (both equal 1/2 by computation; equality follows from
  the palindromic symmetry of S₄). Pure scalar polynomial identity in `p`. -/
lemma s4_sumAB_eq_sumBA (p : ℝ) : s4_sumAB p = s4_sumBA p := by
  unfold s4_sumAB s4_sumBA
  ring

/-- Both sums equal `1/2`. -/
lemma s4_sumAB_eq_half (p : ℝ) : s4_sumAB p = 1 / 2 := by
  unfold s4_sumAB
  ring

/-- Both sums equal `1/2`. -/
lemma s4_sumBA_eq_half (p : ℝ) : s4_sumBA p = 1 / 2 := by
  unfold s4_sumBA
  ring

/-!
### Operator-level order-1 cancellation

The polynomial identity `s4_sumAB = s4_sumBA` immediately gives the
operator-level cancellation `Σ_{i<j} [dᵢ, dⱼ] = 0`, which is the
order-1 coefficient of the τ-Taylor expansion of `w4Residual`.

The 55 commutator pairs split into:
- 25 same-type pairs (both A or both B): each `[Xᵢ, Xⱼ] = 0`
- 15 AB pairs (Xᵢ=A, Xⱼ=B): contribute `s4_sumAB · [A, B]`
- 15 BA pairs (Xᵢ=B, Xⱼ=A): contribute `s4_sumBA · [B, A] = -s4_sumBA · [A, B]`

Total = `(s4_sumAB - s4_sumBA) · [A, B] = 0 · [A, B] = 0`.

For brevity, we expand each `[dᵢ, dⱼ] = cᵢcⱼ·(XᵢXⱼ - XⱼXᵢ)`. After
factoring, the sum collapses to `(s4_sumAB - s4_sumBA)·(A·B - B·A) = 0`.
-/

/-!
### Insight: order numbering and Suzuki conditions

The standard Yoshida/Suzuki theory of symmetric (palindromic) integrators
states that EVEN-order BCH terms automatically vanish. The conditions on
parameters appear only at ODD orders.

For `w4Func(t) - 1 = e^{-tH}·S₄(t) - 1` to be O(t⁵), we need
`w4Func^(k)(0) = 0` for k = 1, 2, 3, 4. Equivalently:

| k | Order condition | Where it comes from | Phase |
|---|-----------------|---------------------|-------|
| 1 | `Σⱼ dⱼ = H` (free term) | Consistency `4p+q=1` | B1 ✅ |
| 2 | `s4''(0) = H²`, equivalent to `Σ_{i<j}[dᵢ,dⱼ] = 0` | Palindromic (automatic) | Phase 2 ✅ |
| 3 | `s4'''(0) = H³`, equivalent to coefficient sums ∝ `4p³+q³` | Suzuki cubic (needs `4p³+q³=0`) | Phase 3 🔴 |
| 4 | `s4^(4)(0) = H⁴` | Palindromic + cubic (automatic given 1-3) | Phase 4 🔴 |

**Discovery via symbolic CAS:** for `s4'''(0) - H³`, each operator-monomial
coefficient (ABA, AB², A²B, BAB, BA², B²A) is a scalar multiple of the
Suzuki cubic polynomial `60p³ - 48p² + 12p - 1` (which equals `-(4p³+q³)·15`).
So ALL six coefficients vanish iff `suzuki4_cubic_cancel` holds.

The MODULE4B-STRATEGY.md's claimed order-2 identity
`4·(p/2)² + 4·p² + 2·((1-3p)/2)² + (1-4p)² = 1` is INCORRECT — it
evaluates to 1.32 for Suzuki p, not 1. The actual order-2 condition
is the palindromic identity `Σ_{i<j}[dᵢ,dⱼ] = 0` (proved as
`s4_pairwise_commutator_sum_zero`), which holds STRUCTURALLY for any
palindromic Suzuki construction without further p-dependence.
-/

/-!
### Phase 3 polynomial identities (for order-3 cancellation)

For order-3 of w4Func to vanish, the operator-monomial coefficients of
`s4'''(0) - H³` must each be 0. From CAS analysis these coefficients
are all scalar multiples of `60p³ - 48p² + 12p - 1 = -(4p³+q³)`:

| Monomial | Coefficient | As multiple of (4p³+(1-4p)³) |
|----------|-------------|-------------------------------|
| ABA | `-30p³ + 24p² - 6p + 1/2` | `(1/2)·(4p³+q³)` |
| AB² | `-30p³ + 24p² - 6p + 1/2` | `(1/2)·(4p³+q³)` |
| B²A | `-30p³ + 24p² - 6p + 1/2` | `(1/2)·(4p³+q³)` |
| A²B | `15p³ - 12p² + 3p - 1/4` | `-(1/4)·(4p³+q³)` |
| BA² | `15p³ - 12p² + 3p - 1/4` | `-(1/4)·(4p³+q³)` |
| BAB | `60p³ - 48p² + 12p - 1` | `-(4p³+q³)` |

For Suzuki `p = 1/(4-r), r³=4`, the cubic `4p³ + (1-4p)³ = 0` (proved as
`suzuki4_cubic_cancel`), so all coefficients vanish, giving
`s4'''(0) = H³` and hence `w4Func'''(0) = 0` (order-3 cancellation).
-/

/-- The Suzuki cubic predicate: `4p³ + (1-4p)³ = 0`. Holds for `p = 1/(4-r), r³=4`
  via `suzuki4_cubic_cancel`. -/
def IsSuzukiCubic (p : ℝ) : Prop := 4 * p ^ 3 + (1 - 4 * p) ^ 3 = 0

/-- Phase 3 identity for ABA / AB² / B²A monomial coefficients. -/
lemma suzuki4_phase3_aba (p : ℝ) (h : IsSuzukiCubic p) :
    -30 * p ^ 3 + 24 * p ^ 2 - 6 * p + 1/2 = 0 := by
  unfold IsSuzukiCubic at h
  linear_combination (1/2 : ℝ) * h

/-- Phase 3 identity for A²B / BA² monomial coefficients. -/
lemma suzuki4_phase3_a2b (p : ℝ) (h : IsSuzukiCubic p) :
    15 * p ^ 3 - 12 * p ^ 2 + 3 * p - 1/4 = 0 := by
  unfold IsSuzukiCubic at h
  linear_combination (-1/4 : ℝ) * h

/-- Phase 3 identity for BAB monomial coefficient (= the cubic itself, negated). -/
lemma suzuki4_phase3_bab (p : ℝ) (h : IsSuzukiCubic p) :
    60 * p ^ 3 - 48 * p ^ 2 + 12 * p - 1 = 0 := by
  unfold IsSuzukiCubic at h
  linear_combination (-1 : ℝ) * h

/-- Bridge: `suzuki4_cubic_cancel` implies `IsSuzukiCubic`. -/
lemma isSuzukiCubic_of_suzuki4 {r : ℝ} (hr : r ^ 3 = 4) (hr_ne : 4 - r ≠ 0) :
    IsSuzukiCubic (1 / (4 - r)) := by
  unfold IsSuzukiCubic
  exact suzuki4_cubic_cancel hr hr_ne

/-- **Phase 2 operator-level order-1 cancellation**: the sum of all
  pair-commutators of the Suzuki insertions vanishes.

  This is the τ-linear coefficient of `w4Residual(τ)` near τ=0. It
  vanishes due to the palindromic symmetry of S₄ (Phase 2 of the
  strategy doc). -/
lemma s4_pairwise_commutator_sum_zero (A B : 𝔸) (p : ℝ) :
    -- Sum of [dᵢ, dⱼ] = cᵢcⱼ·(XᵢXⱼ - XⱼXᵢ) over all 55 ordered pairs (i<j).
    -- Same-type pairs vanish trivially. We list only the AB and BA pairs.
    -- Each row corresponds to a fixed first index i.
    -- AB pairs:
    ((p/2 : ℝ) * p) • (A * B - B * A) +
    ((p/2 : ℝ) * p) • (A * B - B * A) +
    ((p/2 : ℝ) * (1-4*p)) • (A * B - B * A) +
    ((p/2 : ℝ) * p) • (A * B - B * A) +
    ((p/2 : ℝ) * p) • (A * B - B * A) +
    (p * p : ℝ) • (A * B - B * A) +
    (p * (1-4*p) : ℝ) • (A * B - B * A) +
    (p * p : ℝ) • (A * B - B * A) +
    (p * p : ℝ) • (A * B - B * A) +
    (((1-3*p)/2) * (1-4*p) : ℝ) • (A * B - B * A) +
    (((1-3*p)/2) * p : ℝ) • (A * B - B * A) +
    (((1-3*p)/2) * p : ℝ) • (A * B - B * A) +
    (((1-3*p)/2) * p : ℝ) • (A * B - B * A) +
    (((1-3*p)/2) * p : ℝ) • (A * B - B * A) +
    (p * p : ℝ) • (A * B - B * A) +
    -- BA pairs (each contributes -cᵢcⱼ·(A·B - B·A) since [B,A] = -[A,B])
    -((p * p : ℝ) • (A * B - B * A)) +
    -((p * ((1-3*p)/2) : ℝ) • (A * B - B * A)) +
    -((p * ((1-3*p)/2) : ℝ) • (A * B - B * A)) +
    -((p * p : ℝ) • (A * B - B * A)) +
    -((p * (p/2) : ℝ) • (A * B - B * A)) +
    -((p * ((1-3*p)/2) : ℝ) • (A * B - B * A)) +
    -((p * ((1-3*p)/2) : ℝ) • (A * B - B * A)) +
    -((p * p : ℝ) • (A * B - B * A)) +
    -((p * (p/2) : ℝ) • (A * B - B * A)) +
    -(((1-4*p) * ((1-3*p)/2) : ℝ) • (A * B - B * A)) +
    -(((1-4*p) * p : ℝ) • (A * B - B * A)) +
    -(((1-4*p) * (p/2) : ℝ) • (A * B - B * A)) +
    -((p * p : ℝ) • (A * B - B * A)) +
    -((p * (p/2) : ℝ) • (A * B - B * A)) +
    -((p * (p/2) : ℝ) • (A * B - B * A))
    = 0 := by
  -- Factor out (A·B - B·A): coefficient is sumAB - sumBA = 0
  have h := s4_sumAB_eq_sumBA p
  -- After factoring, the coefficient on (A·B - B·A) equals s4_sumAB - s4_sumBA
  -- module tactic handles the smul/abelian-group identity
  unfold s4_sumAB s4_sumBA at h
  module

/-- **Phase 1 (commutator form)**: `w4Residual` decomposes as 11 commutator terms.

  Each term `[Lⱼ(τ), dⱼ]·Rⱼ(τ)` vanishes at τ=0 (since Lⱼ(0) = 1 commutes
  with dⱼ trivially). For τ > 0, it can be analyzed via FTC extraction
  (Phases 2-4 of the strategy). -/
theorem w4Residual_eq_comm_sum (A B : 𝔸) (p τ : ℝ) :
    w4Residual A B p τ =
      letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
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
      -- L_j = e_1 · ... · e_{j-1} (empty for j=1)
      -- R_j = e_j · ... · e_{11}
      -- 11 commutator terms: (L_j · d_j - d_j · L_j) · R_j
      (1 * d1 - d1 * 1) * (e1 * e2 * e3 * e4 * e5 * e6 * e7 * e8 * e9 * e10 * e11)
      + (e1 * d2 - d2 * e1) * (e2 * e3 * e4 * e5 * e6 * e7 * e8 * e9 * e10 * e11)
      + (e1 * e2 * d3 - d3 * (e1 * e2)) * (e3 * e4 * e5 * e6 * e7 * e8 * e9 * e10 * e11)
      + (e1 * e2 * e3 * d4 - d4 * (e1 * e2 * e3)) * (e4 * e5 * e6 * e7 * e8 * e9 * e10 * e11)
      + (e1 * e2 * e3 * e4 * d5 - d5 * (e1 * e2 * e3 * e4)) * (e5 * e6 * e7 * e8 * e9 * e10 * e11)
      + (e1 * e2 * e3 * e4 * e5 * d6 - d6 * (e1 * e2 * e3 * e4 * e5)) * (e6 * e7 * e8 * e9 * e10 * e11)
      + (e1 * e2 * e3 * e4 * e5 * e6 * d7 - d7 * (e1 * e2 * e3 * e4 * e5 * e6)) * (e7 * e8 * e9 * e10 * e11)
      + (e1 * e2 * e3 * e4 * e5 * e6 * e7 * d8 - d8 * (e1 * e2 * e3 * e4 * e5 * e6 * e7)) * (e8 * e9 * e10 * e11)
      + (e1 * e2 * e3 * e4 * e5 * e6 * e7 * e8 * d9 - d9 * (e1 * e2 * e3 * e4 * e5 * e6 * e7 * e8)) * (e9 * e10 * e11)
      + (e1 * e2 * e3 * e4 * e5 * e6 * e7 * e8 * e9 * d10 - d10 * (e1 * e2 * e3 * e4 * e5 * e6 * e7 * e8 * e9)) * (e10 * e11)
      + (e1 * e2 * e3 * e4 * e5 * e6 * e7 * e8 * e9 * e10 * d11 - d11 * (e1 * e2 * e3 * e4 * e5 * e6 * e7 * e8 * e9 * e10)) * e11
      := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  -- Use the cleaner form w4Residual = s4DerivExplicit - (A+B)·s4Func
  rw [w4Residual_eq_s4Deriv_sub_H_s4]
  -- Substitute A+B = Σⱼ dⱼ via suzuki4_free_term (in REVERSE)
  rw [show (A + B) = (p/2 : ℝ) • A + (p : ℝ) • B + (p : ℝ) • A + (p : ℝ) • B +
        ((1-3*p)/2 : ℝ) • A + ((1-4*p) : ℝ) • B + ((1-3*p)/2 : ℝ) • A +
        (p : ℝ) • B + (p : ℝ) • A + (p : ℝ) • B + (p/2 : ℝ) • A from
    (suzuki4_free_term A B p).symm]
  -- Now everything unfolds to a noncommutative algebraic identity
  unfold s4DerivExplicit s4Func
  -- noncomm_ring should close this with the substituted free-term identity
  noncomm_ring

/-!
### Iterated-FTC route for order-2/3 bounds

Rather than computing `s4Func^(k)(0)` explicitly for higher `k`, we use
Phase 1's commutator form and iterated FTC. For each `j ≥ 1`:

  `commⱼ(τ) := [Lⱼ(τ), dⱼ] · Rⱼ(τ)`

with `commⱼ(0) = 0` (trivially). The key observation: each commⱼ
involves a multi-exponential `Lⱼ`, whose conjugation structure can be
peeled layer-by-layer using `exp_conj_sub_eq_integral` — one per
exponential factor.

**Phase 5 outline (the final bridge):**
1. For each `j`, bound `‖commⱼ(τ)‖` via iterated FTC on `Lⱼ`'s factors.
2. Sum over `j` and apply the order-1/2/3 cancellations to eliminate
   the leading `τ`, `τ²`, `τ³` contributions.
3. The remaining residual is `O(τ⁴)` with 4-fold-commutator coefficients.

The polynomial-level identities needed at each cancellation stage are
now all proven:
- Order-1: `s4_pairwise_commutator_sum_zero` (palindromic)
- Order-2: automatic (no separate identity, palindromic structure)
- Order-3: `suzuki4_phase3_{aba,a2b,bab}` (all ∝ Suzuki cubic)

Only the operator-level integration + triangle inequality remain.
-/

/-!
### Anti-Hermitian norm of `w4Residual` = Anti-Hermitian norm of `w4DerivExplicit`

For applying Module 3's conditional bound, we need
`‖w4Deriv τ‖ ≤ C · τ⁴`. Combining our results:
- `w4Deriv = w4DerivExplicit` (4b-A2)
- `‖w4DerivExplicit τ‖ = ‖w4Residual τ‖` (4b-A3, anti-Hermitian)
- For palindromic Suzuki: `‖w4Residual τ‖ = O(τ⁴)` (the remaining work)

The following lemma packages the first two equalities for convenient
application.
-/

section AntiHermitianNorm
variable [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]

/-- **Bridge norm equality**: `‖w4Deriv τ‖ = ‖w4Residual τ‖` for anti-Hermitian
  A, B. Combines `w4Deriv_eq_w4DerivExplicit` (4b-A2) and
  `norm_w4DerivExplicit_eq_norm_residual` (4b-A3). -/
lemma norm_w4Deriv_eq_norm_residual (A B : 𝔸)
    (hA : star A = -A) (hB : star B = -B) (p τ : ℝ) :
    ‖w4Deriv A B p τ‖ = ‖w4Residual A B p τ‖ := by
  rw [w4Deriv_eq_w4DerivExplicit]
  exact norm_w4DerivExplicit_eq_norm_residual A B hA hB p τ

/-!
### Final assembly (Phase 6 per strategy doc)

Given the pointwise τ⁴ bound on `w4Residual` (or equivalently `w4Deriv`),
the S₄ O(t⁵) bound follows directly from Module 3's conditional theorem.

This lemma packages the chain for convenient application.
-/

/-- **Final assembly**: given a τ⁴ bound on `‖w4Residual τ‖` (= `‖w4Deriv τ‖`
  by anti-Hermitian isometry), conclude the S₄ O(t⁵) bound with the specified
  constant `C₅ = C/5`.

  This is the endpoint of the Module 4b chain: once Phase 5 produces the
  pointwise bound, this lemma closes `norm_suzuki4_fifth_order` and friends. -/
theorem norm_suzuki4_order5_from_residual_bound (A B : 𝔸)
    (hA : star A = -A) (hB : star B = -B) (p : ℝ) {t : ℝ} (ht : 0 ≤ t)
    {C : ℝ} (hC : 0 ≤ C)
    (hBound : ∀ τ ∈ Set.Icc (0 : ℝ) t, ‖w4Residual A B p τ‖ ≤ C * τ ^ 4) :
    ‖suzuki4Exp A B p t - exp (t • (A + B))‖ ≤ C / 5 * t ^ 5 := by
  -- Convert residual bound to w4Deriv bound via isometry
  have hDerivBound : ∀ τ ∈ Set.Icc (0 : ℝ) t, ‖w4Deriv A B p τ‖ ≤ C * τ ^ 4 := by
    intro τ hτ
    rw [norm_w4Deriv_eq_norm_residual A B hA hB]
    exact hBound τ hτ
  -- Apply Module 3's conditional
  exact norm_suzuki4_order5_via_module3 A B hA hB p ht
    (continuous_w4Deriv A B p) hC hDerivBound

end AntiHermitianNorm

end
