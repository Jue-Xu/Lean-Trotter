/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Module 4: Continuity of `w4Deriv` (smoothness via analyticity)

This module supplies one of the two ingredients required by Module 3's
FTC-2 reduction (`norm_w4_sub_one_le_t5_via_residual`): namely, the
**continuity** of the extracted derivative `w4Deriv A B p`.

The other ingredient — the pointwise τ⁴ residual bound from Suzuki order
conditions — remains as the genuine algebraic core (Module 4b, future).

## Strategy

`w4Func A B p : ℝ → 𝔸` is a product of 12 exponentials, each of the form
`exp(c · τ • X)` for `c : ℝ`, `X : 𝔸`. Each factor is analytic in τ
(composition of the linear map `τ ↦ (c·τ)•X` with the analytic
exponential `exp`), hence smooth. Products of smooth functions are smooth,
so `w4Func` is `ContDiff ℝ ⊤`. Therefore `deriv (w4Func A B p)` is
continuous (`ContDiff.continuous_deriv`).

Finally, by HasDerivAt uniqueness applied to Module 1's existential
`hasDerivAt_w4`, the extracted `w4Deriv` equals `deriv (w4Func A B p)`
pointwise, so it is continuous.

## What this provides

- `contDiff_w4Func` (PROVED) — w4Func is `ContDiff ℝ ⊤`
- `continuous_w4Deriv` (PROVED) — `Continuous (w4Deriv A B p)`

## What remains for the headline O(t⁵) S₄ bound

Module 4b: the pointwise residual bound `‖w4Deriv A B p τ‖ ≤ C · τ⁴`,
requiring the explicit form of `w4Deriv` and the Suzuki order-condition
algebraic verification. This is the genuine research-level work.
-/

import LieTrotter.Suzuki4Module3
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Deriv

noncomputable section

open NormedSpace

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-!
## Smoothness of a single exponential factor `τ ↦ exp((c·τ) • X)`
-/

/-- Each exponential factor `τ ↦ exp((c·τ) • X)` is smooth. -/
private lemma contDiff_exp_smul_factor (X : 𝔸) (c : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun τ : ℝ => exp ((c * τ) • X)) := by
  -- Step 1: linear map τ ↦ (c·τ)•X is smooth
  have h_lin : ContDiff ℝ n (fun τ : ℝ => (c * τ) • X) := by
    -- (c * τ) • X = τ • (c • X)
    have heq : (fun τ : ℝ => (c * τ) • X) = (fun τ : ℝ => τ • (c • X)) := by
      funext τ; rw [mul_comm, mul_smul]
    rw [heq]
    -- τ ↦ τ • (c•X) is linear (smul by τ on a fixed element), hence smooth
    exact (contDiff_id (𝕜 := ℝ)).smul contDiff_const
  -- Step 2: exp is analytic at every point in 𝔸 (charZero ℝ + complete)
  have h_exp : ∀ y : 𝔸, ContDiffAt ℝ n exp y := fun y =>
    (NormedSpace.exp_analytic (𝕂 := ℝ) y).contDiffAt
  -- Step 3: composition
  have h_exp_cd : ContDiff ℝ n (exp : 𝔸 → 𝔸) := contDiff_iff_contDiffAt.mpr fun y => h_exp y
  exact h_exp_cd.comp h_lin

/-- The prefactor `τ ↦ exp((-τ) • H)` is smooth. -/
private lemma contDiff_exp_neg_smul (H : 𝔸) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun τ : ℝ => exp ((-τ) • H)) := by
  -- (-τ) • H = (-1 * τ) • H
  have heq : (fun τ : ℝ => (-τ) • H) = (fun τ : ℝ => ((-1 : ℝ) * τ) • H) := by
    funext τ; rw [neg_one_mul, neg_smul]
  -- exp ∘ (linear) is smooth
  have h_lin : ContDiff ℝ n (fun τ : ℝ => ((-1 : ℝ) * τ) • H) := by
    have heq2 : (fun τ : ℝ => ((-1 : ℝ) * τ) • H) = (fun τ : ℝ => τ • ((-1 : ℝ) • H)) := by
      funext τ; rw [mul_comm, mul_smul]
    rw [heq2]
    exact (contDiff_id (𝕜 := ℝ)).smul contDiff_const
  have h_exp_cd : ContDiff ℝ n (exp : 𝔸 → 𝔸) := contDiff_iff_contDiffAt.mpr fun y =>
    (NormedSpace.exp_analytic (𝕂 := ℝ) y).contDiffAt
  rw [show (fun τ : ℝ => exp ((-τ) • H)) = exp ∘ (fun τ : ℝ => (-τ) • H) from rfl,
      heq]
  exact h_exp_cd.comp h_lin

/-!
## Smoothness of `s4Func` (11-factor product) and `w4Func` (12-factor)
-/

/-- The 11-factor S₄ product is smooth. -/
private lemma contDiff_s4Func (A B : 𝔸) (p : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (s4Func A B p) := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  unfold s4Func
  -- 11 individual smoothness facts
  have c1  := contDiff_exp_smul_factor A (p/2) (n := n)
  have c2  := contDiff_exp_smul_factor B p (n := n)
  have c3  := contDiff_exp_smul_factor A p (n := n)
  have c4  := contDiff_exp_smul_factor B p (n := n)
  have c5  := contDiff_exp_smul_factor A ((1-3*p)/2) (n := n)
  have c6  := contDiff_exp_smul_factor B (1-4*p) (n := n)
  have c7  := contDiff_exp_smul_factor A ((1-3*p)/2) (n := n)
  have c8  := contDiff_exp_smul_factor B p (n := n)
  have c9  := contDiff_exp_smul_factor A p (n := n)
  have c10 := contDiff_exp_smul_factor B p (n := n)
  have c11 := contDiff_exp_smul_factor A (p/2) (n := n)
  -- Chain via ContDiff.mul, left-associated to match s4Func's structure
  exact ((((((((((c1.mul c2).mul c3).mul c4).mul c5).mul c6).mul c7).mul c8).mul c9).mul c10).mul c11)

/-- The conjugated S₄ product `w₄(τ) = exp(-τ•(A+B)) · S₄(τ)` is smooth. -/
lemma contDiff_w4Func (A B : 𝔸) (p : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (w4Func A B p) := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  unfold w4Func
  exact (contDiff_exp_neg_smul (A + B)).mul (contDiff_s4Func A B p)

/-!
## Continuity of `w4Deriv`

Combining smoothness with `ContDiff.continuous_deriv` gives continuity of
`deriv (w4Func A B p)`. By HasDerivAt uniqueness, this equals `w4Deriv`.
-/

/-- **Module 4 (continuity result)**: The extracted derivative
  `w4Deriv A B p` is continuous. -/
lemma continuous_w4Deriv (A B : 𝔸) (p : ℝ) :
    Continuous (w4Deriv A B p) := by
  -- Step 1: w4Func is C^∞, in particular C¹
  have hCD : ContDiff ℝ 1 (w4Func A B p) := contDiff_w4Func A B p
  -- Step 2: deriv of a C¹ function is continuous
  have hCont : Continuous (deriv (w4Func A B p)) := hCD.continuous_deriv le_rfl
  -- Step 3: w4Deriv = deriv (w4Func A B p) pointwise (by HasDerivAt uniqueness)
  have heq : w4Deriv A B p = deriv (w4Func A B p) := by
    funext τ
    exact (hasDerivAt_w4_explicit A B p τ).deriv.symm
  rw [heq]
  exact hCont

/-!
## Status of Module 4

**Provided (PROVED, no sorry):**
- `contDiff_w4Func`: w4Func is `ContDiff ℝ ⊤`
- `continuous_w4Deriv`: continuity of the extracted derivative

This closes ONE of the two hypotheses required by Module 3's FTC-2
reduction. The remaining hypothesis is the pointwise τ⁴ residual bound:

  ∀ τ ∈ [0, t], ‖w4Deriv A B p τ‖ ≤ C · τ⁴

This requires the genuine algebraic core: explicit derivative computation
+ Suzuki order-condition cancellation at 4 levels. That work remains
deferred (Module 4b, future).

**Order-0 cancellation `w4Deriv A B p 0 = 0`** (deferred):

A natural first sub-result toward the τ⁴ bound. Direct attempt via
chained `HasDerivAt.mul` runs into Pi-multiplication form issues — the
chain produces `HasDerivAt ((f₀ · f₁ · ... · f₁₁ : ℝ → 𝔸) : Pi.mul) D 0`
where the Pi.mul form doesn't reduce to the pointwise `fun u => ...`
form of `w4Func A B p` without significant rewriting work.

A cleaner attempt would either:
(a) define an explicit `w4DerivExplicit` function and prove HasDerivAt
    pointwise (then evaluate at 0 with `simp` + `suzuki4_free_term`), or
(b) prove `HasDerivAt (w4Func A B p) 0 0` by direct limit analysis
    (Taylor expansion of each exp factor to first order).

Both are substantial undertakings; deferred to a future session.
-/

end
