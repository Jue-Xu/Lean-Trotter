/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Module 4b Phase 5: Taylor-Reduction for `w4Residual`

This module reduces the τ⁴ pointwise bound for `w4Residual A B p τ` to
four concrete order-condition hypotheses on its iterated derivatives at
τ = 0.

## Strategy

`w4Residual` is `ContDiff ℝ ⊤` (proved in Suzuki4DerivExplicit as
`contDiff_w4Residual`). Apply Mathlib's
`exists_taylor_mean_remainder_bound` with `n = 3` to obtain:

    ∃ C, ∀ τ ∈ [0, t], ‖w4Residual(τ) - taylorPoly₃(τ)‖ ≤ C · τ⁴

If the Taylor polynomial of order 3 vanishes identically
(`taylorPoly₃ ≡ 0`, which is equivalent to vanishing of the first four
iterated-derivative values at τ = 0), then we get the desired bound

    ‖w4Residual(τ)‖ ≤ C · τ⁴  on [0, t].

## Status

This file provides:
- `exists_norm_w4Residual_t4_bound_of_zero_taylor`: the conditional
  reduction (PROVED)
- `taylorWithin_eq_zero_of_iteratedDerivs_zero`: the Taylor polynomial
  vanishing lemma (PROVED)
- `norm_suzuki4_fifth_order_of_vanishings`: close `norm_suzuki4_fifth_order`
  conditional on the four iteratedDerivWithin vanishings (PROVED)
- `norm_suzuki4_childs_form_of_vanishings`: close `norm_suzuki4_childs_form`
  conditional on the same (PROVED)

The residual work is the four derivative-vanishing hypotheses, which
are the genuine Module 4b content (order 0: proved via
`w4Residual_at_zero`; orders 1-3: Suzuki order conditions `palindromic
+ cubic cancellation` — see comments).
-/

import LieTrotter.Suzuki4DerivExplicit
import LieTrotter.Suzuki4ChildsForm
import Mathlib.Analysis.Calculus.Taylor

noncomputable section

open NormedSpace Set

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-!
## Taylor polynomial vanishes iff the first `n+1` iterated derivatives vanish

For a `ContDiff` function `f : ℝ → 𝔸` with `iteratedDerivWithin k f (Icc 0 t) 0 = 0`
for all `k ≤ n`, the Taylor polynomial `taylorWithinEval f n (Icc 0 t) 0 τ` is 0.
-/

/-- If the first `n+1` iterated derivatives (within `Icc 0 t`) of `f` at `0` all vanish,
  then the `n`th Taylor polynomial of `f` at `0` (within `Icc 0 t`) is identically `0`. -/
lemma taylorWithin_eq_zero_of_iteratedDerivs_zero
    {𝔸 : Type*} [NormedAddCommGroup 𝔸] [NormedSpace ℝ 𝔸]
    {f : ℝ → 𝔸} {n : ℕ} {t τ : ℝ}
    (hZero : ∀ k, k ≤ n → iteratedDerivWithin k f (Icc 0 t) 0 = 0) :
    taylorWithinEval f n (Icc 0 t) 0 τ = 0 := by
  rw [taylor_within_apply]
  apply Finset.sum_eq_zero
  intro k hk
  rw [hZero k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)), smul_zero]

/-!
## Main conditional reduction

Given the four order-vanishing hypotheses, produce the τ⁴ bound on `w4Residual`.
-/

/-- **Phase 5 conditional reduction**: given the vanishing of the first four
  iterated derivatives of `w4Residual A B p` at `τ = 0` (within the interval
  `[0, t]`), there exists a constant `C` such that
  `‖w4Residual A B p τ‖ ≤ C · τ⁴` for `τ ∈ [0, t]`.

  The four order-vanishing hypotheses correspond to Suzuki S₄ order conditions
  (palindromic + cubic cancellation). -/
theorem exists_norm_w4Residual_t4_bound_of_zero_taylor
    (A B : 𝔸) (p : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hZero : ∀ k, k ≤ 3 → iteratedDerivWithin k (w4Residual A B p) (Icc 0 t) 0 = 0) :
    ∃ C ≥ 0, ∀ τ ∈ Icc (0 : ℝ) t, ‖w4Residual A B p τ‖ ≤ C * τ ^ 4 := by
  -- w4Residual is ContDiff ℝ ⊤, hence ContDiffOn ℝ 4 on [0, t]
  have hCD : ContDiffOn ℝ 4 (w4Residual A B p) (Icc 0 t) :=
    (contDiff_w4Residual A B p).contDiffOn
  -- Apply Taylor's theorem with n = 3 (so n+1 = 4)
  obtain ⟨C₀, hC₀⟩ := exists_taylor_mean_remainder_bound (n := 3) ht hCD
  -- Taylor polynomial vanishes at every τ
  have hTaylor : ∀ τ, taylorWithinEval (w4Residual A B p) 3 (Icc 0 t) 0 τ = 0 :=
    fun τ => taylorWithin_eq_zero_of_iteratedDerivs_zero hZero
  -- Combine: ‖w4Residual τ‖ = ‖w4Residual τ - 0‖ ≤ C₀ · (τ - 0)^4 = C₀ · τ⁴
  refine ⟨max C₀ 0, le_max_right _ _, ?_⟩
  intro τ hτ
  have hbound := hC₀ τ hτ
  rw [hTaylor τ, sub_zero] at hbound
  simp only [sub_zero] at hbound
  calc ‖w4Residual A B p τ‖
      ≤ C₀ * τ ^ 4 := hbound
    _ ≤ max C₀ 0 * τ ^ 4 := by
        have hτ4 : 0 ≤ τ ^ 4 := by positivity
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) hτ4

/-!
## Order-0 vanishing (trivial consequence of `w4Residual_at_zero`)

The zeroth iterated derivative of `f` is just `f` itself. Hence the order-0
condition reduces immediately to the known fact `w4Residual A B p 0 = 0`.
-/

/-- **Order-0 vanishing**: `iteratedDerivWithin 0 (w4Residual A B p) s 0 = 0`
  for any set `s`. Immediate from `iteratedDerivWithin_zero` and
  `w4Residual_at_zero`. -/
lemma iteratedDerivWithin_w4Residual_order0 (A B : 𝔸) (p : ℝ) (s : Set ℝ) :
    iteratedDerivWithin 0 (w4Residual A B p) s 0 = 0 := by
  rw [iteratedDerivWithin_zero]
  exact w4Residual_at_zero A B p

/-!
## Closing the two outer sorries

The final assembly uses `norm_suzuki4_order5_from_residual_bound` from
`Suzuki4DerivExplicit`, which converts a τ⁴ pointwise bound on
`w4Residual` into a `t⁵/5`-scaled bound on `suzuki4Exp`.
-/

section AntiHermitian

variable [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]

/-- **Phase 5 packaged**: from the four order-vanishing hypotheses, conclude
  the O(t⁵) S₄ bound (`norm_suzuki4_fifth_order` target). -/
theorem norm_suzuki4_order5_of_vanishings (A B : 𝔸)
    (hA : star A = -A) (hB : star B = -B) (p : ℝ)
    {t : ℝ} (ht : 0 ≤ t)
    (hZero : ∀ k, k ≤ 3 → iteratedDerivWithin k (w4Residual A B p) (Icc 0 t) 0 = 0) :
    ∃ C ≥ 0, ‖suzuki4Exp A B p t - exp (t • (A + B))‖ ≤ C / 5 * t ^ 5 := by
  obtain ⟨C, hC_nn, hBound⟩ := exists_norm_w4Residual_t4_bound_of_zero_taylor A B p ht hZero
  refine ⟨C, hC_nn, ?_⟩
  exact norm_suzuki4_order5_from_residual_bound A B hA hB p ht hC_nn hBound

end AntiHermitian

end
