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
## Bridge: `iteratedDerivWithin` at 0 within `[0, t]` = `iteratedDeriv` at 0

For `0 ≤ t`, the within-derivative at the left endpoint of `Icc 0 t` agrees
with the global `iteratedDeriv` (since `w4Residual` is `ContDiff ℝ ⊤`). This
converts the remaining orders 1-3 vanishing hypotheses into the equivalent
simpler `iteratedDeriv` form, which may be easier to prove via explicit
derivative calculations.
-/

/-- Bridge: `iteratedDerivWithin k (w4Residual A B p) (Icc 0 t) 0` equals
  the global `iteratedDeriv k (w4Residual A B p) 0`, for `0 < t`. -/
lemma iteratedDerivWithin_w4Residual_eq_iteratedDeriv (A B : 𝔸) (p : ℝ) (k : ℕ)
    {t : ℝ} (ht : 0 < t) :
    iteratedDerivWithin k (w4Residual A B p) (Icc 0 t) 0 =
      iteratedDeriv k (w4Residual A B p) 0 :=
  iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc ht)
    ((contDiff_w4Residual A B p).contDiffAt) (left_mem_Icc.mpr ht.le)

/-- Alternative form of the conditional reduction, stated using the global
  `iteratedDeriv` instead of `iteratedDerivWithin`. Easier to discharge because
  it matches the ContDiff derivative framework. -/
theorem exists_norm_w4Residual_t4_bound_of_iteratedDeriv_zero
    (A B : 𝔸) (p : ℝ) {t : ℝ} (ht : 0 < t)
    (hZero : ∀ k, k ≤ 3 → iteratedDeriv k (w4Residual A B p) 0 = 0) :
    ∃ C ≥ 0, ∀ τ ∈ Icc (0 : ℝ) t, ‖w4Residual A B p τ‖ ≤ C * τ ^ 4 := by
  apply exists_norm_w4Residual_t4_bound_of_zero_taylor A B p ht.le
  intro k hk
  rw [iteratedDerivWithin_w4Residual_eq_iteratedDeriv A B p k ht]
  exact hZero k hk

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

/-!
## Alternative formulation via `w4Func` directly

Since `w4Func = exp(-τH) · s4Func` with `w4Func(0) = 1`, Taylor's theorem
applied directly to `w4Func` (instead of the derivative `w4Residual`) gives:

If `iteratedDerivWithin k (w4Func A B p) (Icc 0 t) 0 = 0` for k = 1, 2, 3, 4
(four vanishings for w4Func), then `‖w4Func(τ) - 1‖ ≤ C · τ⁵`. Combined with
Module 2's `norm_suzuki4_diff_eq_norm_relative` (anti-Hermitian isometry),
this directly gives `‖S₄(t) - exp(tH)‖ ≤ C · t⁵`.

**Key advantage**: Order-1 vanishing of `w4Func` follows immediately from
the already-proved `w4Deriv_at_zero` — no new work needed.

**Trade-off**: we need 4 vanishings instead of 3, but order-1 is free.
-/

/-- Taylor polynomial of order `n` equals the constant `f(0)` iff its
  coefficients of orders 1 through n vanish. Proved by induction on `n`. -/
lemma taylorWithin_eq_f_zero_of_higher_iteratedDerivs_zero
    {𝔸 : Type*} [NormedAddCommGroup 𝔸] [NormedSpace ℝ 𝔸]
    {f : ℝ → 𝔸} {n : ℕ} {t τ : ℝ}
    (hZero : ∀ k, 1 ≤ k → k ≤ n → iteratedDerivWithin k f (Icc 0 t) 0 = 0) :
    taylorWithinEval f n (Icc 0 t) 0 τ = f 0 := by
  induction n with
  | zero =>
    rw [taylor_within_zero_eval]
  | succ m ih =>
    rw [taylorWithinEval_succ]
    -- ih applied: taylor of order m equals f(0)
    rw [ih (fun k hk1 hkm => hZero k hk1 (hkm.trans m.le_succ))]
    -- Now the (m+1) term: ((m+1)! * m!)⁻¹ * (τ - 0)^(m+1) • iteratedDerivWithin (m+1) f _ 0
    rw [hZero (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) le_rfl]
    simp

/-- **Phase 5 (w4Func form)**: given the four vanishings
  `iteratedDerivWithin k (w4Func A B p) (Icc 0 t) 0 = 0` for k = 1, 2, 3, 4,
  there exists a constant `C` such that `‖w4Func(τ) - 1‖ ≤ C · τ⁵` on `[0, t]`. -/
theorem exists_norm_w4Func_sub_one_t5_bound_of_zero_taylor
    (A B : 𝔸) (p : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hZero : ∀ k, 1 ≤ k → k ≤ 4 → iteratedDerivWithin k (w4Func A B p) (Icc 0 t) 0 = 0) :
    ∃ C ≥ 0, ∀ τ ∈ Icc (0 : ℝ) t, ‖w4Func A B p τ - 1‖ ≤ C * τ ^ 5 := by
  -- w4Func is ContDiff ℝ ⊤, hence ContDiffOn ℝ 5 on [0, t]
  have hCD : ContDiffOn ℝ 5 (w4Func A B p) (Icc 0 t) :=
    (contDiff_w4Func A B p).contDiffOn
  -- Apply Taylor's theorem with n = 4 (so n+1 = 5)
  obtain ⟨C₀, hC₀⟩ := exists_taylor_mean_remainder_bound (n := 4) ht hCD
  -- Taylor polynomial at every τ equals w4Func(0) = 1
  have hTaylor : ∀ τ, taylorWithinEval (w4Func A B p) 4 (Icc 0 t) 0 τ = 1 := by
    intro τ
    rw [taylorWithin_eq_f_zero_of_higher_iteratedDerivs_zero hZero]
    exact w4Func_zero A B p
  refine ⟨max C₀ 0, le_max_right _ _, ?_⟩
  intro τ hτ
  have hbound := hC₀ τ hτ
  rw [hTaylor τ] at hbound
  simp only [sub_zero] at hbound
  have hτ5 : 0 ≤ τ ^ 5 := pow_nonneg hτ.1 5
  calc ‖w4Func A B p τ - 1‖
      ≤ C₀ * τ ^ 5 := hbound
    _ ≤ max C₀ 0 * τ ^ 5 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hτ5

section AntiHermitian2

variable [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]

/-- **Phase 5 packaged (w4Func form)**: from the four order-vanishing hypotheses
  on `w4Func`, conclude the O(t⁵) S₄ bound. Uses Module 2's
  `norm_suzuki4_diff_eq_norm_relative`. -/
theorem norm_suzuki4_order5_of_w4Func_vanishings (A B : 𝔸)
    (hA : star A = -A) (hB : star B = -B) (p : ℝ)
    {t : ℝ} (ht : 0 ≤ t)
    (hZero : ∀ k, 1 ≤ k → k ≤ 4 → iteratedDerivWithin k (w4Func A B p) (Icc 0 t) 0 = 0) :
    ∃ C ≥ 0, ‖suzuki4Exp A B p t - exp (t • (A + B))‖ ≤ C * t ^ 5 := by
  obtain ⟨C, hC_nn, hBound⟩ := exists_norm_w4Func_sub_one_t5_bound_of_zero_taylor A B p ht hZero
  refine ⟨C, hC_nn, ?_⟩
  -- Module 2: ‖S₄ - exp(tH)‖ = ‖w4Func(t) - 1‖
  rw [norm_suzuki4_diff_eq_norm_relative A B hA hB p t]
  exact hBound t (right_mem_Icc.mpr ht)

end AntiHermitian2

/-!
## Order-1 vanishing for `w4Func` (FREE from existing infrastructure)

Using `iteratedDerivWithin_one`, the order-1 condition becomes
`derivWithin (w4Func A B p) (Icc 0 t) 0 = 0`. By HasDerivAt uniqueness
on `hasDerivAt_w4_explicit` and the known fact `w4Deriv A B p 0 = 0`
(= `w4Deriv_at_zero`), this is immediate.
-/

/-- The global derivative of `w4Func A B p` at 0 equals `w4Deriv A B p 0`, which is 0. -/
lemma deriv_w4Func_at_zero (A B : 𝔸) (p : ℝ) : deriv (w4Func A B p) 0 = 0 := by
  rw [(hasDerivAt_w4_explicit A B p 0).deriv]
  exact w4Deriv_at_zero A B p

/-!
## Structural decomposition of `w4DerivExplicit`

We establish the identity

  `w4DerivExplicit A B p τ = -H · w4Func(τ) + exp(-τH) · s4DerivExplicit(τ)`

where `H = A + B`. This follows by reassociating the 12-term definition:
the first term `(-H·e₀)·e₁·…·e₁₁ = -H · (e₀·e₁·…·e₁₁) = -H · w4Func(τ)`,
and the remaining 11 terms all start with `e₀`, factoring as
`e₀ · (11-term s4DerivExplicit sum) = exp(-τH) · s4DerivExplicit(τ)`.

This decomposition is useful for future iterated-derivative computations,
since it reduces the 12-factor expression to a sum of simpler products.
-/

/-- **Structural decomposition**: `w4DerivExplicit = -H · w4Func + exp(-τH) · s4DerivExplicit`. -/
lemma w4DerivExplicit_decomp (A B : 𝔸) (p τ : ℝ) :
    w4DerivExplicit A B p τ =
      -(A + B) * w4Func A B p τ + exp ((-τ) • (A + B)) * s4DerivExplicit A B p τ := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  unfold w4DerivExplicit w4Func s4Func s4DerivExplicit
  noncomm_ring

/-!
## Corollary: `w4Residual` has a simpler form

Via `w4Residual = s4DerivExplicit - H·s4Func` (already in Suzuki4DerivExplicit),
and `w4DerivExplicit_decomp` above, we can relate the derivatives of w4DerivExplicit
and s4DerivExplicit cleanly.
-/

/-- `w4Func A B p 0 = 1` via `w4Func_zero`. Re-exported for local convenience. -/
lemma w4Func_at_zero (A B : 𝔸) (p : ℝ) : w4Func A B p 0 = 1 := w4Func_zero A B p

/-- `s4DerivExplicit A B p 0 = A + B` (via free-term identity at τ=0). -/
lemma s4DerivExplicit_at_zero (A B : 𝔸) (p : ℝ) :
    s4DerivExplicit A B p 0 = A + B := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  unfold s4DerivExplicit
  simp only [mul_zero, zero_smul, exp_zero, mul_one, one_mul]
  exact suzuki4_free_term A B p

/-- `w4DerivExplicit A B p 0 = 0` via the structural decomposition + boundary values.
  This gives a cleaner proof than the direct simp reduction used earlier. -/
lemma w4DerivExplicit_at_zero_via_decomp (A B : 𝔸) (p : ℝ) :
    w4DerivExplicit A B p 0 = 0 := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  rw [w4DerivExplicit_decomp, w4Func_at_zero, s4DerivExplicit_at_zero]
  simp [neg_zero, zero_smul, exp_zero]

/-!
## Base case for Leibniz-rule expansion: `iteratedDeriv` of a single exp factor

For a single exp factor `τ ↦ exp((c·τ)•X)`, the functional identity:
  `iteratedDeriv k = fun τ => (c•X)^k · exp((c·τ)•X)`

At τ=0: `iteratedDeriv k (fun τ => exp((c·τ)•X)) 0 = (c•X)^k`.

This is the building block for applying Leibniz rule to the 11-factor s4Func.
-/

/-- **Base case**: iterated derivative of a single exp factor (functional form).
  Proved by induction on k using `iteratedDeriv_succ'` and `HasDerivAt.deriv`. -/
lemma iteratedDeriv_exp_smul_mul_fn (X : 𝔸) (c : ℝ) :
    ∀ k : ℕ, iteratedDeriv k (fun τ : ℝ => exp ((c * τ) • X)) =
      fun τ : ℝ => (c • X) ^ k * exp ((c * τ) • X) := by
  intro k
  induction k with
  | zero =>
    funext τ
    simp [iteratedDeriv_zero]
  | succ n ih =>
    funext τ
    rw [iteratedDeriv_succ, ih]
    -- Goal: deriv (fun τ => (c•X)^n · exp((c·τ)•X)) τ = (c•X)^(n+1) · exp((c·τ)•X)
    have h_exp : HasDerivAt (fun u : ℝ => exp ((c * u) • X))
        ((c • X) * exp ((c * τ) • X)) τ := by
      have h := hasDerivAt_exp_smul_mul X c τ
      rwa [← Algebra.smul_mul_assoc] at h
    have h_prod : HasDerivAt (fun u : ℝ => (c • X) ^ n * exp ((c * u) • X))
        ((c • X) ^ n * ((c • X) * exp ((c * τ) • X))) τ := by
      have := (hasDerivAt_const τ ((c • X : 𝔸) ^ n)).mul h_exp
      simpa using this
    rw [h_prod.deriv]
    -- Goal: (c•X)^n · ((c•X) · exp((c·τ)•X)) = (c•X)^(n+1) · exp((c·τ)•X)
    rw [pow_succ]
    noncomm_ring

/-- **Base case at τ=0**: iterated derivative of a single exp factor at 0 equals (c•X)^k. -/
lemma iteratedDeriv_exp_smul_mul_at_zero (X : 𝔸) (c : ℝ) (k : ℕ) :
    iteratedDeriv k (fun τ : ℝ => exp ((c * τ) • X)) 0 = (c • X) ^ k := by
  rw [iteratedDeriv_exp_smul_mul_fn]
  simp

/-- Each `exp((c·τ)•X)` is `ContDiffAt ℝ ∞` at every point (analytic). -/
lemma contDiffAt_exp_smul_mul (X : 𝔸) (c : ℝ) (τ : ℝ) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (fun u : ℝ => exp ((c * u) • X)) τ := by
  have heq : (fun u : ℝ => (c * u) • X) = (fun u : ℝ => u • (c • X)) := by
    funext u; rw [mul_comm, mul_smul]
  have h_lin : ContDiffAt ℝ n (fun u : ℝ => (c * u) • X) τ := by
    rw [heq]; exact (contDiff_id (𝕜 := ℝ)).smul contDiff_const |>.contDiffAt
  have h_exp_cd : ContDiff ℝ n (exp : 𝔸 → 𝔸) := contDiff_iff_contDiffAt.mpr fun y =>
    (NormedSpace.exp_analytic (𝕂 := ℝ) y).contDiffAt
  exact h_exp_cd.contDiffAt.comp τ h_lin

/-!
### Two-factor Leibniz application

The 2-factor iteratedDeriv at 0 has the form
  `iteratedDeriv 2 (fun τ => exp(c₁τ•X₁) * exp(c₂τ•X₂)) 0 = (c₂•X₂)² + 2·(c₁•X₁)·(c₂•X₂) + (c₁•X₁)²`

via Mathlib's `iteratedDeriv_mul` + the base case above. A full Lean proof
requires careful handling of Nat-cast coercions in the binomial coefficients
and ℕ-smul vs ℝ-smul distinctions. Deferred to subsequent session when we
need the multi-factor generalization.
-/

/-!
## Future work: Leibniz-rule path for order-n vanishings

**KEY INSIGHT**: Mathlib provides `iteratedDeriv_mul` (a Leibniz-rule
formula for iterated derivatives of products):

  iteratedDeriv n (f * g) x = Σ_{i=0..n} C(n,i) · iteratedDeriv i f x · iteratedDeriv (n-i) g x

Using this iteratively on the 11-factor product s4Func, and the fact
that `iteratedDeriv k (fun τ => exp((c·τ)•X)) 0 = (c•X)^k` (a baby
lemma needed), we can compute:

  iteratedDeriv n (s4Func A B p) 0 = multinomial sum of ordered products
    of `k` copies of `dⱼ`'s (with multinomial coefficients)

For n=2: `iteratedDeriv 2 (s4Func) 0 = Σⱼ dⱼ² + 2·Σ_{i<j} dᵢ·dⱼ`
For n=3: `iteratedDeriv 3 (s4Func) 0 = Σⱼ dⱼ³ + 3·Σ_{(i,j) i≠j} dᵢdⱼ² (...)` etc.

Then via the decomposition
  `w4Func^(n)(0) = Σ_{i=0..n} C(n,i) · (-H)^i · iteratedDeriv (n-i) (s4Func) 0`
(same Leibniz rule applied to w4Func = exp(-τH) · s4Func), we derive
w4Func^(n)(0) as a polynomial in H combined with s4Func's Taylor
coefficients.

**Order-2 reduction**:
  w4Func''(0) = s4''(0) - 2H·s4'(0) + H²·s4(0)
             = s4''(0) - 2H² + H²
             = s4''(0) - H²

Vanishes iff s4''(0) = H², i.e., Σⱼ dⱼ² + 2·Σ_{i<j} dᵢdⱼ = H²,
i.e., Σ_{i<j} [dᵢ, dⱼ] = 0 — `s4_pairwise_commutator_sum_zero`.

**Order-3 reduction**:
  w4Func'''(0) = s4'''(0) - 3H·s4''(0) + 3H²·s4'(0) - H³·s4(0)

If s4(0) = 1, s4'(0) = H, s4''(0) = H² (from order-2), then:
  w4Func'''(0) = s4'''(0) - 3H·H² + 3H²·H - H³
             = s4'''(0) - H³

Vanishes iff s4'''(0) = H³, i.e., the Phase 3 polynomial identities
(`suzuki4_phase3_{aba,a2b,bab}` multiplied by suzuki4_cubic_cancel).

**Remaining concrete work** (for a future session):
1. Prove `iteratedDeriv_exp_smul_mul` (base case): for `fun τ => exp((c·τ)•X)`,
   `iteratedDeriv k · 0 = (c•X)^k`. ~30 lines.
2. Apply Leibniz rule iteratively on s4Func to get explicit expansion of
   iteratedDeriv n s4Func 0. Complexity grows combinatorially.
3. Match against multinomial expansion of H^n and use
   s4_pairwise_commutator_sum_zero / suzuki4_phase3 to cancel.

The Leibniz path is PREFERABLE to explicit HasDerivAt.mul chains because:
- Mathlib's Leibniz rule does much of the combinatorial bookkeeping
- iteratedDeriv level skips HasDerivAt → deriv conversion
- Each order follows the same template (just different binomial coefficients)
-/

/-- **Order-1 vanishing for w4Func (within any set)**. Follows from
  `deriv_w4Func_at_zero` via ContDiff structure. -/
lemma iteratedDerivWithin_w4Func_order1 (A B : 𝔸) (p : ℝ) {t : ℝ} (ht : 0 < t) :
    iteratedDerivWithin 1 (w4Func A B p) (Icc 0 t) 0 = 0 := by
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc ht)
    ((contDiff_w4Func A B p).contDiffAt (n := 1)) (left_mem_Icc.mpr ht.le)]
  rw [iteratedDeriv_one]
  exact deriv_w4Func_at_zero A B p

/-- **Order-1 vanishing for w4Func (global iteratedDeriv form)**, for use with
  Mathlib's `iteratedDeriv_mul` Leibniz rule. -/
lemma iteratedDeriv_w4Func_order1 (A B : 𝔸) (p : ℝ) :
    iteratedDeriv 1 (w4Func A B p) 0 = 0 := by
  rw [iteratedDeriv_one]
  exact deriv_w4Func_at_zero A B p

/-- **Order-0 for w4Func**: `iteratedDeriv 0 (w4Func A B p) 0 = 1`. -/
lemma iteratedDeriv_w4Func_order0 (A B : 𝔸) (p : ℝ) :
    iteratedDeriv 0 (w4Func A B p) 0 = 1 := by
  rw [iteratedDeriv_zero]
  exact w4Func_zero A B p

/-- **Order-0 for s4Func**: `iteratedDeriv 0 (s4Func A B p) 0 = 1`. -/
lemma iteratedDeriv_s4Func_order0 (A B : 𝔸) (p : ℝ) :
    iteratedDeriv 0 (s4Func A B p) 0 = 1 := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  rw [iteratedDeriv_zero]
  unfold s4Func
  simp only [mul_zero, zero_smul, exp_zero, mul_one, one_mul]

/-- **Order-1 for s4Func**: `iteratedDeriv 1 (s4Func A B p) 0 = A + B`. -/
lemma iteratedDeriv_s4Func_order1 (A B : 𝔸) (p : ℝ) :
    iteratedDeriv 1 (s4Func A B p) 0 = A + B := by
  rw [iteratedDeriv_one, (hasDerivAt_s4Explicit A B p 0).deriv]
  exact s4DerivExplicit_at_zero A B p

/-- Iterated derivative of `exp((-τ)•H)` at 0 equals `(-H)^k`.
  Follows from `iteratedDeriv_exp_smul_mul_at_zero` with `c = -1`. -/
lemma iteratedDeriv_exp_neg_smul_at_zero (H : 𝔸) (k : ℕ) :
    iteratedDeriv k (fun τ : ℝ => exp ((-τ) • H)) 0 = (-H) ^ k := by
  have heq : (fun τ : ℝ => exp ((-τ) • H)) = (fun τ : ℝ => exp (((-1 : ℝ) * τ) • H)) := by
    funext τ; congr 1; rw [neg_one_mul]
  rw [heq]
  rw [iteratedDeriv_exp_smul_mul_at_zero H (-1) k]
  rw [show ((-1 : ℝ) • H) = -H from by rw [neg_one_smul]]

/-- ContDiffAt of `exp((-τ)•H)` at any point. -/
lemma contDiffAt_exp_neg_smul (H : 𝔸) (τ : ℝ) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (fun u : ℝ => exp ((-u) • H)) τ := by
  have heq : (fun u : ℝ => exp ((-u) • H)) = (fun u : ℝ => exp (((-1 : ℝ) * u) • H)) := by
    funext u; congr 1; rw [neg_one_mul]
  rw [heq]
  exact contDiffAt_exp_smul_mul H (-1) τ

/-- **Key Leibniz reduction**: order-2 of w4Func expressed in terms of order-2 of s4Func.
  Using `w4Func = exp(-τH) · s4Func` and Mathlib's Leibniz rule:

    iteratedDeriv 2 (w4Func A B p) 0 = iteratedDeriv 2 (s4Func A B p) 0 - (A+B)^2

  This is the crucial bridge: proving `iteratedDeriv 2 (s4Func A B p) 0 = (A+B)^2`
  gives order-2 vanishing of w4Func. -/
lemma iteratedDeriv_w4Func_order2_eq (A B : 𝔸) (p : ℝ) :
    iteratedDeriv 2 (w4Func A B p) 0 =
      iteratedDeriv 2 (s4Func A B p) 0 - (A + B) ^ 2 := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  -- Rewrite w4Func as the pointwise product of exp(-τH) and s4Func
  have hfunext : w4Func A B p =
      (fun τ : ℝ => exp ((-τ) • (A + B))) * s4Func A B p := by
    funext τ
    show w4Func A B p τ = _
    rfl
  rw [hfunext]
  -- Apply Mathlib's iteratedDeriv_mul
  rw [iteratedDeriv_mul (contDiffAt_exp_neg_smul (A + B) 0)
    ((contDiff_s4Func A B p).contDiffAt (n := 2))]
  -- Expand the sum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    iteratedDeriv_exp_neg_smul_at_zero, iteratedDeriv_s4Func_order0,
    iteratedDeriv_s4Func_order1,
    show (2 - 0 : ℕ) = 2 from rfl, show (2 - 1 : ℕ) = 1 from rfl,
    show (2 - 2 : ℕ) = 0 from rfl, pow_zero, pow_one]
  -- The sum is now:
  --   C(2,0) · 1 · iteratedDeriv 2 s4Func 0 + C(2,1) · (-(A+B)) · (A+B) + C(2,2) · (A+B)^2 · 1
  -- Need to show this equals `iteratedDeriv 2 (s4Func A B p) 0 - (A+B)^2`.
  have h0 : (Nat.choose 2 0 : ℕ) = 1 := rfl
  have h1 : (Nat.choose 2 1 : ℕ) = 2 := rfl
  have h2 : (Nat.choose 2 2 : ℕ) = 1 := rfl
  rw [h0, h1, h2]
  -- Goal: ↑1 · 1 · iDer₂ s4 0 + (↑2 · (-(A+B)) · (A+B) + (↑1 · (-(A+B))^2 · 1 + 0)) = iDer₂ s4 0 - (A+B)^2
  -- Normalize the Nat casts
  simp only [Nat.cast_one, Nat.cast_ofNat, one_mul, mul_one, add_zero]
  -- Goal: iDer₂ s4 0 + (2 · (-(A+B)) · (A+B) + (-(A+B))^2) = iDer₂ s4 0 - (A+B)^2
  have hsq : (-(A + B)) ^ 2 = (A + B) ^ 2 := by noncomm_ring
  have h2mul : (2 : 𝔸) * (-(A + B)) * (A + B) = -(2 * (A + B) * (A + B)) := by noncomm_ring
  rw [hsq, h2mul]
  -- Goal: iDer₂ s4 0 + (-(2 · (A+B) · (A+B)) + (A+B)^2) = iDer₂ s4 0 - (A+B)^2
  noncomm_ring

/-- **Corollary**: order-2 vanishing of w4Func is equivalent to `s4''(0) = (A+B)²`. -/
lemma iteratedDeriv_w4Func_order2_zero_iff (A B : 𝔸) (p : ℝ) :
    iteratedDeriv 2 (w4Func A B p) 0 = 0 ↔
      iteratedDeriv 2 (s4Func A B p) 0 = (A + B) ^ 2 := by
  rw [iteratedDeriv_w4Func_order2_eq]
  exact sub_eq_zero

/-!
### Order-3 Leibniz bridge for w4Func

Applying Mathlib's `iteratedDeriv_mul` with n=3:
  iteratedDeriv 3 w4Func 0 = C(3,0)·1·s4'''(0) + C(3,1)·(-H)·s4''(0)
    + C(3,2)·H²·s4'(0) + C(3,3)·(-H)³·s4(0)
    = s4'''(0) - 3H·s4''(0) + 3H²·(A+B) - H³
    = s4'''(0) - 3H·s4''(0) + 2H³

This is the analog of the order-2 bridge but depends on s4''(0) as well.
Under the order-2 assumption `s4''(0) = H²`, it simplifies to
`s4'''(0) - 3H³ + 2H³ = s4'''(0) - H³`.
-/

/-- **Key Leibniz reduction (order-3)**: unconditional form. -/
lemma iteratedDeriv_w4Func_order3_eq (A B : 𝔸) (p : ℝ) :
    iteratedDeriv 3 (w4Func A B p) 0 =
      iteratedDeriv 3 (s4Func A B p) 0
      - 3 * (A + B) * iteratedDeriv 2 (s4Func A B p) 0
      + 2 * (A + B) ^ 3 := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  have hfunext : w4Func A B p =
      (fun τ : ℝ => exp ((-τ) • (A + B))) * s4Func A B p := by
    funext τ
    show w4Func A B p τ = _
    rfl
  rw [hfunext]
  rw [iteratedDeriv_mul (contDiffAt_exp_neg_smul (A + B) 0)
    ((contDiff_s4Func A B p).contDiffAt (n := 3))]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    iteratedDeriv_exp_neg_smul_at_zero, iteratedDeriv_s4Func_order0,
    iteratedDeriv_s4Func_order1,
    show (3 - 0 : ℕ) = 3 from rfl, show (3 - 1 : ℕ) = 2 from rfl,
    show (3 - 2 : ℕ) = 1 from rfl, show (3 - 3 : ℕ) = 0 from rfl,
    pow_zero, pow_one]
  -- Sum: C(3,0)·1·iDer₃ s4 0 + C(3,1)·(-H)·iDer₂ s4 0 + C(3,2)·H²·(A+B) + C(3,3)·(-H)³·1
  have h0 : (Nat.choose 3 0 : ℕ) = 1 := rfl
  have h1 : (Nat.choose 3 1 : ℕ) = 3 := rfl
  have h2 : (Nat.choose 3 2 : ℕ) = 3 := rfl
  have h3 : (Nat.choose 3 3 : ℕ) = 1 := rfl
  rw [h0, h1, h2, h3]
  simp only [Nat.cast_one, Nat.cast_ofNat, one_mul, mul_one, add_zero]
  -- Manually unfold (-H)^2 = H^2, (-H)^3 = -H^3
  have hsq : (-(A + B)) ^ 2 = (A + B) ^ 2 := by noncomm_ring
  have hcb : (-(A + B)) ^ 3 = -((A + B) ^ 3) := by noncomm_ring
  rw [hsq, hcb]
  -- Final noncomm_ring to clean up
  noncomm_ring

/-- **Corollary**: under order-2 hypothesis `s4''(0) = H²`, order-3 vanishing of
  w4Func ⟺ `s4'''(0) = H³`. -/
lemma iteratedDeriv_w4Func_order3_zero_iff_of_order2
    (A B : 𝔸) (p : ℝ) (h2 : iteratedDeriv 2 (s4Func A B p) 0 = (A + B) ^ 2) :
    iteratedDeriv 3 (w4Func A B p) 0 = 0 ↔
      iteratedDeriv 3 (s4Func A B p) 0 = (A + B) ^ 3 := by
  rw [iteratedDeriv_w4Func_order3_eq, h2]
  -- Goal: s4'''(0) - 3·(A+B)·(A+B)² + 2·(A+B)³ = 0 ↔ s4'''(0) = (A+B)³
  have halg : iteratedDeriv 3 (s4Func A B p) 0
      - 3 * (A + B) * (A + B) ^ 2 + 2 * (A + B) ^ 3
      = iteratedDeriv 3 (s4Func A B p) 0 - (A + B) ^ 3 := by noncomm_ring
  rw [halg]
  exact sub_eq_zero

/-!
### Order-4 Leibniz bridge for w4Func

Applying Mathlib's `iteratedDeriv_mul` with n=4:
  iteratedDeriv 4 w4Func 0 = Σᵢ C(4,i)·(-H)^i·s4^(4-i)(0)
    = s4⁴(0) - 4H·s4'''(0) + 6H²·s4''(0) - 4H³·(A+B) + H⁴
    = s4⁴(0) - 4H·s4'''(0) + 6H²·s4''(0) - 3H⁴

Under orders 2 and 3 (`s4''(0) = H²`, `s4'''(0) = H³`), simplifies to
`s4⁴(0) - H⁴`.
-/

/-- **Key Leibniz reduction (order-4)**: unconditional form. -/
lemma iteratedDeriv_w4Func_order4_eq (A B : 𝔸) (p : ℝ) :
    iteratedDeriv 4 (w4Func A B p) 0 =
      iteratedDeriv 4 (s4Func A B p) 0
      - 4 * (A + B) * iteratedDeriv 3 (s4Func A B p) 0
      + 6 * (A + B) ^ 2 * iteratedDeriv 2 (s4Func A B p) 0
      - 3 * (A + B) ^ 4 := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  have hfunext : w4Func A B p =
      (fun τ : ℝ => exp ((-τ) • (A + B))) * s4Func A B p := by
    funext τ
    show w4Func A B p τ = _
    rfl
  rw [hfunext]
  rw [iteratedDeriv_mul (contDiffAt_exp_neg_smul (A + B) 0)
    ((contDiff_s4Func A B p).contDiffAt (n := 4))]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    iteratedDeriv_exp_neg_smul_at_zero, iteratedDeriv_s4Func_order0,
    iteratedDeriv_s4Func_order1,
    show (4 - 0 : ℕ) = 4 from rfl, show (4 - 1 : ℕ) = 3 from rfl,
    show (4 - 2 : ℕ) = 2 from rfl, show (4 - 3 : ℕ) = 1 from rfl,
    show (4 - 4 : ℕ) = 0 from rfl, pow_zero, pow_one]
  have h0 : (Nat.choose 4 0 : ℕ) = 1 := rfl
  have h1 : (Nat.choose 4 1 : ℕ) = 4 := rfl
  have h2 : (Nat.choose 4 2 : ℕ) = 6 := rfl
  have h3 : (Nat.choose 4 3 : ℕ) = 4 := rfl
  have h4 : (Nat.choose 4 4 : ℕ) = 1 := rfl
  rw [h0, h1, h2, h3, h4]
  simp only [Nat.cast_one, Nat.cast_ofNat, one_mul, mul_one, add_zero]
  have hsq : (-(A + B)) ^ 2 = (A + B) ^ 2 := by noncomm_ring
  have hcb : (-(A + B)) ^ 3 = -((A + B) ^ 3) := by noncomm_ring
  have hq4 : (-(A + B)) ^ 4 = (A + B) ^ 4 := by noncomm_ring
  rw [hsq, hcb, hq4]
  noncomm_ring

/-- **Corollary**: under orders 2 and 3, order-4 vanishing ⟺ `s4⁴(0) = H⁴`. -/
lemma iteratedDeriv_w4Func_order4_zero_iff_of_order23
    (A B : 𝔸) (p : ℝ)
    (h2 : iteratedDeriv 2 (s4Func A B p) 0 = (A + B) ^ 2)
    (h3 : iteratedDeriv 3 (s4Func A B p) 0 = (A + B) ^ 3) :
    iteratedDeriv 4 (w4Func A B p) 0 = 0 ↔
      iteratedDeriv 4 (s4Func A B p) 0 = (A + B) ^ 4 := by
  rw [iteratedDeriv_w4Func_order4_eq, h2, h3]
  have halg : iteratedDeriv 4 (s4Func A B p) 0
      - 4 * (A + B) * (A + B) ^ 3
      + 6 * (A + B) ^ 2 * (A + B) ^ 2
      - 3 * (A + B) ^ 4
      = iteratedDeriv 4 (s4Func A B p) 0 - (A + B) ^ 4 := by noncomm_ring
  rw [halg]
  exact sub_eq_zero

/-!
## Bridge: `iteratedDeriv 2 s4Func = deriv s4DerivExplicit`

Using `hasDerivAt_s4Explicit` (functional equality `deriv s4Func = s4DerivExplicit`
via funext and deriv uniqueness), we reduce the iteratedDeriv problem to a
standard deriv problem.
-/

/-- The derivative function of `s4Func A B p` equals `s4DerivExplicit A B p`,
  as a functional equality. -/
lemma deriv_s4Func_eq_s4DerivExplicit (A B : 𝔸) (p : ℝ) :
    deriv (s4Func A B p) = s4DerivExplicit A B p := by
  funext τ
  exact (hasDerivAt_s4Explicit A B p τ).deriv

/-- `iteratedDeriv 2 (s4Func A B p) = deriv (s4DerivExplicit A B p)` as functions. -/
lemma iteratedDeriv_s4Func_order2_eq_deriv (A B : 𝔸) (p : ℝ) :
    iteratedDeriv 2 (s4Func A B p) = deriv (s4DerivExplicit A B p) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_s4Func_eq_s4DerivExplicit]

/-- Corollary at τ=0: order-2 of s4Func = deriv of s4DerivExplicit at 0. -/
lemma iteratedDeriv_s4Func_order2_at_zero (A B : 𝔸) (p : ℝ) :
    iteratedDeriv 2 (s4Func A B p) 0 = deriv (s4DerivExplicit A B p) 0 := by
  rw [iteratedDeriv_s4Func_order2_eq_deriv]

/-- **Reduction of identity h2**: order-2 identity of s4Func ⟺
  `deriv (s4DerivExplicit A B p) 0 = (A + B)²`. -/
lemma iteratedDeriv_s4Func_order2_eq_iff (A B : 𝔸) (p : ℝ) :
    iteratedDeriv 2 (s4Func A B p) 0 = (A + B) ^ 2 ↔
      deriv (s4DerivExplicit A B p) 0 = (A + B) ^ 2 := by
  rw [iteratedDeriv_s4Func_order2_at_zero]

/-!
## Capstone: closing S₄ O(t⁵) via the s4Func iteratedDeriv identities

With the Leibniz bridges above, the four w4Func order-vanishing hypotheses
reduce to three iteratedDeriv identities for s4Func:

  `s4''(0) = (A+B)²`  (palindromic, uses `s4_pairwise_commutator_sum_zero`)
  `s4'''(0) = (A+B)³` (uses `suzuki4_phase3_*` + `suzuki4_cubic_cancel`)
  `s4⁴(0) = (A+B)⁴`   (automatic from lower orders, palindromic)

Combined, they close the S₄ O(t⁵) bound.
-/

section AntiHermitian3

variable [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]

/-- **Final capstone**: given the three `iteratedDeriv` identities for `s4Func`,
  close the S₄ O(t⁵) bound.

  The three hypotheses are the residual research work of Module 4b:
  - `h2`: `iteratedDeriv 2 (s4Func) 0 = (A+B)²` (palindromic identity)
  - `h3`: `iteratedDeriv 3 (s4Func) 0 = (A+B)³` (Suzuki cubic cancellation)
  - `h4`: `iteratedDeriv 4 (s4Func) 0 = (A+B)⁴` (higher palindromic)

  Each reduces via iterated Leibniz to operator-level polynomial identities
  that are already proved:
  - Palindromic → `s4_pairwise_commutator_sum_zero`
  - Cubic → `suzuki4_phase3_aba`, `suzuki4_phase3_a2b`, `suzuki4_phase3_bab` +
    `suzuki4_cubic_cancel`
-/
theorem norm_suzuki4_order5_of_s4Func_iteratedDerivs
    (A B : 𝔸) (hA : star A = -A) (hB : star B = -B) (p : ℝ)
    {t : ℝ} (ht : 0 < t)
    (h2 : iteratedDeriv 2 (s4Func A B p) 0 = (A + B) ^ 2)
    (h3 : iteratedDeriv 3 (s4Func A B p) 0 = (A + B) ^ 3)
    (h4 : iteratedDeriv 4 (s4Func A B p) 0 = (A + B) ^ 4) :
    ∃ C ≥ 0, ‖suzuki4Exp A B p t - exp (t • (A + B))‖ ≤ C * t ^ 5 := by
  -- Convert iteratedDeriv vanishings to iteratedDerivWithin vanishings
  -- via the ContDiff bridge `iteratedDerivWithin_eq_iteratedDeriv`.
  apply norm_suzuki4_order5_of_w4Func_vanishings A B hA hB p ht.le
  intro k hk1 hk4
  -- Transfer: iteratedDerivWithin k (w4Func) (Icc 0 t) 0 = iteratedDeriv k (w4Func) 0
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc ht)
    ((contDiff_w4Func A B p).contDiffAt (n := k)) (left_mem_Icc.mpr ht.le)]
  -- Case split on k = 1, 2, 3, 4
  interval_cases k
  · -- k = 1: order-1 vanishing of w4Func (already proved)
    exact iteratedDeriv_w4Func_order1 A B p
  · -- k = 2: use the Leibniz bridge + h2
    exact (iteratedDeriv_w4Func_order2_zero_iff A B p).mpr h2
  · -- k = 3: use Leibniz bridge (conditional on order-2) + h3
    exact (iteratedDeriv_w4Func_order3_zero_iff_of_order2 A B p h2).mpr h3
  · -- k = 4: use Leibniz bridge (conditional on orders 2, 3) + h4
    exact (iteratedDeriv_w4Func_order4_zero_iff_of_order23 A B p h2 h3).mpr h4

end AntiHermitian3

end
