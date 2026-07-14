/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# S₄ Total-Error Convergence: O(1/n⁴)

The Suzuki S₄ analogue of `lie_trotter` (O(1/n)) and `symmetric_lie_trotter`
(O(1/n²)).  Every other integrator in this development has both a *single-step*
error bound and a *total-error* convergence theorem; for S₄ only the step bound
existed.  This file supplies the missing half.

We compound the axiom-free single-step BCH bound

  ‖S₄(τ) - exp(τ(A+B))‖ ≤ C·|τ|⁵            (`exists_norm_s4Func_sub_exp_le_t5`)

into the total-error statement

  ‖S₄(t/n)^n - exp(t(A+B))‖ ≤ C(t)/n⁴       (`suzuki4_total_error_quartic`)

and deduce the fourth-order product formula

  S₄(t/n)^n → exp(t(A+B))                   (`suzuki4_convergence_quartic`).

## Architecture

```
exists_norm_s4Func_sub_exp_le_t5          norm_suzuki4Exp_le
(single-step O(|τ|⁵), axiom-free)         (‖S₄(τ)‖ ≤ exp(|τ|·rate))
             │                                     │
             └──────────────┬──────────────────────┘
                            ▼
            norm_pow_sub_pow_le'  (telescoping, Task A2)
                            ▼
       suzuki4_total_error_quartic  →  suzuki4_convergence_quartic
```

The `n`-step error is `n` copies of an `O(n⁻⁵)` step error, damped by
`max(‖S₄(t/n)‖, ‖exp((t/n)(A+B))‖)^{n-1} ≤ exp(|t|·K)` — a constant.  Hence
`n · O(n⁻⁵) = O(n⁻⁴)`.

## Hypotheses

Only `IsSuzukiCubic p`, i.e. `4p³ + (1-4p)³ = 0` — the defining Suzuki order-4
condition, satisfied by the standard `p = 1/(4 - 4^{1/3})`.  No C*-algebra or
anti-Hermitian structure is required: the theorem holds in any complete normed
algebra with `NormOneClass`.  In particular `#print axioms` on the results here
returns only Lean's three foundational axioms.
-/

import LieTrotter.Suzuki4
import LieTrotter.Suzuki4StrangBlocks
import LieTrotter.Suzuki4BchBound
import LieTrotter.Suzuki4DerivExplicit
import LieTrotter.Telescoping
import LieTrotter.ExpDivPow
import BCH.Suzuki5Quintic
import Mathlib.Order.Filter.AtTopBot.Basic

noncomputable section

open NormedSpace Filter Topology

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-!
## The two S₄ spellings agree

`s4Func` (used by the BCH chain) and `suzuki4Exp` (used by the L1–L3 headline
bounds) are the same 11-factor product, definitionally.
-/

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
lemma s4Func_eq_suzuki4Exp (A B : 𝔸) (p τ : ℝ) :
    s4Func A B p τ = suzuki4Exp A B p τ := by
  unfold s4Func suzuki4Exp
  rfl

/-!
## Norm bound: `‖S₄(τ)‖ ≤ exp(|τ| · rate)`

The 11 exponential factors of S₄ carry coefficients `p/2, p, (1-3p)/2` (on `A`)
and `p, 1-4p` (on `B`).  Summing their magnitudes gives the growth rate below.
We reuse Lean-BCH's `norm_suzuki5Product_sub_one_le`, which already performs the
11-factor peel, and convert `‖S₄ - 1‖ ≤ exp R - 1` into `‖S₄‖ ≤ exp R` using
`NormOneClass`.
-/

/-- The exponential growth rate of the 11-factor S₄ product: the sum of the
magnitudes of its coefficients, weighted by `‖A‖` and `‖B‖`. -/
def s4Rate (A B : 𝔸) (p : ℝ) : ℝ :=
  (3 * |p| + |1 - 3 * p|) * ‖A‖ + (4 * |p| + |1 - 4 * p|) * ‖B‖

omit [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸] in
lemma s4Rate_nonneg (A B : 𝔸) (p : ℝ) : 0 ≤ s4Rate A B p := by
  unfold s4Rate
  positivity

omit [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- Lean-BCH's `suzuki5ArgNormBound` is `|τ|` times our rate. -/
lemma suzuki5ArgNormBound_eq_rate (A B : 𝔸) (p τ : ℝ) :
    BCH.suzuki5ArgNormBound (𝕂 := ℝ) A B p τ = |τ| * s4Rate A B p := by
  unfold BCH.suzuki5ArgNormBound s4Rate
  simp only [Real.norm_eq_abs]

/-- **Growth bound for S₄**: `‖S₄(τ)‖ ≤ exp(|τ| · s4Rate A B p)`. -/
theorem norm_suzuki4Exp_le (A B : 𝔸) (p τ : ℝ) :
    ‖suzuki4Exp A B p τ‖ ≤ Real.exp (|τ| * s4Rate A B p) := by
  have hsub : ‖BCH.suzuki5Product (𝕂 := ℝ) A B p τ - 1‖ ≤
      Real.exp (|τ| * s4Rate A B p) - 1 := by
    refine le_trans (BCH.norm_suzuki5Product_sub_one_le (𝕂 := ℝ) A B p τ) ?_
    have h := Real.exp_le_exp.mpr (BCH.sum_arg_norms_le_bound (𝕂 := ℝ) A B p τ)
    rw [suzuki5ArgNormBound_eq_rate] at h
    linarith
  have heq : suzuki4Exp A B p τ = BCH.suzuki5Product (𝕂 := ℝ) A B p τ := by
    rw [← s4Func_eq_suzuki4Exp]
    exact s4Func_eq_suzuki5Product A B p τ
  rw [heq]
  calc ‖BCH.suzuki5Product (𝕂 := ℝ) A B p τ‖
      = ‖BCH.suzuki5Product (𝕂 := ℝ) A B p τ - 1 + 1‖ := by congr 1; abel
    _ ≤ ‖BCH.suzuki5Product (𝕂 := ℝ) A B p τ - 1‖ + ‖(1 : 𝔸)‖ := norm_add_le _ _
    _ ≤ (Real.exp (|τ| * s4Rate A B p) - 1) + 1 := by rw [norm_one]; linarith
    _ = Real.exp (|τ| * s4Rate A B p) := by ring

/-!
## The exact target: `exp((t/n)•V)^n = exp(t•V)`

The S₄ target exponential is exact under `n`-fold composition — all the error
lives in the step bound.  This is the `t/n` analogue of `exp_div_pow`.
-/

omit [NormOneClass 𝔸] in
private lemma exp_smul_div_pow (V : 𝔸) (t : ℝ) (n : ℕ) (hn : 0 < n) :
    (exp ((t / (n : ℝ)) • V)) ^ n = exp (t • V) := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [← exp_nsmul]
  congr 1
  rw [← Nat.cast_smul_eq_nsmul ℝ n, smul_smul]
  congr 1
  field_simp

/-!
## Total-error bound: O(1/n⁴)
-/

/-- **S₄ total-error convergence rate.**  Under the Suzuki cubic condition
`4p³ + (1-4p)³ = 0`, the `n`-step S₄ product formula approximates `exp(t(A+B))`
to *fourth* order:

  `‖S₄(t/n)^n - exp(t(A+B))‖ ≤ C/n⁴`   for all `n ≥ N`.

`N` is the threshold at which the step size `t/n` enters the BCH regime `|τ| < δ`
of the single-step bound.  This is the S₄ counterpart of `lie_trotter_error_rate`
(O(1/n)) and of the O(1/n²) Strang rate. -/
theorem suzuki4_total_error_quartic (A B : 𝔸) (p : ℝ) (hp : IsSuzukiCubic p) (t : ℝ) :
    ∃ C > 0, ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ‖(suzuki4Exp A B p (t / (n : ℝ))) ^ n - exp (t • (A + B))‖ ≤ C / (n : ℝ) ^ 4 := by
  -- SLICE 1: the axiom-free single-step O(|τ|⁵) BCH bound.
  obtain ⟨δ, hδ_pos, C₀, hC₀_nn, hstep⟩ := exists_norm_s4Func_sub_exp_le_t5 A B p hp
  -- A single rate `K` dominating both `‖S₄(τ)‖` and `‖exp(τ(A+B))‖`.
  set K : ℝ := s4Rate A B p + ‖A‖ + ‖B‖ with hK_def
  have hrate_nn : 0 ≤ s4Rate A B p := s4Rate_nonneg A B p
  have hK_nn : 0 ≤ K := by rw [hK_def]; linarith [norm_nonneg A, norm_nonneg B]
  have hrate_le_K : s4Rate A B p ≤ K := by
    rw [hK_def]; linarith [norm_nonneg A, norm_nonneg B]
  have hAB_le_K : ‖A‖ + ‖B‖ ≤ K := by rw [hK_def]; linarith
  -- The constant.
  set Cbase : ℝ := C₀ * |t| ^ 5 * Real.exp (|t| * K) with hCbase_def
  have hCbase_nn : 0 ≤ Cbase := by
    rw [hCbase_def]
    exact mul_nonneg (mul_nonneg hC₀_nn (by positivity)) (Real.exp_pos _).le
  -- The threshold: `n > |t|/δ` forces the step size into the BCH regime.
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (|t| / δ)
  refine ⟨Cbase + 1, by linarith, N₀ + 1, by omega, ?_⟩
  intro n hn
  have hn_pos : 0 < n := by omega
  have hn_posR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_posR
  have habs_tn : |t / (n : ℝ)| = |t| / (n : ℝ) := by rw [abs_div, Nat.abs_cast]
  -- The step size is inside the BCH regime.
  have hτ_lt : |t / (n : ℝ)| < δ := by
    rw [habs_tn, div_lt_iff₀ hn_posR]
    have hN₀n : (N₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : N₀ ≤ n)
    have h1 : |t| / δ < (n : ℝ) := lt_of_lt_of_le hN₀ hN₀n
    calc |t| = |t| / δ * δ := by field_simp
      _ < (n : ℝ) * δ := mul_lt_mul_of_pos_right h1 hδ_pos
      _ = δ * (n : ℝ) := by ring
  set X : 𝔸 := suzuki4Exp A B p (t / (n : ℝ)) with hX_def
  set Y : 𝔸 := exp ((t / (n : ℝ)) • (A + B)) with hY_def
  -- The target composes exactly: no error from the exponential side.
  have hYpow : Y ^ n = exp (t • (A + B)) := by
    rw [hY_def]; exact exp_smul_div_pow (A + B) t n hn_pos
  rw [← hYpow]
  -- Single-step error at step size `t/n`.
  have hstep_n : ‖X - Y‖ ≤ C₀ * |t / (n : ℝ)| ^ 5 := by
    rw [hX_def, hY_def, ← s4Func_eq_suzuki4Exp]
    exact hstep (t / (n : ℝ)) hτ_lt
  -- Both factors grow at most like `exp(|t/n| · K)`.
  have hX_norm : ‖X‖ ≤ Real.exp (|t / (n : ℝ)| * K) := by
    rw [hX_def]
    refine le_trans (norm_suzuki4Exp_le A B p (t / (n : ℝ))) ?_
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hrate_le_K (abs_nonneg _))
  have hY_norm : ‖Y‖ ≤ Real.exp (|t / (n : ℝ)| * K) := by
    rw [hY_def]
    refine le_trans (norm_exp_le (𝕂 := ℝ) _) (Real.exp_le_exp.mpr ?_)
    calc ‖(t / (n : ℝ)) • (A + B)‖ = |t / (n : ℝ)| * ‖A + B‖ := by
          rw [norm_smul, Real.norm_eq_abs]
      _ ≤ |t / (n : ℝ)| * K :=
          mul_le_mul_of_nonneg_left ((norm_add_le A B).trans hAB_le_K) (abs_nonneg _)
  have hmax : max ‖X‖ ‖Y‖ ≤ Real.exp (|t / (n : ℝ)| * K) := max_le hX_norm hY_norm
  -- Telescoping (Task A2).
  have htel := norm_pow_sub_pow_le' X Y n
  -- Bookkeeping for the final chain.
  have hε_nn : (0 : ℝ) ≤ C₀ * |t / (n : ℝ)| ^ 5 := mul_nonneg hC₀_nn (by positivity)
  have hnε_nn : (0 : ℝ) ≤ (n : ℝ) * (C₀ * |t / (n : ℝ)| ^ 5) :=
    mul_nonneg hn_posR.le hε_nn
  have hbase_one : (1 : ℝ) ≤ Real.exp (|t / (n : ℝ)| * K) := by
    have h0 : (0 : ℝ) ≤ |t / (n : ℝ)| * K := mul_nonneg (abs_nonneg _) hK_nn
    linarith [Real.add_one_le_exp (|t / (n : ℝ)| * K)]
  -- The damping factor is a constant: `exp(|t/n|·K)^(n-1) ≤ exp(|t|·K)`.
  have hexp_pow : (Real.exp (|t / (n : ℝ)| * K)) ^ (n - 1) ≤ Real.exp (|t| * K) := by
    calc (Real.exp (|t / (n : ℝ)| * K)) ^ (n - 1)
        ≤ (Real.exp (|t / (n : ℝ)| * K)) ^ n := pow_le_pow_right₀ hbase_one (by omega)
      _ = Real.exp ((n : ℝ) * (|t / (n : ℝ)| * K)) := by rw [← Real.exp_nat_mul]
      _ = Real.exp (|t| * K) := by rw [habs_tn]; congr 1; field_simp
  -- n copies of an O(n⁻⁵) step error, damped by a constant ⟹ O(n⁻⁴).
  calc ‖X ^ n - Y ^ n‖
      ≤ (n : ℝ) * ‖X - Y‖ * (max ‖X‖ ‖Y‖) ^ (n - 1) := htel
    _ ≤ (n : ℝ) * (C₀ * |t / (n : ℝ)| ^ 5) *
        (Real.exp (|t / (n : ℝ)| * K)) ^ (n - 1) := by gcongr
    _ ≤ (n : ℝ) * (C₀ * |t / (n : ℝ)| ^ 5) * Real.exp (|t| * K) :=
        mul_le_mul_of_nonneg_left hexp_pow hnε_nn
    _ = Cbase / (n : ℝ) ^ 4 := by
        rw [hCbase_def, habs_tn]
        field_simp
    _ ≤ (Cbase + 1) / (n : ℝ) ^ 4 :=
        (div_le_div_iff_of_pos_right (pow_pos hn_posR 4)).mpr
          (le_add_of_nonneg_right zero_le_one)

/-!
## Convergence
-/

/-- **The Fourth-Order Suzuki Product Formula.**

For `A, B` in a complete normed algebra and `p` satisfying the Suzuki cubic
condition `4p³ + (1-4p)³ = 0`,

  `S₄(t/n)^n → exp(t(A+B))`   as `n → ∞`,

at rate `O(1/n⁴)` by `suzuki4_total_error_quartic`.  This completes the
hierarchy `lie_trotter` (O(1/n)) → `symmetric_lie_trotter` (O(1/n²)) →
`suzuki4_convergence_quartic` (O(1/n⁴)). -/
theorem suzuki4_convergence_quartic (A B : 𝔸) (p : ℝ) (hp : IsSuzukiCubic p) (t : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => (suzuki4Exp A B p (t / (n : ℝ))) ^ n)
      atTop (nhds (exp (t • (A + B)))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨C, hC_pos, N, hN_pos, hbound⟩ := suzuki4_total_error_quartic A B p hp t
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (C / ε)
  refine ⟨max N (N₂ + 1), fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hnN₂ : N₂ + 1 ≤ n := le_trans (le_max_right _ _) hn
  have hn_pos : 0 < n := by omega
  have hn_posR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
  have hn_one : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos
  rw [dist_eq_norm]
  calc ‖(suzuki4Exp A B p (t / (n : ℝ))) ^ n - exp (t • (A + B))‖
      ≤ C / (n : ℝ) ^ 4 := hbound n hnN
    _ ≤ C / (n : ℝ) := by
        apply div_le_div_of_nonneg_left hC_pos.le hn_posR
        calc (n : ℝ) = (n : ℝ) ^ 1 := (pow_one _).symm
          _ ≤ (n : ℝ) ^ 4 := pow_le_pow_right₀ hn_one (by omega)
    _ ≤ C / ((N₂ : ℝ) + 1) := by
        apply div_le_div_of_nonneg_left hC_pos.le (by positivity)
        exact_mod_cast hnN₂
    _ < ε := by
        rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (N₂ : ℝ) + 1)]
        have hlt : C / ε < (N₂ : ℝ) + 1 := by linarith
        calc C = C / ε * ε := by field_simp
          _ < ((N₂ : ℝ) + 1) * ε := mul_lt_mul_of_pos_right hlt hε
          _ = ε * ((N₂ : ℝ) + 1) := by ring

/-- **S₄ product formula at unit time**: `S₄(1/n)^n → exp(A+B)` at O(1/n⁴).
The direct S₄ analogue of `lie_trotter`. -/
theorem suzuki4_product_formula (A B : 𝔸) (p : ℝ) (hp : IsSuzukiCubic p) :
    Filter.Tendsto
      (fun n : ℕ => (suzuki4Exp A B p ((n : ℝ)⁻¹)) ^ n)
      atTop (nhds (exp (A + B))) := by
  have h := suzuki4_convergence_quartic A B p hp 1
  simpa only [one_div, one_smul] using h

/-!
## The canonical Suzuki parameter

`p = 1/(4 - 4^{1/3})` is the real root of `4p³ + (1-4p)³ = 0`, so the results
above apply unconditionally to the standard S₄ integrator.
-/

/-- The standard Suzuki parameter satisfies the cubic condition. -/
lemma isSuzukiCubic_suzukiP : IsSuzukiCubic (1 / (4 - (4 : ℝ) ^ ((1 : ℝ) / 3))) :=
  BCH.IsSuzukiCubic_suzukiP

/-- **Fourth-order convergence of the standard Suzuki S₄ integrator.**
No hypotheses beyond the ambient algebra: the cubic condition is discharged by
`BCH.IsSuzukiCubic_suzukiP`. -/
theorem suzuki4_convergence_quartic_suzukiP (A B : 𝔸) (t : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => (suzuki4Exp A B (1 / (4 - (4 : ℝ) ^ ((1 : ℝ) / 3))) (t / (n : ℝ))) ^ n)
      atTop (nhds (exp (t • (A + B)))) :=
  suzuki4_convergence_quartic A B _ isSuzukiCubic_suzukiP t

/-- The O(1/n⁴) rate for the standard Suzuki S₄ integrator. -/
theorem suzuki4_total_error_quartic_suzukiP (A B : 𝔸) (t : ℝ) :
    ∃ C > 0, ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ‖(suzuki4Exp A B (1 / (4 - (4 : ℝ) ^ ((1 : ℝ) / 3))) (t / (n : ℝ))) ^ n -
        exp (t • (A + B))‖ ≤ C / (n : ℝ) ^ 4 :=
  suzuki4_total_error_quartic A B _ isSuzukiCubic_suzukiP t

/-!
## Upgrading `suzuki4Step`: O(1/n²) → O(1/n⁴)

`Suzuki4.lean` builds S₄ as five `strangStep`s, each carrying its own `1/n`, and
bounds the resulting `suzuki4Step` at O(1/n²) (`suzuki4_error_rate_sq`) — the
generic rate available *without* the Suzuki cubic condition.  `suzuki4Exp` builds
the same operator as 11 exponentials in a free step size `τ`.

Bridging the two spellings lets us restate the results above for the *same*
object `suzuki4Step`, making the improvement from O(1/n²) to O(1/n⁴) explicit
rather than a comparison across two definitions.

The four exponential merges at the block junctions are already done by
`suzuki4Exp_eq_strangProduct`, so all that remains is the scalar identity
`strangStep(c, n) = strangBlock(c/n)`.
-/

omit [NormOneClass 𝔸] in
/-- A `strangStep` with built-in `1/n` is a `strangBlock` at step size `c/n`. -/
lemma strangStep_eq_strangBlock (A B : 𝔸) (c : ℝ) (n : ℕ) :
    strangStep ℝ A B c n = strangBlock A B (c * (n : ℝ)⁻¹) := by
  unfold strangStep strangBlock
  simp only [smul_smul]
  rw [show (2 * (n : ℝ))⁻¹ * c = c * (n : ℝ)⁻¹ / 2 from by rw [mul_inv]; ring,
    show ((n : ℝ))⁻¹ * c = c * (n : ℝ)⁻¹ from mul_comm _ _]

/-- **The two S₄ step spellings agree**: the five-`strangStep` product of
`Suzuki4.lean` is the 11-exponential `suzuki4Exp` at step size `1/n`.

Proved by rewriting both sides into five `strangBlock`s: `suzuki4Exp_eq_strangProduct`
performs the four junction merges, and `strangStep_eq_strangBlock` matches the
coefficients. -/
theorem suzuki4Step_eq_suzuki4Exp (A B : 𝔸) (p : ℝ) (n : ℕ) :
    suzuki4Step ℝ A B p n = suzuki4Exp A B p ((n : ℝ)⁻¹) := by
  rw [suzuki4Exp_eq_strangProduct]
  unfold suzuki4Step
  simp only [strangStep_eq_strangBlock]

/-- **`suzuki4Step` is fourth-order.**  The same object that `suzuki4_error_rate_sq`
bounds at O(1/n²) satisfies, under the Suzuki cubic condition,

  `‖suzuki4Step(n)ⁿ - exp(A+B)‖ ≤ C/n⁴`   for `n ≥ N`. -/
theorem suzuki4Step_total_error_quartic (A B : 𝔸) (p : ℝ) (hp : IsSuzukiCubic p) :
    ∃ C > 0, ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ‖(suzuki4Step ℝ A B p n) ^ n - exp (A + B)‖ ≤ C / (n : ℝ) ^ 4 := by
  obtain ⟨C, hC_pos, N, hN_pos, hbound⟩ := suzuki4_total_error_quartic A B p hp 1
  refine ⟨C, hC_pos, N, hN_pos, fun n hn => ?_⟩
  have h := hbound n hn
  rw [one_div, one_smul] at h
  rwa [suzuki4Step_eq_suzuki4Exp]

/-- **`suzuki4Step` converges at fourth order**: the O(1/n⁴) upgrade of
`suzuki4_convergence` (which gives the same limit at O(1/n²)). -/
theorem suzuki4Step_convergence_quartic (A B : 𝔸) (p : ℝ) (hp : IsSuzukiCubic p) :
    Filter.Tendsto
      (fun n : ℕ => (suzuki4Step ℝ A B p n) ^ n)
      atTop (nhds (exp (A + B))) := by
  simpa only [suzuki4Step_eq_suzuki4Exp] using suzuki4_product_formula A B p hp

end
