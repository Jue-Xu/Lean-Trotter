/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Track B: Exponential Remainder Bounds

Bounds on the exponential function in normed algebras:
  B1. ‖exp(a)‖ ≤ exp(‖a‖)
  B2. ‖exp(a) - 1‖ ≤ exp(‖a‖) - 1
  B3. exp(x) - 1 - x ≤ x²/2 · exp(x)  for x ≥ 0  (real)
  B4. ‖exp(a) - 1 - a‖ ≤ ‖a‖²/2 · exp(‖a‖)
-/

import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section

open NormedSpace
open scoped BigOperators

variable {𝕂 : Type*} [RCLike 𝕂]
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

/-!
## Auxiliary lemmas for the exponential power series
-/

/-- Each term of `expSeries` applied to constant `a` equals `(n!)⁻¹ • a^n`. -/
protected lemma expSeries_apply_eq (a : 𝔸) (n : ℕ) :
    (expSeries 𝕂 𝔸 n) (fun _ => a) = (n ! : 𝕂)⁻¹ • a ^ n := by
  simp only [expSeries, ContinuousMultilinearMap.smul_apply,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, Fin.prod_const]

/-- The exponential as a tsum of `(n!)⁻¹ • a^n`. -/
lemma exp_tsum_form (a : 𝔸) :
    exp 𝕂 a = ∑' n, ((n ! : 𝕂)⁻¹ • a ^ n : 𝔸) := by
  show (expSeries 𝕂 𝔸).sum a = _
  simp only [FormalMultilinearSeries.sum, expSeries_apply_eq]

/-- Summability of the exponential series terms `(n!)⁻¹ • a^n`. -/
lemma exp_summable (a : 𝔸) :
    Summable fun n => ((n ! : 𝕂)⁻¹ • a ^ n : 𝔸) := by
  have h := expSeries_summable (𝕂 := 𝕂) (𝔸 := 𝔸) a
  simp only [show (fun n => (expSeries 𝕂 𝔸 n) fun _ => a) =
    (fun n => ((n ! : 𝕂)⁻¹ • a ^ n : 𝔸)) from by ext n; exact expSeries_apply_eq a n] at h
  exact h

/-- The norm of each term `(n!)⁻¹ • a^n` is bounded by `‖a‖^n / n!`. -/
lemma norm_exp_term_le (a : 𝔸) (n : ℕ) :
    ‖((n ! : 𝕂)⁻¹ • a ^ n : 𝔸)‖ ≤ ‖a‖ ^ n / (n ! : ℝ) := by
  rw [norm_smul, norm_inv, RCLike.norm_natCast, div_eq_inv_mul]
  gcongr
  exact norm_pow_le a n

/-- Summability of x^n / n! for real x. -/
lemma real_exp_summable (x : ℝ) :
    Summable fun n => x ^ n / (n ! : ℝ) :=
  Real.summable_pow_div_factorial x

/-- Real exp as a tsum. -/
lemma real_exp_eq_tsum (x : ℝ) :
    Real.exp x = ∑' n, x ^ n / (n ! : ℝ) :=
  (Real.hasSum_exp x).tsum_eq.symm

/-!
## B1: Norm bound on the exponential

`‖exp(a)‖ ≤ exp(‖a‖)` for any element in a complete normed algebra.
-/

/-- `‖exp(a)‖ ≤ exp(‖a‖)` for any element in a complete normed algebra. -/
lemma norm_exp_le (a : 𝔸) : ‖exp 𝕂 a‖ ≤ Real.exp ‖a‖ := by
  rw [exp_tsum_form (𝕂 := 𝕂), real_exp_eq_tsum]
  have hnsumm : Summable fun n => ‖((n ! : 𝕂)⁻¹ • a ^ n : 𝔸)‖ :=
    summable_of_nonneg_of_le (fun _ => norm_nonneg _) (norm_exp_term_le a) (real_exp_summable ‖a‖)
  calc ‖∑' n, ((n ! : 𝕂)⁻¹ • a ^ n : 𝔸)‖
      ≤ ∑' n, ‖((n ! : 𝕂)⁻¹ • a ^ n : 𝔸)‖ :=
        norm_tsum_le_tsum_norm hnsumm
    _ ≤ ∑' n, ‖a‖ ^ n / (n ! : ℝ) :=
        tsum_le_tsum (norm_exp_term_le a) hnsumm (real_exp_summable ‖a‖)

/-!
## B2: First-order remainder

`‖exp(a) - 1‖ ≤ exp(‖a‖) - 1` from the power series minus the constant term.
-/

/-- `‖exp(a) - 1‖ ≤ exp(‖a‖) - 1`. -/
lemma norm_exp_sub_one_le (a : 𝔸) :
    ‖exp 𝕂 a - 1‖ ≤ Real.exp ‖a‖ - 1 := by
  have hsumm := exp_summable (𝕂 := 𝕂) a
  have hsub : exp 𝕂 a - 1 = ∑' n, (((↑(n + 1)! : 𝕂)⁻¹ • a ^ (n + 1)) : 𝔸) := by
    rw [exp_tsum_form (𝕂 := 𝕂), tsum_eq_zero_add hsumm]
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
    abel
  rw [hsub]
  have hsumm' : Summable fun n => (((↑(n + 1)! : 𝕂)⁻¹ • a ^ (n + 1)) : 𝔸) :=
    hsumm.comp_injective (fun _ _ h => by omega)
  have hrsumm := real_exp_summable ‖a‖
  have hrsumm1 : Summable fun n => ‖a‖ ^ (n + 1) / ((n + 1)! : ℝ) :=
    hrsumm.comp_injective (fun _ _ h => by omega)
  have hnsumm' : Summable fun n => ‖(((↑(n + 1)! : 𝕂)⁻¹ • a ^ (n + 1)) : 𝔸)‖ :=
    summable_of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => norm_exp_term_le a (n + 1)) hrsumm1
  calc ‖∑' n, (((↑(n + 1)! : 𝕂)⁻¹ • a ^ (n + 1)) : 𝔸)‖
      ≤ ∑' n, ‖(((↑(n + 1)! : 𝕂)⁻¹ • a ^ (n + 1)) : 𝔸)‖ :=
        norm_tsum_le_tsum_norm hnsumm'
    _ ≤ ∑' n, ‖a‖ ^ (n + 1) / ((n + 1)! : ℝ) :=
        tsum_le_tsum (fun n => norm_exp_term_le a (n + 1)) hnsumm' hrsumm1
    _ = Real.exp ‖a‖ - 1 := by
        rw [real_exp_eq_tsum, tsum_eq_zero_add hrsumm]
        simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
        ring

/-!
## B3: Real exponential remainder bound

For `x ≥ 0`: `exp(x) - 1 - x ≤ x²/2 · exp(x)`.

Proof: `exp(x) - 1 - x = ∑_{k≥2} xᵏ/k!`. For `k ≥ 2`,
`k! ≥ 2·(k-2)!`, so `xᵏ/k! ≤ x²/2 · x^{k-2}/(k-2)!`.
Summing: `≤ x²/2 · exp(x)`.
-/

/-- Auxiliary: `2 * n! ≤ (n + 2)!`. -/
private lemma two_mul_factorial_le (n : ℕ) : 2 * n ! ≤ (n + 2)! := by
  calc 2 * n ! ≤ (n + 1) * n ! := by omega
    _ = (n + 1)! := (Nat.factorial_succ n).symm
    _ ≤ (n + 2) * (n + 1)! := Nat.le_mul_of_pos_left _ (by omega)
    _ = (n + 2)! := (Nat.factorial_succ (n + 1)).symm

/-- For `x ≥ 0`, `exp(x) - 1 - x ≤ x²/2 · exp(x)`. -/
lemma exp_sub_one_sub_bound_real (x : ℝ) (hx : 0 ≤ x) :
    Real.exp x - 1 - x ≤ x ^ 2 / 2 * Real.exp x := by
  have hrsumm := real_exp_summable x
  have hrsumm1 : Summable fun n => x ^ (n + 1) / ((n + 1)! : ℝ) :=
    hrsumm.comp_injective (fun _ _ h => by omega)
  have hrsumm2 : Summable fun n => x ^ (n + 2) / ((n + 2)! : ℝ) :=
    hrsumm.comp_injective (fun _ _ h => by omega)
  have hrem : Real.exp x - 1 - x = ∑' n, x ^ (n + 2) / ((n + 2)! : ℝ) := by
    rw [real_exp_eq_tsum, tsum_eq_zero_add hrsumm]
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    rw [tsum_eq_zero_add hrsumm1]
    simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one]
    ring
  rw [hrem]
  have hterm : ∀ n, x ^ (n + 2) / ((n + 2)! : ℝ) ≤
      x ^ 2 / 2 * (x ^ n / (n ! : ℝ)) := by
    intro n
    have hrhs : x ^ 2 / 2 * (x ^ n / (n ! : ℝ)) =
        x ^ (n + 2) / (2 * (n ! : ℝ)) := by
      rw [show x ^ (n + 2) = x ^ 2 * x ^ n from by rw [pow_add]]; ring
    rw [hrhs]
    have h2nfact_pos : (0 : ℝ) < 2 * ↑n ! := by positivity
    have hxpow_nonneg : (0 : ℝ) ≤ x ^ (n + 2) := pow_nonneg hx _
    have hle : (2 : ℝ) * ↑n ! ≤ ↑(n + 2)! := by exact_mod_cast two_mul_factorial_le n
    exact div_le_div_of_le_left hxpow_nonneg h2nfact_pos hle
  calc ∑' n, x ^ (n + 2) / ((n + 2)! : ℝ)
      ≤ ∑' n, (x ^ 2 / 2 * (x ^ n / (n ! : ℝ))) :=
        have hsummg : Summable fun n => x ^ 2 / 2 * (x ^ n / (n ! : ℝ)) := by
          have := hrsumm.hasSum.mul_left (x ^ 2 / 2)
          exact this.summable
        tsum_le_tsum hterm hrsumm2 hsummg
    _ = x ^ 2 / 2 * ∑' n, x ^ n / (n ! : ℝ) :=
        tsum_mul_left _ _
    _ = x ^ 2 / 2 * Real.exp x := by rw [← real_exp_eq_tsum]

/-!
## B4: Second-order remainder in normed algebra

`‖exp(a) - 1 - a‖ ≤ ‖a‖²/2 · exp(‖a‖)`.

Proof: write `exp(a) - 1 - a = ∑_{k≥2} aᵏ/k!`, take norms,
and reduce to the real bound B3 applied to `‖a‖`.
-/

/-- `‖exp(a) - 1 - a‖ ≤ ‖a‖²/2 · exp(‖a‖)`. -/
lemma norm_exp_sub_one_sub_le (a : 𝔸) :
    ‖exp 𝕂 a - 1 - a‖ ≤ ‖a‖ ^ 2 / 2 * Real.exp ‖a‖ := by
  have hsumm := exp_summable (𝕂 := 𝕂) a
  have hsumm1 : Summable fun n => (((↑(n + 1)! : 𝕂)⁻¹ • a ^ (n + 1)) : 𝔸) :=
    hsumm.comp_injective (fun _ _ h => by omega)
  have hsumm2 : Summable fun n => (((↑(n + 2)! : 𝕂)⁻¹ • a ^ (n + 2)) : 𝔸) :=
    hsumm.comp_injective (fun _ _ h => by omega)
  have hrem : exp 𝕂 a - 1 - a =
      ∑' n, (((↑(n + 2)! : 𝕂)⁻¹ • a ^ (n + 2)) : 𝔸) := by
    rw [exp_tsum_form (𝕂 := 𝕂), tsum_eq_zero_add hsumm]
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
    rw [tsum_eq_zero_add hsumm1]
    simp only [pow_one, Nat.factorial_one, Nat.cast_one, inv_one, one_smul]
    abel
  rw [hrem]
  have hrsumm := real_exp_summable ‖a‖
  have hrsumm1r : Summable fun n => ‖a‖ ^ (n + 1) / ((n + 1)! : ℝ) :=
    hrsumm.comp_injective (fun _ _ h => by omega)
  have hrsumm2r : Summable fun n => ‖a‖ ^ (n + 2) / ((n + 2)! : ℝ) :=
    hrsumm.comp_injective (fun _ _ h => by omega)
  have hnsumm2 : Summable fun n => ‖(((↑(n + 2)! : 𝕂)⁻¹ • a ^ (n + 2)) : 𝔸)‖ :=
    summable_of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => norm_exp_term_le a (n + 2)) hrsumm2r
  calc ‖∑' n, (((↑(n + 2)! : 𝕂)⁻¹ • a ^ (n + 2)) : 𝔸)‖
      ≤ ∑' n, ‖(((↑(n + 2)! : 𝕂)⁻¹ • a ^ (n + 2)) : 𝔸)‖ :=
        norm_tsum_le_tsum_norm hnsumm2
    _ ≤ ∑' n, ‖a‖ ^ (n + 2) / ((n + 2)! : ℝ) :=
        tsum_le_tsum (fun n => norm_exp_term_le a (n + 2)) hnsumm2 hrsumm2r
    _ = Real.exp ‖a‖ - 1 - ‖a‖ := by
        rw [real_exp_eq_tsum, tsum_eq_zero_add hrsumm]
        simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
        rw [tsum_eq_zero_add hrsumm1r]
        simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one]
        ring
    _ ≤ ‖a‖ ^ 2 / 2 * Real.exp ‖a‖ :=
        exp_sub_one_sub_bound_real ‖a‖ (norm_nonneg a)
