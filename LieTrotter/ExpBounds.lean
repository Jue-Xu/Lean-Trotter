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
import Mathlib.Tactic

noncomputable section

open NormedSpace

variable {𝕂 : Type*} [RCLike 𝕂]
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-!
## Auxiliary lemmas for the exponential power series
-/


include 𝕂 in
lemma exp_tsum_form (a : 𝔸) :
    exp a = ∑' n, (((Nat.factorial n : 𝕂)⁻¹) • a ^ n : 𝔸) := by
  simpa [inv_natCast_smul_eq 𝕂] using
    congrFun (NormedSpace.exp_eq_tsum (𝕂 := 𝕂) (𝔸 := 𝔸)) a


include 𝕂 in
lemma exp_summable (a : 𝔸) :
    Summable (fun n => (((Nat.factorial n : 𝕂)⁻¹) • a ^ n : 𝔸)) := by
  simpa [inv_natCast_smul_eq 𝕂] using
    NormedSpace.expSeries_summable' (𝕂 := 𝕂) a

/-- The norm of each term `(n!)⁻¹ • a^n` is bounded by `‖a‖^n / n!`. -/
lemma norm_exp_term_le (a : 𝔸) (n : ℕ) :
    ‖(((Nat.factorial n : 𝕂)⁻¹) • a ^ n : 𝔸)‖ ≤ ‖a‖ ^ n / (Nat.factorial n : ℝ) := by
  rw [norm_smul, norm_inv, RCLike.norm_natCast, div_eq_inv_mul]
  gcongr
  exact norm_pow_le a n

/-- Summability of `x^n / n!` for real `x`. -/
lemma real_exp_summable (x : ℝ) :
    Summable (fun n => x ^ n / (Nat.factorial n : ℝ)) :=
  Real.summable_pow_div_factorial x

/-- Real `exp` as a tsum. -/
lemma real_exp_eq_tsum (x : ℝ) :
    Real.exp x = ∑' n, x ^ n / (Nat.factorial n : ℝ) := by
  rw [Real.exp_eq_exp_ℝ]
  exact (NormedSpace.expSeries_div_hasSum_exp (x := x)).tsum_eq.symm

/-!
## B1: Norm bound on the exponential
-/

include 𝕂 in
lemma norm_exp_le (a : 𝔸) : ‖exp a‖ ≤ Real.exp ‖a‖ := by
  rw [exp_tsum_form (𝕂 := 𝕂), real_exp_eq_tsum]
  have hnsumm : Summable (fun n => ‖(((Nat.factorial n : 𝕂)⁻¹) • a ^ n : 𝔸)‖) :=
    (real_exp_summable ‖a‖).of_nonneg_of_le (fun _ => norm_nonneg _) (norm_exp_term_le a)
  calc
    ‖∑' n, (((Nat.factorial n : 𝕂)⁻¹) • a ^ n : 𝔸)‖
      ≤ ∑' n, ‖(((Nat.factorial n : 𝕂)⁻¹) • a ^ n : 𝔸)‖ := norm_tsum_le_tsum_norm hnsumm
    _ ≤ ∑' n, ‖a‖ ^ n / (Nat.factorial n : ℝ) :=
      hnsumm.tsum_le_tsum (norm_exp_term_le a) (real_exp_summable ‖a‖)

/-!
## B2: First-order remainder
-/


include 𝕂 in
lemma norm_exp_sub_one_le (a : 𝔸) :
    ‖exp a - 1‖ ≤ Real.exp ‖a‖ - 1 := by
  have hsumm := exp_summable (𝕂 := 𝕂) a
  have hsub : exp a - 1 = ∑' n, ((((Nat.factorial (n + 1) : 𝕂)⁻¹) • a ^ (n + 1)) : 𝔸) := by
    rw [exp_tsum_form (𝕂 := 𝕂), hsumm.tsum_eq_zero_add]
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
    abel
  rw [hsub]
  have hsumm' : Summable (fun n => ((((Nat.factorial (n + 1) : 𝕂)⁻¹) • a ^ (n + 1)) : 𝔸)) :=
    hsumm.comp_injective (fun _ _ h => by omega)
  have hrsumm := real_exp_summable ‖a‖
  have hrsumm1 : Summable (fun n => ‖a‖ ^ (n + 1) / (Nat.factorial (n + 1) : ℝ)) :=
    hrsumm.comp_injective (fun _ _ h => by omega)
  have hnsumm' : Summable (fun n => ‖((((Nat.factorial (n + 1) : 𝕂)⁻¹) • a ^ (n + 1)) : 𝔸)‖) :=
    hrsumm1.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => norm_exp_term_le a (n + 1))
  calc
    ‖∑' n, ((((Nat.factorial (n + 1) : 𝕂)⁻¹) • a ^ (n + 1)) : 𝔸)‖
      ≤ ∑' n, ‖((((Nat.factorial (n + 1) : 𝕂)⁻¹) • a ^ (n + 1)) : 𝔸)‖ :=
        norm_tsum_le_tsum_norm hnsumm'
    _ ≤ ∑' n, ‖a‖ ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) :=
      hnsumm'.tsum_le_tsum (fun n => norm_exp_term_le a (n + 1)) hrsumm1
    _ = Real.exp ‖a‖ - 1 := by
      rw [real_exp_eq_tsum, hrsumm.tsum_eq_zero_add]
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
      ring

/-!
## B3: Real exponential remainder bound
-/

/-- Auxiliary: `2 * n! ≤ (n + 2)!`. -/
private lemma two_mul_factorial_le (n : ℕ) : 2 * Nat.factorial n ≤ Nat.factorial (n + 2) := by
  have h : 2 ≤ (n + 2) * (n + 1) := by nlinarith
  have step1 : 2 * n.factorial ≤ (n + 2) * (n + 1) * n.factorial :=
    Nat.mul_le_mul_right n.factorial h
  have step2 : (n + 2) * (n + 1) * n.factorial = (n + 2).factorial := by
    rw [mul_assoc, ← Nat.factorial_succ, ← Nat.factorial_succ]
  linarith

/-- For `x ≥ 0`, `exp(x) - 1 - x ≤ x²/2 · exp(x)`. -/
lemma exp_sub_one_sub_bound_real (x : ℝ) (hx : 0 ≤ x) :
    Real.exp x - 1 - x ≤ x ^ 2 / 2 * Real.exp x := by
  have hrsumm := real_exp_summable x
  have hrsumm1 : Summable (fun n => x ^ (n + 1) / (Nat.factorial (n + 1) : ℝ)) :=
    hrsumm.comp_injective (fun _ _ h => by omega)
  have hrsumm2 : Summable (fun n => x ^ (n + 2) / (Nat.factorial (n + 2) : ℝ)) :=
    hrsumm.comp_injective (fun _ _ h => by omega)
  have hrem : Real.exp x - 1 - x = ∑' n, x ^ (n + 2) / (Nat.factorial (n + 2) : ℝ) := by
    rw [real_exp_eq_tsum, hrsumm.tsum_eq_zero_add]
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    rw [hrsumm1.tsum_eq_zero_add]
    norm_num [Nat.factorial]
  rw [hrem]
  have hterm :
      ∀ n, x ^ (n + 2) / (Nat.factorial (n + 2) : ℝ) ≤
        x ^ 2 / 2 * (x ^ n / (Nat.factorial n : ℝ)) := by
    intro n
    have hrhs :
        x ^ 2 / 2 * (x ^ n / (Nat.factorial n : ℝ)) =
          x ^ (n + 2) / (2 * (Nat.factorial n : ℝ)) := by
      rw [show x ^ (n + 2) = x ^ n * x ^ 2 by rw [pow_add]]
      ring
    rw [hrhs]
    have h2nfact_pos : (0 : ℝ) < 2 * (Nat.factorial n : ℝ) := by positivity
    have hxpow_nonneg : (0 : ℝ) ≤ x ^ (n + 2) := pow_nonneg hx _
    have hle : (2 : ℝ) * (Nat.factorial n : ℝ) ≤ (Nat.factorial (n + 2) : ℝ) := by
      exact_mod_cast two_mul_factorial_le n
    exact div_le_div_of_nonneg_left hxpow_nonneg h2nfact_pos hle
  calc
    ∑' n, x ^ (n + 2) / (Nat.factorial (n + 2) : ℝ)
      ≤ ∑' n, x ^ 2 / 2 * (x ^ n / (Nat.factorial n : ℝ)) := by
        have hsummg : Summable (fun n => x ^ 2 / 2 * (x ^ n / (Nat.factorial n : ℝ))) := by
          exact Summable.mul_left (x ^ 2 / 2) hrsumm
        exact hrsumm2.tsum_le_tsum hterm hsummg
    _ = x ^ 2 / 2 * ∑' n, x ^ n / (Nat.factorial n : ℝ) := by
        simpa using hrsumm.tsum_mul_left (x ^ 2 / 2)
    _ = x ^ 2 / 2 * Real.exp x := by rw [← real_exp_eq_tsum]

/-!
## B4: Second-order remainder in normed algebra
-/


include 𝕂 in
lemma norm_exp_sub_one_sub_le (a : 𝔸) :
    ‖exp a - 1 - a‖ ≤ ‖a‖ ^ 2 / 2 * Real.exp ‖a‖ := by
  have hsumm := exp_summable (𝕂 := 𝕂) a
  have hsumm1 :
      Summable (fun n => ((((Nat.factorial (n + 1) : 𝕂)⁻¹) • a ^ (n + 1)) : 𝔸)) :=
    hsumm.comp_injective (fun _ _ h => by omega)
  have hsumm2 :
      Summable (fun n => ((((Nat.factorial (n + 2) : 𝕂)⁻¹) • a ^ (n + 2)) : 𝔸)) :=
    hsumm.comp_injective (fun _ _ h => by omega)
  have hrem :
      exp a - 1 - a = ∑' n, ((((Nat.factorial (n + 2) : 𝕂)⁻¹) • a ^ (n + 2)) : 𝔸) := by
    rw [exp_tsum_form (𝕂 := 𝕂), hsumm.tsum_eq_zero_add]
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
    rw [hsumm1.tsum_eq_zero_add]
    have : ((Nat.factorial 1 : 𝕂)⁻¹) • a ^ 1 = a := by
      simp [Nat.factorial]
    rw [this]; abel
  rw [hrem]
  have hrsumm := real_exp_summable ‖a‖
  have hrsumm1r : Summable (fun n => ‖a‖ ^ (n + 1) / (Nat.factorial (n + 1) : ℝ)) :=
    hrsumm.comp_injective (fun _ _ h => by omega)
  have hrsumm2r : Summable (fun n => ‖a‖ ^ (n + 2) / (Nat.factorial (n + 2) : ℝ)) :=
    hrsumm.comp_injective (fun _ _ h => by omega)
  have hnsumm2 :
      Summable (fun n => ‖((((Nat.factorial (n + 2) : 𝕂)⁻¹) • a ^ (n + 2)) : 𝔸)‖) :=
    hrsumm2r.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => norm_exp_term_le a (n + 2))
  calc
    ‖∑' n, ((((Nat.factorial (n + 2) : 𝕂)⁻¹) • a ^ (n + 2)) : 𝔸)‖
      ≤ ∑' n, ‖((((Nat.factorial (n + 2) : 𝕂)⁻¹) • a ^ (n + 2)) : 𝔸)‖ :=
        norm_tsum_le_tsum_norm hnsumm2
    _ ≤ ∑' n, ‖a‖ ^ (n + 2) / (Nat.factorial (n + 2) : ℝ) :=
      hnsumm2.tsum_le_tsum (fun n => norm_exp_term_le a (n + 2)) hrsumm2r
    _ = Real.exp ‖a‖ - 1 - ‖a‖ := by
      rw [real_exp_eq_tsum, hrsumm.tsum_eq_zero_add]
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
      rw [hrsumm1r.tsum_eq_zero_add]
      norm_num [Nat.factorial]
    _ ≤ ‖a‖ ^ 2 / 2 * Real.exp ‖a‖ :=
      exp_sub_one_sub_bound_real ‖a‖ (norm_nonneg a)
