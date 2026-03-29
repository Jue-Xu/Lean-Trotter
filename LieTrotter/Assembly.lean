/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Track E: Assembly — The Lie-Trotter Product Formula

Combine telescoping (A), step error (C), and exp power identity (D)
to prove the convergence rate and the main theorem.
-/

import LieTrotter.Telescoping
import LieTrotter.StepError
import LieTrotter.ExpDivPow
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter Topology NormedSpace
open scoped BigOperators

variable {𝕂 : Type*} [RCLike 𝕂]
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-!
## E1: Convergence Rate

`‖(exp(A/n) exp(B/n))^n - exp(A+B)‖ ≤ C/n`

Proof:
1. Rewrite `exp(A+B) = exp((A+B)/n)^n` by D1.
2. Apply telescoping norm bound A2.
3. Plug in step error C2 for `‖P-Q‖`.
4. Bound `max(‖P‖,‖Q‖)` using B1+D2.
5. Simplify: `exp(s/n)^n = exp(s)`, cancel `n/n²`.
-/

/-- **Convergence rate**: the Lie-Trotter error is O(1/n).
    `‖(exp(A/n) exp(B/n))^n - exp(A+B)‖ ≤ C/n` -/
theorem lie_trotter_error_rate (A B : 𝔸) :
    ∃ C > 0, ∀ n : ℕ, 0 < n →
      ‖(exp ((n : 𝕂)⁻¹ • A) * exp ((n : 𝕂)⁻¹ • B)) ^ n -
       exp (A + B)‖ ≤ C / n := by
  refine ⟨2 * ‖A‖ * ‖B‖ * Real.exp (2 * (‖A‖ + ‖B‖)) + 1, by positivity, ?_⟩
  intro n hn
  -- Step 1: Rewrite exp(A+B) = exp((A+B)/n)^n
  have hpow : exp (A + B) = (exp ((n : 𝕂)⁻¹ • (A + B))) ^ n :=
    (exp_div_pow (A + B) n hn).symm
  rw [hpow]
  set P := exp ((n : 𝕂)⁻¹ • A) * exp ((n : 𝕂)⁻¹ • B) with hP_def
  set Q := exp ((n : 𝕂)⁻¹ • (A + B)) with hQ_def
  -- Step 2: Apply telescoping norm bound
  have h_telesc := norm_pow_sub_pow_le' P Q n
  -- Step 3: Bound ‖P - Q‖ by step error
  have h_step : ‖P - Q‖ ≤ 2 * ‖A‖ * ‖B‖ / (n : ℝ) ^ 2 *
      Real.exp ((‖A‖ + ‖B‖) / n) := by
    rw [hP_def, hQ_def]
    exact lie_trotter_step_error A B n hn
  -- Step 4: Bound max(‖P‖, ‖Q‖)
  have h_max : max ‖P‖ ‖Q‖ ≤ Real.exp ((‖A‖ + ‖B‖) / n) := by
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have norm_inv_n : ‖(n : 𝕂)⁻¹‖ = ((n : ℝ))⁻¹ := by
      rw [norm_inv, RCLike.norm_natCast]
    have h_P : ‖P‖ ≤ Real.exp ((‖A‖ + ‖B‖) / n) := by
      calc ‖P‖ = ‖exp ((n : 𝕂)⁻¹ • A) * exp ((n : 𝕂)⁻¹ • B)‖ := rfl
        _ ≤ ‖exp ((n : 𝕂)⁻¹ • A)‖ * ‖exp ((n : 𝕂)⁻¹ • B)‖ := norm_mul_le _ _
        _ ≤ Real.exp ‖(n : 𝕂)⁻¹ • A‖ * Real.exp ‖(n : 𝕂)⁻¹ • B‖ := by
            gcongr
            · exact norm_exp_le (𝕂 := 𝕂) ((n : 𝕂)⁻¹ • A)
            · exact norm_exp_le (𝕂 := 𝕂) ((n : 𝕂)⁻¹ • B)
        _ = Real.exp (‖(n : 𝕂)⁻¹ • A‖ + ‖(n : 𝕂)⁻¹ • B‖) := (Real.exp_add _ _).symm
        _ = Real.exp (‖(n : 𝕂)⁻¹‖ * ‖A‖ + ‖(n : 𝕂)⁻¹‖ * ‖B‖) := by
            rw [norm_smul, norm_smul]
        _ = Real.exp ((‖A‖ + ‖B‖) / n) := by
            rw [norm_inv_n, ← mul_add, inv_mul_eq_div]
    have h_Q : ‖Q‖ ≤ Real.exp ((‖A‖ + ‖B‖) / n) := by
      calc ‖Q‖ = ‖exp ((n : 𝕂)⁻¹ • (A + B))‖ := rfl
        _ ≤ Real.exp ‖(n : 𝕂)⁻¹ • (A + B)‖ := norm_exp_le (𝕂 := 𝕂) _
        _ ≤ Real.exp (‖(n : 𝕂)⁻¹‖ * ‖A + B‖) := by
            gcongr
            exact norm_smul_le _ _
        _ ≤ Real.exp (‖(n : 𝕂)⁻¹‖ * (‖A‖ + ‖B‖)) := by
            gcongr
            exact norm_add_le A B
        _ = Real.exp ((‖A‖ + ‖B‖) / n) := by
            rw [norm_inv_n, inv_mul_eq_div]
    exact max_le h_P h_Q
  -- Step 5: Combine and simplify
  calc ‖P ^ n - Q ^ n‖
      ≤ n * ‖P - Q‖ * (max ‖P‖ ‖Q‖) ^ (n - 1) := h_telesc
    _ ≤ n * (2 * ‖A‖ * ‖B‖ / (n : ℝ) ^ 2 * Real.exp ((‖A‖ + ‖B‖) / n)) *
        (Real.exp ((‖A‖ + ‖B‖) / n)) ^ (n - 1) := by
        gcongr
    _ ≤ (2 * ‖A‖ * ‖B‖ * Real.exp (2 * (‖A‖ + ‖B‖)) + 1) / n := by
        set s := ‖A‖ + ‖B‖ with hs_def
        have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
        have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
        have hs_nonneg : 0 ≤ s := by positivity
        have h_pow : Real.exp (s / ↑n) * Real.exp (s / ↑n) ^ (n - 1) =
            Real.exp (s / ↑n) ^ n := by
          cases n with
          | zero => omega
          | succ m => simp [pow_succ']
        have h_exp_pow : Real.exp (s / ↑n) ^ n = Real.exp s := by
          rw [← Real.exp_nat_mul]
          congr 1
          field_simp
        have h_collapse : Real.exp (s / ↑n) * Real.exp (s / ↑n) ^ (n - 1) =
            Real.exp s := by rw [h_pow, h_exp_pow]
        have h_lhs : ↑n * (2 * ‖A‖ * ‖B‖ / (↑n) ^ 2 * Real.exp (s / ↑n)) *
            Real.exp (s / ↑n) ^ (n - 1) =
            2 * ‖A‖ * ‖B‖ * Real.exp s / ↑n := by
          have h_regroup : ↑n * (2 * ‖A‖ * ‖B‖ / (↑n) ^ 2 * Real.exp (s / ↑n)) *
              Real.exp (s / ↑n) ^ (n - 1) =
              ↑n * (2 * ‖A‖ * ‖B‖ / (↑n) ^ 2) *
              (Real.exp (s / ↑n) * Real.exp (s / ↑n) ^ (n - 1)) := by ring
          rw [h_regroup, h_collapse]
          field_simp
        rw [h_lhs]
        have h_num : 2 * ‖A‖ * ‖B‖ * Real.exp s ≤
            2 * ‖A‖ * ‖B‖ * Real.exp (2 * s) + 1 := by
          have h_exp_le : Real.exp s ≤ Real.exp (2 * s) := by
            gcongr; linarith
          have h_ab_nonneg : 0 ≤ 2 * ‖A‖ * ‖B‖ := by positivity
          calc 2 * ‖A‖ * ‖B‖ * Real.exp s
              ≤ 2 * ‖A‖ * ‖B‖ * Real.exp (2 * s) :=
                mul_le_mul_of_nonneg_left h_exp_le h_ab_nonneg
            _ ≤ 2 * ‖A‖ * ‖B‖ * Real.exp (2 * s) + 1 :=
                le_add_of_nonneg_right zero_le_one
        exact (div_le_div_iff_of_pos_right hn_pos).mpr h_num

/-!
## E2: Main Theorem

Standard ε-N argument using the convergence rate from E1.
-/

/-- **The Lie-Trotter Product Formula.**
    For any elements `A, B` in a complete normed algebra,
    `(exp(A/n) exp(B/n))^n → exp(A+B)` as `n → ∞`. -/
theorem lie_trotter (A B : 𝔸) :
    Filter.Tendsto
      (fun n : ℕ => (exp ((n : 𝕂)⁻¹ • A) *
                      exp ((n : 𝕂)⁻¹ • B)) ^ n)
      atTop (nhds (exp (A + B))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨C, hC_pos, hC_bound⟩ := lie_trotter_error_rate (𝕂 := 𝕂) A B
  obtain ⟨N, hN⟩ := exists_nat_gt (C / ε)
  refine ⟨N + 1, fun n hn => ?_⟩
  rw [dist_eq_norm]
  have hn_pos : 0 < n := by omega
  calc ‖(exp ((↑n : 𝕂)⁻¹ • A) * exp ((↑n : 𝕂)⁻¹ • B)) ^ n - exp (A + B)‖
      ≤ C / n := hC_bound n hn_pos
    _ ≤ C / (N + 1) := by
        apply div_le_div_of_nonneg_left hC_pos.le (by positivity : (0:ℝ) < N + 1)
        exact_mod_cast hn
    _ ≤ C / N.succ := by norm_cast
    _ < ε := by
        rw [div_lt_iff₀' (by positivity : (0 : ℝ) < ↑N.succ)]
        calc C = C / ε * ε := by field_simp
          _ < (N + 1) * ε := by
              apply mul_lt_mul_of_pos_right _ hε
              calc C / ε < N := hN
                _ < N + 1 := by linarith
          _ = ↑N.succ * ε := by push_cast; ring
